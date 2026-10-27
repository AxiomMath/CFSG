module

public import CFSG.RankThree.PartTwo.Sec16.ResGapProofFiveScalar
public import CFSG.RankThree.PartTwo.Sec3.MinimalCommutatorTwoGroup
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.Assembly.OrderReductions.FrattiniElementary

public section

namespace CFSG.RankThree.PartTwo.Sec16.ResGapFive

open Subgroup CFSG.RankThree.PartTwo.Sec3
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem exists_fixed_of_conj_mem {c : G} (hc3 : c ^ 3 = 1) {N : Subgroup G}
    (hN : IsPGroup 2 N) (hcN : c ∈ normalizer (N : Set G)) {u : G}
    (hu : u⁻¹ * (c * u * c⁻¹) ∈ N) : ∃ n ∈ N, c * (u * n) * c⁻¹ = u * n := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := zpowers c with hA
  have hA3 : IsPGroup 3 A := fun g => ⟨1, by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp g.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hc3, one_zpow, Subgroup.coe_one]⟩
  let α : A →* MulAut G := MulAut.conj.comp A.subtype
  have hcop : ¬ 3 ∣ Nat.card N := by
    obtain ⟨k, hk⟩ := hN.exists_card_eq
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hstep : ∀ x : G, u⁻¹ * x ∈ N → u⁻¹ * (c * x * c⁻¹) ∈ N := by
    intro x hx
    have h1 := (mem_normalizer_iff.mp hcN _).mp hx
    have e : u⁻¹ * (c * x * c⁻¹) = (u⁻¹ * (c * u * c⁻¹)) * (c * (u⁻¹ * x) * c⁻¹) := by group
    rw [e]
    exact mul_mem hu h1
  have hpow : ∀ n : ℕ, ∀ x : G, u⁻¹ * x ∈ N → u⁻¹ * (c ^ n * x * (c ^ n)⁻¹) ∈ N := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      have e : c ^ (n + 1) * x * (c ^ (n + 1))⁻¹ = c * (c ^ n * x * (c ^ n)⁻¹) * c⁻¹ := by
        rw [pow_succ']
        group
      rw [e]
      exact hstep _ (ih x hx)
  obtain ⟨y, hy, hyfix⟩ :=
    (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3 hA3 α N hcop u).2 (by
      intro a x hx
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr a.2)
      change u⁻¹ * ((a : G) * x * (a : G)⁻¹) ∈ N
      rw [← hn]
      exact hpow n x hx)
  refine ⟨u⁻¹ * y, hy, ?_⟩
  rw [mul_inv_cancel_left]
  exact hyfix ⟨c, mem_zpowers c⟩

theorem mem_normalizer_sup_of {A B : Subgroup G} {g : G}
    (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A ⊔ B) (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ A ⊔ B) :
    g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  refine mem_normalizer_of_forall_conj_mem fun w hw => ?_
  have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hA a ha
    · simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hB b hb
  have := hle hw
  simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this

theorem eq_of_sup_squares {U V : Subgroup G} (hU : IsPGroup 2 U) (hVU : V ≤ U)
    (hsup : V ⊔ squares U = U) : V = U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : squares U ≤ (frattini U).map U.subtype := by
    rw [squares, closure_le]
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu⟩ ^ 2, CFSG.OrderReductions.FrattiniElementary.pow_mem_frattini 2 hU _,
      by simp⟩
  have hle : (⊤ : Subgroup U).map U.subtype ≤ (V.subgroupOf U ⊔ frattini U).map U.subtype := by
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_of_le_left hVU,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    calc U = V ⊔ squares U := hsup.symm
      _ ≤ V ⊔ (frattini U).map U.subtype := sup_le_sup_left hsq V
  have htop : V.subgroupOf U ⊔ frattini U = ⊤ :=
    top_le_iff.mp ((Subgroup.map_le_map_iff_of_injective U.subtype_injective).mp hle)
  have hV := frattini_nongenerating htop
  refine le_antisymm hVU fun u hu => ?_
  have : (⟨u, hu⟩ : U) ∈ V.subgroupOf U := hV ▸ mem_top _
  exact Subgroup.mem_subgroupOf.mp this

structure CMin (X U : Subgroup G) (x c : G) : Prop where
  zpowers_eq : X = zpowers x
  card_X : Nat.card X = 5
  isPGroup : IsPGroup 2 U
  comm_eq : ⁅U, X⁆ = U
  ne_bot : U ≠ ⊥
  c_mem : c ∈ normalizer (U : Set G)
  pow_three : c ^ 3 = 1
  comm_xc : x * c = c * x
  fix : ∀ u ∈ U, c * u * c⁻¹ = u → x * u * x⁻¹ = u
  cmin : ∀ V ≤ U, c ∈ normalizer (V : Set G) → ⁅V, X⁆ = V → V ≠ ⊥ → V = U

namespace CMin

variable {X U : Subgroup G} {x c : G}

omit [Finite G] in
theorem x_mem (h : CMin X U x c) : x ∈ X := h.zpowers_eq ▸ mem_zpowers x

omit [Finite G] in
theorem isPGroup_X (h : CMin X U x c) : IsPGroup 5 X :=
  IsPGroup.of_card (n := 1) (by rw [h.card_X, pow_one])

omit [Finite G] in
theorem pow_five (h : CMin X U x c) : x ^ 5 = 1 := by
  have hp := pow_card_eq_one' (G := X) (x := ⟨x, h.x_mem⟩)
  rw [h.card_X] at hp
  have := congrArg Subtype.val hp
  simpa using this

omit [Finite G] in
theorem le_normalizer (h : CMin X U x c) : X ≤ normalizer (U : Set G) := by
  rw [← h.comm_eq]
  exact normalizer_commutator_ge_right U X

omit [Finite G] in
theorem comm_c (h : CMin X U x c) {y : G} (hy : y ∈ X) : c * y = y * c := by
  rw [h.zpowers_eq] at hy
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  exact (Commute.zpow_right (h.comm_xc.symm : Commute c x) k).eq

theorem c_mem_normalizer_X (h : CMin X U x c) : c ∈ normalizer (X : Set G) :=
  mem_normalizer_of_forall_conj_mem fun y hy => by
    rw [h.comm_c hy, mul_inv_cancel_right]
    exact hy

theorem x_mem_normalizer_squares (h : CMin X U x c) : x ∈ normalizer (squares U : Set G) :=
  mem_normalizer_of_forall_conj_mem fun _ hf => conj_mem_squares (h.le_normalizer h.x_mem) hf

theorem c_mem_normalizer_squares (h : CMin X U x c) : c ∈ normalizer (squares U : Set G) :=
  mem_normalizer_of_forall_conj_mem fun _ hf => conj_mem_squares h.c_mem hf

theorem le_normalizer_squares' (_h : CMin X U x c) : U ≤ normalizer (squares U : Set G) :=
  le_normalizer_squares Subgroup.le_normalizer

theorem commutator_eq_bot (h : CMin X U x c) {R : Subgroup G} (hRU : R ≤ U)
    (hRX : X ≤ normalizer (R : Set G)) (hcR : c ∈ normalizer (R : Set G)) (hRne : R ≠ U) :
    ⁅R, X⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : ⁅R, X⁆ ≤ R := le_normalizer_iff_commutator_le_left.mp hRX
  have hcop : ¬ 5 ∣ Nat.card R := by
    obtain ⟨k, hk⟩ := (h.isPGroup.to_le hRU).exists_card_eq
    rw [hk]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      ((by norm_num : (5 : ℕ).Prime).dvd_of_dvd_pow hd)
    omega
  have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 5
    (by norm_num) X R h.isPGroup_X hcop hRX
  have hc : c ∈ normalizer ((⁅R, X⁆ : Subgroup G) : Set G) :=
    mem_normalizer_of_forall_conj_mem fun _ hk =>
      conj_mem_commutator hcR h.c_mem_normalizer_X hk
  by_contra hbot
  have hU' := h.cmin _ (hle.trans hRU) hc hidem hbot
  exact hRne (le_antisymm hRU (hU' ▸ hle))

theorem mem_squares_of_x (h : CMin X U x c) {u : G} (hu : u ∈ U)
    (hux : x * u * x⁻¹ * u⁻¹ ∈ squares U) : u ∈ squares U :=
  mem_squares_of_conj_mul_inv_mem (by norm_num) (by norm_num) h.zpowers_eq h.card_X h.isPGroup
    h.le_normalizer h.comm_eq hu hux

theorem mem_squares_of_c (h : CMin X U x c) {u : G} (hu : u ∈ U)
    (huc : c * u * c⁻¹ * u⁻¹ ∈ squares U) : u ∈ squares U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu' : u⁻¹ * (c * u * c⁻¹) ∈ squares U := by
    have := (mem_normalizer_iff.mp (h.le_normalizer_squares' (inv_mem hu)) _).mp huc
    have e : u⁻¹ * (c * u * c⁻¹ * u⁻¹) * u⁻¹⁻¹ = u⁻¹ * (c * u * c⁻¹) := by group
    rwa [e] at this
  obtain ⟨n, hn, hfix⟩ := exists_fixed_of_conj_mem h.pow_three
    (h.isPGroup.to_le (squares_le U)) h.c_mem_normalizer_squares hu'
  have hunU : u * n ∈ U := mul_mem hu (squares_le U hn)
  have hx := h.fix _ hunU hfix
  apply h.mem_squares_of_x hu
  have hxn : x * n⁻¹ * x⁻¹ ∈ squares U :=
    (mem_normalizer_iff.mp h.x_mem_normalizer_squares _).mp (inv_mem hn)
  have h1 : n * (x * n⁻¹ * x⁻¹) ∈ squares U := mul_mem hn hxn
  have h2 := (mem_normalizer_iff.mp (h.le_normalizer_squares' hu) _).mp h1
  have e : x * u * x⁻¹ * u⁻¹ = u * (n * (x * n⁻¹ * x⁻¹)) * u⁻¹ := by
    calc x * u * x⁻¹ * u⁻¹ = x * (u * n) * x⁻¹ * (x * n⁻¹ * x⁻¹) * u⁻¹ := by group
      _ = u * n * (x * n⁻¹ * x⁻¹) * u⁻¹ := by rw [hx]
      _ = u * (n * (x * n⁻¹ * x⁻¹)) * u⁻¹ := by group
  rw [e]
  exact h2

theorem irred (h : CMin X U x c) (V : Subgroup G) (hΦV : squares U ≤ V) (hVU : V ≤ U)
    (hxV : x ∈ normalizer (V : Set G)) (hcV : c ∈ normalizer (V : Set G)) :
    V = squares U ∨ V = U := by
  by_cases hV : V = U
  · exact Or.inr hV
  left
  have hXV : X ≤ normalizer (V : Set G) := by
    rw [h.zpowers_eq]
    exact zpowers_le.mpr hxV
  have hb := h.commutator_eq_bot hVU hXV hcV hV
  refine le_antisymm (fun v hv => ?_) hΦV
  apply h.mem_squares_of_x (hVU hv)
  have hc : ⁅v, x⁆ = 1 := by
    have : ⁅v, x⁆ ∈ ⁅V, X⁆ := commutator_mem_commutator hv h.x_mem
    rwa [hb, mem_bot] at this
  rw [commutatorElement_eq_one_iff_mul_comm] at hc
  rw [← hc, mul_inv_cancel_right, mul_inv_cancel]
  exact one_mem _

theorem omega_or (h : CMin X U x c) :
    (∀ u ∈ U, (c * u * c⁻¹)⁻¹ * ((x * u * x⁻¹) * (x⁻¹ * u * x)) ∈ squares U) ∨
      (∀ u ∈ U, (c * u * c⁻¹)⁻¹ * ((x ^ 2 * u * (x ^ 2)⁻¹) * ((x ^ 2)⁻¹ * u * x ^ 2)) ∈
        squares U) :=
  conj_mem_or (squares_le U) h.le_normalizer_squares'
    (fun _ ha _ hb => commutator_le_squares U (commutator_mem_commutator ha hb))
    (fun _ hu => sq_mem_squares hu) (h.le_normalizer h.x_mem) h.c_mem
    h.x_mem_normalizer_squares h.c_mem_normalizer_squares h.pow_five h.pow_three h.comm_xc
    (fun _ hu => h.mem_squares_of_x hu) (fun _ hu => h.mem_squares_of_c hu) h.irred

theorem min (h : CMin X U x c) : ∀ V ≤ U, ⁅V, X⁆ = V → V ≠ ⊥ → V = U := by
  intro V hVU hVX hV1
  have hXV : X ≤ normalizer (V : Set G) := by
    rw [← hVX]
    exact normalizer_commutator_ge_right V X
  have hxV : x ∈ normalizer (V : Set G) := hXV h.x_mem
  have hconjV : ∀ {g : G}, g ∈ normalizer (V : Set G) → ∀ v ∈ V, g * v * g⁻¹ ∈ V :=
    fun hg v hv => (mem_normalizer_iff.mp hg v).mp hv
  have hconjV' : ∀ {g : G}, g ∈ normalizer (V : Set G) → ∀ v ∈ V, g⁻¹ * v * g ∈ V :=
    fun hg v hv => by
      have := (mem_normalizer_iff.mp (inv_mem hg) v).mp hv
      rwa [inv_inv] at this
  have hΦc : ∀ {g : G}, g ∈ normalizer (squares U : Set G) → ∀ f ∈ squares U,
      g * f * g⁻¹ ∈ V ⊔ squares U :=
    fun hg f hf => mem_sup_right ((mem_normalizer_iff.mp hg f).mp hf)
  have hxW : x ∈ normalizer ((V ⊔ squares U : Subgroup G) : Set G) :=
    mem_normalizer_sup_of (fun v hv => mem_sup_left (hconjV hxV v hv))
      (hΦc h.x_mem_normalizer_squares)
  have hpoly : ∀ {g : G}, g ∈ normalizer (V : Set G) →
      (∀ u ∈ U, (c * u * c⁻¹)⁻¹ * ((g * u * g⁻¹) * (g⁻¹ * u * g)) ∈ squares U) →
      ∀ v ∈ V, c * v * c⁻¹ ∈ V ⊔ squares U := by
    intro g hg hω v hv
    have e : c * v * c⁻¹ = ((g * v * g⁻¹) * (g⁻¹ * v * g)) *
        ((c * v * c⁻¹)⁻¹ * ((g * v * g⁻¹) * (g⁻¹ * v * g)))⁻¹ := by group
    rw [e]
    exact mul_mem (mem_sup_left (mul_mem (hconjV hg v hv) (hconjV' hg v hv)))
      (mem_sup_right (inv_mem (hω v (hVU hv))))
  have hcV : ∀ v ∈ V, c * v * c⁻¹ ∈ V ⊔ squares U := by
    rcases h.omega_or with hω | hω
    · exact hpoly hxV hω
    · exact hpoly (pow_mem hxV 2) hω
  have hcW : c ∈ normalizer ((V ⊔ squares U : Subgroup G) : Set G) :=
    mem_normalizer_sup_of hcV (hΦc h.c_mem_normalizer_squares)
  rcases h.irred _ le_sup_right (sup_le hVU (squares_le U)) hxW hcW with hW | hW
  · exfalso
    apply hV1
    have hVΦ : V ≤ squares U := hW ▸ le_sup_left
    have hb := h.commutator_eq_bot (squares_le U) (le_normalizer_squares h.le_normalizer)
      h.c_mem_normalizer_squares (squares_ne h.isPGroup h.ne_bot)
    rw [← hVX, eq_bot_iff, ← hb]
    exact commutator_mono hVΦ le_rfl
  · exact eq_of_sup_squares h.isPGroup hVU hW

end CMin

end CFSG.RankThree.PartTwo.Sec16.ResGapFive
