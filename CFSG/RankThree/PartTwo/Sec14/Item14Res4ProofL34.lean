module

public import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofLower
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofUpper
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec4.Item424ProofInnerBar
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open scoped Pointwise

namespace Res4L34

section Generic

variable {Γ : Type*} [Group Γ]

theorem exists_mem_centralizer_of_coset [Finite Γ] {p : ℕ} [Fact p.Prime] {B T : Subgroup Γ}
    (hB : IsPGroup p B) (hT : ¬ p ∣ Nat.card T) (hBT : B ≤ Subgroup.normalizer (T : Set Γ))
    {n : Γ} (hn : ∀ b ∈ B, n⁻¹ * (b * n * b⁻¹) ∈ T) :
    ∃ m : Γ, n⁻¹ * m ∈ T ∧ m ∈ Subgroup.centralizer (B : Set Γ) := by
  let α : ↥B →* MulAut Γ := MulAut.conj.comp B.subtype
  have hinv : ∀ (a : ↥B) (x : Γ), n⁻¹ * x ∈ T → n⁻¹ * α a x ∈ T := by
    intro a x hx
    have hax : α a x = (a : Γ) * x * (a : Γ)⁻¹ := rfl
    have e : n⁻¹ * ((a : Γ) * x * (a : Γ)⁻¹) =
        (n⁻¹ * ((a : Γ) * n * (a : Γ)⁻¹)) * ((a : Γ) * (n⁻¹ * x) * (a : Γ)⁻¹) := by group
    rw [hax, e]
    exact T.mul_mem (hn a a.2) ((Subgroup.mem_normalizer_iff.mp (hBT a.2) _).mp hx)
  obtain ⟨m, hm, hfix⟩ :=
    (Semidihedral.Principal.coprime_invariant_coset_fixed p hB α T hT n).2 hinv
  refine ⟨m, hm, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
  have h1 : b * m * b⁻¹ = m := hfix ⟨b, hb⟩
  calc b * m = b * m * b⁻¹ * b := by group
    _ = m * b := by rw [h1]

theorem exists_lift_not_three_dvd {Q : Type*} [Group Q] (π : Γ →* Q)
    (hπ : Function.Surjective π) (hker : ∀ z : Γ, π z = 1 → z ^ 3 = 1) {x : Q}
    (hx : ¬ 3 ∣ orderOf x) : ∃ y : Γ, π y = x ∧ ¬ 3 ∣ orderOf y := by
  obtain ⟨y₀, rfl⟩ := hπ x
  set n := orderOf (π y₀) with hn
  have hn0 : n ≠ 0 := fun h => hx (h ▸ dvd_zero 3)
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hx
  have hyn : π (y₀ ^ n) = 1 := by rw [map_pow, hn, pow_orderOf_eq_one]
  have hy3n : y₀ ^ (3 * n) = 1 := by
    rw [mul_comm, pow_mul]
    exact hker _ hyn
  obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hcop hn0
  refine ⟨y₀ ^ (3 * s), ?_, ?_⟩
  · rw [map_pow, ← pow_mod_orderOf, ← hn, hs, pow_mod_orderOf, pow_one]
  · intro h3
    apply hx
    refine h3.trans (orderOf_dvd_of_pow_eq_one ?_)
    rw [← pow_mul, show 3 * s * n = 3 * n * s by ring, pow_mul, hy3n, one_pow]

theorem commute_of_commutator_mem_zpowers {x a c : Γ} (hc3 : c ^ 3 = 1) (hxc : x * c = c * x)
    (hx : ¬ 3 ∣ orderOf x) (hd : x * a * x⁻¹ * a⁻¹ ∈ Subgroup.zpowers c) : x * a = a * x := by
  set d := x * a * x⁻¹ * a⁻¹ with hddef
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hd
  have hxd : Commute x d := by
    rw [← hj]
    exact (Commute.zpow_right hxc j)
  have hd3 : d ^ 3 = 1 := by
    rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]
  have hxa : x * a * x⁻¹ = d * a := by rw [hddef]; group
  have key : ∀ k : ℕ, x ^ k * a * (x ^ k)⁻¹ = d ^ k * a := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc x ^ (k + 1) * a * (x ^ (k + 1))⁻¹ = x * (x ^ k * a * (x ^ k)⁻¹) * x⁻¹ := by group
        _ = x * (d ^ k * a) * x⁻¹ := by rw [ih]
        _ = d ^ k * (x * a * x⁻¹) := by
          have h1 : x * d ^ k = d ^ k * x := (hxd.pow_right k).eq
          calc x * (d ^ k * a) * x⁻¹ = (x * d ^ k) * a * x⁻¹ := by group
            _ = (d ^ k * x) * a * x⁻¹ := by rw [h1]
            _ = d ^ k * (x * a * x⁻¹) := by group
        _ = d ^ (k + 1) * a := by rw [hxa, pow_succ]; group
  have hk := key (orderOf x)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hk
  have hdk : d ^ orderOf x = 1 := by
    have := congrArg (· * a⁻¹) hk
    simpa using this.symm
  have h1 : orderOf d ∣ orderOf x := orderOf_dvd_of_pow_eq_one hdk
  have h2 : orderOf d ∣ 3 := orderOf_dvd_of_pow_eq_one hd3
  have hcop : Nat.Coprime 3 (orderOf x) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hx
  have h3 : orderOf d ∣ Nat.gcd 3 (orderOf x) := Nat.dvd_gcd h2 h1
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
  have : x * a * x⁻¹ * a⁻¹ = 1 := h3
  calc x * a = x * a * x⁻¹ * a⁻¹ * (a * x) := by group
    _ = a * x := by rw [this, one_mul]

theorem isSolvable_sup_of_le_normalizer [Finite Γ] {H N : Subgroup Γ}
    (hHN : H ≤ Subgroup.normalizer (N : Set Γ)) (hH : Group.IsSolvable H)
    (hN : Group.IsSolvable N) : Group.IsSolvable (H ⊔ N : Subgroup Γ) := by
  set S := H ⊔ N with hS
  have hNS : N ≤ S := le_sup_right
  have hHS : H ≤ S := le_sup_left
  have hn : (N.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNS).mpr (sup_le hHN Subgroup.le_normalizer)
  have : Group.IsSolvable (N.subgroupOf S) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hNS).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNS).injective
  have : Group.IsSolvable (S ⧸ N.subgroupOf S) := by
    let f : H →* S ⧸ N.subgroupOf S := (QuotientGroup.mk' _).comp (Subgroup.inclusion hHS)
    have hf : Function.Surjective f := by
      intro z
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf S) z
      have hl : (l : Γ) ∈ (H : Set Γ) * (N : Set Γ) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right H N hHN]
        exact l.2
      obtain ⟨h, hh, n, hn', hhn⟩ := Set.mem_mul.mp hl
      refine ⟨⟨h, hh⟩, ?_⟩
      change QuotientGroup.mk' (N.subgroupOf S) (Subgroup.inclusion hHS ⟨h, hh⟩) = _
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have : ((Subgroup.inclusion hHS ⟨h, hh⟩)⁻¹ * l : S) = (n : Γ) := by
        change h⁻¹ * (l : Γ) = n
        rw [← hhn]
        group
      rw [this]
      exact hn'
    exact Group.isSolvable_of_surjective hf
  exact Group.isSolvable_of_subgroup_quotient (N.subgroupOf S)

omit [Group Γ] in
theorem le_normalizer_of_le_of_le_normalizer {Γ : Type*} [Group Γ] {T W : Subgroup Γ}
    (hTW : T ≤ W) (hWT : W ≤ Subgroup.normalizer (T : Set Γ)) :
    T ≤ Subgroup.normalizer (W : Set Γ) := by
  refine Item148PtRes2.le_normalizer_of_conj_mem' fun t ht w hw => ?_
  have h1 : w * t⁻¹ * w⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hWT hw) _).mp (inv_mem ht)
  have e : t * w * t⁻¹ = (t * (w * t⁻¹ * w⁻¹)) * w := by group
  rw [e]
  exact W.mul_mem (hTW (T.mul_mem ht h1)) hw

theorem mem_normalizer_sup {H K : Subgroup Γ} {g : Γ} (hH : g ∈ Subgroup.normalizer (H : Set Γ))
    (hK : g ∈ Subgroup.normalizer (K : Set Γ)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hH, Subgroup.mem_normalizer_iff_map_conj_eq.mp hK]

end Generic

section Action

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {k : Type} [Field k]

noncomputable def actL34 (ψ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projectiveSL 3 k) :
    ↥(Subgroup.normalizer (L : Set G)) →* MulAut (projectiveSL 3 k) :=
  (MulAut.congr ψ).toMonoidHom.comp ((Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom)

omit [Finite G] in
theorem mk_eq_mk_iff [Finite L] (x l : L) :
    (x : L ⧸ aschbacherSolvableCore 3 L) = (l : L ⧸ aschbacherSolvableCore 3 L) ↔
      (x : G) * (l : G)⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  rw [QuotientGroup.eq_iff_div_mem, inSubgroup]
  rw [show (x : G) * (l : G)⁻¹ = L.subtype (x / l) by simp [div_eq_mul_inv]]
  rw [Subgroup.mem_map_iff_mem L.subtype_injective]

theorem thetaQuotMulAut_eq_one_iff (g : ↥(Subgroup.normalizer (L : Set G))) :
    Sec4.thetaQuotMulAut L (L.normalizerMonoidHom g) = 1 ↔
      ∀ l ∈ L, (g : G) * l * (g : G)⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  have key : ∀ l : L, ((L.normalizerMonoidHom g l : L) : L ⧸ aschbacherSolvableCore 3 L) =
      (l : L ⧸ aschbacherSolvableCore 3 L) ↔
      (g : G) * l * (g : G)⁻¹ * (l : G)⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    intro l
    rw [mk_eq_mk_iff]
    rfl
  constructor
  · intro h l hl
    have h2 := congrArg (fun σ : MulAut (L ⧸ aschbacherSolvableCore 3 L) =>
      σ ((⟨l, hl⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)) h
    exact (key ⟨l, hl⟩).mp h2
  · intro h
    ext q
    induction q using QuotientGroup.induction_on with
    | H l => exact (key l).mpr (h l l.2)

theorem actL34_eq_one_iff (ψ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projectiveSL 3 k)
    (g : ↥(Subgroup.normalizer (L : Set G))) :
    actL34 ψ g = 1 ↔ Sec4.thetaQuotMulAut L (L.normalizerMonoidHom g) = 1 := by
  change (MulAut.congr ψ) (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom g)) = 1 ↔ _
  exact MulEquiv.map_eq_one_iff _

theorem mem_thetaQuotCentralizer_iff' {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ Sec4.thetaQuotCentralizer L ↔
      ∀ l ∈ L, g * l * g⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  rw [← thetaQuotMulAut_eq_one_iff ⟨g, hg⟩]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro h
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem actL34_of_mem (ψ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projectiveSL 3 k) {a : G}
    (ha : a ∈ L) (haN : a ∈ Subgroup.normalizer (L : Set G)) :
    actL34 ψ ⟨a, haN⟩ = MulAut.conj (ψ ((⟨a, ha⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)) := by
  ext p
  obtain ⟨q, rfl⟩ := ψ.surjective p
  induction q using QuotientGroup.induction_on with
  | H l =>
    change ψ (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨a, haN⟩) (ψ.symm (ψ l))) = _
    rw [ψ.symm_apply_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1

end Action

section Kernel

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_eq_mul_zpow_of_mem_sup {B : Subgroup G} {c : G} (h : ∀ β ∈ B, β * c = c * β)
    {a : G} (ha : a ∈ B ⊔ Subgroup.zpowers c) : ∃ β ∈ B, ∃ j : ℤ, a = β * c ^ j := by
  have hDN : Subgroup.zpowers c ≤ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun g hg => h g hg)
  rw [sup_comm, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers c) B hDN] at ha
  obtain ⟨w, hw, u, hu, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hcu : Commute u c := h u hu
  exact ⟨u, hu, j, (hcu.zpow_right j).eq.symm⟩

omit [Finite G] in
theorem commutator_mem_theta_of_mem {A L : Subgroup G} {c : G}
    (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hcA : c ∈ A) {g : G} (hgc : g ∈ Subgroup.centralizer ({c} : Set G))
    (hg : ∀ l ∈ L, g * l * g⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L) {a : G}
    (ha : a ∈ A) : g * a * g⁻¹ * a⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  rw [hAc, sup_comm] at ha
  obtain ⟨β, hβ, j, rfl⟩ :=
    exists_eq_mul_zpow_of_mem_sup (B := A ⊓ L) (fun β hβ => hAab β hβ.1 c hcA) ha
  have hgc' : Commute g c := (Subgroup.mem_centralizer_singleton_iff.mp hgc)
  have hgcj : g * c ^ j * g⁻¹ = c ^ j := by
    rw [(hgc'.zpow_right j).eq]
    group
  have e : g * (β * c ^ j) * g⁻¹ * (β * c ^ j)⁻¹ = g * β * g⁻¹ * β⁻¹ := by
    calc g * (β * c ^ j) * g⁻¹ * (β * c ^ j)⁻¹
        = g * β * g⁻¹ * (g * c ^ j * g⁻¹) * (c ^ j)⁻¹ * β⁻¹ := by group
      _ = g * β * g⁻¹ * β⁻¹ := by rw [hgcj]; group
  rw [e]
  exact hg β hβ.2

theorem mem_pPrimeCoreOf_of_mem_thetaQuotCentralizer {A L : Subgroup G} {c : G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hCN : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hcA : c ∈ A) (hA3 : IsPGroup 3 A) {v : G}
    (hvX : v ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
    (hvC : v ∈ Subgroup.centralizer ({c} : Set G)) (hvN : v ∈ Sec4.thetaQuotCentralizer L) :
    v ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({c} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  set X := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hX
  have : (aschbacherSolvableCore 3 ↥L).Characteristic :=
    Sec4.aschbacherSolvableCore_characteristic _
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have hθL3 : ¬ 3 ∣ Nat.card θL := by
    rw [hθL, inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
    exact hθ3
  have hθLL : θL ≤ L := Subgroup.map_subtype_le _
  have hCθ : C ≤ Subgroup.normalizer (θL : Set G) :=
    hCN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hLθ : L ≤ Subgroup.normalizer (θL : Set G) := hLc.trans hCθ
  have hAC : A ≤ C := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hAab x hx c hcA)
  set N := C ⊓ Sec4.thetaQuotCentralizer L with hN
  have hmemN : ∀ g : G, g ∈ N ↔ g ∈ C ∧
      ∀ l ∈ L, g * l * g⁻¹ * l⁻¹ ∈ θL := fun g => by
    constructor
    · rintro ⟨hgC, hgT⟩
      exact ⟨hgC, (mem_thetaQuotCentralizer_iff' (hCN hgC)).mp hgT⟩
    · rintro ⟨hgC, hg⟩
      exact ⟨hgC, (mem_thetaQuotCentralizer_iff' (hCN hgC)).mpr hg⟩
  have hθN : θL ≤ N := by
    intro t ht
    refine (hmemN t).mpr ⟨hLc (hθLL ht), fun l hl => ?_⟩
    have h1 : l * t⁻¹ * l⁻¹ ∈ θL :=
      (Subgroup.mem_normalizer_iff.mp (hLθ hl) _).mp (inv_mem ht)
    have e : t * l * t⁻¹ * l⁻¹ = t * (l * t⁻¹ * l⁻¹) := by group
    rw [e]
    exact θL.mul_mem ht h1
  have hNθ : N ≤ Subgroup.normalizer (θL : Set G) := inf_le_left.trans hCθ
  have hCNN : C ≤ Subgroup.normalizer (N : Set G) := by
    refine Item148PtRes2.le_normalizer_of_conj_mem' fun g hg n hn => ?_
    obtain ⟨hnC, hn'⟩ := (hmemN n).mp hn
    refine (hmemN _).mpr ⟨C.mul_mem (C.mul_mem hg hnC) (C.inv_mem hg), fun l hl => ?_⟩
    have hl' : g⁻¹ * l * g⁻¹⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hCN (C.inv_mem hg)) l).mp hl
    have h1 := hn' _ hl'
    have h2 : g * (n * (g⁻¹ * l * g⁻¹⁻¹) * n⁻¹ * (g⁻¹ * l * g⁻¹⁻¹)⁻¹) * g⁻¹ ∈ θL :=
      (Subgroup.mem_normalizer_iff.mp (hCθ hg) _).mp h1
    have e : g * n * g⁻¹ * l * (g * n * g⁻¹)⁻¹ * l⁻¹ =
        g * (n * (g⁻¹ * l * g⁻¹⁻¹) * n⁻¹ * (g⁻¹ * l * g⁻¹⁻¹)⁻¹) * g⁻¹ := by group
    rw [e]
    exact h2
  set D := N ⊓ Subgroup.centralizer (A : Set G) with hD
  set W := pPrimeCoreOf 3 D ⊔ θL with hW
  have hWN : W ≤ N := sup_le ((pPrimeCoreOf_le 3 D).trans inf_le_left) hθN
  have hNW : N ≤ Subgroup.normalizer (W : Set G) := by
    intro n hn
    have hnC := ((hmemN n).mp hn)
    obtain ⟨m, hm, hmA⟩ := exists_mem_centralizer_of_coset (n := n) hA3 hθL3
      (hAC.trans hCθ) fun b hb => by
        have h1 := commutator_mem_theta_of_mem hAc hAab hcA (C.inv_mem hnC.1)
          (((hmemN n⁻¹).mp (N.inv_mem hn)).2) hb
        have e : n⁻¹ * (b * n * b⁻¹) = n⁻¹ * b * n⁻¹⁻¹ * b⁻¹ := by group
        rw [e]
        exact h1
    have hmN : m ∈ N := by
      have h1 := N.mul_mem hn (hθN hm)
      rwa [mul_inv_cancel_left] at h1
    have hmD : m ∈ D := ⟨hmN, hmA⟩
    have hmW : m ∈ Subgroup.normalizer (W : Set G) :=
      mem_normalizer_sup (le_normalizer_pPrimeCoreOf 3 D hmD) (hNθ hmN)
    have ht : m⁻¹ * n ∈ θL := by
      have h1 := θL.inv_mem hm
      rwa [mul_inv_rev, inv_inv] at h1
    have htW : m⁻¹ * n ∈ Subgroup.normalizer (W : Set G) :=
      le_normalizer_of_le_of_le_normalizer le_sup_right (hWN.trans hNθ) ht
    have e : n = m * (m⁻¹ * n) := by group
    rw [e]
    exact mul_mem hmW htW
  have hW3 : Nat.Coprime 3 (Nat.card W) := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => ?_
    have hdvd := card_sup_dvd_card_mul
      (((pPrimeCoreOf_le 3 D).trans (inf_le_left.trans hNθ)) : pPrimeCoreOf 3 D ≤ _)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp (h3.trans hdvd) with h | h
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (coprime_card_pPrimeCoreOf 3 D) h
    · exact hθL3 h
  have hWO : W ≤ pPrimeCoreOf 3 N := le_pPrimeCoreOf hWN hNW hW3
  have hNO : pPrimeCoreOf 3 N ≤ pPrimeCoreOf 3 C :=
    le_pPrimeCoreOf ((pPrimeCoreOf_le 3 N).trans inf_le_left)
      (hCNN.trans (normalizer_le_normalizer_pPrimeCoreOf 3 N)) (coprime_card_pPrimeCoreOf 3 N)
  have hvD : v ∈ D := ⟨⟨hvC, hvN⟩, pPrimeCoreOf_le 3 _ hvX⟩
  have hXD : X ⊓ D ≤ pPrimeCoreOf 3 D := by
    refine le_pPrimeCoreOf inf_le_right ?_ ?_
    · refine Item148PtRes2.le_normalizer_of_conj_mem' fun g hg y hy => ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp
          ((le_normalizer_pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) hg.2) y).mp hy.1
      · exact D.mul_mem (D.mul_mem hg hy.2) (D.inv_mem hg)
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (coprime_card_pPrimeCoreOf 3 _)
  exact hNO (hWO (Subgroup.mem_sup_left (hXD ⟨hvX, hvD⟩)))

theorem pPrimeCoreOf_le_thetaQuotCentralizer {A L : Subgroup G} {c : G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hCN : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hAC : A ≤ Subgroup.centralizer ({c} : Set G)) (hA3 : IsPGroup 3 A)
    (ψ₀ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) :
    pPrimeCoreOf 3 (Subgroup.centralizer ({c} : Set G)) ≤ Sec4.thetaQuotCentralizer L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set Oc := pPrimeCoreOf 3 C with hOc
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  have hOcC : Oc ≤ C := pPrimeCoreOf_le 3 C
  have hCOc : C ≤ Subgroup.normalizer (Oc : Set G) := le_normalizer_pPrimeCoreOf 3 C
  have hOc3 : ¬ 3 ∣ Nat.card Oc :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 C)
  set Y := ((Oc ⊓ L).subgroupOf L).map (QuotientGroup.mk' θ) with hY
  set E := ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' θ) with hE
  have hE3 : IsPGroup 3 ((A ⊓ L).subgroupOf L) := fun x => by
    obtain ⟨n, hn⟩ := hA3 ⟨(x : G), (Subgroup.mem_subgroupOf.mp x.2).1⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩
  have hE9 : Nat.card E = 9 := by
    rw [hE, Sec4.Item424Proof.card_map_mk_of_isPGroup hE3,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, h9]
  have hY3 : ¬ 3 ∣ Nat.card Y := by
    intro h3
    apply hOc3
    have h1 := h3.trans (Subgroup.card_map_dvd ((Oc ⊓ L).subgroupOf L) (QuotientGroup.mk' θ))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at h1
    exact h1.trans (Subgroup.card_dvd_of_le inf_le_left)
  have hEY : E ≤ Subgroup.normalizer (Y : Set (↥L ⧸ θ)) := by
    refine (Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map _)
    refine Item148PtRes2.le_normalizer_of_conj_mem' fun e he y hy => ?_
    rw [Subgroup.mem_subgroupOf] at he hy ⊢
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hCOc (hAC he.1)) _).mp hy.1, ?_⟩
    exact L.mul_mem (L.mul_mem e.2 y.2) (L.inv_mem e.2)
  have hYbot : Y = ⊥ := Item148PtRes2.eq_bot_of_l34 ψ₀ hE9 hY3 hEY
  have hOcLθ : ∀ x ∈ Oc ⊓ L, x ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    intro x hx
    have h1 : QuotientGroup.mk' θ ⟨x, hx.2⟩ ∈ Y :=
      ⟨⟨x, hx.2⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hYbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨⟨x, hx.2⟩, h1, rfl⟩
  intro t ht
  refine (mem_thetaQuotCentralizer_iff' (hCN (hOcC ht))).mpr fun l hl => hOcLθ _ ⟨?_, ?_⟩
  · have h1 : l * t⁻¹ * l⁻¹ ∈ Oc :=
      (Subgroup.mem_normalizer_iff.mp (hCOc (hLc hl)) _).mp (inv_mem ht)
    have e : t * l * t⁻¹ * l⁻¹ = t * (l * t⁻¹ * l⁻¹) := by group
    rw [e]
    exact Oc.mul_mem ht h1
  · have h1 : t * l * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hCN (hOcC ht)) l).mp hl
    exact L.mul_mem h1 (L.inv_mem hl)

end Kernel

section ThetaPart

variable {Q : Type*} [Group Q] [Finite Q]

theorem thetaCent_props (b : Q) :
    Group.IsSolvable (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set Q)))
      ∧ ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3)
          (Subgroup.centralizer ({b} : Set Q))) ∧
      Subgroup.centralizer ({b} : Set Q) ≤ Subgroup.normalizer
        ((inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set Q)) :
          Subgroup Q) : Set Q) := by
  set Cb := Subgroup.centralizer ({b} : Set Q)
  have : (aschbacherSolvableCore 3 ↥Cb).Characteristic :=
    Sec4.aschbacherSolvableCore_characteristic _
  obtain ⟨hs, -, h3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Cb) Nat.prime_three
  refine ⟨?_, ?_, ?_⟩
  · exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective Cb.subtype _)
  · rw [inSubgroup, Subgroup.card_map_of_injective Cb.subtype_injective]
    exact h3
  · exact Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)

theorem thetaAlpha_le_of_le {Ñ Θ B : Subgroup Q} [Ñ.Normal] [Θ.Normal] (hΘN : Θ ≤ Ñ)
    (hΘs : Group.IsSolvable Θ) (hΘ3 : ¬ 3 ∣ Nat.card Θ) (hB3 : ∀ β ∈ B, β ^ 3 = 1)
    (hBab : ∀ β ∈ B, ∀ γ ∈ B, β * γ = γ * β)
    (hBN : ∀ β ∈ B, ∀ n ∈ Ñ, n⁻¹ * (β * n * β⁻¹) ∈ Θ) (hB1 : ∃ b ∈ B, b ≠ 1)
    (hT : ∀ b ∈ B, b ≠ 1 →
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set Q)) ≤ Ñ) :
    thetaAlpha 3 B ≤ aschbacherSolvableCore 3 Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M := inSubgroup (aschbacherSolvableCore 3) Ñ with hM
  have : (aschbacherSolvableCore 3 ↥Ñ).Characteristic :=
    Sec4.aschbacherSolvableCore_characteristic _
  obtain ⟨hθNs, -, hθN3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Ñ) Nat.prime_three
  obtain ⟨-, -, -, hθQmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := Q) Nat.prime_three
  have hMQ : M ≤ aschbacherSolvableCore 3 Q := by
    refine hθQmax M ?_ ?_ ?_
    · rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← Subgroup.normalizer_eq_top Ñ]
      exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _
    · exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective Ñ.subtype _)
    · rw [hM, inSubgroup, Subgroup.card_map_of_injective Ñ.subtype_injective]
      exact hθN3
  have hΘnorm : ∀ X : Subgroup Q, X ≤ Subgroup.normalizer (Θ : Set Q) := fun X =>
    le_top.trans (Subgroup.normalizer_eq_top Θ).ge
  have hTM : ∀ b ∈ B, b ≠ 1 →
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set Q)) ≤ M := by
    intro b hb hb1
    set T := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set Q)) with hTdef
    obtain ⟨hTs, hT3, hCbT⟩ := thetaCent_props b
    have hTN := hT b hb hb1
    set W := T ⊔ Θ with hW
    have hWN : W ≤ Ñ := sup_le hTN hΘN
    have hb3 : IsPGroup 3 (Subgroup.zpowers b) := by
      intro x
      refine ⟨1, Subtype.ext ?_⟩
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp x.2
      rw [pow_one, Subgroup.coe_pow, ← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hB3 b hb, one_zpow, OneMemClass.coe_one]
    have hNW : Ñ ≤ Subgroup.normalizer (W : Set Q) := by
      intro n hn
      obtain ⟨m, hm, hmc⟩ := exists_mem_centralizer_of_coset (n := n) hb3 hΘ3
        (hΘnorm _) fun β hβ => hBN β ((Subgroup.zpowers_le.mpr hb) hβ) n hn
      have hmCb : m ∈ Subgroup.centralizer ({b} : Set Q) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hmc b (Subgroup.mem_zpowers b)).symm
      have hmW : m ∈ Subgroup.normalizer (W : Set Q) :=
        mem_normalizer_sup (hCbT hmCb) (hΘnorm ⊤ (Subgroup.mem_top m))
      have ht : m⁻¹ * n ∈ Θ := by
        have h1 := Θ.inv_mem hm
        rwa [mul_inv_rev, inv_inv] at h1
      have htW : m⁻¹ * n ∈ Subgroup.normalizer (W : Set Q) :=
        le_normalizer_of_le_of_le_normalizer le_sup_right (hΘnorm W) ht
      have e : n = m * (m⁻¹ * n) := by group
      rw [e]
      exact mul_mem hmW htW
    have hWs : Group.IsSolvable W := isSolvable_sup_of_le_normalizer (hΘnorm T) hTs hΘs
    have hW3 : ¬ 3 ∣ Nat.card W := by
      intro h3
      have hdvd : Nat.card W ∣ Nat.card T * Nat.card Θ := by
        have h1 := Subgroup.normal_subgroupOf_of_le_normalizer (hΘnorm T)
        have h2 := Subgroup.normal_subgroupOf_sup_of_le_normalizer (hΘnorm T)
        let e := QuotientGroup.quotientInfEquivProdNormalizerQuotient T Θ (hΘnorm T)
        have hq : Nat.card (↥(T ⊔ Θ) ⧸ Θ.subgroupOf (T ⊔ Θ)) ∣ Nat.card T := by
          rw [← Nat.card_congr e.toEquiv]
          exact Subgroup.card_quotient_dvd_card _
        have hs : Nat.card (Θ.subgroupOf (T ⊔ Θ)) = Nat.card Θ :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show Θ ≤ T ⊔ Θ from le_sup_right)).toEquiv
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Θ.subgroupOf (T ⊔ Θ)), hs]
        exact mul_dvd_mul_right hq _
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp (h3.trans hdvd) with h | h
      · exact hT3 h
      · exact hΘ3 h
    have hWθ : W.subgroupOf Ñ ≤ aschbacherSolvableCore 3 Ñ := by
      refine (solvable_prime_complement_core_characterization Nat.prime_three).2.2.2.1 _ ?_ ?_ ?_
      · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hWN).mpr hNW
      · exact Group.isSolvable_of_isSolvable_injective
          (f := (Subgroup.subgroupOfEquivOfLe hWN).toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe hWN).injective
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWN).toEquiv]
        exact hW3
    intro x hx
    exact ⟨⟨x, hTN hx⟩, hWθ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hx)), rfl⟩
  obtain ⟨b₀, hb₀, hb₀1⟩ := hB1
  refine (sup_le ?_ ?_).trans hMQ
  · refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
    obtain ⟨-, -, hCbT⟩ := thetaCent_props b
    have hBCb : B ≤ Subgroup.centralizer ({b} : Set Q) := fun β hβ =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hBab β hβ b hb)
    exact (Subgroup.le_normalizer_iff_commutator_le_left.mp (hBCb.trans hCbT)).trans
      (hTM b hb hb1)
  · exact (iInf_le_of_le b₀ (iInf_le_of_le hb₀ (iInf_le_of_le hb₀1 le_rfl))).trans
      (hTM b₀ hb₀ hb₀1)

end ThetaPart

section Lower

variable {G : Type} [Group G] [Finite G]

theorem inSubgroup_le_thetaQuotCentralizer (L : Subgroup G) :
    inSubgroup (aschbacherSolvableCore 3) L ≤ Sec4.thetaQuotCentralizer L := by
  have : (aschbacherSolvableCore 3 ↥L).Characteristic :=
    Sec4.aschbacherSolvableCore_characteristic _
  have hLθ : L ≤ Subgroup.normalizer ((inSubgroup (aschbacherSolvableCore 3) L : Subgroup G) :
      Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  intro t ht
  have htL : t ∈ L := Subgroup.map_subtype_le _ ht
  refine (mem_thetaQuotCentralizer_iff' (Subgroup.le_normalizer htL)).mpr fun l hl => ?_
  have h1 : l * t⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L :=
    (Subgroup.mem_normalizer_iff.mp (hLθ hl) _).mp (inv_mem ht)
  have e : t * l * t⁻¹ * l⁻¹ = t * (l * t⁻¹ * l⁻¹) := by group
  rw [e]
  exact mul_mem ht h1

theorem exists_mem_not_mem_thetaQuotCentralizer {A L : Subgroup G} {c : G} (hcA : c ∈ A)
    (hc3 : c ^ 3 = 1) (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hCN : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAexp : ∀ a ∈ A, a ^ 3 = 1)
    (hmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    {k : Type} [Field k] (hk : Nat.card k = 4)
    (ψ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projectiveSL 3 k)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (hcL : c ∉ L) (hstar : ¬ StarConditionAt A c) :
    ∃ x ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)),
      x ∉ Sec4.thetaQuotCentralizer L := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  apply hstar
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  have : (aschbacherSolvableCore 3 ↥L).Characteristic :=
    Sec4.aschbacherSolvableCore_characteristic _
  obtain ⟨hθs, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have hθL3 : ¬ 3 ∣ Nat.card θL := by
    rw [hθL, inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
    exact hθ3
  have hθLL : θL ≤ L := Subgroup.map_subtype_le _
  have hθLC : θL ≤ C := hθLL.trans hLc
  have hCθ : C ≤ Subgroup.normalizer (θL : Set G) :=
    hCN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hAC : A ≤ C := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hAab x hx c hcA)
  have hcC : c ∈ C := hAC hcA
  have hA3 : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hAexp a a.2)⟩
  set ρC : ↥C →* MulAut (projectiveSL 3 k) := (actL34 ψ).comp (Subgroup.inclusion hCN) with hρC
  have hρC1 : ∀ g : ↥C, ρC g = 1 ↔ (g : G) ∈ Sec4.thetaQuotCentralizer L := fun g => by
    rw [mem_thetaQuotCentralizer_iff' (hCN g.2), ← thetaQuotMulAut_eq_one_iff ⟨(g : G), hCN g.2⟩,
      ← actL34_eq_one_iff ψ]
    rfl
  have hcN : c ∈ Sec4.thetaQuotCentralizer L := by
    refine (mem_thetaQuotCentralizer_iff' (hCN hcC)).mpr fun l hl => ?_
    have hlc : l * c = c * l := Subgroup.mem_centralizer_singleton_iff.mp (hLc hl)
    have e : c * l * c⁻¹ * l⁻¹ = 1 := by rw [← hlc]; group
    rw [e]
    exact one_mem _
  have hZker : centralLine c ≤ ρC.ker := by
    rw [centralLine, Subgroup.zpowers_le, MonoidHom.mem_ker]
    exact (hρC1 _).mpr hcN
  set π : ↥C →* ↥C ⧸ centralLine c := QuotientGroup.mk' (centralLine c) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set ρQ : ↥C ⧸ centralLine c →* MulAut (projectiveSL 3 k) :=
    QuotientGroup.lift (centralLine c) ρC hZker with hρQ
  have hρQπ : ∀ g : ↥C, ρQ (π g) = ρC g := fun g => QuotientGroup.lift_mk' _ hZker g
  have hπc : ∀ g : ↥C, π g = 1 → ∃ j : ℤ, (g : G) = c ^ j := by
    intro g hg
    have h1 : g ∈ centralLine c := (QuotientGroup.eq_one_iff g).mp hg
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h1
    exact ⟨j, by rw [← hj, Subgroup.coe_zpow]⟩
  set Ñ := ρQ.ker with hÑ
  set Θ := (θL.subgroupOf C).map π with hΘ
  set B := (A.subgroupOf C).map π with hB
  have hθLn : (θL.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hθLC).mpr hCθ
  have hΘn : Θ.Normal := hθLn.map π hπs
  have hΘN : Θ ≤ Ñ := by
    rintro _ ⟨t, ht, rfl⟩
    rw [MonoidHom.mem_ker, hρQπ, hρC1]
    exact inSubgroup_le_thetaQuotCentralizer L (Subgroup.mem_subgroupOf.mp ht)
  have hΘs : Group.IsSolvable Θ := by
    have : Group.IsSolvable (θL.subgroupOf C) := by
      have : Group.IsSolvable θL :=
        Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective L.subtype _)
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hθLC).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hθLC).injective
    exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective π _)
  have hΘ3 : ¬ 3 ∣ Nat.card Θ := by
    intro h3
    apply hθL3
    have h1 := h3.trans (Subgroup.card_map_dvd (θL.subgroupOf C) π)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hθLC).toEquiv] at h1
  have hB3 : ∀ β ∈ B, β ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, hAexp _ (Subgroup.mem_subgroupOf.mp ha), OneMemClass.coe_one])
    rw [this, map_one]
  have hBab : ∀ β ∈ B, ∀ γ ∈ B, β * γ = γ * β := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAab _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp ha'))
  have hBN : ∀ β ∈ B, ∀ n ∈ Ñ, n⁻¹ * (β * n * β⁻¹) ∈ Θ := by
    rintro _ ⟨a, ha, rfl⟩ n hn
    obtain ⟨g, rfl⟩ := hπs n
    rw [MonoidHom.mem_ker, hρQπ, hρC1] at hn
    have hgi : (g : G)⁻¹ ∈ Sec4.thetaQuotCentralizer L := inv_mem hn
    have h1 := commutator_mem_theta_of_mem hAc hAab hcA (C.inv_mem g.2)
      ((mem_thetaQuotCentralizer_iff' (hCN (C.inv_mem g.2))).mp hgi)
      (Subgroup.mem_subgroupOf.mp ha)
    refine ⟨g⁻¹ * (a * g * a⁻¹), Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
    have e : ((g⁻¹ * (a * g * a⁻¹) : ↥C) : G) =
        (g : G)⁻¹ * (a : G) * (g : G)⁻¹⁻¹ * (a : G)⁻¹ := by simp [mul_assoc]
    rw [e]
    exact h1
  have hB1 : ∃ b ∈ B, b ≠ 1 := by
    have hne : (A ⊓ L).subgroupOf (A ⊓ L) ≠ ⊥ := by
      intro hbot
      have h1 := congrArg (fun H : Subgroup ↥(A ⊓ L) => Nat.card H) hbot
      simp only [Subgroup.card_bot] at h1
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_refl (A ⊓ L))).toEquiv, h9] at h1
      norm_num at h1
    obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext (Subtype.ext h))
    refine ⟨π ⟨a, hAC a.2.1⟩, ⟨⟨a, hAC a.2.1⟩, Subgroup.mem_subgroupOf.mpr a.2.1, rfl⟩, ?_⟩
    intro h1
    obtain ⟨j, hj⟩ := hπc _ h1
    have hbot := Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three
      (orderOf_eq_prime hc3 (fun h => hcL (h ▸ L.one_mem))) hcL
    have hmem : (a : G) ∈ L ⊓ Subgroup.zpowers c :=
      ⟨a.2.2, Subgroup.mem_zpowers_iff.mpr ⟨j, hj.symm⟩⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact ha1' hmem
  set E := (((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))).map
    ψ.toMonoidHom with hE
  have hE3 : IsPGroup 3 ((A ⊓ L).subgroupOf L) := fun x => by
    obtain ⟨n, hn⟩ := hA3 ⟨(x : G), (Subgroup.mem_subgroupOf.mp x.2).1⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩
  have hE9 : Nat.card E = 9 := by
    rw [hE, Subgroup.card_map_of_injective ψ.injective,
      Sec4.Item424Proof.card_map_mk_of_isPGroup hE3,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, h9]
  have hBE : ∀ β ∈ B, ∃ e ∈ E, ρQ β = MulAut.conj e := by
    rintro _ ⟨a, ha, rfl⟩
    have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
    rw [hAc, sup_comm] at haA
    obtain ⟨β, hβ, j, hβj⟩ :=
      exists_eq_mul_zpow_of_mem_sup (B := A ⊓ L) (fun β hβ => hAab β hβ.1 c hcA) haA
    have hβC : β ∈ C := hAC hβ.1
    have ha' : a = ⟨β, hβC⟩ * ⟨c, hcC⟩ ^ j := Subtype.ext (by
      rw [hβj, Subgroup.coe_mul, Subgroup.coe_zpow])
    have hρc : ρC ⟨c, hcC⟩ = 1 := (hρC1 _).mpr hcN
    refine ⟨ψ.toMonoidHom (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨β, hβ.2⟩),
      ⟨_, ⟨⟨β, hβ.2⟩, Subgroup.mem_subgroupOf.mpr hβ, rfl⟩, rfl⟩, ?_⟩
    rw [hρQπ, ha', map_mul, map_zpow, hρc, one_zpow, mul_one]
    exact actL34_of_mem ψ hβ.2 (hCN hβC)
  have hT : ∀ b ∈ B, b ≠ 1 →
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set (↥C ⧸ centralLine c)))
        ≤ Ñ := by
    intro b hb _
    set T := inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({b} : Set (↥C ⧸ centralLine c))) with hTdef
    obtain ⟨-, hT3, hCbT⟩ := thetaCent_props b
    have hBCb : B ≤ Subgroup.centralizer ({b} : Set (↥C ⧸ centralLine c)) := fun β hβ =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hBab β hβ b hb)
    have hBT : B ≤ Subgroup.normalizer (T : Set (↥C ⧸ centralLine c)) := hBCb.trans hCbT
    have hcomm : ⁅T, B⁆ ≤ Ñ := by
      have hR3 : ¬ 3 ∣ Nat.card (T.map ρQ) := fun h3 => hT3 (h3.trans (Subgroup.card_map_dvd T ρQ))
      have hER : ∀ e ∈ E, MulAut.conj e ∈
          Subgroup.normalizer ((T.map ρQ : Subgroup (MulAut (projectiveSL 3 k))) :
            Set (MulAut (projectiveSL 3 k))) := by
        rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
        have hlA : (l : G) ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp hl
        have hlC : (l : G) ∈ C := hLc l.2
        have e1 : MulAut.conj (ψ.toMonoidHom (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) l))
            = ρQ (π ⟨l, hlC⟩) := by
          rw [hρQπ]
          exact (actL34_of_mem ψ l.2 (hCN hlC)).symm
        rw [e1]
        refine Subgroup.le_normalizer_map ρQ ⟨π ⟨l, hlC⟩, hBT ?_, rfl⟩
        exact ⟨⟨l, hlC⟩, Subgroup.mem_subgroupOf.mpr hlA.1, rfl⟩
      rw [Subgroup.commutator_le]
      intro t ht β hβ
      rw [MonoidHom.mem_ker]
      obtain ⟨e, he, hβe⟩ := hBE β hβ
      have hfix : ρQ t e = e :=
        KFacts.L34.forall_apply_eq_of_invariant hk hE9 hR3 hER ⟨t, ht, rfl⟩ he
      rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hβe,
        KFacts.mul_mulAutConj_mul_inv, hfix, mul_inv_cancel]
    have hcent : T ⊓ Subgroup.centralizer (B : Set (↥C ⧸ centralLine c)) ≤ Ñ := by
      rintro y ⟨hyT, hyB⟩
      rw [MonoidHom.mem_ker]
      have hy3 : ¬ 3 ∣ orderOf y := fun h => hT3 (h.trans (Subgroup.orderOf_dvd_natCard T hyT))
      have hker : ∀ z : ↥C, π z = 1 → z ^ 3 = 1 := by
        intro z hz
        obtain ⟨j, hj⟩ := hπc z hz
        refine Subtype.ext ?_
        rw [Subgroup.coe_pow, hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
          hc3, one_zpow, OneMemClass.coe_one]
      obtain ⟨x, hxπ, hx3⟩ := exists_lift_not_three_dvd π hπs hker hy3
      have hxA : (x : G) ∈ Subgroup.centralizer (A : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have hxc : (x : G) * c = c * x := Subgroup.mem_centralizer_singleton_iff.mp x.2
        have hd : (x : G) * a * (x : G)⁻¹ * a⁻¹ ∈ Subgroup.zpowers c := by
          set a' : ↥C := ⟨a, hAC ha⟩
          have hβ : π a' ∈ B := ⟨a', Subgroup.mem_subgroupOf.mpr ha, rfl⟩
          have hc' : π a' * y = y * π a' := Subgroup.mem_centralizer_iff.mp hyB _ hβ
          have h1 : π (x * a' * x⁻¹ * a'⁻¹) = 1 := by
            rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxπ, ← hc']
            group
          obtain ⟨j, hj⟩ := hπc _ h1
          refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
          rw [← hj]
          simp [a']
        exact (commute_of_commutator_mem_zpowers hc3 hxc (by rwa [Subgroup.orderOf_coe]) hd).symm
      have hxX : (x : G) ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) :=
        Sec14.inf_centralizer_le_xA hmax (Q := Subgroup.zpowers (x : G))
          (by rw [Nat.card_zpowers, Subgroup.orderOf_coe]; exact hx3)
          ⟨Subgroup.mem_zpowers _, hxA⟩
      rw [← hxπ, hρQπ]
      exact (hρC1 x).mpr (hall _ hxX)
    have hBp : IsPGroup 3 B := fun β => ⟨1, Subtype.ext (by simpa using hB3 β β.2)⟩
    rw [CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization 3
      Nat.prime_three B T hBp hT3 hBT]
    exact sup_le hcomm hcent
  exact thetaAlpha_le_of_le hΘN hΘs hΘ3 hB3 hBab hBN hB1 hT

end Lower

end Res4L34

open Res4L34

theorem step142L34Index : Step142L34Index := by
  intro G _ _ A c L h hL34
  obtain ⟨φ⟩ := hL34
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  obtain ⟨hS, hZS⟩ := isPerfect_center_projSL 2 2 (by norm_num) (by norm_num)
  obtain ⟨hcL, h9, -, ⟨ψ₀⟩⟩ := facts_of_prod hD hS hZS φ
  have hAc := Item148PtRes2.eq_zpowers_sup_of_card hD hcL h9
  have hk := KFacts.L34.card_galoisField_two_two
  set ψ := ψ₀.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)) with hψ
  have h3L : 3 ∣ Nat.card L :=
    three_dvd_card_of_types148 (h.chosen136.2 c hD.zpowers_mem_omegaA L hD.mem_lA).1
  have hCN := centralizer_le_normalizer_of_three_dvd h h3L
  have hLc := hD.le_centralizer
  have hcA := hD.mem_A
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
  have hAexp : ∀ a ∈ A, a ^ 3 = 1 := hD.isElemAbelian.2
  have hA3 : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hAexp a a.2)⟩
  have hmax := Sec14Std.maximal_isElemAbelian h
  have hc3 : c ^ 3 = 1 := hAexp c hcA
  have hstar : ¬ StarConditionAt A c := (zpowers_mem_omegaA_iff.mp hD.zpowers_mem_omegaA).2.2
  have hAC : A ≤ Subgroup.centralizer ({c} : Set G) := hD.A_le_centralizer
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set O := pPrimeCoreOf 3 H with hO
  set X := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hX
  have hXA : X ≤ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _
  have hXC : X ≤ C := hXA.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcA))
  have hCH : C ≤ H := centralizer_singleton_le_normalizer_zpowers c
  have hXO : X ≤ Subgroup.normalizer (O : Set G) :=
    (hXC.trans hCH).trans (le_normalizer_pPrimeCoreOf 3 H)
  have hOC : O ⊓ C ≤ pPrimeCoreOf 3 C := by
    refine le_pPrimeCoreOf inf_le_right ?_ ?_
    · refine Item148PtRes2.le_normalizer_of_conj_mem' fun g hg y hy => ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp ((le_normalizer_pPrimeCoreOf 3 H) (hCH hg)) y).mp
          hy.1
      · exact C.mul_mem (C.mul_mem hg hy.2) (C.inv_mem hg)
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (coprime_card_pPrimeCoreOf 3 H)
  have hiff : ∀ x ∈ X, x ∈ O ↔ x ∈ Sec4.thetaQuotCentralizer L := by
    intro x hx
    constructor
    · intro hxO
      exact pPrimeCoreOf_le_thetaQuotCentralizer hLc hCN hAC hA3 ψ₀ h9 (hOC ⟨hxO, hXC hx⟩)
    · intro hxN
      exact Item148PtRes2.pPrimeCoreOf_centralizer_le c
        (mem_pPrimeCoreOf_of_mem_thetaQuotCentralizer hLc hCN hAc hAab hcA hA3 hx (hXC hx) hxN)
  set f : ↥X →* MulAut (projectiveSL 3 (GaloisField 2 2)) :=
    (actL34 ψ).comp (Subgroup.inclusion (hXC.trans hCN)) with hf
  have hf1 : ∀ x : ↥X, f x = 1 ↔ (x : G) ∈ Sec4.thetaQuotCentralizer L := fun x => by
    rw [mem_thetaQuotCentralizer_iff' (hCN (hXC x.2)),
      ← thetaQuotMulAut_eq_one_iff ⟨(x : G), hCN (hXC x.2)⟩, ← actL34_eq_one_iff ψ]
    rfl
  have hfker : f.ker = O.subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hf1, hiff x x.2]
  set E := (((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))).map
    ψ.toMonoidHom with hE
  have hE3 : IsPGroup 3 ((A ⊓ L).subgroupOf L) := fun x => by
    obtain ⟨n, hn⟩ := hA3 ⟨(x : G), (Subgroup.mem_subgroupOf.mp x.2).1⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩
  have hE9 : Nat.card E = 9 := by
    rw [hE, Subgroup.card_map_of_injective ψ.injective,
      Sec4.Item424Proof.card_map_mk_of_isPGroup hE3,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, h9]
  have hR3 : ¬ 3 ∣ Nat.card f.range := by
    intro h3
    have h1 : Nat.card f.range ∣ Nat.card X := by
      rw [MonoidHom.range_eq_map]
      exact (Subgroup.card_map_dvd ⊤ f).trans (by rw [Subgroup.card_top])
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (coprime_card_pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) (h3.trans h1)
  have hER : ∀ e ∈ E, MulAut.conj e ∈ Subgroup.normalizer
      ((f.range : Subgroup (MulAut (projectiveSL 3 (GaloisField 2 2)))) :
        Set (MulAut (projectiveSL 3 (GaloisField 2 2)))) := by
    rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    have hlA : (l : G) ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp hl
    have hlN : (l : G) ∈ Subgroup.normalizer (L : Set G) := hCN (hLc l.2)
    have e1 : MulAut.conj (ψ.toMonoidHom (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) l)) =
        actL34 ψ ⟨l, hlN⟩ := (actL34_of_mem ψ l.2 hlN).symm
    rw [e1, MonoidHom.range_comp]
    refine Subgroup.le_normalizer_map (actL34 ψ) ⟨⟨l, hlN⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, rfl⟩
      have hx := hXA x.2
      have hcomm : (l : G) * x = x * l := (Subgroup.mem_centralizer_iff.mp hx _ hlA.1)
      refine ⟨x, Subtype.ext ?_⟩
      change (x : G) = (l : G) * x * (l : G)⁻¹
      rw [hcomm]; group
    · rintro ⟨x, hxy⟩
      have hx := hXA x.2
      have hcomm : (l : G) * x = x * l := (Subgroup.mem_centralizer_iff.mp hx _ hlA.1)
      refine ⟨x, Subtype.ext ?_⟩
      have h1 := congrArg Subtype.val hxy
      change (x : G) = (l : G) * y * (l : G)⁻¹ at h1
      change (x : G) = y
      have : (y : G) = (l : G)⁻¹ * x * l := by rw [h1]; group
      rw [this, mul_assoc, ← hcomm]; group
  have hrange : Nat.card f.range = 2 := by
    obtain ⟨x, hx, hxN⟩ := exists_mem_not_mem_thetaQuotCentralizer hcA hc3 hLc hCN hAc hAab
      hAexp hmax hk ψ h9 hcL hstar
    rcases KFacts.L34.eq_bot_or_eq_zpowers_graphField hk hE9 hR3 hER with hbot |
      ⟨τ, hτ, hτ1, hττ, -⟩
    · exfalso
      have h1 : f ⟨x, hx⟩ ∈ f.range := ⟨⟨x, hx⟩, rfl⟩
      rw [hbot, Subgroup.mem_bot, hf1] at h1
      exact hxN h1
    · rw [hτ, Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hττ) hτ1]
  have hidx : (O.subgroupOf X).index = 2 := by
    rw [← hfker, Subgroup.index_ker, hrange]
  have := Subgroup.normal_subgroupOf_of_le_normalizer hXO
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hXO
  let e := QuotientGroup.quotientInfEquivProdNormalizerQuotient X O hXO
  have hq : (O.subgroupOf (X ⊔ O)).index = (O.subgroupOf X).index := by
    rw [Subgroup.index, Subgroup.index, Nat.card_congr e.toEquiv]
  have hs : Nat.card (O.subgroupOf (X ⊔ O)) = Nat.card O :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show O ≤ X ⊔ O from le_sup_right)).toEquiv
  have hcard := Subgroup.card_mul_index (O.subgroupOf (X ⊔ O))
  rw [hs, hq, hidx] at hcard
  rw [sup_comm, ← hcard, mul_comm]

theorem step142LowerS14_of_gen (hGen : Step142LowerGen) : Step142LowerS14 :=
  step142LowerS14_of hGen step142L34Index

end CFSG.RankThree.PartTwo.Sec14
