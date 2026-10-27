module

public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6HeisMain
public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6A

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

open CFSG.Quasithin.G11

namespace SmD6

open CntLin

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {Γ A : Subgroup (GLV V)}

omit [Finite V] in
theorem sq_add_add_eq_zero {e : GLV V} (he3 : e ^ 3 = 1) (hfpf : ∀ v, e v = v → v = 0) (v : V) :
    e (e v) + e v + v = 0 := by
  apply hfpf
  have h3 : e (e (e v)) = v := by
    have := congrArg (fun f : GLV V => f v) he3
    simpa [pow_succ] using this
  rw [map_add, map_add, h3]
  abel

omit [Finite V] in
theorem sq_eq_of_add_add_eq_zero {e : GLV V} (h : ∀ v, e (e v) + e v + v = 0) (v : V) :
    e (e v) = e v + v := by
  have := h v
  calc e (e v) = -(e v + v) := eq_neg_of_add_eq_zero_left (by rwa [add_assoc] at this)
    _ = e v + v := zmod2_neg _

omit [Finite V] in
theorem eq_of_fpf_commuting {a b : GLV V} (hab : a * b = b * a) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (hab3 : (a * b) ^ 3 = 1) (hfa : ∀ v, a v = v → v = 0) (hfb : ∀ v, b v = v → v = 0)
    (hfab : ∀ v, (a * b) v = v → v = 0) : a = b := by
  have Ea := sq_eq_of_add_add_eq_zero (sq_add_add_eq_zero ha3 hfa)
  have Eb := sq_eq_of_add_add_eq_zero (sq_add_add_eq_zero hb3 hfb)
  have Eab := sq_add_add_eq_zero hab3 hfab
  refine LinearEquiv.ext fun v => ?_
  have hcomm : ∀ u, b (a u) = a (b u) := fun u => (comm_apply hab u).symm
  have h1 : (a * b) ((a * b) v) = a (a (b v)) + a (a v) := by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hcomm (b v), Eb v, map_add, map_add]
  have h2 := Eab v
  rw [h1, Ea (b v), Ea v, LinearEquiv.mul_apply] at h2
  set x := a (b v)
  set y := b v
  set z := a v
  have h3 : (x + y + (z + v)) + x + v = (x + x) + (v + v) + (y + z) := by abel
  rw [h3, zmod2_add_self, zmod2_add_self, zero_add, zero_add] at h2
  have h4 : y = z := by
    calc y = -z := eq_neg_of_add_eq_zero_left h2
      _ = z := zmod2_neg z
  exact h4.symm

theorem Ctx.nonabelian_of_simple (hC : Ctx Γ A)
    (hs : ∀ U : Submodule (ZMod 2) V, Invariant (CFSG.Open.pCoreOf 3 Γ) U → U = ⊥ ∨ U = ⊤) :
    ∃ u ∈ CFSG.Open.pCoreOf 3 Γ, ∃ v ∈ CFSG.Open.pCoreOf 3 Γ, u * v ≠ v * u := by
  by_contra hab
  push Not at hab
  obtain ⟨x₀, x₁, a₀, a₁, hx₀, hx₁, -, -, h30, h31, hne0, hne1, hcomm, -, -, -, -, -, -, hne⟩ :=
    hC.exists_frame_elements
  have hfpf : ∀ h ∈ CFSG.Open.pCoreOf 3 Γ, h ≠ 1 → ∀ v, h v = v → v = 0 := by
    intro h hh hne1 v hv
    have hinv : Invariant (CFSG.Open.pCoreOf 3 Γ) (fixSp V h ⊤) := fun p hp u hu =>
      fixSp_invariant (hab p hp h hh) (fun _ _ => Submodule.mem_top) u hu
    rcases hs _ hinv with h0 | h1
    · have : v ∈ fixSp V h ⊤ := mem_fixSp.2 ⟨Submodule.mem_top, hv⟩
      rw [h0] at this
      exact (Submodule.mem_bot (ZMod 2)).1 this
    · exfalso
      apply hne1
      ext u
      have : u ∈ fixSp V h ⊤ := by rw [h1]; exact Submodule.mem_top
      exact (mem_fixSp.1 this).2
  have hne01 : x₀ * x₁ ≠ 1 := by
    intro h
    apply hne
    have : x₁ = x₀⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x₀)
  have hP := (CFSG.Open.pCoreOf 3 Γ).mul_mem hx₀ hx₁
  have hc : Commute x₀ x₁ := hcomm
  have h3 : (x₀ * x₁) ^ 3 = 1 := by rw [hc.mul_pow, h30, h31, one_mul]
  have heq := eq_of_fpf_commuting hcomm h30 h31 h3 (hfpf x₀ hx₀ hne0) (hfpf x₁ hx₁ hne1)
    (hfpf _ hP hne01)
  exact hne (heq ▸ Subgroup.mem_zpowers x₀)

omit [Finite V] in
theorem commutative_of_card_le_nine {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 3 Q)
    (h : Nat.card Q ≤ 9) (a b : Q) : a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hk2 : k ≤ 2 := by
    by_contra hlt
    have h3 : 3 ≤ k := by omega
    have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) h3
    omega
  interval_cases k
  · have : Subsingleton Q := (Nat.card_eq_one_iff_unique.1 (by simpa using hk)).1
    exact Subsingleton.elim _ _
  · have : IsCyclic Q := isCyclic_of_prime_card (p := 3) (by simpa using hk)
    exact mul_comm' a b
  · have : IsMulCommutative Q := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hk
    exact mul_comm' a b

theorem Ctx.card_eq_27 (hC : Ctx Γ A)
    (hnc : ∃ u ∈ CFSG.Open.pCoreOf 3 Γ, ∃ v ∈ CFSG.Open.pCoreOf 3 Γ, u * v ≠ v * u) :
    Nat.card ↥(CFSG.Open.pCoreOf 3 Γ) = 27 := by
  have h27 := hC.card_le
  by_contra hne
  have h9 : Nat.card ↥(CFSG.Open.pCoreOf 3 Γ) ≤ 9 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := (isPGroup_pCoreOf 3 Γ).exists_card_eq
    have hk3 : k ≤ 2 := by
      by_contra hlt
      have h3 : 3 ≤ k := by omega
      have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) h3
      omega
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk3
      _ = 9 := by norm_num
  obtain ⟨u, hu, v, hv, huv⟩ := hnc
  exact huv (congrArg Subtype.val (commutative_of_card_le_nine (isPGroup_pCoreOf 3 Γ) h9
    ⟨u, hu⟩ ⟨v, hv⟩))


omit [Finite V] in
instance pCoreOf_normal_subgroupOf (p : ℕ) (Γ : Subgroup (GLV V)) :
    ((CFSG.Open.pCoreOf p Γ).subgroupOf Γ).Normal where
  conj_mem n hn g := by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact pCoreOf_normal_conj p Γ g g.2 n hn


theorem Ctx.not_three_dvd_index (hC : Ctx Γ A) {P' : Subgroup ↥Γ} (hP' : Nat.card P' = 27) :
    ¬ 3 ∣ P'.index := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hdvd
  let S : Sylow 3 ↥Γ := default
  have hS := S.card_eq_multiplicity
  have hSle : Nat.card (S : Subgroup ↥Γ) ≤ 27 := by
    have := hC.three ((S : Subgroup ↥Γ).map Γ.subtype) (Subgroup.map_subtype_le _)
      (S.isPGroup'.map Γ.subtype)
    rwa [Subgroup.card_map_of_injective Γ.subtype_injective] at this
  have hΓcard : Nat.card ↥Γ = 27 * P'.index := by rw [← hP', Subgroup.card_mul_index]
  have h81 : 3 ^ 4 ∣ Nat.card ↥Γ := by
    rw [hΓcard, show (3 : ℕ) ^ 4 = 27 * 3 by norm_num]
    exact mul_dvd_mul_left 27 hdvd
  have hv : 4 ≤ (Nat.card ↥Γ).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').1 h81
  have : 3 ^ 4 ≤ Nat.card (S : Subgroup ↥Γ) := by
    rw [hS]
    exact Nat.pow_le_pow_right (by norm_num) hv
  omega

omit [Finite V] in
theorem Ctx.four_dvd_index (hC : Ctx Γ A) :
    4 ∣ ((CFSG.Open.pCoreOf 3 Γ).subgroupOf Γ).index := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P' : Subgroup ↥Γ := (CFSG.Open.pCoreOf 3 Γ).subgroupOf Γ with hP'
  set A' : Subgroup ↥Γ := A.subgroupOf Γ with hA'
  have hAdisj : Disjoint A (CFSG.Open.pCoreOf 3 Γ) :=
    IsPGroup.disjoint_of_ne 2 3 (by norm_num) A _ (isPGroup_of_isElemAbelian hC.hyp.A_elem)
      (isPGroup_pCoreOf 3 Γ)
  let f : A' →* ↥Γ ⧸ P' := (QuotientGroup.mk' P').comp A'.subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : (a : ↥Γ) ∈ P' := (QuotientGroup.eq_one_iff _).1 ha
    have h2 : (((a : ↥Γ)) : GLV V) ∈ CFSG.Open.pCoreOf 3 Γ := h1
    have h3 : (((a : ↥Γ)) : GLV V) ∈ A := a.2
    have : (((a : ↥Γ)) : GLV V) = 1 := Subgroup.disjoint_def.1 hAdisj h3 h2
    exact Subtype.ext (Subtype.ext this)
  have hdvd := Subgroup.card_dvd_of_injective f hinj
  have hcardA' : Nat.card A' = 4 := by
    rw [hA', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC.hyp.A_le).toEquiv, hC.hyp.A_card]
    norm_num
  rw [hcardA'] at hdvd
  exact hdvd


theorem Ctx.concl3Partial_of_simple (hC : Ctx Γ A)
    (hs : ∀ U : Submodule (ZMod 2) V, Invariant (CFSG.Open.pCoreOf 3 Γ) U → U = ⊥ ∨ U = ⊤) :
    G112Concl3Partial Γ := by
  have hnc := hC.nonabelian_of_simple hs
  have hP27 : Nat.card ↥(CFSG.Open.pCoreOf 3 Γ) = 27 := hC.card_eq_27 hnc
  obtain ⟨x₀, x₁, a₀, a₁, hx₀, hx₁, ha₀A, ha₁A, h30, h31, hne0, -, hcomm, ha₀, ha₁, hax₀, hax₁, -, -,
    hne⟩ := hC.exists_frame_elements
  have haP : ∀ a ∈ A, ∀ g ∈ CFSG.Open.pCoreOf 3 Γ, a * g * a⁻¹ ∈ CFSG.Open.pCoreOf 3 Γ :=
    fun a ha g hg => pCoreOf_normal_conj 3 Γ a (hC.hyp.A_le ha) g hg
  have hexp : ∀ y ∈ CFSG.Open.pCoreOf 3 Γ, y ^ 3 = 1 :=
    exp_three_of_dihedral_frame hP27 hx₀ hx₁ h30 h31 hne0 hne hnc hcomm ha₀ ha₁ (haP a₀ ha₀A)
      (haP a₁ ha₁A) hax₀ hax₁
  set P' : Subgroup ↥Γ := (CFSG.Open.pCoreOf 3 Γ).subgroupOf Γ with hP'
  have hcard : Nat.card P' = 27 := by
    rw [hP', Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 3 Γ)).toEquiv, hP27]
  have hnc' : ∃ u ∈ P', ∃ v ∈ P', u * v ≠ v * u := by
    obtain ⟨u, hu, v, hv, huv⟩ := hnc
    exact ⟨⟨u, pCoreOf_le 3 Γ hu⟩, hu, ⟨v, pCoreOf_le 3 Γ hv⟩, hv,
      fun h => huv (congrArg Subtype.val h)⟩
  have hexp' : ∀ x : ↥P', x ^ 3 = 1 := fun x =>
    Subtype.ext (Subtype.ext (hexp x.1.1 x.2))
  have hcent : ∀ g : ↥Γ, (∀ x ∈ P', g * x = x * g) → g ∈ P' := by
    intro g hg
    have : (g : GLV V) ∈ CFSG.Open.pCoreOf 3 Γ := by
      refine hC.mem_pCoreOf_of_centralizes g.2 fun x hx => ?_
      have := hg ⟨x, pCoreOf_le 3 Γ hx⟩ hx
      exact congrArg Subtype.val this
    exact this
  have hdvd48 := index_dvd_forty_eight P' hcard hnc' hcent
  have h3 := hC.not_three_dvd_index hcard
  have hcop : Nat.Coprime P'.index 3 :=
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3))
  have h16 : P'.index ∣ 16 := by
    have : P'.index ∣ 16 * 3 := by simpa using hdvd48
    exact hcop.dvd_of_dvd_mul_right this
  refine ⟨hC.hd, P', inferInstance, ?_, hcard, hexp', h16, hC.four_dvd_index⟩
  obtain ⟨u, hu, v, hv, huv⟩ := hnc'
  exact isExtraspecial_three_of_card_27 (Q := ↥P') hcard
    ⟨⟨u, hu⟩, ⟨v, hv⟩, fun h => huv (congrArg Subtype.val h)⟩ hexp'


theorem Ctx.concl3_of_simple (hC : Ctx Γ A)
    (hs : ∀ U : Submodule (ZMod 2) V, Invariant (CFSG.Open.pCoreOf 3 Γ) U → U = ⊥ ∨ U = ⊤) :
    G112Concl3 Γ := by
  obtain ⟨hd, P, hPn, hPe, hPc, hPx, hPi, hP4⟩ := hC.concl3Partial_of_simple hs
  exact ⟨hd, P, hPn, hPe, hPc, hPx, hPi, hP4, SmD6Heis.exists_sylow_semidihedral_of_core hd P hPn
    hPe hPc hPx hPi hC.card_le hs hC.hyp.A_le hC.hyp.A_elem
    (by rw [hC.hyp.A_card]; norm_num)⟩


end SmD6

end CFSG.Quasithin.SzN31
