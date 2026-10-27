module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KUn4M
public import CFSG.RankThree.PartTwo.Sec21.Hering214KGen
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitzUE
public import CFSG.Models.PGLSimple
public import CFSG.RankThree.GF2n.Stroth80.FieldAut
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartTwo.Sec21.Hering214KNine

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Assembly (IsElemAbelian)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU)
open CFSG.Assembly.RankThreeEven (projSU)

section Un4

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem un4_hq : ¬ (4 = 3 ∧ 2 ^ f = 2) := by omega

theorem coprime_four_pow_two_add_one (hf : 1 ≤ f) : Nat.Coprime 4 (2 ^ f + 1) := by
  have h2 : Odd (2 ^ f + 1) := by
    apply Even.add_one
    exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have h1 : Nat.Coprime 2 (2 ^ f + 1) := Nat.coprime_two_left.mpr h2
  simpa using h1.pow_left 2

theorem normOneScalars_four_eq_bot (hf : 1 ≤ f) :
    normOneScalars h (gramSU h (Cid1 4 K)) 4 = ⊥ := by
  have hcop := coprime_four_pow_two_add_one hf
  rw [eq_bot_iff]
  rintro z ⟨c, hcN, hc4, hz⟩
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  have hc : c ^ (2 ^ f + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ, ← h.bar_apply (c : K)]
    simpa [UnitaryFieldData.norm, mul_comm] using hcN
  have : c = 1 := by
    have := pow_gcd_eq_one.2 ⟨hc4, hc⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
  rw [hz, this]
  simp

@[expose] noncomputable def eTS (hf : 1 ≤ f) : primeFormP h (Cid1 4 K) ≃* gramSU h (Cid1 4 K) :=
  (QuotientGroup.quotientMulEquivOfEq (normOneScalars_four_eq_bot h hf)).trans
    QuotientGroup.quotientBot

theorem eTS_mk (hf : 1 ≤ f) (g : gramSU h (Cid1 4 K)) :
    eTS h hf (g : primeFormP h (Cid1 4 K)) = g := rfl

noncomputable def θ4 : MulAut (primeFormP h (Cid1 4 K)) →* (K ≃+* K) :=
  primeFormFieldFactor h (isPrimeFormGram_one (n := 4) (K := K)) (by norm_num) (un4_hq (f := f))

theorem θ4_ker_le_inner (hf : 1 ≤ f) : (θ4 h).ker ≤
    (MulAut.conj : primeFormP h (Cid1 4 K) →* MulAut (primeFormP h (Cid1 4 K))).range := by
  classical
  haveI : Finite K := h.finite
  obtain ⟨-, -, hcard, -⟩ := unitary_full_diagonal_outer_order h (n := 4) (by norm_num)
    (un4_hq (f := f))
  rw [Nat.Coprime.gcd_eq_one (coprime_four_pow_two_add_one hf)] at hcard
  have hker : (θ4 h).ker = primeFormD h (Cid1 4 K) := ker_primeFormFieldFactor h _ _ _
  have htop : (inner (primeFormP h (Cid1 4 K))).subgroupOf (primeFormD h (Cid1 4 K)) = ⊤ := by
    rw [← Subgroup.index_eq_one, Subgroup.index_eq_card]
    exact hcard
  intro α hα
  rw [hker] at hα
  have : (⟨α, hα⟩ : primeFormD h (Cid1 4 K)) ∈
      (inner (primeFormP h (Cid1 4 K))).subgroupOf (primeFormD h (Cid1 4 K)) := by
    rw [htop]; trivial
  exact this

theorem fieldSU_eq_iff (σ : K ≃+* K) (s : gramSU h (Cid1 4 K)) :
    primeFormFieldSU h (isPrimeFormGram_one (n := 4) (K := K)) σ s = s ↔
      ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map σ =
        ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  constructor
  · intro hs
    have := congrArg
      (fun x : gramSU h (Cid1 4 K) => ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hs
    simpa [primeFormFieldSU, coe_glAut] using this
  · intro hm
    apply Subtype.ext
    apply Units.ext
    simpa [primeFormFieldSU, coe_glAut] using hm

theorem eTS_field (hf : 1 ≤ f) (σ : K ≃+* K) (x : primeFormP h (Cid1 4 K)) :
    eTS h hf (primeFormFieldHom h (isPrimeFormGram_one (n := 4) (K := K)) σ x) =
      primeFormFieldSU h (isPrimeFormGram_one (n := 4) (K := K)) σ (eTS h hf x) := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    change eTS h hf (primeFormFieldAut h (isPrimeFormGram_one (n := 4) (K := K)) σ
      (g : primeFormP h (Cid1 4 K))) = _
    rw [primeFormFieldAut_mk, eTS_mk, eTS_mk]

theorem conj_eTS_symm (hf : 1 ≤ f) (z : primeFormP h (Cid1 4 K)) (x : gramSU h (Cid1 4 K)) :
    z * (eTS h hf).symm x * z⁻¹ = (eTS h hf).symm (eTS h hf z * x * (eTS h hf z)⁻¹) := by
  rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]

theorem eInvFour_un4_inner {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) (hωb : h.bar ω = ω)
    (hf : 1 ≤ f) (hZ : Subgroup.center (primeFormP h (Cid1 4 K)) = ⊥)
    {Ē : Subgroup (MulAut (primeFormP h (Cid1 4 K)))} (hE3 : IsElemAbelian 3 Ē)
    (hE9 : Nat.card Ē = 9)
    (hrange : Ē ≤ (MulAut.conj : primeFormP h (Cid1 4 K) →*
      MulAut (primeFormP h (Cid1 4 K))).range) : EInvFour (primeFormP h (Cid1 4 K)) Ē := by
  classical
  have hinj : Function.Injective (MulAut.conj : primeFormP h (Cid1 4 K) →*
      MulAut (primeFormP h (Cid1 4 K))) := conj_injective_of_mulEquiv (MulEquiv.refl _) hZ
  haveI : Finite Ē := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial Ē := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨σ₀, hσ₀E⟩, hne⟩ := exists_ne (1 : Ē)
  have hσ₀1 : σ₀ ≠ 1 := fun e => hne (Subtype.ext e)
  obtain ⟨τ₀, hτ₀E, hτ₀⟩ := exists_not_mem_zpowers hE3 hE9 hσ₀E hσ₀1
  obtain ⟨z₁, hz₁⟩ := hrange hσ₀E
  obtain ⟨z₂, hz₂⟩ := hrange hτ₀E
  have hz₁3 : z₁ ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hz₁, map_one]
    exact hE3.2 _ hσ₀E
  have hz₂3 : z₂ ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hz₂, map_one]
    exact hE3.2 _ hτ₀E
  have hz₁₂ : z₁ * z₂ = z₂ * z₁ := by
    apply hinj
    rw [map_mul, map_mul, hz₁, hz₂]
    exact congrArg Subtype.val (hE3.1.is_comm.comm ⟨_, hσ₀E⟩ ⟨_, hτ₀E⟩)
  have hz₁1 : z₁ ≠ 1 := by
    rintro rfl
    exact hσ₀1 (by rw [← hz₁, map_one])
  obtain ⟨W, hWab, hW4, hW1, hW2, w, hw, hmove⟩ := un_four_inner h hω hω1 hωb
    (g₁ := eTS h hf z₁) (g₂ := eTS h hf z₂) (by rw [← map_pow, hz₁3, map_one])
    (by rw [← map_pow, hz₂3, map_one]) (by rw [← map_mul, ← map_mul, hz₁₂])
    (fun e => hz₁1 ((eTS h hf).injective (e.trans (eTS h hf).map_one.symm)))
  refine eInvFour_of_two_gens hE3 hE9 hσ₀E hτ₀E hσ₀1 hτ₀
    (W := W.map (eTS h hf).symm.toMonoidHom) (CFSG.Open.IsElemAbelian.map hWab _)
    (by rw [Subgroup.card_map_of_injective (eTS h hf).symm.injective, hW4]) ?_ ?_ (Or.inl ?_)
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨_, hW1 x hx, ?_⟩
    rw [← hz₁, MulAut.conj_apply]
    exact (conj_eTS_symm h hf z₁ x).symm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨_, hW2 x hx, ?_⟩
    rw [← hz₂, MulAut.conj_apply]
    exact (conj_eTS_symm h hf z₂ x).symm
  · refine ⟨(eTS h hf).symm w, ⟨w, hw, rfl⟩, fun hc => hmove ?_⟩
    rw [← hz₁, MulAut.conj_apply, conj_eTS_symm] at hc
    exact (eTS h hf).symm.injective hc

theorem eInvFour_un4_fixing {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) (hωb : h.bar ω = ω)
    (hf : 1 ≤ f) (hZ : Subgroup.center (primeFormP h (Cid1 4 K)) = ⊥) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) {Ē : Subgroup (MulAut (primeFormP h (Cid1 4 K)))}
    (hE3 : IsElemAbelian 3 Ē) (hE9 : Nat.card Ē = 9)
    (hσE : primeFormFieldHom h (isPrimeFormGram_one (n := 4) (K := K)) σ ∈ Ē) :
    EInvFour (primeFormP h (Cid1 4 K)) Ē := by
  classical
  haveI : Finite K := h.finite
  haveI := CFSG.RankThree.GF2n.Stroth80.isCyclic_ringEquiv K
  haveI : Finite (K ≃+* K) := Finite.of_injective (fun τ : K ≃+* K => (τ : K → K))
    (fun a b hab => RingEquiv.ext (fun x => congrFun hab x))
  have hinj : Function.Injective (MulAut.conj : primeFormP h (Cid1 4 K) →*
      MulAut (primeFormP h (Cid1 4 K))) := conj_injective_of_mulEquiv (MulEquiv.refl _) hZ
  obtain ⟨Φσ, hΦσ⟩ : ∃ Φσ, Φσ = primeFormFieldHom h (isPrimeFormGram_one (n := 4) (K := K)) σ :=
    ⟨_, rfl⟩
  rw [← hΦσ] at hσE
  have hθΦ : θ4 h Φσ = σ := by
    have := primeFormFieldFactor_apply h (isPrimeFormGram_one (n := 4) (K := K)) (by norm_num)
      (un4_hq (f := f)) 1 σ
    rw [map_one, one_mul] at this
    rw [hΦσ]
    exact this
  have hσ1 : σ ≠ 1 := fun e => by rw [e, orderOf_one] at hσ; omega
  have hΦ1 : Φσ ≠ 1 := fun e => hσ1 (by rw [← hθΦ, e, map_one])
  obtain ⟨b, hbE, hbθ, hbnot⟩ :=
    exists_ker_of_cyclic_hom (θ4 h) hE3 hE9 hσE (by rw [hθΦ]; exact hσ1)
  obtain ⟨g₀, hg₀⟩ := θ4_ker_le_inner h hf (MonoidHom.mem_ker.mpr hbθ)
  have hcomm : Φσ * b = b * Φσ :=
    congrArg Subtype.val (hE3.1.is_comm.comm ⟨_, hσE⟩ ⟨_, hbE⟩)
  have hfix : Φσ g₀ = g₀ := by
    apply hinj
    rw [← mulAut_mul_conj_mul_inv, hg₀, hcomm]
    group
  have hg₀3 : g₀ ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hg₀, map_one]
    exact hE3.2 _ hbE
  have hg₀1 : g₀ ≠ 1 := by
    rintro rfl
    exact hbnot (by rw [← hg₀, map_one]; exact Subgroup.one_mem _)
  obtain ⟨s, hs⟩ : ∃ s, s = eTS h hf g₀ := ⟨_, rfl⟩
  have hsfix : primeFormFieldSU h (isPrimeFormGram_one (n := 4) (K := K)) σ s = s := by
    rw [hs, ← eTS_field, ← hΦσ, hfix]
  have hs3 : s ^ 3 = 1 := by rw [hs, ← map_pow, hg₀3, map_one]
  have hs1 : s ≠ 1 := fun e => hg₀1 ((eTS h hf).injective (by rw [← hs, e, map_one]))
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hσω : σ ω = ω := ringEquiv_fixes_cube_root hσ3 hω hω1
  obtain ⟨W, hWab, hW4, hWσ, hWg, w, hw, hmove⟩ := un_four_fixed h hω hω1 hωb hσω hs3 hs1
    ((fieldSU_eq_iff h σ s).mp hsfix)
  have hconj : ∀ x : gramSU h (Cid1 4 K), b ((eTS h hf).symm x) =
      (eTS h hf).symm (s * x * s⁻¹) := by
    intro x
    rw [← hg₀, MulAut.conj_apply, conj_eTS_symm, hs]
  refine eInvFour_of_two_gens hE3 hE9 hσE hbE hΦ1 hbnot
    (W := W.map (eTS h hf).symm.toMonoidHom) (CFSG.Open.IsElemAbelian.map hWab _)
    (by rw [Subgroup.card_map_of_injective (eTS h hf).symm.injective, hW4]) ?_ ?_ (Or.inr ?_)
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    have h1 := eTS_field h hf σ ((eTS h hf).symm x)
    rw [MulEquiv.apply_symm_apply, (fieldSU_eq_iff h σ x).mpr (hWσ x hx), ← hΦσ] at h1
    change (eTS h hf).symm x = Φσ ((eTS h hf).symm x)
    exact (eTS h hf).injective (by rw [MulEquiv.apply_symm_apply, h1])
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨_, hWg x hx, (hconj x).symm⟩
  · refine ⟨(eTS h hf).symm w, ⟨w, hw, rfl⟩, fun hc => hmove ?_⟩
    rw [hconj] at hc
    exact (eTS h hf).symm.injective hc

theorem eInvFour_un4_outer {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) (hωb : h.bar ω = ω)
    (hf : 1 ≤ f) (hZ : Subgroup.center (primeFormP h (Cid1 4 K)) = ⊥)
    {Ē : Subgroup (MulAut (primeFormP h (Cid1 4 K)))} (hE3 : IsElemAbelian 3 Ē)
    (hE9 : Nat.card Ē = 9) (hout : ¬ Ē ≤ (θ4 h).ker) : EInvFour (primeFormP h (Cid1 4 K)) Ē := by
  classical
  haveI : Finite K := h.finite
  obtain ⟨a, haE, haθ⟩ : ∃ a ∈ Ē, θ4 h a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hout fun a ha => MonoidHom.mem_ker.mpr (hcon a ha)
  have ha3 : a ^ 3 = 1 := hE3.2 a haE
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = θ4 h a := ⟨_, rfl⟩
  have hσ3 : σ ^ 3 = 1 := by rw [hσdef, ← map_pow, ha3, map_one]
  have hσ1 : σ ≠ 1 := fun e => haθ (by rw [← hσdef, e])
  have hσo : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have ha1 : a ≠ 1 := fun e => haθ (by rw [e, map_one])
  have haord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.unitary_prime_semilinear_field_descent'
    h (n := 4) (by norm_num) (un4_hq (f := f)) Nat.prime_three (by norm_num) a haord σ
    hσdef.symm hσo
  refine eInvFour_of_map_conj (primeFormConjHom h _ M)⁻¹ ?_
  refine eInvFour_un4_fixing h hω hω1 hωb hf hZ hσo (CFSG.Open.IsElemAbelian.map hE3 _) ?_
    ⟨a, haE, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, hE9]
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hM

theorem bar_primitive_of_even {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hf : Even f) :
    h.bar ω = ω := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω4 : ω ^ 4 = ω := by
    calc ω ^ 4 = ω ^ 3 * ω := by ring
      _ = ω := by rw [hω3, one_mul]
  have key : ∀ m : ℕ, ω ^ (4 ^ m) = ω := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_mul, ih, hω4]
  obtain ⟨m, hm⟩ := hf
  rw [UnitaryFieldData.bar_apply, hm, ← two_mul, pow_mul]
  simpa using key m

theorem eInvNine_primeForm4 (hf : Even f) (hf0 : 0 < f)
    (hZ : Subgroup.center (primeFormP h (Cid1 4 K)) = ⊥) :
    EInvNine (primeFormP h (Cid1 4 K)) := by
  intro Ē hE3 hE9
  haveI : Finite K := h.finite
  have h3 : 3 ∣ Nat.card K - 1 := by
    rw [h.card]
    exact three_dvd_two_pow_sub_one (even_two_mul f)
  obtain ⟨ω, hω, hω1⟩ := exists_primitive_cube_root h3
  have hωb := bar_primitive_of_even h hω hf
  by_cases hin : Ē ≤ (θ4 h).ker
  · exact eInvFour_un4_inner h hω hω1 hωb hf0 hZ hE3 hE9 (hin.trans (θ4_ker_le_inner h hf0))
  · exact eInvFour_un4_outer h hω hω1 hωb hf0 hZ hE3 hE9 hin

theorem four_dvd_card_gramSU (hf : Even f) (hf0 : 0 < f) :
    4 ∣ Nat.card (gramSU h (Cid1 4 K)) := by
  haveI : Finite K := h.finite
  haveI : CharP K 2 := h.charP
  have h3 : 3 ∣ Nat.card K - 1 := by
    rw [h.card]
    exact three_dvd_two_pow_sub_one (even_two_mul f)
  obtain ⟨ω, hω, hω1⟩ := exists_primitive_cube_root h3
  have hωb := bar_primitive_of_even h hω hf
  let v : Fin 4 → K := ![1, 1, 0, 0]
  have hv0 : v ≠ 0 := fun e => one_ne_zero (congrFun e 0)
  have hv : uB h v v = 0 := by
    rw [uB_apply]
    simp only [dotProduct, Fin.sum_univ_four, v]
    simp [map_one, map_zero]
    exact CharTwo.add_self_eq_zero (1 : K)
  let ω' : h.fixedField := ⟨ω, (UnitaryFieldData.mem_fixedField h).mpr hωb⟩
  have hω' : ω' ^ 2 + ω' + 1 = 0 := Subtype.ext (by simpa [ω'] using hω)
  have hω'1 : ω' ≠ 1 := fun e => hω1 (by simpa [ω'] using congrArg Subtype.val e)
  have hmul := uRoot_add h hv
  have hinj : ∀ s t, uRoot h hv s = uRoot h hv t → s = t := fun s t e => uRoot_inj h hv hv0 e
  have h4 := (rootFourOf_spec hmul hinj hω' hω'1).2
  have hd := Subgroup.card_subgroup_dvd_card (rootFourOf (uRoot h hv) ω')
  rwa [h4] at hd

theorem center_primeForm4_eq_bot (hf : Even f) (hf0 : 0 < f)
    (hs : IsSimpleGroup (primeFormP h (Cid1 4 K))) :
    Subgroup.center (primeFormP h (Cid1 4 K)) = ⊥ := by
  haveI : Finite K := h.finite
  refine center_eq_bot_of_simple_of_not_prime hs ?_
  have h4 : 4 ∣ Nat.card (primeFormP h (Cid1 4 K)) := by
    rw [Nat.card_congr (eTS h hf0).toEquiv]
    exact four_dvd_card_gramSU h hf hf0
  intro hp
  have := (Nat.dvd_prime hp).mp h4
  rcases this with e | e
  · omega
  · rw [← e] at hp
    exact absurd hp (by norm_num)

end Un4

theorem eInvNine_of_projSU4 {X : Type} [Group X] {f : ℕ} (hf0 : 0 < f) (hf : Even f)
    (e : X ≃* projSU 4 2 f) : EInvNine X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKcard : Nat.card (GaloisField 2 (2 * f)) = 2 ^ (2 * f) :=
    GaloisField.card 2 (2 * f) (by omega)
  have h : UnitaryFieldData 2 f (GaloisField 2 (2 * f)) := ⟨Nat.prime_two, hf0, hKcard⟩
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU 4 2 f :=
    ⟨Nat.prime_two, hf0, by norm_num, by simp [Prod.ext_iff]⟩
  let eT : projSU 4 2 f ≃* primeFormP h (Cid1 4 (GaloisField 2 (2 * f))) :=
    (CFSG.PGLModel.projSUEquivStatedProj 4 2 f).trans
      (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz.statedProjEquivPrimeFormOne
        h (n := 4) (by norm_num))
  haveI : IsSimpleGroup (projSU 4 2 f) := CFSG.PGLModel.isSimpleGroup_projSU_of_admissible hadm
  have hs : IsSimpleGroup (primeFormP h (Cid1 4 (GaloisField 2 (2 * f)))) :=
    eT.symm.isSimpleGroup
  exact EInvNine.of_mulEquiv (e.trans eT)
    (eInvNine_primeForm4 h hf hf0 (center_primeForm4_eq_bot h hf hf0 hs))

end CFSG.RankThree.PartTwo.Sec21.Hering214
