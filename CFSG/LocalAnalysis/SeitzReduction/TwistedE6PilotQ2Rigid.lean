module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2RigidModel
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2BLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)
open CFSG.SeitzReduction.EPilot (cartanChar_E6_zero cartanChar_E6_one cartanChar_E6_two
  cartanChar_E6_three cartanChar_E6_four cartanChar_E6_five perm_E6_zero perm_E6_one perm_E6_two
  perm_E6_three perm_E6_four perm_E6_five)

local instance twistedE6PilotQ2RigidNeZero : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

section Arith

variable {K : Type} [Field K]

theorem units_pow_three_of_card_four (hK : Nat.card K = (2 ^ 1) ^ 2) (x : Kˣ) : x ^ 3 = 1 := by
  have := finite_of_card hK
  have h : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]; norm_num
  rw [← h]
  exact pow_card_eq_one'

theorem units_map_sigma_two (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (x : Kˣ) : Units.map σ.toMonoidHom x = x⁻¹ := by
  have h3 := units_pow_three_of_card_four hK x
  refine Units.ext ?_
  change σ (x : K) = _
  rw [hσ, pow_one]
  have h : (x : K) ^ 2 * x = 1 := by
    rw [← pow_succ, ← Units.val_pow_eq_pow_val, h3, Units.val_one]
  rw [Units.val_inv_eq_inv_val]
  exact eq_inv_of_mul_eq_one_left h

theorem eq_one_of_eq_inv_two (hK : Nat.card K = (2 ^ 1) ^ 2) {x : Kˣ} (h : x = x⁻¹) : x = 1 := by
  have h3 := units_pow_three_of_card_four hK x
  have h2 : x * x = 1 := by
    calc x * x = x * x⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel x
  calc x = x ^ 3 * (x * x)⁻¹ := by group
    _ = 1 := by rw [h3, h2, inv_one, one_mul]

theorem compat_facts_two (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) {b : Fin TwistTag.E6.tag.rank → Kˣ}
    (hb : ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b i)) :
    b 1 = 1 ∧ b 3 = 1 ∧ b 4 = (b 2)⁻¹ ∧ b 5 = (b 0)⁻¹ := by
  have h1 := hb 1
  have h3 := hb 3
  have h2 := hb 2
  have h0 := hb 0
  rw [show TwistTag.E6.perm 1 = 1 from perm_E6_one, units_map_sigma_two hK hσ] at h1
  rw [show TwistTag.E6.perm 3 = 3 from perm_E6_three, units_map_sigma_two hK hσ] at h3
  rw [show TwistTag.E6.perm 2 = 4 from perm_E6_two, units_map_sigma_two hK hσ] at h2
  rw [show TwistTag.E6.perm 0 = 5 from perm_E6_zero, units_map_sigma_two hK hσ] at h0
  exact ⟨eq_one_of_eq_inv_two hK h1, eq_one_of_eq_inv_two hK h3, h2, h0⟩

theorem rootChar_e6HighestRoot (b : Fin TwistTag.E6.tag.rank → Kˣ) :
    rootChar b e6HighestRoot = b 0 * b 1 ^ 2 * b 2 ^ 2 * b 3 ^ 3 * b 4 ^ 2 * b 5 := by
  change ∏ i : Fin 6, b i ^ e6HighestRoot i = _
  rw [Fin.prod_univ_six]
  simp [e6HighestRoot]
  rfl

theorem rootChar_theta_eq_one_two (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) {b : Fin TwistTag.E6.tag.rank → Kˣ}
    (hb : ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b i)) :
    rootChar b e6HighestRoot = 1 := by
  obtain ⟨h1, h3, h4, h5⟩ := compat_facts_two hK hσ hb
  rw [rootChar_e6HighestRoot, h1, h3, h4, h5]
  group

end Arith

section Theta

variable
  {K : Type} [Field K]

theorem thetaRankOneGroup_le_centralizer_rootDiagUnit {k : Type} [Field k] (ι : k →+* K)
    {b : Fin TwistTag.E6.tag.rank → Kˣ} (hb : rootChar b e6HighestRoot = 1) :
    thetaRankOneGroup ι ≤
      centralizer ({rootDiagUnit TwistTag.E6.tag b} : Set (ModGL TwistTag.E6.tag K)) := by
  have hneg : rootChar b (-e6HighestRoot) = 1 := by
    have h := CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar_add b
      e6HighestRoot (-e6HighestRoot)
    rw [add_neg_cancel, CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar_zero, hb,
      one_mul] at h
    exact h.symm
  have key : ∀ (β : Fin TwistTag.E6.tag.rank → ℤ), IsRoot TwistTag.E6.tag β → rootChar b β = 1 →
      Subgroup.closure (Set.range fun c : k => pinnedX TwistTag.E6.tag K β (ι c)) ≤
        centralizer ({rootDiagUnit TwistTag.E6.tag b} : Set (ModGL TwistTag.E6.tag K)) := by
    intro β hβ hχ
    rw [Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    have h := rootDiagUnit_conj_pinnedX b hβ (ι c)
    rw [hχ, Units.val_one, one_mul] at h
    calc pinnedX TwistTag.E6.tag K β (ι c) * rootDiagUnit TwistTag.E6.tag b =
        rootDiagUnit TwistTag.E6.tag b * pinnedX TwistTag.E6.tag K β (ι c) *
          (rootDiagUnit TwistTag.E6.tag b)⁻¹ * rootDiagUnit TwistTag.E6.tag b := by rw [h]
      _ = rootDiagUnit TwistTag.E6.tag b * pinnedX TwistTag.E6.tag K β (ι c) := by group
  exact sup_le (key _ isRoot_e6HighestRoot hb) (key _ (IsRoot.neg isRoot_e6HighestRoot) hneg)

end Theta

section Tau

variable {K : Type} [Field K]

@[expose] def diagTau (b : Fin TwistTag.E6.tag.rank → Kˣ) : Fin 6 → Kˣ :=
  ![b 0 * b 2 * b 3 * b 4 * b 5, b 2 * b 3 * b 4 * b 5, b 3 * b 4 * b 5, b 4 * b 5, b 5, 1]

theorem diagTau_spec (b : Fin TwistTag.E6.tag.rank → Kˣ) :
    ∀ t : Fin 5, b (pathIdx t) = diagTau b t.castSucc * (diagTau b t.succ)⁻¹ := by
  intro t
  fin_cases t
  · change b 0 = (b 0 * b 2 * b 3 * b 4 * b 5) * (b 2 * b 3 * b 4 * b 5)⁻¹
    group
  · change b 2 = (b 2 * b 3 * b 4 * b 5) * (b 3 * b 4 * b 5)⁻¹
    group
  · change b 3 = (b 3 * b 4 * b 5) * (b 4 * b 5)⁻¹
    group
  · change b 4 = (b 4 * b 5) * (b 5)⁻¹
    group
  · change b 5 = b 5 * (1 : Kˣ)⁻¹
    group

theorem eq_of_prod_diagTau_eq_one (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) {b : Fin TwistTag.E6.tag.rank → Kˣ}
    (hb : ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b i))
    (h : ∏ i, ((diagTau b i : Kˣ) : K) = 1) : b 2 = b 0 := by
  obtain ⟨h1, h3, h4, h5⟩ := compat_facts_two hK hσ hb
  have hx3 := units_pow_three_of_card_four hK (b 0)
  have hy3 := units_pow_three_of_card_four hK (b 2)
  rw [Fin.prod_univ_six] at h
  change ((b 0 * b 2 * b 3 * b 4 * b 5 : Kˣ) : K) * ((b 2 * b 3 * b 4 * b 5 : Kˣ) : K) *
    ((b 3 * b 4 * b 5 : Kˣ) : K) * ((b 4 * b 5 : Kˣ) : K) * ((b 5 : Kˣ) : K) * ((1 : Kˣ) : K) = 1
    at h
  rw [h3, h4, h5] at h
  push_cast at h
  have hx0 : ((b 0 : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have hy0 : ((b 2 : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have hx3' : ((b 0 : Kˣ) : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hx3, Units.val_one]
  have hy3' : ((b 2 : Kˣ) : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hy3, Units.val_one]
  have hP : ((b 0 : Kˣ) : K) ^ 4 * ((b 2 : Kˣ) : K) ^ 2 = 1 := by
    field_simp at h
    linear_combination -h
  refine Units.ext ?_
  calc ((b 2 : Kˣ) : K) = ((b 2 : Kˣ) : K) * (((b 0 : Kˣ) : K) ^ 4 * ((b 2 : Kˣ) : K) ^ 2) := by
        rw [hP, mul_one]
    _ = ((b 0 : Kˣ) : K) ^ 3 * ((b 0 : Kˣ) : K) * ((b 2 : Kˣ) : K) ^ 3 := by ring
    _ = ((b 0 : Kˣ) : K) := by rw [hx3', hy3', one_mul, mul_one]

end Tau

section Det

variable
  {K : Type} [Field K]

theorem prod_diagTau_eq_one_of_conj (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (b : Fin TwistTag.E6.tag.rank → Kˣ)
    {d₁ : ModGL TwistTag.E6.tag K} (hd₁ : d₁ ∈ su6Levi σ)
    (h : ∀ y ∈ su6Levi σ, rootDiagUnit TwistTag.E6.tag b * y * (rootDiagUnit TwistTag.E6.tag b)⁻¹ =
      d₁⁻¹ * y * d₁) :
    ∏ i, ((diagTau b i : Kˣ) : K) = 1 := by
  have hf : 1 ≤ 1 := le_rfl
  have : Finite K := finite_of_card hK
  have : CharP K 2 := charP_two_of_card hf hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  have hD : su6Levi σ = (unitarySL σ).map (realize h2) :=
    (subsystemGroup_inf_eq_map_realize hK hσ h2).1
  rw [hD] at hd₁
  obtain ⟨B₁, -, rfl⟩ := hd₁
  have hcomm : ∀ B ∈ unitaryInvolutions K, Commute (B : Matrix (Fin 6) (Fin 6) K)
      ((B₁ : Matrix (Fin 6) (Fin 6) K) *
        Matrix.diagonal (fun i => ((diagTau b i : Kˣ) : K))) := by
    intro B hB
    obtain ⟨hBu, hBB⟩ := unitaryInvolutions_facts σ h2 B hB
    have hy : realize h2 B ∈ su6Levi σ := by
      rw [hD]
      exact ⟨B, hBu, rfl⟩
    have h1 := h _ hy
    rw [conj_rootDiagUnit_realize h2 b (diagTau b) (diagTau_spec b)] at h1
    have h1' : realize h2 (diagConjSL (diagTau b) B) = realize h2 (B₁⁻¹ * B * B₁) := by
      rw [h1, map_mul, map_mul, map_inv]
    have hX : diagConjSL (diagTau b) B * diagConjSL (diagTau b) B = 1 := by
      rw [← map_mul, hBB, map_one]
    have hY : B₁⁻¹ * B * B₁ * (B₁⁻¹ * B * B₁) = 1 := by
      calc B₁⁻¹ * B * B₁ * (B₁⁻¹ * B * B₁) = B₁⁻¹ * (B * B) * B₁ := by group
        _ = 1 := by rw [hBB, mul_one, inv_mul_cancel]
    exact commute_of_diagConjSL_eq (eq_of_realize_eq_of_mul_self h2 h1' hX hY)
  set M := (B₁ : Matrix (Fin 6) (Fin 6) K) *
    Matrix.diagonal (fun i => ((diagTau b i : Kˣ) : K)) with hMdef
  have hM := eq_scalar_of_commute_unitary hcomm
  have hdetM : M.det = ∏ i, ((diagTau b i : Kˣ) : K) := by
    rw [hMdef, Matrix.det_mul, B₁.2, one_mul, Matrix.det_diagonal]
  have hdet6 : M.det = M 0 0 ^ 6 := by
    conv_lhs => rw [hM]
    rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hne : ∏ i, ((diagTau b i : Kˣ) : K) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => Units.ne_zero _
  have hμ : M 0 0 ≠ 0 := by
    intro h0
    rw [← hdetM, hdet6, h0, zero_pow (by norm_num)] at hne
    exact hne rfl
  have hμ3 : M 0 0 ^ 3 = 1 := by
    have h3 := units_pow_three_of_card_four hK (Units.mk0 _ hμ)
    have h3' := congrArg Units.val h3
    rwa [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at h3'
  rw [← hdetM, hdet6]
  calc M 0 0 ^ 6 = (M 0 0 ^ 3) ^ 2 := by ring
    _ = 1 := by rw [hμ3, one_pow]

theorem eq_of_conj_rootDiagUnit_su6Levi_two (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) {b : Fin TwistTag.E6.tag.rank → Kˣ}
    (hb : ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b i))
    {d₁ : ModGL TwistTag.E6.tag K} (hd₁ : d₁ ∈ su6Levi σ)
    (h : ∀ y ∈ su6Levi σ, rootDiagUnit TwistTag.E6.tag b * y * (rootDiagUnit TwistTag.E6.tag b)⁻¹ =
      d₁⁻¹ * y * d₁) : b 2 = b 0 :=
  eq_of_prod_diagTau_eq_one hK hσ hb (prod_diagTau_eq_one_of_conj hK hσ b hd₁ h)

theorem rootDiagUnit_mem_C0_of_eq_two (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) {b : Fin TwistTag.E6.tag.rank → Kˣ}
    (hb : ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b i)) (h20 : b 2 = b 0) :
    rootDiagUnit TwistTag.E6.tag b ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  obtain ⟨h1, h3, h4, h5⟩ := compat_facts_two hK hσ hb
  have hx3 := units_pow_three_of_card_four hK (b 0)
  have hinv2 : ((b 0)⁻¹) ^ 2 = b 0 := by
    calc ((b 0)⁻¹) ^ 2 = b 0 ^ 3 * ((b 0)⁻¹) ^ 2 := by rw [hx3, one_mul]
      _ = b 0 := by group
  have hsq : b 0 ^ 2 = (b 0)⁻¹ := by
    calc b 0 ^ 2 = b 0 ^ 3 * (b 0)⁻¹ := by group
      _ = (b 0)⁻¹ := by rw [hx3, one_mul]
  set c : Fin TwistTag.E6.tag.rank → Kˣ := ![1, 1, (b 0)⁻¹, 1, b 0, 1] with hcdef
  have hc : ∀ i, c (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (c i) := by
    intro i
    rw [units_map_sigma_two hK hσ]
    fin_cases i
    · rw [perm_E6_zero]
      exact inv_one.symm
    · rw [perm_E6_one]
      exact inv_one.symm
    · rw [perm_E6_two]
      exact (inv_inv (b 0)).symm
    · rw [perm_E6_three]
      exact inv_one.symm
    · rw [perm_E6_four]
      rfl
    · rw [perm_E6_five]
      exact inv_one.symm
  have hcb : cartanChar c = b := by
    funext l
    fin_cases l
    · refine (cartanChar_E6_zero c).trans ?_
      change (1 : Kˣ) ^ 2 * ((b 0)⁻¹)⁻¹ = b 0
      group
    · refine (cartanChar_E6_one c).trans ?_
      change (1 : Kˣ) ^ 2 * (1 : Kˣ)⁻¹ = b 1
      rw [h1]
      group
    · refine (cartanChar_E6_two c).trans ?_
      change (1 : Kˣ)⁻¹ * ((b 0)⁻¹) ^ 2 * (1 : Kˣ)⁻¹ = b 2
      rw [h20, hinv2]
      group
    · refine (cartanChar_E6_three c).trans ?_
      change (1 : Kˣ)⁻¹ * ((b 0)⁻¹)⁻¹ * (1 : Kˣ) ^ 2 * (b 0)⁻¹ = b 3
      rw [h3]
      group
    · refine (cartanChar_E6_four c).trans ?_
      change (1 : Kˣ)⁻¹ * b 0 ^ 2 * (1 : Kˣ)⁻¹ = b 4
      rw [h4, h20, hsq]
      group
    · refine (cartanChar_E6_five c).trans ?_
      change (b 0)⁻¹ * (1 : Kˣ) ^ 2 = b 5
      rw [h5]
      group
  obtain ⟨w, hw⟩ := exists_compatDiag_eq hc
  rw [← hcb, ← hw, ← list_prod_orbitH_eq_rootDiagUnit]
  exact Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hg
    exact orbitH_mem_graphFixedRootGroup _ _ _ _

end Det

section Main


theorem twistedE6TwoDiagonalRigidity_holds : TwistedE6TwoDiagonalRigidity := by
  intro k K _ _ _ hk hK σ hσ A hAJ hA hcyc β hodd hβA hβD
  have hf : 1 ≤ 1 := le_rfl
  have : Finite K := finite_of_card hK
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  have hσE : ∀ c, σE c = c ^ (2 ^ 1) := hσ
  obtain ⟨-, -, -, -, -, hcoe, -, hNF, ⟨Θ, hΘ, -, -, -, -, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σE hσE
  obtain ⟨g, u, δ, rfl⟩ := hNF β
  have hδ : δ = 1 := by
    have hΘβ := hΘ _ g u δ rfl
    have hodd' : Odd (orderOf δ) := by
      rw [← hΘβ]
      exact hodd.of_dvd_nat (orderOf_map_dvd Θ _)
    have hcard : Nat.card (RingAut K) = 2 :=
      (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K
        (by rw [hK]; norm_num : Nat.card K = 2 ^ 2)).1
    have h2 : orderOf δ ∣ 2 := hcard ▸ orderOf_dvd_natCard δ
    have h1 : orderOf δ = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
      · exact h
      · rw [h] at hodd'
        exact absurd hodd' (by decide)
    exact orderOf_eq_one_iff.1 h1
  subst hδ
  rw [fieldActor_one, mul_one] at hβA hβD ⊢
  set b := compatDiag TwistTag.E6 σE.toRingHom u with hbdef
  have hb : ∀ i, b (TwistTag.E6.perm i) = Units.map σE.toRingHom.toMonoidHom (b i) :=
    compatDiag_perm u
  have hθ := rootChar_theta_eq_one_two hK hσ hb
  set A' := A.subgroupOf (graphFixedRootGroup TwistTag.E6 K σE.toRingHom) with hA'
  set D' := (su6Levi σE.toRingHom).subgroupOf (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)
    with hD'
  have hΔA : ∀ x ∈ A', compatDiagAutHom TwistTag.E6 K σE.toRingHom u x = x := by
    intro x hx
    apply Subtype.ext
    rw [hcoe]
    have hc := thetaRankOneGroup_le_centralizer_rootDiagUnit (algebraMap k K) hθ
      (hAJ (mem_subgroupOf.1 hx))
    rw [mem_centralizer_singleton_iff] at hc
    rw [← hc, mul_inv_cancel_right]
  have hgA : g ∈ centralizer (A' : Set (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)) := by
    rw [mem_centralizer_iff]
    intro a ha
    have h1 := hβA a ha
    rw [MulAut.mul_apply, hΔA a ha, MulAut.conj_apply] at h1
    calc a * g = g * a * g⁻¹ * g := by rw [h1]
      _ = g * a := by group
  rw [centralizer_nonsplit_subgroupOf hf hk hK hσ hAJ hA hcyc] at hgA
  obtain ⟨-, -, hXD, -⟩ := centralizer_nonsplit_twistedE6 hf hk hK hσ hAJ hA hcyc
  have hAD : A' ≤ centralizer (D' : Set (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)) :=
    subgroupOf_le_centralizer_subgroupOf hXD
  have hAN : A' ≤ normalizer (D' : Set (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)) :=
    hAD.trans (centralizer_le_normalizer _)
  have hg' : g ∈ ((A' ⊔ D' : Subgroup _) : Set (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)) :=
    hgA
  rw [coe_mul_of_left_le_normalizer_right _ _ hAN] at hg'
  obtain ⟨x, hx, d₁, hd₁, rfl⟩ := Set.mem_mul.1 hg'
  have hconj : ∀ y ∈ su6Levi σE.toRingHom,
      rootDiagUnit TwistTag.E6.tag b * y * (rootDiagUnit TwistTag.E6.tag b)⁻¹ =
        ((d₁ : graphFixedRootGroup TwistTag.E6 K σE.toRingHom) : ModGL TwistTag.E6.tag K)⁻¹ * y *
          d₁ := by
    intro y hy
    have hyC : y ∈ graphFixedRootGroup TwistTag.E6 K σE.toRingHom :=
      su6Levi_le_graphFixedRootGroup _ hy
    have hyD : (⟨y, hyC⟩ : graphFixedRootGroup TwistTag.E6 K σE.toRingHom) ∈ D' :=
      mem_subgroupOf.2 hy
    have h1 := hβD _ hyD
    rw [MulAut.mul_apply, MulAut.conj_apply] at h1
    set z := compatDiagAutHom TwistTag.E6 K σE.toRingHom u ⟨y, hyC⟩ with hz
    have hxd : x * d₁ = d₁ * x := (mem_centralizer_iff.1 (hAD hx) d₁ hd₁).symm
    have hxy : x * ⟨y, hyC⟩ = ⟨y, hyC⟩ * x :=
      (mem_centralizer_iff.1 (hAD hx) ⟨y, hyC⟩ hyD).symm
    have hxz : x * z = z * x := by
      have h2 := congrArg (compatDiagAutHom TwistTag.E6 K σE.toRingHom u) hxy
      rwa [map_mul, map_mul, hΔA x hx] at h2
    have hxd' : x * d₁⁻¹ = d₁⁻¹ * x := by
      calc x * d₁⁻¹ = d₁⁻¹ * (d₁ * x) * d₁⁻¹ := by group
        _ = d₁⁻¹ * (x * d₁) * d₁⁻¹ := by rw [hxd]
        _ = d₁⁻¹ * x := by group
    have h5 : x * (d₁ * z * d₁⁻¹) = (d₁ * z * d₁⁻¹) * x := by
      calc x * (d₁ * z * d₁⁻¹) = (x * d₁) * z * d₁⁻¹ := by group
        _ = d₁ * (x * z) * d₁⁻¹ := by rw [hxd]; group
        _ = d₁ * z * (x * d₁⁻¹) := by rw [hxz]; group
        _ = (d₁ * z * d₁⁻¹) * x := by rw [hxd']; group
    have h4 : d₁ * z * d₁⁻¹ = ⟨y, hyC⟩ := by
      calc d₁ * z * d₁⁻¹ = x * (d₁ * z * d₁⁻¹) * x⁻¹ := by rw [h5]; group
        _ = x * d₁ * z * (x * d₁)⁻¹ := by group
        _ = ⟨y, hyC⟩ := h1
    have h3 : z = d₁⁻¹ * ⟨y, hyC⟩ * d₁ := by
      rw [← h4]
      group
    have h6 := congrArg Subtype.val h3
    rw [hz, hcoe] at h6
    rw [h6]
    rfl
  have h20 := eq_of_conj_rootDiagUnit_su6Levi_two hK hσ hb (mem_subgroupOf.1 hd₁) hconj
  have hmem := rootDiagUnit_mem_C0_of_eq_two hK hσ hb h20
  have hmem1 : rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σE.toRingHom u) ^ 1 ∈
      graphFixedRootGroup TwistTag.E6 K σE.toRingHom := by
    rw [pow_one]
    exact hmem
  refine ⟨x * d₁ * ⟨_, hmem1⟩, ?_⟩
  rw [map_mul, ← compatDiagAutHom_pow_eq_conj u 1 hmem1, pow_one]

end Main

end CFSG.SeitzReduction.TwistedE6Pilot
