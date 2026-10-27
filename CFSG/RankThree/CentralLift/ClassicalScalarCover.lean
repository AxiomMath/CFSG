module

public import CFSG.RankThree.CentralLift.ClassicalCoverTools
public import CFSG.RankThree.CentralLift.CrossOrthogonalSplit
public import CFSG.RankThree.CentralLift.DefiningUnitary
public import CFSG.RankThree.CentralLiftU.UnitaryThreeLift
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LieType.Steinberg.CentralExt.SymplecticPerfect
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive

public section

namespace CFSG.RankThree.CentralLift

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal (toLinEquiv toLinEquiv_apply statedOmega_eq_comap
  statedOmegaEquiv)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit (flag finrank_flag
  quadPlus_eq_zero_of_mem_flag)
open CFSG.RankThree.CentralLiftU (forall_section_of_mulEquiv gramSU_three_forall_section)

universe u

theorem exact_scalar_cover_of_forall_section {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {H : Subgroup (GL ι K)} [Finite H] {L : Type u} [Group L] [Finite L]
    [Group.IsPerfect L] {η : L →* StatedProj H} (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center L) {p : ℕ} (hCp : IsPGroup p η.ker)
    (hsplit : ∀ (E : Type u) [Group E] [Finite E] (π : E →* H), Function.Surjective π →
      π.ker ≤ Subgroup.center E → IsPGroup p π.ker → ∃ s : H →* E, ∀ x, π (s x) = x) :
    ∃ φ : H →* L, Function.Surjective φ ∧
      η.comp φ = QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H) ∧
      φ.ker ≤ (StatedScalars ι K).subgroupOf H ∧
      ((StatedScalars ι K).subgroupOf H).map φ = η.ker ∧
      (∃ e : H ⧸ φ.ker ≃* L, ∀ h : H, e (h : H ⧸ φ.ker) = φ h ∧
        η (e (h : H ⧸ φ.ker)) = QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H) h) ∧
      Nonempty (η.ker ≃* (StatedScalars ι K).subgroupOf H ⧸
        φ.ker.subgroupOf ((StatedScalars ι K).subgroupOf H)) := by
  obtain ⟨φ, hφ⟩ := exists_comp_eq_of_pullback_section
    (β := QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H)) hη hC hCp
    fun P ρ hρ hρC hρp => by
      obtain ⟨s, hs⟩ := hsplit P ρ hρ hρC hρp
      exact ⟨s, MonoidHom.ext hs⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := cover_map_of_comp_eq (QuotientGroup.mk'_surjective _) hC hφ
  rw [QuotientGroup.ker_mk'] at h2 h3 h5
  exact ⟨φ, h1, hφ, h2, h3, h4, h5⟩

section Split

variable {p ℓ f : ℕ}

theorem statedSp_forall_section (hp : p.Prime) (hp3 : 3 < p) (hℓ : ℓ.Prime) (hℓodd : Odd ℓ)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f) {n : ℕ} (hn : 1 ≤ n)
    {E : Type*} [Group E] [Finite E] (π : E →* StatedSp n K) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker) :
    ∃ s : StatedSp n K →* E, ∀ x, π (s x) = x := by
  by_cases hpℓ : p = ℓ
  · subst hpℓ
    obtain ⟨⟨s, hs, -⟩, -⟩ := symplectic_defining_splitting hp hp3 hf hK π hπ hC hCp
    exact ⟨s, DFunLike.congr_fun hs⟩
  · obtain ⟨⟨s, hs, -⟩, -⟩ := symplectic_cross_splitting hp hp3 hℓ hℓodd hpℓ hf hK hn π hπ hC hCp
    exact ⟨s, DFunLike.congr_fun hs⟩

theorem statedOmegaPlus_forall_section (hp : p.Prime) (hp3 : 3 < p) (hℓ : ℓ.Prime)
    (hℓodd : Odd ℓ) (hpℓ : p ≠ ℓ) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) {n : ℕ} (hn : 3 ≤ n) {E : Type*} [Group E] [Finite E]
    (π : E →* StatedOmega (StatedQuadPlus n K)) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker) :
    ∃ s : StatedOmega (StatedQuadPlus n K) →* E, ∀ x, π (s x) = x := by
  have hK2 : ringChar K ≠ 2 := CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hℓ
    (hℓodd.ne_two_of_dvd_nat (dvd_refl ℓ)) hK
  have hE := orthogonal_odd_derived_elementary hK2 (nondegenerate_polarBilin_quadPlus n K)
    ⟨flag n K 3, finrank_flag hn, fun _ hx => quadPlus_eq_zero_of_mem_flag hx⟩
  let e : StatedOmega (StatedQuadPlus n K) ≃* orthElementaryGroup (quadPlus n K) :=
    statedOmegaEquiv (coe_quadPlus n K) hE
  refine forall_section_of_mulEquiv e (fun ρ hρ hρC hρp => ?_) π hπ hC hCp
  obtain ⟨⟨s, hs, -⟩, -⟩ := split_orthogonal_cross_splitting hp hp3 hℓ hℓodd hpℓ hf hK hn ρ hρ hρC
    hρp
  exact ⟨s, DFunLike.congr_fun hs⟩

theorem nonempty_statedSU_mulEquiv_sesq {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (n : ℕ) :
    Nonempty (StatedSU n (ℓ ^ f) K ≃*
      sesqSpecialUnitaryGroup (gramForm h (1 : Matrix (Fin n) (Fin n) K))) := by
  have hmap : (gramSU h (1 : Matrix (Fin n) (Fin n) K)).map
      (Matrix.GeneralLinearGroup.toLin : GL (Fin n) K ≃* _).toMonoidHom =
      sesqSpecialUnitaryGroup (gramForm h (1 : Matrix (Fin n) (Fin n) K)) := by
    ext g
    rw [Subgroup.mem_map_equiv, ← toLin_mem_sesqSpecialUnitaryGroup_iff h,
      MulEquiv.apply_symm_apply]
  exact ⟨((MulEquiv.subgroupCongr (unitarySU_eq_gramSU h n)).trans
    (Matrix.GeneralLinearGroup.toLin.subgroupMap _)).trans (MulEquiv.subgroupCongr hmap)⟩

theorem statedSU_three_forall_section (hp : p.Prime) (hp3 : 3 < p) (hℓ : ℓ.Prime)
    (hℓodd : Odd ℓ) (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2)
    {E : Type*} [Group E] [Finite E] (π : E →* StatedSU 3 (ℓ ^ f) K)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker) :
    ∃ s : StatedSU 3 (ℓ ^ f) K →* E, ∀ x, π (s x) = x := by
  have h : UnitaryFieldData ℓ f K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hℓ2 : ℓ ≠ 2 := hℓodd.ne_two_of_dvd_nat (dvd_refl ℓ)
  exact forall_section_of_mulEquiv (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 3))
    (fun ρ hρ hρC hρp => gramSU_three_forall_section h hℓ2 (G₀ := 1)
      (by rw [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), Matrix.transpose_one])
      (by rw [Matrix.det_one]; exact one_ne_zero) hp hp3 E ρ hρ hρC hρp) π hπ hC hCp

theorem statedSU_even_forall_section (hp : p.Prime) (hp3 : 3 < p) (hf : 1 ≤ f) {K : Type}
    [Field K] (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (hn : 3 ≤ n) (hne : Even n) {E : Type*}
    [Group E] [Finite E] (π : E →* StatedSU n (p ^ f) K) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker) :
    ∃ s : StatedSU n (p ^ f) K →* E, ∀ x, π (s x) = x := by
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨r, hr⟩ := hne
  obtain ⟨e⟩ := nonempty_statedSU_mulEquiv_sesq h n
  refine forall_section_of_mulEquiv e (fun ρ hρ hρC hρp => ?_) π hπ hC hCp
  obtain ⟨⟨s, hs, -⟩, -⟩ := unitary_defining_splitting h hp3
    (gramForm_isSymm h (by rw [Matrix.map_one _ (map_zero h.bar) (map_one h.bar),
      Matrix.transpose_one]))
    (gramForm_separatingLeft h (by rw [Matrix.det_one]; exact one_ne_zero)) (r := r) (by omega)
    (by rw [Module.finrank_fin_fun]; omega) ρ hρ hρC hρp
  exact ⟨s, DFunLike.congr_fun hs⟩

theorem statedSU_forall_section_of_three_or_defining (hp : p.Prime) (hp3 : 3 < p) (hℓ : ℓ.Prime)
    (hℓodd : Odd ℓ) (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) {n : ℕ}
    (hn : 3 ≤ n) (hcase : n = 3 ∨ (p = ℓ ∧ Even n)) {E : Type*} [Group E] [Finite E]
    (π : E →* StatedSU n (ℓ ^ f) K) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker) :
    ∃ s : StatedSU n (ℓ ^ f) K →* E, ∀ x, π (s x) = x := by
  rcases hcase with rfl | ⟨rfl, hne⟩
  · exact statedSU_three_forall_section hp hp3 hℓ hℓodd hf hK π hπ hC hCp
  · exact statedSU_even_forall_section hp hp3 hf hK hn hne π hπ hC hCp

end Split

theorem card_statedScalars_subgroupOf_statedOmega_le_two {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀)
    (hv : ∃ v, Q v ≠ 0) :
    Nat.card ((StatedScalars ι K).subgroupOf (StatedOmega Q₀)) ≤ 2 := by
  refine CFSG.LieType.Steinberg.card_le_two_of_forall_scalar
    (φ := (StatedOmega Q₀).subtype.comp (Subgroup.subtype _))
    (Subtype.val_injective.comp Subtype.val_injective) fun g => ?_
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 g.2
  have hmat : (((g : StatedOmega Q₀) : GL ι K) : Matrix ι ι K) = Matrix.scalar ι (c : K) := by
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]
  refine ⟨c, ?_, hmat⟩
  obtain ⟨v, hv⟩ := hv
  have hO : ∀ A ∈ StatedOmega Q₀, toLinEquiv ι K A ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro A hA
    rw [statedOmega_eq_comap hQ, Subgroup.mem_comap] at hA
    set O := TauCeti.QuadraticMap.orthogonalGroup Q
    refine (Subgroup.commutator_le.2 fun a ha b hb => ?_ : ⁅O, O⁆ ≤ O) hA
    rw [commutatorElement_def]
    exact O.mul_mem (O.mul_mem (O.mul_mem ha hb) (O.inv_mem ha)) (O.inv_mem hb)
  have hmem := hO _ (g : StatedOmega Q₀).2
  have h := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hmem v
  have hmul : (((g : StatedOmega Q₀) : GL ι K) : Matrix ι ι K) *ᵥ v = (c : K) • v := by
    ext i
    rw [hmat, Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  rw [toLinEquiv_apply, hmul, QuadraticMap.map_smul, smul_eq_mul] at h
  have h' : ((c : K) * c - 1) * Q v = 0 := by linear_combination h
  rw [pow_two]
  exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hv)

theorem exists_quadPlus_ne_zero {K : Type} [Field K] {n : ℕ} (hn : 1 ≤ n) :
    ∃ v, quadPlus n K v ≠ 0 := by
  refine ⟨Pi.single (Sum.inl ⟨0, hn⟩) 1 + Pi.single (Sum.inr ⟨0, hn⟩) 1, ?_⟩
  rw [quadPlus_apply, Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

section Cover

variable {p ℓ f : ℕ} {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]

theorem symplectic_exact_scalar_cover (hp : p.Prime) (hp3 : 3 < p) (hℓ : ℓ.Prime)
    (hℓodd : Odd ℓ) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    {n : ℕ} (hn : 1 ≤ n) (η : L →* StatedProj (StatedSp n K)) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center L) (hCp : IsPGroup p η.ker) :
    (∃ φ : StatedSp n K →* L, Function.Surjective φ ∧
      η.comp φ = QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K)) ∧
      φ.ker ≤ (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) ∧
      ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K)).map φ = η.ker ∧
      (∃ e : StatedSp n K ⧸ φ.ker ≃* L, ∀ h : StatedSp n K,
        e (h : StatedSp n K ⧸ φ.ker) = φ h ∧ η (e (h : StatedSp n K ⧸ φ.ker)) =
          QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K)) h) ∧
      Nonempty (η.ker ≃* (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) ⧸
        φ.ker.subgroupOf ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K)))) ∧
    Nat.card ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K)) ≤ 2 :=
  ⟨exact_scalar_cover_of_forall_section hη hC hCp fun _ _ _ π hπ hπC hπp =>
      statedSp_forall_section hp hp3 hℓ hℓodd hf hK hn π hπ hπC hπp,
    CFSG.LieType.Steinberg.card_statedScalars_subgroupOf_statedSp_le_two n K⟩

theorem omegaPlus_exact_scalar_cover (hp : p.Prime) (hp3 : 3 < p) (hℓ : ℓ.Prime)
    (hℓodd : Odd ℓ) (hpℓ : p ≠ ℓ) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) {n : ℕ} (hn : 3 ≤ n)
    (η : L →* StatedProj (StatedOmega (StatedQuadPlus n K))) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center L) (hCp : IsPGroup p η.ker) :
    (∃ φ : StatedOmega (StatedQuadPlus n K) →* L, Function.Surjective φ ∧
      η.comp φ = QuotientGroup.mk'
        ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedOmega (StatedQuadPlus n K))) ∧
      φ.ker ≤ (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedOmega (StatedQuadPlus n K)) ∧
      ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedOmega (StatedQuadPlus n K))).map φ =
        η.ker ∧
      (∃ e : StatedOmega (StatedQuadPlus n K) ⧸ φ.ker ≃* L, ∀ h : StatedOmega (StatedQuadPlus n K),
        e (h : StatedOmega (StatedQuadPlus n K) ⧸ φ.ker) = φ h ∧
        η (e (h : StatedOmega (StatedQuadPlus n K) ⧸ φ.ker)) = QuotientGroup.mk'
          ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedOmega (StatedQuadPlus n K))) h) ∧
      Nonempty (η.ker ≃*
        (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedOmega (StatedQuadPlus n K)) ⧸
        φ.ker.subgroupOf
          ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedOmega (StatedQuadPlus n K))))) ∧
    Nat.card ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedOmega (StatedQuadPlus n K))) ≤
      2 :=
  ⟨exact_scalar_cover_of_forall_section hη hC hCp fun _ _ _ π hπ hπC hπp =>
      statedOmegaPlus_forall_section hp hp3 hℓ hℓodd hpℓ hf hK hn π hπ hπC hπp,
    card_statedScalars_subgroupOf_statedOmega_le_two (coe_quadPlus n K)
      (exists_quadPlus_ne_zero (by omega))⟩

theorem unitary_exact_scalar_cover_of_three_or_defining (hp : p.Prime) (hp3 : 3 < p)
    (hℓ : ℓ.Prime) (hℓodd : Odd ℓ) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) {n : ℕ} (hn : 3 ≤ n) (hcase : n = 3 ∨ (p = ℓ ∧ Even n))
    (η : L →* StatedProj (StatedSU n (ℓ ^ f) K)) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center L) (hCp : IsPGroup p η.ker) :
    (∃ φ : StatedSU n (ℓ ^ f) K →* L, Function.Surjective φ ∧
      η.comp φ = QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K)) ∧
      φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K) ∧
      ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K)).map φ = η.ker ∧
      (∃ e : StatedSU n (ℓ ^ f) K ⧸ φ.ker ≃* L, ∀ h : StatedSU n (ℓ ^ f) K,
        e (h : StatedSU n (ℓ ^ f) K ⧸ φ.ker) = φ h ∧
        η (e (h : StatedSU n (ℓ ^ f) K ⧸ φ.ker)) =
          QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K)) h) ∧
      Nonempty (η.ker ≃* (StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K) ⧸
        φ.ker.subgroupOf ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K)))) ∧
    Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K)) ∣
      Nat.gcd n (ℓ ^ f + 1) :=
  ⟨exact_scalar_cover_of_forall_section hη hC hCp fun _ _ _ π hπ hπC hπp =>
      statedSU_forall_section_of_three_or_defining hp hp3 hℓ hℓodd hf hK hn hcase π hπ hπC hπp,
    dvd_of_eq (CFSG.LinearGroups.unitary_scalar_kernel hℓ hK (by omega)).2.2⟩

end Cover

end CFSG.RankThree.CentralLift
