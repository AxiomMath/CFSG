module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaGroup

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

namespace RecipeFieldOmega

section Plus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}

theorem commute_fieldAutP_of_mem_plusCompl (hm : 1 ≤ m) (σ : K ≃+* K)
    {c : MulAut (matrixDerived (coordinateQuadPlus m K))} (hc : c ∈ AutOm.plusCompl hm) :
    Commute (AutOm.fieldAutP m σ) c := by
  have hφ : ∀ τ : K ≃+* K, Commute (AutOm.fieldAutP m σ) (AutOm.fieldAutP m τ) := fun τ => by
    change _ * _ = _ * _
    rw [← map_mul, ← map_mul, ringEquiv_mul_comm_of_finite]
  obtain ⟨τ, rfl | rfl⟩ := hc
  · exact hφ τ
  · exact Commute.mul_right (AutOm.plusRefl_mul_fieldAutP hm σ).symm (hφ τ)

theorem commute_plusRefl_of_mem_plusCompl (hm : 1 ≤ m)
    {c : MulAut (matrixDerived (coordinateQuadPlus m K))} (hc : c ∈ AutOm.plusCompl hm) :
    Commute (AutOm.plusRefl (K := K) hm) c := by
  obtain ⟨τ, rfl | rfl⟩ := hc
  · exact AutOm.plusRefl_mul_fieldAutP hm τ
  · exact Commute.mul_right (Commute.refl _) (AutOm.plusRefl_mul_fieldAutP hm τ)

theorem commute_of_mem_plusCompl (hm : 1 ≤ m)
    {c c' : MulAut (matrixDerived (coordinateQuadPlus m K))}
    (hc : c ∈ AutOm.plusCompl hm) (hc' : c' ∈ AutOm.plusCompl hm) : Commute c c' := by
  obtain ⟨σ, rfl | rfl⟩ := hc
  · exact commute_fieldAutP_of_mem_plusCompl hm σ hc'
  · exact Commute.mul_left (commute_plusRefl_of_mem_plusCompl hm hc')
      (commute_fieldAutP_of_mem_plusCompl hm σ hc')

theorem exists_eq_mul_fieldAutP_of_mem_plusCompl (hm : 1 ≤ m)
    {c : MulAut (matrixDerived (coordinateQuadPlus m K))} (hc : c ∈ AutOm.plusCompl hm) :
    ∃ y ∈ ({1, AutOm.plusRefl hm} : Set (MulAut (matrixDerived (coordinateQuadPlus m K)))),
      ∃ σ : K ≃+* K, c = y * AutOm.fieldAutP m σ := by
  obtain ⟨σ, rfl | rfl⟩ := hc
  · exact ⟨1, Or.inl rfl, σ, (one_mul _).symm⟩
  · exact ⟨_, Or.inr rfl, σ, rfl⟩

omit [Finite K] in
theorem congr_plusEquiv_of_mem_closure (hm : 1 ≤ m)
    {f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))}
    (hf : f ∈ Subgroup.closure
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m))))) :
    ∃ σ : K ≃+* K, MulAut.congr (plusEquiv hm) f = AutOm.fieldAutP m σ := by
  obtain ⟨σ, hσ⟩ := congr_mem_of_mem_closure (plusEquiv hm) (S := (AutOm.fieldAutP m).range)
    (fun g hg => by
      obtain ⟨σ, hσ⟩ := congr_plusEquiv_of_mem_field hm hg
      exact ⟨σ, hσ.symm⟩) hf
  exact ⟨σ, hσ.symm⟩

theorem ggRawInnField_omegaPlus (hm3 : 3 ≤ m) {p : ℕ} (hp : p ≠ 1) :
    GGRawInnField p (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)))) := by
  have hm : 1 ≤ m := by omega
  refine ggRawInnField_of_subgroup hp (inner _) coe_inner_eq_innSet (fun r => ⟨r, rfl⟩)
    fun f hf hfI => ?_
  obtain ⟨σ, hσ⟩ := congr_plusEquiv_of_mem_field hm hf
  have hI := (mem_innSet_iff_congr (plusEquiv hm) f).1 hfI
  rw [hσ] at hI
  have hσ1 := AutOm.eq_one_of_mem_inner_plusCompl hm3 (Or.inl rfl) hI
  subst hσ1
  apply (MulAut.congr (plusEquiv (K := K) hm)).injective
  rw [hσ, map_one, map_one]

theorem commutator_mem_inner_plus (hm5 : 5 ≤ m)
    (α β : MulAut (matrixDerived (coordinateQuadPlus m K))) :
    α * β * α⁻¹ * β⁻¹ ∈ inner (matrixDerived (coordinateQuadPlus m K)) := by
  have hm : 1 ≤ m := by omega
  refine commutator_mem_of_eq_mul (inner _) (AutOm.plusCompl (K := K) hm)
    (fun _ hx _ hy => (commute_of_mem_plusCompl hm hx hy).eq)
    (fun x _ d hd => (inner_normal _).conj_mem d hd x) (fun a => ?_) α β
  obtain ⟨ι, hι, c, hc, h⟩ := AutOm.exists_inner_mul_plusCompl hm5 a
  exact ⟨ι, hι, c, hc, h⟩

theorem ggRawFieldCentral_omegaPlus (hm5 : 5 ≤ m) :
    GGRawFieldCentral (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)))) :=
  ggRawFieldCentral_of_commutator_mem fun α β => by
    rw [mem_innSet_iff_congr (plusEquiv (by omega)), map_mul, map_mul, map_mul, map_inv, map_inv]
    exact commutator_mem_inner_plus hm5 _ _

theorem ggRawFieldCentral_omegaPlusFour (hT : PlusFourTrialityInput) :
    GGRawFieldCentral (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K 4)))) := by
  intro _ _ α u hu f hf
  have h14 : 1 ≤ 4 := by norm_num
  obtain ⟨θ, -, -, hφθ, hgen, -, -⟩ := hT K
  obtain ⟨σ, hσ⟩ := congr_plusEquiv_of_mem_closure h14 hf
  obtain ⟨ι, hι, k, c, hc, hα⟩ := hgen (MulAut.congr (plusEquiv h14) α)
  rw [mem_innSet_iff_congr (plusEquiv h14), map_mul, map_mul, map_mul, map_inv, map_inv, map_mul,
    hσ]
  refine commutator_mem_of_commute (inner _) hι hα ?_ ((mem_innSet_iff_congr _ u).1 hu)
  rw [mul_assoc, (commute_fieldAutP_of_mem_plusCompl h14 σ hc).eq.symm, ← mul_assoc,
    ← AutOm.fieldAutP_mul_pow hφθ σ k, mul_assoc]

theorem ggRawPCyclic_omegaPlus_of (hm : 1 ≤ m) {p M : ℕ} (hpM : Nat.Coprime M p)
    (hdec : ∀ α : MulAut (matrixDerived (coordinateQuadPlus m K)),
      ∃ ι ∈ inner (matrixDerived (coordinateQuadPlus m K)),
        ∃ (y : MulAut (matrixDerived (coordinateQuadPlus m K))) (σ : K ≃+* K),
          y * AutOm.fieldAutP m σ = AutOm.fieldAutP m σ * y ∧ y ^ M = 1 ∧
            α = ι * y * AutOm.fieldAutP m σ) :
    GGRawPCyclic p (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)))) := by
  intro _ _
  set Θ := plusEquiv (K := K) hm
  set Sg : Subgroup (MulAut (matrixDerived (coordinateQuadPlus m K))) :=
    inner _ ⊔ (AutOm.fieldAutP m).range
  have hIn := inner_normal (matrixDerived (coordinateQuadPlus m K))
  refine ⟨inner _, Sg.comap (MulAut.congr Θ).toMonoidHom, coe_inner_eq_innSet,
    fun φ hφ => Subgroup.mem_sup_left ((mem_innSet_iff_congr Θ φ).1 hφ),
    (inner_normal _).subgroupOf _, ?_, fun α ⟨k, hk⟩ => ?_⟩
  · refine ⟨(MulAut.congr Θ).symm (AutOm.fieldAutP m (frobeniusEquiv K 2)), ?_, fun s hs => ?_⟩
    · change MulAut.congr Θ ((MulAut.congr Θ).symm _) ∈ Sg
      rw [MulEquiv.apply_symm_apply]
      exact Subgroup.mem_sup_right ⟨_, rfl⟩
    · obtain ⟨ι, hι, _, ⟨σ, rfl⟩, hs'⟩ := Subgroup.mem_sup_of_normal_left.1 (show
        MulAut.congr Θ s ∈ Sg from hs)
      obtain ⟨i, rfl⟩ := CFSG.RankThree.PartOne.AUTSL.exists_frob_pow σ
      refine ⟨-(i : ℤ), (mem_innSet_iff_congr Θ _).2 ?_⟩
      rw [map_mul, map_zpow, MulEquiv.apply_symm_apply, ← hs', zpow_neg, zpow_natCast, ← map_pow]
      have := hIn.conj_mem ι hι (AutOm.fieldAutP m (frobeniusEquiv K 2 ^ i))⁻¹
      rwa [inv_inv, mul_assoc] at this
  · obtain ⟨ι, hι, y, σ, hyσ, hyM, hα⟩ := hdec (MulAut.congr Θ α)
    refine mem_of_pow_mem_of_coprime _ (a := M) (N := p ^ k) ?_ hk (hpM.pow_right k)
    change MulAut.congr Θ (α ^ M) ∈ Sg
    obtain ⟨ι', hι', h⟩ := exists_pow_eq_mul_pow (inner _) hι hyσ M
    rw [map_pow, hα, h, hyM, mul_one, ← map_pow]
    exact Subgroup.mul_mem_sup hι' ⟨_, rfl⟩

theorem ggRawPCyclic_omegaPlus (hm5 : 5 ≤ m) {p : ℕ} (hp : Odd p) :
    GGRawPCyclic p (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)))) := by
  have hm : 1 ≤ m := by omega
  refine ggRawPCyclic_omegaPlus_of hm (M := 2) (Nat.coprime_two_left.2 hp) fun α => ?_
  obtain ⟨ι, hι, c, hc, hα⟩ := AutOm.exists_inner_mul_plusCompl hm5 α
  obtain ⟨y, hy, σ, rfl⟩ := exists_eq_mul_fieldAutP_of_mem_plusCompl hm hc
  refine ⟨ι, hι, y, σ, ?_, ?_, by rw [hα, mul_assoc]⟩
  · rcases hy with rfl | rfl
    · rw [one_mul, mul_one]
    · exact AutOm.plusRefl_mul_fieldAutP hm σ
  · rcases hy with rfl | rfl
    · exact one_pow 2
    · rw [sq]
      exact AutOm.plusRefl_mul_self hm

theorem ggRawPCyclic_omegaPlusFour (hT : PlusFourTrialityInput) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    GGRawPCyclic p (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K 4)))) := by
  have h14 : 1 ≤ 4 := by norm_num
  have hcop : Nat.Coprime 6 p := by
    rw [show 6 = 2 * 3 by norm_num, Nat.coprime_mul_iff_left]
    exact ⟨(Nat.coprime_primes Nat.prime_two hp).2 hp2.symm,
      (Nat.coprime_primes Nat.prime_three hp).2 hp3.symm⟩
  obtain ⟨θ, h3, hρθ, hφθ, hgen, -, -⟩ := hT K
  refine ggRawPCyclic_omegaPlus_of h14 hcop fun α => ?_
  obtain ⟨ι, hι, k, c, hc, hα⟩ := hgen α
  obtain ⟨y, hy, σ, rfl⟩ := exists_eq_mul_fieldAutP_of_mem_plusCompl h14 hc
  have hyc : y * AutOm.fieldAutP 4 σ = AutOm.fieldAutP 4 σ * y := by
    rcases hy with rfl | rfl
    · rw [one_mul, mul_one]
    · exact AutOm.plusRefl_mul_fieldAutP h14 σ
  refine ⟨ι, hι, θ ^ k * y, σ, ?_, ?_, by rw [hα]; simp only [mul_assoc]⟩
  · rw [mul_assoc, hyc, ← mul_assoc, ← AutOm.fieldAutP_mul_pow hφθ σ k, mul_assoc]
  · rcases hy with rfl | rfl
    · rw [mul_one, ← pow_mul, show k * 6 = 3 * (2 * k) by ring, pow_mul, h3, one_pow]
    · have h2 : (θ ^ k * AutOm.plusRefl h14) ^ 2 = 1 := by
        rw [sq, mul_assoc, ← mul_assoc (AutOm.plusRefl h14),
          AutOm.plusRefl_mul_pow le_rfl h3 hρθ k, mul_assoc, AutOm.plusRefl_mul_self,
          mul_one, ← pow_add, show k + 2 * k = 3 * k by ring, pow_mul, h3, one_pow]
      rw [show 6 = 2 * 3 by norm_num, pow_mul, h2, one_pow]

end Plus

end RecipeFieldOmega

open RecipeFieldOmega

theorem largeEvenLabelAll_omegaPlus {lab : LargeEvenLabel} (ht : lab.tag = .D) (h4 : 4 ≤ lab.rank)
    {P : LargeEvenRawCont}
    (hP : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ lab.n →
      P (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K lab.rank))) (LargeEvenInnSet _)
        (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K lab.rank))))) :
    LargeEvenLabelAll lab P := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht h4 hP ⊢
  subst ht
  intro Q hQ
  have h3 : l ≠ 3 := by omega
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  simp only [h3, ↓reduceIte] at hQ ⊢
  obtain ⟨K, _, _, hK, hQK⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQK, hP K hK⟩

@[expose] def GGOmegaPlusLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .D ∧ 4 ≤ lab.rank

theorem ggRawInnFieldOn_omegaPlus : GGRawInnFieldOn GGOmegaPlusLabel :=
  fun _ hp _ _ _ ⟨ht, h4⟩ => largeEvenLabelAll_omegaPlus ht h4 fun _ _ _ _ _ =>
    ggRawInnField_omegaPlus (by omega) hp.one_lt.ne'

theorem ggRawFieldCentralOn_omegaPlus :
    GGRawFieldCentralOn fun lab => lab.tag = .D ∧ 5 ≤ lab.rank :=
  fun _ _ ⟨ht, h5⟩ => largeEvenLabelAll_omegaPlus ht (by omega) fun _ _ _ _ _ =>
    ggRawFieldCentral_omegaPlus h5

theorem ggRawFieldCentralOn_omegaPlusFour (hT : PlusFourTrialityInput) :
    GGRawFieldCentralOn fun lab => lab.tag = .D ∧ lab.rank = 4 := by
  rintro ⟨t, l, n⟩ _ ⟨ht, h4⟩
  dsimp only at ht h4
  subst h4
  exact largeEvenLabelAll_omegaPlus ht le_rfl fun _ _ _ _ _ => ggRawFieldCentral_omegaPlusFour hT

theorem ggRawPCyclicOn_omegaPlus : GGRawPCyclicOn fun _ lab => lab.tag = .D ∧ 5 ≤ lab.rank :=
  fun _ hp hp2 _ _ ⟨ht, h5⟩ => largeEvenLabelAll_omegaPlus ht (by omega) fun _ _ _ _ _ =>
    ggRawPCyclic_omegaPlus h5 (hp.odd_of_ne_two hp2)

theorem ggRawPCyclicOn_omegaPlusFour (hT : PlusFourTrialityInput) :
    GGRawPCyclicOn fun p lab => lab.tag = .D ∧ lab.rank = 4 ∧ p ≠ 3 := by
  rintro p hp hp2 ⟨t, l, n⟩ _ ⟨ht, h4, hp3⟩
  dsimp only at ht h4
  subst h4
  exact largeEvenLabelAll_omegaPlus ht le_rfl fun _ _ _ _ _ =>
    ggRawPCyclic_omegaPlusFour hT hp hp2 hp3

end CFSG.StandardType
