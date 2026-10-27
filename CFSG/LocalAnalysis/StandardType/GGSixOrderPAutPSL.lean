module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAut
public import CFSG.LocalAnalysis.StandardType.GGHypSixTypeA

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

namespace OrdPAut

section Main

variable {K : Type} [Field K] [Finite K] {m : ℕ} {G : Type*} [Group G]
  {ψ : SpecialLinearGroup (Fin (m + 1)) K →* G}

theorem ggPsiDiagField_sl (hm : 2 ≤ m)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) K))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {p : ℕ} (hp : Odd p) {c : G}
    (hc : c ∈ Subgroup.normalizer (ψ.range : Set G)) (hcp : c ^ p = 1) :
    GGPsiDiagField (SpecialLinear.rootDatum m K) ψ c := by
  have hn : 3 ≤ m + 1 := by omega
  obtain ⟨α, hα⟩ := HypSixTypeA.exists_projAut hn hker hc
  have hαp : α ^ p = 1 := by
    ext x
    obtain ⟨y, rfl⟩ := proj_surjective (m + 1) K x
    rw [MulAut.one_apply]
    apply HypSixTypeA.projAut_pow_apply hker hc hα p y y
    rw [hcp]
    group
  obtain ⟨A, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := K) hn).2 α
  have hε0 : ε = 0 := HypSixTypeA.graph_exp_eq_zero hn hp hε (by rw [← hαeq]; exact hαp)
  subst hε0
  rw [pow_zero, mul_one] at hαeq
  have hkerS : ψ.ker = scalars (m + 1) K := AutPSL.ker_eq_scalars hker hC
  have hpsi : ∀ a b : SpecialLinearGroup (Fin (m + 1)) K,
      proj (m + 1) K a = proj (m + 1) K b → ψ a = ψ b := by
    intro a b h
    have h' := proj_eq_proj_iff.mp h
    rw [← hkerS, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h'
    exact h'
  set d : K := (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K).det with hd
  have hd0 : d ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero A
  set e : Fin (m + 1) → K := fun l => if l = 0 then d else 1 with he
  have he0 : ∀ l, e l ≠ 0 := fun l => by
    simp only [e]
    split_ifs
    exacts [hd0, one_ne_zero]
  have hdetD : (Matrix.diagonal e).det = d := by
    rw [Matrix.det_diagonal]
    simp [e]
  set D : GL (Fin (m + 1)) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal e)
    (by rw [hdetD]; exact hd0)
  have hDval : (D : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = Matrix.diagonal e := rfl
  have hdet1 : Matrix.GeneralLinearGroup.det (A * D⁻¹) = 1 := by
    rw [map_mul, map_inv, mul_inv_eq_one]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hDval,
      hdetD]
  obtain ⟨A₀, hA₀⟩ : A * D⁻¹ ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin (m + 1)) K →*
      GL (Fin (m + 1)) K).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet1
  set cD := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation (m + 1) K D
  set cA := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation (m + 1) K A
  have hkey : ∀ w, A₀⁻¹ * cA w * A₀ = cD w := by
    intro w
    apply SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, map_inv,
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, hA₀]
    group
  refine ⟨ψ A₀, ⟨A₀, rfl⟩, fun γ hγ z hz => ?_⟩
  have hij : (SpecialLinear.idx m γ).1 ≠ (SpecialLinear.idx m γ).2 :=
    (SpecialLinear.idx_spec m hγ).1
  change z ∈ SpecialLinear.rootGroup m K γ at hz
  rw [SpecialLinear.rootGroup_eq_idx m K hγ] at hz
  obtain ⟨t, rfl⟩ := (SpecialLinear.mem_rootSubgroup hij z).mp hz
  set i := (SpecialLinear.idx m γ).1
  set j := (SpecialLinear.idx m γ).2
  refine ⟨SpecialLinearGroup.transvection hij (e i * σ t * (e j)⁻¹), ?_, ?_⟩
  · change _ ∈ SpecialLinear.rootGroup m K γ
    rw [SpecialLinear.rootGroup_eq_idx m K hγ]
    exact SpecialLinear.transvection_mem_rootSubgroup hij _
  · obtain ⟨z₁, hz₁⟩ := HypSixTypeA.exists_conj_preimage hc (SpecialLinearGroup.transvection hij t)
    have hproj : proj (m + 1) K z₁ = proj (m + 1) K (cA (SpecialLinearGroup.transvection hij (σ t)))
        := by
      rw [← hα _ _ hz₁, hαeq, MulAut.mul_apply, AutPSL.fieldAut_proj_transvection, conjAut_proj]
    calc (c * ψ A₀)⁻¹ * ψ (SpecialLinearGroup.transvection hij t) * (c * ψ A₀) =
        ψ (A₀⁻¹ * z₁ * A₀) := by
          rw [map_mul, map_mul, map_inv, hz₁]
          group
      _ = ψ (A₀⁻¹ * cA (SpecialLinearGroup.transvection hij (σ t)) * A₀) := by
          apply hpsi
          rw [map_mul, map_mul, map_mul, map_mul, hproj]
      _ = ψ (SpecialLinearGroup.transvection hij (e i * σ t * (e j)⁻¹)) := by
          rw [hkey, HypSixTypeA.slConjugation_diag_transvection he0 hDval hij (σ t)]

end Main

end OrdPAut

section Family

theorem ggOrdPGraphAt_PSL : GGOrdPGraphAt .PSL := by
  intro G _ _ n f ψ G₀ hpres hC p hp hp2 y hyM hyp hDF
  exfalso
  apply hDF
  obtain ⟨⟨hadm, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  have hm : 2 ≤ m := hrank
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← hrange] at hyM hC
  exact OrdPAut.ggPsiDiagField_sl (K := GaloisField 2 f) hm hker hC (hp.odd_of_ne_two hp2) hyM hyp

theorem ggSixLSixElevenKGInput_of_rest (h1 : ∀ t, ¬ GGOrdPSmallTag t → GGOrdPInnerConjAt t)
    (h2 : ∀ t, ¬ GGOrdPSmallTag t → GGOrdPFieldConjAt t)
    (h3 : ∀ t, (t = .PSL ∨ t = .PSU ∨ t = .E6 ∨ t = .twistedE6) → GGOrdPOutdiagAt t)
    (h4 : ∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → GGOrdPGraphAt t) (h5 : GGOrdPTrialityInput) :
    GGSixLSixElevenKGInput := by
  refine ggSixLSixElevenKGInput_of_kinds (fun t => ?_) (fun t => ?_) (fun t => ?_) (fun t => ?_) h5
  · by_cases ht : GGOrdPSmallTag t
    · exact ggOrdPInnerConjAt_of_small ht
    · exact h1 t ht
  · by_cases ht : GGOrdPSmallTag t
    · exact ggOrdPFieldConjAt_of_small ht
    · exact h2 t ht
  · by_cases ht : t = .PSL ∨ t = .PSU ∨ t = .E6 ∨ t = .twistedE6
    · exact h3 t ht
    · exact ggOrdPOutdiagAt_of_not ⟨fun h => ht (Or.inl h), fun h => ht (Or.inr (Or.inl h)),
        fun h => ht (Or.inr (Or.inr (Or.inl h))), fun h => ht (Or.inr (Or.inr (Or.inr h)))⟩
  · by_cases ht : GGOrdPSmallTag t
    · exact ggOrdPGraphAt_of_small ht
    · by_cases hP : t = .PSL
      · subst hP
        exact ggOrdPGraphAt_PSL
      · exact h4 t ht hP

end Family

end CFSG.StandardType
