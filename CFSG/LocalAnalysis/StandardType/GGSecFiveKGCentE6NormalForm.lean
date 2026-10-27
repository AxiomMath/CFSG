module

public import CFSG.RankThree.PartOne.KE8F.FamBruhat
public import CFSG.LieType.Chevalley.ExactNormalFormE
public import CFSG.LieType.Chevalley.RootCharacterConjugation
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6TwistBruhat
import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangCore
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType

namespace KGCentE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE8F

theorem exists_normalForm_mul_canonicalRep_E6
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    {F : Set (Fin Tag.E6.rank → Kˣ)} (hF : famKernel F = ∅) {α : MulAut (adjointGroup .E6 K)}
    (hαF : ∀ a ∈ F, α * rootDiagAutHom .E6 K a = rootDiagAutHom .E6 K a * α) :
    ∃ (h : ModGL .E6 K) (w : WeylGroup Tag.E6) (a : Fin Tag.E6.rank → Kˣ) (σ : K ≃+* K)
      (ε : Fin (exactE .E6)), h ∈ torusGroup .E6 K ∧
      (∀ x : adjointGroup .E6 K, ((α x : adjointGroup .E6 K) : ModGL .E6 K) =
        h * canonicalRep (coxeterSystem .E6) K w * exactNormalAutGL .E6 K a σ ε (x : ModGL .E6 K) *
          (h * canonicalRep (coxeterSystem .E6) K w)⁻¹) ∧
      ∀ b ∈ F, canonicalRep (coxeterSystem .E6) K w *
        exactNormalAutGL .E6 K a σ ε (rootDiagUnit .E6 b) *
          (canonicalRep (coxeterSystem .E6) K w)⁻¹ = rootDiagUnit .E6 b := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨-, -, hex⟩ := ordinary_E_exact_automorphism_normal_form .E6 (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hga⟩ := hex α
  set ψ := exactNormalAutGL .E6 K a σ ε with hψ
  have hαx : ∀ x : adjointGroup .E6 K, ((α x : adjointGroup .E6 K) : ModGL .E6 K) =
      (g : ModGL .E6 K) * ψ (x : ModGL .E6 K) * (g : ModGL .E6 K)⁻¹ := by
    intro x
    rw [hga x, hψ, exactNormalAutGL_apply]
    group
  have hψd : ∀ b : Fin Tag.E6.rank → Kˣ, ∃ c, ψ (rootDiagUnit .E6 b) = rootDiagUnit .E6 c := by
    intro b
    obtain ⟨c, hc⟩ := exists_exactQ_conj_rootDiagUnit (K := K) ε
      (fun i => Units.map σ.toRingHom.toMonoidHom (b i))
    refine ⟨c, ?_⟩
    rw [hψ, exactNormalAutGL_apply, units_map_entrywiseHom_rootDiagUnit_ringEquiv]
    calc _ = rootDiagUnit .E6 a * (exactQ .E6 K ε *
          rootDiagUnit .E6 (fun i => Units.map σ.toRingHom.toMonoidHom (b i)) *
            (exactQ .E6 K ε)⁻¹) * (rootDiagUnit .E6 a)⁻¹ := by group
      _ = rootDiagUnit .E6 c := by
        rw [hc, rootDiagUnit_inv, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm a c,
          mul_inv_cancel_right]
  have hgc : ∀ b ∈ F, ∀ c, ψ (rootDiagUnit .E6 b) = rootDiagUnit .E6 c →
      (g : ModGL .E6 K) * rootDiagUnit .E6 c = rootDiagUnit .E6 b * g := by
    intro b hb c hc
    set G : ModGL .E6 K := (g : ModGL .E6 K)
    set db := rootDiagUnit .E6 b
    set dc := rootDiagUnit .E6 c
    have hsI : db⁻¹ * G * dc * G⁻¹ ∈ RecipeExcLang.inndiagGroup .E6 K :=
      mul_mem (mul_mem (mul_mem (inv_mem (RecipeExcLang.rootDiagUnit_mem_inndiagGroup b))
        (RecipeExcLang.adjointGroup_le_inndiagGroup g.2))
          (RecipeExcLang.rootDiagUnit_mem_inndiagGroup c))
        (inv_mem (RecipeExcLang.adjointGroup_le_inndiagGroup g.2))
    have hs := RecipeExcLang.eq_one_of_commute_adjointGroup hK4 hsI fun y hy => by
      obtain ⟨x, hx⟩ := α.surjective ⟨y, hy⟩
      have hδ : ∀ z : adjointGroup .E6 K,
          ((rootDiagAutHom .E6 K b z : adjointGroup .E6 K) : ModGL .E6 K) = db * z * db⁻¹ :=
        fun _ => rfl
      have h1 := congrArg (fun φ : MulAut (adjointGroup .E6 K) =>
        ((φ x : adjointGroup .E6 K) : ModGL .E6 K)) (hαF b hb)
      simp only [MulAut.mul_apply] at h1
      rw [hαx, hδ, hδ, hαx x, map_mul, map_mul, map_inv, hc] at h1
      have hy' : y = G * ψ (x : ModGL .E6 K) * G⁻¹ := by
        rw [← hαx, hx]
      rw [hy']
      calc db⁻¹ * G * dc * G⁻¹ * (G * ψ x * G⁻¹) =
          db⁻¹ * (G * (dc * ψ x * dc⁻¹) * G⁻¹) * (G * dc * G⁻¹) := by group
        _ = db⁻¹ * (db * (G * ψ x * G⁻¹) * db⁻¹) * (G * dc * G⁻¹) := by rw [h1]
        _ = G * ψ x * G⁻¹ * (db⁻¹ * G * dc * G⁻¹) := by group
    calc G * dc = db * (db⁻¹ * G * dc * G⁻¹) * G := by group
      _ = db * G := by rw [hs]; group
  have hg1 : (g : ModGL .E6 K) ∈ toralCentralizer .E6 K 1 := by
    rw [mem_toralCentralizer, rootDiagUnit_one]
    exact ⟨g.2, by simp⟩
  obtain ⟨w, -, h, hh, u, hu, v, hv, hgf⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors .E6 K (1 : Fin Tag.E6.rank → Kˣ)).1 _ hg1
  have hu₀ : u ∈ posUnipotent .E6 K := rootSpan_mono Set.inter_subset_right hu
  have hv₀ : v ∈ rootSpan .E6 K (inversionSet w) := rootSpan_mono Set.inter_subset_right hv
  have htw : ∀ b ∈ F, ∀ c, ψ (rootDiagUnit .E6 b) = rootDiagUnit .E6 c →
      rootDiagUnit .E6 b * u * (rootDiagUnit .E6 b)⁻¹ = u ∧
        rootDiagUnit .E6 c * v * (rootDiagUnit .E6 c)⁻¹ = v ∧
        rootDiagUnit .E6 b = canonicalRep (coxeterSystem .E6) K w * rootDiagUnit .E6 c *
          (canonicalRep (coxeterSystem .E6) K w)⁻¹ := by
    intro b hb c hc
    have := hgc b hb c hc
    rw [hgf] at this
    exact twisted_torus_bruhat_of_diag hh hu₀ hv₀ this
  have hbot : rootSpan .E6 K (∅ : Set (Fin Tag.E6.rank → ℤ)) = ⊥ := by simp [rootSpan]
  have hposfin : {β : Fin Tag.E6.rank → ℤ | IsRoot .E6 β ∧ 0 < height β}.Finite :=
    (finite_setOf_isRoot .E6).subset fun β hβ => hβ.1
  have hu1 : u = 1 := by
    have hmem := mem_rootSpan_famKernel_of_conj_eq F hposfin (fun β hβ => hβ.1)
      (fun α hα hr => (positive_root_collection .E6 K).2 α hα hr) hu₀ fun b hb =>
        (htw b hb _ (hψd b).choose_spec).1
    rwa [hF, Set.empty_inter, hbot, Subgroup.mem_bot] at hmem
  set F₂ : Set (Fin Tag.E6.rank → Kˣ) := {c | ∃ b ∈ F, ψ (rootDiagUnit .E6 b) = rootDiagUnit .E6 c}
  have hF₂ : famKernel F₂ = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun γ hγ => ?_
    have hwγ : w • γ ∈ famKernel F := by
      refine ⟨CFSG.LieType.Chevalley.IsRoot.smul hγ.1 w, fun b hb => ?_⟩
      obtain ⟨c, hc⟩ := hψd b
      rw [(rootDiagUnit_eq_conj_canonicalRep_iff b c w).1 (htw b hb c hc).2.2 γ]
      exact hγ.2 c ⟨b, hb, hc⟩
    rw [hF] at hwγ
    simp at hwγ
  have hv1 : v = 1 := by
    have hmem := mem_rootSpan_famKernel_of_conj_eq F₂ (inversionSet_finite w) (fun β hβ => hβ.1)
      (fun α hα hr => (bruhat_cell_factorization .E6 K).2.1 w α hα hr) hv₀
      fun c ⟨b, hb, hc⟩ => (htw b hb c hc).2.1
    rwa [hF₂, Set.empty_inter, hbot, Subgroup.mem_bot] at hmem
  refine ⟨h, w, a, σ, ε, hh, fun x => ?_, fun b hb => ?_⟩
  · rw [hαx x, hgf, hu1, hv1]
    simp only [mul_one, hψ]
  · obtain ⟨c, hc⟩ := hψd b
    rw [hc, ← (htw b hb c hc).2.2]

end KGCentE6

end CFSG.StandardType

end
