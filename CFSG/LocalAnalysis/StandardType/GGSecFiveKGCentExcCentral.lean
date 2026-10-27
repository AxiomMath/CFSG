module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotFusionEntrywise
public import CFSG.RankThree.PartOne.KE8F.FamBruhat
import CFSG.LieType.Chevalley.AdjointCenter
import CFSG.LieType.Chevalley.OddF4CosetDescent
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentExcFieldAut
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentExcTwoElt
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType.KGCentExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE8F

theorem mem_centralizer_of_conj_entrywise_fam
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] (hτ : τ = .E7 ∨ τ = .E8)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card Kˣ) {G : Type*} [Group G]
    {ψ : adjointGroup τ K →* G} (hψ : Function.Injective ψ) {t : G}
    (ht : ∃ k : ℕ, t ^ 2 ^ k = 1) {g : adjointGroup τ K} {σ : K ≃+* K}
    (htg : ∀ k, t * ψ k * t⁻¹ = ψ (g * entrywiseAdjointAut τ σ k * g⁻¹))
    (F : Set (Fin τ.rank → Kˣ)) (hFp : ∀ a ∈ F, ∀ i, a i ^ p = 1)
    (hFt : ∀ a ∈ F, ∃ (d : G) (u : adjointGroup τ K), (u : ModGL τ K) = rootDiagUnit τ a ∧
      Commute t d ∧ ∀ k, d * ψ k * d⁻¹ = ψ (u * k * u⁻¹))
    (hS : ∀ β ∈ famKernel F, ∀ c : K,
      Commute t (ψ (SeitzReduction.EPilot.pinnedElt τ β c)))
    (hne : (famKernel F).Nonempty) :
    t ∈ Subgroup.centralizer (ψ.range : Set G) := by
  have hcen : ∀ z : adjointGroup τ K, (∀ k, z * k * z⁻¹ = k) → z = 1 := by
    intro z hz
    have hzc : z ∈ Subgroup.center (adjointGroup τ K) :=
      Subgroup.mem_center_iff.2 fun k => (mul_inv_eq_iff_eq_mul.1 (hz k)).symm
    rwa [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hzc
  have hkey : ∀ β ∈ famKernel F, ∀ c : K, g * SeitzReduction.EPilot.pinnedElt τ β (σ c) * g⁻¹ =
      SeitzReduction.EPilot.pinnedElt τ β c := by
    intro β hβ c
    apply hψ
    rw [← SeitzReduction.EPilot.entrywiseAdjointAut_pinnedElt σ β c, ← htg, (hS β hβ c).eq,
      mul_inv_cancel_right]
  obtain ⟨β₀, hβ₀⟩ := hne
  obtain ⟨β, hβ, hβp⟩ : ∃ β ∈ famKernel F, 0 < height β := by
    rcases IsRoot.height_pos_or_neg hβ₀.1 with h | h
    · exact ⟨β₀, hβ₀, h⟩
    · exact ⟨-β₀, StandardType.LayerExc.neg_mem_famKernel hβ₀, by rw [height_neg]; omega⟩
  have hσ : σ = 1 := entrywise_eq_one_of_conj_pinnedElt (Or.inr hτ) hβ.1 hβp (hkey β hβ)
  have htg1 : ∀ k, t * ψ k * t⁻¹ = ψ (g * k * g⁻¹) := fun k => by
    rw [htg, hσ, entrywiseAdjointAut_one, MulAut.one_apply]
  have hcomm : ∀ a ∈ F, rootDiagUnit τ a * (g : ModGL τ K) * (rootDiagUnit τ a)⁻¹ = g := by
    intro a ha
    obtain ⟨d, u, hu, htd, hd⟩ := hFt a ha
    have hid : ∀ k, g * u * k * (g * u)⁻¹ = u * g * k * (u * g)⁻¹ := fun k => by
      apply hψ
      have e1 : t * (d * ψ k * d⁻¹) * t⁻¹ = ψ (g * u * k * (g * u)⁻¹) := by
        rw [hd, htg1, show g * (u * k * u⁻¹) * g⁻¹ = g * u * k * (g * u)⁻¹ by group]
      have e2 : d * (t * ψ k * t⁻¹) * d⁻¹ = ψ (u * g * k * (u * g)⁻¹) := by
        rw [htg1, hd, show u * (g * k * g⁻¹) * u⁻¹ = u * g * k * (u * g)⁻¹ by group]
      have e3 : t * (d * ψ k * d⁻¹) * t⁻¹ = d * (t * ψ k * t⁻¹) * d⁻¹ := by
        calc t * (d * ψ k * d⁻¹) * t⁻¹ = t * d * ψ k * (t * d)⁻¹ := by group
          _ = d * t * ψ k * (d * t)⁻¹ := by rw [htd.eq]
          _ = d * (t * ψ k * t⁻¹) * d⁻¹ := by group
      rw [← e1, ← e2, e3]
    have hgu : g * u = u * g := inv_mul_eq_one.1 (hcen _ fun k => by
      rw [show (g * u)⁻¹ * (u * g) * k * ((g * u)⁻¹ * (u * g))⁻¹ =
        (g * u)⁻¹ * (u * g * k * (u * g)⁻¹) * (g * u) by group, ← hid k]
      group)
    have hgu' : (u : ModGL τ K) * g = g * u := (congrArg Subtype.val hgu).symm
    rw [← hu, hgu', mul_inv_cancel_right]
  have hle : rootSpan τ K (famKernel F) ≤ Subgroup.centralizer {(g : ModGL τ K)} := by
    refine iSup₂_le fun β hβ => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    have e : (g : ModGL τ K) * pinnedX τ K β c * (g : ModGL τ K)⁻¹ = pinnedX τ K β c := by
      have h := hkey β hβ c
      rw [hσ] at h
      exact congrArg Subtype.val h
    exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 e).symm
  have hcent : (g : ModGL τ K) ∈
      Subgroup.centralizer (rootSpan τ K (famKernel F) : Set (ModGL τ K)) :=
    Subgroup.mem_centralizer_iff.2 fun y hy => Subgroup.mem_centralizer_singleton_iff.1 (hle hy)
  obtain ⟨m, hm⟩ := ht
  have hpow : ∀ n : ℕ, ∀ k, t ^ n * ψ k * (t ^ n)⁻¹ = ψ (g ^ n * k * (g ^ n)⁻¹) := by
    intro n
    induction n with
    | zero => exact fun k => by simp
    | succ n ih =>
      intro k
      calc t ^ (n + 1) * ψ k * (t ^ (n + 1))⁻¹ = t ^ n * (t * ψ k * t⁻¹) * (t ^ n)⁻¹ := by
            group
        _ = ψ (g ^ n * (g * k * g⁻¹) * (g ^ n)⁻¹) := by rw [htg1, ih]
        _ = ψ (g ^ (n + 1) * k * (g ^ (n + 1))⁻¹) := by
            congr 1
            group
  have hg2 : g ^ 2 ^ m = 1 := hcen _ fun k => by
    apply hψ
    rw [← hpow, hm]
    group
  have hg1 : (g : ModGL τ K) = 1 :=
    eq_one_of_commute_famKernel_rootSpan hτ hp hp2 hpK F hFp g.2
      ⟨m, by simpa using congrArg Subtype.val hg2⟩ hcomm hcent
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨k, rfl⟩
  have e := htg1 k
  have hg1' : g = 1 := Subtype.ext hg1
  rw [hg1', one_mul, inv_one, mul_one] at e
  exact (mul_inv_eq_iff_eq_mul.1 e).symm

end CFSG.StandardType.KGCentExc

end
