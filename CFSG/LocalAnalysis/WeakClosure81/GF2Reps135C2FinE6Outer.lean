module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinE6Module
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Ctx
import CFSG.Quasithin.Background.StabSubBasics

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
open CFSG.Quasithin.SmithCurtis CFSG.QuasithinUnique.Setup
open CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem mem_normalizer_of_isContext {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} (hctx : Is135Context Y L) {g : MulAut W} (hg : g ∈ Y) :
    g ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
  have hLY : L ≤ Y := hctx.2.2.1
  have hN := w135_normal_of_ctx hctx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have := hN.conj_mem ⟨h, hLY hh⟩ (Subgroup.mem_subgroupOf.mpr hh) ⟨g, hg⟩
    simpa using Subgroup.mem_subgroupOf.mp this
  · intro hh
    have := hN.conj_mem ⟨g * h * g⁻¹, hLY hh⟩ (Subgroup.mem_subgroupOf.mpr hh)
      ⟨g⁻¹, Y.inv_mem hg⟩
    simpa [mul_assoc] using Subgroup.mem_subgroupOf.mp this


theorem mem_of_normalizer_of_isE6TwentySevenType
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : X1.IsIrrOn L)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (eS : ↥L ⧸ Subgroup.center ↥L ≃* ↥(adjointGroup .E6 K)) (D : HatData K ↥L)
    (hDf : ∀ x : ↥L, D.f x = eS (QuotientGroup.mk x))
    {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra K k] {m : ℕ}
    {ρ : Representation k ↥L (Fin m → k)} (hρ : IsSimpleRep ρ)
    (hty : IsE6TwentySevenType (ρ.comp D.π))
    {b : MulAut W} (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) (hb2 : b * b = 1)
    (B : Module.End k (Fin m → k)) (hBu : IsUnit B)
    (hBρ : ∀ s : ↥L, B * ρ s = ρ (X1.conjAut L hb s) * B) : b ∈ L := by
  classical
  obtain ⟨y, χ, s, hs, ht, hχ⟩ := hty
  have hK2 : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  obtain ⟨g, a, σ, ε, hαe, h1, h2⟩ :=
    outer_params (n := 1) hK2 eS D hDf hρ ht hb B hBu hBρ
  have hεs : ¬ s = (⟨1, by decide⟩ : N6) → (ε : ℕ) = 0 := by
    intro hs1
    rcases exactPerm_cases ε with h0 | h0
    · exact h0
    · exfalso
      have hh := h2 s
      rw [h0] at hh
      have hh' : exactPerm .E6 1 s = s := by
        by_contra hne
        have hB : (exactPerm .E6 1) s ∈ Finset.univ.erase s := by
          rw [Finset.mem_erase]
          exact ⟨hne, Finset.mem_univ _⟩
        have hA : s ∈ Finset.univ.erase s := hh.mpr hB
        simp [Finset.mem_erase] at hA
      rcases hs with rfl | rfl
      · exact perm_zero_ne hh'
      · exact perm_five_ne hh'
  have hs1 : ¬ s = (⟨1, by decide⟩ : N6) := by
    rcases hs with h0 | h5
    · rw [h0]; decide
    · rw [h5]; decide
  have hε : (ε : ℕ) = 0 := hεs hs1
  have hperm : exactPerm .E6 ε s = s := by
    rcases exactPerm_cases ε with h0 | h0
    · rw [h0, exactPerm_zero]; rfl
    · rw [h0]
      by_cases h1s : s = (⟨1, by decide⟩ : N6)
      · rw [h1s]; exact perm_one_fix
      · exact absurd (hεs h1s) (by omega)
  have hσ : σ = 1 := by
    refine RingEquiv.ext fun c => ?_
    by_cases hc : c = 0
    · rw [hc, map_zero]; rfl
    · have h1' := h1 s (Units.mk0 c hc)
      rw [hperm, hχ s, hχ s] at h1'
      simp only [ite_true] at h1'
      have h4 : σ c = c := RingHom.injective (algebraMap K k) h1'
      simpa using h4
  obtain ⟨Θ, -, hΘrel, hΘker, -, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions .E6 (Or.inl rfl) K
  have hΘ : Θ (psiAut L eS hb) = 1 := by
    rw [hΘrel _ g a σ ε (expr_of_eq hαe), hσ, hε]
    simp
  have hel : IsElemAbelian2 (Subgroup.zpowers b) :=
    CFSG.Quasithin.StabLat.isElemAbelian2_zpowers (by rw [pow_two]; exact hb2)
  have hEN : Subgroup.zpowers b ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    Subgroup.zpowers_le.2 hb
  exact mem_of_theta_one hW hperf hirr hEN hel eS Θ hΘker e6InnerOfSqOne_holds
    (Subgroup.mem_zpowers b) hΘ

end CFSG.LocalAnalysis.WeakClosure81
