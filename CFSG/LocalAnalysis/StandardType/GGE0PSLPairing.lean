module

public import CFSG.LocalAnalysis.StandardType.GGE0LiftGeneric
public import CFSG.LocalAnalysis.StandardType.GGE0PSLNotDvd
public import CFSG.LocalAnalysis.StandardType.GGE0PSLRigid
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType.ClassicalPosition


theorem ggE0Pairing_PSL {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {m f : ℕ} {ψ : (ggU .PSL (m + 1) f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .PSL (m + 1) f).D .PSL (m + 1) f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) {b g : G} (hg : g ∈ ggM p B x L D J)
    (hEC : D.map (MulAut.conj g⁻¹).toMonoidHom ≤ Subgroup.centralizer {b})
    {s : GL (Fin (m + 1)) (GaloisField 2 f)}
    (hs : IsGLLift Matrix.SpecialLinearGroup.toGL ψ s b) :
    ∀ e ∈ D.map (MulAut.conj g⁻¹).toMonoidHom, ∀ t : GL (Fin (m + 1)) (GaloisField 2 f),
      IsGLLift Matrix.SpecialLinearGroup.toGL ψ t e → Commute t s := by
  have hm : 2 ≤ m := hctx.2.2.2.1.2
  have hker : ψ.ker ≤ Subgroup.center _ := hctx.2.2.2.2.1.2
  have hp := hctx.prime
  have hE₀G1 := map_conj_le_ggG1 ggSteinbergCorrectionAt_PSL hctx hg
    (hctx.d_le_bstar.trans (ggBs_le_ggG1 hctx))
  have hcomm : ∀ e ∈ D.map (MulAut.conj g⁻¹).toMonoidHom, Commute b e := fun e he =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hEC he)).symm
  by_cases hpq : p ∣ Nat.card (GaloisField 2 f) - 1
  · have hB₁G1 := map_conj_le_ggG1 ggSteinbergCorrectionAt_PSL hctx hg (ggBs_le_ggG1 hctx)
    have hcardB₁ : Nat.card ↥(Bs.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card Bs :=
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.sstar.1.2.1
    have hBBs : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hctx.bstar.1
    have hr4 : 4 ≤ LargeEvenTwoLocalRank p G := hctx.beta.2.2.2
    have hrm : m - 1 ≤ LargeEvenTwoLocalRank p G :=
      RootPlaneA.sub_one_le_twoLocalRank (F := GaloisField 2 f) hp hpq (by omega) hker
    have hle : ∀ k ≤ LargeEvenTwoLocalRank p G,
        p ^ k ≤ Nat.card ↥(Bs.map (MulAut.conj g⁻¹).toMonoidHom) := fun k hk => by
      rw [hcardB₁]
      exact (Nat.pow_le_pow_right hp.pos hk).trans (hBcard.symm.le.trans hBBs)
    have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
      rw [hctx.range_eq]
      exact s1.1
    obtain ⟨x', y', hE, hrig⟩ := ggE0_rigid_generators hctx hg
    have hlift : ∀ c ∈ Subgroup.closure ({x', y'} : Set G),
        ∃ t, IsGLLift Matrix.SpecialLinearGroup.toGL ψ t c := by
      intro c hc
      rw [← hE] at hc
      exact exists_isGLLift_PSL m _ ψ hker (hE₀G1 hc).1 (hE₀G1 hc).2
    intro e he t ht
    rw [hE] at he hcomm
    refine isGLLift_commute_of_mem_closure (fun h h' => isGLLift_unique_PSL m _ ψ hker h h')
      hlift (fun z hz t' ht' => ?_) e he t ht
    obtain ⟨hzB, L', hL', hcard⟩ := hrig z hz
    rw [← hctx.range_eq] at hL'
    exact (isGLLift_commute_of_rigid_PSL m hm ψ hker hC hp hctx.ne_two hpq
      (fun b' hb' => (hB₁G1 hb').1) (fun b' hb' => (hB₁G1 hb').2)
      (CFSG.Open.IsElemAbelian.map hctx.bstar.2.1 _) (hle 3 (by omega)) (hle (m - 1) hrm) hzB
      hL' hcard
      (hcomm z (Subgroup.subset_closure hz)) hs ht').symm
  · intro e he t ht
    exact (isGLLift_commute_of_not_dvd_PSL m ψ hker hp hpq
      ((CFSG.Open.IsElemAbelian.map hctx.d_elem _).2 e he) (hcomm e he) hs ht).symm

end CFSG.StandardType
