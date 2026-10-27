module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePrimDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpSameSuppRoots
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpLayerSub
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpRankOneQS
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpMoves
import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

theorem ggDk_pumpup_sameSupp
    (hKG : GGSecFiveKGPosInput) (hLB : GGLBalanceInput) (hSplit : GGSecFiveSplitNbrInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hsplit : GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {k : ℕ} (hk : 4 ≤ k) {σ : Fin k ≃ ι}
    (hM : M = (ggCoxeterMatrixD k).reindex σ) (φ : M.Group ≃* ggWeylD k)
    (hφ : ∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a)
    (hss : GGDNoSameSupp e φ) {a₀ : Fin k} {d₀ : ↥Bs}
    (hD : D = Subgroup.closure {x, (d₀ : G)}) (hpt : GGDPumpPt e φ a₀ d₀)
    (hpJ : p ∣ Nat.card J)
    (hJ : ∀ η : Fin k → ℤ, η ∈ ggDMemberRoots e φ J ↔ η ∈ ggDMemberRoots e φ L ∧ η a₀ = 0) :
    ∃ t t' : M.Group, GGDSameSupp k (φ t) (φ t') ∧
      ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈
        ggAutomizer (ggLayerClosure p (Subgroup.centralizer ({(d₀ : G)} : Set G)) J) Bs ∧
      ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈
        ggAutomizer (ggLayerClosure p (Subgroup.centralizer ({(d₀ : G)} : Set G)) J) Bs ∧
      ∃ xb : ↥Bs, (xb : G) = x ∧ ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) xb ≠ xb := by
  obtain ⟨K₁, hK₁, t₁, tδ, tρ, tσ, ht₁K, hrefl, htδ, htρ, htσ, hSS, hx, ht₁d, ht'd, ht'w⟩ :=
    ggDk_pumpup_roots hKG hLB hcfg hsplit hpres hle3 hk hM φ hφ hss hpt hpJ hJ
  have hJKd := le_ggLayerClosure p (Subgroup.centralizer ({(d₀ : G)} : Set G)) J
  refine ⟨tσ, tδ * t₁ * tδ⁻¹, hSS, ggAutomizer_mono Bs hJKd htσ, ?_, hx⟩
  have hE : ((e (tδ * t₁ * tδ⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
      ((e tδ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
        ((e t₁ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
        ((e tδ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)⁻¹ := by
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hE] at ht'd ht'w ⊢
  have hBs : ∀ a b : ↥Bs, a * b = b * a := (ggRouteCfg_isElemAbelian hcfg).1.is_comm.comm
  obtain ⟨y₁, hnbr⟩ := hcfg.2.2.2.1.2 K₁ hK₁
  have hK := (isComponentOf_of_isNeighborOf hcfg.1.1.1.2.2.2.2.2.2.2
    (isNeighborOf_of_ggNbr hcfg.1.1.2.2 hnbr)).1
  have hy₁B : y₁ ∈ Bs := hcfg.1.1.2.1.1 hnbr.1.2.1
  have hy₁ : y₁ ∈ (ggHyperplane Bs ((e t₁ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) : Set G) :=
    ⟨⟨y₁, hy₁B⟩, ggAutomizer_apply_eq_of_le_centralizer (x := ⟨y₁, hy₁B⟩) hK.1 ht₁K, rfl⟩
  have hpre := hcfg.1.1.2.2.1
  have hBsD : Bs ≤ Subgroup.centralizer (D : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun d hd =>
      congrArg Subtype.val (hBs ⟨d, hcfg.1.1.2.1.1 (hpre.1 hd)⟩ ⟨b, hb⟩)
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) := by
    rw [hpre.2.2.2.2.1]
    exact le_normalizer_of_map_conj_le fun g hg => map_conj_largeEvenLayer_le
      (mem_normalizer_inf_centralizer (GGInnerDiagOn.le_normalizer hcfg.1.2.2.1.1 hg) (hBsD hg))
  have hb' : ((((e tδ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
      ((e t₁ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
      ((e tδ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)⁻¹)
      (((e tδ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) d₀)) ≠
      ((e tδ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) d₀ := by
    intro h
    apply ht₁d
    simpa only [MulAut.mul_apply, MulAut.inv_apply_self] using
      congrArg (fun z : ↥Bs => (((e tδ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs))⁻¹ z) h
  exact ggPumpup_mem_ggAutomizer_of_moves hBs hK
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hy₁))
    (ggRankOneIn_isQuasisimple_of_kgPos hKG hcfg hsplit hpres hle3 (Or.inr hK₁)
      (hSplit G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 K₁ hK₁) ht₁K hrefl)
    ht₁K ((sq _).symm.trans hrefl.1)
    (ggLayerClosure_isSubnormal_of_stdSub hLB hcfg.1.1.1 hcfg.1.1.2.2 hpJ hD)
    hJKd hBsJ htδ htρ ht'd ht'w hb'

end CFSG.StandardType

end
