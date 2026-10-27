module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestOriginalWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinCore
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrType
import CFSG.LocalAnalysis.StandardType.GGSecFiveBFixLine
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSp
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSU
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSUCharts
import CFSG.LocalAnalysis.StandardType.GGSharedInvolution

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem GGSecFiveRouteCfg.le_sup_of_bCoordinateBlock {G : Type} [Group G] [Finite G] {p n : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hTBF : GGTBFixInput) (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B = Bs) (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hAJ : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hAL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    {K₀ : Subgroup G} {i0 : Fin n} (hK₀ : K₀ ∈ 𝒦)
    (hA₀ : (ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    {K : Subgroup G} (hK : K ∈ 𝒦) : K ≤ L ⊔ K₀ := by
  obtain ⟨hp, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  obtain ⟨-, hElem, -, -, -⟩ := hR.1.1.tableB_facts
  have hst : LargeEvenStandardType p B x L := hR.1.1.1.2.2.2.2.2.2.2
  have hDJ : LargeEvenStdSub p B x L D J := hR.1.1.2.2
  have hjoin : (ggAutomizerJoin L Bs {K₀}).map (MulAut.congr eta).toMonoidHom =
      bSignedFull n p := by
    simp only [ggAutomizerJoin, Finset.iSup_singleton, Subgroup.map_sup, hAL, hA₀]
    exact aPermutationFull_sup_bCoordinateBlock p (by omega) i0
  obtain ⟨y, hy⟩ := hR.2.2.2.1.2 K hK
  have hle := le_join_of_signedCoordPosition (𝒦 := {K₀})
    (Nb := fun y K => K ∈ 𝒦 ∧ GGNbr p B x D J y K) (i0 := i0) hp hp2 hn eta
    (fun b hb h2 =>
      eq_one_of_mul_self_eq_one_of_isElemAbelian (hp.odd_of_ne_two hp2) hElem hb h2)
    (hR.1.fixLineComp_L hTBF hR.2.1) (Or.inr (Or.inr hAL)) hjoin
    (fun K' hK' => by
      obtain rfl := Finset.mem_singleton.1 hK'
      obtain ⟨y₀, hy₀⟩ := hR.2.2.2.1.2 _ hK₀
      exact ⟨y₀, hK₀, hy₀⟩)
    (fun _ _ hn' => hR.1.fixLineComp_nbr hFC hR.2.1 hB hn'.2)
    (fun _ _ hn' =>
      hB ▸ (isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hDJ hn'.2)).2)
    (fun _ K' hn' => GGSecFiveRouteCfg.nbr_coordType hX hTCJ hRig hTPn hA8 hraw hiso hFC hR hB
      eta hAJ hn'.2
      (le_sup_of_le_right (le_iSup₂ (f := fun K (_ : K ∈ 𝒦) => ggAutomizer K Bs) K' hn'.1)))
    (fun _ _ _ _ hn' hn₀ => hn'.2.mem_closure_pair hn₀.2)
    (fun _ _ hn' => GGConfig.not_mem_zpowers_of_ggNbr hR.1.1 hn'.2) (y := y) ⟨hK, hy⟩
  simpa only [Finset.iSup_singleton] using hle

theorem GGSecFiveRouteCfg.ggG0_eq_sup_of_selected_bCoordinateBlock {G : Type} [Group G]
    [Finite G] {p n : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)}
    (hTBF : GGTBFixInput) (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B = Bs) (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hAJ : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hAL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    {K₀ : Subgroup G} {i0 : Fin n} (hK₀ : K₀ ∈ 𝒦)
    (hA₀ : (ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hG0 : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K) : ggG0 p B x L D J = L ⊔ K₀ := by
  rw [hG0]
  refine le_antisymm (sup_le le_sup_left (iSup₂_le fun K hK => ?_))
    (sup_le_sup_left (le_iSup₂ (f := fun K (_ : K ∈ 𝒦) => K) K₀ hK₀) L)
  exact hR.le_sup_of_bCoordinateBlock hTBF hX hTCJ hRig hTPn hA8 hraw hiso hFC hB hn eta hAJ hAL
    hK₀ hA₀ hK


theorem GGSecFiveRouteCfg.compat_of_suCell {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hMp : GGInnerDiagMpInput) (hTBF : GGTBFixInput) (hX : GGResXDichotomyInput)
    (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) (hTPn : GGNbrTablePNbrInputNarrow)
    (hA8 : GGForkA8NotReflInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B = Bs) {n a : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hAJ : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hAL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    {K : Subgroup G} {i0 : Fin n} (hcell : GGSecFiveBPermSUCell p Bs L 𝒦 n eta a K i0)
    (hG0 : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K) :
    GGSecFiveCompat p B x L D J := by
  obtain ⟨φ, κ, hφ, hφL, hκinj, hκK, h1, h2, hcross⟩ :=
    ggSecFiveBPermSU_exists_charts hMp hR eta hAL hcell
  have hκker : κ.ker ≤ Subgroup.center _ := by
    rw [(MonoidHom.ker_eq_bot_iff κ).mpr hκinj]
    exact bot_le
  have hG0K : ggG0 p B x L D J = L ⊔ K :=
    hR.ggG0_eq_sup_of_selected_bCoordinateBlock hTBF hX hTCJ hRig hTPn hA8 hraw hiso hFC hB
      (by rw [hcell.1]) eta hAJ hAL hcell.2.2.2.1 hcell.2.2.2.2.2.2 hG0
  exact hR.compat_of_suRanges hcell.2.2.2.1 hcell.2.1 φ hφ κ hκker hκK h1 h2 hcross
    (by rw [hG0K, hφL, hκK])

end CFSG.StandardType

end
