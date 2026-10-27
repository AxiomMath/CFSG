module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBUniFourCharts
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseNonsplitFrames
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseEndpoint
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockGeneration
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKCrossing
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpSp
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrAxis

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.Models.OrthogonalPairs

section LiftCharts

variable {G F K : Type} [Group G] [Field F] [Field K] [Algebra F K]
  [Finite K] [CharP K 2] {f p : ℕ}
  {E : QuadExt F K (unitaryInvolution K 2 f)}

@[expose] noncomputable def orthFourChartOfLifts
    (κ : normOmega E 3 →* G) (w : Fin 4 → G) (i : Fin 4) : normOmega E 3 →* G :=
  (MulAut.conj (w i)).toMonoidHom.comp κ

theorem orthFourChartOfLifts_three (κ : normOmega E 3 →* G) (w : Fin 4 → G)
    (hw : w 3 = 1) : orthFourChartOfLifts κ w 3 = κ := by
  ext g
  simp [orthFourChartOfLifts, hw]

theorem orthFourChartOfLifts_range (κ : normOmega E 3 →* G) (w : Fin 4 → G)
    {L : Subgroup G} (hκ : κ.range = L) (i : Fin 4) :
    (orthFourChartOfLifts κ w i).range = L.map (MulAut.conj (w i)).toMonoidHom := by
  rw [orthFourChartOfLifts, MonoidHom.range_comp, hκ]

theorem orthFourChartOfLifts_frame [Finite G] {Bs L : Subgroup G}
    {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin 4)}
    {κ : normOmega E 3 →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs L eta π κ χ) (w : Fin 4 → G) (i : Fin 4)
    (hw : w i ∈ Subgroup.normalizer (Bs : Set G))
    (hact : MulAut.congr eta (ggConjAut Bs hw) =
      SpCoord.permAut (π * uniFourTau i * π⁻¹)) :
    GGSecFiveBPermOmKFrame E Bs (L.map (MulAut.conj (w i)).toMonoidHom)
      eta ((uniFourTau i).trans π) (orthFourChartOfLifts κ w i) χ := by
  have h := hκ.conj_transporter hw hact
  have hπ : π.trans (π * uniFourTau i * π⁻¹) = (uniFourTau i).trans π := by
    ext a
    simp [Equiv.Perm.mul_apply]
  rw [hπ] at h
  exact h

theorem orthFourChartOfLifts_pair [Finite G] [Fact p.Prime] {Bs L : Subgroup G} {x : G}
    {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin 4)}
    {κ : normOmega E 3 →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs L eta π κ χ) (w : Fin 4 → G) (i : Fin 4)
    (hw : w i ∈ Subgroup.normalizer (Bs : Set G))
    (hact : MulAut.congr eta (ggConjAut Bs hw) =
      SpCoord.permAut (π * uniFourTau i * π⁻¹))
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hL : CFSG.Open.IsComponentOf L (Subgroup.centralizer {x})) (hx : x ∈ Bs)
    {s t : Fin 3} (hst : s ≠ t) :
    (normBlock E 3 {s, t}).map (orthFourChartOfLifts κ w i) =
      ggBlockComm Bs eta ({π (i.succAbove s), π (i.succAbove t)} : Set (Fin 4)) := by
  have hfr := orthFourChartOfLifts_frame hκ w i hw hact
  have hX : CFSG.Open.IsComponentOf (L.map (MulAut.conj (w i)).toMonoidHom)
      (Subgroup.centralizer {w i * x * (w i)⁻¹}) :=
    isComponentOf_iff_open.mp
      (isComponentOf_centralizer_map_conj (isComponentOf_iff_open.mpr hL) (w i))
  have hy : w i * x * (w i)⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hw x).mp hx
  have hcard : ({s, t} : Finset (Fin 3)).card = 2 := Finset.card_pair hst
  have h := hfr.blockComm_eq_map_normBlock hSC hy hX (S := {s, t}) (by omega) (by omega)
  rw [← h]
  congr 1
  rw [Finset.coe_pair, Set.image_pair]
  exact congrArg₂ (fun a b => ({a, b} : Set (Fin 4)))
    (congrArg π (uniFourTau_castSucc i s)) (congrArg π (uniFourTau_castSucc i t))

theorem orthFourChartOfLifts_singleton [Finite G] [Fact p.Prime] {Bs L : Subgroup G} {x : G}
    {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin 4)}
    {κ : normOmega E 3 →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs L eta π κ χ) (w : Fin 4 → G) (i : Fin 4)
    (hw : w i ∈ Subgroup.normalizer (Bs : Set G))
    (hact : MulAut.congr eta (ggConjAut Bs hw) =
      SpCoord.permAut (π * uniFourTau i * π⁻¹))
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hL : CFSG.Open.IsComponentOf L (Subgroup.centralizer {x})) (hx : x ∈ Bs)
    (hpq : p ∣ 2 ^ f + 1) {s t : Fin 3} (hst : s ≠ t) :
    (normBlock E 3 {s}).map (orthFourChartOfLifts κ w i) =
      ggSingletonFrom Bs eta (π (i.succAbove s)) (π (i.succAbove t)) := by
  have hfr := orthFourChartOfLifts_frame hκ w i hw hact
  have hb : eta (eta.symm (Pi.mulSingle (π (i.succAbove t)) (Multiplicative.ofAdd 1))) =
      Pi.mulSingle (((uniFourTau i).trans π) t.castSucc) (Multiplicative.ofAdd 1) := by
    rw [MulEquiv.apply_symm_apply, Equiv.trans_apply, uniFourTau_castSucc]
  rw [hfr.map_normBlock_singleton (by norm_num) hpq hst _ hb,
    orthFourChartOfLifts_pair hκ w i hw hact hSC hL hx hst, ggSingletonFrom]

theorem orthFourChartOfLifts_smallBlocks [Finite G] [Fact p.Prime] {Bs L : Subgroup G} {x : G}
    {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin 4)}
    {κ : normOmega E 3 →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs L eta π κ χ) (w : Fin 4 → G)
    (hw : ∀ i, w i ∈ Subgroup.normalizer (Bs : Set G))
    (hact : ∀ i, MulAut.congr eta (ggConjAut Bs (hw i)) =
      SpCoord.permAut (π * uniFourTau i * π⁻¹))
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hL : CFSG.Open.IsComponentOf L (Subgroup.centralizer {x})) (hx : x ∈ Bs)
    (hpq : p ∣ 2 ^ f + 1) (i : Fin 4) (S : Finset (Fin 3))
    (hS : S.Nonempty) (hS2 : S.card ≤ 2) :
    (normBlock E 3 S).map (orthFourChartOfLifts κ w i) =
      uniFourBlocks Bs eta π (S.image i.succAbove) := by
  exact fourCharts_map_normBlock_eq_uniFourBlocks (orthFourChartOfLifts κ w)
    (fun i s t hst => orthFourChartOfLifts_singleton hκ w i (hw i) (hact i) hSC hL hx hpq hst)
    (fun i s t hst => orthFourChartOfLifts_pair hκ w i (hw i) (hact i) hSC hL hx hst)
    i S hS hS2

theorem GGSecFiveBPermOmKFrame.range_le_orthFourChartOfLifts [Finite G] [Fact p.Prime]
    {Bs L X : Subgroup G} {x y : G}
    {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))} {π πX : Equiv.Perm (Fin 4)}
    {κ κX : normOmega E 3 →* G} {χ χX : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs L eta π κ χ)
    (hκX : GGSecFiveBPermOmKFrame E Bs X eta πX κX χX) (w : Fin 4 → G)
    (hw : ∀ i, w i ∈ Subgroup.normalizer (Bs : Set G))
    (hact : ∀ i, MulAut.congr eta (ggConjAut Bs (hw i)) =
      SpCoord.permAut (π * uniFourTau i * π⁻¹))
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hL : CFSG.Open.IsComponentOf L (Subgroup.centralizer {x})) (hx : x ∈ Bs)
    (hX : CFSG.Open.IsComponentOf X (Subgroup.centralizer {y})) (hy : y ∈ Bs)
    (hpq : p ∣ 2 ^ f + 1) :
    κX.range ≤ ⨆ i : Fin 4, (orthFourChartOfLifts κ w i).range := by
  classical
  rw [MonoidHom.range_eq_map, ← iSup_singleton_normBlock_eq_top E (by norm_num : 2 ≤ 3),
    Subgroup.map_iSup]
  refine iSup_le fun s => ?_
  obtain ⟨t, hts⟩ : ∃ t : Fin 3, t ≠ s := ⟨s + 1, by fin_cases s <;> decide⟩
  have hcard : ({s, t} : Finset (Fin 3)).card = 2 := Finset.card_pair hts.symm
  have hpair : (normBlock E 3 {s, t}).map κX =
      ggBlockComm Bs eta ({πX s.castSucc, πX t.castSucc} : Set (Fin 4)) := by
    have h := hκX.blockComm_eq_map_normBlock hSC hy hX (S := {s, t}) (by omega) (by omega)
    rw [← h]
    congr 1
    rw [Finset.coe_pair, Set.image_pair]
  have hb : eta (eta.symm (Pi.mulSingle (πX t.castSucc) (Multiplicative.ofAdd 1))) =
      Pi.mulSingle (πX t.castSucc) (Multiplicative.ofAdd 1) := eta.apply_symm_apply _
  have hsingle := hκX.map_normBlock_singleton (by norm_num) hpq hts.symm _ hb
  rw [hpair] at hsingle
  change (normBlock E 3 {s}).map κX =
    ggSingletonFrom Bs eta (πX s.castSucc) (πX t.castSucc) at hsingle
  rw [hsingle]
  let c : Fin 4 := π.symm (πX s.castSucc)
  let d : Fin 4 := π.symm (πX t.castSucc)
  obtain ⟨i, hic, hid⟩ := uniFour_exists_ne_ne c d
  obtain ⟨u, hu⟩ := Fin.exists_succAbove_eq hic.symm
  obtain ⟨v, hv⟩ := Fin.exists_succAbove_eq hid.symm
  have hπu : π (i.succAbove u) = πX s.castSucc := by rw [hu]; exact π.apply_symm_apply _
  have hπv : π (i.succAbove v) = πX t.castSucc := by rw [hv]; exact π.apply_symm_apply _
  have huv : u ≠ v := by
    intro h
    have hst : s = t := Fin.castSucc_injective 3 (πX.injective (by rw [← hπu, ← hπv, h]))
    exact hts hst.symm
  have h := orthFourChartOfLifts_singleton hκ w i (hw i) (hact i) hSC hL hx hpq huv
  rw [hπu, hπv] at h
  rw [← h]
  rintro z ⟨a, -, rfl⟩
  exact (le_iSup (fun j => (orthFourChartOfLifts κ w j).range) i) ⟨a, rfl⟩

end LiftCharts

section ActualLifts

variable {G : Type} [Group G] [Finite G] {p : ℕ} {Bs L H : Subgroup G}
  {𝒦 : Finset (Subgroup G)} {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))}
  {π : Equiv.Perm (Fin 4)}

theorem exists_orthFourChart_lifts_of_join
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 4 p)
    (hH : H = L ⊔ ⨆ K ∈ 𝒦, K) :
    ∃ (w : Fin 4 → G), w 3 = 1 ∧
      ∃ hw : ∀ i, w i ∈ Subgroup.normalizer (Bs : Set G),
        (∀ i, w i ∈ H) ∧ ∀ i,
          MulAut.congr eta (ggConjAut Bs (hw i)) =
            SpCoord.permAut (π * uniFourTau i * π⁻¹) := by
  classical
  have hLift : ∀ i : Fin 4, ∃ (g : G) (hg : g ∈ Subgroup.normalizer (Bs : Set G)),
      g ∈ H ∧ MulAut.congr eta (ggConjAut Bs hg) =
        SpCoord.permAut (π * uniFourTau i * π⁻¹) := by
    intro i
    obtain ⟨g, hg, hgg, hact⟩ :=
      exists_normalizer_conjAut_eq_permAut_of_join hEta (π * uniFourTau i * π⁻¹)
    exact ⟨g, hg, hH.symm ▸ hgg, hact⟩
  choose w0 hw0 hH0 hact0 using hLift
  let w : Fin 4 → G := fun i => if i = 3 then 1 else w0 i
  have hw3 : w 3 = 1 := by simp [w]
  have hw : ∀ i, w i ∈ Subgroup.normalizer (Bs : Set G) := by
    intro i
    dsimp only [w]
    split_ifs with hi
    · exact Subgroup.one_mem _
    · exact hw0 i
  refine ⟨w, hw3, hw, ?_, ?_⟩
  · intro i
    dsimp only [w]
    split_ifs with hi
    · exact H.one_mem
    · exact hH0 i
  · intro i
    by_cases hi : i = 3
    · subst i
      have hOne : ggConjAut Bs (hw 3) = 1 := by
        ext b
        simp [ggConjAut_apply, hw3]
      rw [hOne, map_one]
      simp [uniFourTau]
    · simpa only [w, if_neg hi] using hact0 i

end ActualLifts

section FourChartPackage

variable {G F K : Type} [Group G] [Finite G] [Field F] [Field K] [Algebra F K]
  [Finite K] [CharP K 2] {f p : ℕ} [Fact p.Prime]
  {E : QuadExt F K (unitaryInvolution K 2 f)}
  {Bs L X H : Subgroup G} {x y : G} {𝒦 : Finset (Subgroup G)}
  {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))} {π πX : Equiv.Perm (Fin 4)}
  {κ κX : normOmega E 3 →* G} {χ χX : Multiplicative (ZMod p) →* Kˣ}

theorem exists_orthFourChart_data_of_original_frames
    (hκ : GGSecFiveBPermOmKFrame E Bs L eta π κ χ)
    (hκX : GGSecFiveBPermOmKFrame E Bs X eta πX κX χX)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hL : CFSG.Open.IsComponentOf L (Subgroup.centralizer {x})) (hx : x ∈ Bs)
    (hX : CFSG.Open.IsComponentOf X (Subgroup.centralizer {y})) (hy : y ∈ Bs)
    (hpq : p ∣ 2 ^ f + 1)
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 4 p)
    (hH : H = L ⊔ ⨆ K ∈ 𝒦, K) (hHX : H = L ⊔ X) :
    ∃ a : Fin 4 → (normOmega E 3 →* G), a 3 = κ ∧
      (∀ i, Function.Injective (a i)) ∧
      (∀ (i : Fin 4) (S : Finset (Fin 3)), S.Nonempty → S.card ≤ 2 →
        (normBlock E 3 S).map (a i) = uniFourBlocks Bs eta π (S.image i.succAbove)) ∧
      (⨆ i, (a i).range) = H := by
  classical
  obtain ⟨w, hw3, hw, hwH, hwact⟩ := exists_orthFourChart_lifts_of_join (π := π) hEta hH
  let a : Fin 4 → (normOmega E 3 →* G) := orthFourChartOfLifts κ w
  have ha3 : a 3 = κ := orthFourChartOfLifts_three κ w hw3
  have hinj : ∀ i, Function.Injective (a i) := by
    intro i
    exact (MulAut.conj (w i)).injective.comp hκ.1
  have hHupper : (⨆ i, (a i).range) ≤ H := by
    refine iSup_le fun i => ?_
    change (orthFourChartOfLifts κ w i).range ≤ H
    rw [orthFourChartOfLifts_range κ w hκ.2.1]
    rintro z ⟨l, hl, rfl⟩
    have hLle : L ≤ H := by rw [hHX]; exact le_sup_left
    change w i * l * (w i)⁻¹ ∈ H
    exact H.mul_mem (H.mul_mem (hwH i) (hLle hl)) (H.inv_mem (hwH i))
  have hHlower : H ≤ ⨆ i, (a i).range := by
    rw [hHX]
    refine sup_le ?_ ?_
    · rw [← hκ.2.1, ← ha3]
      exact le_iSup (fun i => (a i).range) 3
    · rw [← hκX.2.1]
      exact GGSecFiveBPermOmKFrame.range_le_orthFourChartOfLifts hκ hκX w hw hwact hSC hL hx hX hy hpq
  exact ⟨a, ha3, hinj, orthFourChartOfLifts_smallBlocks hκ w hw hwact hSC hL hx hpq,
    le_antisymm hHupper hHlower⟩

end FourChartPackage

theorem GGSecFiveRouteCfg.exists_four_chart_data_of_twDNonsplit
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) (hBJ : BMaxJoinInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (e : (CoxeterMatrix.B 4).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B 4) e)
    (eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))) (i0 : Fin 4)
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 4 p)
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 p i0)
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel 4 p lab ∧
      lab.n ≠ 1 ∧ lab.tag = .twD ∧ p ∣ 2 ^ lab.n + 1) p Bs L)
    (hB : B = Bs)
    (hRM : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hG0 : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    (hNoDense : ¬ ∃ K : Subgroup G, GGSecFiveBCoordBDenseNbr p Bs 𝒦 4 eta K) :
    ∃ (f : ℕ) (K : Type) (_ : Field K) (_ : Algebra (GaloisField 2 f) K) (_ : Finite K)
      (_ : CharP K 2) (E : QuadExt (GaloisField 2 f) K (unitaryInvolution K 2 f)),
      2 ≤ f ∧ p ∣ 2 ^ f + 1 ∧ UnitaryFieldData 2 f K ∧
      ∃ (π : Equiv.Perm (Fin 4)) (κ : normOmega E 3 →* G)
        (χ : Multiplicative (ZMod p) →* Kˣ), π (Fin.last 3) = i0 ∧
        GGSecFiveBPermOmKFrame E Bs L eta π κ χ ∧
        ∃ a : Fin 4 → (normOmega E 3 →* G), a 3 = κ ∧
          (∀ i, Function.Injective (a i)) ∧
          (∀ (i : Fin 4) (S : Finset (Fin 3)), S.Nonempty → S.card ≤ 2 →
            (normBlock E 3 S).map (a i) = uniFourBlocks Bs eta π (S.image i.succAbove)) ∧
          (⨆ i, (a i).range) = ggG0 p B x L D J := by
  classical
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  let : Fact p.Prime := ⟨hp⟩
  have hcfg : GGConfig p B Bs x L D J := hR.1.1
  obtain ⟨N, hNmem, hNL⟩ := exists_mem_not_le_ggAutomizer_of_bSignedFull hp hp2 eta hEta hLB
  obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 N hNmem
  have hy : y ∈ Bs := hB ▸ hnb.1.2.1
  rcases hR.nbr_axis_or_dense hX hTCJ hRig hTPn hA8 hraw hiso hFC hB (by norm_num) eta hEta hLB
    hnb (hRM y N hnb) hNL hy with ⟨j, hj, hblk, haxis⟩ | ⟨⟨δ, hδ, hNδ⟩, -⟩
  swap
  · exact (hNoDense ⟨N, hNmem, δ, hδ, hNδ⟩).elim
  obtain ⟨v, hv, hvact, hNeq, hAN⟩ :=
    hR.exists_eq_map_conj_swap_of_sparse hB (by norm_num) eta i0 hEta hLB hy hnb hj haxis hblk
  have hGN : ggG0 p B x L D J = L ⊔ N :=
    ggG0_eq_sup_of_bCoordinateBlocks hBJ hR e hP (by norm_num) hEta hLB hRM hNmem hj hAN
  obtain ⟨-, -, -, f, K, fieldK, algebraK, finiteK, charK, E, hf, hpq, hUF, π, hπ, κ, χ, hκ⟩ :=
    hcfg.exists_omKFrame_of_twDNonsplit hB (by norm_num) eta hLB hLab
  let : Field K := fieldK
  let : Algebra (GaloisField 2 f) K := algebraK
  let : Finite K := finiteK
  let : CharP K 2 := charK
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hx : x ∈ Bs := hcfg.tableB_facts.2.2.1
  have hLc : CFSG.Open.IsComponentOf L (Subgroup.centralizer {x}) :=
    isComponentOf_iff_open.mp hcfg.1.2.2.2.2.2.2.1.2.2.2.1
  have hNv : CFSG.Open.IsComponentOf (L.map (MulAut.conj v).toMonoidHom)
      (Subgroup.centralizer {v * x * v⁻¹}) :=
    isComponentOf_iff_open.mp
      (isComponentOf_centralizer_map_conj (isComponentOf_iff_open.mpr hLc) v)
  have hxv : v * x * v⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hv x).mp hx
  have hκv := hκ.conj_transporter hv hvact
  have hGNv : ggG0 p B x L D J = L ⊔ L.map (MulAut.conj v).toMonoidHom := by
    rw [hGN, hNeq]
  obtain ⟨a, ha3, hainj, hsmall, harange⟩ :=
    exists_orthFourChart_data_of_original_frames hκ hκv hSC hLc hx hNv hxv hpq hEta hG0 hGNv
  exact ⟨f, K, fieldK, algebraK, finiteK, charK, E, hf, hpq, hUF, π, κ, χ, hπ, hκ,
    a, ha3, hainj, hsmall, harange⟩

end CFSG.StandardType

end
