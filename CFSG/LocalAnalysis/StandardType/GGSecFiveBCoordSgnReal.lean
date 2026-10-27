module

public import CFSG.LocalAnalysis.StandardType.GGRealSgnRealize
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGRealKGThree
import CFSG.LocalAnalysis.StandardType.GGSignedCoordRefl
import CFSG.LocalAnalysis.StandardType.GGSignedPermCount
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commute_conj_of_congr_eq_sgnAut {Bs : Subgroup G} {n p : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {W : Subgroup (MulAut ↥Bs)}
    (hW : W.map (MulAut.congr eta).toMonoidHom ≤ bSignedFull n p) {r : MulAut ↥Bs} {i : Fin n}
    (hri : MulAut.congr eta r = SpCoord.sgnAut i) {w : MulAut ↥Bs} (hw : w ∈ W) :
    Commute (w * r * w⁻¹) r := by
  have hu : MulAut.congr eta w ∈ bSignedFull n p :=
    hW (Subgroup.mem_map_of_mem (MulAut.congr eta).toMonoidHom hw)
  have hsp : SpCoord.IsSignedPerm ⇑(MulAut.congr eta w) := by
    rw [bSignedFull_eq_signedPermSubgroup] at hu
    exact hu
  obtain ⟨π, ε, hε, hu'⟩ := hsp
  have hconj : MulAut.congr eta (w * r * w⁻¹) = SpCoord.sgnAut (π i) := by
    have h := SpCoord.IsSignedPerm.mul_sgnAut (u := MulAut.congr eta w) hu' i
    have h1 : MulAut.congr eta (w * r * w⁻¹) =
        (MulAut.congr eta w * SpCoord.sgnAut i) * (MulAut.congr eta w)⁻¹ := by
      simp only [map_mul, map_inv, hri]
    rw [h1, h]
    group
  refine Commute.of_map (MulAut.congr eta).injective ?_
  rw [hconj, hri]
  exact SpCoord.sgnAut_mul_comm (π i) i

theorem ggRealized_of_nbr_realSgnOn {S : ℕ → LargeEvenLabel → Prop} (hS : GGRealSgnOn S)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hNT : GGNoTransvection p Bs) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (hM : GGInnerDiagOnLabel S p Bs K) {r : MulAut ↥Bs} (hr : r ∈ ggAutomizer K Bs)
    (hrefl : GGIsReflection p r) (hcomm : ∀ w ∈ ggAutomizer K Bs, Commute (w * r * w⁻¹) r) :
    GGRealized p Bs r := by
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hXc, lab, hlab, hraw'⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => S p lab)
    (fun lab hlab hs => hS p lab hp hlab hs)
    (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, hR, I, F, hRs, hRna, θ, ⟨⟨-, hBsN, h3I⟩, hT⟩⟩ :=
    largeEvenRawDatum_exists hraw'
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces K θ hBsN h3I hb
  have h3 := pow_three_le_card_range_ggGamma_bstar hcfg hnb hBsN
  have hr0 : p ^ 0 ≤ Nat.card (ggGamma K hBsN).range := by
    rw [pow_zero]
    exact Nat.succ_le_of_lt (Nat.card_pos : 0 < Nat.card (ggGamma K hBsN).range)
  have hJ := ggReflRealizedAt_of_torusSgnComponents hp hp2 hBs hSC hNT hXc θ hBsN hBsI
    hr0 h3 hT hr hrefl hcomm
  have hyBs : y ∈ Bs := hcfg.2.1.1 hnb.1.2.1
  have hKcomp : GLAPComponent p (centralizer ({y} : Set G)) K :=
    (CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent p _ K).mp hnb.1.2.2.2.2.1
  exact ggRealized_of_reflRealizedAt hp hyBs hKcomp hr hJ

theorem GGSecFiveRouteCfg.realized_of_sgnAut_of_realSgnOn {S : ℕ → LargeEvenLabel → Prop}
    (hS : GGRealSgnOn S) {p n : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    {y : G} {K : Subgroup G} (hK𝒦 : K ∈ 𝒦) (hnb : GGNbr p B x D J y K)
    (hM : GGInnerDiagOnLabel S p Bs K) {r : MulAut ↥Bs} (hr : r ∈ ggAutomizer K Bs)
    (hrefl : GGIsReflection p r) {i : Fin n} (hri : MulAut.congr eta r = SpCoord.sgnAut i) :
    GGRealized p Bs r := by
  have hcfg : GGConfig p B Bs x L D J := hR.1.1
  have hNT : GGNoTransvection p Bs := hR.1.2.2.2.1
  have hAK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom ≤ bSignedFull n p := by
    rw [← hK]
    exact Subgroup.map_mono (f := (MulAut.congr eta).toMonoidHom) fun w hw =>
      Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem K (Subgroup.mem_iSup_of_mem hK𝒦 hw))
  have hcomm : ∀ w ∈ ggAutomizer K Bs, Commute (w * r * w⁻¹) r := fun w hw =>
    commute_conj_of_congr_eq_sgnAut eta hAK hri hw
  exact ggRealized_of_nbr_realSgnOn hS hcfg hNT hnb hM hr hrefl hcomm

end CFSG.StandardType

end
