module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestOriginalWeyl
import CFSG.LocalAnalysis.StandardType.GGFieldNbr
import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
import CFSG.LocalAnalysis.StandardType.GGRowKFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrCompare
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPosition

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G]

theorem GGConfig.five_le_of_ne [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hc : GGConfig p B Bs x L D J) (hB : B ≠ Bs) {n : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) : 5 ≤ n := by
  obtain ⟨hp, -, -, -, -⟩ := hc.tableB_facts
  have hcardB : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hc.1.2.2.2.2.2.2.1.1.2.1
  have h4 : 4 ≤ LargeEvenTwoLocalRank p G := hc.1.2.2.2.2.2.1.2.2.2
  have hBBs : B ≤ Bs := hc.2.1.1
  have hcardlt : Nat.card B < Nat.card Bs := Subgroup.card_lt_of_lt (lt_of_le_of_ne hBBs hB)
  have hBsCard : Nat.card Bs = p ^ n := by
    rw [Nat.card_congr eta.toEquiv, Nat.card_fun, Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod, Nat.card_fin]
  rw [hcardB, hBsCard] at hcardlt
  have hlt : LargeEvenTwoLocalRank p G < n := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hcardlt
  omega

private theorem signedNbrDatum_card_fix_le [Finite G] {p n : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {y : G} {K : Subgroup G}
    (hn : GGNbr p B x D J y K) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) :
    Nat.card {f : Fin n → Multiplicative (ZMod p) //
      ∀ u ∈ (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom, u f = f} ≤ p ^ 2 := by
  have hres : GGResHyp p B Bs x L D J y K :=
    ⟨hR.1.1, hR.1.2.1, hR.1.2.2.1, hR.1.2.2.2.1, hn, hR.2.1 y K hn, Or.inr hR.2.1⟩
  have hfixle : Nat.card {f : Fin n → Multiplicative (ZMod p) //
      ∀ u ∈ (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom, u f = f} ≤
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := by
    refine Nat.card_le_card_of_injective
      (fun f => (⟨(eta.symm f.1 : ↥Bs), ?_⟩ : ↥(Bs ⊓ Subgroup.centralizer (K : Set G))))
      ?_
    · refine Subgroup.mem_inf.mpr ⟨(eta.symm f.1).2, ?_⟩
      exact hFC G p B Bs x L D J y K hres (eta.symm f.1)
        ((forall_map_congr_fix_iff eta (ggAutomizer K Bs) (eta.symm f.1)).mp
          (by simpa using f.2))
    · intro f g hfg
      have hval : ((eta.symm f.1 : ↥Bs) : G) = ((eta.symm g.1 : ↥Bs) : G) :=
        congrArg (fun x : ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) => (x : G)) hfg
      have hval' : (eta.symm f.1 : ↥Bs) = eta.symm g.1 := Subtype.ext hval
      exact Subtype.ext (by simpa only [MulEquiv.apply_symm_apply] using congrArg eta hval')
  exact hfixle.trans (card_bstar_inf_centralizer_le hR.1.1 hn)

private theorem signedNbrDatum_not_fix [Finite G] {p n : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {y : G} {K : Subgroup G}
    (hn : GGNbr p B x D J y K) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (xb : ↥Bs) (hxb : (xb : G) = x) :
    ¬ ∀ u ∈ (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom, u (eta xb) = eta xb := by
  have hres : GGResHyp p B Bs x L D J y K :=
    ⟨hR.1.1, hR.1.2.1, hR.1.2.2.1, hR.1.2.2.2.1, hn, hR.2.1 y K hn, Or.inr hR.2.1⟩
  intro hfix
  have hxfix : (xb : G) ∈ Subgroup.centralizer (K : Set G) :=
    hFC G p B Bs x L D J y K hres xb
      ((forall_map_congr_fix_iff eta (ggAutomizer K Bs) xb).mp (by simpa using hfix))
  have hxB : (xb : G) ∈ B := by
    rw [hxb]
    exact hR.1.1.1.2.2.2.2.2.2.1.2.1
  have hzp : B ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y :=
    inf_centralizer_eq_zpowers_of_sHat hn.1
  have hxzp : (xb : G) ∈ Subgroup.zpowers y := by
    have hmem : (xb : G) ∈ B ⊓ Subgroup.centralizer (K : Set G) := ⟨hxB, hxfix⟩
    rwa [hzp] at hmem
  have hxzp' : x ∈ Subgroup.zpowers y := by
    rw [← hxb]
    exact hxzp
  have hDle : D ≤ Subgroup.zpowers y := by
    rw [hn.2.1, Subgroup.closure_le]
    intro z hz
    rcases hz with hzx | hzy
    · rw [hzx]
      exact hxzp'
    · rw [hzy]
      exact Subgroup.mem_zpowers y
  have hyD : y ∈ D := by
    rw [hn.2.1]
    exact Subgroup.subset_closure (by simp)
  have hp : p.Prime := hR.1.1.tableB_facts.1
  have := Fact.mk hp
  have hzpcard : Nat.card (Subgroup.zpowers y) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hn.1.1.1.2 y hn.1.2.1) hn.1.2.2.1
  have hcard : p ^ 2 = p := by
    rw [← hR.1.1.2.2.1.2.2.1, ← hzpcard]
    exact le_antisymm (Subgroup.card_le_of_le hDle)
      (Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr hyD))
  have hp2 : 2 ≤ p := hp.two_le
  have hpp : p * p = p := by simpa [pow_two] using hcard
  nlinarith

theorem GGSecFiveRouteCfg.signedNbrDatum [Finite G] {p n : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hX : GGResXDichotomyInput)
    (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) (hTPn : GGNbrTablePNbrInputNarrow)
    (hA8 : GGForkA8NotReflInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    {y : G} {K : Subgroup G} (hn : GGNbr p B x D J y K)
    (hK : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) {xb yb : ↥Bs} (hxb : (xb : G) = x)
    (hyb : (yb : G) = y) :
    SignedNbrDatum n p (eta xb) (eta yb)
      ((ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom) := by
  obtain ⟨hp, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ LargeEvenBeta 4 G)
  refine ⟨?_, signedNbrDatum_card_fix_le hFC hR hn eta, ?_,
    signedNbrDatum_not_fix hFC hR hn eta xb hxb⟩
  · have hA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom ≤ bSignedFull n p := by
      rw [← hEta]
      exact Subgroup.map_mono hK
    exact exists_isSignedBlockOn_of_weyl hp hp2 eta hA
      (GGSecFiveRestHyp.weylReflectionGroup_nbr hX hTCJ hRig hTPn hA8 hraw hiso hR.1 hR.2.1 hn)
  · intro u hu
    obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hu
    change MulAut.congr eta ψ (eta yb) = eta yb
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    have hy : y ∈ Bs := hR.1.1.2.1.1 (hn.1.2.1)
    have hyb' : yb = ⟨y, hy⟩ := Subtype.ext hyb
    rw [hyb', ggRC_automizer_fixes_y (K := K) hy hn.1.2.2.2.1 ψ hψ]

theorem GGSecFiveRouteCfg.mem_zpowers_of_fix_of_mem [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {y : G} {K : Subgroup G}
    (hn : GGNbr p B x D J y K) (b : ↥Bs) (hbB : (b : G) ∈ B)
    (hb : ∀ φ ∈ ggAutomizer K Bs, φ b = b) : (b : G) ∈ Subgroup.zpowers y := by
  have hres : GGResHyp p B Bs x L D J y K :=
    ⟨hR.1.1, hR.1.2.1, hR.1.2.2.1, hR.1.2.2.2.1, hn, hR.2.1 y K hn, Or.inr hR.2.1⟩
  have hmem : (b : G) ∈ B ⊓ Subgroup.centralizer (K : Set G) :=
    ⟨hbB, hFC G p B Bs x L D J y K hres b hb⟩
  rwa [inf_centralizer_eq_zpowers_of_sHat hn.1] at hmem

theorem GGSecFiveRouteCfg.bProperFrame_of_nb [Finite G] {p n : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hTBF : GGTBFixInput)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B ≠ Bs)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (Nb : G → Subgroup G → Prop) (hNb : ∀ y K, Nb y K → GGNbr p B x D J y K)
    (hK : ∀ y K, Nb y K → ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hex : ∀ K ∈ 𝒦, ∃ y, Nb y K) :
    GGBProperFrame p n B Bs L x 𝒦 Nb eta := by
  obtain ⟨hp, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ LargeEvenBeta 4 G)
  obtain ⟨-, hElem, -, -, -⟩ := hR.1.1.tableB_facts
  have hst : LargeEvenStandardType p B x L := hR.1.1.1.2.2.2.2.2.2.2
  have hDJ : LargeEvenStdSub p B x L D J := hR.1.1.2.2
  exact
    { prime := hp
      ne_two := hp2
      five_le := hR.1.1.five_le_of_ne hB eta
      le := hR.1.1.2.1.1
      pow_eq_one := fun b hb => hElem.2 b hb
      fixLineComp := hR.1.fixLineComp_L hTBF hR.2.1
      join := hEta
      exists_nb := hex
      mem := fun y K hn => (hNb y K hn).1.2.1
      isComponentOf := fun y K hn =>
        (isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hDJ (hNb y K hn))).1
      datum := fun y K hn _ _ hxb hyb =>
        hR.signedNbrDatum hX hTCJ hRig hTPn hA8 hraw hiso hFC eta hEta (hNb y K hn) (hK y K hn)
          hxb hyb
      mem_zpowers := fun y K hn b hbB hb => hR.mem_zpowers_of_fix_of_mem hFC (hNb y K hn) b hbB hb
      plane := fun y K y₀ K₀ hn hn₀ => (hNb y K hn).mem_closure_pair (hNb y₀ K₀ hn₀)
      not_mem := fun y K hn => GGConfig.not_mem_zpowers_of_ggNbr hR.1.1 (hNb y K hn) }

theorem GGSecFiveRouteCfg.bProperFrame [Finite G] {p n : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hTBF : GGTBFixInput)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B ≠ Bs)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hK : ∀ y K, GGNbr p B x D J y K → ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) :
    GGBProperFrame p n B Bs L x 𝒦 (fun y K => GGNbr p B x D J y K) eta :=
  hR.bProperFrame_of_nb hTBF hX hTCJ hRig hTPn hA8 hraw hiso hFC hB eta hEta _
    (fun _ _ hn => hn) hK (fun K hK' => hR.2.2.2.1.2 K hK')

theorem GGSecFiveRouteCfg.bProperFrame_selected [Finite G] {p n : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hTBF : GGTBFixInput)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B ≠ Bs)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p) :
    GGBProperFrame p n B Bs L x 𝒦 (fun y K => K ∈ 𝒦 ∧ GGNbr p B x D J y K) eta :=
  hR.bProperFrame_of_nb hTBF hX hTCJ hRig hTPn hA8 hraw hiso hFC hB eta hEta _
    (fun _ _ hn => hn.2)
    (fun _ K hn =>
      le_sup_of_le_right (le_iSup₂ (f := fun K (_ : K ∈ 𝒦) => ggAutomizer K Bs) K hn.1))
    (fun K hK' => (hR.2.2.2.1.2 K hK').imp fun _ hy => ⟨hK', hy⟩)

end CFSG.StandardType

end
