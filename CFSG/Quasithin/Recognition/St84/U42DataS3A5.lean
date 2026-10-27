module

public import CFSG.Quasithin.Recognition.St84.TransferS3A5U42
public import CFSG.Quasithin.Recognition.St84.U42Ident
public import CFSG.Quasithin.Recognition.St84.U42ExtIdent
public import CFSG.GH74.QTGen4.DSGen4.Leaf.Short2OfA5
public import CFSG.GH74.QTGen4.DSGen4.Leaf.M3
public import CFSG.GH74.QTGen4.DSGen4.Leaf.Alt5OfOrth
public import CFSG.GH74.QTGen4.DSGen4.Leaf.Omega4MinusOfOrth
public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSBJZ2
public import CFSG.Quasithin.EmptyFaithful.Gold14610CmpMain

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

private theorem dsZi_eq_pCoreOf_of_s3a5VertexId {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2)
    (hB : S3A5VertexId L1 L2 S) (hU : S3A5U42Hyp L1 L2 S) :
    dsZi L2 S = pCoreOf 2 L2 := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hZS : centerOf S ≤ pCoreOf 2 L2 := by
    intro z hz
    have hzP : z ∈ L2 ⊔ bigB L2 L1 S :=
      ((le_sup_right : S ≤ bigB L2 L1 S).trans le_sup_right) hz.1
    have hzC : z ∈ Subgroup.centralizer (pCoreOf 2 (L2 ⊔ bigB L2 L1 S) : Set H) :=
      Subgroup.centralizer_le (leafSylowS hR.symm).2.2 hz.2
    rw [hB.oTwo_right]
    exact F1.parabolic_charTwo hR.symm ⟨hzP, hzC⟩
  have hle : dsZi L2 S ≤ pCoreOf 2 L2 :=
    DSBJZ2.dsConjClosure_le' fun y hy z hz =>
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L2 hy) z).mp
        (hZS (DSBJZ2.omega_centerOf_le S hz))
  have hN : f112saP2' L1 L2 S ≤ Subgroup.normalizer (dsZi L2 S : Set H) := by
    refine hB.L2_eq.ge.trans (DSBJZ2.le_normalizer_of_conj fun g hg x hx => ?_)
    have hcl : dsZi L2 S ≤ (dsZi L2 S).comap (MulAut.conj g).toMonoidHom :=
      DSBJZ2.dsConjClosure_le' fun y hy z hz => by
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          show g * (y * z * y⁻¹) * g⁻¹ = (g * y) * z * (g * y)⁻¹ by group]
        exact DSBJZ2.conj_mem_dsConjClosure (L2.mul_mem hg hy) hz
    simpa [mul_assoc] using hcl hx
  have hQne : pCoreOf 2 (f112saP2' L1 L2 S) ≠ ⊥ := by
    intro h
    have hc := hU.card_right
    rw [h, Subgroup.card_bot] at hc
    norm_num at hc
  have hSne : S ≠ ⊥ := fun hS => hQne (eq_bot_iff.mpr fun q hq => by
    have hqS := (f112sa_QA_le_T hF hq).1
    rwa [hS] at hqS)
  obtain ⟨x, hxZ, hx2, hx1⟩ :=
    CFSG.QuasithinUnique.Setup.exists_involution_centerOf hF.1.h1.pgroup hSne
  have hne : dsZi L2 S ≠ ⊥ := fun h => hx1 (by
    have hx : x ∈ dsZi L2 S := dsZ_le_dsZi L2 S (DSBJZ2.mem_omega_of hxZ hx2)
    rw [h] at hx
    exact Subgroup.mem_bot.mp hx)
  rcases f112sa_irred_of_u42Hyp hF h1 h2 hU (hle.trans hB.QA_eq.le) hN with h | h
  · exact absurd h hne
  · exact h.trans hB.QA_eq.symm

private theorem not_dsQ_le_dsQ_of_s3a5VertexId {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hB : S3A5VertexId L1 L2 S) :
    ¬ dsQ L2 L1 S ≤ dsQ L1 L2 S := by
  intro hle
  have heq : pCoreOf 2 (f112saP1' L1 L2 S) = S ⊓ f112saK L1 L2 S := by
    rw [← hB.QS_eq, hB.oTwo_left, ← hB.T_eq, ← hB.sup_eq, sup_eq_right.mpr hle]
  have hc := f112sa_card_T_eq_QS hF h1 h2
  rw [← heq] at hc
  have hpos : 0 < Nat.card ↥(pCoreOf 2 (f112saP1' L1 L2 S)) := Nat.card_pos
  omega

theorem f112B6Loc_of_s3a5VertexId
    {L1 L2 S : Subgroup H} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2)
    (hB : S3A5VertexId L1 L2 S) (hU : S3A5U42Hyp L1 L2 S)
    (hnat : ¬ NatSec (oTwoPrime (f112saP2' L1 L2 S)) ⊥ (pCoreOf 2 (f112saP2' L1 L2 S))) :
    F112B6Loc L1 L2 := by
  have hct : CharTwo L2 := hB.charTwo_right
  have hE : IsElemAbelian 2 (pCoreOf 2 L2) := hB.QA_eq ▸ hU.elem_right
  have hO16 : Nat.card ↥(pCoreOf 2 L2) = 16 := by
    rw [hB.QA_eq, hU.card_right]
    norm_num
  have hNat : ¬ NatSec L2 ⊥ (pCoreOf 2 L2) := by
    rw [f112sa_oTwoPrime_P2'_eq hF h1 h2, ← hB.L2_eq] at hnat
    exact hnat
  haveI : DSLeaf LeafFaithfulA5 := ⟨leafFaithfulA5⟩
  haveI : DSLeaf LeafShort2OfA5 := ⟨leafShort2OfA5⟩
  haveI : DSLeaf LeafM3 := ⟨leafM3⟩
  haveI : DSLeaf LeafAlt5OfOrth := ⟨leafAlt5OfOrth⟩
  refine ⟨isL2Quot_one_iff_perm3.mpr h1, ?_,
    Gold14610.isBlock2_of_short (leafShort2OfA5 h2 hct hE hO16) le_rfl Subgroup.le_normalizer,
    h2, leafOmega4MinusOfOrth h2 hct hE hO16 hNat, leafAlt5OfOrth h2 hct hE hO16 hNat⟩
  rw [hB.QS_eq]
  exact hU.special_left

theorem u42Data_of_s3a5ParabolicId
    {L1 L2 S : Subgroup H} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2)
    (hT : S3A5ParabolicId L1 L2 S) (hU : S3A5U42Hyp L1 L2 S)
    (hnat : ¬ NatSec (oTwoPrime (f112saP2' L1 L2 S)) ⊥ (pCoreOf 2 (f112saP2' L1 L2 S))) :
    U42PlainData L1 L2 S ∨ U42ExtData L1 L2 S := by
  have hb6 := f112B6Loc_of_s3a5VertexId hF h1 h2 hT.toS3A5VertexId hU hnat
  have hZ := dsZi_eq_pCoreOf_of_s3a5VertexId hF h1 h2 hT.toS3A5VertexId hU
  have hdsQ : dsQ L2 L1 S = dsZi L2 S := hT.oTwo_right.symm.trans hZ.symm
  have hcR : Nat.card ↥(pCoreOf 2 L2) = 2 ^ 4 := by rw [hT.QA_eq]; exact hU.card_right
  have hcL : Nat.card ↥(pCoreOf 2 L1) = 2 ^ 5 := by
    rw [hT.QS_eq, hU.special_left.2.1]
  have hnle : ¬ dsZi L2 S ≤ dsQ L1 L2 S := by
    rw [← hdsQ]
    exact not_dsQ_le_dsQ_of_s3a5VertexId hF h1 h2 hT.toS3A5VertexId
  by_cases hS : S ≤ L2
  · exact Or.inl ⟨hb6, hS, hT.oTwo_right, hdsQ, hcR, hT.oTwo_left, hcL,
      hT.sup_eq.trans (inf_eq_left.mpr hS), hnle⟩
  · exact Or.inr ⟨hb6, hS, hT.oTwo_right, hdsQ, hcR, hT.oTwo_left, hcL, hT.sup_eq, hnle,
      (hT.ext hS).2.1, (hT.ext hS).2.2⟩

end CFSG.Quasithin.F112R.St84
