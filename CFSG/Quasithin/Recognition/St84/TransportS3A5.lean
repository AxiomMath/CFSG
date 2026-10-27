module

public import CFSG.Quasithin.Recognition.St84.TreeBase
public import CFSG.Quasithin.Recognition.St84.Gen.TreeSLE
public import CFSG.Quasithin.Recognition.St84.Sec5Hyp
public import CFSG.Quasithin.Recognition.St84.TransferS3A5Setup
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeBZero
public import CFSG.Quasithin.Recognition.GoldschmidtF112RJ2
public import CFSG.Quasithin.Recognition.St84.TransferInner

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ CFSG.GH74.QTGen4.DSGen4
open CFSG.SignalizerFunctorTheorem.CatalogBridge (isoOfMapEq)
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

private theorem pCoreOf_P1'_le_P1 {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) : pCoreOf 2 (f112saP1' L1 L2 S) ≤ f112P1 L1 L2 S :=
  (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (f112sa_P1'_le_P1 hF.toW)

private theorem pCoreOf_P2'_le_P2 {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) : pCoreOf 2 (f112saP2' L1 L2 S) ≤ f112P2 L1 L2 S :=
  (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (f112sa_P2'_le_P2 hF.toW)

private theorem oTwoPrime_P1'_le_P1 {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) : oTwoPrime (f112saP1' L1 L2 S) ≤ f112P1 L1 L2 S :=
  (oTwoPrime_le _).trans (f112sa_P1'_le_P1 hF.toW)

private theorem oTwoPrime_P2'_le_P2 {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) : oTwoPrime (f112saP2' L1 L2 S) ≤ f112P2 L1 L2 S :=
  (oTwoPrime_le _).trans (f112sa_P2'_le_P2 hF.toW)

private theorem s3a5_dictionary {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S)
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S)) :
    (X.Gi 0).map (f112EOdd L1 L2 S).subtype = f112OfA L1 L2 S (f112saP1' L1 L2 S) ∧
    (X.Q 0).map (f112EOdd L1 L2 S).subtype =
      f112OfA L1 L2 S (pCoreOf 2 (f112saP1' L1 L2 S)) ∧
    (X.Q 1).map (f112EOdd L1 L2 S).subtype =
      f112OfB L1 L2 S (pCoreOf 2 (f112saP2' L1 L2 S)) ∧
    (X.L 0).map (f112EOdd L1 L2 S).subtype =
      f112OfA L1 L2 S (oTwoPrime (f112saP1' L1 L2 S)) ∧
    (X.L 1).map (f112EOdd L1 L2 S).subtype =
      f112OfB L1 L2 S (oTwoPrime (f112saP2' L1 L2 S)) ∧
    X.S.map (f112EOdd L1 L2 S).subtype = f112OfA L1 L2 S (pCoreOf 2 (f112saK L1 L2 S)) ∧
    IsSylowTwoOf (pCoreOf 2 (f112saK L1 L2 S)) (f112saK L1 L2 S) := by
  let D : BaseEdgeData H :=
    { L1 := L1, L2 := L2, S := S, E := f112EOdd L1 L2 S
      Pα := f112saP1' L1 L2 S, Pβ := f112saP2' L1 L2 S, Ke := f112saK L1 L2 S
      le_Pα := f112sa_P1'_le_P1 hF.toW
      le_Pβ := f112sa_P2'_le_P2 hF.toW
      le_Ke := by rw [f112_inf_eq_bigB hF.toW]; exact f112sa_K_le_bigB L1 L2 S
      ofA_eq := f112sl_EOdd_inf_ofA_range hF
      ofB_eq := f112sl_EOdd_inf_ofB_range hF
      ofA_inf_ofB_eq := f112sl_EOdd_inf_ofA_range_inf_ofB_range hF
      X := X, X_zero := hX0, X_one := hX1 }
  exact ⟨D.gi_zero_map, D.Q_zero_map, D.Q_one_map, D.L_zero_map, D.L_one_map, D.S_map,
    D.isSylowTwoOf_pCoreOf⟩

private theorem map_bot_eq_ofA_bot (L1 L2 S : Subgroup H) :
    (⊥ : Subgroup ↥(f112EOdd L1 L2 S)).map (f112EOdd L1 L2 S).subtype = f112OfA L1 L2 S ⊥ := by
  rw [Subgroup.map_bot, f112OfA, Subgroup.bot_subgroupOf, Subgroup.map_bot]

private theorem map_bot_eq_ofB_bot (L1 L2 S : Subgroup H) :
    (⊥ : Subgroup ↥(f112EOdd L1 L2 S)).map (f112EOdd L1 L2 S).subtype = f112OfB L1 L2 S ⊥ := by
  rw [Subgroup.map_bot, f112OfB, Subgroup.bot_subgroupOf, Subgroup.map_bot]

private theorem natSec_left_of_treeU42Data {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S)
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : X.TreeU42Data) :
    NatSec (oTwoPrime (f112saP1' L1 L2 S)) (centerOf (pCoreOf 2 (f112saP1' L1 L2 S)))
      (pCoreOf 2 (f112saP1' L1 L2 S)) := by
  obtain ⟨-, hQ0, -, hL0, -, -, -⟩ := s3a5_dictionary hF hX0 hX1
  have hQα := pCoreOf_P1'_le_P1 hF
  have hLα := oTwoPrime_P1'_le_P1 hF
  have hZ0 : (centerOf (X.Q 0)).map (f112EOdd L1 L2 S).subtype =
      f112OfA L1 L2 S (centerOf (pCoreOf 2 (f112saP1' L1 L2 S))) := by
    rw [← CFSG.Quasithin.SimsD1.TransGrp.centerOf_map_eq _ (f112EOdd L1 L2 S).subtype_injective,
      hQ0, f112_ofA_centerOf L1 L2 S hQα]
  exact (natSec_of_map_iff hLα (inf_le_left.trans hQα) hQα hL0 hZ0 hQ0).mp hd.nat_left

theorem s3a5U42Hyp_of_treeU42Data {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S)
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : X.TreeU42Data) : S3A5U42Hyp L1 L2 S := by
  obtain ⟨-, hQ0, hQ1, -, -, -, -⟩ := s3a5_dictionary hF hX0 hX1
  have hQα := pCoreOf_P1'_le_P1 hF
  have hQβ := pCoreOf_P2'_le_P2 hF
  exact ⟨(isElemAbelian_of_map_iff_ofB hQβ hQ1).mp hd.elem_right,
    (card_of_map_eq_ofB hQβ hQ1).symm.trans hd.card_right,
    IsSpecialPow.of_mulEquiv ((isoOfMapEq (f112EOdd L1 L2 S) _ _ (f112Gold L1 L2 S).ofA
      (f112Gold L1 L2 S).ofA_injective hQ0).trans (Subgroup.subgroupOfEquivOfLe hQα))
      hd.special_left,
    natSec_left_of_treeU42Data hF hX0 hX1 hd⟩

theorem not_natSec_of_treeU42Data {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S)
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : X.TreeU42Data) :
    ¬ NatSec (oTwoPrime (f112saP2' L1 L2 S)) ⊥ (pCoreOf 2 (f112saP2' L1 L2 S)) := by
  obtain ⟨-, -, hQ1, -, hL1, -, -⟩ := s3a5_dictionary hF hX0 hX1
  have hQβ := pCoreOf_P2'_le_P2 hF
  have hLβ := oTwoPrime_P2'_le_P2 hF
  rw [← natSec_of_map_iff_ofB hLβ bot_le hQβ hL1 (map_bot_eq_ofB_bot L1 L2 S) hQ1]
  exact hd.notNat_right

private theorem natSec_left_of_treeJ2Data {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S)
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : X.TreeJ2Data) :
    NatSec (oTwoPrime (f112saP1' L1 L2 S)) ⊥ (pCoreOf 2 (f112saP1' L1 L2 S)) := by
  obtain ⟨-, hQ0, -, hL0, -, -, -⟩ := s3a5_dictionary hF hX0 hX1
  have hQα := pCoreOf_P1'_le_P1 hF
  have hLα := oTwoPrime_P1'_le_P1 hF
  exact (natSec_of_map_iff hLα bot_le hQα hL0 (map_bot_eq_ofA_bot L1 L2 S) hQ0).mp hd.nat_left

theorem s3a5J2Hyp_of_treeJ2Data {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S)
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : X.TreeJ2Data) : S3A5J2Hyp L1 L2 S := by
  obtain ⟨-, -, hQ1, -, -, -, -⟩ := s3a5_dictionary hF hX0 hX1
  have hQβ := pCoreOf_P2'_le_P2 hF
  exact ⟨CFSG.Quasithin.F112R.isQ8D8_of_mulEquiv ((isoOfMapEq (f112EOdd L1 L2 S) _ _
    (f112Gold L1 L2 S).ofB (f112Gold L1 L2 S).ofB_injective hQ1).trans
    (Subgroup.subgroupOfEquivOfLe hQβ)) hd.q8d8_right,
    natSec_left_of_treeJ2Data hF hX0 hX1 hd⟩

theorem card_pCoreOf_P1'_of_treeJ2Data {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S)
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : X.TreeJ2Data) : Nat.card ↥(pCoreOf 2 (f112saP1' L1 L2 S)) = 2 ^ 6 := by
  obtain ⟨-, hQ0, -, -, -, -, -⟩ := s3a5_dictionary hF hX0 hX1
  exact (card_of_map_eq (pCoreOf_P1'_le_P1 hF) hQ0).symm.trans hd.card_left

theorem exists_involution_of_treeJ2Data {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S)
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : X.TreeJ2Data) :
    ∃ x ∈ pCoreOf 2 (f112saP1' L1 L2 S), x ∉ pCoreOf 2 (f112saP2' L1 L2 S) ∧ x ^ 2 = 1 := by
  obtain ⟨-, hQ0, hQ1, -, -, -, -⟩ := s3a5_dictionary hF hX0 hX1
  have hQβ := pCoreOf_P2'_le_P2 hF
  obtain ⟨x, hx0, hx1, hx2⟩ := hd.inv_left
  have hxA : ((x : (f112Gold L1 L2 S).Universal)) ∈
      f112OfA L1 L2 S (pCoreOf 2 (f112saP1' L1 L2 S)) := by
    rw [← hQ0]
    exact Subgroup.mem_map_of_mem _ hx0
  obtain ⟨a, ha, hax⟩ := hxA
  refine ⟨(a : H), Subgroup.mem_subgroupOf.mp ha, fun haQ => hx1 ?_, ?_⟩
  · have haP2 : (a : H) ∈ f112P2 L1 L2 S := hQβ haQ
    have hab : (f112Gold L1 L2 S).ofA a = (f112Gold L1 L2 S).ofB ⟨(a : H), haP2⟩ :=
      f112sa_ofA_eq_ofB_of_mem_inf L1 L2 S ⟨a.2, haP2⟩
    have hmem : ((x : (f112Gold L1 L2 S).Universal)) ∈
        (X.Q 1).map (f112EOdd L1 L2 S).subtype := by
      rw [hQ1, ← hax, hab]
      exact ⟨⟨(a : H), haP2⟩, Subgroup.mem_subgroupOf.mpr haQ, rfl⟩
    exact (Subgroup.mem_map_iff_mem (f112EOdd L1 L2 S).subtype_injective).mp hmem
  · have h : (f112Gold L1 L2 S).ofA (a ^ 2) = (f112Gold L1 L2 S).ofA 1 := by
      rw [map_pow, hax, map_one]
      exact congrArg Subtype.val hx2
    have ha2 : a ^ 2 = 1 := (f112Gold L1 L2 S).ofA_injective h
    simpa using congrArg Subtype.val ha2

theorem exists_zSigma_of_treeJ2Data {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S)
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : X.TreeJ2Data) :
    ∃ Zs : Subgroup H, Zs ≤ pCoreOf 2 (f112saP2' L1 L2 S) ∧
      f112saP1' L1 L2 S ≤ Subgroup.normalizer (Zs : Set H) ∧
      centerOf (S ⊓ f112saK L1 L2 S) ≤ Zs := by
  obtain ⟨hG0, hQ0, hQ1, -, -, hS0, hsylK⟩ := s3a5_dictionary hF hX0 hX1
  have hP1' : f112saP1' L1 L2 S ≤ f112P1 L1 L2 S := f112sa_P1'_le_P1 hF.toW
  have hQα := pCoreOf_P1'_le_P1 hF
  have hQβ := pCoreOf_P2'_le_P2 hF
  have hTP : S ⊓ f112saK L1 L2 S ≤ f112P1 L1 L2 S :=
    inf_le_right.trans ((f112saK_le_P1' L1 L2 S).trans hP1')
  let Zs : Subgroup H :=
    (((X.Z 0).map (f112EOdd L1 L2 S).subtype).comap (f112Gold L1 L2 S).ofA).map
      (f112P1 L1 L2 S).subtype
  have hmem : ∀ a : ↥(f112P1 L1 L2 S),
      (f112Gold L1 L2 S).ofA a ∈ (X.Z 0).map (f112EOdd L1 L2 S).subtype → (a : H) ∈ Zs :=
    fun a ha => ⟨a, ha, rfl⟩
  have hZQ : (X.Z 0).map (f112EOdd L1 L2 S).subtype ≤
      f112OfA L1 L2 S (pCoreOf 2 (f112saP1' L1 L2 S) ⊓ pCoreOf 2 (f112saP2' L1 L2 S)) := by
    rw [← ofA_map_inf_ofB_map L1 L2 S hQα hQβ, ← hQ0, ← hQ1]
    exact le_inf (Subgroup.map_mono (X.Z_le_Q 0)) (Subgroup.map_mono hd.Z_left_le_right)
  refine ⟨Zs, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hba⟩ := hZQ ha
    rw [← (f112Gold L1 L2 S).ofA_injective hba]
    exact (Subgroup.mem_subgroupOf.mp hb).2
  ·
    have hconj : ∀ g ∈ f112saP1' L1 L2 S, ∀ z ∈ Zs, g * z * g⁻¹ ∈ Zs := by
      rintro g hg _ ⟨a, ha, rfl⟩
      obtain ⟨w, hw, hwa⟩ := Subgroup.mem_map.mp ha
      have hgA : (f112Gold L1 L2 S).ofA ⟨g, hP1' hg⟩ ∈
          (X.Gi 0).map (f112EOdd L1 L2 S).subtype := by
        rw [hG0]
        exact ⟨⟨g, hP1' hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
      obtain ⟨e, he, hea⟩ := Subgroup.mem_map.mp hgA
      have hew : e * w * e⁻¹ ∈ X.Z 0 := by
        rw [← X.Z_normal 0 e he, CFSG.Quasithin.mem_conjSub]
        simpa [mul_assoc] using hw
      show ((⟨g, hP1' hg⟩ * a * (⟨g, hP1' hg⟩)⁻¹ : ↥(f112P1 L1 L2 S)) : H) ∈ Zs
      refine hmem _ ⟨e * w * e⁻¹, hew, ?_⟩
      simp only [map_mul, map_inv, Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hea, ← hwa]
      rfl
    exact Subgroup.le_normalizer_iff.mpr hconj
  ·
    have hKT : pCoreOf 2 (f112saK L1 L2 S) = S ⊓ f112saK L1 L2 S :=
      eq_pCoreOf_of_isSylowTwoOf (f112sa_T_sylow_K hF.toW) hsylK
    have hSsyl : IsSylowTwoOf X.S (X.Gi 0) := by
      rw [← X.edgeSylow_zero]
      exact isSylowTwoOf_of_edgeStab X.hyp (X.adj 0) (X.isSylowTwoOf_edgeSylow 0)
    have hZS : centerOf X.S ⊓ X.Q 0 ≤ X.Z 0 :=
      le_iSup₂_of_le (f := fun P (_ : IsSylowTwoOf P (X.Gi 0)) => centerOf P ⊓ X.Q 0)
        X.S hSsyl le_rfl
    have hcS : (centerOf X.S).map (f112EOdd L1 L2 S).subtype =
        f112OfA L1 L2 S (centerOf (S ⊓ f112saK L1 L2 S)) := by
      rw [← CFSG.Quasithin.SimsD1.TransGrp.centerOf_map_eq _
        (f112EOdd L1 L2 S).subtype_injective, hS0, hKT, f112_ofA_centerOf L1 L2 S hTP]
    intro z hz
    have hzQ : z ∈ pCoreOf 2 (f112saP1' L1 L2 S) := (f112sa_centerOf_T_le_P1' hF hz).1
    have hzP : z ∈ f112P1 L1 L2 S := hTP hz.1
    have h1' : (f112Gold L1 L2 S).ofA ⟨z, hzP⟩ ∈ (centerOf X.S).map (f112EOdd L1 L2 S).subtype := by
      rw [hcS]
      exact ⟨⟨z, hzP⟩, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
    have h2' : (f112Gold L1 L2 S).ofA ⟨z, hzP⟩ ∈ (X.Q 0).map (f112EOdd L1 L2 S).subtype := by
      rw [hQ0]
      exact ⟨⟨z, hzP⟩, Subgroup.mem_subgroupOf.mpr hzQ, rfl⟩
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp h1'
    have hwQ : w ∈ X.Q 0 := by
      rw [← hwz] at h2'
      exact (Subgroup.mem_map_iff_mem (f112EOdd L1 L2 S).subtype_injective).mp h2'
    exact hmem ⟨z, hzP⟩ ⟨w, hZS ⟨hw, hwQ⟩, hwz⟩

end CFSG.Quasithin.F112R.St84
