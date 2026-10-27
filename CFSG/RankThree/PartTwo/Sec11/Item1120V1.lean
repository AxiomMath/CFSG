module

public import CFSG.RankThree.PartTwo.Sec11.Item1120V1Data
public import CFSG.RankThree.PartTwo.Sec11.Item1119ResProofU
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
public import CFSG.RankThree.PartTwo.Sec11.Item1119StepsProofUV1

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Statements


@[expose] def Step1120V1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Big G A c L a R Y d x s r g →
      Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s} →
      ∀ y ∈ sec11P R g, (∀ w ∈ Subgroup.closure ({s, a, x ^ 3} : Set G),
          y * w * y⁻¹ * w⁻¹ ∈ Subgroup.zpowers d) →
        y ∈ Subgroup.closure ({s, x, a} : Set G)

@[expose] def Step1120Cube : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Big G A c L a R Y d x s r g →
      ∀ y ∈ Subgroup.zpowers (x ^ 3), y ^ 3 ≠ 1 → d ∈ Subgroup.zpowers y →
        g * y * g⁻¹ ∈ Subgroup.zpowers y → False

end Statements

section Provers


theorem step1120G_of_V0_V1 (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hV0 : Step1120V0) (hV1 : Step1120V1) : Step1120G := by
  intro G _ _ A c L a R Y d x s r g hbig hrs
  exact Item1119StepsProof.g_mem_normalizer_V_of_le h45 h113 h117 hbig
    (hV0 G A c L a R Y d x s r g hbig hrs) (hV1 G A c L a R Y d x s r g hbig hrs)

theorem item1120_of_V0_V1 (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hV0 : Step1120V0) (hV1 : Step1120V1) : Item1120 :=
  item1120_of_G h45 h113 (step1120G_of_V0_V1 h45 h113 h117 hV0 hV1)

theorem step1120V1_of_V0_Cube (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hV0 : Step1120V0) (hCube : Step1120Cube) : Step1120V1 := by
  intro G _ _ A c L a R Y d x s r g hbig hrs y hyP hy
  exact Item1120V1Proof.V1_le_V h45 h113 h117 hbig (hV0 G A c L a R Y d x s r g hbig hrs)
    (hCube G A c L a R Y d x s r g hbig) (y := y)
    (Item1120V1Proof.mem_V1_iff.mpr ⟨hyP, hy⟩)

theorem item1120_of_V0_Cube (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hV0 : Step1120V0) (hCube : Step1120Cube) : Item1120 :=
  item1120_of_V0_V1 h45 h113 h117 hV0 (step1120V1_of_V0_Cube h45 h113 h117 hV0 hCube)

theorem step1120Cube_of (h45 : Sec4.Item4_5) (h117 : Item117) (h118 : Item118) (h119 : Item119)
    (hG2 : KFact1117CubeG2) (hL3 : KFact1117CubeL3) : Step1120Cube := by
  intro G _ _ A c L a R Y d x s r g hbig y hyx3 hy3 hdy hgy
  have h := hbig.toSec11Data
  have hAe := h.mem_partTwoF.1
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe h.a_mem h.a_ne_one Y
      h.mem_thetaComponentsAt_Y
  have hsec := (h118 G A c L a R Y h.toSec11Std d g h.inf_eq h.closure_eq h.g_mem.2 h.g_not_mem
    h.conj_mem).2.2
  have hK := mem_thetaComponentsIn_sec11K_inf h.toSec11Std
  have hT := kType119 G A c L a R Y h.toSec11Std d h.inf_eq h.closure_eq
  have hyK : y ∈ sec11K L a :=
    (Subgroup.zpowers_le.mpr (Item1117Proof.x_cube_mem_sec11K h)) hyx3
  have hyx : y ∈ Subgroup.zpowers x :=
    (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 3)) hyx3
  obtain ⟨k, hk⟩ := Item1117Proof.x_pow_eq_one h
  have hyk : y ^ 3 ^ k = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_of_mem_zpowers hyx).trans (orderOf_dvd_of_pow_eq_one hk))
  have hgc := Item1117Proof.conj_g_c_mem h117 h
  have hgc' : g * c * g⁻¹ ≠ c := by
    intro he
    apply h.g_not_mem
    refine Sec10.mem_normalizer_zpowers_of_conj_mem ?_
    rw [he]
    exact Subgroup.mem_zpowers c
  rcases h119 G A c L a R Y h.toSec11Std d h.inf_eq h.closure_eq with
    ⟨hf, -⟩ | ⟨h2, hD⟩ | ⟨h3, hS⟩ | ⟨-, ⟨e⟩, -⟩
  · exact hbig.not_field hf
  · exact hG2 G A a c d Y (sec11K L a) g y hAe h.card_eq h.closure_eq
      h.mem_thetaComponentsAt_Y hAY hsec hK hT h2 hD hyK ⟨k, hyk⟩ hy3 hdy h.g_mem h.pow_eq_one
      hgy hgc hgc'
  · exact hL3 G A a c d Y (sec11K L a) g y hAe h.card_eq h.closure_eq
      h.mem_thetaComponentsAt_Y hAY hsec hK hT h3 hS hyK ⟨k, hyk⟩ hy3 hdy h.g_mem h.pow_eq_one
      hgy hgc hgc'
  · exact Item1117Proof.false_of_card_L32 h hbig.orderOf_x_gt e

theorem item1120_of_V0_kfacts (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h118 : Item118) (h119 : Item119) (hV0 : Step1120V0) (hG2 : KFact1117CubeG2)
    (hL3 : KFact1117CubeL3) : Item1120 :=
  item1120_of_V0_Cube h45 h113 h117 hV0 (step1120Cube_of h45 h117 h118 h119 hG2 hL3)

end Provers

end CFSG.RankThree.PartTwo.Sec11
