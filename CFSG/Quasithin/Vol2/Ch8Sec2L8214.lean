module

public import CFSG.Quasithin.Vol2.Ch8Sec2L8212G
public import CFSG.Quasithin.Vol2.Ch8Sec2HFus

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

theorem stmt8_2_14_fusion_of
    (h3228 : Stmt3_2_2_eight) (h3109 : Stmt3_2_10_nine)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h711n : Stmt7_1_1_normal)
    (h822 : Stmt8_2_2) (h825 : Stmt8_2_5) (h828 : Stmt8_2_8) (h829 : Stmt8_2_9_12)
    (h8213 : Stmt8_2_13) (hm24 : SchurMult2M24) : Stmt8_2_14_fusion := by
  have hcovL : KG82CoverL34 := kg82CoverL34_holds
  have hcovM : KG82CoverM22 := kg82CoverM22_holds
  have hsimp : HSimple82 := hSimple82_holds
  have hcent : HCent82 := hCent82_holds
  have htype : HType82 := hType82_holds
  have hpar : HParab82 := hParab82_holds
  have hfus : HFus82 := hFus82_holds
  intro G _ _ T L I hyp h731 h821 hc hrow z hz hzV
  obtain ⟨hV, hTL, hLN, hTV, hVT, hVL, hCLV, hTCL, hL0, hmod, hn1⟩ :=
    setup_82 h3228 h3109 h37 h38 h39 h711n h822 h825 h828 h829 hsimp hcent htype hpar hcovL
      hcovM hm24 hyp h731 h821 hrow
  have hco : Row711M24Cocode T L I := (h8213 G T L I hyp h731 h821 hc hrow).1.1
  set V := fsuV T I with hVdef
  have hM : MathieuCocode24 (V := ↥V) (autOn L V) ⊤ ⊥ := by
    rw [← hL0]
    exact hco
  have hzVT : z ∈ V ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hzV' : z ∈ V := hzVT.1
  have hzT : z ∈ Subgroup.centralizer (T : Set G) := hzVT.2
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz
    norm_num at hz
  set z' : ↥V := ⟨z, hzV'⟩ with hz'def
  have hz'1 : z' ≠ 1 := fun h1 => hz1 (congrArg Subtype.val h1)
  have hSc := card_autOn_inf_of_sylow (isSylowIn_top_of_fsu hyp.fsu) hTL hTV
  have hSz : z' ∈ fixV (autOn (T ⊓ L) V) := by
    rintro _ ⟨t, ht, rfl⟩
    have ht' : (t : G) ∈ T := ht.1
    apply Subtype.ext
    rw [CFSG.QuasithinUnique.Setup.coe_conjAct_apply,
      Subgroup.mem_centralizer_iff.mp hzT t ht', mul_inv_cancel_right]
  have hSH : autOn (T ⊓ L) V ≤ autOn L V := Subgroup.map_mono fun x hx => hx.2
  have hCLp : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [hCLV]
    exact isPGroup_of_isElemAbelian_two hV
  have hWbar : vz82 (autOn L V) z' = (ch8Vz V L z).subgroupOf V := vz82_eq_82 hzV' hLN hCLp
  obtain ⟨φ, hφ, hφz, hφW⟩ := hfus ↥V (autOn L V) z' hM hz'1 ⟨_, hSH, hSc, hSz⟩
  obtain ⟨n, hn, rfl⟩ := hφ
  have hn' : (n : G) ∈ L := hn
  refine ⟨(n : G)⁻¹, L.inv_mem hn', ?_, ?_⟩
  · rw [hWbar, Subgroup.mem_subgroupOf, CFSG.QuasithinUnique.Setup.coe_conjAct_apply] at hφW
    simpa using hφW
  · intro h1
    apply hφz
    apply Subtype.ext
    rw [CFSG.QuasithinUnique.Setup.coe_conjAct_apply]
    simpa using h1

end CFSG.Quasithin.H13
