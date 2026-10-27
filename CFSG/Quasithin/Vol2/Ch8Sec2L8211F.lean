module

public import CFSG.Quasithin.Vol2.Ch8Sec2L8211E
public import CFSG.Quasithin.Vol2.Ch8Sec2L8212F
public import CFSG.Quasithin.Vol2.Ch8Sec2L8212B

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin
open scoped IsMulCommutative

theorem stmt8_2_11_of
    (h3228 : Stmt3_2_2_eight) (h3109 : Stmt3_2_10_nine) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h711n : Stmt7_1_1_normal) (h822 : Stmt8_2_2)
    (h825 : Stmt8_2_5) (h828 : Stmt8_2_8) (h829 : Stmt8_2_9_12) (hcovL : KG82CoverL34)
    (hcovM : KG82CoverM22) (hm24 : SchurMult2M24) : Stmt8_2_11 := by
  have hsimp : HSimple82 := hSimple82_holds
  have hcent : HCent82 := hCent82_holds
  have htype : HType82 := hType82_holds
  have hpar : HParab82 := hParab82_holds
  intro G _ _ T L I hyp h731 h821 hc hrow hnot24 z hz hzV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV, hTL, hLN, hTV, hVT, hVL, hCLV, hTCL, hL0, hmod, hn1⟩ :=
    setup_82 h3228 h3109 h37 h38 h39 h711n h822 h825 h828 h829 hsimp hcent htype hpar hcovL
      hcovM hm24 hyp h731 h821 hrow
  set V := fsuV T I with hVdef
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
  obtain ⟨e, hmode⟩ : ∃ e, IsModel82e (V := ↥V) (autOn L V) e := by
    rcases hrow with ⟨n, hn⟩ | h' | h' | h'
    · obtain rfl := hn1 n hn
      refine ⟨4, Or.inl ⟨?_, rfl⟩⟩
      rw [← hL0]
      exact hn.2
    · refine ⟨4, Or.inr (Or.inl ⟨?_, rfl⟩)⟩
      rw [← hL0]
      exact h'
    · exact absurd h' hnot24
    · refine ⟨6, Or.inr (Or.inr ⟨?_, rfl⟩)⟩
      rw [← hL0]
      exact h'
  have hSc := card_autOn_inf_of_sylow (isSylowIn_top_of_fsu hyp.fsu) hTL hTV
  have hconj : ∀ t ∈ T, ∀ ht : t ∈ Subgroup.normalizer (V : Set G),
      conjAct V ⟨t, ht⟩ z' = z' := by
    intro t ht htN
    apply Subtype.ext
    rw [CFSG.QuasithinUnique.Setup.coe_conjAct_apply,
      Subgroup.mem_centralizer_iff.mp hzT t ht, mul_inv_cancel_right]
  have hSz : z' ∈ fixV (autOn (T ⊓ L) V) := by
    rintro _ ⟨t, ht, rfl⟩
    exact hconj t ht.1 t.2
  have hSH : autOn (T ⊓ L) V ≤ autOn L V := Subgroup.map_mono fun x hx => hx.2
  have hSV : IsSylowVec82 (autOn L V) z' := ⟨_, hSH, hSc, hSz⟩
  have hTN : autOn T V ≤ Subgroup.normalizer (autOn L V : Set (MulAut ↥V)) :=
    autOn_le_normalizer_82 hTL
  have hTz : autOn T V ≤ centSub (Subgroup.zpowers z') := by
    rintro _ ⟨t, ht, rfl⟩ u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [map_zpow, hconj t ht t.2]
  have hLzN : ch8Lz L z ≤ Subgroup.normalizer (V : Set G) :=
    ((perfectCore_le _).trans inf_le_left).trans hLN
  have hsup : autOn (ch8Lz L z ⊔ T) V = autOn (ch8Lz L z) V ⊔ autOn T V := by
    unfold autOn
    rw [Subgroup.subgroupOf_sup hLzN hTV, Subgroup.map_sup]
  have hLz : autOn (ch8Lz L z) V = parz82 (autOn L V) z' := autOn_ch8Lz_82 hLN z'
  rw [hsup, hLz]
  exact L8211.pCoreOf_parz82_sup hmode hz'1 hSV hTN hTz

end CFSG.Quasithin.H13
