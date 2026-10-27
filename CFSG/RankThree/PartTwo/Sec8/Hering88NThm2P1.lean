module

public import CFSG.RankThree.PartTwo.Sec8.Hering88NAlphaPrime
import CFSG.RankThree.PartTwo.Sec8.Rudvalis88Swap
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofAssembly
public import CFSG.RankThree.PartTwo.Sec8.Hering88FG2Two
public import CFSG.RankThree.PartTwo.Sec8.Hering88NThm2

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88N

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSp)

theorem five_dvd_card_projSp_two {n : ℕ} (hn : 1 ≤ n) :
    5 ∣ Nat.card (projSp 2 (GaloisField 2 n)) := by
  rw [Sec19.Step1911Proof.card_projSp_two hn]
  refine Dvd.dvd.mul_left (Dvd.dvd.mul_left ?_ _) _
  have h16 : (2 ^ n) ^ 4 = 16 ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h16]
  have hmod : 16 ^ n ≡ 1 [MOD 5] := by
    calc 16 ^ n ≡ 1 ^ n [MOD 5] := Nat.ModEq.pow n (by decide)
      _ = 1 := one_pow n
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow n 16 (by norm_num))).mp hmod.symm

theorem isSimpleGroup_isPerfect_of_projSp {Q : Type} [Group Q] [Finite Q] {C : Subgroup Q}
    {n : ℕ} (hn : 2 ≤ n) (ι : C ≃* projSp 2 (GaloisField 2 n)) :
    IsSimpleGroup C ∧ Group.IsPerfect C := by
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set ψ : C ≃* CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSp 2 (GaloisField 2 n)) :=
    ι.trans (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).symm with hψ
  have hs := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp
    (GaloisField 2 n) 2 (by norm_num) (Or.inl (Or.inr h4))
  have h4' : ∃ s : Finset (GaloisField 2 n), s.card = 4 := by
    have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ :
      Finset (GaloisField 2 n))) (n := 4) (by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
        exact h4)
    exact ⟨s, hs⟩
  have hp := CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect 2
    (GaloisField 2 n) (Or.inl h4')
  exact ⟨ψ.isSimpleGroup, hp.ofSurjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective⟩

theorem kF88Case1ClassBPGU_of
    (h45 : Sec4.Item4_5) (h83 : Item83) (h84 : Pair84A) (hF : KF84Field) (hPG : PartnerGamma88) :
    KF88Case1ClassBPGU := by
  intro G _ _ A c L a b X n h hn2 Y hY hIJ x hxc hxY A₀ d' m hodd hm2 hc1 hD4 hP d hdcl hdx hdA
    hd3 hdN hin hne _
  subst hxc
  classical
  obtain ⟨-, hA3⟩ := Hering88C.pair_commute_pow_three h
  have ha3 : a ^ 3 = 1 := hA3 a h.a_mem
  have hcN : x ∈ Subgroup.normalizer (Y : Set G) :=
    hxY.elim (fun h' => h'.mem_normalizer) (fun h' => h'.mem_normalizer)
  have haN : a ∈ Subgroup.normalizer (L : Set G) := h.toHyp81.a_mem_normalizer
  have hUn3 : ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3 :=
    Hering88F.not_isUnitaryTwo_three_of_two_le hn2
      (Item87Proof.isGammaType_of_isGammaIndex h.isGammaIndex)
  have hIdef : sec8I L a = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) := by
    simp only [sec8I, hUn3, ↓reduceIte]
  have hIY : sec8I L a ≤ Y := le_sup_left.trans hIJ
  have hIL_img : imageModTheta L (sec8I L a) =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) L) := by
    rw [hIdef]
    exact KFacts.imageModTheta_perfectResidual_centralizer_eq haN ⟨1, by simpa using ha3⟩
  have hI : sec8I L a ≠ ⊥ := by
    intro hbot
    apply kF87INontriv_holds G L a n (by omega)
      (Item87Proof.isGammaType_of_isGammaIndex h.isGammaIndex) hUn3 ha3 h.inducesStdKind h.gTwo
    rw [← hIL_img, hbot, imageModTheta, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  have hS := isSimpleGroup_inSubgroup_perfectResidual_of_isoPGUThree hm2 hP
  have hM1 := Hering88E.imageModTheta_sec8I_eq_perfectResidual kF87Cent_holds h hUn3 hI hY hIY
    hcN hS
  have hNI := card_quot_theta_eq_of_isSimpleGroup hIY hM1 hS
  rw [card_inSubgroup_perfectResidual_of_isoPGUThree hm2 hP] at hNI
  have hLU : ∃ g : ℕ, IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) g := by
    by_contra hnot
    push Not at hnot
    obtain ⟨N, r, hN, hr, hNr⟩ := even_two_part_of_isGammaIndex hn2 h.isGammaIndex hnot ha3
      h.inducesStdKind h.gTwo
    rw [← hIdef] at hNr
    exact KFacts.ne_ordTwistedA_two hr hN hodd (hNr.symm.trans hNI)
  have hk := h84 G A x L a b X n h
  have haX : a ∈ Subgroup.normalizer (X : Set G) :=
    hk.elim (fun h' => h'.mem_normalizer) (fun h' => h'.mem_normalizer)
  have hJX : sec8J X a ≤ X := (Item87Proof.residual_le _).trans inf_le_left
  have hJY : sec8J X a ≤ Y := le_sup_right.trans hIJ
  have hJX_img : imageModTheta X (sec8J X a) =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) X) :=
    KFacts.imageModTheta_perfectResidual_centralizer_eq haX ⟨1, by simpa using ha3⟩
  rcases h.centralizer_of_unitary hLU with hCX | hSp
  swap
  ·
    exfalso
    obtain ⟨ι⟩ := hSp
    obtain ⟨hSs, hPs⟩ := isSimpleGroup_isPerfect_of_projSp hn2 ι
    have hres : inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) X) =
        barCentralizer (Subgroup.zpowers a) X :=
      inSubgroup_perfectResidual_of_isPerfect (R := barCentralizer (Subgroup.zpowers a) X) hPs
    have hS' : IsSimpleGroup
        (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) X)) := by
      rw [hres]
      exact hSs
    have hN := card_quot_theta_eq_of_isSimpleGroup hJX hJX_img hS'
    rw [hres, Nat.card_congr ι.toEquiv] at hN
    have hdvd := card_quot_theta_dvd_card_imageModTheta hJY
    rw [hN] at hdvd
    exact five_not_dvd_card_of_case1 hodd (Or.inl hD4)
      (((five_dvd_card_projSp_two (by omega)).trans hdvd).trans
        (Subgroup.card_subgroup_dvd_card _))
  have h8 := exists_order_eight_quot_of_isoGTwoEven hJX hJX_img hCX (by omega)
  obtain ⟨hbY, hdb, A₀', d'', hc1'⟩ :=
    swap_data_of_order_eight h45 h83 h84 h hY hIJ hxY hodd (Or.inl hD4) hdcl hdx hdN hin hne h8
  have hbN : b ∈ Subgroup.normalizer (Y : Set G) :=
    hbY.elim (fun h' => h'.mem_normalizer) (fun h' => h'.mem_normalizer)
  have hG2b : IsoGTwoEven (barCentralizer (Subgroup.zpowers b) Y) m := by
    rcases hc1'.2.2 with hG2 | ⟨-, hPb, -⟩
    · exact hG2
    · exfalso
      have hJ := Item812Res6.sec8J_ne_bot_of_gTwoPartner kF87INontriv_holds h84 h
      have hSb := isSimpleGroup_inSubgroup_perfectResidual_of_isoPGUThree hm2 hPb
      have hM1b := Hering88E.imageModTheta_sec8J_eq_perfectResidual kF87Cent_holds h84 h hJ hY
        hJY hbN hSb
      have hNJY := card_quot_theta_eq_of_isSimpleGroup hJY hM1b hSb
      rw [card_inSubgroup_perfectResidual_of_isoPGUThree hm2 hPb] at hNJY
      have hNJX := card_quot_theta_eq_of_isSimpleGroup hJX hJX_img
        (Hering88E.isSimpleGroup_perfectResidual_of_isoGTwoEven hn2 hCX)
      rw [Hering88F.inSubgroup_perfectResidual_eq_of_isoGTwoEven hn2 hCX] at hNJX
      obtain ⟨K, _, _, hK, ⟨eG⟩⟩ := hCX
      rw [Nat.card_congr eG.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2,
        hK] at hNJX
      obtain ⟨s, hs, hseq⟩ := (CFSG.Timmesfeld.Orders.profile_ordG2 (f := n) (by omega)).two
      exact KFacts.ne_ordTwistedA_two hs ⟨n * 3, by ring⟩ hodd
        (hseq.symm.trans (hNJX.symm.trans hNJY))
  exact classB_swap_covered_of_partner h45 hF h84 hPG Hering88F.g2TwoCentThreeSolvable_holds h hY
    hIJ hbY hodd hc1' ⟨rfl, hn2, Or.inl hG2b⟩ hdcl hdb hdA hd3 hdN hin hne

end CFSG.RankThree.PartTwo.Sec8.Hering88N

end
