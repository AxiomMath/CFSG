module

public import CFSG.LocalAnalysis.StandardType.GGResThreeSettled
public import CFSG.LocalAnalysis.StandardType.GGResUnitaryQPlusKProducers
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkTransport
public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabels
public import CFSG.LocalAnalysis.StandardType.GGResLineJAssembly
public import CFSG.LocalAnalysis.StandardType.GGQTwoVACE6
public import CFSG.LocalAnalysis.StandardType.GGTDModelU

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.LineU TableB

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggIsWeylMatrix_eq_A_of_card_five_of_le
    {ι : Type} [Fintype ι] {M : CoxeterMatrix ι} (hM : GGIsWeylMatrix M)
    (hcard : Fintype.card ι = 5) (hle : Nat.card M.Group ≤ 720) :
    ∃ e : Fin 5 ≃ ι, M = (CoxeterMatrix.A 5).reindex e := by
  rcases hM with ⟨n, e, -, hcase⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
  · have hn : n = 5 := by
      have hc : Fintype.card (Fin n) = Fintype.card ι := Fintype.card_congr e
      simpa [hcard] using hc
    subst n
    rcases hcase with hA | ⟨-, hB⟩ | ⟨-, hD⟩
    · exact ⟨e, hA⟩
    · exfalso
      have h1 : Nat.card M.Group = Nat.card (CoxeterMatrix.B 5).Group := by
        rw [hB]
        exact Nat.card_congr ((CoxeterMatrix.B 5).reindexGroupEquiv e).toEquiv
      have h2 := SpFrame.card_coxeterB_ge 5 (by norm_num)
      rw [← h1] at h2
      have h3 : 2 ^ 5 * Nat.factorial 5 = 3840 := by decide
      omega
    · exfalso
      have h1 : Nat.card M.Group = Nat.card (ggCoxeterMatrixD 5).Group := by
        rw [hD]
        exact Nat.card_congr ((ggCoxeterMatrixD 5).reindexGroupEquiv e).toEquiv
      rw [h1, OrthF3.card_coxeterD_eq 5 (by norm_num)] at hle
      have h3 : 2 ^ (5 - 1) * Nat.factorial 5 = 1920 := by decide
      omega
  all_goals
    exfalso
    have hc := Fintype.card_congr e
    simp [hcard] at hc

theorem ggWeylTypeData_six_not_dvd_720 {n c : ℕ} (h : GGWeylTypeData 6 n c) : ¬ n ∣ 720 := by
  intro hdvd
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  rcases h with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ |
      ⟨h4, -⟩ | ⟨h2, -⟩
  · have : Nat.factorial (6 + 1) = 5040 := by decide
    omega
  · have : 2 ^ 6 * Nat.factorial 6 = 46080 := by decide
    omega
  · have : 2 ^ (6 - 1) * Nat.factorial 6 = 23040 := by decide
    omega
  · omega
  · omega
  · omega
  · omega
  · omega

section CardBs


theorem GGResHyp.card_Bs_of_e6Two_L
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hm : 5 ≤ LargeEvenTwoLocalRank 3 G)
    (hL : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E6 ∧ lab.n = 1) 3 Bs L) :
    Nat.card Bs = 3 ^ 5 ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
      GGHasLabel ⟨.E6, 0, 1⟩ (↥L ⧸ Subgroup.center ↥L) := by
  obtain ⟨hperf, labL, hΛL, hrawL⟩ := hL
  have hlabL : labL.tag = .E6 ∧ labL.n = 1 :=
    GGDichotomy.rawDatum_elim_const (lab := labL) (Q := labL.tag = .E6 ∧ labL.n = 1)
      (largeEvenRawDatum_mono (fun R _ I F h => by
        obtain ⟨-, -, θ, hP, -⟩ := h
        exact hP) hrawL)
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.rawDatum_elim_const (lab := labL) (Q := Bs ≤ Subgroup.normalizer (L : Set G))
      (largeEvenRawDatum_mono (fun R _ I F h => by
        obtain ⟨-, -, θ, -, hN, -⟩ := h
        exact hN) hrawL)
  have hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = labL) 3 Bs L :=
    ⟨hperf, labL, hΛL, largeEvenRawDatum_mono (fun R _ I F h => by
      obtain ⟨hs, hna, θ, -, hP⟩ := h
      exact ⟨hs, hna, θ, rfl, hP⟩) hrawL⟩
  have hq2 : GGLabQTwo 3 labL := by
    unfold GGLabQTwo
    omega
  have hle := ggQTwoE6_card_Bs_le_three_pow_five hH.1 hq2 hlabL.1 hmark
  have hcardB : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hH.1.1.2.2.2.2.2.2.1.1.2.1
  have hB5 : 3 ^ 5 ≤ Nat.card B := by
    rw [hcardB]
    exact Nat.pow_le_pow_right (by norm_num) hm
  have hBBs : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hH.1.2.1.1
  exact ⟨le_antisymm hle (hB5.trans hBBs), hN, ggQTwoE6_hasLabel_E6 (_B := B) hq2 hlabL.1 hmark⟩

end CardBs

section ResidualK


theorem GGResHyp.residual_K_six_two_cell_or_card_dvd
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hm : 5 ≤ LargeEvenTwoLocalRank 3 G)
    (hBs5 : Nat.card Bs ≤ 3 ^ 5)
    (hK : GGInnerDiagOnLabel ggThreeResidualLabelK 3 Bs K) :
    GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) 3 Bs K ∨
      Nat.card ↥(ggAutomizer K Bs) ∣ 720 := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hnb : GGNbr 3 B x D J y K := hH.2.2.2.2.1
  have hSy : LargeEvenSHat 3 B y K := hnb.1
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hK
  have hraw0 := hraw
  obtain ⟨R₀, iR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hP₀⟩ := hQ₀
  obtain ⟨⟨htag, hr4, hdvd, hpq⟩, hN, -⟩ := hP₀
  obtain ⟨tag, rank, n⟩ := lab
  change tag = .twA at htag
  change 4 ≤ rank at hr4
  change 3 ∣ rank + 1 at hdvd
  change 3 ∣ 2 ^ n + 1 at hpq
  subst tag
  dsimp only [LargeEvenRawDatumLegacy] at hraw
  obtain ⟨F, hField, hFinite, hFK, hQ⟩ := hraw
  let _ : Field F := hField
  let _ : Finite F := hFinite
  obtain ⟨-, -, θ, hP⟩ := hQ
  obtain ⟨-, -, hact⟩ := hP
  have hn : 1 ≤ n := hΛ.1
  have hdq : (rank + 1, 2 ^ n) ≠ (3, 2) := by
    intro h
    have h1 := congrArg Prod.fst h
    simp only at h1
    omega
  have hlift := ggTorusLift_unitary hFK hn (by omega : 3 ≤ rank + 1) hdq hp hpq
  have hr := pow_le_card_range_ggGamma_bstar_of_torusLift hH.1 hnb hperf θ hN hlift
  have hrk : ggUnitaryTorusRank 3 (rank + 1) = rank + 1 - 3 := by
    simp only [ggUnitaryTorusRank, if_pos hdvd]
  rw [hrk] at hr
  have hyB : y ∈ B := hSy.2.1
  have hy1 : y ≠ 1 := hSy.2.2.1
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hSy.2.2.2.1
  have hyC : y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKy hk)
  have hup := card_range_ggGamma_mul_prime_le hp hBs hN (hH.1.2.1.1 hyB) hy1 hyC
  have h5 : rank = 5 := by
    have h1 : 3 ^ (rank + 1 - 3 + 1) ≤ 3 ^ 5 := by
      rw [pow_succ]
      exact (Nat.mul_le_mul_right 3 hr).trans (hup.trans hBs5)
    have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h1
    omega
  subst h5
  by_cases hn1 : n = 1
  · left
    subst hn1
    have hraw1 := (largeEvenRawDatum_legacy _ _).mpr hraw0
    refine ⟨hperf, ⟨.twA, 5, 1⟩, hΛ, (largeEvenRawDatum_legacy _ _).mp ?_⟩
    exact largeEvenRawDatum_mono (fun R _ I F h => by
      obtain ⟨hs, hna, θ', -, hP'⟩ := h
      exact ⟨hs, hna, θ', ⟨rfl, rfl, rfl⟩, hP'⟩) hraw1
  right
  have hn2 : 2 ≤ n := by omega
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := hH.1.2.1.1.trans hN
  have hcA := card_range_ggGamma_mul_of_sHat hp hSy hBN
  have hle : Nat.card (ggGamma K hBN).range ≤ Nat.card (ggGamma K hN).range := by
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hH.1.2.1.1 b.2⟩, rfl⟩
  have hcardB : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hSy.1.2.1
  have h4 : 3 ^ 4 ≤ Nat.card (ggGamma K hN).range := by
    have hB5 : 3 ^ 5 ≤ Nat.card B := by
      rw [hcardB]
      exact Nat.pow_le_pow_right (by norm_num) hm
    rw [← hcA, pow_succ] at hB5
    exact (Nat.le_of_mul_le_mul_right hB5 (by norm_num)).trans hle
  obtain ⟨ψ, hM, hdiag⟩ :=
    hH.exists_unitaryModel_K_six_three_qGeFour_of_gamma hFK hn2 hpq θ hN hact h4
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hperf θ hN
    (fun b hb => ggLAut_mem_of_induces K θ hN hact hb) h4 (le_trans (by norm_num) h4)
  obtain ⟨-, -, -, hA, -, -, -, hsc⟩ := hTB
  have hTor := ggTorusTorData_of_model_U (N := 5) hFK hp (by norm_num) hpq (by norm_num) hM hA
    hsc hdiag
  obtain ⟨w, hw⟩ := hTor
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨e, -⟩⟩ := hw
  have hinner : Nat.card ↥(ggAutomizer (MulAut.conj : ↥K →* MulAut ↥K).range
      (ggGamma K hN).range) = 720 := by
    rw [← Nat.card_congr e.toEquiv, l05nK3a_card_coxeterA 5]
    decide
  have hZ := ggNbr_card_center_le_of_centerPCyclic ggLabelCenterPCyclicInput_holds hH.1
    (hH.2.2.1.2 y K hnb)
  have hdvd' := card_ggAutomizer_dvd_gamma hp hBs hH.2.2.2.1 hN hZ
  rwa [hinner] at hdvd'

end ResidualK

section Cert


theorem GGResHyp.not_exactThree_K_of_e6Two_L_residual_K
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E6 ∧ lab.n = 1) 3 Bs L)
    (hK : GGInnerDiagOnLabel ggThreeResidualLabelK 3 Bs K) :
    ¬ GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny := by
  classical
  intro hD
  have hLq : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs L :=
    GGInnerDiagOnLabel.mono_label (fun lab h => ⟨h.1, by rw [h.2]; norm_num⟩) hL
  obtain ⟨hcardL, hm⟩ := hH.card_automizer_L_and_twoLocalRank_of_splitE6_qplus hLq
  obtain ⟨hcard5, hN, hLlab⟩ := hH.card_Bs_of_e6Two_L hm hL
  rcases hH.residual_K_six_two_cell_or_card_dvd hm hcard5.le hK with hcell | hdvd720
  · exact hH.not_exactThree_K_of_six_two_cell hcell hD
  obtain ⟨Λ, i1, i2, Sdel, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS3, hA1, hA3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hdel, hclosJ⟩ := hD
  let _ := i1
  let _ := i2
  let _ := i3
  let _ := i4
  let _ := i5
  let _ := i6
  have hcardMK : Nat.card MK.Group = 1152 := by
    rw [Nat.card_congr fK.toEquiv]
    exact hcardL
  have hWMK := ggWeylTypeData_of_isWeylMatrix hMK
  rw [hcardMK] at hWMK
  have hF4 : GGWeylTypeData 4 1152 2 :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨rfl, by norm_num, by norm_num⟩))))))
  have hrankK := ggWeylTypeData_rank_eq hWMK hF4
  rw [Fintype.card_sum, Fintype.card_subtype_compl, Fintype.card_coe, hS3] at hrankK
  have hΛa1 : 1 ≤ Fintype.card Λa := by rw [← Nat.card_eq_fintype_card]; exact hA1
  have hΛa3 : Fintype.card Λa ≤ 3 := by rw [← Nat.card_eq_fintype_card]; exact hA3
  have hΛ3 : 3 ≤ Fintype.card Λ := hS3 ▸ Finset.card_le_univ Sdel
  have hcardML : Nat.card ML.Group ∣ 720 := by
    rw [Nat.card_congr fL.toEquiv]
    exact hdvd720
  have hWML := ggWeylTypeData_of_isWeylMatrix hML
  have hmemJ : ∀ j : {j : Λ // j ∉ Sdel}, φ (Sum.inl j) ∈ ggAutomizer J Bs := by
    intro j
    rw [hclosJ]
    exact Subgroup.subset_closure ⟨j, rfl⟩
  rcases (by omega : Fintype.card Λ = 4 ∨ Fintype.card Λ = 5 ∨ Fintype.card Λ = 6) with
    h4 | h5 | h6
  ·
    have hcompl : Fintype.card {i : Λ // i ∉ Sdel} = 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_coe, h4, hS3]
    obtain ⟨j⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card {i : Λ // i ∉ Sdel})
    have hAJne : ggAutomizer J Bs ≠ ⊥ := by
      intro hbot
      have hj := hmemJ j
      rw [hbot, Subgroup.mem_bot] at hj
      exact (hrefl (Sum.inl j)).ne_one Nat.prime_three hj
    rcases ggAutomizer_eq_bot_or_zpowers_of_card_le_four φ hS3 (by omega) hrefl hclosJ with
      hbot | ⟨τ, hτ, hAJ⟩
    · exact hAJne hbot
    · exact hH.false_of_automizer_J_eq_zpowers_of_twoLocalRank hm hτ hAJ
  ·
    obtain ⟨eA, hMA⟩ := ggIsWeylMatrix_eq_A_of_card_five_of_le hML h5
      (Nat.le_of_dvd (by norm_num) hcardML)
    have hcompl : Nat.card {i : Λ // i ∉ Sdel} = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_coe, h5, hS3]
    obtain ⟨u, v, huv, huniv⟩ := Nat.card_eq_two_iff.mp hcompl
    have hcover : ∀ w : {i : Λ // i ∉ Sdel}, w = u ∨ w = v := by
      intro w
      have hw : w ∈ ({u, v} : Set {i : Λ // i ∉ Sdel}) := by
        rw [huniv]
        exact Set.mem_univ w
      simpa using hw
    have hadj : ML.M u v ≠ 2 := by
      rcases Relation.ReflTransGen.cases_head (hdel u v) with huv' | ⟨c, ⟨huc, hc2⟩, -⟩
      · exact absurd huv' huv
      · rcases hcover c with rfl | rfl
        · exact absurd rfl huc
        · exact hc2
    have huv1 : u.1 ≠ v.1 := fun h' => huv (Subtype.ext h')
    have hle3 : ML.M u.1 v.1 ≤ 3 := by
      rw [hMA]
      exact coxeterMatrixA_reindex_le_three eA _ _
    have hCuv : CL u.1 v.1 = -1 ∧ CL v.1 u.1 = -1 := by
      rcases hCL.2 u.1 v.1 huv1 with ⟨h2, -, -⟩ | ⟨-, hc1, hc2⟩ | ⟨h4', -⟩ | ⟨h6', -⟩
      · exact absurd h2 hadj
      · exact ⟨hc1, hc2⟩
      · change ML.M u.1 v.1 = 4 at h4'
        omega
      · change ML.M u.1 v.1 = 6 at h6'
        omega
    let pr : Fin 2 → Λ := ![u.1, v.1]
    let r : Fin 2 → MulAut ↥Bs := fun k => φ (Sum.inl (pr k))
    let hv : Fin 2 → V := fun k => h (Sum.inl (pr k))
    let αv : Fin 2 → Module.Dual (ZMod 3) V := fun k => α (Sum.inl (pr k))
    have hform : ∀ k w, ggLin (p := 3) ι (r k) w = w - αv k w • hv k :=
      fun k w => hlin (Sum.inl (pr k)) w
    have hCLA : ∀ i j, CL (pr i) (pr j) = CartanMatrix.A 2 i j := by
      intro i j
      fin_cases i <;> fin_cases j
      · show CL u.1 u.1 = CartanMatrix.A 2 0 0
        rw [hCL.1]
        decide
      · show CL u.1 v.1 = CartanMatrix.A 2 0 1
        rw [hCuv.1]
        decide
      · show CL v.1 u.1 = CartanMatrix.A 2 1 0
        rw [hCuv.2]
        decide
      · show CL v.1 v.1 = CartanMatrix.A 2 1 1
        rw [hCL.1]
        decide
    have hpairv : ∀ i j, αv i (hv j) = (CartanMatrix.A 2 i j : ZMod 3) := by
      intro i j
      rw [← hCLA i j]
      exact hpairL (pr i) (pr j)
    have hrange : Set.range r = Set.range fun j : {j : Λ // j ∉ Sdel} => φ (Sum.inl j) := by
      ext ψ
      constructor
      · rintro ⟨k, rfl⟩
        fin_cases k
        · exact ⟨u, rfl⟩
        · exact ⟨v, rfl⟩
      · rintro ⟨j, rfl⟩
        rcases hcover j with rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    have hmem : ∀ k, r k ∈ ggAutomizer J Bs := by
      intro k
      fin_cases k
      · exact hmemJ u
      · exact hmemJ v
    rcases linearIndependent_coroots_or_eq_of_A2 ι hform hpairv hmem hH.2.2.2.1 with hind | heq
    ·
      have hLine : GGResLineJDatum 3 Bs J .A2 :=
        ⟨V, inferInstance, inferInstance, ι, r, hv, αv, hform, fun k => hrefl _, hpairv, hind,
          hclosJ.trans (congrArg Subgroup.closure hrange.symm)⟩
      obtain ⟨lab3, hΛ3, hLine3, hHas3⟩ :=
        ggResLineJLabelInput_holds G 3 B Bs x L D J y K hH rfl .A2 hLine
      obtain ⟨labJ, hΛJ, hHasJ, hW, -⟩ := hH.exists_e6_two_original_J_label_table hL
      have hLineJ := ggResLineJLabel_of_iso hLine3
        (ggLabelRigidInput_holds lab3 labJ _ hΛ3 hΛJ hHas3 hHasJ)
      unfold TablePThreeKG.E6TwoCompLabelW at hW
      rcases hW with rfl | rfl | rfl
      · simp [ggResLineJLabel] at hLineJ
      · simp [ggResLineJLabel] at hLineJ
      · have hJL : J ≤ L := hH.1.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
        have hJsub : GGHasLabel ⟨.A, 2, 2⟩
            (↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L)) :=
          ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJL).symm hHasJ
        have hZ : Subgroup.center ↥L = ⊥ := ggQTwoE6_center_bot (K := ↥L) hL.1 hLlab
        have hZL : ∀ g ∈ Subgroup.center ↥L, Nat.Coprime 3 (orderOf g) := by
          intro g hg
          rw [hZ, Subgroup.mem_bot] at hg
          rw [hg]
          norm_num
        exact ggR4Meet_noE6TwoL34 hH.1 hN hcard5 hL.1 hZL hLlab hJsub
    ·
      have hr1 : Set.range r = {r 0} := by
        ext ψ
        constructor
        · rintro ⟨k, rfl⟩
          fin_cases k
          · rfl
          · exact heq.symm
        · rintro rfl
          exact ⟨0, rfl⟩
      have hAJ : ggAutomizer J Bs = Subgroup.zpowers (r 0) := by
        rw [hclosJ, ← hrange, hr1, Subgroup.zpowers_eq_closure]
      exact hH.false_of_automizer_J_eq_zpowers_of_twoLocalRank hm (hrefl _) hAJ
  ·
    rw [h6] at hWML
    exact ggWeylTypeData_six_not_dvd_720 hWML hcardML

end Cert

end CFSG.StandardType

end
