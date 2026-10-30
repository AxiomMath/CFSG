module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.StatementsDeltaFree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.DeltaAPI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenOne
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ui
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem517
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThreeOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTen
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}

theorem oUpperTwo_eq_twoResidual (H : Subgroup G) :
    S17.oUpperTwo H = CFSG.Quasithin.twoResidual H :=
  (CFSG.Quasithin.H13.twoResidual_eq_oTwoUpper' H).symm

theorem not_normalizer_wClos_le_of_no_calO1 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h126 : R126 D) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hV₀ : V₀ ≠ ⊥) {s : ℕ}
    (hkr : ((s + D.k : ℕ) : ℕ∞) < rMV D.M V)
    (hkm : s + D.k < mBar D.M V₀ V h.isElemAbelian)
    (hno : ∀ g : G, ¬ InCalO1 (s + D.k) D.M V₀ V g) :
    ¬ normalizer (E3.wClos V s D.T : Set G) ≤ D.M := by
  obtain ⟨H₀, hmin⟩ := h.exists_hyp124Min
  have hE : E1.InE D.k H₀ := h126 H₀ hmin
  have hT : IsSylowIn 2 D.T H₀ := TwelveShort.isSylowIn_of_le D hmin.1.1
  have hH := (weakClosureSetting_of_hyp125 D hx h61 h127 h1114 h hV₀).hyp6H
  have hgen := TwelveEighteen.six_thirteen_two_of_no_calO1_gen hH hV₀ (i := s) (n := D.k)
    le_rfl hkr hkm hno hT hE
  have hC : H₀ ⊓ centralizer (E3.cClos V (s + D.k) D.T : Set G) ≤ D.M :=
    inf_le_right.trans (TwelveTwentyTwo.centralizer_cClos_le h hV₀ _)
  intro hN
  apply hmin.1.2.1
  rw [← hgen]
  exact sup_le (inf_le_right.trans hN) hC

theorem oUpperTwo_not_le_conj_of_p_dvd (h : Hyp18 D V₀ V p L) (hSg : UC6S846.SigmaStd D)
    {H : Subgroup G} (hHM : H ≤ D.M) (hp : p ∣ Nat.card H) :
    ∀ g : G, g ∉ D.M → ¬ S17.oUpperTwo H ≤ CFSG.Quasithin.conjSubgroup D.M g := by
  intro g hg hle
  haveI : Fact p.Prime := ⟨h.p_prime⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) p hp
  have hxp : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe, hx]
  have hxodd : Odd (orderOf (x : G)) := by
    rw [hxp]
    exact h.p_prime.odd_of_ne_two h.p_ne_two
  have hxO : (x : G) ∈ S17.oUpperTwo H := by
    unfold S17.oUpperTwo CFSG.ComponentClassification.AS76b.oUpperTwo
    exact Subgroup.subset_closure ⟨x.2, hxodd⟩
  have hxM : (x : G) ∈ D.M ⊓ CFSG.Quasithin.conjSubgroup D.M g := ⟨hHM x.2, hle hxO⟩
  have hdvd := Subgroup.orderOf_dvd_natCard (D.M ⊓ CFSG.Quasithin.conjSubgroup D.M g) hxM
  rw [hxp] at hdvd
  exact h.p_not_dvd_card_inf hSg hg hdvd

theorem r18_7b_of_bot (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D)
    (h111 : W3Thm111 G) (h : Hyp18 D V₀ V p L) (hV₀ : V₀ = ⊥)
    (hL1 : barSub V₀ V h.hyp125.isElemAbelian L ≠ ⊥)
    (h17_66_1 : S17.R17_66_1At D V₀ V) (h18_4 : R18_4At D V₀ V p L) :
    R18_7bAt D V₀ V p L h := by
  intro hgt
  have hk2 : D.k ≤ 2 := TwelveSeven.k_le_two D
  have hUL : UniqueMax D.M L := by
    rcases h17_66_1 p h.hp L h.hL (UC22.conjClosure D.M L) rfl h.hX with hh | hh
    · exact hh
    · exact absurd hh h18_4
  have hU : UniqueMax D.M (UC22.conjClosure D.M L) :=
    uc22p22u_uniqueMax_mono D (TwelveTwentyThree.le_conjClosure D.M L)
      (TwelveTwentyThree.conjClosure_le h.hL.1.1.le) hUL
  have h1223 := twelve_twentyThree_one D hx h61 h126 h111 h.hyp125 hV₀ h.hL.1.1 h.hL.1.2.2 hL1 hU
  have hlt := (h.hyp125.mBarGT_iff_lt_mBar _).1 hgt
  omega

section Certified


theorem eighteen_one_four_max (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hV₀ : V₀ ≠ ⊥)
    (hhyp : MBarGT D.M V₀ V
        (bBar (UC22.conjClosure D.M L) D.M V₀ V h.hyp125.isElemAbelian + 1) ∨
      calO 1 D.M V₀ V = ∅)
    (hX1 : barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) ≠ ⊥)
    {Δ : Set (Subgroup G)} (hΔ : ∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M)
    (hΔU : UniqueMax D.M (⨆ H ∈ Δ, H))
    (hO2 : ∀ H ∈ Δ, ∀ g : G, g ∉ D.M →
      ¬ S17.oUpperTwo H ≤ CFSG.Quasithin.conjSubgroup D.M g) :
    (mBar D.M V₀ V h.hyp125.isElemAbelian : ℕ∞) ≤ fIndexMax Δ + (D.k : ℕ∞) := by
  classical
  have hV := h.hyp125.isElemAbelian
  by_cases htop : fIndexMax Δ = ⊤
  · rw [htop, top_add]
    exact le_top
  set i := (fIndexMax Δ).toNat with hi
  have hieq : fIndexMax Δ = (i : ℕ∞) := (ENat.coe_toNat htop).symm
  have hF : ∀ H ∈ Δ, InFSq i H := fIndexMax_le_iff.1 hieq.le
  rw [hieq]
  by_contra hlt
  have hlt' : i + D.k < mBar D.M V₀ V hV := by
    have : ((i + D.k : ℕ) : ℕ∞) < (mBar D.M V₀ V hV : ℕ∞) := by
      push_cast
      exact not_le.1 hlt
    exact_mod_cast this
  have hk := TwelveShort.one_le_k D
  have h11 := eighteen_one_one D hx h61 h127 h1114 h162 h hV₀ hhyp hX1
  have h12 := eighteen_one_two D hx h61 h127 h1114 h162 hTor h1482 h hV₀ hhyp hX1
  have hHs := (weakClosureSetting_of_hyp125 D hx h61 h127 h1114 h.hyp125 hV₀).hyp6H
  have hno : ∀ n, n < mBar D.M V₀ V hV → ∀ g : G, ¬ InCalO1 n D.M V₀ V g := by
    intro n hn g hg
    have hmem : CFSG.Quasithin.conjSubgroup V g ∈ calO n D.M V₀ V := ⟨g, rfl, hg.1⟩
    rw [h12 n hn] at hmem
    exact hmem
  have hkr : ∀ n, n < mBar D.M V₀ V hV → ((n : ℕ) : ℕ∞) < rMV D.M V := fun n hn =>
    lt_of_lt_of_le (by exact_mod_cast hn) h11.le
  have hrk : mBar D.M V₀ V hV ≤ rk ↥V := mBar_le_rk hV h.hyp125.pairFacts.le
  have hN0 : ¬ normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M :=
    not_normalizer_wClos_le_of_no_calO1 D hx h61 h127 h1114 h126 h.hyp125 hV₀
      (hkr _ (by omega)) (by omega) (hno _ (by omega))
  have hNi : ¬ normalizer (E3.wClos V i D.T : Set G) ≤ D.M :=
    not_normalizer_wClos_le_of_no_calO1 D hx h61 h127 h1114 h126 h.hyp125 hV₀
      (hkr _ hlt') hlt' (hno _ hlt')
  have hVT := TwelveTwentyTwo.le_T_of_hyp125 h.hyp125
  have hW0 : E3.wClos V 0 D.T ≠ ⊥ := E3.wClos_ne_bot hV hVT (by omega)
  have hW02 : IsPGroup 2 (E3.wClos V 0 D.T) :=
    (TwelveTwentyTwo.isPGroup_T D).to_le (E3.wClos_le 0 D.T)
  have hex : ∃ H ∈ Δ, ¬ H ≤ normalizer (E3.wClos V 0 D.T : Set G) := by
    by_contra hc
    push Not at hc
    exact hN0 (uc22p22p_le_of_uniqueMax hΔU ⟨E3.wClos V 0 D.T, hW0, hW02, rfl⟩
      (iSup₂_le fun H hH => hc H hH))
  obtain ⟨H, hH, hHN⟩ := hex
  have hTH : IsSylowIn 2 D.T H := TwelveShort.isSylowIn_of_le D (hΔ H hH).1
  have h3 := TwelveEighteen.twelve_eighteen_three_of_no_calO1 hHs hV₀ (i := 0) (n := i)
    (k := i) (by omega) (hkr i (by omega)) (by omega) (hno i (by omega)) hTH (hF H hH)
  have hC := h3.resolve_left hHN
  rw [Subgroup.commutator_comm] at hC
  have hR : CFSG.Quasithin.twoResidual H ≤ centralizer (E3.cClos V i D.T : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hC
  obtain ⟨g, hgN, hgM⟩ := SetLike.not_le_iff_exists.1 hNi
  apply hO2 H hH g hgM
  rw [oUpperTwo_eq_twoResidual]
  exact TwelveTwentyTwo.le_conjSubgroup_of_le_centralizer_cClos h.hyp125 hV₀ (by omega) hR hgN

theorem r18_7b_of_delta' (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) (hSg : UC6S846.SigmaStd D)
    {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hV₀ : V₀ ≠ ⊥)
    (hX1 : barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) ≠ ⊥)
    {Δ : Set (Subgroup G)} (hΔ : ∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M)
    (hΔU : UniqueMax D.M (⨆ H ∈ Δ, H)) (hΔp : ∀ H ∈ Δ, p ∣ Nat.card H)
    (hΔn : fIndexMax Δ ≤ (S17.nOf L : ℕ∞)) : R18_7bAt D V₀ V p L h := by
  intro hgt
  have hk2 : D.k ≤ 2 := TwelveSeven.k_le_two D
  have hlt := (h.hyp125.mBarGT_iff_lt_mBar _).1 hgt
  have hmgt : MBarGT D.M V₀ V
      (bBar (UC22.conjClosure D.M L) D.M V₀ V h.hyp125.isElemAbelian + 1) :=
    (h.hyp125.mBarGT_iff_lt_mBar _).2 (by omega)
  have hle := eighteen_one_four_max D hx h61 h127 h1114 h162 hTor h1482 h126 h hV₀
    (Or.inl hmgt) hX1 hΔ hΔU
    (fun H hH => oUpperTwo_not_le_conj_of_p_dvd h hSg (hΔ H hH).2 (hΔp H hH))
  have hle' : (mBar D.M V₀ V h.hyp125.isElemAbelian : ℕ∞) ≤ ((S17.nOf L + D.k : ℕ) : ℕ∞) := by
    push_cast
    exact hle.trans (add_le_add_left hΔn _)
  have hle'' : mBar D.M V₀ V h.hyp125.isElemAbelian ≤ S17.nOf L + D.k := by exact_mod_cast hle'
  omega

theorem r18_7b_of_ne_bot_XT (h : Hyp18 D V₀ V p L) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) (hSg : UC6S846.SigmaStd D)
    (hV₀ : V₀ ≠ ⊥) (hX1 : barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) ≠ ⊥)
    (h17_66_1 : S17.R17_66_1At D V₀ V)
    (h18_4 : R18_4At D V₀ V p L)
    (hF : CFSG.LocalAnalysis.WeakClosure81.InFSq (S17.nOf L) (UC22.conjClosure D.M L ⊔ D.T)) :
    R18_7bAt D V₀ V p L h := by
  have hUL : UniqueMax D.M L := by
    rcases h17_66_1 p h.hp L h.hL (UC22.conjClosure D.M L) rfl h.hX with hh | hh
    · exact hh
    · exact absurd hh h18_4
  have hXM : UC22.conjClosure D.M L ⊔ D.T ≤ D.M := sup_le h.X_le_M D.sylowM.le
  have hU : UniqueMax D.M (⨆ H ∈ ({UC22.conjClosure D.M L ⊔ D.T} : Set (Subgroup G)), H) := by
    rw [iSup_singleton]
    exact uc22p22u_uniqueMax_mono D (h.L_le_X.trans le_sup_left) hXM hUL
  exact r18_7b_of_delta' D hx h61 h127 h1114 h162 hTor h1482 h126 hSg h hV₀ hX1
    (Δ := {UC22.conjClosure D.M L ⊔ D.T})
    (fun H hH => by rw [Set.mem_singleton_iff.1 hH]; exact ⟨le_sup_right, hXM⟩)
    hU
    (fun H hH => by
      rw [Set.mem_singleton_iff.1 hH]
      exact h.p_dvd_card_L.trans (Subgroup.card_dvd_of_le (h.L_le_X.trans le_sup_left)))
    (fIndexMax_le_iff.2 fun H hH => by rw [Set.mem_singleton_iff.1 hH]; exact hF)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
