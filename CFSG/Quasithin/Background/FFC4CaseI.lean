module

public import CFSG.Quasithin.Background.FFC4Coh
public import CFSG.Quasithin.Background.FFC4Six
public import CFSG.Quasithin.Background.FFC4Main

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Assembly.LowTwoRank CFSG.Open Equiv Equiv.Perm

section E9

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {U Z : Subgroup W}

theorem false_of_sp4 (hno : ¬ ThreeRank2 ↥L) {n : ℕ} (h : BinaryNaturalSp4 L U Z n) : False := by
  obtain ⟨K, hK, hf, hc, π, hπ⟩ := h
  exact hno (threeRank2_of_realizes (FFModel.nat_faithful _) hπ threeRank2_statedSp)

theorem false_of_alt_ge_six (hno : ¬ ThreeRank2 ↥L) {n : ℕ} (hn : 6 ≤ n)
    (h : AlternatingNatural L U Z n) : False := by
  obtain ⟨π, hπ⟩ := h
  exact hno (threeRank2_of_realizes (altDn_faithful (by omega)) hπ (threeRank2_alt hn))

theorem false_of_g2 (hI : B58Inputs) (hno : ¬ ThreeRank2 ↥L) {n : ℕ} (h : G2Natural L U Z n) :
    False := by
  obtain ⟨K, hK, hf, hc, π, hπ⟩ := h
  have := charP_two_of_card_pow hc
  exact hno (threeRank2_of_realizes (zornQ_faithful _ le_rfl) hπ (hI.g2 K ‹_›))

theorem false_of_g2d (hI : B58Inputs) (hno : ¬ ThreeRank2 ↥L) (h : G2NaturalDerived L U Z 1) :
    False := by
  obtain ⟨K, hK, hf, hc, π, hπ⟩ := h
  have hc' : Nat.card K = 2 ^ 1 := hc
  have := charP_two_of_card_pow hc'
  exact hno (threeRank2_of_realizes (zornQ_faithful _ (commutator_le_self_aux _)) hπ
    (hI.g2d K (by simpa using hc')))

end E9

section S5

variable {W : Type} [CommGroup W] [Finite W]

theorem Z_eq_bot_of_s5 (hI : B58Inputs) {H L : Subgroup (MulAut W)} (hLH : L ≤ H)
    (hno : ¬ ThreeRank2 ↥H) {π : Perm (Fin 5) →* ↥H}
    (hπ : (FFModel.symDn 5).RealizesVia H (commV L) (fixV L ⊓ commV L) π) (hP2 : B51Part2 L) :
    fixV L ⊓ commV L = ⊥ := by
  by_contra hZ
  have hnot : ¬ IsIntDirect (commV L) (fixV L) ⊤ := fun h => hZ (by rw [inf_comm]; exact h.2)
  have hL3 : ¬ ThreeRank2 ↥L := fun h => hno (h.of_le hLH)
  rcases (hP2.2 hnot).2 with ⟨n, hn⟩ | ⟨n, hn⟩ | ⟨n, hn⟩ | h6 | h8 | hg2d | h3
  · obtain ⟨K, hK, hf, hc, ρ, hρ⟩ := hn
    have := charP_two_of_card_pow hc
    exact false_of_sl2_sym5 hLH hρ hπ
  · exact false_of_sp4 hL3 hn
  · exact false_of_g2 hI hL3 hn
  · exact false_of_alt_ge_six hL3 (by norm_num) h6
  · exact false_of_alt_ge_six hL3 (by norm_num) h8
  · exact false_of_g2d hI hL3 hg2d
  · obtain ⟨K, hK, hf, hc, ρ, hρ⟩ := h3
    exact false_of_sl3_sym5 (by simpa using hc) hρ hπ

end S5

section CaseI

variable {W : Type} [CommGroup W] [Finite W]

theorem good_of_case_i
    (hI : B58Inputs) {H L : Subgroup (MulAut W)} (hJ : H = ffJ H) (hne : H ≠ ⊥)
    (hno : ¬ ThreeRank2 ↥H) (hLH : L ≤ H) (P2 : B51Part2 L) (P5 : B51Part5 H L)
    (hi : B51Case1i H L) : GoodFactor H := by
  obtain ⟨hirr, hpair, hT⟩ := hi
  obtain ⟨T, hTsyl⟩ := CFSG.QuasithinUnique.exists_isSylowTwoOf H
  rcases hT T hTsyl with hHL | ⟨hHLT, hn⟩
  · subst hHL
    by_cases hα : commV H ⊔ fixV H = ⊤
    · rcases pairOK_of_pair hI hno hpair with hnat | hnat | h5
      · exact good_of_natural_alpha hα (inf_comm _ _) rfl (Or.inl hnat)
      · exact good_of_natural_alpha hα (inf_comm _ _) rfl (Or.inr hnat)
      · exact (false_of_alt5 hJ hne hα (inf_comm _ _) h5).elim
    · obtain ⟨hirr', hlist5, hZ3⟩ := P5.resolve_left hα
      rcases hlist5 with ⟨n, hn⟩ | h6 | h8 | h3
      · exact (false_of_sp4 hno hn).elim
      · exact (false_of_alt_ge_six hno (by norm_num) h6).elim
      · exact (false_of_alt_ge_six hno (by norm_num) h8).elim
      · exact good_of_beta hα hirr' h3 (hZ3 h3)
  · have hL3 : ¬ ThreeRank2 ↥L := fun h => hno (h.of_le hLH)
    rcases hn with ⟨n, hn5, hn8, hsym⟩ | hg2
    · obtain ⟨π, hπ⟩ : ∃ π : Perm (Fin n) →* ↥H,
          (FFModel.symDn n).RealizesVia H (commV L) (fixV L ⊓ commV L) π := hsym
      by_cases hn : n = 5
      · subst hn
        have hπinj : Function.Injective π :=
          injective_of_faithful_sec (symDn_faithful (by norm_num)) hπ
        by_cases hα : commV L ⊔ fixV H = ⊤
        · have hZ : fixV L ⊓ commV L = ⊥ := Z_eq_bot_of_s5 hI hLH hno hπ P2
          have hCinv : ∀ g : ↥H, ∀ c ∈ fixV H, (g : MulAut W) c ∈ fixV H := fun g c hc => by
            rw [hc g g.2]; exact hc
          have h1 : commV L ⊓ fixV H ≤ fixV L ⊓ commV L := fun x hx =>
            ⟨B1.fixV_le_fixV hLH hx.2, hx.1⟩
          have hUZ : commV L ⊓ fixV H = fixV L ⊓ commV L :=
            le_antisymm h1 (by rw [hZ]; exact bot_le)
          have hext := RealizesVia.extend hπ hCinv hUZ
          rw [hα] at hext
          have hcomm : commV L ≤ commV H := by
            unfold commV
            exact Subgroup.closure_mono fun w ⟨x, hx, v, hxv⟩ => ⟨x, hLH hx, v, hxv⟩
          have hT' : (⊤ : Subgroup W) = commV H ⊔ fixV H :=
            le_antisymm (by rw [← hα]; exact sup_le_sup_right hcomm _) le_top
          have hbij : Function.Bijective π := ⟨hπinj, hπ.1⟩
          have hF : B56FactorList ↥H := Or.inr (Or.inl ⟨(MulEquiv.ofBijective π hbij).symm⟩)
          have hS : SymmetricNatural H ⊤ (fixV H) 5 := ⟨π, hext⟩
          have hP : B56Piece H ⊤ (fixV H) := Or.inl ⟨hT', Or.inr (Or.inl hS)⟩
          exact ⟨hF, hP⟩
        · obtain ⟨hirr', hlist5, hZ3⟩ := P5.resolve_left hα
          rcases hlist5 with ⟨m, hm⟩ | h6 | h8 | h3
          · exact (false_of_sp4 hL3 hm).elim
          · exact (false_of_alt_ge_six hL3 (by norm_num) h6).elim
          · exact (false_of_alt_ge_six hL3 (by norm_num) h8).elim
          · obtain ⟨K, hK, hf, hc, ρ, hρ⟩ := h3
            exact (false_of_sl3_sym5 (by simpa using hc) hρ hπ).elim
      · exact (hno (threeRank2_of_realizes (symDn_faithful (by omega)) hπ
          (threeRank2_perm (by omega)))).elim
    · exact (false_of_g2 hI hno hg2).elim

theorem good_of_case1_aux
    (hI : B58Inputs) {H L : Subgroup (MulAut W)} (hJ : H = ffJ H) (hne : H ≠ ⊥)
    (hno : ¬ ThreeRank2 ↥H) (hLH : L ≤ H) (P1 : B51Part1 H L) (P2 : B51Part2 L)
    (P5 : B51Part5 H L) : GoodFactor H := by
  obtain ⟨-, hcases⟩ := P1
  rcases hcases with hi | hii | ⟨n, hiii⟩ | hiv
  · exact good_of_case_i hI hJ hne hno hLH P2 P5 hi
  · have hHL : H = L := hii.1
    subst hHL
    exact good_of_case_ii hno (P5.imp_right (·.1)) hii
  · exact (false_of_case_iii hLH hno hiii.2).elim
  · exact (false_of_case_iv hLH hno hiv.2).elim

theorem good_of_case1 (hI : B58Inputs) : B58Case1Good := by
  intro W _ _ _ H hH hne hno h1
  obtain ⟨-, hB51, -⟩ := h1
  exact good_of_case1_aux hI hH.2.1 hne hno (quasithinGenFitting_le H) hB51.1 hB51.2.1
    hB51.2.2.2.2.1

theorem asB58_of_inputs
    (hI : B58Inputs) : AsB58 := asB58_of_case1 (good_of_case1 hI)

end CaseI

end FFC

end CFSG.Quasithin
