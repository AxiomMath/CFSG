module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251i
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3L3
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddDefs
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251j
import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rs
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ui
import CFSG.LocalAnalysis.UniquenessCase.UC22P22xd
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Opp
import CFSG.Mathlib.Arithmetic.TwoPowSubOnePrimes
import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Alt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9 (R920odd)

variable {G : Type} [Group G] [Finite G]

theorem uc22p2251p_exists_A (D : Data G) (Ch : Choice2011 G) (hH : H1930 D) (c : Ctx21 D Ch)
    (hSg : UC6S846.SigmaStd D) (hn : 3 ≤ c.n) (h2112 : S21_12 D Ch) {K : Subgroup G}
    (hK : K ∈ calC D.M) (hbs : BadShape22 (Bar2 K)) :
    ∃ A : Subgroup G, A ≤ c.B0 ∧ (Nat.card A).Prime ∧ Nat.card A ≠ 2 ∧ Nat.card A ≠ 3 ∧
      Nat.card A ∉ D.sig ∧ ¬ normalizer (A : Set G) ≤ D.M ∧ normalizer (A : Set G) ≠ ⊤ ∧
      ⁅A, K⁆ ≤ pCoreOf 2 K := by
  let c' : Ctx21 D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  obtain ⟨r, hr, hr2, hr3, hrn⟩ := CFSG.exists_prime_ne_two_ne_three_dvd_two_pow_sub_one hn
  have hrB : r ∣ Nat.card c.B0 := by
    have h' : r ∈ etaSet c.n := ⟨hr, hrn⟩
    rw [← c.hpi] at h'
    exact h'.2
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B0) r hrB
  have hxo : orderOf (x : G) = r := by rw [orderOf_coe, hx]
  have hAB : zpowers (x : G) ≤ c.B0 := zpowers_le.2 x.2
  have hAcard : Nat.card (zpowers (x : G)) = r := by rw [Nat.card_zpowers, hxo]
  have hAN := s21_2 D Ch hH c' _ hAB
  refine ⟨zpowers (x : G), hAB, hAcard ▸ hr, hAcard ▸ hr2, hAcard ▸ hr3, ?_, hAN, ?_, ?_⟩
  · rw [hAcard]
    intro hrσ
    have hne : zpowers (x : G) ≠ ⊥ := by
      intro h
      rw [h, card_bot] at hAcard
      exact hr.one_lt.ne hAcard
    exact hAN (normalizer_le_of_mem_uniqueSet D.maxLocal (uc22p22r_mem_uniqueSet_of_sp D hr
      (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hK) hrσ) (hAB.trans c.hBM)
      (IsPGroup.of_card (n := 1) (by rw [hAcard, pow_one])) hne))
  · intro htop
    have := D.standing.simple
    rcases (normalizer_eq_top_iff.1 htop).eq_bot_or_eq_top with h | h
    · rw [h, card_bot] at hAcard
      exact hr.one_lt.ne hAcard
    · exact CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab D.maxLocal.1
        (eq_top_iff.2 (by rw [← h]; exact hAB.trans c.hBM))
  · obtain ⟨p, hp, hp2, hch⟩ := P2251h.exists_isChev hK hbs
    have hc := (h2112 hH c' K hK p hp hp2 hch).2
    have hle : zpowers (x : G) ≤ CFSG.Quasithin.opResidual 3 c.B0 :=
      zpowers_le.2 (CFSG.Quasithin.mem_opResidual_of_coprime x.2
        (by rw [hxo]; exact (Nat.coprime_primes hr Nat.prime_three).2 hr3))
    exact (commutator_mono hle le_rfl).trans hc

theorem uc22p2251p_false_of_isL3U (D : Data G) (h847 : R847E3L3 D) (h920 : R920odd D)
    {K Y H : Subgroup G} (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal)
    (hU : ∀ X : Subgroup G, X ≤ K → Nat.card X = 3 → X ∈ uniqueSet D.M)
    (hL3 : IsL3 (Bar2 K) 1) (hYK : Y ≤ K) (hcov : K = Y ⊔ pCoreOf 2 K)
    (hY : Nonempty (Bar2 Y ≃* Bar2 K)) (hYH : Y ≤ H) (hHT : H ≠ ⊤) (hHM : ¬ H ≤ D.M) :
    False := by
  have hKM : K ≤ D.M := hK.1.le
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 K
  have hP3 := PartTwo.card_sylow_three_of_isL3_bar2 hL3 hP
  have hKY : K ⊓ Y = Y := inf_eq_right.2 hYK
  have hyp : PartTwo.Hyp919c D K P Y H := by
    refine ⟨hK, hP.le, hP3, hU P hP.le hP3, hYK.trans hKM, ?_, ?_, ⟨0, ?_⟩, hHT, hYH, hHM⟩
    · rw [hKY]
      exact hcov
    · rw [hKY, subgroupOf_self]
      infer_instance
    · rw [hKY, subgroupOf_self, index_top, pow_zero]
  obtain ⟨eY⟩ := hY
  have hL27 : IsL2Odd (Bar2 Y) 7 :=
    CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism (Bar2 Y)
      (CFSG.Blueprint.LieModel.of_mulEquiv eY.symm hL3)
  obtain ⟨A', hA'Y, hA'p, hA'o, hA'N⟩ :=
    h920 K P Y H hyp hYK 7 (by norm_num) (by norm_num) hL27
  have hq2 : Nat.card A' ≠ 2 := by
    intro h
    have h1 := Nat.odd_iff.1 hA'o
    omega
  exact hA'N (h847 K hK hKn hL3 A' (hA'Y.trans hYK) hA'p hq2)

theorem uc22p2251p_uniqueMaxU (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch)
    (hH : H1930 D) (c : Ctx21 D Ch) {K : Subgroup G} (hKM : K ≤ D.M)
    (hKN : D.M ≤ normalizer (K : Set G)) (e : Bar2 K ≃* alternatingGroup (Fin 5))
    (hU : ∀ X : Subgroup G, X ≤ K → Nat.card X = 3 → X ∈ uniqueSet D.M) :
    UniqueMax D.M (K ⊔ D.T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨X, hXB, hX3, hXS, hsup⟩ := CFSG.Quasithin.FA5.exists_cartan_three (L := K) (S := D.T)
    (CFSG.ABGLocalTools.isSylowOf_iff.1 (D.sylowM.inf_of_le_normalizer hKM hKN)) e
  have hBK := CFSG.Quasithin.F1.borelOf_le K D.T
  have hBN := CFSG.Quasithin.F1.borelOf_le_normalizer K D.T
  have hSB := CFSG.Quasithin.F1.sylow_le_borelOf K D.T
  have hTB := CFSG.Quasithin.F1.le_normalizer_borelOf (D.sylowM.le.trans hKN)
  generalize CFSG.Quasithin.borelOf K D.T = B at hXB hsup hBK hBN hSB hTB
  have hcardB : Nat.card B = Nat.card ↥(D.T ⊓ K) * 3 := by
    rw [← hsup, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer (D.T ⊓ K) X
      (hXB.trans hBN) (disjoint_iff.2 (by rw [inf_comm]; exact hXS)), hX3]
  have hBT : B ⊓ D.T = D.T ⊓ K :=
    le_antisymm (le_inf inf_le_right (inf_le_left.trans hBK)) (le_inf hSB inf_le_left)
  have h1 := relIndex_mul_card B D.T
  have h2 := relIndex_mul_card B (D.T ⊔ B)
  rw [hBT] at h1
  rw [inf_eq_left.2 (le_sup_right : B ≤ D.T ⊔ B),
    CFSG.Quasithin.F1.relIndex_sup_eq_of_le_normalizer hTB, hcardB] at h2
  have hXT : X ⊔ D.T = D.T ⊔ B :=
    le_antisymm (sup_le (hXB.trans le_sup_right) le_sup_left)
      (sup_le le_sup_right
        (hsup.symm.le.trans (sup_le (inf_le_left.trans le_sup_right) le_sup_left)))
  obtain ⟨a, ha⟩ := D.sylowM.isPGroup.exists_card_eq
  have hcard : Nat.card ↥(X ⊔ D.T) = 2 ^ a * 3 := by
    rw [hXT, ← h2, ← ha, ← h1]
    ring
  have hXK : X ≤ K := hXB.trans hBK
  exact uc22p22u_uniqueMax_mono D (sup_le_sup_right hXK D.T) (sup_le hKM D.sylowM.le)
    (P2251j.calMOf_eq_of_card D Ch h211 hH c Nat.prime_three (by norm_num) hX3 hcard
      (hU X hXK hX3))

theorem uc22p2251p_sylow_mem {M K : Subgroup G} (hKM : K ≤ M) (h3 : 3 ∣ Nat.card K)
    (hU : ∀ X : Subgroup G, X ≤ K → Nat.card X = 3 → X ∈ uniqueSet M) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P K) : P ∈ uniqueSet M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf := Nat.Prime.factorization_pos_of_dvd Nat.prime_three (Nat.card_pos (α := ↥K)).ne' h3
  have h3P : 3 ∣ Nat.card P := by
    rw [hP.card_eq]
    exact dvd_pow_self 3 hf.ne'
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 3 h3P
  have hxP : zpowers (x : G) ≤ P := zpowers_le.2 x.2
  exact mem_uniqueSet_of_le
    (hU _ (hxP.trans hP.le) (by rw [Nat.card_zpowers, orderOf_coe, hx])) hxP (hP.le.trans hKM)

theorem uc22p2251p_false_of_isA5U (D : Data G) (Ch : Choice2011 G) (h33 : S22_3_3 D Ch)
    (h211 : S21_1 D Ch) (h923 : F09.R923 D) (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ}
    {Nb : Fin m → Subgroup (MBar D.M D.U)} (hNb : NbarSplit D Nb) {i : Fin m}
    (hi : IsL2Ev ↥(Nb i) 2 ∨ IsS5 ↥(Nb i)) {K A : Subgroup G} (hK : K ∈ calC D.M)
    (hKb : mbarImage D.M D.U K = ⁅Nb i, Nb i⁆) (hKN : D.M ≤ normalizer (K : Set G))
    (e5 : Bar2 K ≃* alternatingGroup (Fin 5))
    (hU : ∀ X : Subgroup G, X ≤ K → Nat.card X = 3 → X ∈ uniqueSet D.M) (hAM : A ≤ D.M)
    (hA : (Nat.card A).Prime) (hA7 : 7 ≤ Nat.card A) (hc : ⁅A, K⁆ ≤ pCoreOf 2 K)
    (hcov : K = Opp 3 (K ⊓ centralizer (A : Set G)) ⊔ pCoreOf 2 K)
    (hAN : ¬ normalizer (A : Set G) ≤ D.M) (hAT : normalizer (A : Set G) ≠ ⊤) : False := by
  have hKM : K ≤ D.M := hK.1.le
  have h3 : 3 ∣ Nat.card K := by
    have h60 : Nat.card (Bar2 K) = 60 :=
      (Nat.card_congr e5.toEquiv).trans CFSG.QuasithinUnique.A5.Delta5.a5_card
    exact (show 3 ∣ Nat.card (Bar2 K) by rw [h60]; norm_num).trans (card_quotient_dvd_card _)
  have hX := PartTwo.close16_opp_le 3 (K ⊓ centralizer (A : Set G))
  have hN := h923 K hK hKM hKN ⟨e5⟩ (uc22p2251p_uniqueMaxU D Ch h211 hH c.toCtx21 hKM hKN e5 hU)
    (fun P hP => uc22p2251p_sylow_mem hKM h3 hU hP) (Opp 3 (K ⊓ centralizer (A : Set G)))
    (PartTwo.close16_opp_idem 3 _) (hX.trans inf_le_left) hcov
    (uc22p2251i_r923_hyp D Ch h33 hH c hNb hi hK hKb hKN hAM hA hA7 hc hcov)
  exact hAN (P2251j.le_of_calNOf hN
    (hX.trans (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))) hAT)

theorem uc22p2251p_exists_not_mem (D : Data G) (Ch : Choice2011 G) (h33 : S22_3_3 D Ch)
    (h211 : S21_1 D Ch) (h2112 : S21_12 D Ch) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n)
    (hSg : UC6S846.SigmaStd D) (h847 : R847E3L3 D) (h920 : R920odd D) (h923 : F09.R923 D)
    (hnsp : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M) (hH : H1930 D)
    (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)} (hNb : NbarSplit D Nb)
    {i : Fin m} (hbad : ¬ ∃ n : ℕ, IsL2Ev ↥(Nb i) n ∧ n ≠ 2)
    (hσ : ∀ p ∈ D.sig, p ∣ Nat.card ↥(Nb i)) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hKb : mbarImage D.M D.U K = ⁅Nb i, Nb i⁆) (hKe : Nonempty (Bar2 K ≃* ↥⁅Nb i, Nb i⁆))
    (hbs : BadShape22 (Bar2 K)) (hKn : (K.subgroupOf D.M).Normal) :
    ∃ X : Subgroup G, X ≤ K ∧ Nat.card X = 3 ∧ X ∉ uniqueSet D.M := by
  by_contra hne
  have hU : ∀ X : Subgroup G, X ≤ K → Nat.card X = 3 → X ∈ uniqueSet D.M :=
    fun X hXK hX => Classical.byContradiction fun hXU => hne ⟨X, hXK, hX, hXU⟩
  have hKM : K ≤ D.M := hK.1.le
  have hKN : D.M ≤ normalizer (K : Set G) := (normal_subgroupOf_iff_le_normalizer hKM).1 hKn
  obtain ⟨A, hAB, hA, hA2, hA3, hAσ, hAN, hAT, hc⟩ :=
    uc22p2251p_exists_A D Ch hH c.toCtx21 hSg (hn3 hH _) h2112 hK hbs
  have hAM : A ≤ D.M := hAB.trans c.hBM
  obtain ⟨-, hcov1, hY, hcov⟩ := uc22p2251h_cover hKM hKn hAM hA hA2 hc hbs.layerShape
  have hYN : K ⊓ centralizer (A : Set G) ≤ normalizer (A : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  rcases hbs with h2 | h3
  · obtain ⟨e5⟩ := BadShape22.nonempty_mulEquiv_alt_five_of_isL2Ev_two h2
    obtain ⟨eK⟩ := hKe
    have h60 : Nat.card (Bar2 K) = 60 :=
      (Nat.card_congr e5.toEquiv).trans CFSG.QuasithinUnique.A5.Delta5.a5_card
    have hi : IsL2Ev ↥(Nb i) 2 ∨ IsS5 ↥(Nb i) := by
      rcases hNb.2 i with ⟨n, hn⟩ | h | h
      · obtain rfl : n = 2 := by
          by_contra hne
          exact hbad ⟨n, hn, hne⟩
        exact Or.inl hn
      · rw [Nat.card_congr eK.toEquiv, LayerShape22.commutator_eq_self (Y := Nb i) (Or.inr h),
          PartTwo.card_eq_of_isL3 h] at h60
        exfalso
        omega
      · exact Or.inr h
    have hNi : Nat.card ↥(Nb i) ∣ 2 ^ 3 * (3 * 5) := by
      rcases hi with h | h
      · rw [P22x.card_of_isL2Ev h]
        norm_num
      · obtain ⟨e⟩ := h
        rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
        decide
    have h5 : 5 ∈ D.sig := by
      obtain ⟨p, hp⟩ := hSg.nonempty
      obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
      have hp3 : p ≠ 3 := by
        rintro rfl
        exact hnsp (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hK) hp)
      have hd := (hσ p hp).trans hNi
      rcases (Nat.Prime.dvd_mul hpp).1 hd with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow h)) hp2
      · rcases (Nat.Prime.dvd_mul hpp).1 h with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1 h) hp3
        · rwa [← (Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).1 h]
    have hA7 : 7 ≤ Nat.card A := by
      have hA5 : Nat.card A ≠ 5 := fun h => hAσ (h ▸ h5)
      have h2le := hA.two_le
      by_contra hlt
      generalize Nat.card A = r at hA hA2 hA3 hA5 h2le hlt
      interval_cases r <;> first | omega | norm_num at hA
    exact uc22p2251p_false_of_isA5U D Ch h33 h211 h923 hH c hNb hi hK hKb hKN e5 hU hAM hA hA7 hc
      hcov hAN hAT
  · exact uc22p2251p_false_of_isL3U D h847 h920 hK hKn hU h3 inf_le_left hcov1 hY hYN hAT hAN

theorem uc22p2251p_isL2Ev_one (D : Data G) (Ch : Choice2011 G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h33 : S22_3_3 D Ch) (h119 : R119W D) (h17 : S21_17 D Ch)
    (h211 : S21_1 D Ch) (h2112 : S21_12 D Ch) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n)
    (hSg : UC6S846.SigmaStd D) (h847 : R847E3L3 D) (h920 : R920odd D) (h923 : F09.R923 D)
    (h8107 : F08.R8107 D) (hnsp : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) {i : Fin m} (hbad : ¬ ∃ n : ℕ, IsL2Ev ↥(Nb i) n ∧ n ≠ 2)
    (hσ : ∀ p ∈ D.sig, p ∣ Nat.card ↥(Nb i)) : ∀ j, j ≠ i → IsL2Ev ↥(Nb j) 1 := by
  intro j hji
  by_contra hj
  obtain ⟨K, hK, hKb, hKe, hKs, hKn⟩ :=
    uc22p2251b_exists_bad D hx h61 h119 h17 hH c.toCtx22 hNb hbad
  obtain ⟨L, hL, hLb, -, hLs⟩ := uc22p2251b_exists_lift_nb D hx h61 h119 c.toCtx22 hNb j hj
  have hKL : K ≠ L :=
    uc22p2251b_ne D hNb (Ne.symm hji) (P2251b.not_isL2Ev_one_of_bad hbad) hKb hLb
  obtain ⟨X, hXK, hX, hXU⟩ := uc22p2251p_exists_not_mem D Ch h33 h211 h2112 hn3 hSg h847 h920
    h923 hnsp hH c hNb hbad hσ hK hKb hKe hKs hKn
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3
    (hLs.three_dvd_card.trans (card_quotient_dvd_card _))
  have hYL : zpowers (y : G) ≤ L := zpowers_le.2 y.2
  have hY : Nat.card (zpowers (y : G)) = 3 := by rw [Nat.card_zpowers, orderOf_coe, hy]
  have hr : ∀ {Q E : Subgroup G}, LayerShape22 (Bar2 Q) → E ≤ Q → Nat.card E = 3 →
      CFSG.Open.pRank 3 Q = 1 := fun hQs hEQ hE =>
    le_antisymm (uc22p2251b_thin8 hQs 3 Nat.prime_three (by norm_num))
      (CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hEQ
        (CFSG.GroupTheory.isElemAbelian_of_card_prime hE) (by rw [hE, pow_one]))
  exact hXU (h8107 K hK L hL hKL (hr hKs.layerShape hXK hX) (hr hLs hYL hY)
    (Or.inl (uc22p2251b_thin8 hKs.layerShape)) (Or.inl (uc22p2251b_thin8 hLs)) X _ hXK hX hYL
    hY).1

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
