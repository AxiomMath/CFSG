module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35Inner
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Odd
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Fun
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Hall
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Inn
import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
import CFSG.LocalAnalysis.UniquenessCase.UC22P22i
import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
import CFSG.LocalAnalysis.UniquenessCase.UC22P20zbb
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
import CFSG.Adapters.LieModelOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLie (IsSmallThreeTag)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem kq35NormSylowAlpha_of_normSylow (h : KQ35NormSylow) : KQ35NormSylowAlpha := by
  intro X _ _ _ t n p hp35 hadm ht hX P x hx s m hs hs7 _ _ hxs
  have h3 := h X t n p hp35 hadm ht hX P x hx (by rw [hxs]; exact hs.odd_of_ne_two (by omega))
  rw [hxs] at h3
  have := Nat.le_of_dvd (by norm_num) h3
  omega

theorem uc22s2112r34q35_exists_mem_orderOf_alpha {D : Data G} {Ch : Choice2011 G}
    (c : Ctx21 D Ch) {e m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) (hn : c.n = 2 ^ e * m) :
    ∃ b ∈ c.B0, b ∈ normalizer (D.T : Set G) ∧
      ∃ s : ℕ, s.Prime ∧ 7 ≤ s ∧ s ∣ 2 ^ m - 1 ∧ orderOf b = s := by
  obtain ⟨s, hs, hs7, hsd⟩ := uc22s2112r34_exists_prime_seven_le hm3 fun h => by
    subst h
    exact absurd hm (by decide)
  have hmn : 2 ^ m - 1 ∣ 2 ^ c.n - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow (2 ^ m) 1 (2 ^ e)
    rwa [one_pow, ← pow_mul, mul_comm m, ← hn] at h
  have hsB : s ∈ piSet c.B0 := by
    rw [c.hpi]
    exact ⟨hs, hsd.trans hmn⟩
  obtain ⟨b, hbB, hbs⟩ := uc22p22i_exists_elt_of_mem_piSet hsB
  have hbα : b ∈ oPi {q | q.Prime ∧ q ∣ 2 ^ m - 1} c.B0 :=
    uc22pwtb_mem_oPi c.hB0.2.1 hbB fun q hq hqd => by
      rw [hbs] at hqd
      obtain rfl := (Nat.prime_dvd_prime_iff_eq hq hs).1 hqd
      exact ⟨hq, hsd⟩
  exact ⟨b, hbB, c.hα e m hm hn hbα, s, hs, hs7, hsd, hbs⟩

theorem uc22s2112r34q35_false_alpha (hKF1 : KFieldAutOdd) (hNS : KQ35NormSylowAlpha) {D : Data G}
    {Ch : Choice2011 G} (c : Ctx21 D Ch) {e m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m)
    (hn : c.n = 2 ^ e * m) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hBN : c.B0 ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    {t : StatedLieTag} {n p : ℕ} (hp35 : p = 3 ∨ p = 5) (hadm : StatedLieAdmissible t n p 1)
    (ht : FunTwoType t n) (hX : LieModel (BarInf L) t n p 1) : False := by
  have : IsSimpleGroup (BarInf L) := (uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)).1
  obtain ⟨hA1, -, hRee⟩ := uc22s2112r34_funTwoType_ne ht
  have hp : p.Prime := hadm.1
  have hp2 : p ≠ 2 := by rcases hp35 with rfl | rfl <;> norm_num
  obtain ⟨b, hbB, hbT, s, hs, hs7, hsd, hbs⟩ :=
    uc22s2112r34q35_exists_mem_orderOf_alpha c hm hm3 hn
  obtain ⟨x, hx, hxs⟩ := uc22s2112r34q35_exists_conj hKF1 hL hp hp2 hadm hX hA1 hRee hfaith hbB
    (hBN hbB) hs (by omega) hbs (uc22s2112r34_not_dvd_genericOrders (Or.inl ht) hs hs7)
  obtain ⟨P, hP⟩ := uc22s2112r34_exists_sylow_barInf hL
  have hxP : x ∈ normalizer ((P : Subgroup (BarInf L)) : Set (BarInf L)) := by
    rw [hP]
    exact uc22s2112r34_mem_normalizer_map (hBN hbB) hbT hx
  exact hNS (BarInf L) t n p hp35 hadm ht hX P x hxP s m hs hs7 hm hsd hxs

section Orders


theorem uc22s2112r34q35_not_dvd_card {X : Type} [Group X] {t : StatedLieTag} {n p : ℕ}
    (hp35 : p = 3 ∨ p = 5) (ht : FunTwoType t n) (hX : LieModel X t n p 1) :
    ¬ 17 ∣ Nat.card X := by
  cases t
  case G2 =>
    rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional
      (hX.chevalleyExceptionalModel (by decide))]
    rcases hp35 with rfl | rfl <;> decide
  case trialityD4 =>
    rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional
      (hX.chevalleyExceptionalModel (by decide))]
    rcases hp35 with rfl | rfl <;> decide
  case PSL =>
    rcases ht with rfl | rfl <;> rw [hX.card_eq_lieOrd (by norm_num)] <;>
      rcases hp35 with rfl | rfl <;> decide
  case PSU =>
    rcases ht with rfl | rfl <;> rw [hX.card_eq_lieOrd (by norm_num)] <;>
      rcases hp35 with rfl | rfl <;> decide
  case PSp =>
    obtain rfl : n = 2 := ht
    rw [hX.card_eq_lieOrd (by norm_num)]
    rcases hp35 with rfl | rfl <;> decide
  case POmegaOdd =>
    obtain rfl : n = 3 := ht
    rw [hX.card_eq_lieOrd (by norm_num)]
    rcases hp35 with rfl | rfl <;> decide
  case POmegaMinus =>
    obtain rfl : n = 4 := ht
    rw [hX.card_eq_lieOrd (by norm_num)]
    rcases hp35 with rfl | rfl <;> decide
  all_goals exact ht.elim

theorem uc22s2112r34q35_false_eight (hKF1 : KFieldAutOdd) {D : Data G} {Ch : Choice2011 G}
    (c : Ctx21 D Ch) (h8 : 8 ∣ c.n) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hBN : c.B0 ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    {t : StatedLieTag} {n p : ℕ} (hp35 : p = 3 ∨ p = 5) (hadm : StatedLieAdmissible t n p 1)
    (ht : FunTwoType t n) (hX : LieModel (BarInf L) t n p 1) : False := by
  obtain ⟨hA1, -, hRee⟩ := uc22s2112r34_funTwoType_ne ht
  have hp : p.Prime := hadm.1
  have hp2 : p ≠ 2 := by rcases hp35 with rfl | rfl <;> norm_num
  have h17 : (17 : ℕ).Prime := by norm_num
  have h17π : 17 ∈ piSet c.B0 := by
    rw [c.hpi]
    refine ⟨h17, ?_⟩
    obtain ⟨k, hk⟩ := h8
    have h := Nat.sub_dvd_pow_sub_pow (2 ^ 8) 1 k
    rw [one_pow, ← pow_mul, ← hk] at h
    exact (by norm_num : 17 ∣ 2 ^ 8 - 1).trans h
  obtain ⟨b, hbB, hb⟩ := uc22p22i_exists_elt_of_mem_piSet h17π
  obtain ⟨x, -, hx⟩ := uc22s2112r34q35_exists_conj hKF1 hL hp hp2 hadm hX hA1 hRee hfaith hbB
    (hBN hbB) h17 (by norm_num) hb
    (uc22s2112r34_not_dvd_genericOrders (Or.inl ht) h17 (by norm_num))
  exact uc22s2112r34q35_not_dvd_card hp35 ht hX (hx ▸ orderOf_dvd_natCard x)

end Orders

section Four


theorem uc22s2112r34q35_false_four (hKF1 : KFieldAutOdd) (hPF : KQ35PermFive) {D : Data G}
    {Ch : Choice2011 G} (hσ : UC6S846.SigmaStd D) (hH : H1930 D) (c : Ctx21 D Ch)
    (hn4 : c.n = 4) {L : Subgroup G} (hL : L ∈ calC D.M) (hBN : c.B0 ≤ normalizer (L : Set G))
    (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1) {t : StatedLieTag} {n p : ℕ}
    (hp35 : p = 3 ∨ p = 5) (hadm : StatedLieAdmissible t n p 1) (ht : FunTwoType t n)
    (hX : LieModel (BarInf L) t n p 1) : False := by
  have : IsSimpleGroup (BarInf L) := (uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)).1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : center (BarInf L) = ⊥ := center_barInf_eq_bot hL.2.2
  obtain ⟨hA1, hA3, hRee⟩ := uc22s2112r34_funTwoType_ne ht
  have hp : p.Prime := hadm.1
  have hp2 : p ≠ 2 := by rcases hp35 with rfl | rfl <;> norm_num
  have hπ : ∀ r : ℕ, r.Prime → r ∣ 15 → r ∈ piSet c.B0 := fun r hr hrd => by
    rw [c.hpi]
    exact ⟨hr, by rw [hn4]; exact hrd⟩
  have hrk : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L) → (t = .PSp ∧ n = 2) ∨ t = .G2 := by
    intro hpN
    obtain ⟨-, h4⟩ := uc22s2112r34_pRank_of_lieModel hp hp2 hX hA1 (fun h => hA3 ⟨h.1, h.2.1⟩)
      hRee hpN
    rcases h4 with ⟨h, -⟩ | h4
    · exact h
    · exact absurd (uc22s2112r34_sig_of_le_pRank hσ hL hp hp2 h4).1
        (uc22s2112r34_not_mem_sig hσ hH c hL
          (hπ p hp (by rcases hp35 with rfl | rfl <;> norm_num)))
  have hcase : (t = .G2 ∧ p = 3) ∨ ((t = .PSp ∧ n = 2 ∧ (p = 3 ∨ p = 5)) ∨
      (t = .PSU ∧ n = 4 ∧ p = 3) ∨ (t = .POmegaOdd ∧ n = 3 ∧ p = 3) ∨
      (t = .G2 ∧ n = 0 ∧ p = 5)) := by
    rcases hp35 with rfl | rfl
    · by_cases hsm : IsSmallThreeTag t n
      · rcases hsm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl ⟨rfl, rfl, Or.inl rfl⟩)
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
      · have hpN := not_dvd_card_solvableRadical hL.2.2 hp hp2
          (uc22s2112r34_not_dvd_center_char hL hp hp2 hRee hX (Or.inr ⟨rfl, rfl, hsm⟩))
        rcases hrk hpN with h | h
        · exact absurd (Or.inl h) hsm
        · exact absurd (Or.inr (Or.inr (Or.inl h))) hsm
    · have hpN := not_dvd_card_solvableRadical hL.2.2 hp hp2
        (uc22s2112r34_not_dvd_center_char hL hp hp2 hRee hX (Or.inl ⟨by norm_num, hA1⟩))
      rcases hrk hpN with ⟨rfl, rfl⟩ | rfl
      · exact Or.inr (Or.inl ⟨rfl, rfl, Or.inr rfl⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hadm.2.2.1, rfl⟩)))
  have hrg : ¬ 5 ∣ (genericOrders t n p 1).1 := by
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl | rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ <;> norm_num [genericOrders]
  have h5 : (5 : ℕ).Prime := by norm_num
  obtain ⟨R, hRB, hR5, h5R, -, hRT, hRr⟩ :=
    uc22s2112r34_exists_rSub_calB1 c.hB0 D.sylowM.isPGroup h5 (hπ 5 h5 (by norm_num)).2
  have hRN : R ≤ normalizer (L : Set G) := hRB.trans hBN
  obtain ⟨P, ψ, hψ, hperm⟩ := uc22s2112r34_exists_innerHom_permutes hZ hRN
    (fun x hx => uc22s2112r34q35_inner_of_mem hKF1 hL hp hp2 hadm hX hA1 hRee hBN hfaith h5
      le_rfl hrg hRB hRr hx)
    (uc22p2214_isSylowOf_inf D.sylowM hL.1) D.sylowM.isPGroup hRT
  have hψ5 : IsPGroup 5 ψ.range := hR5.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hbot : ψ.range = ⊥ := by
    rcases hcase with ⟨rfl, rfl⟩ | hK
    · rcases hψ5.card_eq_or_dvd with h1 | h5d
      · exact Subgroup.card_eq_one.1 h1
      · have hc := CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional
          (hX.chevalleyExceptionalModel (by decide))
        have h5L := h5d.trans (Subgroup.card_subgroup_dvd_card ψ.range)
        rw [hc] at h5L
        exact absurd h5L (by decide)
    · exact hPF (BarInf L) t n p hK hX P ψ.range hψ5 hperm
  have hR1 : R = ⊥ := (eq_bot_iff_forall R).2 fun x hx => by
    have hψx : ψ ⟨x, hx⟩ = 1 := by
      have h : ψ ⟨x, hx⟩ ∈ ψ.range := MonoidHom.mem_range.2 ⟨_, rfl⟩
      rwa [hbot, mem_bot] at h
    have h1 : inducedBarInfAutHom L ⟨x, hRN hx⟩ = 1 := by
      rw [← hψ ⟨x, hx⟩, hψx, map_one]
    exact hfaith x (hRB hx) (uc22s2113_centralizesBar_of_inducedBarInfAutHom_eq_one hL.2.2 _ h1)
  rw [hR1, card_bot] at h5R
  exact absurd h5R (by norm_num)

end Four

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
