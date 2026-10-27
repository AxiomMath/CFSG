module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114E3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3LBorel
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Thin
import CFSG.LocalAnalysis.UniquenessCase.UC22P20zbb
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214d
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSL
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
import CFSG.LocalAnalysis.UniquenessCase.UC22P22i

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114r4t_dvd_of_mem_normalizer {Y : Type} [Group Y] [Finite Y] {m f : ℕ}
    (hY : LieModel Y .PSL m 2 f) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) {y : Y}
    (hy : y ∈ normalizer (U : Set Y)) (hy1 : y ≠ 1) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hyr : y ^ r = 1) : r ∣ 2 ^ f - 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ U.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hU.2.2
  have hyS : y ∈ normalizer (((hU.2.1.toSylow hidx : Sylow 2 Y) : Subgroup Y) : Set Y) := hy
  obtain ⟨⟨-, -, hm, -⟩, F, _, _, hF, ⟨e⟩⟩ := LieModel.statedClassicalModel hY (by decide)
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hF)
  have h := uc22s2114r3l_dvd_of_borelQuotient (CFSG.AGLEmbedding.ParabHub.borelQuotient_sl
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (m + 1) F).trans
      e.symm)) _ hyS hy1 hr hr2 hyr
  rwa [hF] at h

theorem uc22s2114r4t_exists_mem_normalizer {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch)
    (hn4 : ¬ 4 ∣ c.n) (hn3 : 3 ≤ c.n) :
    ∃ b ∈ c.B0, b ∈ normalizer (D.T : Set G) ∧ ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ orderOf b = r := by
  obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (n := c.n) (by omega)
  have hm2 : 2 ≤ m := by
    by_contra hlt
    obtain rfl : m = 1 := by
      obtain ⟨j, rfl⟩ := hm
      omega
    rw [mul_one] at hnm
    rcases e with _ | _ | e
    · rw [pow_zero] at hnm
      omega
    · rw [pow_one] at hnm
      omega
    · exact hn4 ⟨2 ^ e, by rw [hnm]; ring⟩
  have h4 : 4 ≤ 2 ^ m := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm2)
  obtain ⟨r, hr, hrm⟩ := Nat.exists_prime_and_dvd (n := 2 ^ m - 1) (by omega)
  have hr2 : r ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    omega
  have hrn : r ∣ 2 ^ c.n - 1 :=
    hrm.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (Dvd.intro_left _ hnm.symm))
  obtain ⟨b, hb, hbr⟩ := uc22p22i_exists_elt_of_mem_piSet
    (show r ∈ piSet c.B0 by rw [c.hpi]; exact ⟨hr, hrn⟩)
  have hbα : b ∈ oPi {p | p.Prime ∧ p ∣ 2 ^ m - 1} c.B0 :=
    uc22pwtb_mem_oPi c.hB0.2.1 hb fun p hp hpb => by
      rw [hbr] at hpb
      obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hr).1 hpb
      exact ⟨hp, hrm⟩
  exact ⟨b, hb, c.hα e m hm hnm hbα, r, hr, hr2, hbr⟩

theorem s21_14R4T_holds (D : Data G) (Ch : Choice2011 G) : S21_14R4T D Ch := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro _ c L hL _ _ hX hn3 hBL hfaith hk1
  exfalso
  obtain ⟨m, hm, hmod, hn4⟩ : ∃ m : ℕ, 3 ≤ m ∧ LieModel (BarInf L) .PSL m 2 1 ∧ ¬ 4 ∣ c.n := by
    rcases hX with ⟨h, h4⟩ | ⟨h | h, hk⟩
    · exact ⟨5, by norm_num, h, h4⟩
    · exact ⟨6, by norm_num, h, fun h4 => by obtain ⟨j, hj⟩ := (hk1 hk).1; omega⟩
    · exact ⟨7, by norm_num, h, fun h4 => by obtain ⟨j, hj⟩ := (hk1 hk).1; omega⟩
  obtain ⟨b, hb, hbT, r, hr, hr2, hbr⟩ := uc22s2114r4t_exists_mem_normalizer c hn4 hn3
  have hbr' : b ^ r = 1 := by
    rw [← hbr]
    exact pow_orderOf_eq_one b
  have hb1 : inducedBarInfAutHom L ⟨b, hBL hb⟩ ≠ 1 := fun h1 => by
    rw [uc22s2114_eq_one_of_inducedBarInfAutHom_eq_one hL hBL hfaith hb h1, orderOf_one] at hbr
    exact hr.ne_one hbr.symm
  have hout := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (Or.inl rfl) hm Nat.prime_two le_rfl (LieModel.statedClassicalModel hmod (by decide))).1
  have h2 : ¬ r ∣ 2 * 1 * CFSG.RankThree.OuterOrder.determinantParameter .PSL m (2 ^ 1) := by
    simpa [CFSG.RankThree.OuterOrder.determinantParameter] using
      fun h : r ∣ 2 => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h)
  obtain ⟨U, hU, y, hy, hy1, hyr⟩ := uc22s2114_exists_of_borel hL
    (uc22p2214_isSylowOf_inf D.sylowM hL.1) (hBL hb) hbT hbr' hb1
    fun _ hα => uc22p2214_out_mem_of_card_dvd hout hr h2 hα
  have h1 := uc22s2114r4t_dvd_of_mem_normalizer hmod hU hy hy1 hr hr2 hyr
  norm_num at h1
  exact hr.ne_one h1

end CFSG.LocalAnalysis.UniquenessCase.UC22
