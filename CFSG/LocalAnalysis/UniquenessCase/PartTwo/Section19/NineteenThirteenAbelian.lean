module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenThirteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTenTwoComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.AutOmegaThreeL2Square
import CFSG.GroupTheory.PGroup.CommuteOfRankThreeKernel
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Arithmetic
import CFSG.RankThree.PartTwo.Sec18.Item1810Act

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (K_19_13_autOmega)

variable {G : Type} [Group G] [Finite G]

section Certificates


theorem even_shape_of_ctx19_10 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h42 : S17.R17_42At D V₀ V) (h3 : 3 ∈ piSet A) :
    Even (S17.nOf L) ∧ 2 < S17.nOf L ∧
      (IsL2Square (Bar2 (IOf D p L)) (S17.nOf L) ∨
        (S17.IsL2U3Product (Bar2 (IOf D p L)) (S17.nOf L) ∧ IsPowTwo (S17.nOf L))) := by
  have hn : Even (S17.nOf L) := by
    by_contra hne
    have hodd : Odd (S17.nOf L) := Nat.not_even_iff_odd.mp hne
    have h3sq : 3 ∣ (2 ^ S17.nOf L - 1) * (2 ^ S17.nOf L - 1) := by
      rw [← card_eq_of_isZModSq h.hAcard]
      exact h3.2
    exact CFSG.SignalizerFunctorTheorem.McBride.PSL2Even.not_three_dvd_pow_sub_one hodd
      ((Nat.prime_three.dvd_mul.mp h3sq).elim id id)
  have h1910 := h.h1910
  simp only [Setting1910] at h1910
  obtain ⟨-, h1 | h2 | h3'⟩ := h1910
  · exact absurd h1.2.1 (Nat.not_odd_iff_even.mpr hn)
  · refine ⟨hn, h2.2.2.1, ?_⟩
    rcases (bar2_IOf_shape_of_alt2 D h h42 h2).2 with hsq | hsq
    · exact Or.inl hsq
    · exfalso
      obtain ⟨A', B', _, _, -, hA', -⟩ := hsq
      obtain ⟨-, -, -, -, hodd, -⟩ := hA'.admissible
      exact (Nat.not_odd_iff_even.mpr hn) hodd
  · obtain ⟨hsh, hn2, hpow, -⟩ := h3'
    refine ⟨hn, hn2, ?_⟩
    rcases hsh with hU | hL2
    · exact Or.inr ⟨hU, hpow⟩
    · exact Or.inl hL2

theorem omegaOne_comm_of_ctx19_10 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h42 : S17.R17_42At D V₀ V) (hK : K_19_13_autOmega) (h3 : 3 ∈ piSet A)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    IsMulCommutative ↥(UCK.omegaOne 3 P) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hn, hn2, hshape⟩ := even_shape_of_ctx19_10 D h h42 h3
  have hL : L ∈ calC D.M := h.hyp.hL.1
  have hMN : D.M ≤ normalizer (IOf D p L : Set G) := le_normalizer_IOf D hL
  have hPN : P ≤ normalizer (IOf D p L : Set G) := hP.le.trans hMN
  have hP3 : IsPGroup 3 P := hP.isPGroup
  have hZ : Subgroup.center (Bar2 (IOf D p L)) = ⊥ :=
    Inputs1719.center_eq_bot_of_isL2Square_or_isL2U3Product (hshape.imp id And.left)
  have hKI := hK (Bar2 (IOf D p L)) (S17.nOf L) hn hn2 hshape
  obtain ⟨E₀, hE₀A, hE₀el, hE₀card⟩ :=
    exists_isElemAbelian_card_nine_of_isZModSq h.hAcard h3.2
  have hE₀M : E₀ ≤ D.M := hE₀A.trans (A_le_M_of_ctx19_10 D h)
  have hE₀p : IsPGroup 3 E₀ := IsPGroup.of_card (n := 2) (by rw [hE₀card]; norm_num)
  obtain ⟨m, hmM, hm⟩ :=
    CFSG.RankThree.PartTwo.Sec18.Item1810Proof.exists_conj_le_of_isSylowOf hP hE₀M hE₀p
  let E : Subgroup G := E₀.map (MulAut.conj m⁻¹).toMonoidHom
  have hEP : E ≤ P := by
    rintro x ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using hm y hy
  have hEI : E ≤ IOf D p L := by
    rintro x ⟨y, hy, rfl⟩
    have hyI : y ∈ IOf D p L := h.hA (hE₀A hy)
    have hm' : m⁻¹ ∈ normalizer (IOf D p L : Set G) := hMN (D.M.inv_mem hmM)
    exact (Subgroup.mem_normalizer_iff.mp hm' y).mp hyI
  have hEel : IsElemAbelian 3 E := hE₀el.map (MulAut.conj m⁻¹).toMonoidHom
  have hEcard : Nat.card E = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective]
    exact hE₀card
  let K : Subgroup G := (CFSG.GroupTheory.conjModPCore 2 (IOf D p L) P hPN).ker.map P.subtype
  have hJn : P ≤ normalizer ((P ⊓ IOf D p L : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hg) x
    have h2 := Subgroup.mem_normalizer_iff.mp (hPN hg) x
    simp only [Subgroup.mem_inf]
    exact ⟨fun hx => ⟨h1.mp hx.1, h2.mp hx.2⟩, fun hx => ⟨h1.mpr hx.1, h2.mpr hx.2⟩⟩
  have hKn : P ≤ normalizer (K : Set G) :=
    CFSG.ABGLocalTools.le_normalizer_map_subtype P _
  have hrank : CFSG.Open.pRank 3 P ≤ 3 :=
    (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hP.le).trans
      ((CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
        (by norm_num) D.M D.maxLocal.1).trans_eq (evenRank_eq_three_of_ctx h))
  have key : ∀ x ∈ P, ∀ y ∈ P, x ^ 3 = 1 → y ^ 3 = 1 → x * y = y * x :=
    fun x hx y hy hx3 hy3 =>
      CFSG.GroupTheory.commute_of_pow_three_of_commutator_mem_ker hP3 inf_le_left
        (Subgroup.map_subtype_le _) hJn hKn
        (Inputs1719.inf_inf_map_ker_conjModPCore_eq_bot hPN hP3 hZ) (le_inf hEP hEI) hEel
        hEcard hrank
        (fun a ha b hb ha3 hb3 =>
          Inputs1719.commutator_mem_ker_conjModPCore_of_autOmega hPN hP3 hKI ha hb ha3 hb3)
        hx hy hx3 hy3
  refine Subgroup.isMulCommutative_closure ?_
  intro a ha b hb _
  exact key a ha.1 b hb.1 ha.2 hb.2

theorem nineteen_thirteen_of_autOmega (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h12 : Concl19_12 D A 3) (h42 : S17.R17_42At D V₀ V) (hK : K_19_13_autOmega) :
    R19_13At D V₀ V p L A t B r h :=
  fun h3 P hP =>
    ⟨nineteen_thirteen_sylow D h h12 h3 P hP, omegaOne_comm_of_ctx19_10 D h h42 hK h3 hP⟩

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
