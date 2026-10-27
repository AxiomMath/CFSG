module

public import CFSG.RankThree.PartTwo.Sec4.Item426RestModels
public import CFSG.RankThree.PartTwo.KFacts.K426Rest
import CFSG.RankThree.PartTwo.Sec4.Item426RestLinear
import CFSG.RankThree.PartTwo.Sec4.Item426A6Proof
import CFSG.RankThree.PartTwo.Sec4.Item426A6U43
import CFSG.RankThree.PartTwo.KFacts.K426RestMcL
import CFSG.RankThree.PartTwo.KFacts.K426J3
import CFSG.RankThree.PartTwo.KFacts.K412TripleCover
import CFSG.Models.PGLOrders

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item426Rest

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

structure RestNumerics (N : ℕ) : Prop where
  nine_dvd : 9 ∣ N
  big : 720 < N
  not_dvd_mcl_a : ¬ N ∣ 29160
  not_dvd_mcl_b : ¬ N ∣ 972
  not_dvd_on : ¬ N ∣ 3240
  not_dvd_u43 : ¬ N ∣ 653184
  not_dvd_g23 : ¬ N ∣ 4245696

theorem card_projSU_four_three : Nat.card (projSU 4 3 1) = 3265920 :=
  CFSG.PGLModel.card_projSU_four_three

theorem card_dvd_of_G2_three
    {S : Type} [Group S]
    (hS : Blueprint.ChevalleyExceptionalModel S .G2 3 1) : Nat.card S ∣ 4245696 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hS
  have h1 : Nat.card S = Nat.card (Blueprint.AdjointQuotient .G2 K) := Nat.card_congr e.toEquiv
  have h2 : Nat.card (Blueprint.AdjointQuotient .G2 K) ∣
      Nat.card (Blueprint.Chevalley.adjointGroup .G2 K) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (Blueprint.Chevalley.adjointGroup .G2 K))]
    exact Dvd.intro _ rfl
  have h4 : Nat.card (Blueprint.Chevalley.adjointGroup .G2 K) = 4245696 := by
    rw [(CFSG.LieType.Chevalley.exact_G2_finite_order K hK).2.1]
    norm_num
  rw [h1, ← h4]
  exact h2

theorem card_quotient_center_dvd_of_isExtOf {X : Type} [Group X] (hX : IsQuasisimple X)
    {S : Type*} [Group S] (hext : IsExtOf X S (Multiplicative (ZMod 3))) :
    Nat.card (X ⧸ Subgroup.center X) ∣ Nat.card S := by
  obtain ⟨N, hN, ⟨eN⟩, ⟨eQ⟩⟩ := hext
  have hNZ : N ≤ Subgroup.center X := le_center_of_normal_mulEquiv_zmod3 hX hN eN
  rw [← Nat.card_congr eQ.toEquiv]
  exact card_quotient_center_dvd hNZ

namespace ConfigRest

variable {X : Type} [Group X] [Finite X] {α : MulAut X} {P : Subgroup X}

theorem false_of_inner_matrix (h : ConfigRest X α P) {y : X} (hα : α = MulAut.conj y)
    (hy : y ∉ Subgroup.center X) {K : Type*} [Field K] (h3 : (3 : K) ≠ 0)
    {H : Subgroup (GL (Fin 3) K)} (e : X ≃* H) : False := by
  have : Group.IsPerfect P := h.isPerfect
  obtain ⟨z, hzP, hzZ, hz1, hz3⟩ := h.central
  set M : X →* Matrix (Fin 3) (Fin 3) K :=
    (Units.coeHom (Matrix (Fin 3) (Fin 3) K)).comp (H.subtype.comp e.toMonoidHom) with hM
  have hMinj : Function.Injective M := fun x x' hxx' =>
    e.injective (Subtype.ext (Units.ext hxx'))
  let ρ : P →* Matrix (Fin 3) (Fin 3) K := M.comp P.subtype
  have hρ : ∀ g : P, ρ g = M g := fun _ => rfl
  obtain ⟨μ, hμ⟩ := exists_scalar_of_perfect h3 ρ (z := ⟨z, hzP⟩)
    (fun g => by
      rw [hρ, hρ, ← map_mul, ← map_mul]
      exact congrArg M (Subgroup.mem_center_iff.mp hzZ (g : X)).symm)
    (by rw [hρ, ← map_pow]; exact congrArg M hz3 |>.trans (map_one M))
    (fun h1 => hz1 (hMinj (by rw [← hρ ⟨z, hzP⟩]; exact h1.trans (map_one M).symm)))
    (y := M y) (fun g => by
      rw [hρ, ← map_mul, ← map_mul, h.commute_of_eq_conj hα g.2])
  apply hy
  rw [Subgroup.mem_center_iff]
  intro g
  apply hMinj
  rw [map_mul, map_mul, hμ]
  exact (Matrix.scalar_commute μ (fun _ => Commute.all _ _) (M g)).symm

theorem false_of_inner_eps (h : ConfigRest X α P) {y : X} (hα : α = MulAut.conj y)
    (hy : y ∉ Subgroup.center X) {p e : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hSL : IsSLThreeEpsAt X (p ^ e)) : False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hK⟩ := hSL
  have := Fintype.ofFinite K
  rcases hK with ⟨hKc, ⟨eK⟩⟩ | ⟨hKc, ⟨eK⟩⟩
  · have : CharP K p := charP_of_card_eq_prime_pow (f := e)
      (by rw [← Nat.card_eq_fintype_card, hKc])
    exact h.false_of_inner_matrix hα hy (Item426.Config426.three_ne_zero_of_charP hp hp3) eK
  · have : CharP K p := charP_of_card_eq_prime_pow (f := 2 * e)
      (by rw [← Nat.card_eq_fintype_card, hKc, ← pow_mul, mul_comm])
    exact h.false_of_inner_matrix hα hy (Item426.Config426.three_ne_zero_of_charP hp hp3) eK

theorem false_of_inner (hON : K426Rest.ONThreeCentralizer) (h : ConfigRest X α P)
    (hlist : IsList46 X) (hnum : RestNumerics (Nat.card (secQ P))) {y : X}
    (hα : α = MulAut.conj y) (hy : y ∉ Subgroup.center X) : False := by
  have hX := h.quasisimple
  have hZ := h.center_ne_bot
  have hbig : ∃ N, 720 < N ∧ N ∣ Nat.card X := ⟨_, hnum.big, card_secQ_dvd⟩
  obtain ⟨-, h3N, -⟩ := h.inner_dvd hα hy
  have h27 : 27 ∣ Nat.card (X ⧸ Subgroup.center X) :=
    (Nat.mul_dvd_mul_left 3 hnum.nine_dvd).trans h3N
  have hN : Nat.card (secQ P) ∣ Nat.card (X ⧸ Subgroup.center X) :=
    (Dvd.intro_left 3 rfl).trans h3N
  have hnot27 : ∀ {S : Type} [Group S], IsExtOf X S (Multiplicative (ZMod 3)) →
      ¬ 27 ∣ Nat.card S → False :=
    fun hext hS => hS (h27.trans (card_quotient_center_dvd_of_isExtOf hX hext))
  obtain ⟨hZJ3, hZMcL, hZON⟩ := Item426.center_J3_McL_ON
  rcases hlist with ⟨p, e, _, -, -, ⟨e1⟩⟩ |
      ⟨p, e, _, hp3, he1, -, hSL | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩⟩ |
      ⟨p, _, hp3, hG2 | ⟨⟨e1⟩⟩ | ⟨-, ⟨e1⟩⟩ | ⟨-, ⟨e1⟩⟩⟩ |
      (⟨n, -, ⟨e1⟩⟩ | hA6 | hA7) | (⟨s, hs, ⟨e1⟩⟩ | ⟨s, hs, hext⟩) |
      (hchev | ⟨n, -, hSL⟩) | (⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩) |
      ((⟨e, he1, -, ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩⟩) | ⟨⟨e1⟩⟩ | ⟨-, hG23 | hU43'⟩)
  ·
    exact false_of_projSL hX hZ e1
  ·
    exact h.false_of_inner_eps hα hy Fact.out (by omega) hSL
  · exact false_of_projSL hX hZ e1
  · exact false_of_projSU hX hZ le_rfl he1 e1
  ·
    exact false_of_chevalleyExceptional hX hZ (Or.inl rfl) hG2
  · refine false_of_projSp hX hZ (by norm_num) (Or.inl (Or.inr ?_)) e1
    rw [GaloisField.card p 1 one_ne_zero, pow_one]
    omega
  · exact false_of_projSU hX hZ (by norm_num) le_rfl e1
  · exact false_of_projSL hX hZ e1
  ·
    exact false_of_alternating hX hZ hbig e1
  · exact hnot27 hA6 (by rw [KFacts.K412.card_alternating_six_seven.1]; norm_num)
  · exact hnot27 hA7 (by rw [KFacts.K412.card_alternating_six_seven.2]; norm_num)
  ·
    exact false_of_sporadic46 hX hZ hs e1
  · simp only [sporadicCovers46, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    ·
      refine hnot27 hext ?_
      change ¬ 27 ∣ Nat.card Blueprint.NativeSporadic.M22
      rw [Item426.card_M22]
      norm_num
    ·
      obtain ⟨h3, ⟨eJ⟩⟩ := (isTripleCover_iff_isExtOf hX hZJ3).mpr hext
      have hPC : P ≤ Subgroup.centralizer {y} := fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.mpr (h.commute_of_eq_conj hα hx).symm
      have hbot := K426.j3CoverCentralizer X hX h3 ⟨eJ⟩ y hy (h.pow_three_mem_center hα) P hPC
        h.isPerfect
      obtain ⟨z, hzP, hzZ, hz1, -⟩ := h.central
      have hmem : z ∈ P ⊓ Subgroup.center X := ⟨hzP, hzZ⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hz1 hmem
    ·
      obtain ⟨-, ⟨eM⟩⟩ := (isTripleCover_iff_isExtOf hX hZMcL).mpr hext
      obtain ⟨-, x, hxo, hdvd⟩ := h.inner_dvd_of_mulEquiv hα hy eM
      rcases K426Rest.mclThreeCentralizerCard x hxo with hc | hc
      · rw [hc] at hdvd
        exact hnum.not_dvd_mcl_a hdvd
      · rw [hc] at hdvd
        exact hnum.not_dvd_mcl_b hdvd
    ·
      obtain ⟨-, ⟨eO⟩⟩ := (isTripleCover_iff_isExtOf hX hZON).mpr hext
      obtain ⟨-, x, hxo, hdvd⟩ := h.inner_dvd_of_mulEquiv hα hy eO
      rw [hON x hxo] at hdvd
      exact hnum.not_dvd_on hdvd
  ·
    rcases hchev with ⟨n, hn, ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩⟩ |
      ⟨f, hG2 | hD4 | hSz | hF4 | hTits⟩
    · exact false_of_projSL hX hZ e1
    · exact false_of_projSL hX hZ e1
    · exact false_of_projSU hX hZ le_rfl hn e1
    · exact false_of_projSp_two hX hZ hbig hn e1
    · exact false_of_projSU hX hZ (by norm_num) hn e1
    · exact false_of_chevalleyExceptional hX hZ (Or.inl rfl) hG2
    · exact false_of_chevalleyExceptional hX hZ (Or.inr rfl) hD4
    · exact false_of_suzuki hX hZ hSz
    · exact false_of_reeTits hX hZ (Or.inl rfl) hF4
    · exact false_of_reeTits hX hZ (Or.inr rfl) hTits
  ·
    exact h.false_of_inner_eps hα hy Nat.prime_two (by norm_num) hSL
  ·
    exact false_of_projSL hX hZ e1
  · exact false_of_projSp hX hZ (by norm_num)
      (Or.inr (Or.inr ⟨GaloisField.card 2 1 one_ne_zero, le_rfl⟩)) e1
  · exact false_of_projSU hX hZ (by norm_num) (by norm_num) e1
  ·
    exact false_of_projSL hX hZ e1
  · exact false_of_projSU hX hZ le_rfl he1 e1
  · exact false_of_projSL hX hZ e1
  ·
    exact hnum.not_dvd_g23 (hN.trans (card_dvd_of_G2_three hG23))
  ·
    obtain ⟨eU⟩ := hU43'
    obtain ⟨-, x, hxo, hdvd⟩ := h.inner_dvd_of_mulEquiv hα hy eU
    have h5 := Item426.u43ThreeCentralizer x hxo
    have hC : Nat.card (Subgroup.centralizer {x}) ∣ 5 * 653184 := by
      rw [show 5 * 653184 = 3265920 by norm_num, ← card_projSU_four_three]
      exact Subgroup.card_subgroup_dvd_card _
    have hcop : Nat.Coprime (Nat.card (Subgroup.centralizer {x})) 5 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr h5).symm
    exact hnum.not_dvd_u43 (hdvd.trans (hcop.dvd_of_dvd_mul_left hC))

end ConfigRest

end CFSG.RankThree.PartTwo.Sec4.Item426Rest
