module

public import CFSG.RankThree.PartTwo.Sec19.Step1917ProofDefs
public import CFSG.RankThree.PartTwo.Sec19.Step1918ProofEnd
import CFSG.RankThree.PartTwo.Sec3.ThreeGroupCentralizer
import CFSG.RankThree.PartTwo.Sec19.Step1919Narrow
import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.RankThree.PartTwo.Sec13.Item136PGL

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

namespace Step1917Proof

variable {G : Type} [Group G] [Finite G]

theorem two_lt_card_of_mem_upperCentralSeries {P S : Subgroup G} (hP : IsPGroup 3 P)
    (hS : IsPGroup 2 S) (hPS : P ≤ Subgroup.normalizer (S : Set G))
    (hfaith : ∀ g ∈ P, (∀ s ∈ S, g * s = s * g) → g = 1) {x : G} (hxP : x ∈ P)
    (hx : orderOf x = 3) (hx2 : (⟨x, hxP⟩ : P) ∈ Subgroup.upperCentralSeries P 2)
    (hxZ : (⟨x, hxP⟩ : P) ∉ Subgroup.center P) :
    2 < Nat.card (S ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) := by
  classical
  obtain ⟨y, hyP, hxy⟩ : ∃ y ∈ P, x * y ≠ y * x := by
    by_contra h
    push Not at h
    apply hxZ
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (h g g.2).symm
  set z := x * y * x⁻¹ * y⁻¹ with hz
  have hzc : ∀ g ∈ P, g * z = z * g := by
    intro g hg
    have h1 := (Subgroup.mem_upperCentralSeries_succ_iff (n := 1)).mp hx2 ⟨y, hyP⟩
    rw [Subgroup.upperCentralSeries_one, Subgroup.mem_center_iff] at h1
    have h2 := congrArg Subtype.val (h1 ⟨g, hg⟩)
    simpa [hz, commutatorElement_def, mul_assoc] using h2
  set P₀ := Subgroup.closure ({x, y} : Set G) with hP₀
  have hP₀P : P₀ ≤ P := by
    rw [hP₀, Subgroup.closure_le]
    intro w hw
    rcases hw with rfl | rfl
    · exact hxP
    · exact hyP
  have hxP₀ : x ∈ P₀ := Subgroup.subset_closure (Set.mem_insert x _)
  have hyP₀ : y ∈ P₀ := Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have hzpow : ∀ g ∈ P, ∀ w ∈ Subgroup.zpowers z, g * w * g⁻¹ = w := by
    intro g hg w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [(Commute.zpow_right (hzc g hg) k).eq, mul_inv_cancel_right]
  have hcomm : ∀ p ∈ P₀, y * p * y⁻¹ * p⁻¹ ∈ Subgroup.zpowers z := by
    intro p hp
    induction hp using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with h | h
      · have e : y * a * y⁻¹ * a⁻¹ = z⁻¹ := by rw [hz, h]; group
        rw [e]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers z)
      · rw [Set.mem_singleton_iff.mp h, show y * y * y⁻¹ * y⁻¹ = 1 by group]
        exact Subgroup.one_mem _
    | one =>
      rw [show y * 1 * y⁻¹ * (1 : G)⁻¹ = 1 by group]
      exact Subgroup.one_mem _
    | mul a b ha hb iha ihb =>
      have e : y * (a * b) * y⁻¹ * (a * b)⁻¹ =
          (y * a * y⁻¹ * a⁻¹) * (a * (y * b * y⁻¹ * b⁻¹) * a⁻¹) := by group
      rw [e, hzpow a (hP₀P ha) _ ihb]
      exact Subgroup.mul_mem _ iha ihb
    | inv a ha iha =>
      have e : y * a⁻¹ * y⁻¹ * a⁻¹⁻¹ = a⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
      rw [e, hzpow _ (P.inv_mem (hP₀P ha)) _ (Subgroup.inv_mem _ iha)]
      exact Subgroup.inv_mem _ iha
  have hyZ2 : (⟨y, hyP₀⟩ : P₀) ∈ Subgroup.upperCentralSeries P₀ 2 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff,
      Subgroup.upperCentralSeries_one]
    intro p
    rw [Subgroup.mem_center_iff]
    intro q
    apply Subtype.ext
    have h1 := hzpow q (hP₀P q.2) _ (hcomm p p.2)
    have h2 : (q : G) * (y * p * y⁻¹ * (p : G)⁻¹) = (y * p * y⁻¹ * (p : G)⁻¹) * q := by
      calc (q : G) * (y * p * y⁻¹ * (p : G)⁻¹)
          = (q * (y * p * y⁻¹ * (p : G)⁻¹) * (q : G)⁻¹) * q := by group
        _ = (y * p * y⁻¹ * (p : G)⁻¹) * q := by rw [h1]
    simpa [commutatorElement_def, mul_assoc] using h2
  rcases Sec3.rank3II_3_19 (hP.to_le hP₀P) hS (hP₀P.trans hPS)
      (fun g hg => hfaith g (hP₀P hg)) hxP₀ hx with h | h
  · exact absurd (h y ⟨_, hyZ2, rfl⟩) hxy
  · exact h

theorem map_conj_eq_of_mem_of_isMaximalTwoLocal (hst : PartTwoStanding G)
    {Y K L F : Subgroup G} (hY : IsMaximalTwoLocal Y)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    (hK : K ∈ oTwoComponentsIn Y) (hLK : L ≤ K) (hFL : F ≤ L)
    (hF : CFSG.Assembly.IsElemAbelian 3 F) (hF9 : Nat.card F = 9) {m : G} (hm : m ∈ Y) :
    K.map (MulAut.conj m).toMonoidHom = K := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.Open.pCoreOf 2 Y with hQdef
  have hQ : Q ≠ ⊥ := pCoreOf_ne_bot_of_isMaximalTwoLocal hY
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hYQ : Y ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hKY : K ≤ Y := le_of_mem_oTwoComponentsIn hK
  have hLY : L ≤ Y := hLK.trans hKY
  set J := K.map (MulAut.conj m).toMonoidHom with hJ
  have hJY : J ∈ oTwoComponentsIn Y := Sec18.map_conj_mem_oTwoComponentsIn hK hm
  have hJK : J ≠ K := hne
  have hF₂ : CFSG.Assembly.IsElemAbelian 3 (F.map (MulAut.conj m).toMonoidHom) :=
    Sec13.isElemAbelian_map hF _
  have hF₂9 : Nat.card (F.map (MulAut.conj m).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj m).injective, hF9]
  have hF₂J : F.map (MulAut.conj m).toMonoidHom ≤ J :=
    Subgroup.map_mono (hFL.trans hLK)
  have h4 := Step1918Proof.four_le_localRank_of_pair hQ hQ2 hYQ
    (CFSG.LieType.BorelTits.pCoreOf_le 2 Y) hQ2
    hYQ hF hF9 (hFL.trans hLY) hF₂ hF₂9 (hF₂J.trans (le_of_mem_oTwoComponentsIn hJY))
    (fun a ha b hb => Step1910Proof.commutator_mem_pCoreOf hK hJY (Ne.symm hJK)
      (hLK (hFL ha)) (hF₂J hb))
    (fun a ha b hb hab => by
      refine Step1916Proof2.eq_one_of_forall_commutator_mem hZ hLY (hFL ha) (k := 1)
        (by rw [pow_one]; exact hF.2 a ha) fun l hl => ?_
      exact Step1918Proof.commutator_mem_of_inv_mul_mem hab (hYQ (hLY (hFL ha))) (hYQ (hLY hl))
        (Step1910Proof.commutator_mem_pCoreOf hJY hK hJK (hF₂J hb) (hLK hl)))
  rw [hst.toTheoremFourHyp.localRank_three] at h4
  omega

omit [Finite G] in
theorem normalizer_zpowers_le (d : G) :
    Subgroup.normalizer (Subgroup.zpowers d : Set G) ≤ Subgroup.normalizer
      (CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) : Set G) := by
  intro g hg
  have h1 := Step1919Narrow.mem_normalizer_centralizer hg
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h1
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ h1

end Step1917Proof

end CFSG.RankThree.PartTwo.Sec19
