module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentySixAProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.VZeroSmall17

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def JChoice19 (D : Data G) (L K J : Subgroup G) : Prop :=
  ((J = L ∨ J = K) ∧ (L.subgroupOf D.M).Normal) ∨ (J = L ⊔ K ∧ ¬ (L.subgroupOf D.M).Normal)

@[expose] def calP19_4 (D : Data G) (L K J A : Subgroup G) : Set (Subgroup G) :=
  {Y | E1.IsE 1 (J ⊔ D.T) D.T A Y ∧ ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      (Nat.card Y).primeFactors = {2, q} ∧ (q = 5 ∨ (q = 3 ∧ (Opp 3 Y ≤ L ∨ Opp 3 Y ≤ K)))}

theorem not_le_centralizer_cClos_two_19 {D : Data G} {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hm : 4 < mSub V₀) (hsp : IsStronglyPEmbedded 5 D.M)
    (hN2 : ¬ normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M) {J : Subgroup G} (hJM : J ≤ D.M)
    (h5J : 5 ∣ Nat.card J) : ¬ J ≤ centralizer (E3.cClos V₀ 2 D.T : Set G) := by
  intro hJC
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) 5 h5J
  have hzo : orderOf (z : G) = 5 := by rw [Subgroup.orderOf_coe, hzord]
  obtain ⟨g, hgN, hgM⟩ := SetLike.not_le_iff_exists.mp hN2
  have hzC : (z : G) ∈ centralizer (E3.cClos V₀ 2 D.T : Set G) := hJC z.2
  have hmem : g⁻¹ * (z : G) * g ∈
      centralizer ((V₀ ⊓ centerOf (E3.wClos V₀ 2 D.T) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvW : v ∈ E3.wClos V₀ 2 D.T := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hv).2).1
    have hvCw : v ∈ centralizer (E3.wClos V₀ 2 D.T : Set G) :=
      (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hv).2).2
    have hvC2 : g * v * g⁻¹ ∈ E3.cClos V₀ 2 D.T := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact E3.wClos_le 2 D.T ((Subgroup.mem_normalizer_iff.mp hgN v).mp hvW)
      · rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have hw' : g⁻¹ * w * g ∈ E3.wClos V₀ 2 D.T := by
          simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) w).mp hw
        have hvw := Subgroup.mem_centralizer_iff.mp hvCw (g⁻¹ * w * g) hw'
        calc w * (g * v * g⁻¹) = g * ((g⁻¹ * w * g) * v) * g⁻¹ := by group
          _ = g * (v * (g⁻¹ * w * g)) * g⁻¹ := by rw [hvw]
          _ = (g * v * g⁻¹) * w := by group
    have hyc := Subgroup.mem_centralizer_iff.mp hzC (g * v * g⁻¹) hvC2
    calc v * (g⁻¹ * (z : G) * g) = g⁻¹ * ((g * v * g⁻¹) * (z : G)) * g := by group
      _ = g⁻¹ * ((z : G) * (g * v * g⁻¹)) * g := by rw [hyc]
      _ = (g⁻¹ * (z : G) * g) * v := by group
  have hzM : g⁻¹ * (z : G) * g ∈ D.M := S17.centralizer_inf_centerOf_wClos_two_le h hm hmem
  have hYM : Subgroup.zpowers (z : G) ≤ D.M := Subgroup.zpowers_le.2 (hJM z.2)
  have hYp : IsPGroup 5 (Subgroup.zpowers (z : G)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hzo, pow_one]
  have hbot := hsp.inf_map_conj_eq_bot (by norm_num) hYM hYp g hgM
  have hzmem : (z : G) ∈ Subgroup.zpowers (z : G) ⊓
      (D.M).map (MulAut.conj g).toMonoidHom := by
    refine ⟨Subgroup.mem_zpowers _, ?_⟩
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * (z : G) * g, hzM, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  rw [hbot, Subgroup.mem_bot] at hzmem
  rw [hzmem, orderOf_one] at hzo
  omega

theorem calPMTA_eq_empty_19 (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h66 : UC6.R6_6 D) (h88 : W3Thm88 G)
    {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) (hm : 4 < mSub V₀) (h93 : Thm93 V₀ D.T)
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T)
    (hAS : IsSylowIn 2 (D.T ⊓ centralizer (A : Set G)) (D.M ⊓ centralizer (A : Set G))) :
    calPMTA V₀ D.T A = ∅ := by
  have hne : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub (by omega)
  have hV : InCalV D.M V₀ := S17.hyp125_inCalV h hne
  have hTI := S17.hyp125_isTI h hne
  have hN : normalizer (V₀ : Set G) = D.M := normalizer_eq_of_inCalV D hV
  have h8 : 8 ≤ Nat.card V₀ := by
    have hcardV0 : Nat.card V₀ = 2 ^ mSub V₀ :=
      card_eq_two_pow_mSub h.pairFacts.elemAbelian₀.isPGroup
    rw [hcardV0]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ mSub V₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hCU : CentralizersUnique D.M D.T := by
    rcases h.1 with ⟨-, hbot⟩ | ⟨-, hCU, -⟩
    · exact absurd hbot hne
    · exact hCU
  have h9 : Hyp9 V₀ D.T :=
    { hyp7 := TwelveSeven.hyp7_of_inCalV D hV hTI h8
      sylow := by rw [hN]; exact TwelveShort.isSylowIn_of_le D D.sylowM.le
      ne := (TwelveFourteen.wClos_zero_ne_self hTim hcat D hV hTI (by omega)).symm
      rk_gt := TwelveSeven.two_lt_rk_of_card hV.2.2.2 h8 }
  obtain ⟨hAT, g, hAg, hmq⟩ := hA
  have hAeq : A = conjSubgroup V₀ g :=
    (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup hV.2.2.2.isPGroup g) hAg).1 hmq
  rcases h93 h9 A ⟨g, hAeq⟩ hAT (by rw [hN]; exact hAS) with h1 | h1
  · exact absurd (h1.trans hN.le) (twelve_seven_three_one hTim hcat D h66 h88 h.2 hV hTI h8
      fun z hz hzc hz1 => (hCU z hz hzc hz1).1)
  · exact h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
