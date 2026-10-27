module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen4Aux
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
import CFSG.LocalAnalysis.UniquenessCase.UCFront09l

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem L9_le_of_le {Y H : Subgroup G} (hYH : Y ≤ H) : L9 Y H ≤ H :=
  iSup_le fun h => by
    rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem h.2 (hYH (opp_le_self 3 Y hx))) (H.inv_mem h.2)

omit [Finite G] in
theorem le_normalizer_L9 (Y H : Subgroup G) : H ≤ normalizer (L9 Y H : Set G) := by
  have key : ∀ g : ↥H, (L9 Y H).map (MulAut.conj (g : G)).toMonoidHom ≤ L9 Y H := by
    intro g
    unfold L9
    rw [Subgroup.map_iSup]
    refine iSup_le fun h => ?_
    rw [Subgroup.map_map]
    have e : (MulAut.conj (g : G)).toMonoidHom.comp (MulAut.conj (h : G)).toMonoidHom =
        (MulAut.conj ((g * h : ↥H) : G)).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [e]
    exact le_iSup (fun h : ↥H => (Opp 3 Y).map (MulAut.conj (h : G)).toMonoidHom) (g * h)
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact key ⟨g, hg⟩ (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
  · intro hx
    have := key ⟨g⁻¹, H.inv_mem hg⟩ (Subgroup.mem_map.2 ⟨g * x * g⁻¹, hx, rfl⟩)
    simpa [MulAut.conj_apply, mul_assoc] using this

omit [Finite G] in
theorem L9_le_of_forall {Y H K : Subgroup G}
    (hK : ∀ x ∈ L9 Y H, (∃ k : ℕ, x ^ 3 ^ k = 1) → x ∈ K) : L9 Y H ≤ K := by
  refine iSup_le fun h => ?_
  unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
  rw [MonoidHom.map_closure, closure_le]
  rintro _ ⟨y, ⟨hyY, k, hk⟩, rfl⟩
  refine hK _ ?_ ⟨k, ?_⟩
  · refine le_iSup (fun h : ↥H => (Opp 3 Y).map (MulAut.conj (h : G)).toMonoidHom) h ?_
    refine mem_map_of_mem _ ?_
    unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
    exact subset_closure ⟨hyY, k, hk⟩
  · rw [← map_pow, ← hk, pow_orderOf_eq_one, map_one]

omit [Finite G] in
theorem exists_surjective_Lbar9 {Y H : Subgroup G} (hYH : Y ≤ H) :
    ∃ φ : ↥(L9 Y H) →* Lbar9 Y H, Function.Surjective φ ∧
      ∀ l : ↥(L9 Y H), φ l = 1 ↔ (l : G) ∈ I9 H := by
  have hLH := L9_le_of_le hYH
  let π : ↥H →* Hbar9 H := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)
  refine ⟨(π.comp (inclusion hLH)).codRestrict (img9 H (L9 Y H))
    fun l => ⟨inclusion hLH l, l.2, rfl⟩, ?_, fun l => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  · have h1 : π (inclusion hLH l) = 1 := congrArg Subtype.val h
    exact mem_map.2 ⟨_, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
  · obtain ⟨y, hy, hyl⟩ := mem_map.1 h
    have e : y = inclusion hLH l := Subtype.ext hyl
    exact Subtype.ext ((QuotientGroup.eq_one_iff (inclusion hLH l)).2 (e ▸ hy))

theorem coprime_card_of_map_le_I9 {H K : Subgroup G} {P : Subgroup ↥K}
    (hP : P.map K.subtype ≤ I9 H) : Nat.Coprime 3 (Nat.card P) := by
  have hd := card_dvd_of_le hP
  rw [card_map_of_injective K.subtype_injective] at hd
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h3 =>
    not_dvd_card_I9 H (h3.trans hd)

theorem le_I9_or_le_of_isSimpleGroup {Y H N : Subgroup G} (hYH : Y ≤ H) (hNL : N ≤ L9 Y H)
    (hLN : L9 Y H ≤ normalizer (N : Set G)) (hs : IsSimpleGroup (Lbar9 Y H)) :
    N ≤ I9 H ∨ L9 Y H ≤ N := by
  obtain ⟨φ, hφ, hker⟩ := exists_surjective_Lbar9 hYH
  have hn : (N.subgroupOf (L9 Y H)).Normal := (normal_subgroupOf_iff_le_normalizer hNL).2 hLN
  haveI hK : ((N.subgroupOf (L9 Y H)).map φ).Normal := hn.map φ hφ
  rcases hs.eq_bot_or_eq_top_of_normal ((N.subgroupOf (L9 Y H)).map φ) with h | h
  · left
    intro n hnN
    have hm : φ ⟨n, hNL hnN⟩ ∈ (N.subgroupOf (L9 Y H)).map φ := mem_map_of_mem _ hnN
    rw [h, mem_bot] at hm
    exact (hker _).1 hm
  · right
    have hNI : N ≤ normalizer (I9 H : Set G) := (hNL.trans (L9_le_of_le hYH)).trans
      (le_normalizer_I9 H)
    refine L9_le_of_forall fun l hl ⟨k, hk⟩ => ?_
    have hlN : φ ⟨l, hl⟩ ∈ (N.subgroupOf (L9 Y H)).map φ := h ▸ mem_top _
    obtain ⟨⟨n, hnL⟩, hnN, hnl⟩ := mem_map.1 hlN
    have hi : n⁻¹ * l ∈ I9 H := (hker (⟨n, hnL⟩⁻¹ * ⟨l, hl⟩)).1 (by
      rw [map_mul, map_inv, hnl, inv_mul_cancel])
    have hcop : Nat.Coprime (Nat.card ↥(L9 Y H ⊓ I9 H)) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h3 =>
        not_dvd_card_I9 H (h3.trans (card_dvd_of_le inf_le_right))).symm
    refine CFSG.AGLEmbedding.L34FF.mem_of_mem_sup_of_pow_prime_pow (inf_le_left.trans hLN) hcop
      ?_ hk
    rw [show l = n * (n⁻¹ * l) by group]
    exact mul_mem_sup hnN ⟨by simpa using (L9 Y H).mul_mem ((L9 Y H).inv_mem hnL) hl, hi⟩

theorem ne_top_of_hyp97 {D : Data G} {Y H D₃ S : Subgroup G} (hY : Hyp97 D Y H D₃ S)
    (hR : pCoreOf 2 Y ≠ ⊥) : H ≠ ⊤ := by
  haveI := D.standing.simple
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : H ≠ ⊥ := by
    intro h
    apply hR
    rw [← le_bot_iff, ← h]
    exact (CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hY.1.2.1.1
  have hne := CFSG.LocalAnalysis.UniquenessCase.PartTwo.pCoreOf_ne_bot_of_fstar hY.2.2.1.2 hH
  intro htop
  refine CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab
    (show IsTwoLocal (normalizer (pCoreOf 2 H : Set G)) from
      ⟨pCoreOf 2 H, hne, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H, rfl⟩) ?_
  exact top_le_iff.1 (htop.ge.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))

theorem normalizer_le_of_hyp97 {D : Data G} (h910 : R910 D) {Y H D₃ S : Subgroup G}
    (hY : Hyp97 D Y H D₃ S) (hSM : ¬ IsSylowOf 2 S D.M) {C : Subgroup G} (hCS : C ≤ S)
    (hC : C ≠ ⊥) (hchar : (C.subgroupOf S).Characteristic)
    (hYC : Y ≤ normalizer (C : Set G)) : normalizer (C : Set G) ≤ D.M := by
  have hSY : IsSylowOf 2 S Y := hY.2.2.2
  have hNSC := normalizer_le_normalizer_of_char hCS hchar
  have hSMC : ¬ IsSylowOf 2 S (D.M ⊓ normalizer (C : Set G)) := fun h =>
    hSM (isSylowOf_of_inf_normalizer_le (hSY.le.trans hY.1.1.1) (inf_le_inf_left _ hNSC) h)
  have hU : calMOf (D.M ⊓ normalizer (C : Set G)) = {D.M} := h910 Y hY.2.1 C hC
    (hCS.trans hSY.le) ((normal_subgroupOf_iff_le_normalizer (hCS.trans hSY.le)).2 hYC)
    ⟨S, hSY, hSMC⟩
  have hloc : IsTwoLocal (normalizer (C : Set G)) := ⟨C, hC, hSY.isPGroup.to_le hCS, rfl⟩
  obtain ⟨M', hCM', hmax⟩ := Finite.exists_le_maximal hloc
  have hmem : M' ∈ calMOf (D.M ⊓ normalizer (C : Set G)) :=
    ⟨⟨hmax.1, fun K hK hMK => le_antisymm (hmax.2 hK hMK) hMK⟩, inf_le_right.trans hCM'⟩
  rw [hU] at hmem
  exact hmem ▸ hCM'

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
