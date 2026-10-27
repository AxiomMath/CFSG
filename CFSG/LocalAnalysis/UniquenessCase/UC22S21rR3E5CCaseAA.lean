module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rN
import CFSG.GroupTheory.PRankLeOfSylowLe
import CFSG.LocalAnalysis.SectionRank.TwoGenerators
import CFSG.LocalAnalysis.UniquenessCase.UC22P20n
import CFSG.GroupTheory.WielandtProductBasic
import CFSG.Quasithin.H13.NQBlockPRankProduct
import CFSG.RankThree.OddKernel.CentralCoverComponentModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.GroupTheory.WielandtProduct
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem uc22r3e5c_inf_permutes_mul_eq {C T Y : Subgroup G} (hperm : Permutes C T)
    (hTY : T ≤ Y) (hYCT : Y ≤ C ⊔ T) :
    (Y : Set G) = ((Y ⊓ C) : Set G) * (T : Set G) := by
  have hsup : ((C ⊔ T : Subgroup G) : Set G) = (C : Set G) * (T : Set G) :=
    uc22p20n_coe_sup_of_perm hperm
  ext y
  constructor
  · intro hy
    have hy' : y ∈ ((C ⊔ T : Subgroup G) : Set G) := hYCT hy
    rw [hsup] at hy'
    obtain ⟨c, hc, t, ht, hct⟩ := hy'
    have htY : t ∈ Y := hTY ht
    have hcY : c = y * t⁻¹ := by
      rw [← hct]
      group
    have hcy : c ∈ Y := by
      rw [hcY]
      exact Y.mul_mem hy (Y.inv_mem htY)
    exact ⟨c, ⟨hcy, hc⟩, t, ht, hct⟩
  · rintro ⟨c, hc, t, ht, rfl⟩
    exact Y.mul_mem ((inf_le_left : Y ⊓ C ≤ Y) hc) (hTY ht)

private theorem uc22r3e5c_inf_permutes_inf_eq_bot {C T Y : Subgroup G}
    (hT : IsPGroup 2 ↥T) (hC : Odd (Nat.card C)) :
    (Y ⊓ C) ⊓ T = ⊥ := by
  have hcop : Nat.Coprime (Nat.card C) (Nat.card T) := by
    obtain ⟨k, hk⟩ := hT.exists_card_eq
    rw [hk]
    exact (Nat.coprime_two_right.mpr hC).pow_right k
  have hCT : C ⊓ T = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  have hle : (Y ⊓ C) ⊓ T ≤ C ⊓ T := inf_le_inf_right T inf_le_right
  exact le_bot_iff.mp (hle.trans (le_of_eq hCT))

private theorem uc22r3e5c_card_eq_mul_of_inf_permutes {C T Y : Subgroup G} (hperm : Permutes C T)
    (hTY : T ≤ Y) (hYCT : Y ≤ C ⊔ T) (hT : IsPGroup 2 ↥T) (hC : Odd (Nat.card C)) :
    Nat.card ↥Y = Nat.card ↥(Y ⊓ C) * Nat.card ↥T := by
  have hY_eq := uc22r3e5c_inf_permutes_mul_eq hperm hTY hYCT
  have hdisj := uc22r3e5c_inf_permutes_inf_eq_bot (Y := Y) hT hC
  have hcard := card_eq_mul_of_forall_mul (G := ↥Y)
    (A := (Y ⊓ C).subgroupOf Y) (B := T.subgroupOf Y) ?_ ?_
  · have h1 : Nat.card ↥((Y ⊓ C).subgroupOf Y) = Nat.card ↥(Y ⊓ C) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Y ⊓ C ≤ Y)).toEquiv
    have h2 : Nat.card ↥(T.subgroupOf Y) = Nat.card ↥T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTY).toEquiv
    rw [h1, h2] at hcard
    exact hcard
  · ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    constructor
    · rintro ⟨hxA, hxB⟩
      have hx1 : (x : G) ∈ Y ⊓ C := hxA
      have hx2 : (x : G) ∈ T := hxB
      have hx3 : (x : G) ∈ (Y ⊓ C) ⊓ T := ⟨hx1, hx2⟩
      rw [hdisj] at hx3
      exact Subtype.ext (Subgroup.mem_bot.mp hx3)
    · intro hx
      rw [hx]
      exact ⟨⟨Subgroup.one_mem Y, Subgroup.one_mem C⟩, Subgroup.one_mem T⟩
  · intro y
    have hy : (y : G) ∈ (Y : Set G) := y.2
    rw [hY_eq] at hy
    obtain ⟨a, ha, b, hb, hab⟩ := hy
    obtain ⟨haY, haC⟩ := Subgroup.mem_inf.mp ha
    have hbY : b ∈ Y := hTY hb
    have hbT : b ∈ T := hb
    let a' : ↥((Y ⊓ C).subgroupOf Y) := ⟨⟨a, haY⟩, Subgroup.mem_inf.mpr ⟨haY, haC⟩⟩
    let b' : ↥(T.subgroupOf Y) := ⟨⟨b, hbY⟩, hbT⟩
    refine ⟨a', a'.2, b', b'.2, ?_⟩
    exact Subtype.ext hab.symm

theorem uc22r3e5c_exists_index_eq_two_pow {C T Y : Subgroup G} (hperm : Permutes C T)
    (hTY : T ≤ Y) (hYCT : Y ≤ C ⊔ T) (hT : IsPGroup 2 ↥T) (hC : Odd (Nat.card C)) :
    ∃ k, ((Y ⊓ C).subgroupOf Y).index = 2 ^ k := by
  have hcard := uc22r3e5c_card_eq_mul_of_inf_permutes hperm hTY hYCT hT hC
  have hidx : ((Y ⊓ C).subgroupOf Y).index = Nat.card T := by
    have h1 : Nat.card ↥((Y ⊓ C).subgroupOf Y) = Nat.card ↥(Y ⊓ C) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Y ⊓ C ≤ Y)).toEquiv
    have h2 : Nat.card ((Y ⊓ C).subgroupOf Y) * ((Y ⊓ C).subgroupOf Y).index = Nat.card Y :=
      Subgroup.card_mul_index _
    rw [h1, hcard] at h2
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos) h2
  obtain ⟨k, hk⟩ := hT.exists_card_eq
  exact ⟨k, by rw [hidx, hk]⟩

private theorem uc22r3e5c_injective_comp_of_ker {H A B : Type} [Group H] [Group A] [Group B]
    (f : H →* A × B) {E : Subgroup H} (hinj : ∀ x ∈ E, f x = 1 → x = 1) :
    Function.Injective (f.comp E.subtype) := by
  intro x y hxy
  have h1 : f ((x : H) * (y : H)⁻¹) = 1 := by
    have := congrArg (fun z => z * (f (y : H))⁻¹) hxy
    simpa [map_mul, map_inv] using this
  have h2 : (x : H) * (y : H)⁻¹ = 1 := hinj _ (E.mul_mem x.2 (E.inv_mem y.2)) h1
  exact Subtype.ext (mul_inv_eq_one.mp h2)

theorem uc22r3e5c_card_le_sq_of_map_le_prod {H A B : Type} [Group H] [Group A] [Group B]
    [Finite H] [Finite A] [Finite B] {q : ℕ} (hq : q.Prime) {DA : Subgroup A} {DB : Subgroup B}
    (hA : IsCyclic ↥DA) (hB : IsCyclic ↥DB) (f : H →* A × B) {E : Subgroup H}
    (hinj : ∀ x ∈ E, f x = 1 → x = 1) (hEf : E.map f ≤ DA.prod DB) (hE : IsElemAbelian q E) :
    Nat.card E ≤ q ^ 2 := by
  have hinj' := uc22r3e5c_injective_comp_of_ker f hinj
  have hcard : Nat.card E = Nat.card (E.map f) := by
    have htop : (⊤ : Subgroup E).map (f.comp E.subtype) = E.map f := by
      ext x; constructor
      · rintro ⟨y, -, rfl⟩; exact ⟨y, y.2, rfl⟩
      · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, trivial, rfl⟩
    simpa [htop] using (Subgroup.card_map_of_injective (K := ⊤) hinj').symm
  have hmap_ea : IsElemAbelian q (E.map f) := CFSG.Open.IsElemAbelian.map hE f
  have hrank_le : CFSG.Open.pRank q (E.map f) ≤ 2 := by
    have hDA : CFSG.Open.pRank q DA ≤ 1 := CFSG.SectionRank.pRank_le_one_of_isCyclic hq hA
    have hDB : CFSG.Open.pRank q DB ≤ 1 := CFSG.SectionRank.pRank_le_one_of_isCyclic hq hB
    have hprod : CFSG.Open.pRank q (DA.prod DB) ≤ 2 := by
      have e : ↥(DA.prod DB) ≃* (↥DA × ↥DB) := Subgroup.prodEquiv DA DB
      have h := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hq.one_lt e
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (DA.prod DB)] at h
      rw [h]
      calc CFSG.Open.pRank q (⊤ : Subgroup (↥DA × ↥DB))
          ≤ CFSG.Open.pRank q (⊤ : Subgroup ↥DA) +
            CFSG.Open.pRank q (⊤ : Subgroup ↥DB) :=
            CFSG.Quasithin.H13.NQBlock.pRank_prod_le hq
        _ = CFSG.Open.pRank q DA + CFSG.Open.pRank q DB := by
            rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (DA),
              ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (DB)]
        _ ≤ 2 := by omega
    exact le_trans (CFSG.SectionRank.pRank_mono hq.one_lt hEf) hprod
  calc Nat.card E = Nat.card (E.map f) := hcard
    _ ≤ q ^ CFSG.Open.pRank q (E.map f) :=
      CFSG.RankThree.OddKernel.card_le_pow_pRank_of_le hq hmap_ea (le_refl _)
    _ ≤ q ^ 2 := Nat.pow_le_pow_right hq.pos hrank_le

private theorem uc22r3e5c_isSylowOf_of_two_pow_index {Y A S : Subgroup G} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hAY : A ≤ Y) (hidx : ∃ k, (A.subgroupOf Y).index = 2 ^ k)
    (hS : CFSG.ABGLocalTools.IsSylowOf q S A) : CFSG.ABGLocalTools.IsSylowOf q S Y := by
  have hq_fact : Fact q.Prime := ⟨hq⟩
  have hSA : S ≤ A := hS.le
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_trans hSA hAY, hS.isPGroup, ?_⟩
  have h1 : ¬ q ∣ (A.subgroupOf Y).index := by
    obtain ⟨k, hk⟩ := hidx
    rw [hk]
    intro h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))
  have h2 : ¬ q ∣ (S.subgroupOf A).index := (CFSG.ABGLocalTools.isSylowOf_iff.mp hS).2.2
  have h3 : ¬ q ∣ S.relIndex Y := by
    rw [← Subgroup.relIndex_mul_relIndex S A Y hSA hAY]
    intro h
    rcases (Nat.Prime.dvd_mul hq).1 h with h1' | h2'
    · exact h2 h1'
    · exact h1 h2'
  exact h3

theorem uc22r3e5c_pRank_le_two_of_relIndex {Y A C : Subgroup G} (hAY : A ≤ Y) (hAC : A ≤ C)
    (hidx : ∃ k, (A.subgroupOf Y).index = 2 ^ k)
    (hC : ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ E : Subgroup G, E ≤ C → IsElemAbelian q E →
      Nat.card E ≤ q ^ 2) :
    ∀ q ∈ piSet Y, q ≠ 2 → CFSG.Open.pRank q Y ≤ 2 := by
  intro q hqY hq2
  have hq_prime : q.Prime := hqY.1
  have hq_fact : Fact q.Prime := ⟨hq_prime⟩
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf q A
  have hSY_sylow := uc22r3e5c_isSylowOf_of_two_pow_index hq_prime hq2 hAY hidx hS
  have hrank_le : CFSG.Open.pRank q Y ≤ CFSG.Open.pRank q C :=
    CFSG.pRank_le_of_isSylowOf_le hq_prime (le_trans hS.le hAY) hSY_sylow (le_trans hS.le hAC)
  have hC_rank : CFSG.Open.pRank q C ≤ 2 :=
    CFSG.SectionRank.pRank_le hq_prime.one_lt (hC q hq_prime hq2)
  exact le_trans hrank_le hC_rank

theorem uc22r3e5c_false_of_le_hSet {D : Data G} {Ch : Choice2011 G} (h211 : S21_1 D Ch)
    (h1930 : H1930 D) (c : Ctx21 D Ch) {C H : Subgroup G} (hH : H ∈ hSet D.T D.M)
    (hCodd : Odd (Nat.card C)) (hCcomm : IsMulCommutative ↥C) (hperm : Permutes C D.T)
    (hCTs : Group.IsSolvable ↥(C ⊔ D.T))
    (hCrk : ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ E : Subgroup G, E ≤ C → IsElemAbelian q E →
      Nat.card E ≤ q ^ 2)
    {A : Subgroup G} (hAC : A ≤ C) (hAH : A ≤ H) (hAp : (Nat.card A).Prime)
    (hA2 : Nat.card A ≠ 2) (hAU : A ∈ uniqueSet D.M) : False := by
  let Y := A ⊔ D.T
  have hYCT : Y ≤ C ⊔ D.T := sup_le (le_trans hAC le_sup_left) le_sup_right
  have hCTs' : Group.IsSolvable ↥(C ⊔ D.T) := hCTs
  have hYs : Group.IsSolvable ↥Y :=
    solvable_of_solvable_injective (f := Subgroup.inclusion hYCT)
      (Subgroup.inclusion_injective hYCT)
  have hY_index : ∃ k, ((Y ⊓ C).subgroupOf Y).index = 2 ^ k := by
    apply uc22r3e5c_exists_index_eq_two_pow hperm le_sup_right hYCT
    exact D.sylowM.isPGroup
    exact hCodd
  have hhall : IsHallOddIn (Y ⊓ C) Y := by
    refine ⟨inf_le_left, ?_, hY_index⟩
    exact Odd.of_dvd_nat hCodd (Subgroup.card_dvd_of_le inf_le_right)
  have hcomm : IsMulCommutative ↥(Y ⊓ C) := isMulCommutative_anti inf_le_right
  have hrank : ∀ q ∈ piSet Y, q ≠ 2 → CFSG.Open.pRank q Y ≤ 2 :=
    uc22r3e5c_pRank_le_two_of_relIndex (A := Y ⊓ C) inf_le_left inf_le_right hY_index hCrk
  have hM := (h211 h1930 c A hAp hA2 hYs ⟨_, hhall, hcomm⟩ hrank hAU).1
  exact uc22s21rn_not_le_of_uniqueMax D hH hM (sup_le hAH hH.1)

end CFSG.LocalAnalysis.UniquenessCase.UC22
