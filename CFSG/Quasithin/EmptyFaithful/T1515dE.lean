module

public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Background.InternalSecTwo
public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.InternalSec
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_thompsonJ_eq1527d {S L Y M : Subgroup G} (hY : Y = L ⊔ S)
    (hS : IsSylowTwoOf S Y) (hSN : S ≤ Subgroup.normalizer (L : Set G)) (hperf : ⁅L, L⁆ = L)
    (hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L))
    (hNJ : Subgroup.normalizer (thompsonJ S : Set G) ≤ M) (hLM : ¬ L ≤ M) :
    ⁅L, thompsonJ S⁆ = L := by
  have hLY : L ≤ Y := hY ▸ le_sup_left
  have hJS : thompsonJ S ≤ S := thompsonJ_le_self151 S
  have hJN : thompsonJ S ≤ Subgroup.normalizer (L : Set G) := hJS.trans hSN
  have hNL : ⁅L, thompsonJ S⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_left.mp hJN
  have hPN : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 L
  by_cases hNP : ⁅L, thompsonJ S⁆ ≤ pCoreOf 2 L
  · exfalso
    have hYN : Y ≤ Subgroup.normalizer (L : Set G) := hY ▸ sup_le Subgroup.le_normalizer hSN
    have hPY : pCoreOf 2 L ≤ pCoreOf 2 Y :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLY) (hYN.trans hPN)
        (pCoreOf_isPGroup 2 L)
    have hRS : pCoreOf 2 Y ≤ S := pCoreOf_le_of_isSylowTwoOf hS
    have hPS : pCoreOf 2 L ≤ S := hPY.trans hRS
    have hJP : thompsonJ S ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := hJN.trans hPN
    have hQS : pCoreOf 2 L ⊔ thompsonJ S ≤ S := sup_le hPS hJS
    have hQ2 : IsPGroup 2 ↥(pCoreOf 2 L ⊔ thompsonJ S) := hS.2.1.to_le hQS
    have hQmem : ∀ x ∈ pCoreOf 2 L ⊔ thompsonJ S,
        ∃ p ∈ pCoreOf 2 L, ∃ j ∈ thompsonJ S, p * j = x := fun x hx => by
      have : x ∈ (pCoreOf 2 L : Set G) * (thompsonJ S : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left (pCoreOf 2 L) (thompsonJ S) hJP]
        exact hx
      obtain ⟨p, hp, j, hj, h⟩ := this
      exact ⟨p, hp, j, hj, h⟩
    have hLQ : ∀ l ∈ L, ∀ q ∈ pCoreOf 2 L ⊔ thompsonJ S,
        l * q * l⁻¹ ∈ pCoreOf 2 L ⊔ thompsonJ S := by
      intro l hl q hq
      obtain ⟨p, hp, j, hj, rfl⟩ := hQmem q hq
      have h1 : l * p * l⁻¹ ∈ pCoreOf 2 L :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L hl) p).mp hp
      have h2 : ⁅l, j⁆ ∈ pCoreOf 2 L := hNP (Subgroup.commutator_mem_commutator hl hj)
      have e : l * (p * j) * l⁻¹ = (l * p * l⁻¹) * ⁅l, j⁆ * j := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left h1)
        (Subgroup.mem_sup_left h2)) (Subgroup.mem_sup_right hj)
    have hSQ : ∀ s ∈ S, ∀ q ∈ pCoreOf 2 L ⊔ thompsonJ S,
        s * q * s⁻¹ ∈ pCoreOf 2 L ⊔ thompsonJ S := by
      intro s hs q hq
      obtain ⟨p, hp, j, hj, rfl⟩ := hQmem q hq
      have h1 : s * p * s⁻¹ ∈ pCoreOf 2 L :=
        (Subgroup.mem_normalizer_iff.mp (hSN.trans hPN hs) p).mp hp
      have h2 : s * j * s⁻¹ ∈ thompsonJ S :=
        (Subgroup.mem_normalizer_iff.mp
          (normalizer_le_normalizer_thompsonJ S (Subgroup.le_normalizer hs)) j).mp hj
      have e : s * (p * j) * s⁻¹ = (s * p * s⁻¹) * (s * j * s⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
    have hQN : ∀ g : G, (g ∈ L ∨ g ∈ S) →
        g ∈ Subgroup.normalizer ((pCoreOf 2 L ⊔ thompsonJ S : Subgroup G) : Set G) := by
      intro g hg
      have hgq : ∀ q ∈ pCoreOf 2 L ⊔ thompsonJ S, g * q * g⁻¹ ∈ pCoreOf 2 L ⊔ thompsonJ S := by
        rcases hg with hg | hg
        exacts [hLQ g hg, hSQ g hg]
      have hgq' : ∀ q ∈ pCoreOf 2 L ⊔ thompsonJ S, g⁻¹ * q * g ∈ pCoreOf 2 L ⊔ thompsonJ S := by
        rcases hg with hg | hg
        · simpa using hLQ g⁻¹ (L.inv_mem hg)
        · simpa using hSQ g⁻¹ (S.inv_mem hg)
      rw [Subgroup.mem_normalizer_iff]
      intro q
      exact ⟨fun hq => hgq q hq, fun hq => by simpa [mul_assoc] using hgq' _ hq⟩
    have hYQ : Y ≤ Subgroup.normalizer ((pCoreOf 2 L ⊔ thompsonJ S : Subgroup G) : Set G) :=
      hY ▸ sup_le (fun g hg => hQN g (Or.inl hg)) (fun g hg => hQN g (Or.inr hg))
    have hQR : pCoreOf 2 L ⊔ thompsonJ S ≤ pCoreOf 2 Y :=
      le_pCoreOf_of_le_normalizer 2 (hQS.trans hS.1) hYQ hQ2
    have hJR : thompsonJ S ≤ pCoreOf 2 Y := le_sup_right.trans hQR
    have hJeq : thompsonJ (pCoreOf 2 Y) = thompsonJ S := B6.thompsonJ_eq_of_le hJR hRS
    have hYR : Y ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) := le_normalizer_pCoreOf 2 Y
    have hYJ : Y ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
      rw [← hJeq]
      exact hYR.trans (normalizer_le_normalizer_thompsonJ _)
    exact hLM ((hLY.trans hYJ).trans hNJ)
  · have hN' : (⁅L, thompsonJ S⁆.subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr
        (Subgroup.normalizer_commutator_ge_left L (thompsonJ S))
    let Nbar : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
      (⁅L, thompsonJ S⁆.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
    have hNbar : Nbar.Normal := Subgroup.Normal.map hN' _ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Nbar with h | h
    · exfalso
      apply hNP
      intro x hx
      have hxL : x ∈ L := hNL hx
      have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨x, hxL⟩ ∈ Nbar := ⟨⟨x, hxL⟩, hx, rfl⟩
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
      exact ⟨⟨x, hxL⟩, by exact hmem, rfl⟩
    · have hall : ∀ x : ↥L, ∃ n ∈ ⁅L, thompsonJ S⁆.subgroupOf L, ∃ p ∈ CFSG.pCore 2 ↥L,
          x = n * p := by
        intro x
        have hx : QuotientGroup.mk' (CFSG.pCore 2 ↥L) x ∈ Nbar := by rw [h]; trivial
        obtain ⟨n, hn, hnx⟩ := hx
        refine ⟨n, hn, n⁻¹ * x, ?_, by simp⟩
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hnx
        exact QuotientGroup.eq.1 hnx
      have hpg : IsPGroup 2 (↥L ⧸ ⁅L, thompsonJ S⁆.subgroupOf L) := by
        intro y
        induction y using QuotientGroup.induction_on with
        | H x =>
          obtain ⟨n, hn, p, hp, rfl⟩ := hall x
          obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨p, hp⟩
          refine ⟨k, ?_⟩
          have hp1 : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
          have hn1 : (QuotientGroup.mk n : ↥L ⧸ ⁅L, thompsonJ S⁆.subgroupOf L) = 1 :=
            (QuotientGroup.eq_one_iff n).2 hn
          rw [QuotientGroup.mk_mul, hn1, one_mul, ← QuotientGroup.mk_pow, hp1]
          rfl
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hnil : Group.IsNilpotent (↥L ⧸ ⁅L, thompsonJ S⁆.subgroupOf L) := hpg.isNilpotent
      have hperfL : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 hperf
      have hperfQ : Group.IsPerfect (↥L ⧸ ⁅L, thompsonJ S⁆.subgroupOf L) :=
        Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      have hsub : Subsingleton (↥L ⧸ ⁅L, thompsonJ S⁆.subgroupOf L) := by
        by_contra hns
        rw [not_subsingleton_iff_nontrivial] at hns
        exact Group.IsPerfect.not_isSolvable (↥L ⧸ ⁅L, thompsonJ S⁆.subgroupOf L)
          (inferInstance : Group.IsSolvable _)
      have hidx : (⁅L, thompsonJ S⁆.subgroupOf L).index = 1 := by
        rw [Subgroup.index]
        exact Nat.card_of_subsingleton (1 : ↥L ⧸ ⁅L, thompsonJ S⁆.subgroupOf L)
      have htop : ⁅L, thompsonJ S⁆.subgroupOf L = ⊤ := Subgroup.index_eq_one.1 hidx
      exact le_antisymm hNL (Subgroup.subgroupOf_eq_top.1 htop)

end CFSG.Quasithin
