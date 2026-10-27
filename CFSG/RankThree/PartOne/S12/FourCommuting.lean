module

public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionRank

public section

namespace CFSG.RankThree.PartOne

namespace FourCommutingRank

open Subgroup

variable {G : Type*} [Group G]

private theorem isPGroup_sup_four {p : ℕ} {H : Fin 4 → Subgroup G} (hp : ∀ i, IsPGroup p (H i))
    (hc : ∀ i j, i ≠ j → H i ≤ centralizer (H j : Set G)) :
    IsPGroup p (H 0 ⊔ H 1 ⊔ H 2 ⊔ H 3 : Subgroup G) := by
  have key : ∀ (A : Subgroup G) (j : Fin 4), IsPGroup p A → A ≤ centralizer (H j : Set G) →
      IsPGroup p (A ⊔ H j : Subgroup G) := fun A j hA hAj =>
    hA.to_sup_of_normal_right' (hp j) (hAj.trans (centralizer_le_normalizer _))
  have h1 := key (H 0) 1 (hp 0) (hc 0 1 (by decide))
  have h2 := key (H 0 ⊔ H 1) 2 h1 (sup_le (hc 0 2 (by decide)) (hc 1 2 (by decide)))
  exact key (H 0 ⊔ H 1 ⊔ H 2) 3 h2
    (sup_le (sup_le (hc 0 3 (by decide)) (hc 1 3 (by decide))) (hc 2 3 (by decide)))

private theorem mem_normalizer_sup_four [Finite G] {H : Fin 4 → Subgroup G} {g : G}
    (h : ∀ i, ∀ n ∈ H i, g * n * g⁻¹ ∈ H i) :
    g ∈ normalizer ((H 0 ⊔ H 1 ⊔ H 2 ⊔ H 3 : Subgroup G) : Set G) := by
  have hl0 : H 0 ≤ H 0 ⊔ H 1 ⊔ H 2 ⊔ H 3 := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hl1 : H 1 ≤ H 0 ⊔ H 1 ⊔ H 2 ⊔ H 3 := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hl2 : H 2 ≤ H 0 ⊔ H 1 ⊔ H 2 ⊔ H 3 := le_sup_right.trans le_sup_left
  have hl3 : H 3 ≤ H 0 ⊔ H 1 ⊔ H 2 ⊔ H 3 := le_sup_right
  have hS : (H 0 ⊔ H 1 ⊔ H 2 ⊔ H 3 : Subgroup G) ≤
      (H 0 ⊔ H 1 ⊔ H 2 ⊔ H 3 : Subgroup G).comap (MulAut.conj g).toMonoidHom :=
    sup_le (sup_le (sup_le (fun n hn => hl0 (h 0 n hn)) (fun n hn => hl1 (h 1 n hn)))
      (fun n hn => hl2 (h 2 n hn))) (fun n hn => hl3 (h 3 n hn))
  exact mem_normalizer_fintype fun n hn => hS hn

private theorem elemAbelian_iSup_zpowers_four {r : ℕ} (hr : r.Prime) {K : Fin 4 → Subgroup G}
    (hcomm : ∀ i j, i ≠ j → K i ≤ centralizer (K j : Set G)) {y : Fin 4 → G}
    (hyK : ∀ i, y i ∈ K i) (hyo : ∀ i, orderOf (y i) = r)
    (hy : ∀ i, y i ∉ centralizer (K i : Set G)) :
    IsMulCommutative (⨆ i, zpowers (y i) : Subgroup G) ∧
      (∀ g ∈ (⨆ i, zpowers (y i) : Subgroup G), g ^ r = 1) ∧
      Nat.card (⨆ i, zpowers (y i) : Subgroup G) = r ^ 4 := by
  have hA : ∀ i, Nat.card (zpowers (y i)) = r := fun i => by rw [Nat.card_zpowers, hyo i]
  have hAK : ∀ i, zpowers (y i) ≤ K i := fun i => zpowers_le.2 (hyK i)
  have hcommA : Pairwise fun i j : Fin 4 =>
      ∀ a b : G, a ∈ zpowers (y i) → b ∈ zpowers (y j) → Commute a b :=
    fun i j hij a b ha hb => (mem_centralizer_iff.1 (hcomm i j hij (hAK i ha)) b (hAK j hb)).symm
  have hind : iSupIndep fun i => zpowers (y i) := by
    intro i
    rw [Subgroup.disjoint_def]
    intro z hz hz'
    have hzc : z ∈ centralizer (K i : Set G) :=
      (iSup₂_le fun j hj => (hAK j).trans (hcomm j i hj) :
        (⨆ (j) (_ : j ≠ i), zpowers (y j) : Subgroup G) ≤ centralizer (K i : Set G)) hz'
    have : Fact (Nat.card (zpowers (y i))).Prime := ⟨by rw [hA i]; exact hr⟩
    rcases ((centralizer (K i : Set G)).subgroupOf (zpowers (y i))).eq_bot_or_eq_top_of_prime_card
      with h | h
    · have hz1 : (⟨z, hz⟩ : zpowers (y i)) ∈
          (centralizer (K i : Set G)).subgroupOf (zpowers (y i)) := hzc
      rw [h] at hz1
      exact congrArg Subtype.val (Subgroup.mem_bot.1 hz1)
    · have hyi : (⟨y i, mem_zpowers _⟩ : zpowers (y i)) ∈
          (centralizer (K i : Set G)).subgroupOf (zpowers (y i)) := by
        rw [h]
        exact Subgroup.mem_top _
      exact absurd (Subgroup.mem_subgroupOf.1 hyi) (hy i)
  obtain ⟨f, hinj, hrange⟩ : ∃ f : (∀ i, zpowers (y i)) →* G,
      Function.Injective f ∧ f.range = ⨆ i, zpowers (y i) :=
    ⟨noncommPiCoprod hcommA, injective_noncommPiCoprod_of_iSupIndep hind, noncommPiCoprod_range⟩
  have hexp : ∀ a : (∀ i, zpowers (y i)), a ^ r = 1 := by
    intro a
    funext i
    have := pow_card_eq_one' (x := a i)
    rwa [hA i] at this
  rw [← hrange]
  refine ⟨inferInstance, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow, hexp, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_pi]
    simp [hA]

private theorem four_le_localRank_aux [Finite G] {r : ℕ} (hr : r.Prime) {K V : Fin 4 → Subgroup G}
    (hcomm : ∀ i j, i ≠ j → K i ≤ centralizer (K j : Set G))
    (hVK : ∀ i, V i ≤ K i) (hV2 : ∀ i, IsPGroup 2 (V i)) (hV0 : V 0 ≠ ⊥) {y : Fin 4 → G}
    (hyK : ∀ i, y i ∈ K i) (hyo : ∀ i, orderOf (y i) = r)
    (hyV : ∀ i, ∀ n ∈ V i, y i * n * (y i)⁻¹ ∈ V i)
    (hy : ∀ i, ∃ v ∈ V i, y i * v ≠ v * y i) :
    4 ≤ CFSG.Assembly.RankThreeEven.localRank r G := by
  have hVc : ∀ i j, i ≠ j → V i ≤ centralizer (V j : Set G) := fun i j hij =>
    (hVK i).trans ((hcomm i j hij).trans (centralizer_le (SetLike.coe_subset_coe.2 (hVK j))))
  have hS2 : IsPGroup 2 (V 0 ⊔ V 1 ⊔ V 2 ⊔ V 3 : Subgroup G) := isPGroup_sup_four hV2 hVc
  have hS0 : (V 0 ⊔ V 1 ⊔ V 2 ⊔ V 3 : Subgroup G) ≠ ⊥ := fun h =>
    hV0 (le_bot_iff.1 (h ▸ le_sup_left.trans (le_sup_left.trans le_sup_left)))
  have hyc : ∀ i, y i ∉ centralizer (K i : Set G) := by
    intro i hc
    obtain ⟨v, hv, hne⟩ := hy i
    exact hne (mem_centralizer_iff.1 hc v (hVK i hv)).symm
  obtain ⟨hXc, hXe, hXr⟩ := elemAbelian_iSup_zpowers_four hr hcomm hyK hyo hyc
  have hXU : (⨆ i, zpowers (y i) : Subgroup G) ≤
      normalizer ((V 0 ⊔ V 1 ⊔ V 2 ⊔ V 3 : Subgroup G) : Set G) := by
    refine iSup_le fun i => zpowers_le.2 (mem_normalizer_sup_four fun j n hn => ?_)
    by_cases hij : i = j
    · subst hij
      exact hyV i n hn
    · have := mem_centralizer_iff.1 (hcomm i j hij (hyK i)) n (hVK j hn)
      rw [← this, mul_inv_cancel_right]
      exact hn
  exact Sec9Excl.le_localRank_of_normalizes hr.one_lt hS0 hS2 hXc hXe hXr hXU

end FourCommutingRank

theorem four_le_localRank_of_commuting {G : Type*} [Group G] [Finite G] {r : ℕ}
    (hr : r.Prime) (K : Fin 4 → Subgroup G)
    (hcomm : ∀ i j, i ≠ j → K i ≤ Subgroup.centralizer (K j : Set G))
    (hU : ∀ i, ∃ U : Subgroup (K i), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∃ x ∈ Subgroup.normalizer (U : Set (K i)), orderOf x = r ∧ ∃ u ∈ U, x * u * x⁻¹ ≠ u) :
    4 ≤ CFSG.Assembly.RankThreeEven.localRank r G := by
  choose U hU0 hU2 x hxN hxo u huU hxu using hU
  refine FourCommutingRank.four_le_localRank_aux hr hcomm (V := fun i => (U i).map (K i).subtype)
    (fun i => Subgroup.map_subtype_le _) (fun i => (hU2 i).map _)
    (fun h => hU0 0
      ((Subgroup.map_eq_bot_iff_of_injective (U 0) (K 0).subtype_injective).1 h))
    (y := fun i => ((x i : K i) : G)) (fun i => (x i).2)
    (fun i => (Subgroup.orderOf_coe (x i)).trans (hxo i)) ?_ ?_
  · rintro i _ ⟨n, hn, rfl⟩
    exact ⟨x i * n * (x i)⁻¹, (hxN i n).1 hn, rfl⟩
  · intro i
    refine ⟨u i, ⟨u i, huU i, rfl⟩, fun h => hxu i ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    exact Subtype.ext h

end CFSG.RankThree.PartOne
