module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Leaves
import CFSG.GroupTheory.PGroup.ElemAbelianSq

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Blueprint (LieModel)
open CFSG.Open

@[expose] def ClassLeaf {G : Type} [Group G] (H : Subgroup G) (z₀ : G) : Prop :=
  ∀ z ∈ H, orderOf z = 3 → ∀ X : Subgroup G, X ≤ H → z ∈ X →
    X ≤ Subgroup.centralizer {z} → ⁅X, X⁆ = X →
    ∃ g ∈ H, g * z * g⁻¹ = z₀ ∨ g * z * g⁻¹ = z₀⁻¹

@[expose] def CompLeaf {G : Type} [Group G] (H : Subgroup G) (z₀ : G) (X₀ : Subgroup G) : Prop :=
  ∀ X : Subgroup G, X ≤ H → z₀ ∈ X → X ≤ Subgroup.centralizer {z₀} → ⁅X, X⁆ = X → X ≤ X₀

@[expose] def GenLeaf {G : Type} [Group G] (H : Subgroup G) (z₀ t₀ : G) : Prop :=
  H ⊓ Subgroup.centralizer {z₀} ⊔ H ⊓ Subgroup.centralizer {t₀} ⊔
    H ⊓ Subgroup.centralizer {z₀ * t₀} ⊔ H ⊓ Subgroup.centralizer {z₀ * t₀ ^ 2} = H

theorem exists_zpowers_of_card_three {M : Type} [Group M] [Finite M] {Z : Subgroup M}
    (hZ : Nat.card Z = 3) : ∃ z ∈ Z, orderOf z = 3 ∧ Z = Subgroup.zpowers z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 3 (by rw [hZ])
  refine ⟨z, z.2, by rw [Subgroup.orderOf_coe, hz], ?_⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.zpowers_le]; exact z.2
  · rw [hZ, Nat.card_zpowers, Subgroup.orderOf_coe, hz]

theorem commutator_self_of_perfect {M : Type} [Group M] {X : Subgroup M}
    (h : commutator X = ⊤) : ⁅X, X⁆ = X := by
  have := map_commutator_eq (f := X.subtype)
  rw [h, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
  exact this.symm

theorem pos_G {G : Type} [Group G] [Finite G] {H : Subgroup G} {Z X : Subgroup H}
    (h : Pos H Z X) {z : H} (hz : Z = Subgroup.zpowers z) :
    X.map H.subtype ≤ H ∧ (z : G) ∈ X.map H.subtype ∧
      X.map H.subtype ≤ Subgroup.centralizer {(z : G)} ∧
      ⁅X.map H.subtype, X.map H.subtype⁆ = X.map H.subtype := by
  obtain ⟨-, hZX, hXC, -, hqs, -, -⟩ := h
  have hzZ : z ∈ Z := hz ▸ Subgroup.mem_zpowers z
  refine ⟨?_, ⟨z, hZX hzZ, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩; exact x.2
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have := Subgroup.mem_centralizer_iff.mp (hXC hx) z hzZ
    simpa using congrArg Subtype.val this
  · rw [← Subgroup.map_commutator, commutator_self_of_perfect hqs.1]

theorem matrixReduction :
    ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (K : Type) [Group K] [Finite K]
      (_ : K ≃* H) (z₀ t₀ : G) (X₀ : Subgroup G) (hz₀ : z₀ ∈ H),
      z₀ ∈ X₀ → t₀ ∈ X₀ → X₀ ≤ H → orderOf z₀ = 3 → orderOf t₀ = 3 → z₀ * t₀ = t₀ * z₀ →
      t₀ ∉ Subgroup.zpowers z₀ →
      Pos ↥H (Subgroup.zpowers (⟨z₀, hz₀⟩ : H)) (X₀.subgroupOf H) →
      (∀ X : Subgroup G, X ≤ X₀ → Pos ↥H (Subgroup.zpowers (⟨z₀, hz₀⟩ : H)) (X.subgroupOf H) →
        Nat.card X = Nat.card X₀) →
      ClassLeaf H z₀ → CompLeaf H z₀ X₀ → GenLeaf H z₀ t₀ → RowLeaves K := by
  intro G _ _ H K _ _ eK z₀ t₀ X₀ hz₀ hz₀X ht₀X hX₀H hoz hot hzt htz hpos0 hsize hCL hCompL hGL
  apply rowLeaves_of_mulEquiv eK
  have ht₀ : t₀ ∈ H := hX₀H ht₀X
  set z₀' : H := ⟨z₀, hz₀⟩ with hz₀'
  set t₀' : H := ⟨t₀, ht₀⟩ with ht₀'
  set Z₀ : Subgroup H := Subgroup.zpowers z₀' with hZ₀
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have toZ0 : ∀ Z X : Subgroup H, Pos H Z X → ∃ k : H, rankThreeConj k Z = Z₀ := by
    intro Z X hp
    obtain ⟨z, -, hzo, hZ⟩ := exists_zpowers_of_card_three hp.1
    obtain ⟨hXH, hzX, hXC, hperf⟩ := pos_G hp hZ
    obtain ⟨g, hgH, hg⟩ := hCL z z.2 (by rw [Subgroup.orderOf_coe, hzo]) _ hXH hzX hXC hperf
    refine ⟨(⟨g, hgH⟩ : H)⁻¹, ?_⟩
    unfold rankThreeConj
    rw [hZ, inv_inv, MonoidHom.map_zpowers]
    rcases hg with hg | hg
    · have hc : (MulAut.conj (⟨g, hgH⟩ : H)).toMonoidHom z = z₀' := by
        apply Subtype.ext; simpa [MulAut.conj_apply] using hg
      rw [hc]
    · have hc : (MulAut.conj (⟨g, hgH⟩ : H)).toMonoidHom z = z₀'⁻¹ := by
        apply Subtype.ext; simpa [MulAut.conj_apply] using hg
      rw [hc, Subgroup.zpowers_inv]
  have eqX0 : ∀ Y : Subgroup H, Pos H Z₀ Y → Y = X₀.subgroupOf H := by
    intro Y hp
    obtain ⟨hYH, hzY, hYC, hperf⟩ := pos_G hp rfl
    have hle : Y.map H.subtype ≤ X₀ := hCompL _ hYH hzY hYC hperf
    have hYY : (Y.map H.subtype).subgroupOf H = Y :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective Y
    have hc := hsize _ hle (by rw [hYY]; exact hp)
    apply Subgroup.eq_of_le_of_card_ge
    · intro y hy; exact hle ⟨y, hy, rfl⟩
    · rw [card_subgroupOf_of_le hX₀H, ← hc, Subgroup.card_map_of_injective H.subtype_injective]
  refine ⟨?_, ?_, ?_⟩
  · intro Z₁ X₁ Z₂ X₂ h1 h2
    obtain ⟨k₁, hk₁⟩ := toZ0 _ _ h1
    obtain ⟨k₂, hk₂⟩ := toZ0 _ _ h2
    refine ⟨k₁ * k₂⁻¹, ?_⟩
    rw [← rankThreeConj_rankThreeConj, hk₁, ← hk₂, rankThreeConj_rankThreeConj, mul_inv_cancel,
      rankThreeConj_one]
  · intro Z X₁ X₂ h1 h2
    obtain ⟨k, hk⟩ := toZ0 _ _ h1
    have e1 := pos_map (MulAut.conj k⁻¹) h1
    have e2 := pos_map (MulAut.conj k⁻¹) h2
    have hk' : Z.map (MulAut.conj k⁻¹).toMonoidHom = Z₀ := hk
    rw [hk'] at e1 e2
    exact Subgroup.map_injective (f := (MulAut.conj k⁻¹).toMonoidHom) (MulAut.conj k⁻¹).injective
      ((eqX0 _ e1).trans (eqX0 _ e2).symm)
  · have hz₀'o : orderOf z₀' = 3 := by rw [← Subgroup.orderOf_coe]; exact hoz
    have ht₀'o : orderOf t₀' = 3 := by rw [← Subgroup.orderOf_coe]; exact hot
    have hZ₀card : Nat.card Z₀ = 3 := by rw [hZ₀, Nat.card_zpowers, hz₀'o]
    have ht₀Z : t₀' ∉ Z₀ := by
      intro h; apply htz
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h
      exact Subgroup.mem_zpowers_iff.mpr ⟨i, by simpa [z₀', t₀'] using congrArg Subtype.val hi⟩
    have hcz : Commute z₀' t₀' := Subtype.ext hzt
    have hcomm : ∀ a ∈ Z₀, a * t₀' = t₀' * a := by
      intro a ha
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (hcz.zpow_left i).eq
    obtain ⟨hel, hcard⟩ :=
      CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute hZ₀card ht₀'o ht₀Z hcomm
    set E₀ := Z₀ ⊔ Subgroup.zpowers t₀' with hE₀
    refine ⟨Z₀, X₀.subgroupOf H, E₀, hpos0, ?_, hel, by rw [hcard]; norm_num, ?_⟩
    · exact sup_le (by rw [Subgroup.zpowers_le]; exact hz₀X)
        (by rw [Subgroup.zpowers_le]; exact ht₀X)
    · set S := ⨆ (F : Subgroup H) (_ : F ≤ E₀) (_ : Nat.card F = 3),
        Subgroup.centralizer (F : Set H) with hS
      have hterm : ∀ (g : G) (hg : g ∈ H), (⟨g, hg⟩ : H) ∈ E₀ → orderOf g = 3 →
          H ⊓ Subgroup.centralizer {g} ≤ S.map H.subtype := by
        intro g hg hgE hgo x ⟨hxH, hxc⟩
        refine ⟨⟨x, hxH⟩, ?_, rfl⟩
        have hsE : Subgroup.zpowers (⟨g, hg⟩ : H) ≤ E₀ := by rw [Subgroup.zpowers_le]; exact hgE
        have h3 : Nat.card (Subgroup.zpowers (⟨g, hg⟩ : H)) = 3 := by
          rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]; exact hgo
        have hcx : Commute (⟨g, hg⟩ : H) ⟨x, hxH⟩ := by
          apply Subtype.ext
          have := Subgroup.mem_centralizer_iff.mp hxc g (Set.mem_singleton g)
          simpa using this
        have hmem : (⟨x, hxH⟩ : H) ∈ Subgroup.centralizer
            ((Subgroup.zpowers (⟨g, hg⟩ : H) : Subgroup H) : Set H) := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
          exact (hcx.zpow_left i).eq
        have hle1 : Subgroup.centralizer
            ((Subgroup.zpowers (⟨g, hg⟩ : H) : Subgroup H) : Set H) ≤ S := by
          rw [hS]
          exact le_iSup_of_le (Subgroup.zpowers (⟨g, hg⟩ : H))
            (le_iSup_of_le hsE (le_iSup_of_le h3 le_rfl))
        exact hle1 hmem
      have hzE : z₀' ∈ E₀ := le_sup_left (a := Z₀) (Subgroup.mem_zpowers z₀')
      have htE : t₀' ∈ E₀ := le_sup_right (a := Z₀) (Subgroup.mem_zpowers t₀')
      have hz3 : z₀ ^ 3 = 1 := by rw [← hoz]; exact pow_orderOf_eq_one z₀
      have ht3 : t₀ ^ 3 = 1 := by rw [← hot]; exact pow_orderOf_eq_one t₀
      have hczG : Commute z₀ t₀ := hzt
      have ho1 : orderOf (z₀ * t₀) = 3 := by
        apply orderOf_eq_prime
        · rw [hczG.mul_pow, hz3, ht3, one_mul]
        · intro h1
          apply htz
          have : t₀ = z₀⁻¹ := eq_inv_of_mul_eq_one_right h1
          rw [this]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers z₀)
      have ho2 : orderOf (z₀ * t₀ ^ 2) = 3 := by
        apply orderOf_eq_prime
        · rw [(hczG.pow_right 2).mul_pow, hz3, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul,
            ht3, one_pow, one_mul]
        · intro h1
          apply htz
          have h2 : t₀ ^ 2 = z₀⁻¹ := eq_inv_of_mul_eq_one_right h1
          have : t₀ = (z₀⁻¹) ^ 2 := by
            rw [← h2, ← pow_mul]
            calc t₀ = t₀ ^ 3 * t₀ := by rw [ht3, one_mul]
              _ = t₀ ^ (2 * 2) := by rw [← pow_succ]
          rw [this]; exact Subgroup.pow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers z₀)) 2
      have hle : H ≤ S.map H.subtype := by
        refine hGL.ge.trans ?_
        refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
        · exact hterm z₀ hz₀ hzE hoz
        · exact hterm t₀ ht₀ htE hot
        · exact hterm (z₀ * t₀) (H.mul_mem hz₀ ht₀) (E₀.mul_mem hzE htE) ho1
        · exact hterm (z₀ * t₀ ^ 2) (H.mul_mem hz₀ (H.pow_mem ht₀ 2))
            (E₀.mul_mem hzE (E₀.pow_mem htE 2)) ho2
      refine le_antisymm le_top fun x _ => ?_
      obtain ⟨y, hy, hyx⟩ := hle x.2
      rwa [show y = x from Subtype.ext hyx] at hy

@[expose] def stdComp {G : Type} [Group G] (H : Subgroup G) (z₀ : G) : Subgroup G :=
  ⁅H ⊓ Subgroup.centralizer {z₀}, H ⊓ Subgroup.centralizer {z₀}⁆

@[expose] def MatrixRowData {G : Type} [Group G] [Finite G] (H : Subgroup G) (z₀ t₀ : G)
    (X₀ : Subgroup G) : Prop :=
  ∃ hz₀ : z₀ ∈ H, z₀ ∈ X₀ ∧ t₀ ∈ X₀ ∧ X₀ ≤ H ∧ orderOf z₀ = 3 ∧ orderOf t₀ = 3 ∧
    z₀ * t₀ = t₀ * z₀ ∧ t₀ ∉ Subgroup.zpowers z₀ ∧
    Pos ↥H (Subgroup.zpowers (⟨z₀, hz₀⟩ : H)) (X₀.subgroupOf H) ∧
    (∀ X : Subgroup G, X ≤ X₀ → Pos ↥H (Subgroup.zpowers (⟨z₀, hz₀⟩ : H)) (X.subgroupOf H) →
      Nat.card X = Nat.card X₀) ∧
    ClassLeaf H z₀ ∧ CompLeaf H z₀ X₀ ∧ GenLeaf H z₀ t₀

theorem rowLeaves_of_matrixRowData {G : Type} [Group G] [Finite G] {H : Subgroup G}
    {K : Type} [Group K] [Finite K] (e : K ≃* H) {z₀ t₀ : G} {X₀ : Subgroup G}
    (h : MatrixRowData H z₀ t₀ X₀) : RowLeaves K := by
  obtain ⟨hz₀, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact matrixReduction G H K e z₀ t₀ X₀ hz₀ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem compLeaf_stdComp {G : Type} [Group G] (H : Subgroup G) (z₀ : G) :
    CompLeaf H z₀ (stdComp H z₀) := by
  intro X hXH _ hXC hperf
  have hle : X ≤ H ⊓ Subgroup.centralizer {z₀} := le_inf hXH hXC
  rw [← hperf]
  exact Subgroup.commutator_mono hle hle

theorem stdComp_le {G : Type} [Group G] (H : Subgroup G) (z₀ : G) : stdComp H z₀ ≤ H := by
  have h : ⁅H ⊓ Subgroup.centralizer {z₀}, H ⊓ Subgroup.centralizer {z₀}⁆ ≤
      H ⊓ Subgroup.centralizer {z₀} := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  exact h.trans inf_le_left

@[expose] def FactsLeaf {G : Type} [Group G] (H : Subgroup G) (z₀ t₀ : G) : Prop :=
  ∃ _ : z₀ ∈ H, z₀ ∈ stdComp H z₀ ∧ t₀ ∈ stdComp H z₀ ∧ orderOf z₀ = 3 ∧ orderOf t₀ = 3 ∧
    z₀ * t₀ = t₀ * z₀ ∧ t₀ ∉ Subgroup.zpowers z₀

@[expose] def PosLeaf {G : Type} [Group G] [Finite G] (H : Subgroup G) (z₀ : G) : Prop :=
  ∀ hz₀ : z₀ ∈ H, Pos ↥H (Subgroup.zpowers (⟨z₀, hz₀⟩ : H)) ((stdComp H z₀).subgroupOf H)

@[expose] def SizeLeaf {G : Type} [Group G] [Finite G] (H : Subgroup G) (z₀ : G) : Prop :=
  ∀ hz₀ : z₀ ∈ H, ∀ X : Subgroup G, X ≤ stdComp H z₀ →
    Pos ↥H (Subgroup.zpowers (⟨z₀, hz₀⟩ : H)) (X.subgroupOf H) →
    Nat.card X = Nat.card (stdComp H z₀)

theorem matrixRowData_stdComp {G : Type} [Group G] [Finite G] {H : Subgroup G} {z₀ t₀ : G}
    (hfacts : FactsLeaf H z₀ t₀) (hpos : PosLeaf H z₀) (hsize : SizeLeaf H z₀)
    (hclass : ClassLeaf H z₀) (hgen : GenLeaf H z₀ t₀) :
    MatrixRowData H z₀ t₀ (stdComp H z₀) := by
  obtain ⟨hz₀, h1, h2, h3, h4, h5, h6⟩ := hfacts
  exact ⟨hz₀, h1, h2, stdComp_le H z₀, h3, h4, h5, h6, hpos hz₀, hsize hz₀, hclass,
    compLeaf_stdComp H z₀, hgen⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
