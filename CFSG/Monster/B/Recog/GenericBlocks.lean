module

public import CFSG.Monster.B.GSide.GenericGeneration
public import CFSG.Monster.B.Recog.GenericStrongClosure
public import CFSG.Monster.B.Recog.GenericStrongEmbedding

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Recog

open StrongClosure

variable {G : Type*} [Group G]

theorem mem_of_conj_mem_of_block {M : Subgroup G} {D₀ D : Set G}
    (hD₀ : ∀ a ∈ D₀, ∀ b ∈ D₀, ∃ m ∈ M, m * a * m⁻¹ = b)
    (hC₀ : ∀ a ∈ D₀, Subgroup.centralizer {a} ≤ M)
    (hDconj : ∀ x ∈ D, ∀ g : G, g * x * g⁻¹ ∈ D) (hD₀D : D₀ ⊆ D)
    (hDM : ∀ x ∈ D, x ∈ M → x ∈ D₀)
    (hInv : ∀ x ∈ M, x * x = 1 → ∃ a ∈ D₀, a * x = x * a)
    {w : G} (hw2 : w * w = 1) (hwC : Subgroup.centralizer {w} ≤ M)
    {g : G} (hg : g * w * g⁻¹ ∈ M) : g ∈ M := by
  have hx2 : g * w * g⁻¹ * (g * w * g⁻¹) = 1 := by
    calc g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
      _ = 1 := by rw [hw2, mul_one, mul_inv_cancel]
  obtain ⟨a, ha, hax⟩ := hInv _ hg hx2
  have hb : g⁻¹ * a * g ∈ Subgroup.centralizer {w} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * a * g * w = g⁻¹ * (a * (g * w * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * w * g⁻¹) * a) * g := by rw [hax]
      _ = w * (g⁻¹ * a * g) := by group
  have hbD : g⁻¹ * a * g ∈ D := by
    have h := hDconj a (hD₀D ha) g⁻¹
    rwa [inv_inv] at h
  have hbD₀ : g⁻¹ * a * g ∈ D₀ := hDM _ hbD (hwC hb)
  refine GSide.mem_of_conj_mem_of_centralizer_le hD₀ hC₀ hbD₀ ?_
  rw [show g * (g⁻¹ * a * g) * g⁻¹ = a by group]
  exact ha

theorem mem_of_conj_mem_of_block_of_class {M : Subgroup G} {d : G}
    (hC : ∀ m ∈ M, Subgroup.centralizer {m * d * m⁻¹} ≤ M)
    (hDM : ∀ x ∈ M, IsConj d x → x ∈ {y : G | ∃ m ∈ M, m * d * m⁻¹ = y})
    (hInv : ∀ x ∈ M, x * x = 1 → ∃ a ∈ {y : G | ∃ m ∈ M, m * d * m⁻¹ = y}, a * x = x * a)
    {w : G} (hw2 : w * w = 1) (hwC : Subgroup.centralizer {w} ≤ M)
    {g : G} (hg : g * w * g⁻¹ ∈ M) : g ∈ M := by
  refine mem_of_conj_mem_of_block (D := {x | IsConj d x}) ?_ ?_ ?_ ?_
    (fun x hx hxM => hDM x hxM hx) hInv hw2 hwC hg
  · rintro _ ⟨g₁, hg₁, rfl⟩ _ ⟨g₂, hg₂, rfl⟩
    exact ⟨g₂ * g₁⁻¹, M.mul_mem hg₂ (M.inv_mem hg₁), by group⟩
  · rintro _ ⟨m, hm, rfl⟩
    exact hC m hm
  · intro x hx g
    exact hx.trans (isConj_iff.2 ⟨g, rfl⟩)
  · rintro _ ⟨m, -, rfl⟩
    exact isConj_iff.2 ⟨m, rfl⟩

theorem eq_of_le_isPGroup_of_block [Finite G] {Y M P₀ : Subgroup G} (hP₀ : P₀ ≤ Y ⊓ M)
    (hmax : ∀ Q : Subgroup G, Q ≤ Y ⊓ M → IsPGroup 2 Q → P₀ ≤ Q → Q = P₀)
    {w : G} (hwP : w ∈ P₀) (hblock : ∀ g : G, g * w * g⁻¹ ∈ M → g ∈ M)
    {Q : Subgroup G} (hQY : Q ≤ Y) (hQ : IsPGroup 2 Q) (hPQ : P₀ ≤ Q) : Q = P₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have hwQ : w ∈ Q := hPQ hwP
  have hself : Subgroup.normalizer ((P₀.subgroupOf Q : Subgroup Q) : Set Q) = P₀.subgroupOf Q := by
    refine le_antisymm ?_ Subgroup.le_normalizer
    have hN : (Subgroup.normalizer ((P₀.subgroupOf Q : Subgroup Q) : Set Q)).map Q.subtype =
        P₀ := by
      refine hmax _ (fun x hx => ?_) (hQ.to_le (Subgroup.map_subtype_le _)) (fun x hx => ?_)
      · obtain ⟨n, hn, rfl⟩ := hx
        refine ⟨hQY n.2, hblock _ ?_⟩
        have h := (Subgroup.mem_normalizer_iff.1 hn ⟨w, hwQ⟩).1 (by
          rw [Subgroup.mem_subgroupOf]
          exact hwP)
        rw [Subgroup.mem_subgroupOf] at h
        exact hP₀.trans inf_le_right h
      · exact ⟨⟨x, hPQ hx⟩, Subgroup.le_normalizer (by rw [Subgroup.mem_subgroupOf]; exact hx), rfl⟩
    intro n hn
    rw [Subgroup.mem_subgroupOf, ← hN]
    exact ⟨n, hn, rfl⟩
  have htop := normalizerCondition_iff_only_full_group_self_normalizing.1
    Group.normalizerCondition_of_isNilpotent _ hself
  exact le_antisymm (Subgroup.subgroupOf_eq_top.1 htop) hPQ

theorem exists_sylow_eq_subgroupOf_of_block [Finite G] {Y M P₀ : Subgroup G} (hP₀ : P₀ ≤ Y ⊓ M)
    (hP₂ : IsPGroup 2 P₀)
    (hmax : ∀ Q : Subgroup G, Q ≤ Y ⊓ M → IsPGroup 2 Q → P₀ ≤ Q → Q = P₀)
    {w : G} (hwP : w ∈ P₀) (hblock : ∀ g : G, g * w * g⁻¹ ∈ M → g ∈ M) :
    ∃ T : Sylow 2 Y, (T : Subgroup Y) = P₀.subgroupOf Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := (hP₂.comap_of_injective Y.subtype Y.subtype_injective).exists_le_sylow
  refine ⟨T, ?_⟩
  have hPY : P₀ ≤ Y := hP₀.trans inf_le_left
  have hTP : (T : Subgroup Y).map Y.subtype = P₀ := by
    refine eq_of_le_isPGroup_of_block hP₀ hmax hwP hblock (Subgroup.map_subtype_le _)
      (T.isPGroup'.map _) (fun x hx => ⟨⟨x, hPY hx⟩, hT ?_, rfl⟩)
    rw [Subgroup.mem_comap]
    exact hx
  rw [← hTP, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Y.subtype_injective]

theorem strongly_closed_of_blocks {Y : Type*} [Group Y] [Finite Y] {Y₀ V W : Subgroup Y}
    {D₀ : Set Y} (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hV2 : ∀ x ∈ V, x * x = 1)
    (hD₀V : D₀ ⊆ V) (hVY₀ : V ≤ Y₀) (hY₀N : Y₀ ≤ Subgroup.normalizer (V : Set Y))
    (hNY₀ : Subgroup.normalizer (V : Set Y) ≤ Y₀)
    (hD₀ : ∀ g : Y, ∀ a ∈ D₀, g * a * g⁻¹ ∈ Y₀ → g ∈ Y₀)
    (T : Sylow 2 Y) (hTY₀ : (T : Subgroup Y) ≤ Y₀)
    (hWV : W ≤ V) (hW1 : W ≠ ⊥) (hWD₀ : ∀ w ∈ W, w ≠ 1 → w ∈ D₀)
    (hWn : ∀ g ∈ Y₀, ∀ w ∈ W, g * w * g⁻¹ ∈ W) :
    ∀ a ∈ V, ∀ g : Y, g⁻¹ * a * g ∈ (T : Subgroup Y) → g⁻¹ * a * g ∈ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCa : ∀ a ∈ D₀, ∀ c : Y, c * a = a * c → c ∈ Y₀ := fun a ha c hc =>
    hD₀ c a ha (by rw [hc, mul_inv_cancel_right]; exact hVY₀ (hD₀V ha))
  refine strongly_closed_of_le_normalizer hVab hV2 hD₀V ?_ ?_ ?_ (hTY₀.trans hY₀N)
  ·
    intro g k a ha b hb hcomm
    have hc : (g⁻¹ * k) * b * (g⁻¹ * k)⁻¹ ∈ Y₀ := by
      refine hCa a ha _ ?_
      calc (g⁻¹ * k) * b * (g⁻¹ * k)⁻¹ * a =
          g⁻¹ * ((k * b * k⁻¹) * (g * a * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * a * g⁻¹) * (k * b * k⁻¹)) * g := by rw [hcomm]
        _ = a * ((g⁻¹ * k) * b * (g⁻¹ * k)⁻¹) := by group
    exact hY₀N (hD₀ _ b hb hc)
  ·
    rintro _ ⟨g, a, ha, rfl⟩ _ ⟨k, b, hb, rfl⟩ hP
    obtain ⟨P, hP⟩ := hP.exists_le_sylow
    obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq Y T P
    have hmem : ∀ x ∈ ({g * a * g⁻¹, k * b * k⁻¹} : Set Y), h⁻¹ * x * h ∈ (T : Subgroup Y) := by
      intro x hx
      have hxP := hP (Subgroup.subset_closure hx)
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxP
      obtain ⟨y, hy, hyx⟩ := hxP
      have hyx' : h * y * h⁻¹ = x := hyx
      rw [← hyx', show h⁻¹ * (h * y * h⁻¹) * h = y by group]
      exact hy
    have hga : h⁻¹ * g ∈ Y₀ := hD₀ _ a ha (by
      rw [show h⁻¹ * g * a * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * a * g⁻¹) * h by group]
      exact hTY₀ (hmem _ (Set.mem_insert _ _)))
    have hkb : h⁻¹ * k ∈ Y₀ := hD₀ _ b hb (by
      rw [show h⁻¹ * k * b * (h⁻¹ * k)⁻¹ = h⁻¹ * (k * b * k⁻¹) * h by group]
      exact hTY₀ (hmem _ (Set.mem_insert_of_mem _ rfl)))
    have ha' := (Subgroup.mem_normalizer_iff.1 (hY₀N hga) a).1 (hD₀V ha)
    have hb' := (Subgroup.mem_normalizer_iff.1 (hY₀N hkb) b).1 (hD₀V hb)
    have hab := hVab _ ha' _ hb'
    calc g * a * g⁻¹ * (k * b * k⁻¹) =
        h * (h⁻¹ * g * a * (h⁻¹ * g)⁻¹ * (h⁻¹ * k * b * (h⁻¹ * k)⁻¹)) * h⁻¹ := by group
      _ = h * (h⁻¹ * k * b * (h⁻¹ * k)⁻¹ * (h⁻¹ * g * a * (h⁻¹ * g)⁻¹)) * h⁻¹ := by rw [hab]
      _ = k * b * k⁻¹ * (g * a * g⁻¹) := by group
  ·
    intro w hwN hw2 _
    have hwY₀ := hNY₀ hwN
    have hW2 : IsPGroup 2 W := fun x =>
      ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, pow_two, hV2 _ (hWV x.2)]; rfl)⟩
    have hZ2 : IsPGroup 2 (Subgroup.zpowers w) := by
      have hdvd : orderOf w ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two, hw2])
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
    have hwW : w ∈ Subgroup.normalizer (W : Set Y) :=
      Subgroup.mem_normalizer_fintype fun x hx => hWn w hwY₀ x hx
    have hNW : W ⊔ Subgroup.zpowers w ≤ Subgroup.normalizer (W : Set Y) :=
      sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hwW)
    obtain ⟨z, hzW, hz2, hz⟩ := StrongEmbedding.exists_involution_centralized hW1 le_sup_left hNW
      (hW2.to_sup_of_normal_left' hZ2 (Subgroup.zpowers_le.2 hwW))
    have hz1 : z ≠ 1 := fun h => by
      rw [h, orderOf_one] at hz2
      exact absurd hz2 (by norm_num)
    refine ⟨z, hWD₀ z hzW hz1, ?_⟩
    exact (Subgroup.mem_centralizer_singleton_iff.1
      (hz (Subgroup.mem_sup_right (Subgroup.mem_zpowers w)))).symm

theorem strongly_closed_map {Y : Type*} [Group Y] {V T Z : Subgroup Y} [Z.Normal]
    (hZT : Z ≤ T) (hcl : ∀ a ∈ V, ∀ g : Y, g⁻¹ * a * g ∈ T → g⁻¹ * a * g ∈ V) :
    ∀ a ∈ V.map (QuotientGroup.mk' Z), ∀ g : Y ⧸ Z,
      g⁻¹ * a * g ∈ T.map (QuotientGroup.mk' Z) → g⁻¹ * a * g ∈ V.map (QuotientGroup.mk' Z) := by
  rintro _ ⟨v, hv, rfl⟩ g hg
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective Z g
  obtain ⟨t, ht, hth⟩ := hg
  have hz : t⁻¹ * (h⁻¹ * v * h) ∈ Z := by
    rw [← QuotientGroup.eq]
    change QuotientGroup.mk' Z t = QuotientGroup.mk' Z (h⁻¹ * v * h)
    rw [hth, map_mul, map_mul, map_inv]
  have hT : h⁻¹ * v * h ∈ T := by
    have := T.mul_mem ht (hZT hz)
    rwa [mul_inv_cancel_left] at this
  refine ⟨h⁻¹ * v * h, hcl v hv h hT, ?_⟩
  rw [map_mul, map_mul, map_inv]

end CFSG.Monster.B.Recog
