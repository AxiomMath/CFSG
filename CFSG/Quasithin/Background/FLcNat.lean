module

public import CFSG.Quasithin.Background.FLcFlag
public import CFSG.Quasithin.Background.C3Defs

public section

namespace CFSG.Quasithin.FLc

open Matrix

theorem isNaturalSection_data {G : Type} [Group G] {A V Z : Subgroup G} {N : Subgroup ↥A} {n : ℕ}
    (h : CFSG.Quasithin.IsNaturalSection A V Z N
      (CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2))) :
    ∃ (α : ↥A →* SLt n) (β : ↥V →* Multiplicative (Vt n)),
      A ≤ Subgroup.normalizer (V : Set G) ∧ Function.Surjective α ∧ α.ker = N ∧
      Function.Surjective β ∧ β.ker = Z.subgroupOf V ∧
      ∀ (a : ↥A) (u v : ↥V), (v : G) = a * u * a⁻¹ →
        Multiplicative.toAdd (β v) = mat (α a) *ᵥ Multiplicative.toAdd (β u) := by
  obtain ⟨hAV, α₀, hα₀s, hα₀k, β, hβs, hβk, hrel⟩ := h
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n (ZMod 2)
  refine ⟨e.symm.toMonoidHom.comp α₀, β, hAV, e.symm.surjective.comp hα₀s, ?_, hβs, hβk, ?_⟩
  · rw [← hα₀k]
    ext a
    simp [MonoidHom.mem_ker]
  · intro a u v huv
    rw [hrel a u v huv]
    have h1 : mat (e.symm (α₀ a)) = (((α₀ a : ↥(CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2))) :
        GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
      have h2 := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe n (ZMod 2)
        (e.symm (α₀ a))
      have h3 : (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n (ZMod 2))
          (e.symm (α₀ a)) = α₀ a := e.apply_symm_apply _
      rw [h3] at h2
      exact h2.symm
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    rw [h1]

theorem exists_sylow_of_isSylowTwoOf {G : Type} [Group G] [Finite G] {B H : Subgroup G}
    (h : CFSG.QuasithinUnique.IsSylowTwoOf B H) :
    ∃ P : Sylow 2 ↥H, (P : Subgroup ↥H) = B.subgroupOf H := by
  have hp : IsPGroup 2 ↥(B.subgroupOf H) :=
    h.2.1.of_surjective (Subgroup.subgroupOfEquivOfLe h.1).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe h.1).symm.surjective
  exact ⟨hp.toSylow h.2.2, IsPGroup.toSylow_coe hp h.2.2⟩

theorem flagLocal_core {G : Type} [Group G] [Finite G] {L S UL : Subgroup G} {n : ℕ} (hn : 1 ≤ n)
    (α : ↥L →* SLt n) (β : ↥UL →* Multiplicative (Vt n))
    (hαs : Function.Surjective α) (hβi : Function.Injective β) (hβs : Function.Surjective β)
    (hrel : ∀ (a : ↥L) (u v : ↥UL), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) = mat (α a) *ᵥ Multiplicative.toAdd (β u))
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hSU : S ≤ Subgroup.normalizer (UL : Set G))
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ L) L) :
    ∃ W : ℕ → Subgroup G,
      (∀ k, W k ≤ UL) ∧ (∀ k ≤ n, Nat.card (W k) = 2 ^ k) ∧
      (∀ k ≤ n, S ≤ Subgroup.normalizer (W k : Set G)) ∧ (∀ k, W k ≤ W (k + 1)) ∧
      ∀ k ≤ n, ∀ X : Subgroup G, X ≤ UL → S ≤ Subgroup.normalizer (X : Set G) →
        Nat.card X = 2 ^ k → X = W k := by
  obtain ⟨P, hP⟩ := exists_sylow_of_isSylowTwoOf hSyl
  let Q : Sylow 2 (SLt n) := Sylow.mapSurjective hαs P
  have hQ : (Q : Subgroup (SLt n)) = (P : Subgroup ↥L).map α := Sylow.coe_mapSurjective hαs P
  obtain ⟨Y, hY1, hY2, hY3, hY4⟩ := exists_unique_flag_subgroup hn Q
  have hmemP : ∀ a : ↥L, a ∈ (P : Subgroup ↥L) ↔ (a : G) ∈ S ⊓ L := fun a => by
    rw [hP, Subgroup.mem_subgroupOf]
  let W : ℕ → Subgroup G := fun k => ((Y k).comap β).map UL.subtype
  have hmem : ∀ k (x : G), x ∈ W k ↔ ∃ hx : x ∈ UL, β ⟨x, hx⟩ ∈ Y k := by
    intro k x
    simp only [W, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hy⟩
      exact ⟨⟨x, hx⟩, hy, rfl⟩
  let BInv : Subgroup G → Prop := fun X => ∀ b ∈ S ⊓ L, ∀ x ∈ X, b * x * b⁻¹ ∈ X
  have hWB : ∀ k ≤ n, BInv (W k) := by
    intro k hk b hb x hx
    obtain ⟨hxU, hβx⟩ := (hmem k x).1 hx
    have hxU' : b * x * b⁻¹ ∈ UL := (Subgroup.mem_normalizer_iff.1 (hSU hb.1) x).1 hxU
    refine (hmem k _).2 ⟨hxU', ?_⟩
    have hbL : b ∈ L := hb.2
    have h1 := hrel ⟨b, hbL⟩ ⟨x, hxU⟩ ⟨b * x * b⁻¹, hxU'⟩ rfl
    have h2 : α ⟨b, hbL⟩ ∈ (Q : Subgroup (SLt n)) := by
      rw [hQ]
      exact ⟨⟨b, hbL⟩, (hmemP _).2 hb, rfl⟩
    have h3 := hY2 k hk _ h2 _ hβx
    rw [← h1] at h3
    exact h3
  have huniqB : ∀ k ≤ n, ∀ X : Subgroup G, X ≤ UL → BInv X → Nat.card X = 2 ^ k → X = W k := by
    intro k hk X hXU hXB hXc
    let Z : Subgroup (Multiplicative (Vt n)) := (X.subgroupOf UL).map β
    have hZinv : SInvG (Q : Subgroup (SLt n)) Z := by
      intro q hq z hz
      rw [hQ] at hq
      obtain ⟨a, haP, rfl⟩ := hq
      obtain ⟨y, hyX, rfl⟩ := hz
      have hb : (a : G) ∈ S ⊓ L := (hmemP a).1 haP
      have hyX' : (y : G) ∈ X := hyX
      have hxX := hXB _ hb _ hyX'
      have hxU' : (a : G) * y * (a : G)⁻¹ ∈ UL :=
        (Subgroup.mem_normalizer_iff.1 (hSU hb.1) y).1 y.2
      have h1 := hrel a y ⟨(a : G) * y * (a : G)⁻¹, hxU'⟩ rfl
      refine ⟨⟨(a : G) * y * (a : G)⁻¹, hxU'⟩, hxX, ?_⟩
      rw [← h1]
      rfl
    have hZc : Nat.card Z = 2 ^ k := by
      rw [Subgroup.card_map_of_injective hβi]
      rw [← hXc]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXU).toEquiv
    have hZY : Z = Y k := hY4 Z hZinv k hk hZc
    ext x
    constructor
    · intro hx
      refine (hmem k x).2 ⟨hXU hx, ?_⟩
      rw [← hZY]
      exact ⟨⟨x, hXU hx⟩, hx, rfl⟩
    · intro hx
      obtain ⟨hxU, hβx⟩ := (hmem k x).1 hx
      rw [← hZY] at hβx
      obtain ⟨y, hyX, hy⟩ := hβx
      have : y = ⟨x, hxU⟩ := hβi hy
      rw [this] at hyX
      exact hyX
  have hWU : ∀ k, W k ≤ UL := fun k => Subgroup.map_subtype_le _
  have hWc : ∀ k ≤ n, Nat.card (W k) = 2 ^ k := by
    intro k hk
    have h1 : Nat.card (W k) = Nat.card ((Y k).comap β) :=
      Subgroup.card_map_of_injective UL.subtype_injective
    have h2 : Nat.card (Y k) = Nat.card ((Y k).comap β) := by
      conv_lhs => rw [← Subgroup.map_comap_eq_self_of_surjective hβs (Y k)]
      exact Subgroup.card_map_of_injective hβi
    rw [h1, ← h2, hY1 k hk]
  have hSW : ∀ k ≤ n, ∀ s ∈ S, ∀ x ∈ W k, s * x * s⁻¹ ∈ W k := by
    intro k hk s hs x hx
    let Xs : Subgroup G := (W k).map (MulAut.conj s).toMonoidHom
    have hXsU : Xs ≤ UL := by
      rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 (hSU hs) y).1 (hWU k hy)
    have hXsc : Nat.card Xs = 2 ^ k := by
      rw [Subgroup.card_map_of_injective (MulAut.conj s).injective, hWc k hk]
    have hXsB : BInv Xs := by
      rintro b hb _ ⟨y, hy, rfl⟩
      have hb' : s⁻¹ * b * s ∈ S ⊓ L := by
        refine ⟨S.mul_mem (S.mul_mem (S.inv_mem hs) hb.1) hs, ?_⟩
        have := (Subgroup.mem_normalizer_iff.1 (hSL (S.inv_mem hs)) b).1 hb.2
        simpa using this
      refine ⟨s⁻¹ * b * s * y * (s⁻¹ * b * s)⁻¹, hWB k hk _ hb' y hy, ?_⟩
      show s * (s⁻¹ * b * s * y * (s⁻¹ * b * s)⁻¹) * s⁻¹ = b * (s * y * s⁻¹) * b⁻¹
      group
    have := huniqB k hk Xs hXsU hXsB hXsc
    rw [← this]
    exact ⟨x, hx, rfl⟩
  refine ⟨W, hWU, hWc, fun k hk s hs => ?_, fun k => ?_, fun k hk X hXU hSX hXc => ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hSW k hk s hs x hx, fun hx => ?_⟩
    have h1 := hSW k hk s⁻¹ (S.inv_mem hs) _ hx
    have h2 : s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x := by group
    rwa [h2] at h1
  · intro x hx
    obtain ⟨hxU, hβx⟩ := (hmem k x).1 hx
    exact (hmem (k + 1) x).2 ⟨hxU, hY3 k hβx⟩
  · refine huniqB k hk X hXU (fun b hb x hx => ?_) hXc
    exact (Subgroup.mem_normalizer_iff.1 (hSX hb.1) x).1 hx

end CFSG.Quasithin.FLc
