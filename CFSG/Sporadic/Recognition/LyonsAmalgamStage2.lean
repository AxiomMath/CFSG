module

public import CFSG.Sporadic.Recognition.LyonsLocalEdge
public import CFSG.Sporadic.Recognition.LyonsLocalNormalizerA3
public import CFSG.Sporadic.Recognition.LyonsAmalgamExtAut
import CFSG.Sporadic.Recognition.LyonsAmalgamLines

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup

section Transport

variable {E Y0 : Type*} [Group E] [Group Y0] (Yb : Subgroup E) [Yb.Normal]

theorem exists_conjEquiv_transport [Finite E] (φ : Yb ≃* Y0)
    (hC : centralizer (Yb : Set E) = ⊥) (hcard : Nat.card (MulAut Y0) ≤ Nat.card E) :
    ∃ Φ : E ≃* MulAut Y0, ∀ (e : E) (y : Yb), Φ e (φ y) = φ (MulAut.conjNormal e y) := by
  have : Finite (MulAut Yb) := Finite.of_injective (fun f : MulAut Yb => (f : Yb → Yb))
    DFunLike.coe_injective
  have hcard' : Nat.card (MulAut Yb) ≤ Nat.card E := by
    rw [Nat.card_congr (MulAut.congr φ).toEquiv]
    exact hcard
  let Ψ : E ≃* MulAut Yb := conjNormalEquiv Yb hC hcard'
  refine ⟨Ψ.trans (MulAut.congr φ), fun e y => ?_⟩
  simp only [MulEquiv.trans_apply]
  have h1 : Ψ e = MulAut.conjNormal e := rfl
  rw [h1]
  simp [MulAut.congr_apply]

end Transport

section Generic

variable {G : Type*} [Group G]

theorem conj_mem_normalizer_zpowers_amalgam {a b s g : G} (hab : s * a * s⁻¹ = b)
    (hg : g ∈ normalizer (zpowers a : Set G)) : s * g * s⁻¹ ∈ normalizer (zpowers b : Set G) := by
  have hb : zpowers b = (zpowers a).map (MulAut.conj s).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    simp [← hab]
  have h := map_equiv_normalizer_eq (zpowers a) (MulAut.conj s)
  rw [hb]
  have : s * g * s⁻¹ ∈ (normalizer (zpowers a : Set G)).map (MulAut.conj s).toMonoidHom :=
    ⟨g, hg, by simp⟩
  rw [h] at this
  exact this

@[expose] def KN (a b c : G) : Subgroup G := NN a b ⊓ normalizer (zpowers c : Set G)

@[expose] def TrN (a b c : G) : Subgroup G := normalizer (A3 a b c : Set G)

@[expose] def EN (a b : G) : Subgroup G := normalizer (EE a b : Set G)

@[expose] def TxN (a b c : G) : Subgroup G := TrN a b c ⊓ normalizer (zpowers a : Set G)

theorem mem_NN_iff {a b g : G} : g ∈ NN a b ↔ g ∈ normalizer (zpowers a : Set G) ∧
    g ∈ normalizer (zpowers b : Set G) := by
  simp only [NN, Subgroup.mem_inf]

theorem conj_mem_zpowers_of_mem_normalizer {a g : G} (hg : g ∈ normalizer (zpowers a : Set G)) :
    g * a * g⁻¹ ∈ zpowers a :=
  (mem_normalizer_iff.1 hg a).1 (mem_zpowers a)

theorem mem_KN_iff {a b c g : G} : g ∈ KN a b c ↔ g ∈ normalizer (zpowers a : Set G) ∧
    g ∈ normalizer (zpowers b : Set G) ∧ g ∈ normalizer (zpowers c : Set G) := by
  simp only [KN, NN, Subgroup.mem_inf]
  tauto

theorem KN_le_NN (a b c : G) : KN a b c ≤ NN a b := inf_le_left

theorem mem_EN_of_mem_NN [Finite G] {a b g : G} (hg : g ∈ NN a b) : g ∈ EN a b :=
  NN_le_normalizer_EE a b hg

theorem KN_le_TrN [Finite G] (a b c : G) : KN a b c ≤ TrN a b c := by
  intro g hg
  obtain ⟨ha, hb, hc⟩ := mem_KN_iff.1 hg
  refine McLAS.mem_normalizer_closure (S := ({a, b, c} : Set G)) fun s hs => ?_
  have hs' : s = a ∨ s = b ∨ s = c := by simpa using hs
  have key : ∀ {d : G}, d ∈ ({a, b, c} : Set G) → g ∈ normalizer (zpowers d : Set G) →
      g * d * g⁻¹ ∈ Subgroup.closure ({a, b, c} : Set G) := by
    intro d hd hgd
    exact zpowers_le.2 (subset_closure hd) ((mem_normalizer_iff.1 hgd d).1 (mem_zpowers d))
  rcases hs' with rfl | rfl | rfl
  · exact key (by simp) ha
  · exact key (by simp) hb
  · exact key (by simp) hc

theorem KN_le_TxN [Finite G] (a b c : G) : KN a b c ≤ TxN a b c :=
  fun _ hg => ⟨KN_le_TrN a b c hg, (mem_KN_iff.1 hg).1⟩

theorem swap_mem_TrN [Finite G] {a b c s : G} (h1 : s * a * s⁻¹ = b) (h2 : s * b * s⁻¹ = a)
    (h3 : s * c * s⁻¹ = c) : s ∈ TrN a b c := by
  refine McLAS.mem_normalizer_closure (S := ({a, b, c} : Set G)) fun e he => ?_
  have he' : e = a ∨ e = b ∨ e = c := by simpa using he
  rcases he' with rfl | rfl | rfl
  · rw [h1]; exact subset_closure (by simp)
  · rw [h2]; exact subset_closure (by simp)
  · rw [h3]; exact subset_closure (by simp)

theorem swap_mem_EN [Finite G] {a b s : G} (h1 : s * a * s⁻¹ = b) (h2 : s * b * s⁻¹ = a) :
    s ∈ EN a b := by
  refine McLAS.mem_normalizer_closure (S := ({a, b} : Set G)) fun e he => ?_
  have he' : e = a ∨ e = b := by simpa using he
  rcases he' with rfl | rfl
  · rw [h1]; exact subset_closure (by simp)
  · rw [h2]; exact subset_closure (by simp)

theorem conj_swap_mem_KN {a b c s g : G} (h1 : s * a * s⁻¹ = b) (h2 : s * b * s⁻¹ = a)
    (h3 : s * c * s⁻¹ = c) (hg : g ∈ KN a b c) : s * g * s⁻¹ ∈ KN a b c := by
  obtain ⟨ha, hb, hc⟩ := mem_KN_iff.1 hg
  exact mem_KN_iff.2 ⟨conj_mem_normalizer_zpowers_amalgam h2 hb,
    conj_mem_normalizer_zpowers_amalgam h1 ha, conj_mem_normalizer_zpowers_amalgam h3 hc⟩

theorem mul_inv_mem_of_index_two {E : Type*} [Group E] {Y : Subgroup E} (h : Y.index = 2)
    {k s : E} (hk : k ∉ Y) (hs : s ∉ Y) : k * s⁻¹ ∈ Y := by
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 h
  have hk' : k * a ∈ Y := ((ha k).resolve_right (fun h => hk h.1)).1
  have hs' : s * a ∈ Y := ((ha s).resolve_right (fun h => hs h.1)).1
  have := Y.mul_mem hk' (Y.inv_mem hs')
  simpa [mul_assoc] using this

end Generic

section Main

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

theorem iE_axes : ∀ m : Fin 8, ((iE m).1.val < 2 ∧ 2 ≤ (iE m).2.val) ∨
    (2 ≤ (iE m).1.val ∧ (iE m).2.val < 2) := by decide

theorem iE_two : iE 2 = (1, 2) := by decide

omit [Finite G] in
theorem e4H_cases (i : Fin 4) :
    (i.val < 2 → ((e4H x₁ x₂ i : G) = (x₁ : G) ∨ (e4H x₁ x₂ i : G) = (x₁ : G)⁻¹)) ∧
      (2 ≤ i.val → ((e4H x₁ x₂ i : G) = (x₂ : G) ∨ (e4H x₁ x₂ i : G) = (x₂ : G)⁻¹)) := by
  fin_cases i <;> simp [e4H]

namespace LyData

theorem exists_inv_fix (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    ∃ w ∈ NN (x₁ : G) (x₂ : G), w * (x₁ : G) * w⁻¹ = (x₁ : G)⁻¹ ∧ w * (x₂ : G) * w⁻¹ = x₂ := by
  obtain ⟨w, -, hw1, hw2⟩ := D.exists_lift_pE_normalizer S 2
  rw [iE_two] at hw1 hw2
  have h1 : w * (x₁ : G) * w⁻¹ = (x₁ : G)⁻¹ := by simpa [e4H] using hw1
  have h2 : w * (x₂ : G) * w⁻¹ = (x₂ : G) := by simpa [e4H] using hw2
  exact ⟨w, mem_NN_of_conj (Or.inr h1) (Or.inl h2), h1, h2⟩

theorem exists_conj_x₂_of_not_mem_NN (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) {n : G}
    (hn : n ∈ EN (x₁ : G) (x₂ : G)) (hnN : n ∉ NN (x₁ : G) (x₂ : G)) :
    ∃ u : G, (u = (x₂ : G) ∨ u = (x₂ : G)⁻¹) ∧ n * (x₁ : G) * n⁻¹ = u := by
  obtain ⟨m, hm1, hm2⟩ := D.exists_pE_of_mem_normalizer S hn
  rcases iE_axes m with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exfalso
    apply hnN
    refine mem_NN_of_conj ?_ ?_
    · rw [hm1]
      exact (e4H_cases (x₁ := x₁) (x₂ := x₂) (iE m).1).1 h1
    · rw [hm2]
      exact (e4H_cases (x₁ := x₁) (x₂ := x₂) (iE m).2).2 h2
  · exact ⟨_, (e4H_cases (x₁ := x₁) (x₂ := x₂) (iE m).1).2 h1, hm1⟩

theorem centralizer_eq_bot (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hZ : ∀ z ∈ NN (x₁ : G) (x₂ : G), (∀ y ∈ NN (x₁ : G) (x₂ : G), z * y = y * z) → z = 1) :
    centralizer (((NN (x₁ : G) (x₂ : G)).subgroupOf (EN (x₁ : G) (x₂ : G)) :
      Subgroup ↥(EN (x₁ : G) (x₂ : G))) : Set ↥(EN (x₁ : G) (x₂ : G))) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  rw [mem_centralizer_iff] at hc
  have hcomm : ∀ y ∈ NN (x₁ : G) (x₂ : G), y * (c : G) = (c : G) * y := by
    intro y hy
    have := hc ⟨y, mem_EN_of_mem_NN hy⟩ (by simpa [Subgroup.mem_subgroupOf] using hy)
    exact congrArg Subtype.val this
  by_cases hcN : (c : G) ∈ NN (x₁ : G) (x₂ : G)
  · exact Subtype.ext (hZ _ hcN fun y hy => (hcomm y hy).symm)
  · exfalso
    obtain ⟨u, hu, hcu⟩ := D.exists_conj_x₂_of_not_mem_NN S c.2 hcN
    obtain ⟨w, hwN, hw1, hw2⟩ := D.exists_inv_fix S
    have hcw : (w : G) * (c : G) = (c : G) * w := hcomm w hwN
    have hwu : w * u * w⁻¹ = u := by
      rcases hu with rfl | rfl
      · exact hw2
      · calc w * (x₂ : G)⁻¹ * w⁻¹ = (w * (x₂ : G) * w⁻¹)⁻¹ := by group
          _ = (x₂ : G)⁻¹ := by rw [hw2]
    have h1 : (c : G) * (w * (x₁ : G) * w⁻¹) * (c : G)⁻¹ = u⁻¹ := by
      rw [hw1]
      calc (c : G) * (x₁ : G)⁻¹ * (c : G)⁻¹ = ((c : G) * (x₁ : G) * (c : G)⁻¹)⁻¹ := by group
        _ = u⁻¹ := by rw [hcu]
    have h2 : (c : G) * (w * (x₁ : G) * w⁻¹) * (c : G)⁻¹ = u := by
      calc (c : G) * (w * (x₁ : G) * w⁻¹) * (c : G)⁻¹
          = ((c : G) * w) * (x₁ : G) * ((c : G) * w)⁻¹ := by group
        _ = (w * (c : G)) * (x₁ : G) * (w * (c : G))⁻¹ := by rw [hcw]
        _ = w * ((c : G) * (x₁ : G) * (c : G)⁻¹) * w⁻¹ := by group
        _ = u := by rw [hcu, hwu]
    have hsq : u * u = 1 := by
      have := h2.symm.trans h1
      exact mul_eq_one_iff_eq_inv.2 this
    have h3 : u ^ 3 = 1 := by
      have hx3 : (x₂ : G) ^ 3 = 1 := by simpa using congrArg Subtype.val S.pow₂
      rcases hu with rfl | rfl
      · exact hx3
      · rw [inv_pow, hx3, inv_one]
    have hu1 : u = 1 := by
      calc u = u ^ 3 * (u * u)⁻¹ := by group
        _ = 1 := by rw [h3, hsq]; simp
    have hx2 : (x₂ : G) = 1 := by
      rcases hu with rfl | rfl
      · exact hu1
      · simpa using hu1
    have := orderOf_x₂ S (G := G)
    rw [hx2, orderOf_one] at this
    omega

end LyData

end Main

structure Stage2Model (Y0 : Type*) [Group Y0] where
  κ : MulAut Y0
  T : Subgroup Y0
  center_eq_bot : center Y0 = ⊥
  card_aut_le : Nat.card (MulAut Y0) ≤ 699840
  κ_mul_κ : κ * κ = 1
  κ_mem : ∀ t ∈ T, κ t ∈ T
  normalizer_le : ∀ n : Y0, (∀ t ∈ T, n * t * n⁻¹ ∈ T) → n ∈ T
  not_inner : ∀ t ∈ T, MulAut.conj t ≠ κ

section Main2

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

structure IsSwapElement (a b c : G) {Y0 : Type*} [Group Y0] (M : Stage2Model Y0)
    (φY : ↥(NN a b) ≃* Y0) (k : G) : Prop where
  mem_EN : k ∈ EN a b
  act : ∀ (y : G) (hy : y ∈ NN a b), ∃ hy' : k * y * k⁻¹ ∈ NN a b,
    φY ⟨k * y * k⁻¹, hy'⟩ = M.κ (φY ⟨y, hy⟩)
  mul_self : k * k = 1
  not_mem_NN : k ∉ NN a b
  conj_a : k * a * k⁻¹ ∈ zpowers b
  conj_b : k * b * k⁻¹ ∈ zpowers a
  conj_c : k * c * k⁻¹ ∈ zpowers c
  mem_TrN : k ∈ TrN a b c
  conj_KN : ∀ g ∈ KN a b c, k * g * k⁻¹ ∈ KN a b c

theorem LyData.exists_swapElement (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    {Y0 : Type*} [Group Y0] (M : Stage2Model Y0) (φY : ↥(NN (x₁ : G) (x₂ : G)) ≃* Y0)
    (hK : ∀ y : ↥(NN (x₁ : G) (x₂ : G)), (y : G) ∈ KN (x₁ : G) (x₂ : G) (x₃ : G) ↔ φY y ∈ M.T)
    (hE : Nat.card ↥(EN (x₁ : G) (x₂ : G)) = 699840) :
    ∃ k : G, IsSwapElement (x₁ : G) (x₂ : G) (x₃ : G) M φY k := by
  classical
  have hNY : ((NN (x₁ : G) (x₂ : G)).subgroupOf (EN (x₁ : G) (x₂ : G))).Normal :=
    Subgroup.normal_of_index_eq_two (D.relIndex_NN_normalizer_EE S)
  have hidx : ((NN (x₁ : G) (x₂ : G)).subgroupOf (EN (x₁ : G) (x₂ : G))).index = 2 :=
    D.relIndex_NN_normalizer_EE S
  have hZ' : ∀ z ∈ NN (x₁ : G) (x₂ : G), (∀ y ∈ NN (x₁ : G) (x₂ : G), z * y = y * z) → z = 1 := by
    intro z hz hcomm
    have hmem : φY ⟨z, hz⟩ ∈ center Y0 := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := φY.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm y y.2).symm
    rw [M.center_eq_bot, Subgroup.mem_bot] at hmem
    have := φY.injective (hmem.trans (map_one φY).symm)
    exact congrArg Subtype.val this
  have hC := D.centralizer_eq_bot S hZ'
  let Yb : Subgroup ↥(EN (x₁ : G) (x₂ : G)) :=
    (NN (x₁ : G) (x₂ : G)).subgroupOf (EN (x₁ : G) (x₂ : G))
  have hYbN : Yb.Normal := hNY
  let ψ : ↥Yb ≃* ↥(NN (x₁ : G) (x₂ : G)) :=
    Subgroup.subgroupOfEquivOfLe (NN_le_normalizer_EE _ _)
  let φ : ↥Yb ≃* Y0 := ψ.trans φY
  have hcard : Nat.card (MulAut Y0) ≤ Nat.card ↥(EN (x₁ : G) (x₂ : G)) := by
    rw [hE]
    exact M.card_aut_le
  obtain ⟨Φ, hΦ⟩ := exists_conjEquiv_transport Yb φ hC hcard
  let k₀ : ↥(EN (x₁ : G) (x₂ : G)) := Φ.symm M.κ
  have hk₀ : Φ k₀ = M.κ := Φ.apply_symm_apply _
  have act : ∀ (y : G) (hy : y ∈ NN (x₁ : G) (x₂ : G)),
      ∃ hy' : (k₀ : G) * y * (k₀ : G)⁻¹ ∈ NN (x₁ : G) (x₂ : G),
        φY ⟨(k₀ : G) * y * (k₀ : G)⁻¹, hy'⟩ = M.κ (φY ⟨y, hy⟩) := by
    intro y hy
    have hy' : (k₀ : G) * y * (k₀ : G)⁻¹ ∈ NN (x₁ : G) (x₂ : G) :=
      D.conj_mem_NN_of_mem_normalizer_EE S k₀.2 hy
    refine ⟨hy', ?_⟩
    let yb : ↥Yb := ⟨⟨y, mem_EN_of_mem_NN hy⟩, Subgroup.mem_subgroupOf.2 hy⟩
    have h := hΦ k₀ yb
    rw [hk₀] at h
    exact h.symm
  have hmul : k₀ * k₀ = 1 := by
    apply Φ.injective
    rw [map_mul, hk₀, map_one]
    exact M.κ_mul_κ
  have hmulG : (k₀ : G) * (k₀ : G) = 1 := congrArg Subtype.val hmul
  have conjK : ∀ g ∈ KN (x₁ : G) (x₂ : G) (x₃ : G),
      (k₀ : G) * g * (k₀ : G)⁻¹ ∈ KN (x₁ : G) (x₂ : G) (x₃ : G) := by
    intro g hg
    have hgN : g ∈ NN (x₁ : G) (x₂ : G) := KN_le_NN _ _ _ hg
    obtain ⟨hy', hφ⟩ := act g hgN
    rw [hK ⟨(k₀ : G) * g * (k₀ : G)⁻¹, hy'⟩, hφ]
    exact M.κ_mem _ ((hK ⟨g, hgN⟩).1 hg)
  have normK : ∀ n : G, ∀ hn : n ∈ NN (x₁ : G) (x₂ : G),
      (∀ g ∈ KN (x₁ : G) (x₂ : G) (x₃ : G), n * g * n⁻¹ ∈ KN (x₁ : G) (x₂ : G) (x₃ : G)) →
        n ∈ KN (x₁ : G) (x₂ : G) (x₃ : G) := by
    intro n hn hnorm
    refine (hK ⟨n, hn⟩).2 (M.normalizer_le _ fun t ht => ?_)
    obtain ⟨y, rfl⟩ := φY.surjective t
    have hy : (y : G) ∈ KN (x₁ : G) (x₂ : G) (x₃ : G) := (hK y).2 ht
    have hc := hnorm _ hy
    have hcN : n * (y : G) * n⁻¹ ∈ NN (x₁ : G) (x₂ : G) := KN_le_NN _ _ _ hc
    have h1 := (hK ⟨n * (y : G) * n⁻¹, hcN⟩).1 hc
    have h2 : (⟨n * (y : G) * n⁻¹, hcN⟩ : ↥(NN (x₁ : G) (x₂ : G))) =
        (⟨n, hn⟩ : ↥(NN (x₁ : G) (x₂ : G))) * y * (⟨n, hn⟩ : ↥(NN (x₁ : G) (x₂ : G)))⁻¹ := rfl
    rw [h2, map_mul, map_mul, map_inv] at h1
    exact h1
  have hnotNN : (k₀ : G) ∉ NN (x₁ : G) (x₂ : G) := by
    intro hkN
    have hkK : (k₀ : G) ∈ KN (x₁ : G) (x₂ : G) (x₃ : G) := normK _ hkN conjK
    have hT := (hK ⟨k₀, hkN⟩).1 hkK
    refine M.not_inner _ hT ?_
    ext y0
    obtain ⟨y, rfl⟩ := φY.surjective y0
    obtain ⟨hy', hφ⟩ := act y y.2
    rw [MulAut.conj_apply, ← hφ]
    have h2 : (⟨(k₀ : G) * (y : G) * (k₀ : G)⁻¹, hy'⟩ : ↥(NN (x₁ : G) (x₂ : G))) =
        (⟨k₀, hkN⟩ : ↥(NN (x₁ : G) (x₂ : G))) * y *
          (⟨k₀, hkN⟩ : ↥(NN (x₁ : G) (x₂ : G)))⁻¹ := rfl
    rw [h2, map_mul, map_mul, map_inv]
  obtain ⟨s, hs1, hs2, hs3, -⟩ := D.exists_swap S
  have h1 : (s : G) * (x₁ : G) * (s : G)⁻¹ = (x₂ : G) := by
    simpa using congrArg Subtype.val hs1
  have h2 : (s : G) * (x₂ : G) * (s : G)⁻¹ = (x₁ : G) := by
    simpa using congrArg Subtype.val hs2
  have h3 : (s : G) * (x₃ : G) * (s : G)⁻¹ = (x₃ : G) := by
    simpa using congrArg Subtype.val hs3
  have hsEN : (s : G) ∈ EN (x₁ : G) (x₂ : G) := swap_mem_EN h1 h2
  have hsNN : (s : G) ∉ NN (x₁ : G) (x₂ : G) := by
    intro hs
    have hmem := conj_mem_zpowers_of_mem_normalizer (mem_NN_iff.1 hs).1
    rw [h1] at hmem
    rcases mem_zpowers_cases (a := (x₁ : G)) (by simpa using congrArg Subtype.val S.pow₁) hmem
      with h | h | h
    · have := orderOf_x₂ S (G := G)
      rw [h, orderOf_one] at this
      omega
    · exact (ne_of_e4H S).1 h
    · exact (ne_of_e4H S).2 h
  have hkNN : (k₀ : G) * (s : G)⁻¹ ∈ NN (x₁ : G) (x₂ : G) := by
    have hk' : k₀ ∉ (NN (x₁ : G) (x₂ : G)).subgroupOf (EN (x₁ : G) (x₂ : G)) := fun h =>
      hnotNN (Subgroup.mem_subgroupOf.1 h)
    have hs' : (⟨(s : G), hsEN⟩ : ↥(EN (x₁ : G) (x₂ : G))) ∉
        (NN (x₁ : G) (x₂ : G)).subgroupOf (EN (x₁ : G) (x₂ : G)) := fun h =>
      hsNN (Subgroup.mem_subgroupOf.1 h)
    exact Subgroup.mem_subgroupOf.1 (mul_inv_mem_of_index_two hidx hk' hs')
  have hinv1 : (s : G)⁻¹ * (x₁ : G) * ((s : G)⁻¹)⁻¹ = (x₂ : G) := by
    calc (s : G)⁻¹ * (x₁ : G) * ((s : G)⁻¹)⁻¹
        = (s : G)⁻¹ * ((s : G) * (x₂ : G) * (s : G)⁻¹) * (s : G) := by rw [h2]; group
      _ = (x₂ : G) := by group
  have hinv2 : (s : G)⁻¹ * (x₂ : G) * ((s : G)⁻¹)⁻¹ = (x₁ : G) := by
    calc (s : G)⁻¹ * (x₂ : G) * ((s : G)⁻¹)⁻¹
        = (s : G)⁻¹ * ((s : G) * (x₁ : G) * (s : G)⁻¹) * (s : G) := by rw [h1]; group
      _ = (x₁ : G) := by group
  have hinv3 : (s : G)⁻¹ * (x₃ : G) * ((s : G)⁻¹)⁻¹ = (x₃ : G) := by
    calc (s : G)⁻¹ * (x₃ : G) * ((s : G)⁻¹)⁻¹
        = (s : G)⁻¹ * ((s : G) * (x₃ : G) * (s : G)⁻¹) * (s : G) := by rw [h3]; group
      _ = (x₃ : G) := by group
  obtain ⟨κ', hκ'def⟩ : ∃ κ' : G, κ' = (k₀ : G) * (s : G)⁻¹ := ⟨_, rfl⟩
  have hκNN : κ' ∈ NN (x₁ : G) (x₂ : G) := by rw [hκ'def]; exact hkNN
  have hκK : κ' ∈ KN (x₁ : G) (x₂ : G) (x₃ : G) := by
    refine normK _ hκNN fun g hg => ?_
    have hg' := conj_swap_mem_KN hinv1 hinv2 hinv3 hg
    have := conjK _ hg'
    convert this using 1
    rw [hκ'def]
    group
  have hkeq : (k₀ : G) = κ' * (s : G) := by rw [hκ'def]; group
  have hκN := mem_KN_iff.1 hκK
  have e1 : (k₀ : G) * (x₁ : G) * (k₀ : G)⁻¹ = κ' * (x₂ : G) * κ'⁻¹ := by
    rw [hkeq]
    calc κ' * (s : G) * (x₁ : G) * (κ' * (s : G))⁻¹
        = κ' * ((s : G) * (x₁ : G) * (s : G)⁻¹) * κ'⁻¹ := by group
      _ = κ' * (x₂ : G) * κ'⁻¹ := by rw [h1]
  have e2 : (k₀ : G) * (x₂ : G) * (k₀ : G)⁻¹ = κ' * (x₁ : G) * κ'⁻¹ := by
    rw [hkeq]
    calc κ' * (s : G) * (x₂ : G) * (κ' * (s : G))⁻¹
        = κ' * ((s : G) * (x₂ : G) * (s : G)⁻¹) * κ'⁻¹ := by group
      _ = κ' * (x₁ : G) * κ'⁻¹ := by rw [h2]
  have e3 : (k₀ : G) * (x₃ : G) * (k₀ : G)⁻¹ = κ' * (x₃ : G) * κ'⁻¹ := by
    rw [hkeq]
    calc κ' * (s : G) * (x₃ : G) * (κ' * (s : G))⁻¹
        = κ' * ((s : G) * (x₃ : G) * (s : G)⁻¹) * κ'⁻¹ := by group
      _ = κ' * (x₃ : G) * κ'⁻¹ := by rw [h3]
  refine ⟨k₀, ⟨k₀.2, act, hmulG, hnotNN, ?_, ?_, ?_, ?_, conjK⟩⟩
  · rw [e1]
    exact conj_mem_zpowers_of_mem_normalizer hκN.2.1
  · rw [e2]
    exact conj_mem_zpowers_of_mem_normalizer hκN.1
  · rw [e3]
    exact conj_mem_zpowers_of_mem_normalizer hκN.2.2
  · rw [hkeq]
    exact Subgroup.mul_mem _ (KN_le_TrN _ _ _ hκK) (swap_mem_TrN h1 h2 h3)

theorem LyData.exists_mulEquiv_mulAut (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    {Y0 : Type*} [Group Y0] (M : Stage2Model Y0) (φY : ↥(NN (x₁ : G) (x₂ : G)) ≃* Y0)
    (hE : Nat.card ↥(EN (x₁ : G) (x₂ : G)) = 699840) :
    ∃ Φ : ↥(EN (x₁ : G) (x₂ : G)) ≃* MulAut ↥(NN (x₁ : G) (x₂ : G)),
      ∀ (e : ↥(EN (x₁ : G) (x₂ : G))) (y : ↥(NN (x₁ : G) (x₂ : G))),
        ((Φ e y : ↥(NN (x₁ : G) (x₂ : G))) : G) = (e : G) * (y : G) * (e : G)⁻¹ := by
  have hNY : ((NN (x₁ : G) (x₂ : G)).subgroupOf (EN (x₁ : G) (x₂ : G))).Normal :=
    Subgroup.normal_of_index_eq_two (D.relIndex_NN_normalizer_EE S)
  have hZ' : ∀ z ∈ NN (x₁ : G) (x₂ : G), (∀ y ∈ NN (x₁ : G) (x₂ : G), z * y = y * z) → z = 1 := by
    intro z hz hcomm
    have hmem : φY ⟨z, hz⟩ ∈ center Y0 := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := φY.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm y y.2).symm
    rw [M.center_eq_bot, Subgroup.mem_bot] at hmem
    have := φY.injective (hmem.trans (map_one φY).symm)
    exact congrArg Subtype.val this
  have hC := D.centralizer_eq_bot S hZ'
  let ψ : ↥((NN (x₁ : G) (x₂ : G)).subgroupOf (EN (x₁ : G) (x₂ : G))) ≃*
      ↥(NN (x₁ : G) (x₂ : G)) := Subgroup.subgroupOfEquivOfLe (NN_le_normalizer_EE _ _)
  have hcard : Nat.card (MulAut ↥(NN (x₁ : G) (x₂ : G))) ≤ Nat.card ↥(EN (x₁ : G) (x₂ : G)) := by
    rw [hE, Nat.card_congr (MulAut.congr φY).toEquiv]
    exact M.card_aut_le
  obtain ⟨Φ, hΦ⟩ := exists_conjEquiv_transport
    ((NN (x₁ : G) (x₂ : G)).subgroupOf (EN (x₁ : G) (x₂ : G))) ψ hC hcard
  refine ⟨Φ, fun e y => ?_⟩
  have h := hΦ e (ψ.symm y)
  rw [ψ.apply_symm_apply] at h
  rw [h]
  rfl

end Main2

end CFSG.Sporadic.Recognition.LyonsSims
