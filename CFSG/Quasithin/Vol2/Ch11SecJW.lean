module

public import CFSG.Quasithin.Vol2.Ch11SecD557T
public import CFSG.Quasithin.Vol2.Ch11SecJSetup

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecJ

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Quasithin.SL3Model CFSG.Quasithin.SL2Model
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped MatrixGroups Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

omit [Finite G] in
theorem eq_of_isNaturalSection {K W X : Subgroup G} {F : Type} [Field F] {N : Subgroup ↥K}
    (hnat : IsNaturalSection K W V₁ N (StatedSL 2 F)) (hV₁X : V₁ ≤ X) (hXW : X ≤ W)
    (hKX : K ≤ Subgroup.normalizer (X : Set G)) : X = V₁ ∨ X = W := by
  obtain ⟨hKW, α', hα', -, β', -, hker, heq⟩ := hnat
  let Y : Subgroup (Wm F) := (X.subgroupOf W).map β'
  have hY : ∀ A : SL(2, F), ∀ y ∈ Y, SL2Model.natAct A y ∈ Y := by
    intro A y hy
    obtain ⟨w, hw, rfl⟩ := hy
    obtain ⟨k, hk⟩ := hα' ((SecD.statedSLEquiv' 2 F).symm A)
    have hkw : (k : G) * w * (k : G)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hKW k.2) w).mp w.2
    refine ⟨⟨_, hkw⟩, ?_, ?_⟩
    · simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hw ⊢
      exact (Subgroup.mem_normalizer_iff.mp (hKX k.2) w).mp hw
    · have h1 := heq k w ⟨_, hkw⟩ rfl
      apply Multiplicative.toAdd.injective
      rw [h1, SL2Model.natAct_apply, toAdd_ofAdd, hk, ← SecD.coe_statedSLEquiv',
        MulEquiv.apply_symm_apply]
      rfl
  rcases SL2Model.natAct_irreducible Y hY with hb | ht
  · left
    refine le_antisymm (fun x hx => ?_) hV₁X
    have h1 : β' ⟨x, hXW hx⟩ ∈ Y := ⟨⟨x, hXW hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    rw [hb, Subgroup.mem_bot] at h1
    have h2 : (⟨x, hXW hx⟩ : ↥W) ∈ β'.ker := h1
    rw [hker, Subgroup.mem_subgroupOf] at h2
    exact h2
  · right
    refine le_antisymm hXW (fun w hw => ?_)
    have h1 : β' ⟨w, hw⟩ ∈ Y := by rw [ht]; exact Subgroup.mem_top _
    obtain ⟨y, hy, hyw⟩ := h1
    have h2 : y⁻¹ * ⟨w, hw⟩ ∈ β'.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyw, inv_mul_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at h2
    have h3 := X.mul_mem (Subgroup.mem_subgroupOf.1 hy) (hV₁X h2)
    simpa using h3

namespace Core

variable (C : Core G T L I n V₁)

include C in
theorem card_V₁ : Nat.card ↥V₁ = 2 ^ n := by
  have h1 := SecA.IsVi.relIndex_eq C.hV₁
  rw [SecD.inf_centralizer_eq_bot_of_natData C.St.D, Subgroup.relIndex_bot_left, mul_one] at h1
  exact h1

include C in
theorem card_V : Nat.card ↥(fsuV T I) = 2 ^ (3 * n) := by
  have hn0 : n ≠ 0 := by have := C.h.one_lt; omega
  rw [Nat.card_congr C.St.D.ψ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
    GaloisField.card 2 n hn0, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul, mul_comm]

include C in
theorem exists_complement (h1110 : Stmt11_1_0) (h1154 : Stmt11_5_4) (h1155 : Stmt11_5_5) :
    ∃ W : Subgroup G, V₁ ≤ W ∧ W ≤ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ∧
      W ⊓ fsuV T I = V₁ ∧
      W ⊔ fsuV T I = conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ∧
      LOf L V₁ ≤ Subgroup.normalizer (W : Set G) := by
  obtain ⟨s, W, F, _, _, hF, hW, hsup, hnat⟩ :=
    SecD.stmt11_5_5_normalizer_three h1110 h1154 h1155 C.h C.hV₁ C.hSL3 C.hK
  obtain ⟨h5one, h5two, -⟩ := SecD.stmt11_5_5_normalizer h1110 h1154 h1155 C.h C.hV₁ C.hSL3
  set U := conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) with hU
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ V₁ := fun a ha b hb =>
    h5two (Subgroup.commutator_mem_commutator ha (h5one hb))
  have hVU : fsuV T I ≤ U := le_conjClosure _ _
  have hV₁V : V₁ ≤ fsuV T I := C.St.hyp.base.le_V
  have hn := C.h.one_lt
  obtain ⟨i, hi⟩ : ∃ i, ¬ W i ≤ fsuV T I := by
    by_contra hall
    push Not at hall
    have hle : U ≤ fsuV T I := hsup ▸ sup_le hV₁V (iSup_le hall)
    have h1 := Subgroup.card_le_of_le hle
    rw [C.hcard, C.card_V] at h1
    have h2 : 2 ^ (3 * n) < 2 ^ (5 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hnat' := hnat i
  rw [C.hK] at hnat'
  have hKW : LOf L V₁ ≤ Subgroup.normalizer (W i : Set G) := hnat'.1
  have hKV : LOf L V₁ ≤ Subgroup.normalizer (fsuV T I : Set G) := lOf_le_L.trans C.St.D.hnorm
  have hX : W i ⊓ fsuV T I = V₁ := by
    rcases eq_of_isNaturalSection hnat' (le_inf (hW i).1 hV₁V) inf_le_left
        (fun k hk => Subgroup.inf_normalizer_le_normalizer_inf ⟨hKW hk, hKV hk⟩) with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) hi
  obtain ⟨-, α', -, -, β', hβ', hker, -⟩ := hnat'
  have hWcard : Nat.card ↥(W i) = 2 ^ n * (2 ^ n) ^ 2 := by
    have h1 := Subgroup.card_mul_index β'.ker
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hβ', Subgroup.card_top, hker] at h1
    rw [← h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hW i).1).toEquiv, C.card_V₁,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_eq_fintype_card (α := F), hF]
    simp
  have hVW : fsuV T I ≤ Subgroup.normalizer (W i : Set G) := fun v hv =>
    A4.mem_normalizer_of_conj_mem fun w hw => by
      have h2 := (W i).mul_mem ((hW i).1 (hUcomm v (hVU hv) w ((hW i).2 hw))) hw
      simpa using h2
  have hrel := B6.relIndex_inf_eq_relIndex_sup hVW
  rw [inf_comm, hX] at hrel
  have e2 := Subgroup.relIndex_mul_card V₁ (W i)
  rw [inf_eq_left.2 (hW i).1, hWcard, C.card_V₁] at e2
  have hrel2 : V₁.relIndex (W i) = (2 ^ n) ^ 2 := by
    have hpos : 0 < 2 ^ n := by positivity
    have e3 : V₁.relIndex (W i) * 2 ^ n = (2 ^ n) ^ 2 * 2 ^ n := by rw [e2]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos e3
  have e1 := Subgroup.relIndex_mul_card (fsuV T I) (fsuV T I ⊔ W i)
  rw [inf_eq_left.2 le_sup_left, ← hrel, hrel2, C.card_V] at e1
  refine ⟨W i, (hW i).1, (hW i).2, hX, ?_, hKW⟩
  rw [sup_comm]
  refine Subgroup.eq_of_le_of_card_ge (sup_le hVU (hW i).2) ?_
  rw [← e1, C.hcard]
  apply le_of_eq
  rw [← pow_mul, ← pow_add]
  congr 1
  ring

end Core

end CFSG.Quasithin.Vol2.Ch11.SecJ
