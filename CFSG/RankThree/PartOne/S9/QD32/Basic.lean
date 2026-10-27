module

public import CFSG.RankThree.GroupTheory.SteinbergBYQD32Extraspecial

public section

namespace CFSG.RankThree.PartOne.QD32Facts

open CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY Subgroup
open scoped commutatorElement

instance instFiniteQD32 : Finite QD32 :=
  Nat.finite_of_card_ne_zero (by rw [card_QD32]; norm_num)

theorem card_dvd_two_pow_of_displacement {S : Type*} [Group S] {z : S} (hz : orderOf z = 2)
    {m : ℕ} (g : Fin m → S) (hg : closure (Set.range g) = ⊤) (K : Subgroup (MulAut S))
    (hK : ∀ α ∈ K, α z = z ∧ ∀ i, (g i)⁻¹ * α (g i) ∈ zpowers z) :
    Nat.card K ∣ 2 ^ m := by
  have hfix : ∀ α ∈ K, ∀ w ∈ zpowers z, α w = w := by
    intro α hα w hw
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hw
    rw [map_zpow, (hK α hα).1]
  let δ : Fin m → K →* zpowers z := fun i =>
    { toFun := fun α => ⟨(g i)⁻¹ * α.1 (g i), (hK α.1 α.2).2 i⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro α β
        apply Subtype.ext
        have hβ := (hK β.1 β.2).2 i
        have h1 : β.1 (g i) = g i * ((g i)⁻¹ * β.1 (g i)) := by group
        have h2 : α.1 (β.1 (g i)) = α.1 (g i) * ((g i)⁻¹ * β.1 (g i)) := by
          conv_lhs => rw [h1]
          rw [map_mul, hfix α.1 α.2 _ hβ]
        change (g i)⁻¹ * α.1 (β.1 (g i)) = ((g i)⁻¹ * α.1 (g i)) * ((g i)⁻¹ * β.1 (g i))
        rw [h2]
        group }
  let Δ : K →* (Fin m → zpowers z) := MonoidHom.pi δ
  have hΔ : Function.Injective Δ := by
    rw [injective_iff_map_eq_one]
    intro α hα
    have hα' : ∀ i, α.1 (g i) = g i := by
      intro i
      have h := congrArg Subtype.val (congrFun hα i)
      change (g i)⁻¹ * α.1 (g i) = 1 at h
      exact (inv_mul_eq_one.mp h).symm
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    have key : (α.1.toMonoidHom) = (1 : MulAut S).toMonoidHom := by
      apply MonoidHom.eq_of_eqOn_dense (s := Set.range g)
      · exact hg
      · rintro _ ⟨i, rfl⟩
        exact hα' i
    exact DFunLike.congr_fun key x
  have hcard := Subgroup.card_dvd_of_injective Δ hΔ
  have h2 : Nat.card (Fin m → zpowers z) = 2 ^ m := by
    rw [Nat.card_fun, Nat.card_zpowers, hz, Nat.card_eq_fintype_card, Fintype.card_fin]
  rwa [h2] at hcard

@[expose] def qd32Gens : Fin 4 → QD32 :=
  ![qd32I * qd32U, qd32J * qd32U, qd32I * qd32J * qd32U, qd32V]

theorem closure_range_qd32Gens : closure (Set.range qd32Gens) = ⊤ := by
  have h := (quaternion_dihedral_extraspecial_involution_generation).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [← h]
  congr 1
  ext x
  simp only [Set.mem_range, qd32Gens, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

theorem center_QD32 : center QD32 = zpowers qd32Z :=
  (quaternion_dihedral_extraspecial_involution_generation).2.2.2.2.2.2.2.1

theorem commutator_QD32 : commutator QD32 = zpowers qd32Z :=
  (quaternion_dihedral_extraspecial_involution_generation).2.2.2.2.2.2.2.2.1

theorem mem_center_QD32_iff (x : QD32) : x ∈ center QD32 ↔ x = 1 ∨ x = qd32Z := by
  rw [center_QD32, mem_zpowers_qd32Z]

theorem qd32Z_mul_self : qd32Z * qd32Z = 1 := by
  have := pow_orderOf_eq_one qd32Z
  rw [orderOf_qd32Z] at this
  rw [← pow_two]
  exact this

theorem aut_mem_center {S : Type*} [Group S] (α : MulAut S) {w : S} (hw : w ∈ center S) :
    α w ∈ center S := by
  rw [mem_center_iff] at hw ⊢
  intro y
  have h := congrArg α (hw (α.symm y))
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h

theorem aut_qd32Z (α : MulAut QD32) : α qd32Z = qd32Z := by
  have hc : α qd32Z ∈ center QD32 := aut_mem_center α (center_QD32 ▸ mem_zpowers qd32Z)
  rw [mem_center_QD32_iff] at hc
  rcases hc with h | h
  · exfalso
    have h1 : qd32Z = 1 := α.injective (h.trans (map_one α).symm)
    have := orderOf_qd32Z
    rw [h1, orderOf_one] at this
    omega
  · exact h

@[expose] def trivialOnCenterQuotient (S : Type*) [Group S] : Subgroup (MulAut S) where
  carrier := {α | ∀ s, s⁻¹ * α s ∈ center S}
  one_mem' := by
    intro s
    simp [one_mem]
  mul_mem' := by
    intro α β hα hβ s
    have hw := hβ s
    have h1 : β s = s * (s⁻¹ * β s) := by group
    have h2 : s⁻¹ * (α * β) s = (s⁻¹ * α s) * α (s⁻¹ * β s) := by
      rw [MulAut.mul_apply]
      conv_lhs => rw [h1]
      rw [map_mul]
      group
    rw [h2]
    exact mul_mem (hα s) (aut_mem_center α hw)
  inv_mem' := by
    intro α hα s
    have h := hα (α⁻¹ s)
    rw [MulAut.apply_inv_self] at h
    have h2 := inv_mem h
    rwa [mul_inv_rev, inv_inv] at h2

theorem mem_trivialOnCenterQuotient {S : Type*} [Group S] {α : MulAut S} :
    α ∈ trivialOnCenterQuotient S ↔ ∀ s, s⁻¹ * α s ∈ center S := Iff.rfl

theorem ker_conj_eq_center (S : Type*) [Group S] :
    (MulAut.conj : S →* MulAut S).ker = center S := by
  ext s
  rw [MonoidHom.mem_ker, mem_center_iff]
  constructor
  · intro h g
    have := congrArg (fun f : MulAut S => f g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * s = (s * g * s⁻¹) * s := by rw [this]
      _ = s * g := by group
  · intro h
    ext g
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h g, mul_inv_cancel_right]

theorem card_range_conj_QD32 : Nat.card (MulAut.conj : QD32 →* MulAut QD32).range = 16 := by
  have h := Subgroup.card_ker_mul_card_range (MulAut.conj : QD32 →* MulAut QD32)
  rw [ker_conj_eq_center, center_QD32, Nat.card_zpowers, orderOf_qd32Z, card_QD32] at h
  omega

theorem card_dvd_trivialOnCenterQuotient_QD32 :
    Nat.card (trivialOnCenterQuotient QD32) ∣ 16 := by
  have h := card_dvd_two_pow_of_displacement (z := qd32Z) orderOf_qd32Z qd32Gens
    closure_range_qd32Gens (trivialOnCenterQuotient QD32) (fun α hα => ⟨aut_qd32Z α, fun i => by
      have := hα (qd32Gens i)
      rwa [center_QD32] at this⟩)
  simpa using h

theorem trivialOnCenterQuotient_QD32_eq : trivialOnCenterQuotient QD32 =
    (MulAut.conj : QD32 →* MulAut QD32).range := by
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨s₀, rfl⟩ s
    rw [center_QD32, ← commutator_QD32, commutator_def]
    have : s⁻¹ * (MulAut.conj s₀) s = ⁅s⁻¹, s₀⁆ := by
      simp only [MulAut.conj_apply, commutatorElement_def]
      group
    rw [this]
    exact commutator_mem_commutator (mem_top _) (mem_top _)
  · rw [card_range_conj_QD32]
    exact Nat.le_of_dvd (by norm_num) card_dvd_trivialOnCenterQuotient_QD32

theorem exists_conj_of_trivialOnCenterQuotient_QD32 {α : MulAut QD32}
    (hα : ∀ s, s⁻¹ * α s ∈ center QD32) : ∃ s₀ : QD32, α = MulAut.conj s₀ := by
  have : α ∈ trivialOnCenterQuotient QD32 := hα
  rw [trivialOnCenterQuotient_QD32_eq] at this
  obtain ⟨s₀, hs₀⟩ := this
  exact ⟨s₀, hs₀.symm⟩

theorem exists_data_of_equiv_QD32 {S : Type*} [Group S] (φ : S ≃* QD32) :
    ∃ z : S, orderOf z = 2 ∧ center S = zpowers z ∧ (∃ i j : S, ⁅i, j⁆ = z) ∧
      closure {s : S | s ^ 2 = 1} = ⊤ ∧
      ∀ α : MulAut S, (∀ s, s⁻¹ * α s ∈ center S) → ∃ s₀ : S, α = MulAut.conj s₀ := by
  refine ⟨φ.symm qd32Z, ?_, ?_, ⟨φ.symm qd32I, φ.symm qd32J, ?_⟩, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, orderOf_qd32Z]
  · rw [← map_center_eq (φ.symm : QD32 ≃* S), center_QD32, MonoidHom.map_zpowers]
    rfl
  · rw [← map_commutatorElement, commutatorElement_qd32I_qd32J]
  · rw [eq_top_iff]
    intro s _
    have hs : φ s ∈ closure {g : QD32 | orderOf g = 2} := by
      rw [(quaternion_dihedral_extraspecial_involution_generation).2.2.1]
      exact mem_top _
    have hmap : (closure {g : QD32 | orderOf g = 2}).map (φ.symm : QD32 →* S) ≤
        closure {s : S | s ^ 2 = 1} := by
      rw [MonoidHom.map_closure, closure_le]
      rintro _ ⟨g, hg, rfl⟩
      apply Subgroup.subset_closure
      change (φ.symm g) ^ 2 = 1
      have hg2 : g ^ 2 = 1 := by
        have := pow_orderOf_eq_one g
        rwa [show orderOf g = 2 from hg] at this
      rw [← map_pow, hg2, map_one]
    refine hmap ⟨φ s, hs, ?_⟩
    simp
  · intro α hα
    let α' : MulAut QD32 := (φ.symm.trans α).trans φ
    have hα' : ∀ g, g⁻¹ * α' g ∈ center QD32 := by
      intro g
      have h2 : φ ((φ.symm g)⁻¹ * α (φ.symm g)) ∈ center QD32 := by
        rw [← map_center_eq φ]
        exact mem_map_of_mem _ (hα (φ.symm g))
      simpa [α'] using h2
    obtain ⟨s₀, hs₀⟩ := exists_conj_of_trivialOnCenterQuotient_QD32 hα'
    refine ⟨φ.symm s₀, ?_⟩
    ext s
    have := congrArg (fun f : MulAut QD32 => φ.symm (f (φ s))) hs₀
    simpa [α', MulAut.conj_apply] using this

end CFSG.RankThree.PartOne.QD32Facts
