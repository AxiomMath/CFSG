module

public import CFSG.Quasithin.Vol2.Ch10SecEE3Q

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE.C10P02

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique Equiv
open CFSG.QuasithinUnique.A5.Delta5 (pact isEven)

theorem pact_sA_sub_eq_zero : ∀ x y : Fin 5 → ZMod 2,
    pact sA x - x = pact sB y - y → pact sA x - x = 0 := by
  decide +kernel

theorem pact_sB_sub_eq_zero : ∀ x y : Fin 5 → ZMod 2,
    pact sB x - x = pact sA y - y → pact sB x - x = 0 := by
  decide +kernel

section Component

variable {W : Type*} [CommGroup W] {K : Subgroup (MulAut W)} {θ : ↥K ≃* Perm (Fin 5)}
  {β : ↥(commV K) ≃* Multiplicative (evenWeight 5)}

@[expose] noncomputable def crd (β : ↥(commV K) ≃* Multiplicative (evenWeight 5))
    (u : ↥(commV K)) : Fin 5 → ZMod 2 :=
  ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2)

theorem crd_injective : Function.Injective (crd β) := by
  intro u u' h
  apply β.injective
  apply Multiplicative.toAdd.injective
  exact Subtype.ext h

theorem crd_mul (u u' : ↥(commV K)) : crd β (u * u') = crd β u + crd β u' := by
  unfold crd
  rw [map_mul, toAdd_mul, AddSubgroup.coe_add]

theorem crd_inv (u : ↥(commV K)) : crd β u⁻¹ = - crd β u := by
  unfold crd
  rw [map_inv, toAdd_inv]
  rfl

theorem crd_one : crd β 1 = 0 := by
  unfold crd
  rw [map_one, toAdd_one, AddSubgroup.coe_zero]

theorem crd_symm_ofAdd (y : evenWeight 5) :
    crd β (β.symm (Multiplicative.ofAdd y)) = (y : Fin 5 → ZMod 2) := by
  simp [crd]

theorem crd_symm_apply (hβ : A5Equivariant θ β) (σ : Perm (Fin 5)) (u : ↥(commV K)) :
    crd β ⟨((θ.symm σ : ↥K) : MulAut W) (u : W), commV_invariant K _ (θ.symm σ).2 _ u.2⟩ =
      pact σ (crd β u) := by
  have h := coord_apply θ β hβ (θ.symm σ) u
  rw [MulEquiv.apply_symm_apply] at h
  exact h

theorem comm_eq_one_of_eq (hβ : A5Equivariant θ β) {σ σ' : Perm (Fin 5)}
    (hσ : (σ = sA ∧ σ' = sB) ∨ (σ = sB ∧ σ' = sA)) {u u' : W} (hu : u ∈ commV K)
    (hu' : u' ∈ commV K)
    (h : ((θ.symm σ : ↥K) : MulAut W) u * u⁻¹ = ((θ.symm σ' : ↥K) : MulAut W) u' * u'⁻¹) :
    ((θ.symm σ : ↥K) : MulAut W) u * u⁻¹ = 1 := by
  set U : ↥(commV K) := ⟨u, hu⟩
  set U' : ↥(commV K) := ⟨u', hu'⟩
  set X : ↥(commV K) :=
    ⟨((θ.symm σ : ↥K) : MulAut W) u, commV_invariant K _ (θ.symm σ).2 _ hu⟩ * U⁻¹ with hX
  set X' : ↥(commV K) :=
    ⟨((θ.symm σ' : ↥K) : MulAut W) u', commV_invariant K _ (θ.symm σ').2 _ hu'⟩ * U'⁻¹ with hX'
  have hXX : X = X' := Subtype.ext h
  have hc : crd β X = pact σ (crd β U) - crd β U := by
    rw [hX, crd_mul, crd_inv, crd_symm_apply hβ σ U]
    exact (sub_eq_add_neg _ _).symm
  have hc' : crd β X' = pact σ' (crd β U') - crd β U' := by
    rw [hX', crd_mul, crd_inv, crd_symm_apply hβ σ' U']
    exact (sub_eq_add_neg _ _).symm
  have h0 : crd β X = 0 := by
    rw [hc]
    rcases hσ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact pact_sA_sub_eq_zero _ _ (hc ▸ hXX ▸ hc')
    · exact pact_sB_sub_eq_zero _ _ (hc ▸ hXX ▸ hc')
  have hX1 : X = 1 := crd_injective (h0.trans crd_one.symm)
  exact congrArg Subtype.val hX1

theorem comm_mem {a : MulAut W} (ha : a ∈ K) {u : W} (hu : u ∈ commV K) :
    a u * u⁻¹ ∈ commV K :=
  (commV K).mul_mem (commV_invariant K _ ha _ hu) ((commV K).inv_mem hu)

end Component

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {hyp : Hyp10 G T L I} {t : G}
  (D : Case2Data hyp t)

theorem tau_mem_K₁ {i : Fin 4} (hi : i = 0 ∨ i = 1) : D.tau i ∈ D.K₁ := by
  rcases hi with rfl | rfl
  exacts [(D.θ₁.symm sA).2, (D.θ₁.symm sB).2]

theorem tau_mem_K₂ {i : Fin 4} (hi : i = 2 ∨ i = 3) : D.tau i ∈ D.K₂ := by
  rcases hi with rfl | rfl
  exacts [(D.θ₂.symm sA).2, (D.θ₂.symm sB).2]

theorem exists_comm_eq₁ (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥)
    {a : MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp))} (ha : a ∈ D.K₁)
    (w : IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)) :
    ∃ u ∈ commV D.K₁, a w * w⁻¹ = a u * u⁻¹ := by
  have hw : w ∈ commV D.K₁ ⊔ commV D.K₂ := by
    rw [D.commV_sup_eq_top hC0]; exact Subgroup.mem_top w
  obtain ⟨u, hu, z, hz, rfl⟩ := Subgroup.mem_sup.mp hw
  refine ⟨u, hu, ?_⟩
  rw [map_mul, D.triv₁ ha hz, mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]

theorem exists_comm_eq₂ (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥)
    {b : MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp))} (hb : b ∈ D.K₂)
    (w : IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)) :
    ∃ z ∈ commV D.K₂, b w * w⁻¹ = b z * z⁻¹ := by
  have hw : w ∈ commV D.K₁ ⊔ commV D.K₂ := by
    rw [D.commV_sup_eq_top hC0]; exact Subgroup.mem_top w
  obtain ⟨u, hu, z, hz, rfl⟩ := Subgroup.mem_sup.mp hw
  refine ⟨z, hz, ?_⟩
  rw [map_mul, D.triv₂ hb hu, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]

theorem tau_comm_mem₁ (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥) {i : Fin 4}
    (hi : i = 0 ∨ i = 1) (w : IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)) :
    D.tau i w * w⁻¹ ∈ commV D.K₁ := by
  obtain ⟨u, hu, e⟩ := exists_comm_eq₁ D hC0 (tau_mem_K₁ D hi) w
  rw [e]
  exact comm_mem (tau_mem_K₁ D hi) hu

theorem tau_comm_mem₂ (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥) {i : Fin 4}
    (hi : i = 2 ∨ i = 3) (w : IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)) :
    D.tau i w * w⁻¹ ∈ commV D.K₂ := by
  obtain ⟨z, hz, e⟩ := exists_comm_eq₂ D hC0 (tau_mem_K₂ D hi) w
  rw [e]
  exact comm_mem (tau_mem_K₂ D hi) hz

theorem same_comp₁ (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥)
    {σ σ' : Perm (Fin 5)} (hσ : (σ = sA ∧ σ' = sB) ∨ (σ = sB ∧ σ' = sA))
    {w w' : IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)}
    (h : ((D.θ₁.symm σ : ↥D.K₁) : MulAut _) w * w⁻¹ =
      ((D.θ₁.symm σ' : ↥D.K₁) : MulAut _) w' * w'⁻¹) :
    ((D.θ₁.symm σ : ↥D.K₁) : MulAut _) w * w⁻¹ = 1 := by
  obtain ⟨u, hu, e⟩ := exists_comm_eq₁ D hC0 (D.θ₁.symm σ).2 w
  obtain ⟨u', hu', e'⟩ := exists_comm_eq₁ D hC0 (D.θ₁.symm σ').2 w'
  rw [e, e'] at h
  rw [e]
  exact comm_eq_one_of_eq D.equiv₁ hσ hu hu' h

theorem same_comp₂ (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥)
    {σ σ' : Perm (Fin 5)} (hσ : (σ = sA ∧ σ' = sB) ∨ (σ = sB ∧ σ' = sA))
    {w w' : IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)}
    (h : ((D.θ₂.symm σ : ↥D.K₂) : MulAut _) w * w⁻¹ =
      ((D.θ₂.symm σ' : ↥D.K₂) : MulAut _) w' * w'⁻¹) :
    ((D.θ₂.symm σ : ↥D.K₂) : MulAut _) w * w⁻¹ = 1 := by
  obtain ⟨u, hu, e⟩ := exists_comm_eq₂ D hC0 (D.θ₂.symm σ).2 w
  obtain ⟨u', hu', e'⟩ := exists_comm_eq₂ D hC0 (D.θ₂.symm σ').2 w'
  rw [e, e'] at h
  rw [e]
  exact comm_eq_one_of_eq D.equiv₂ hσ hu hu' h

theorem cross_comp (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥) {i j : Fin 4}
    (hi : i = 0 ∨ i = 1) (hj : j = 2 ∨ j = 3)
    {w w' : IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)}
    (h : D.tau i w * w⁻¹ = D.tau j w' * w'⁻¹) : D.tau i w * w⁻¹ = 1 := by
  have h1 := tau_comm_mem₁ D hC0 hi w
  have h2 := tau_comm_mem₂ D hC0 hj w'
  rw [← h] at h2
  have h3 : D.tau i w * w⁻¹ ∈ commV D.K₁ ⊓ commV D.K₂ := ⟨h1, h2⟩
  rw [D.commV_inf_commV] at h3
  exact h3

theorem tau_comm_eq_one (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥) {i j : Fin 4}
    (hij : i ≠ j) {w w' : IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)}
    (h : D.tau i w * w⁻¹ = D.tau j w' * w'⁻¹) : D.tau i w * w⁻¹ = 1 := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact same_comp₁ D hC0 (Or.inl ⟨rfl, rfl⟩) h
  · exact cross_comp D hC0 (by decide) (by decide) h
  · exact cross_comp D hC0 (by decide) (by decide) h
  · exact same_comp₁ D hC0 (Or.inr ⟨rfl, rfl⟩) h
  · exact absurd rfl hij
  · exact cross_comp D hC0 (by decide) (by decide) h
  · exact cross_comp D hC0 (by decide) (by decide) h
  · exact h.trans (cross_comp D hC0 (by decide) (by decide) h.symm)
  · exact h.trans (cross_comp D hC0 (by decide) (by decide) h.symm)
  · exact absurd rfl hij
  · exact same_comp₂ D hC0 (Or.inl ⟨rfl, rfl⟩) h
  · exact h.trans (cross_comp D hC0 (by decide) (by decide) h.symm)
  · exact h.trans (cross_comp D hC0 (by decide) (by decide) h.symm)
  · exact same_comp₂ D hC0 (Or.inr ⟨rfl, rfl⟩) h
  · exact absurd rfl hij

end CFSG.Quasithin.Vol2.Ch10.SecE.C10P02
