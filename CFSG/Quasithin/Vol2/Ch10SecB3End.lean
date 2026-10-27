module

public import CFSG.Quasithin.Vol2.Ch10SecB3Comm
public import CFSG.Quasithin.Vol2.Ch10SecB3Facts

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

@[expose] def TrivOnU (T L I : Subgroup G) (p : ℕ) : Prop :=
  ∀ A' : Subgroup (MulAut ↥(fsuUL T L I)), ¬ p ∣ Nat.card (autOn L (fsuUL T L I)) →
    IsPGroup p A' → (∀ x ∈ A', ∀ h ∈ autOn L (fsuUL T L I), x * h = h * x) →
    (∀ x ∈ A', ∀ z ∈ cV1 T L I, x z ∈ cV1 T L I) →
    ∀ x ∈ A', ∀ v : ↥(fsuUL T L I), x v * v⁻¹ ∈ cV1 T L I

theorem commutator_fsuUL_eq_bot_of (hyp : Hyp10 G T L I) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpL : ¬ p ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) (hfact : TrivOnU T L I p) {A : Subgroup G}
    (hA : A ≤ cenL0 T L I) (hAp : IsPGroup p A) : ⁅fsuUL T L I, A⁆ = ⊥ := by
  have hc : ∀ a ∈ A, ∀ l ∈ L,
      a * l * a⁻¹ * l⁻¹ ∈ Subgroup.centralizer (fsuUL T L I : Set G) := fun a ha l hl =>
    Subgroup.centralizer_le (fsuUL_le' T L I) ((mem_cenL0.mp (hA ha)).2 l (SecA.le_fsuL0 T L hl))
  exact commutator_fsuUL_eq_bot hyp hA (comm_mem_of_autOn hA
    (hfact _ (not_dvd_card_autOn_L hp hp2 hpL _) (isPGroup_autOn hAp) (autOn_comm hc)
      (autOn_mem_cV1 hA)))

theorem commutator_fsuVM_eq_bot_of_conj (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {A : Subgroup G} (h1 : ⁅fsuUL T L I, A⁆ = ⊥)
    (h2 : ⁅fsuUL T L I, A.map (MulAut.conj t).toMonoidHom⁆ = ⊥) : ⁅fsuVM T L I, A⁆ = ⊥ := by
  have htM : t ∈ fsuM T L := SecA.le_fsuM T L ht
  have h3 : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ Subgroup.centralizer (A : Set G) := by
    rw [← SecA.conjugate_commutator_fsuVM htM]
    intro x hx
    rw [SecA.mem_conjugate_iff] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hta : t * a * t⁻¹ ∈ A.map (MulAut.conj t).toMonoidHom :=
      ⟨a, ha, by simp [MulAut.conj_apply]⟩
    have hc := Subgroup.mem_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2) hx) _ hta
    have e : t * (a * x) * t⁻¹ = t * (x * a) * t⁻¹ := by
      calc t * (a * x) * t⁻¹ = t * a * t⁻¹ * (t * x * t⁻¹) := by group
        _ = t * x * t⁻¹ * (t * a * t⁻¹) := hc
        _ = t * (x * a) * t⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, SecA.fsuVM_eq_sup h37 h38 hyp ht htn]
  exact sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1) h3

omit [Finite G] in
theorem map_conj_le_cenL0 {t : G} (htM : t ∈ fsuM T L) {A : Subgroup G}
    (hA : A ≤ cenL0 T L I) : A.map (MulAut.conj t).toMonoidHom ≤ cenL0 T L I := by
  rintro _ ⟨a, ha, rfl⟩
  have := (Subgroup.mem_normalizer_iff.mp (fsuM_le_normalizer_cenL0 T L I htM) a).mp (hA ha)
  simpa [MulAut.conj_apply] using this

theorem commutator_fsuVM_eq_bot_of_U (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {p : ℕ}
    (hU : ∀ A : Subgroup G, A ≤ cenL0 T L I → IsPGroup p A → ⁅fsuUL T L I, A⁆ = ⊥)
    {A : Subgroup G} (hA : A ≤ cenL0 T L I) (hAp : IsPGroup p A) : ⁅fsuVM T L I, A⁆ = ⊥ := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  exact commutator_fsuVM_eq_bot_of_conj h37 h38 hyp ht htn (hU A hA hAp)
    (hU _ (map_conj_le_cenL0 (SecA.le_fsuM T L ht) hA) (hAp.map _))

theorem trivOnU_of_one (hF : FactCommNatSL) {n : ℕ} (h1 : Case10_1_1One T L I n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : TrivOnU T L I p := by
  obtain ⟨-, -, hab, hnat⟩ := h1
  intro A' hpH hA'p hcomm hZ
  exact hF ↥(fsuUL T L I) (autOn L (fsuUL T L I)) A' (cV1 T L I) 2 n p le_rfl hnat hp hp2 hpH
    hA'p hcomm hZ

theorem trivOnU_of_three (hF : FactCommNatSL) (h3 : Case10_1_1Three T L I) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : TrivOnU T L I p := by
  obtain ⟨-, hab, hnat⟩ := h3
  intro A' hpH hA'p hcomm hZ
  exact hF ↥(fsuUL T L I) (autOn L (fsuUL T L I)) A' (cV1 T L I) 3 1 p (by norm_num) hnat hp
    hp2 hpH hA'p hcomm hZ

theorem trivOnU_of_two (hF : FactCommAlt5) (h2 : Case10_1_1Two T L I) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : TrivOnU T L I p := by
  obtain ⟨-, hab, hnat⟩ := h2
  intro A' hpH hA'p hcomm _ x hx v
  have h := hF ↥(fsuUL T L I) (autOn L (fsuUL T L I)) A' ⊥ p hnat hp hp2 hpH hA'p hcomm
    (fun x _ z hz => by rw [Subgroup.mem_bot] at hz ⊢; rw [hz, map_one]) x hx v
  rw [Subgroup.mem_bot] at h
  rw [h]
  exact Subgroup.one_mem _

theorem trivOnU_of_four (hF : FactCommOrth) {n : ℕ} (h4 : Case10_1_1Four T L I n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : TrivOnU T L I p := by
  obtain ⟨-, -, hab, hnat⟩ := h4
  intro A' hpH hA'p hcomm _ x hx v
  have h := hF ↥(fsuUL T L I) (autOn L (fsuUL T L I)) A' ⊥ n p hnat hp hp2 hpH hA'p hcomm
    (fun x _ z hz => by rw [Subgroup.mem_bot] at hz ⊢; rw [hz, map_one]) x hx v
  rw [Subgroup.mem_bot] at h
  rw [h]
  exact Subgroup.one_mem _

theorem trivOnU_of_seven (hF : FactCommSz) (h7 : Case10_1_1Seven T L I) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : TrivOnU T L I p := by
  obtain ⟨n, -, hab, hnat⟩ := h7
  intro A' hpH hA'p hcomm _ x hx v
  have h := hF ↥(fsuUL T L I) (autOn L (fsuUL T L I)) A' ⊥ n p hnat hp hp2 hpH hA'p hcomm
    (fun x _ z hz => by rw [Subgroup.mem_bot] at hz ⊢; rw [hz, map_one]) x hx v
  rw [Subgroup.mem_bot] at h
  rw [h]
  exact Subgroup.one_mem _

end CFSG.Quasithin.Vol2.Ch10.SecB
