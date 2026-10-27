module

public import CFSG.Timmesfeld.Transvection.TriangleCoordsG

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.NaturalModule CFSG.Timmesfeld.RankOne

variable {G : Type*} [Group G]

namespace SL2Coords

variable {A E : Subgroup G} {k : ℕ} (φ : SL2Coords A E k)

@[expose] noncomputable def elt (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k)) : G :=
  (φ.toMulEquiv.symm g : G)

theorem elt_mem (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k)) : φ.elt g ∈ A ⊔ E :=
  (φ.toMulEquiv.symm g).2

@[simp] theorem mat_elt (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k)) :
    φ.mat (φ.elt g) = g := by
  have h := φ.toMulEquiv_apply (φ.toMulEquiv.symm g)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem elt_mat {x : G} (hx : x ∈ A ⊔ E) : φ.elt (φ.mat x) = x :=
  φ.mat_injOn (φ.elt_mem _) hx (φ.mat_elt _)

theorem elt_mul (g h : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k)) :
    φ.elt (g * h) = φ.elt g * φ.elt h := by
  simp only [elt, map_mul, Subgroup.coe_mul]

@[simp] theorem elt_one : φ.elt 1 = 1 := by
  simp only [elt, map_one, Subgroup.coe_one]

theorem elt_inv (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k)) :
    φ.elt g⁻¹ = (φ.elt g)⁻¹ := by
  simp only [elt, map_inv, Subgroup.coe_inv]

theorem elt_lowerElt_mem (s : GaloisField 2 k) : φ.elt (lowerElt _ s) ∈ A :=
  (φ.mem_A_iff (φ.elt_mem _)).2 (by rw [mat_elt]; exact (mem_lowerUnipotent_iff _).2 ⟨s, rfl⟩)

theorem elt_upperElt_mem (s : GaloisField 2 k) : φ.elt (upperElt _ s) ∈ E :=
  (φ.mem_E_iff (φ.elt_mem _)).2 (by rw [mat_elt]; exact (mem_upperUnipotent_iff _).2 ⟨s, rfl⟩)

theorem exists_eq_elt_lowerElt {a : G} (ha : a ∈ A) : ∃ s, a = φ.elt (lowerElt _ s) := by
  have haX : a ∈ A ⊔ E := Subgroup.mem_sup_left ha
  obtain ⟨s, hs⟩ := (mem_lowerUnipotent_iff _).1 ((φ.mem_A_iff haX).1 ha)
  exact ⟨s, by rw [← hs, φ.elt_mat haX]⟩

theorem exists_eq_elt_upperElt {e : G} (he : e ∈ E) : ∃ s, e = φ.elt (upperElt _ s) := by
  have heX : e ∈ A ⊔ E := Subgroup.mem_sup_right he
  obtain ⟨s, hs⟩ := (mem_upperUnipotent_iff _).1 ((φ.mem_E_iff heX).1 he)
  exact ⟨s, by rw [← hs, φ.elt_mat heX]⟩

theorem elt_lowerElt_add (s t : GaloisField 2 k) :
    φ.elt (lowerElt _ (s + t)) = φ.elt (lowerElt _ s) * φ.elt (lowerElt _ t) := by
  rw [← lowerElt_mul, elt_mul]

theorem elt_lowerElt_injective : Function.Injective fun s => φ.elt (lowerElt (GaloisField 2 k) s) :=
  fun s t h => by
    have := congrArg φ.mat h
    simp only [mat_elt] at this
    exact lowerElt_injective _ this

theorem weylElt_mul_lowerElt_mul_weylElt (t : GaloisField 2 k) :
    weylElt (GaloisField 2 k) * lowerElt _ t * weylElt _ = upperElt _ t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_weylElt, coe_upperElt, coe_lowerElt]

theorem elt_weylElt_mul_self : φ.elt (weylElt _) * φ.elt (weylElt _) = 1 := by
  rw [← elt_mul, weylElt_mul_self, elt_one]

theorem elt_weylElt_inv : (φ.elt (weylElt _))⁻¹ = φ.elt (weylElt _) :=
  inv_eq_of_mul_eq_one_right φ.elt_weylElt_mul_self

theorem elt_weylElt_conj_lowerElt (s : GaloisField 2 k) :
    φ.elt (weylElt _) * φ.elt (lowerElt _ s) * (φ.elt (weylElt _))⁻¹ = φ.elt (upperElt _ s) := by
  rw [elt_weylElt_inv, ← elt_mul, ← elt_mul, weylElt_mul_lowerElt_mul_weylElt]

theorem elt_weylElt_conj_upperElt (s : GaloisField 2 k) :
    φ.elt (weylElt _) * φ.elt (upperElt _ s) * (φ.elt (weylElt _))⁻¹ = φ.elt (lowerElt _ s) := by
  rw [elt_weylElt_inv, ← elt_mul, ← elt_mul, weylElt_mul_upperElt_mul_weylElt]

theorem conjSub_A_elt_weylElt [Finite G] (hc : Nat.card E = Nat.card A) :
    conjSub A (φ.elt (weylElt _)) = E := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨s, rfl⟩ := φ.exists_eq_elt_lowerElt ha
    show _ * _ * _ ∈ E
    rw [elt_weylElt_conj_lowerElt]
    exact φ.elt_upperElt_mem s
  · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, hc]

theorem conjSub_E_elt_weylElt [Finite G] (hc : Nat.card E = Nat.card A) :
    conjSub E (φ.elt (weylElt _)) = A := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨s, rfl⟩ := φ.exists_eq_elt_upperElt he
    show _ * _ * _ ∈ A
    rw [elt_weylElt_conj_upperElt]
    exact φ.elt_lowerElt_mem s
  · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, hc]

theorem elt_diagElt_conj_lowerElt (c : (GaloisField 2 k)ˣ) (s : GaloisField 2 k) :
    φ.elt (diagElt c) * φ.elt (lowerElt _ s) * (φ.elt (diagElt c))⁻¹ =
      φ.elt (lowerElt _ (((c⁻¹ : (GaloisField 2 k)ˣ) : GaloisField 2 k) ^ 2 * s)) := by
  rw [← elt_inv, ← elt_mul, ← elt_mul, diagElt_mul_lowerElt, mul_assoc, mul_inv_cancel, mul_one]

theorem elt_weylElt_conj_diagElt (c : (GaloisField 2 k)ˣ) :
    φ.elt (weylElt _) * φ.elt (diagElt c) * (φ.elt (weylElt _))⁻¹ = φ.elt (diagElt c⁻¹) := by
  rw [elt_weylElt_inv, ← elt_mul, ← elt_mul, weylElt_mul_diagElt, mul_assoc, weylElt_mul_self,
    mul_one]

theorem map_lowerElt (τ : GaloisField 2 k ≃+* GaloisField 2 k) (s : GaloisField 2 k) :
    Matrix.SpecialLinearGroup.map τ.toRingHom (lowerElt _ s) = lowerElt _ (τ s) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_lowerElt]

theorem map_upperElt (τ : GaloisField 2 k ≃+* GaloisField 2 k) (s : GaloisField 2 k) :
    Matrix.SpecialLinearGroup.map τ.toRingHom (upperElt _ s) = upperElt _ (τ s) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_upperElt]

theorem map_diagElt (τ : GaloisField 2 k ≃+* GaloisField 2 k) (c : (GaloisField 2 k)ˣ) :
    Matrix.SpecialLinearGroup.map τ.toRingHom (diagElt c) =
      diagElt (Units.map τ.toRingHom.toMonoidHom c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_diagElt]

theorem map_symm_map (τ : GaloisField 2 k ≃+* GaloisField 2 k)
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k)) :
    Matrix.SpecialLinearGroup.map τ.symm.toRingHom (Matrix.SpecialLinearGroup.map τ.toRingHom g) =
      g := by
  ext i j
  simp

theorem map_map_symm (τ : GaloisField 2 k ≃+* GaloisField 2 k)
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k)) :
    Matrix.SpecialLinearGroup.map τ.toRingHom (Matrix.SpecialLinearGroup.map τ.symm.toRingHom g) =
      g := by
  ext i j
  simp

theorem map_mem_lowerUnipotent_iff (τ : GaloisField 2 k ≃+* GaloisField 2 k)
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k)) :
    Matrix.SpecialLinearGroup.map τ.toRingHom g ∈ lowerUnipotent (GaloisField 2 k) ↔
      g ∈ lowerUnipotent (GaloisField 2 k) := by
  rw [mem_lowerUnipotent_iff, mem_lowerUnipotent_iff]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨τ.symm s, ?_⟩
    rw [← map_symm_map τ g, hs, map_lowerElt]
  · rintro ⟨s, rfl⟩
    exact ⟨τ s, map_lowerElt τ s⟩

theorem map_mem_upperUnipotent_iff (τ : GaloisField 2 k ≃+* GaloisField 2 k)
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k)) :
    Matrix.SpecialLinearGroup.map τ.toRingHom g ∈ upperUnipotent (GaloisField 2 k) ↔
      g ∈ upperUnipotent (GaloisField 2 k) := by
  rw [mem_upperUnipotent_iff, mem_upperUnipotent_iff]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨τ.symm s, ?_⟩
    rw [← map_symm_map τ g, hs, map_upperElt]
  · rintro ⟨s, rfl⟩
    exact ⟨τ s, map_upperElt τ s⟩

@[expose] noncomputable def map (τ : GaloisField 2 k ≃+* GaloisField 2 k) : SL2Coords A E k where
  card_eq := φ.card_eq
  mat x := Matrix.SpecialLinearGroup.map τ.toRingHom (φ.mat x)
  mat_mul hx hy := by rw [φ.mat_mul hx hy, map_mul]
  mat_surj g := by
    obtain ⟨x, hx, hxg⟩ := φ.mat_surj (Matrix.SpecialLinearGroup.map τ.symm.toRingHom g)
    exact ⟨x, hx, by rw [hxg, map_map_symm]⟩
  mat_inj hx h1 := φ.mat_inj hx (by
    rw [← map_symm_map τ (φ.mat _), h1, map_one])
  mem_A_iff hx := by rw [map_mem_lowerUnipotent_iff]; exact φ.mem_A_iff hx
  mem_E_iff hx := by rw [map_mem_upperUnipotent_iff]; exact φ.mem_E_iff hx

theorem map_mat (τ : GaloisField 2 k ≃+* GaloisField 2 k) (x : G) :
    (φ.map τ).mat x = Matrix.SpecialLinearGroup.map τ.toRingHom (φ.mat x) := rfl

theorem map_elt (τ : GaloisField 2 k ≃+* GaloisField 2 k)
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k)) :
    (φ.map τ).elt g = φ.elt (Matrix.SpecialLinearGroup.map τ.symm.toRingHom g) := by
  refine (φ.map τ).mat_injOn ((φ.map τ).elt_mem g) (φ.elt_mem _) ?_
  rw [mat_elt, map_mat, mat_elt, map_map_symm]

end SL2Coords

end CFSG.Timmesfeld.Transvection
