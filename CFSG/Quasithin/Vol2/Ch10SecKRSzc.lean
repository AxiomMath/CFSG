module

public import CFSG.Quasithin.Vol2.Ch10SecKRSw

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique C10P4F
open scoped Matrix

@[expose] def tw (b : Bool) : SL5 →* SL5 :=
  cond b (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 5 (ZMod 2)).toMonoidHom
    (MonoidHom.id SL5)

theorem tw_false (g : SL5) : tw false g = g := rfl

theorem tw_true (g : SL5) :
    ((tw true g : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      ((g⁻¹ : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ := rfl

variable {G : Type} [Group G]

structure MultiCoord (J W : Subgroup G) (k : ℕ) where
  E : G → Fin k → Fin 5 → ZMod 2
  ρ : ↥J →* SL5
  dual : Fin k → Bool
  le : J ≤ Subgroup.normalizer (W : Set G)
  map_mul : ∀ a ∈ W, ∀ b ∈ W, E (a * b) = E a + E b
  inj : ∀ a ∈ W, ∀ b ∈ W, E a = E b → a = b
  surj : ∀ x, ∃ a ∈ W, E a = x
  conj : ∀ (j : ↥J), ∀ a ∈ W, ∀ i, E ((j : G) * a * (j : G)⁻¹) i =
    (tw (dual i) (ρ j) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ E a i
  ρ_surj : Function.Surjective ρ

namespace MultiCoord

variable {J W : Subgroup G} {k : ℕ} (C : MultiCoord J W k)

include C in
theorem conj_mem (j : ↥J) {a : G} (ha : a ∈ W) : (j : G) * a * (j : G)⁻¹ ∈ W :=
  (Subgroup.mem_normalizer_iff.1 (C.le j.2) a).1 ha

theorem E_one : C.E 1 = 0 := by
  have h := C.map_mul 1 W.one_mem 1 W.one_mem
  rw [mul_one] at h
  have h2 : C.E 1 + C.E 1 = C.E 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

theorem eq_one_of_E {a : G} (ha : a ∈ W) (h : C.E a = 0) : a = 1 :=
  C.inj a ha 1 W.one_mem (by rw [h, C.E_one])

theorem E_inv {a : G} (ha : a ∈ W) : C.E a⁻¹ = C.E a := by
  have h := C.map_mul a ha a⁻¹ (W.inv_mem ha)
  rw [mul_inv_cancel, C.E_one] at h
  have : ∀ x : Fin k → Fin 5 → ZMod 2, 0 = x + C.E a⁻¹ → C.E a⁻¹ = x := fun x hx => by
    have h2 : x + x = 0 := by
      funext i b
      exact zmod2_add_self _
    calc C.E a⁻¹ = (x + x) + C.E a⁻¹ := by rw [h2, zero_add]
      _ = x := by rw [add_assoc, ← hx, add_zero]
  exact this _ h

theorem mem_centralizer_of_rho {j : ↥J} (hj : C.ρ j = 1) :
    (j : G) ∈ Subgroup.centralizer (W : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hja : (j : G) * a * (j : G)⁻¹ ∈ W := C.conj_mem j ha
  have h1 : C.E ((j : G) * a * (j : G)⁻¹) = C.E a := by
    funext i
    rw [C.conj j a ha i, hj, map_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have h2 := C.inj _ hja a ha h1
  calc a * (j : G) = (j : G) * a * (j : G)⁻¹ * (j : G) := by rw [h2]
    _ = (j : G) * a := by group

theorem ker_two [Finite G] (hCJ : J ⊓ Subgroup.centralizer (W : Set G) = pCoreOf 2 J) {j : ↥J}
    (hj : C.ρ j = 1) : ∃ m : ℕ, (j : G) ^ 2 ^ m = 1 :=
  exists_two_pow_of_mem_pCoreOf (L := J) (hCJ ▸
    (⟨j.2, C.mem_centralizer_of_rho hj⟩ : (j : G) ∈ J ⊓ Subgroup.centralizer (W : Set G)))

@[expose] noncomputable def conjBy (A : SL5) : MultiCoord J W k where
  E g i := (tw (C.dual i) A : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ C.E g i
  ρ := (MulAut.conj A).toMonoidHom.comp C.ρ
  dual := C.dual
  le := C.le
  map_mul a ha b hb := by
    funext i
    rw [C.map_mul a ha b hb, Pi.add_apply, Matrix.mulVec_add, Pi.add_apply]
  inj a ha b hb h := C.inj a ha b hb (by
    funext i
    have h1 := congrArg (fun x : Fin k → Fin 5 → ZMod 2 =>
      (tw (C.dual i) A⁻¹ : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x i) h
    simpa only [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, ← _root_.map_mul,
      inv_mul_cancel, map_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] using h1)
  surj x := by
    obtain ⟨a, ha, hax⟩ := C.surj fun i =>
      (tw (C.dual i) A⁻¹ : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x i
    refine ⟨a, ha, ?_⟩
    funext i
    rw [hax, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, ← _root_.map_mul,
      mul_inv_cancel, map_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  conj l a ha i := by
    show (tw (C.dual i) A : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ C.E ((l : G) * a * (l : G)⁻¹) i =
      (tw (C.dual i) (A * C.ρ l * A⁻¹) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ
        ((tw (C.dual i) A : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ C.E a i)
    rw [C.conj l a ha i, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, ← _root_.map_mul,
      ← _root_.map_mul, show A * C.ρ l * A⁻¹ * A = A * C.ρ l by group]
  ρ_surj := (MulAut.conj A).surjective.comp C.ρ_surj

theorem conjBy_ρ (A : SL5) (j : ↥J) : (C.conjBy A).ρ j = A * C.ρ j * A⁻¹ := by
  change ((MulAut.conj A).toMonoidHom.comp C.ρ) j = _
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem conjBy_dual (A : SL5) : (C.conjBy A).dual = C.dual := rfl

end MultiCoord

variable [Finite G] {T L I J : Subgroup G} {t w : G}

theorem Conf.exists_multiCoord_normalized (c : Conf T L I t w J)
    (hCJ : J ⊓ Subgroup.centralizer (VI T L I J w : Set G) = pCoreOf 2 J) {k : ℕ}
    (C : MultiCoord J (VI T L I J w) k) :
    ∃ C' : MultiCoord J (VI T L I J w) k, C'.dual = C.dual ∧ ∀ j : ↥J,
      C'.ρ j ∈ uniSL 5 ↔ (j : G) ∈ T ⊓ Subgroup.centralizer ({w} : Set G) := by
  obtain ⟨A, hA⟩ := exists_conj_iff C.ρ C.ρ_surj (Conf.isSylowTwoOf_inf_J c) fun j hj =>
    Conf.pCoreOf_J_le c (hCJ ▸ (⟨j.2, C.mem_centralizer_of_rho hj⟩ :
      (j : G) ∈ J ⊓ Subgroup.centralizer (VI T L I J w : Set G)))
  refine ⟨C.conjBy A, C.conjBy_dual A, fun j => ?_⟩
  rw [C.conjBy_ρ, hA j]
  exact ⟨fun h => h.1, fun h => ⟨h, j.2⟩⟩

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
