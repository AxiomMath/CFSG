module

public import CFSG.Timmesfeld.RankTwo.LevisExtras

public noncomputable section

namespace CFSG.Timmesfeld.LieEmbed

open CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Universal
open CFSG.LieType.RootSystem
open scoped commutatorElement

section Torus

variable {F : Type} [Field F] {G : Type*} [Group G]

@[expose] def wEl (u v : F → G) (t : F) : G := u t * v (-t⁻¹) * u t

@[expose] def hEl (u v : F → G) (t : F) : G := wEl u v t * wEl u v (-1)

theorem map_hEl {H : Type*} [Group H] (φ : G →* H) (u v : F → G) (t : F) :
    φ (hEl u v t) = hEl (fun c => φ (u c)) (fun c => φ (v c)) t := by
  simp only [hEl, wEl, map_mul]

theorem cm_hEl01 {t : F} (ht : t ≠ 0) : Matrix.SpecialLinearGroup.coeMonoidHom
    (hEl (tv 0 1) (tv 1 0) t : Matrix.SpecialLinearGroup (Fin 3) F) =
      !![t, 0, 0; 0, t⁻¹, 0; 0, 0, 1] := by
  simp only [hEl, wEl, map_mul, LevisExtras.cm_tv01, LevisExtras.cm_tv10, Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [ht]

theorem cm_hEl12 {t : F} (ht : t ≠ 0) : Matrix.SpecialLinearGroup.coeMonoidHom
    (hEl (tv 1 2) (tv 2 1) t : Matrix.SpecialLinearGroup (Fin 3) F) =
      !![1, 0, 0; 0, t, 0; 0, 0, t⁻¹] := by
  simp only [hEl, wEl, map_mul, LevisExtras.cm_tv12, LevisExtras.cm_tv21, Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [ht]

theorem exists_eq_hEl_of_mem_center {g : Matrix.SpecialLinearGroup (Fin 3) F}
    (hg : g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) :
    ∃ ω : F, ω ≠ 0 ∧ ω ^ 3 = 1 ∧ g = hEl (tv 0 1) (tv 1 0) ω * hEl (tv 1 2) (tv 2 1) (ω ^ 2) ∧
      (ω = 1 → g = 1) := by
  obtain ⟨ω, hω, hg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hg
  rw [Fintype.card_fin] at hω
  have hω0 : ω ≠ 0 := fun h => by simp [h] at hω
  refine ⟨ω, hω0, hω, ?_, fun h1 => ?_⟩
  · apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
    rw [map_mul, cm_hEl01 hω0, cm_hEl12 (pow_ne_zero 2 hω0), Matrix.mul_fin_three,
      Matrix.SpecialLinearGroup.coeMonoidHom_apply, ← hg]
    have e1 : ω⁻¹ * ω ^ 2 = ω := by field_simp
    have e2 : (ω ^ 2)⁻¹ = ω := inv_eq_of_mul_eq_one_left (by rw [← pow_succ', hω])
    ext a b
    fin_cases a <;> fin_cases b <;> simp [e1, e2]
  · apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
    rw [Matrix.SpecialLinearGroup.coeMonoidHom_apply, ← hg, h1, map_one, map_one]

end Torus

section Action

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F] [CharP F 2]
  {x : (Fin D.rank → ℤ) → F → K} {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}

omit [CharP F 2] in
theorem wEl_eq_weylElement (i : Fin D.rank) (T : Fˣ) :
    wEl (x (Pi.single i 1)) (x (-Pi.single i 1)) (T : F) = weylElement x i T := by
  rw [wEl, weylElement, Units.val_inv_eq_inv_val]

theorem intCast_eq_one_of_sign {ε : ℤ} (h : ε = 1 ∨ ε = -1) : (ε : F) = 1 := by
  rcases h with rfl | rfl
  · simp
  · simp [CharTwo.neg_eq]

theorem neg_one_units_eq_one : (-1 : Fˣ) = 1 :=
  Units.ext (by simp [CharTwo.neg_eq])

theorem hEl_conj (hE : ChevalleyExtras D F x C O) (i : Fin D.rank) {β : Fin D.rank → ℤ}
    (hβ : β ∈ D.roots) (T : Fˣ) (u : F) :
    hEl (x (Pi.single i 1)) (x (-Pi.single i 1)) (T : F) * x β u *
        (hEl (x (Pi.single i 1)) (x (-Pi.single i 1)) (T : F))⁻¹ =
      x β (((T ^ (∑ j, D.cartan i j * β j) : Fˣ) : F) * u) := by
  have hii := D.isFiniteType.apply_self i
  have hs : reflection D.cartan i β ∈ D.roots := LevisExtras.reflection_mem_roots i hβ
  obtain ⟨ε, hε, h1⟩ := hE.weyl i β hβ
  obtain ⟨ε', hε', h2⟩ := hE.weyl i _ hs
  have hss : reflection D.cartan i (reflection D.cartan i β) = β := by
    rw [← Module.End.mul_apply, reflection_mul_self hii, Module.End.one_apply]
  have hm : ∑ j, D.cartan i j * reflection D.cartan i β j = -∑ j, D.cartan i j * β j := by
    have := coroot_reflection hii β
    rwa [coroot_apply, coroot_apply] at this
  have hw1 : wEl (x (Pi.single i 1)) (x (-Pi.single i 1)) (-1 : F) =
      weylElement x i (-1 : Fˣ) := by
    rw [← wEl_eq_weylElement, Units.val_neg, Units.val_one]
  rw [hEl, hw1, wEl_eq_weylElement, _root_.mul_inv_rev,
    show ∀ a b c d : K, a * b * c * (d * a⁻¹) = a * (b * c * d) * a⁻¹ from fun _ _ _ _ => by
      group,
    h1, neg_one_units_eq_one, one_zpow, Units.val_one, mul_one, intCast_eq_one_of_sign hε,
    one_mul, h2, hss, hm, neg_neg, intCast_eq_one_of_sign hε', one_mul]

theorem hEl_conj' (hE : ChevalleyExtras D F x C O) (i : Fin D.rank) {β : Fin D.rank → ℤ}
    (hβ : β ∈ D.roots) {t : F} (ht : t ≠ 0) (u : F) :
    hEl (x (Pi.single i 1)) (x (-Pi.single i 1)) t * x β u *
        (hEl (x (Pi.single i 1)) (x (-Pi.single i 1)) t)⁻¹ =
      x β (((Units.mk0 t ht ^ (∑ j, D.cartan i j * β j) : Fˣ) : F) * u) := by
  have h := hEl_conj hE i hβ (Units.mk0 t ht) u
  rwa [Units.val_mk0] at h

end Action

section F4

variable (K : Type) [Field K]

open Adjoint in
theorem exists_f4_chevalleyExtras :
    ∃ (O : CommOrder (Steinberg.RootSystem.ofCartan (f4Datum K).isFiniteType
        (f4Datum K).divisible)) (C : (Fin (Tag.rank .F4) → ℤ) → (Fin (Tag.rank .F4) → ℤ) →
          ℕ × ℕ → ℤ),
      ChevalleyExtras (f4Datum K) K (f4Par K) C O ∧
        ∀ α ∈ (f4Datum K).roots, ∀ β ∈ (f4Datum K).roots, α + β ∈ (f4Datum K).roots →
          β - α ∉ (f4Datum K).roots → (C α β (1, 1)).natAbs = 1 := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (f4Datum K).isFiniteType
    (Dv := (f4Datum K).divisible) rfl
  refine ⟨O, _, f4_chevalleyExtras K O _
    (commutatorFormula_commC f4Data_valid noG2_F4 _ (adjDatum_roots _ K) O), ?_⟩
  intro α hα β hβ hr hd
  rw [mem_adjDatum_roots] at hα hβ hr hd
  have hne : α + β ≠ 0 := hr.ne_zero
  rw [commC_11 hα hβ hne, RootOperatorFamily'.coeff11,
    RootOperatorFamily'.bracketCoeff_natAbs _ _ (fun h => hne (by
      change β = -α at h
      rw [h, add_neg_cancel])) hr]
  exact stringNorm_of_not_isRoot hd

variable {K} [Finite K] [CharP K 2]

@[expose] def f4n (k : Fin 4) : Fin (Tag.rank .F4) := k

theorem exists_sl3ToF4 : ∃ l : Matrix.SpecialLinearGroup (Fin 3) K →* ↥(adjointGroup .F4 K),
    Function.Injective l ∧ ∀ c,
      l (tv 0 1 c) = Adjoint.f4Par K (sroot (f4n 0)) c ∧
      l (tv 1 0 c) = Adjoint.f4Par K (-sroot (f4n 0)) c ∧
      l (tv 1 2 c) = Adjoint.f4Par K (sroot (f4n 1)) c ∧
      l (tv 2 1 c) = Adjoint.f4Par K (-sroot (f4n 1)) c ∧
      l (tv 0 2 c) = Adjoint.f4Par K (sroot (f4n 0) + sroot (f4n 1)) c ∧
      l (tv 2 0 c) = Adjoint.f4Par K (-(sroot (f4n 0) + sroot (f4n 1))) c := by
  obtain ⟨O, C, hE, hC⟩ := exists_f4_chevalleyExtras K
  obtain ⟨l, hl⟩ := LevisExtras.exists_sl3 hE hC rfl (i := f4n 0) (j := f4n 1)
    (Fin.ne_of_val_ne (by decide))
    (by show Tag.cartan .F4 (f4n 0) (f4n 1) = -1; decide)
    (by show Tag.cartan .F4 (f4n 1) (f4n 0) = -1; decide)
  refine ⟨l, ?_, hl⟩
  have hinj2 : Function.Injective (Adjoint.f4Par K (sroot (f4n 2))) :=
    (hE.param _ (LevisExtras.single_mem_roots (f4n 2))).2.2
  rw [injective_iff_map_eq_one]
  intro g hg
  have hnt : ∃ g, l g ≠ 1 := ⟨tv 0 1 1, by
    rw [(hl 1).1]
    intro h
    have h0 := LevisExtras.x_zero hE (LevisExtras.single_mem_roots (f4n 0))
    exact one_ne_zero ((hE.param _ (LevisExtras.single_mem_roots (f4n 0))).2.2 (h.trans h0.symm))⟩
  have hker : g ∈ Subgroup.center _ := CurtisTits.ker_le_center_of_isQuasisimple
    (SpecialLinear.isQuasisimple 2 K le_rfl) hnt hg
  obtain ⟨ω, hω0, hω3, rfl, h1⟩ := exists_eq_hEl_of_mem_center hker
  apply h1
  have e01 : (fun c => l (tv 0 1 c)) = Adjoint.f4Par K (sroot (f4n 0)) := funext fun c => (hl c).1
  have e10 : (fun c => l (tv 1 0 c)) = Adjoint.f4Par K (-sroot (f4n 0)) :=
    funext fun c => (hl c).2.1
  have e12 : (fun c => l (tv 1 2 c)) = Adjoint.f4Par K (sroot (f4n 1)) :=
    funext fun c => (hl c).2.2.1
  have e21 : (fun c => l (tv 2 1 c)) = Adjoint.f4Par K (-sroot (f4n 1)) :=
    funext fun c => (hl c).2.2.2.1
  rw [map_mul, map_hEl, map_hEl, e01, e10, e12, e21] at hg
  have hconj := congrArg (fun z => z * Adjoint.f4Par K (sroot (f4n 2)) 1 * z⁻¹) hg
  simp only [one_mul, inv_one, mul_one] at hconj
  have hω0' : ω ^ 2 ≠ 0 := pow_ne_zero 2 hω0
  rw [_root_.mul_inv_rev, show ∀ a b c d : ↥(adjointGroup .F4 K), a * b * c * (d * a⁻¹) =
      a * (b * c * d) * a⁻¹ from fun _ _ _ _ => by group,
    hEl_conj' hE (f4n 1) (LevisExtras.single_mem_roots (f4n 2)) hω0',
    hEl_conj' hE (f4n 0) (LevisExtras.single_mem_roots (f4n 2)) hω0] at hconj
  have e0 : (∑ j, (Adjoint.f4Datum K).cartan (f4n 0) j * sroot (f4n 2) j) = 0 := by
    show (∑ j, Tag.cartan .F4 (f4n 0) j * sroot (f4n 2) j) = 0
    decide
  have e1 : (∑ j, (Adjoint.f4Datum K).cartan (f4n 1) j * sroot (f4n 2) j) = -1 := by
    show (∑ j, Tag.cartan .F4 (f4n 1) j * sroot (f4n 2) j) = -1
    decide
  rw [e0, e1, zpow_zero, Units.val_one, one_mul, zpow_neg_one, Units.val_inv_eq_inv_val,
    Units.val_mk0, mul_one] at hconj
  have h2 : (ω ^ 2)⁻¹ = 1 := hinj2 hconj
  have h2' : ω ^ 2 = 1 := inv_eq_one.1 h2
  rw [← hω3, pow_succ, h2', one_mul]

omit [Finite K] in
theorem exists_sl2sl2ToF4 {j : Fin (Tag.rank .F4)} (hj : j = f4n 2 ∨ j = f4n 3) :
    ∃ m : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →*
        ↥(adjointGroup .F4 K), Function.Injective m ∧ ∀ c,
        m (tv 0 1 c, 1) = Adjoint.f4Par K (sroot (f4n 0)) c ∧
        m (tv 1 0 c, 1) = Adjoint.f4Par K (-sroot (f4n 0)) c ∧
        m (1, tv 0 1 c) = Adjoint.f4Par K (sroot j) c ∧
        m (1, tv 1 0 c) = Adjoint.f4Par K (-sroot j) c := by
  obtain ⟨O, C, hE, hC⟩ := exists_f4_chevalleyExtras K
  obtain ⟨φ, hφ, hupφ, hlowφ⟩ := hE.rankOne (f4n 0)
  obtain ⟨ψ, hψ, hupψ, hlowψ⟩ := hE.rankOne j
  have hj0 : f4n 0 ≠ j := by rcases hj with rfl | rfl <;> decide
  have hc0 : (Adjoint.f4Datum K).cartan (f4n 0) j = 0 := by
    show Tag.cartan .F4 (f4n 0) j = 0
    rcases hj with rfl | rfl <;> decide
  have hc1 : (Adjoint.f4Datum K).cartan j (f4n 0) = 0 := by
    show Tag.cartan .F4 j (f4n 0) = 0
    rcases hj with rfl | rfl <;> decide
  have hcomm := LevisExtras.commute_of_cartan_eq_zero hE hC rfl hj0 hc0 hc1
  have hc : ∀ a b, Commute (φ a) (ψ b) := commute_of_tv φ ψ fun c d => by
    rw [LevisExtras.tv01_eq_sl2Upper, LevisExtras.tv10_eq_sl2Lower,
      LevisExtras.tv01_eq_sl2Upper, LevisExtras.tv10_eq_sl2Lower, hupφ, hlowφ, hupψ, hlowψ]
    exact hcomm c d
  refine ⟨φ.noncommCoprod ψ hc, LevisExtras.injective_noncommCoprod hφ hψ hc,
    fun c => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [MonoidHom.noncommCoprod_apply, map_one, mul_one, LevisExtras.tv01_eq_sl2Upper, hupφ]
  · rw [MonoidHom.noncommCoprod_apply, map_one, mul_one, LevisExtras.tv10_eq_sl2Lower, hlowφ]
  · rw [MonoidHom.noncommCoprod_apply, map_one, one_mul, LevisExtras.tv01_eq_sl2Upper, hupψ]
  · rw [MonoidHom.noncommCoprod_apply, map_one, one_mul, LevisExtras.tv10_eq_sl2Lower, hlowψ]

end F4

end CFSG.Timmesfeld.LieEmbed
