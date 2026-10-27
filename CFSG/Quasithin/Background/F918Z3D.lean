module

public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.Background.F918Z0Def
public import CFSG.Quasithin.Background.D2Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin

open scoped Matrix

namespace Z3D

@[expose] def colHom (d r : ℕ) (F : Type) [Field F] (j : Fin r) :
    Multiplicative (Matrix (Fin d) (Fin r) F) →* Multiplicative (Fin d → F) where
  toFun M := Multiplicative.ofAdd fun i => Multiplicative.toAdd M i j
  map_one' := rfl
  map_mul' _ _ := rfl

theorem colHom_mul (d r : ℕ) (F : Type) [Field F] (j : Fin r) (A : Matrix (Fin d) (Fin d) F)
    (M : Matrix (Fin d) (Fin r) F) :
    colHom d r F j (Multiplicative.ofAdd (A * M)) =
      Multiplicative.ofAdd (A *ᵥ Multiplicative.toAdd (colHom d r F j (Multiplicative.ofAdd M))) :=
  rfl

theorem exists_card_eq_pow_of_ringHom {K F : Type} [Field K] [Field F] [Finite F] (f : K →+* F) :
    ∃ k : ℕ, Nat.card F = Nat.card K ^ k := by
  let _ : Algebra K F := f.toAlgebra
  exact ⟨Module.finrank K F, Module.natCard_eq_pow_finrank⟩

theorem dvd_of_ringHom {K F : Type} [Field K] [Field F] [Finite F] (f : K →+* F) {a e : ℕ}
    (hK : Nat.card K = 2 ^ a) (hF : Nat.card F = 2 ^ e) : a ∣ e := by
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_ringHom f
  rw [hF, hK, ← pow_mul] at hk
  exact ⟨k, Nat.pow_right_injective (le_refl 2) hk⟩

section Dictionary

variable {V : Type} [CommGroup V] {D X : Subgroup (MulAut V)} {F : Type} [Field F] {d r : ℕ}
  {β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F)}
  {ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F}
  {σ : ↥X →* Matrix.GeneralLinearGroup (Fin r) F}

@[expose] def colProj (β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F)) (I : Subgroup V)
    (j : Fin r) : ↥I →* Multiplicative (Fin d → F) :=
  (colHom d r F j).comp (β.toMonoidHom.comp I.subtype)

theorem colProj_smul (hM : IsMatModel D X β ρ σ) {I : Subgroup V} (j : Fin r) (y : ↥D) (u : ↥I)
    (hu : (y : MulAut V) (u : V) ∈ I) :
    colProj β I j ⟨(y : MulAut V) (u : V), hu⟩ =
      Multiplicative.ofAdd
        ((ρ y : Matrix (Fin d) (Fin d) F) *ᵥ Multiplicative.toAdd (colProj β I j u)) := by
  have h := hM.hρ y (u : V)
  change colHom d r F j (β ((y : MulAut V) (u : V))) = _
  rw [h]
  exact colHom_mul d r F j _ _

theorem exists_entry_ne_zero {I : Subgroup V} (hI0 : I ≠ ⊥) :
    ∃ v₀ ∈ I, ∃ (i : Fin d) (j : Fin r), Multiplicative.toAdd (β v₀) i j ≠ 0 := by
  obtain ⟨v₀, hv₀, hv₀1⟩ : ∃ v₀ ∈ I, v₀ ≠ 1 := by
    by_contra h
    exact hI0 ((Subgroup.eq_bot_iff_forall I).2 fun v hv => by_contra fun hv1 => h ⟨v, hv, hv1⟩)
  refine ⟨v₀, hv₀, ?_⟩
  by_contra h
  have h' : ∀ (i : Fin d) (j : Fin r), Multiplicative.toAdd (β v₀) i j = 0 := fun i j =>
    by_contra fun hne => h ⟨i, j, hne⟩
  refine hv₀1 (β.injective ?_)
  apply Multiplicative.toAdd.injective
  ext i j
  rw [map_one]
  exact h' i j

theorem exists_equiv_column (hM : IsMatModel D X β ρ σ) {I : Subgroup V} (hI0 : I ≠ ⊥)
    (hIinv : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I)
    (hImin : ∀ U ≤ I, (∀ y ∈ D, ∀ v ∈ U, y v ∈ U) → U = ⊥ ∨ U = I) :
    ∃ e : ↥I ≃* Multiplicative (Fin d → F), ∀ (y : ↥D) (v : ↥I)
      (hv : (y : MulAut V) (v : V) ∈ I), e ⟨(y : MulAut V) (v : V), hv⟩ =
        Multiplicative.ofAdd
          ((ρ y : Matrix (Fin d) (Fin d) F) *ᵥ Multiplicative.toAdd (e v)) := by
  obtain ⟨v₀, hv₀, i₀, j₀, hij⟩ := exists_entry_ne_zero (β := β) hI0
  set π := colProj β I j₀ with hπ
  have hπv₀ : Multiplicative.toAdd (π ⟨v₀, hv₀⟩) i₀ ≠ 0 := hij
  have hequi : ∀ (y : ↥D) (v : ↥I) (hv : (y : MulAut V) (v : V) ∈ I),
      π ⟨(y : MulAut V) (v : V), hv⟩ =
        Multiplicative.ofAdd
          ((ρ y : Matrix (Fin d) (Fin d) F) *ᵥ Multiplicative.toAdd (π v)) :=
    fun y v hv => colProj_smul hM j₀ y v hv
  have hinj : Function.Injective π := by
    let U : Subgroup V := π.ker.map I.subtype
    have hUle : U ≤ I := Subgroup.map_subtype_le _
    have hUinv : ∀ y ∈ D, ∀ v ∈ U, y v ∈ U := by
      rintro y hy _ ⟨u, hu, rfl⟩
      have hyu : y (u : V) ∈ I := hIinv y hy u u.2
      have hu' : π u = 1 := hu
      refine ⟨⟨y (u : V), hyu⟩, ?_, rfl⟩
      show π ⟨y (u : V), hyu⟩ = 1
      rw [hequi ⟨y, hy⟩ u hyu, hu']
      simp
    rcases hImin U hUle hUinv with h | h
    · rw [injective_iff_map_eq_one]
      intro u hu
      have : (u : V) ∈ U := ⟨u, hu, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact Subtype.ext this
    · exfalso
      have hv₀U : v₀ ∈ U := by rw [h]; exact hv₀
      obtain ⟨u, hu, hu'⟩ := hv₀U
      have hu0 : u = ⟨v₀, hv₀⟩ := Subtype.ext hu'
      have hu1 : π u = 1 := hu
      rw [hu0] at hu1
      apply hπv₀
      rw [hu1]
      rfl
  have hsurj : Function.Surjective π := by
    let W : AddSubgroup (Fin d → F) :=
      { carrier := {w | ∃ u : ↥I, Multiplicative.toAdd (π u) = w}
        zero_mem' := ⟨1, by simp⟩
        add_mem' := by
          rintro _ _ ⟨u, rfl⟩ ⟨u', rfl⟩
          exact ⟨u * u', by simp⟩
        neg_mem' := by
          rintro _ ⟨u, rfl⟩
          exact ⟨u⁻¹, by simp⟩ }
    have hWinv : ∀ g : ↥D, ∀ w ∈ W, (ρ g : Matrix (Fin d) (Fin d) F) *ᵥ w ∈ W := by
      rintro g _ ⟨u, rfl⟩
      have hyu : (g : MulAut V) (u : V) ∈ I := hIinv g g.2 u u.2
      refine ⟨⟨(g : MulAut V) (u : V), hyu⟩, ?_⟩
      rw [hequi g u hyu]
      rfl
    rcases hM.I_irr W hWinv with h | h
    · exfalso
      have hmem : Multiplicative.toAdd (π ⟨v₀, hv₀⟩) ∈ W := ⟨_, rfl⟩
      rw [h, AddSubgroup.mem_bot] at hmem
      exact hπv₀ (by rw [hmem]; rfl)
    · intro m
      have hmem : Multiplicative.toAdd m ∈ W := by rw [h]; exact AddSubgroup.mem_top _
      obtain ⟨u, hu⟩ := hmem
      exact ⟨u, Multiplicative.toAdd.injective hu⟩
  exact ⟨MulEquiv.ofBijective π ⟨hinj, hsurj⟩, fun y v hv => hequi y v hv⟩

theorem card_eq_pow_of_equiv {I : Subgroup V} (e : ↥I ≃* Multiplicative (Fin d → F)) :
    Nat.card ↥I = Nat.card F ^ d := by
  rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_pi]
  simp

theorem card_eq_pow (hM : IsMatModel D X β ρ σ) {I : Subgroup V} (hI0 : I ≠ ⊥)
    (hIinv : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I)
    (hImin : ∀ U ≤ I, (∀ y ∈ D, ∀ v ∈ U, y v ∈ U) → U = ⊥ ∨ U = I) :
    Nat.card ↥I = Nat.card F ^ d := by
  obtain ⟨e, -⟩ := exists_equiv_column hM hI0 hIinv hImin
  exact card_eq_pow_of_equiv e

theorem mem_fixV_zpowers_iff (g : MulAut V) (v : V) :
    v ∈ fixV (Subgroup.zpowers g) ↔ g v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem card_inf_fixV_zpowers_of_equiv {I : Subgroup V} (hIinv : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I)
    (e : ↥I ≃* Multiplicative (Fin d → F))
    (he : ∀ (y : ↥D) (v : ↥I) (hv : (y : MulAut V) (v : V) ∈ I),
      e ⟨(y : MulAut V) (v : V), hv⟩ = Multiplicative.ofAdd
        ((ρ y : Matrix (Fin d) (Fin d) F) *ᵥ Multiplicative.toAdd (e v)))
    (j : ↥D) :
    Nat.card ↥(I ⊓ fixV (Subgroup.zpowers (j : MulAut V))) =
      Nat.card {w : Fin d → F // (ρ j : Matrix (Fin d) (Fin d) F) *ᵥ w = w} := by
  refine Nat.card_congr
    { toFun := fun x => ⟨Multiplicative.toAdd (e ⟨x.1, x.2.1⟩), ?_⟩
      invFun := fun w => ⟨((e.symm (Multiplicative.ofAdd w.1) : ↥I) : V), (e.symm _).2, ?_⟩
      left_inv := fun x => ?_
      right_inv := fun w => ?_ }
  · have hx := (mem_fixV_zpowers_iff _ _).1 x.2.2
    have hv : (j : MulAut V) x.1 ∈ I := hIinv j j.2 x.1 x.2.1
    have h1 := he j ⟨x.1, x.2.1⟩ hv
    have h2 : (⟨(j : MulAut V) x.1, hv⟩ : ↥I) = ⟨x.1, x.2.1⟩ := Subtype.ext hx
    rw [h2] at h1
    exact (congrArg Multiplicative.toAdd h1).symm
  · refine (mem_fixV_zpowers_iff _ _).2 ?_
    set u := e.symm (Multiplicative.ofAdd w.1) with hu
    have hv : (j : MulAut V) (u : V) ∈ I := hIinv j j.2 u u.2
    have h1 := he j u hv
    have hu' : e u = Multiplicative.ofAdd w.1 := by rw [hu]; simp
    rw [hu', toAdd_ofAdd, w.2] at h1
    exact congrArg Subtype.val (e.injective (h1.trans hu'.symm))
  · apply Subtype.ext
    simp
  · apply Subtype.ext
    simp

theorem card_inf_fixV_zpowers (hM : IsMatModel D X β ρ σ) {I : Subgroup V} (hI0 : I ≠ ⊥)
    (hIinv : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I)
    (hImin : ∀ U ≤ I, (∀ y ∈ D, ∀ v ∈ U, y v ∈ U) → U = ⊥ ∨ U = I) (j : ↥D) :
    Nat.card ↥(I ⊓ fixV (Subgroup.zpowers (j : MulAut V))) =
      Nat.card {w : Fin d → F // (ρ j : Matrix (Fin d) (Fin d) F) *ᵥ w = w} := by
  obtain ⟨e, he⟩ := exists_equiv_column hM hI0 hIinv hImin
  exact card_inf_fixV_zpowers_of_equiv hIinv e he j

theorem card_inf_fixV_zpowers_of_mem (hM : IsMatModel D X β ρ σ) {I : Subgroup V} (hI0 : I ≠ ⊥)
    (hIinv : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I)
    (hImin : ∀ U ≤ I, (∀ y ∈ D, ∀ v ∈ U, y v ∈ U) → U = ⊥ ∨ U = I) {j : MulAut V} (hj : j ∈ D) :
    Nat.card ↥(I ⊓ fixV (Subgroup.zpowers j)) =
      Nat.card {w : Fin d → F // (ρ ⟨j, hj⟩ : Matrix (Fin d) (Fin d) F) *ᵥ w = w} :=
  card_inf_fixV_zpowers hM hI0 hIinv hImin ⟨j, hj⟩

theorem exists_ringHom_of_commuting_scalars (hM : IsMatModel D X β ρ σ) (hd : 0 < d) {K : Type}
    [Field K] {M : Type} [AddCommGroup M] [Module K M] (E : M ≃+ (Fin d → F))
    (hcomm : ∀ (g : ↥D) (c : K) (x : M),
      E.symm ((ρ g : Matrix (Fin d) (Fin d) F) *ᵥ E (c • x)) =
        c • E.symm ((ρ g : Matrix (Fin d) (Fin d) F) *ᵥ E x)) :
    ∃ f : K →+* F, ∀ (c : K) (x : M), E (c • x) = f c • E x := by
  let T : K → (Fin d → F) →+ (Fin d → F) := fun c =>
    E.toAddMonoidHom.comp ((DistribSMul.toAddMonoidHom M c).comp E.symm.toAddMonoidHom)
  have hT : ∀ c w, T c w = E (c • E.symm w) := fun c w => rfl
  have hTcomm : ∀ (c : K) (g : ↥D) (w : Fin d → F),
      T c ((ρ g : Matrix (Fin d) (Fin d) F) *ᵥ w) = (ρ g : Matrix (Fin d) (Fin d) F) *ᵥ T c w := by
    intro c g w
    have h := hcomm g c (E.symm w)
    rw [AddEquiv.apply_symm_apply] at h
    rw [hT, hT, ← h, AddEquiv.apply_symm_apply]
  choose f hf using fun c => hM.comm_F (T c) (hTcomm c)
  let w₀ : Fin d → F := Pi.single ⟨0, hd⟩ 1
  have hscal : ∀ a b : F, a • w₀ = b • w₀ → a = b := fun a b h => by
    simpa [w₀] using congrFun h ⟨0, hd⟩
  have hT1 : ∀ w, T 1 w = w := fun w => by rw [hT, one_smul, AddEquiv.apply_symm_apply]
  have hT0 : ∀ w, T 0 w = 0 := fun w => by rw [hT, zero_smul, map_zero]
  have hTadd : ∀ a b w, T (a + b) w = T a w + T b w := fun a b w => by
    simp only [hT, add_smul, map_add]
  have hTmul : ∀ a b w, T (a * b) w = T a (T b w) := fun a b w => by
    simp only [hT, mul_smul, AddEquiv.symm_apply_apply]
  refine ⟨{ toFun := f
            map_one' := hscal _ _ (by rw [← hf 1 w₀, hT1, one_smul])
            map_mul' := fun a b => hscal _ _ (by
              rw [← hf (a * b) w₀, hTmul, hf b w₀, hf a, smul_smul])
            map_zero' := hscal _ _ (by rw [← hf 0 w₀, hT0, zero_smul])
            map_add' := fun a b => hscal _ _ (by
              rw [← hf (a + b) w₀, hTadd, hf a w₀, hf b w₀, add_smul]) }, fun c x => ?_⟩
  have h := hf c (E x)
  rw [hT, AddEquiv.symm_apply_apply] at h
  exact h

theorem le_stabSub_of_invariant {I : Subgroup V} (hIinv : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I) :
    D ≤ stabSub I := by
  intro a ha u
  refine ⟨fun hu => ?_, hIinv a ha u⟩
  have := hIinv a⁻¹ (D.inv_mem ha) _ hu
  simpa using this

theorem exists_ringHom_of_smul_comm (hM : IsMatModel D X β ρ σ) {I : Subgroup V} (hI0 : I ≠ ⊥)
    (hIinv : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I)
    (hImin : ∀ U ≤ I, (∀ y ∈ D, ∀ v ∈ U, y v ∈ U) → U = ⊥ ∨ U = I) {K : Type} [Field K]
    [Module K (Additive ↥I)]
    (hcomm : ∀ g ∈ autSub D I, ∀ (c : K) (v : Additive ↥I),
      Additive.ofMul (g (Additive.toMul (c • v))) = c • Additive.ofMul (g (Additive.toMul v))) :
    ∃ f : K →+* F, Function.Injective f := by
  obtain ⟨v₀, hv₀, i₀, j₀, hij⟩ := exists_entry_ne_zero (β := β) hI0
  have hd : 0 < d := Fin.pos i₀
  obtain ⟨e, he⟩ := exists_equiv_column hM hI0 hIinv hImin
  let E : Additive ↥I ≃+ (Fin d → F) :=
    { toFun := fun x => Multiplicative.toAdd (e (Additive.toMul x))
      invFun := fun w => Additive.ofMul (e.symm (Multiplicative.ofAdd w))
      left_inv := fun x => by simp
      right_inv := fun w => by simp
      map_add' := fun x y => by simp }
  have hstab := le_stabSub_of_invariant hIinv
  have hE : ∀ (g : ↥D) (x : Additive ↥I),
      E.symm ((ρ g : Matrix (Fin d) (Fin d) F) *ᵥ E x) =
        Additive.ofMul (resHom I ⟨(g : MulAut V), hstab g.2⟩ (Additive.toMul x)) := by
    intro g x
    have hv : (g : MulAut V) ((Additive.toMul x : ↥I) : V) ∈ I :=
      hIinv g g.2 _ (Additive.toMul x).2
    have h1 := he g (Additive.toMul x) hv
    change Additive.ofMul (e.symm (Multiplicative.ofAdd
      ((ρ g : Matrix (Fin d) (Fin d) F) *ᵥ Multiplicative.toAdd (e (Additive.toMul x))))) = _
    rw [← h1, MulEquiv.symm_apply_apply]
    rfl
  obtain ⟨f, -⟩ := exists_ringHom_of_commuting_scalars hM hd E fun g c x => by
    rw [hE, hE]
    exact hcomm _ (mem_autSub.2 ⟨⟨g, hstab g.2⟩, g.2, rfl⟩) c x
  exact ⟨f, f.injective⟩

theorem dvd_of_smul_comm [Finite F] (hM : IsMatModel D X β ρ σ) {I : Subgroup V}
    (hI0 : I ≠ ⊥) (hIinv : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I)
    (hImin : ∀ U ≤ I, (∀ y ∈ D, ∀ v ∈ U, y v ∈ U) → U = ⊥ ∨ U = I) {K : Type} [Field K]
    [Module K (Additive ↥I)]
    (hcomm : ∀ g ∈ autSub D I, ∀ (c : K) (v : Additive ↥I),
      Additive.ofMul (g (Additive.toMul (c • v))) = c • Additive.ofMul (g (Additive.toMul v)))
    {a e : ℕ} (hK : Nat.card K = 2 ^ a) (hF : Nat.card F = 2 ^ e) : a ∣ e := by
  obtain ⟨f, -⟩ := exists_ringHom_of_smul_comm hM hI0 hIinv hImin hcomm
  exact dvd_of_ringHom f hK hF

end Dictionary

end Z3D

end CFSG.Quasithin
