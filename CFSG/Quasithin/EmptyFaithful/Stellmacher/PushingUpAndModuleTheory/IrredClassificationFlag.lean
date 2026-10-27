module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.IrredClassificationPerm
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.IrredClassificationBase

public section

namespace CFSG.Quasithin.F53Mod

open Equiv Matrix

@[expose] def Tmask : List ℕ :=
  [32767, 17082, 23430, 23784, 14256, 28032, 3584, 28188, 31836, 25152, 22848, 1564, 9216, 6236,
    18432]

@[expose] def Tcols : List ℕ :=
  [1, 57, 58, 15, 23, 154, 978, 9754, 18963, 4205, 438, 14256, 23784, 23430, 15685]

@[expose] def Tm : Matrix (Fin 15) (Fin 15) (ZMod 2) :=
  Matrix.of fun j ω => if (Tmask.getD j.val 0).testBit ω.val then 1 else 0

@[expose] def Tim : Matrix (Fin 15) (Fin 15) (ZMod 2) :=
  Matrix.of fun ω k => if (Tcols.getD k.val 0).testBit ω.val then 1 else 0

@[expose] noncomputable def Rm (σ : Perm (Fin 5)) : Matrix (Fin 15) (Fin 15) (ZMod 2) :=
  Matrix.of fun j k => ∑ ω, Tm j (piF σ ω) * Tim ω k

theorem Tim_Tm_entries :
    ∀ a b : Fin 15, ∑ k, Tim a k * Tm k b = if a = b then 1 else 0 := by decide +kernel

theorem Tim_Tm : Tim * Tm = 1 := by
  ext a b
  rw [Matrix.mul_apply, Tim_Tm_entries a b]
  simp [Matrix.one_apply]

theorem Tm_Tim_entries :
    ∀ a b : Fin 15, ∑ k, Tm a k * Tim k b = if a = b then 1 else 0 := by decide +kernel

theorem Tm_Tim : Tm * Tim = 1 := by
  ext a b
  rw [Matrix.mul_apply, Tm_Tim_entries a b]
  simp [Matrix.one_apply]

@[expose] noncomputable def vact (σ : Perm (Fin 5)) (x : Fin 15 → ZMod 2) : Fin 15 → ZMod 2 :=
  fun ω => x (piF σ⁻¹ ω)

theorem toAdd_act (σ : Perm (Fin 5)) (x : Pm.W) :
    Multiplicative.toAdd (Pm.act σ x) = vact σ (Multiplicative.toAdd x) :=
  funext fun ω => Pm_act_apply σ x ω

@[expose] noncomputable def Pmat (σ : Perm (Fin 5)) : Matrix (Fin 15) (Fin 15) (ZMod 2) :=
  Matrix.of fun a b => if a = piF σ b then 1 else 0

theorem Pmat_mulVec (σ : Perm (Fin 5)) (x : Fin 15 → ZMod 2) : Pmat σ *ᵥ x = vact σ x := by
  ext a
  simp only [Matrix.mulVec, dotProduct, Pmat, Matrix.of_apply, vact]
  rw [Finset.sum_eq_single (piF σ⁻¹ a)]
  · rw [← piF_mul, mul_inv_cancel, piF_one]
    simp
  · intro b _ hb
    have : a ≠ piF σ b := by
      intro h
      apply hb
      rw [h, ← piF_mul, inv_mul_cancel, piF_one]
    simp [this]
  · simp

theorem Rm_eq (σ : Perm (Fin 5)) : Rm σ = Tm * Pmat σ * Tim := by
  ext j k
  simp only [Rm, Matrix.of_apply, Matrix.mul_apply, Pmat]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp [mul_ite]

theorem T_act (σ : Perm (Fin 5)) (x : Fin 15 → ZMod 2) :
    Tm *ᵥ vact σ x = Rm σ *ᵥ (Tm *ᵥ x) := by
  rw [Rm_eq, Matrix.mulVec_mulVec, Matrix.mul_assoc (Tm * Pmat σ), Tim_Tm, Matrix.mul_one,
    ← Matrix.mulVec_mulVec, Pmat_mulVec]

@[expose] def ta (x : Pm.W) : Fin 15 → ZMod 2 :=
  Multiplicative.toAdd (show Multiplicative (Fin 15 → ZMod 2) from x)

theorem ta_one : ta 1 = 0 := rfl

theorem ta_mul (x y : Pm.W) : ta (x * y) = ta x + ta y := rfl

theorem ta_inv (x : Pm.W) : ta x⁻¹ = ta x := by
  funext ω
  have h2 : ∀ a : ZMod 2, -a = a := by decide
  exact h2 _

theorem ta_act (σ : Perm (Fin 5)) (x : Pm.W) : ta (Pm.act σ x) = vact σ (ta x) := toAdd_act σ x

@[expose] def Qd (d : ℕ) : Subgroup Pm.W where
  carrier := {x | ∀ j : Fin 15, j.val < d → (Tm *ᵥ ta x) j = 0}
  one_mem' := fun j _ => by simp [ta_one]
  mul_mem' := fun {x y} hx hy j hj => by
    have hx' : (Tm *ᵥ ta x) j = 0 := hx j hj
    have hy' : (Tm *ᵥ ta y) j = 0 := hy j hj
    show (Tm *ᵥ ta (x * y)) j = 0
    rw [ta_mul, Matrix.mulVec_add, Pi.add_apply, hx', hy', add_zero]
  inv_mem' := fun {x} hx j hj => by
    have hx' : (Tm *ᵥ ta x) j = 0 := hx j hj
    show (Tm *ᵥ ta x⁻¹) j = 0
    rw [ta_inv]
    exact hx'

theorem Qd_act_mem {d : ℕ} {σ : Perm (Fin 5)}
    (h : ∀ j k : Fin 15, j.val < d → d ≤ k.val → Rm σ j k = 0) :
    ∀ x ∈ Qd d, Pm.act σ x ∈ Qd d := by
  intro x hx j hj
  show (Tm *ᵥ ta (Pm.act σ x)) j = 0
  rw [ta_act, T_act]
  show ∑ k, Rm σ j k * (Tm *ᵥ ta x) k = 0
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k.val < d
  · rw [hx k hk, mul_zero]
  · rw [h j k hj (by omega), zero_mul]

@[expose] def gens5 : Set (Perm (Fin 5)) := {finRotate 5, swap 0 1}

theorem closure_gens5 : Subgroup.closure gens5 = ⊤ := by
  have h := Equiv.Perm.closure_cycle_adjacent_swap (σ := finRotate 5) isCycle_finRotate
    support_finRotate (0 : Fin 5)
  have e : finRotate 5 (0 : Fin 5) = 1 := by decide
  rw [e] at h
  exact h

theorem Qd_inv {d : ℕ}
    (h : ∀ g ∈ gens5, ∀ j k : Fin 15, j.val < d → d ≤ k.val → Rm g j k = 0) :
    Pm.InvSub (Qd d) :=
  invSub_of_gens closure_gens5 fun g hg => Qd_act_mem (h g hg)

theorem Qd_zero : Qd 0 = ⊤ := by
  rw [eq_top_iff]
  intro x _ j hj
  exact absurd hj (by omega)

theorem Qd_fifteen : Qd 15 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have h0 : Tm *ᵥ ta x = 0 := funext fun j => hx j j.isLt
  have h1 : ta x = 0 := by
    have : Tim *ᵥ (Tm *ᵥ ta x) = ta x := by
      rw [Matrix.mulVec_mulVec, Tim_Tm, Matrix.one_mulVec]
    rw [← this, h0, Matrix.mulVec_zero]
  exact Multiplicative.toAdd.injective h1

@[expose] def ιB (off s : ℕ) (hs : off + s ≤ 15) (b : Fin s) : Fin 15 := ⟨off + b.val, by omega⟩

@[expose] def embB (off s : ℕ) (c : Fin s → ZMod 2) (j : Fin 15) : ZMod 2 :=
  if h : off ≤ j.val ∧ j.val < off + s then c ⟨j.val - off, by omega⟩ else 0

theorem embB_ιB (off s : ℕ) (hs : off + s ≤ 15) (c : Fin s → ZMod 2) (b : Fin s) :
    embB off s c (ιB off s hs b) = c b := by
  have h : off ≤ off + b.val ∧ off + b.val < off + s := ⟨by omega, by omega⟩
  unfold embB ιB
  simp only [h]
  exact congrArg c (Fin.ext (by simp))

theorem embB_of_lt (off s : ℕ) (c : Fin s → ZMod 2) (j : Fin 15) (hj : j.val < off) :
    embB off s c j = 0 := by
  have h : ¬ (off ≤ j.val ∧ j.val < off + s) := by omega
  simp [embB, h]

theorem sum_block (off s : ℕ) (hs : off + s ≤ 15) (m : Fin 15 → ZMod 2) (c : Fin s → ZMod 2) :
    ∑ k, m k * embB off s c k = ∑ a : Fin s, m (ιB off s hs a) * c a := by
  have hinj : Function.Injective (ιB off s hs) := by
    intro a b hab
    have := congrArg Fin.val hab
    simp only [ιB] at this
    exact Fin.ext (by omega)
  have h1 : ∑ k ∈ Finset.univ.image (ιB off s hs), m k * embB off s c k =
      ∑ k, m k * embB off s c k := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hk
    have : embB off s c k = 0 := by
      by_cases h : off ≤ k.val ∧ k.val < off + s
      · exfalso
        apply hk
        refine Finset.mem_image.mpr ⟨⟨k.val - off, by omega⟩, Finset.mem_univ _, ?_⟩
        ext
        simp only [ιB]
        omega
      · simp [embB, h]
    rw [this, mul_zero]
  rw [← h1, Finset.sum_image (fun a _ b _ hab => hinj hab)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [embB_ιB]

@[expose] def blkHom (off s : ℕ) (hs : off + s ≤ 15) : Pm.W →* Multiplicative (Fin s → ZMod 2) where
  toFun x := Multiplicative.ofAdd (fun b => (Tm *ᵥ ta x) (ιB off s hs b))
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext b
    show (Tm *ᵥ ta 1) _ = 0
    rw [ta_one, Matrix.mulVec_zero]
    rfl
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext b
    show (Tm *ᵥ ta (x * y)) _ = (Tm *ᵥ ta x) _ + (Tm *ᵥ ta y) _
    rw [ta_mul, Matrix.mulVec_add]
    rfl

theorem step_of_check (off s : ℕ) (hs : off + s ≤ 15) (X : Model 5) (hX : X.IsIrred)
    (C : Multiplicative (Fin s → ZMod 2) →* X.W)
    (hC1 : ∀ c : Fin s → ZMod 2, C (Multiplicative.ofAdd c) = 1 → c = 0)
    (hC2 : ∀ y, ∃ c : Fin s → ZMod 2, C (Multiplicative.ofAdd c) = y)
    (hQ : Pm.InvSub (Qd off))
    (hR : ∀ g ∈ gens5, ∀ j k : Fin 15, j.val < off + s → off + s ≤ k.val → Rm g j k = 0)
    (hE : ∀ g ∈ gens5, ∀ c : Fin s → ZMod 2,
      C (Multiplicative.ofAdd fun b => ∑ a, Rm g (ιB off s hs b) (ιB off s hs a) * c a) =
        X.act g (C (Multiplicative.ofAdd c))) :
    Step Pm (Qd off) (Qd (off + s)) X := by
  have hQ' : Pm.InvSub (Qd (off + s)) := Qd_inv hR
  have hle : Qd (off + s) ≤ Qd off := fun x hx j hj => hx j (by omega)
  have hker : ∀ x ∈ Qd off, C (blkHom off s hs x) = 1 ↔ x ∈ Qd (off + s) := by
    intro x hx
    constructor
    · intro hfx
      have h1 : blkHom off s hs x = 1 := by
        have := hC1 _ hfx
        apply Multiplicative.toAdd.injective
        exact this
      have h2 : ∀ b : Fin s, (Tm *ᵥ ta x) (ιB off s hs b) = 0 := fun b =>
        congrFun (congrArg Multiplicative.toAdd h1) b
      intro j hj
      by_cases hjo : j.val < off
      · exact hx j hjo
      · have := h2 ⟨j.val - off, by omega⟩
        have e : ιB off s hs ⟨j.val - off, by omega⟩ = j := by
          ext
          simp only [ιB]
          omega
        rwa [e] at this
    · intro hx'
      have h1 : blkHom off s hs x = 1 := by
        apply Multiplicative.toAdd.injective
        funext b
        exact hx' (ιB off s hs b) (by simp only [ιB]; omega)
      rw [h1, map_one]
  have hsec : ∀ y : X.W, ∃ x0 ∈ Qd off, C (blkHom off s hs x0) = y ∧
      ∀ g ∈ gens5, C (blkHom off s hs (Pm.act g x0)) = X.act g y := by
    intro y
    obtain ⟨c, hc⟩ := hC2 y
    set e : Fin 15 → ZMod 2 := embB off s c with he
    let x0 : Pm.W := Multiplicative.ofAdd (Tim *ᵥ e)
    have hT : Tm *ᵥ ta x0 = e := by
      show Tm *ᵥ (Tim *ᵥ e) = e
      rw [Matrix.mulVec_mulVec, Tm_Tim, Matrix.one_mulVec]
    have hx0 : x0 ∈ Qd off := fun j hj => by rw [hT]; exact embB_of_lt off s _ j hj
    have hb : blkHom off s hs x0 = Multiplicative.ofAdd c := by
      apply Multiplicative.toAdd.injective
      funext b
      show (Tm *ᵥ ta x0) (ιB off s hs b) = _
      rw [hT]
      exact embB_ιB off s hs _ b
    refine ⟨x0, hx0, by rw [hb, hc], fun g hg => ?_⟩
    have h1 : blkHom off s hs (Pm.act g x0) = Multiplicative.ofAdd fun b =>
        ∑ a, Rm g (ιB off s hs b) (ιB off s hs a) * c a := by
      apply Multiplicative.toAdd.injective
      funext b
      show (Tm *ᵥ ta (Pm.act g x0)) (ιB off s hs b) = _
      rw [ta_act, T_act, hT]
      show ∑ k, Rm g (ιB off s hs b) k * embB off s c k = _
      exact sum_block off s hs _ _
    rw [h1, hE g hg c, hc]
  exact step_of_section closure_gens5 hQ hQ' hle hX (C.comp (blkHom off s hs)) hker hsec

end CFSG.Quasithin.F53Mod
