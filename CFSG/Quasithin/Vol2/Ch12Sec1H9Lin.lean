module

public import CFSG.Quasithin.Vol2.Ch12Sec1H9Coord
public import CFSG.Quasithin.Vol2.Ch12Sec1H9Conj

public section

namespace CFSG.Quasithin.H13.H9Coord

open CFSG.Open CFSG.Quasithin.SLnTwo CFSG.ComponentClassification.CatalogueBGraphForm
open scoped Matrix

variable {n : ℕ}

theorem card_vec : Nat.card (Vec n) = 2 ^ n := by
  rw [Nat.card_congr (Multiplicative.toAdd (α := Fin n → ZMod 2)), Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]

theorem dot_glGraph (A : GL (Fin n) (ZMod 2)) (x z : Fin n → ZMod 2) :
    ((A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) ⬝ᵥ
      ((glGraphAut n (ZMod 2) A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ z) = x ⬝ᵥ z := by
  rw [glGraphAut_matrix, Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one,
    dotProduct_comm]

theorem card_mul_card_orth_gen {F : Type*} [Field F] [Finite F] (S : Submodule F (Fin n → F)) :
    Nat.card S * Nat.card {y : Fin n → F // ∀ x ∈ S, x ⬝ᵥ y = 0} = Nat.card F ^ n := by
  have e : {y : Fin n → F // ∀ x ∈ S, x ⬝ᵥ y = 0} ≃ S.dualAnnihilator :=
    { toFun := fun y => ⟨dotProductEquiv F (Fin n) y.1, by
        rw [Submodule.mem_dualAnnihilator]
        intro x hx
        rw [dotProductEquiv_apply_apply, dotProduct_comm]
        exact y.2 x hx⟩
      invFun := fun φ => ⟨(dotProductEquiv F (Fin n)).symm φ.1, by
        intro x hx
        have h := (Submodule.mem_dualAnnihilator _).mp φ.2 x hx
        rw [dotProduct_comm, ← dotProductEquiv_apply_apply, LinearEquiv.apply_symm_apply]
        exact h⟩
      left_inv := fun y => Subtype.ext (LinearEquiv.symm_apply_apply _ _)
      right_inv := fun φ => Subtype.ext (LinearEquiv.apply_symm_apply _ _) }
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := F) (V := S),
    Module.natCard_eq_pow_finrank (K := F) (V := S.dualAnnihilator), ← pow_add,
    Subspace.finrank_add_finrank_dualAnnihilator_eq, Module.finrank_fin_fun]

@[expose] def toSub (U : AddSubgroup (Fin n → ZMod 2)) : Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := U
  add_mem' := U.add_mem
  zero_mem' := U.zero_mem
  smul_mem' c x hx := by
    rcases zmod_two_cases c with rfl | rfl
    · rw [zero_smul]
      exact U.zero_mem
    · rwa [one_smul]

theorem card_mul_card_orth (U : AddSubgroup (Fin n → ZMod 2)) :
    Nat.card U * Nat.card {y : Fin n → ZMod 2 // ∀ x ∈ U, x ⬝ᵥ y = 0} = 2 ^ n := by
  have h := card_mul_card_orth_gen (toSub U)
  rw [Nat.card_zmod] at h
  exact h

variable {W : Type} [CommGroup W] [Finite W] {M L T : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W}

theorem exists_linIso (hyp : H9Hyp n M L T W₁ W₂) (hn : 3 ≤ n) :
    ∃ (e : W ≃* Vec n × Vec n) (φ : ↥L ≃* GL (Fin n) (ZMod 2)),
      (∀ l : ↥L, ∀ w : W, e ((l : MulAut W) w) =
        (vecAut (φ l) (e w).1, vecAut (glGraphAut n (ZMod 2) (φ l)) (e w).2)) ∧
      (∀ m ∈ M, m ∉ L → ∃ P : GL (Fin n) (ZMod 2), ∀ w : W,
        e (m w) = (vecAut P (e w).2, vecAut (glGraphAut n (ZMod 2) P) (e w).1)) ∧
      (∀ w, w ∈ W₁ ↔ (e w).2 = 1) ∧ (∀ w, w ∈ W₂ ↔ (e w).1 = 1) := by
  have hexp₁ : ∀ u : ↥W₁, u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hyp.exp u)
  obtain ⟨e₁⟩ := exists_coord hexp₁ hyp.card₁
  obtain ⟨φ, hφ⟩ := exists_glRep hyp e₁
  obtain ⟨t, htT, htL, ht⟩ := hyp.swap
  have htM : t ∈ M := hyp.sylow_le htT
  obtain ⟨c, hc⟩ := exists_graph hyp hn φ htM htL
  have hsq := phi_sq hyp φ htM htL hc
  let E : Vec n × Vec n →* W :=
    { toFun := fun p => (e₁.symm p.1 : W) * t (e₁.symm (vecAut c p.2) : W)
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul, Subgroup.coe_mul]
        exact mul_mul_mul_comm _ _ _ _ }
  have hE : ∀ p : Vec n × Vec n, E p = (e₁.symm p.1 : W) * t (e₁.symm (vecAut c p.2) : W) :=
    fun _ => rfl
  have hmem₁ : ∀ x, (e₁.symm x : W) ∈ W₁ := fun x => (e₁.symm x).2
  have hmem₂ : ∀ x, t (e₁.symm x : W) ∈ W₂ := fun x => by
    rw [ht]
    exact Subgroup.mem_map_of_mem t.toMonoidHom (e₁.symm x).2
  have hdisj : ∀ a ∈ W₁ ⊓ W₂, a = 1 := fun a ha => by
    rwa [hyp.inf, Subgroup.mem_bot] at ha
  have hcancel₁ : ∀ x, (e₁.symm x : W) = 1 → x = 1 := fun x h => by
    have h1 : e₁.symm x = 1 := Subtype.ext h
    simpa using congrArg e₁ h1
  have hcancel₂ : ∀ y, t (e₁.symm (vecAut c y) : W) = 1 → y = 1 := fun y h =>
    (map_eq_one_iff (vecAut c) (vecAut c).injective).mp
      (hcancel₁ _ ((map_eq_one_iff t t.injective).mp h))
  have hEinj : Function.Injective E := by
    rw [injective_iff_map_eq_one]
    intro p hp
    rw [hE] at hp
    have h2 : t (e₁.symm (vecAut c p.2) : W) = 1 := hdisj _ ⟨by
      have := W₁.mul_mem (W₁.inv_mem (hmem₁ p.1)) (hp ▸ W₁.one_mem)
      rwa [inv_mul_cancel_left] at this, hmem₂ _⟩
    rw [h2, mul_one] at hp
    exact Prod.ext (hcancel₁ _ hp) (hcancel₂ _ h2)
  have hcard : Nat.card W ≤ Nat.card (Vec n × Vec n) := by
    rw [H9Conj.card_W hyp, Nat.card_prod, card_vec]
  let e : W ≃* Vec n × Vec n :=
    (MulEquiv.ofBijective E (hEinj.bijective_of_nat_card_le hcard)).symm
  have he : ∀ p, e.symm p = E p := fun _ => rfl
  have heE : ∀ p, e (E p) = p := fun p => by rw [← he p, MulEquiv.apply_symm_apply]
  have hEe : ∀ w, E (e w) = w := fun w => by rw [← he, MulEquiv.symm_apply_apply]
  have hKL : ∀ l : ↥L, ∀ p : Vec n × Vec n, (l : MulAut W) (E p) =
      E (vecAut (φ l) p.1, vecAut (glGraphAut n (ZMod 2) (φ l)) p.2) := by
    intro l p
    have h1 : (l : MulAut W) (t (e₁.symm (vecAut c p.2) : W)) =
        t ((tConj hyp htM l : MulAut W) (e₁.symm (vecAut c p.2) : W)) := by
      rw [coe_tConj]
      simp [MulAut.mul_apply]
    have h2 : vecAut (c * glGraphAut n (ZMod 2) (φ l) * c⁻¹) (vecAut c p.2) =
        vecAut c (vecAut (glGraphAut n (ZMod 2) (φ l)) p.2) := by
      rw [vecAut_mul_apply, vecAut_mul_apply, ← vecAut_mul_apply c⁻¹ c, inv_mul_cancel,
        vecAut_one, MulAut.one_apply]
    rw [hE, hE, map_mul, hφ l, h1, hφ (tConj hyp htM l), hc l, h2]
  have hKt : ∀ p : Vec n × Vec n, t (E p) =
      E (vecAut (glGraphAut n (ZMod 2) c⁻¹) p.2, vecAut c⁻¹ p.1) := by
    intro p
    have ha : t (t (e₁.symm (vecAut c p.2) : W)) =
        (e₁.symm (vecAut (glGraphAut n (ZMod 2) c⁻¹) p.2) : W) := by
      rw [← hsq, vecAut_mul_apply]
      exact hφ ⟨t * t, mul_mem_L hyp htM htM htL htL⟩ (vecAut c p.2)
    have hb : vecAut c (vecAut c⁻¹ p.1) = p.1 := by
      rw [← vecAut_mul_apply, mul_inv_cancel, vecAut_one, MulAut.one_apply]
    rw [hE, hE, map_mul, ha, hb, mul_comm]
  have hLe : ∀ l : ↥L, ∀ w : W, e ((l : MulAut W) w) =
      (vecAut (φ l) (e w).1, vecAut (glGraphAut n (ZMod 2) (φ l)) (e w).2) := by
    intro l w
    have := hKL l (e w)
    rw [hEe] at this
    rw [this, heE]
  refine ⟨e, φ, hLe, fun m hm hmL => ?_, fun w => ?_, fun w => ?_⟩
  · have hl : t⁻¹ * m ∈ L := mul_mem_L hyp (M.inv_mem htM) hm
      (fun h => htL (by simpa using L.inv_mem h)) hmL
    refine ⟨glGraphAut n (ZMod 2) (c⁻¹ * φ ⟨_, hl⟩), fun w => ?_⟩
    have h1 : m w = t (((⟨_, hl⟩ : ↥L) : MulAut W) w) := by
      show m w = t ((t⁻¹ * m) w)
      rw [MulAut.mul_apply, MulAut.apply_inv_self]
    rw [h1, ← hEe (((⟨_, hl⟩ : ↥L) : MulAut W) w), hKt, heE, hLe,
      Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose, map_mul, vecAut_mul_apply,
      vecAut_mul_apply]
  · rw [← hEe w, heE, hE]
    constructor
    · intro h
      have h1 : t (e₁.symm (vecAut c (e w).2) : W) ∈ W₁ := by
        have := W₁.mul_mem (W₁.inv_mem (hmem₁ (e w).1)) h
        rwa [inv_mul_cancel_left] at this
      exact hcancel₂ _ (hdisj _ ⟨h1, hmem₂ _⟩)
    · intro h
      rw [h]
      simp
  · rw [← hEe w, heE, hE]
    constructor
    · intro h
      have h1 : (e₁.symm (e w).1 : W) ∈ W₂ := by
        have := W₂.mul_mem h (W₂.inv_mem (hmem₂ (vecAut c (e w).2)))
        rwa [mul_inv_cancel_right] at this
      exact hcancel₁ _ (hdisj _ ⟨hmem₁ _, h1⟩)
    · intro h
      rw [h]
      simpa using hmem₂ (vecAut c (e w).2)

theorem exists_goodDual (hyp : H9Hyp n M L T W₁ W₂) (hn : 3 ≤ n) :
    ∃ β : W → W → ZMod 2, IsDualH9 L W₁ W₂ β ∧
      (∀ U : Subgroup W, U ≤ W₁ →
        Nat.card U * Nat.card {c : W // c ∈ W₂ ∧ ∀ u ∈ U, β u c = 0} = 2 ^ n) ∧
      (∀ U : Subgroup W, U ≤ W₂ →
        Nat.card U * Nat.card {a : W // a ∈ W₁ ∧ ∀ c ∈ U, β a c = 0} = 2 ^ n) := by
  obtain ⟨e, φ, hLe, -, hW₁, hW₂⟩ := exists_linIso hyp hn
  have hL : ∀ l ∈ L, ∃ A : GL (Fin n) (ZMod 2), ∀ w : W,
      e (l w) = (vecAut A (e w).1, vecAut (glGraphAut n (ZMod 2) A) (e w).2) :=
    fun l hl => ⟨φ ⟨l, hl⟩, hLe ⟨l, hl⟩⟩
  let β : W → W → ZMod 2 := fun a c => (e a).1.toAdd ⬝ᵥ (e c).2.toAdd
  have hβ : ∀ a c, β a c = (e a).1.toAdd ⬝ᵥ (e c).2.toAdd := fun _ _ => rfl
  refine ⟨β, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro a _ b _ c _
    simp only [hβ, map_mul, Prod.fst_mul, toAdd_mul, add_dotProduct]
  · intro a _ c _ d _
    simp only [hβ, map_mul, Prod.snd_mul, toAdd_mul, dotProduct_add]
  · intro a ha ha1
    have hx : (e a).1.toAdd ≠ 0 := fun h => ha1 (by
      have h1 : e a = 1 := Prod.ext (by simpa using h) ((hW₁ a).mp ha)
      simpa using congrArg e.symm h1)
    obtain ⟨i, hi⟩ := exists_eq_one_of_ne_zero hx
    refine ⟨e.symm (1, Multiplicative.ofAdd (Pi.single i 1)), (hW₂ _).mpr (by simp), ?_⟩
    simp [hβ, hi]
  · intro c hc hc1
    have hy : (e c).2.toAdd ≠ 0 := fun h => hc1 (by
      have h1 : e c = 1 := Prod.ext ((hW₂ c).mp hc) (by simpa using h)
      simpa using congrArg e.symm h1)
    obtain ⟨i, hi⟩ := exists_eq_one_of_ne_zero hy
    refine ⟨e.symm (Multiplicative.ofAdd (Pi.single i 1), 1), (hW₁ _).mpr (by simp), ?_⟩
    simp [hβ, hi]
  · intro l hl a _ c _
    obtain ⟨A, hA⟩ := hL l hl
    rw [hβ, hβ, hA a, hA c]
    exact dot_glGraph A _ _
  · intro U hU
    let U₀ : AddSubgroup (Fin n → ZMod 2) :=
      { carrier := {x | e.symm (Multiplicative.ofAdd x, 1) ∈ U}
        add_mem' := fun {x y} hx hy => by
          have := U.mul_mem hx hy
          rwa [← map_mul, Prod.mk_mul_mk, one_mul, ← ofAdd_add] at this
        zero_mem' := by
          show e.symm 1 ∈ U
          rw [map_one]
          exact U.one_mem
        neg_mem' := fun {x} hx => by
          show e.symm (Multiplicative.ofAdd (-x), 1) ∈ U
          rwa [show -x = x from funext fun i => CharTwo.neg_eq (x i)] }
    have h1 : Nat.card U = Nat.card U₀ := Nat.card_congr
      { toFun := fun u => ⟨(e u).1.toAdd, by
          show e.symm (Multiplicative.ofAdd (e u).1.toAdd, 1) ∈ U
          rw [ofAdd_toAdd, ← (hW₁ u).mp (hU u.2)]
          simp⟩
        invFun := fun x => ⟨e.symm (Multiplicative.ofAdd x.1, 1), x.2⟩
        left_inv := fun u => Subtype.ext (by
          show e.symm (Multiplicative.ofAdd (e u).1.toAdd, 1) = u
          rw [ofAdd_toAdd, ← (hW₁ u).mp (hU u.2)]
          simp)
        right_inv := fun x => Subtype.ext (by simp) }
    have h2 : Nat.card {c : W // c ∈ W₂ ∧ ∀ u ∈ U, β u c = 0} =
        Nat.card {y : Fin n → ZMod 2 // ∀ x ∈ U₀, x ⬝ᵥ y = 0} := Nat.card_congr
      { toFun := fun c => ⟨(e c).2.toAdd, fun x hx => by
          have := c.2.2 _ hx
          simpa [hβ] using this⟩
        invFun := fun y => ⟨e.symm (1, Multiplicative.ofAdd y.1), (hW₂ _).mpr (by simp),
          fun u hu => by
            have h3 := y.2 (e u).1.toAdd (by
              show e.symm (Multiplicative.ofAdd (e u).1.toAdd, 1) ∈ U
              rw [ofAdd_toAdd, ← (hW₁ u).mp (hU hu)]
              simpa using hu)
            simpa [hβ] using h3⟩
        left_inv := fun c => Subtype.ext (by
          show e.symm (1, Multiplicative.ofAdd (e c).2.toAdd) = c
          rw [ofAdd_toAdd, ← (hW₂ c).mp c.2.1]
          simp)
        right_inv := fun y => Subtype.ext (by simp) }
    rw [h1, h2]
    exact card_mul_card_orth U₀
  · intro U hU
    let U₀ : AddSubgroup (Fin n → ZMod 2) :=
      { carrier := {y | e.symm (1, Multiplicative.ofAdd y) ∈ U}
        add_mem' := fun {x y} hx hy => by
          have := U.mul_mem hx hy
          rwa [← map_mul, Prod.mk_mul_mk, one_mul, ← ofAdd_add] at this
        zero_mem' := by
          show e.symm 1 ∈ U
          rw [map_one]
          exact U.one_mem
        neg_mem' := fun {x} hx => by
          show e.symm (1, Multiplicative.ofAdd (-x)) ∈ U
          rwa [show -x = x from funext fun i => CharTwo.neg_eq (x i)] }
    have h1 : Nat.card U = Nat.card U₀ := Nat.card_congr
      { toFun := fun c => ⟨(e c).2.toAdd, by
          show e.symm (1, Multiplicative.ofAdd (e c).2.toAdd) ∈ U
          rw [ofAdd_toAdd, ← (hW₂ c).mp (hU c.2)]
          simp⟩
        invFun := fun y => ⟨e.symm (1, Multiplicative.ofAdd y.1), y.2⟩
        left_inv := fun c => Subtype.ext (by
          show e.symm (1, Multiplicative.ofAdd (e c).2.toAdd) = c
          rw [ofAdd_toAdd, ← (hW₂ c).mp (hU c.2)]
          simp)
        right_inv := fun y => Subtype.ext (by simp) }
    have h2 : Nat.card {a : W // a ∈ W₁ ∧ ∀ c ∈ U, β a c = 0} =
        Nat.card {x : Fin n → ZMod 2 // ∀ y ∈ U₀, y ⬝ᵥ x = 0} := Nat.card_congr
      { toFun := fun a => ⟨(e a).1.toAdd, fun y hy => by
          have := a.2.2 _ hy
          rw [dotProduct_comm]
          simpa [hβ] using this⟩
        invFun := fun x => ⟨e.symm (Multiplicative.ofAdd x.1, 1), (hW₁ _).mpr (by simp),
          fun c hc => by
            have h3 := x.2 (e c).2.toAdd (by
              show e.symm (1, Multiplicative.ofAdd (e c).2.toAdd) ∈ U
              rw [ofAdd_toAdd, ← (hW₂ c).mp (hU hc)]
              simpa using hc)
            rw [dotProduct_comm] at h3
            simpa [hβ] using h3⟩
        left_inv := fun a => Subtype.ext (by
          show e.symm (Multiplicative.ofAdd (e a).1.toAdd, 1) = a
          rw [ofAdd_toAdd, ← (hW₁ a).mp a.2.1]
          simp)
        right_inv := fun x => Subtype.ext (by simp) }
    rw [h1, h2]
    exact card_mul_card_orth U₀

end CFSG.Quasithin.H13.H9Coord
