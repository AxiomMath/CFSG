module

public import CFSG.Quasithin.Vol2.Ch9L34Herm9
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.H13.Ch9.L34M

open CFSG.Fischer Matrix CFSG.Quasithin.H13.Ch9.Herm9

@[expose] def w0 : Matrix (Fin 3) (Fin 3) F4 := Matrix.of ![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]]

theorem w0_mul_w0 : w0 * w0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w0, Matrix.mul_apply, Fin.sum_univ_three]

theorem w0_transpose : w0ᵀ = w0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem w0_mul_w0_mul (X : Matrix (Fin 3) (Fin 3) F4) : w0 * (w0 * X) = X := by
  rw [← Matrix.mul_assoc, w0_mul_w0, Matrix.one_mul]

theorem bar_w0 : bar w0 = w0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w0, bar_apply, cj_zero, cj_one]

@[expose] def grM (g : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4 :=
  w0 * (↑g⁻¹ : Matrix (Fin 3) (Fin 3) F4)ᵀ * w0

theorem grM_mul_grM_inv (g : GL (Fin 3) F4) :
    grM g * (w0 * (↑g : Matrix (Fin 3) (Fin 3) F4)ᵀ * w0) = 1 := by
  simp only [grM, Matrix.mul_assoc, w0_mul_w0_mul]
  rw [← Matrix.mul_assoc ((↑g⁻¹ : Matrix (Fin 3) (Fin 3) F4)ᵀ), ← transpose_mul, Units.mul_inv,
    transpose_one, Matrix.one_mul, w0_mul_w0]

theorem grM_inv_mul_grM (g : GL (Fin 3) F4) :
    (w0 * (↑g : Matrix (Fin 3) (Fin 3) F4)ᵀ * w0) * grM g = 1 := by
  simp only [grM, Matrix.mul_assoc, w0_mul_w0_mul]
  rw [← Matrix.mul_assoc ((↑g : Matrix (Fin 3) (Fin 3) F4)ᵀ), ← transpose_mul, Units.inv_mul,
    transpose_one, Matrix.one_mul, w0_mul_w0]

@[expose] def grU (g : GL (Fin 3) F4) : GL (Fin 3) F4 :=
  ⟨grM g, w0 * (↑g : Matrix (Fin 3) (Fin 3) F4)ᵀ * w0, grM_mul_grM_inv g, grM_inv_mul_grM g⟩

theorem coe_grU (g : GL (Fin 3) F4) : (grU g : Matrix (Fin 3) (Fin 3) F4) = grM g := rfl

theorem coe_grU_inv (g : GL (Fin 3) F4) :
    ((grU g)⁻¹ : GL (Fin 3) F4) = w0 * (↑g : Matrix (Fin 3) (Fin 3) F4)ᵀ * w0 := rfl

theorem grU_grU (g : GL (Fin 3) F4) : grU (grU g) = g := by
  apply Units.ext
  rw [coe_grU, grM, coe_grU_inv, transpose_mul, transpose_mul, w0_transpose, transpose_transpose,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, w0_mul_w0, Matrix.one_mul, Matrix.mul_assoc,
    w0_mul_w0, Matrix.mul_one]

theorem grU_mul (g h : GL (Fin 3) F4) : grU (g * h) = grU g * grU h := by
  apply Units.ext
  rw [Units.val_mul, coe_grU, coe_grU, coe_grU, grM, grM, grM, _root_.mul_inv_rev, Units.val_mul,
    transpose_mul]
  simp only [Matrix.mul_assoc, w0_mul_w0_mul]

@[expose] def grGL : GL (Fin 3) F4 ≃* GL (Fin 3) F4 where
  toFun := grU
  invFun := grU
  left_inv := grU_grU
  right_inv := grU_grU
  map_mul' := grU_mul

theorem grGL_apply (g : GL (Fin 3) F4) : grGL g = grU g := rfl

theorem frobGL_inv (g : GL (Fin 3) F4) :
    ((frobGL g)⁻¹ : GL (Fin 3) F4) = bar (↑g⁻¹ : Matrix (Fin 3) (Fin 3) F4) := by
  rw [← map_inv, coe_frobGL]

theorem frobGL_grGL (g : GL (Fin 3) F4) : frobGL (grGL g) = grGL (frobGL g) := by
  apply Units.ext
  rw [coe_frobGL, grGL_apply, grGL_apply, coe_grU, coe_grU, grM, grM, bar_mul, bar_mul,
    bar_w0, bar_transpose, frobGL_inv]

abbrev C2 : Type := Multiplicative (ZMod 2)

abbrev C22 : Type := Multiplicative (ZMod 2 × ZMod 2)

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

@[expose] def c2Hom {M : Type*} [Monoid M] (t : M) (ht : t * t = 1) : C2 →* M where
  toFun a := if Multiplicative.toAdd a = 0 then 1 else t
  map_one' := by simp
  map_mul' a b := by
    rcases zmod2_cases (Multiplicative.toAdd a) with ha | ha <;>
      rcases zmod2_cases (Multiplicative.toAdd b) with hb | hb <;>
      simp [ha, hb, ht, show (1 : ZMod 2) + 1 = 0 from rfl]

theorem c2Hom_apply {M : Type*} [Monoid M] (t : M) (ht : t * t = 1) (a : C2) :
    c2Hom t ht a = if Multiplicative.toAdd a = 0 then 1 else t := rfl

@[expose] def c22Hom {M : Type*} [Monoid M] (s t : M) (hs : s * s = 1) (ht : t * t = 1)
    (hst : s * t = t * s) : C22 →* M where
  toFun a := (if (Multiplicative.toAdd a).1 = 0 then 1 else s) *
    (if (Multiplicative.toAdd a).2 = 0 then 1 else t)
  map_one' := by simp
  map_mul' a b := by
    have h1 : ∀ x : M, s * (s * x) = x := fun x => by rw [← mul_assoc, hs, one_mul]
    have h3 : ∀ x : M, t * (s * x) = s * (t * x) := fun x => by rw [← mul_assoc, ← hst, mul_assoc]
    have h4 : t * s = s * t := hst.symm
    rcases zmod2_cases (Multiplicative.toAdd a).1 with ha | ha <;>
      rcases zmod2_cases (Multiplicative.toAdd a).2 with ha' | ha' <;>
      rcases zmod2_cases (Multiplicative.toAdd b).1 with hb | hb <;>
      rcases zmod2_cases (Multiplicative.toAdd b).2 with hb' | hb' <;>
      simp [ha, ha', hb, hb', hs, ht, mul_assoc, h1, h3, h4,
        show (1 : ZMod 2) + 1 = 0 from rfl]

theorem c22Hom_apply {M : Type*} [Monoid M] (s t : M) (hs : s * s = 1) (ht : t * t = 1)
    (hst : s * t = t * s) (a : C22) :
    c22Hom s t hs ht hst a = (if (Multiplicative.toAdd a).1 = 0 then 1 else s) *
      (if (Multiplicative.toAdd a).2 = 0 then 1 else t) := rfl

theorem frobAut_sq : (frobGL : MulAut (GL (Fin 3) F4)) * frobGL = 1 :=
  MulEquiv.ext fun g => frobGL_frobGL g

theorem grAut_sq : (grGL : MulAut (GL (Fin 3) F4)) * grGL = 1 :=
  MulEquiv.ext fun g => grU_grU g

theorem frobAut_grAut :
    (frobGL : MulAut (GL (Fin 3) F4)) * grGL = grGL * frobGL :=
  MulEquiv.ext fun g => frobGL_grGL g

@[expose] def outAct9 : C2 →* MulAut (GL (Fin 3) F4) := c2Hom frobGL frobAut_sq

@[expose] def outAct : C22 →* MulAut (GL (Fin 3) F4) :=
  c22Hom frobGL grGL frobAut_sq grAut_sq frobAut_grAut

abbrev Gam9 : Type := GL (Fin 3) F4 ⋊[outAct9] C2

abbrev Gam : Type := GL (Fin 3) F4 ⋊[outAct] C22

instance : Finite Gam9 := Finite.of_equiv _ SemidirectProduct.equivProd.symm

instance : Finite Gam := Finite.of_equiv _ SemidirectProduct.equivProd.symm

theorem card_GL : Nat.card (GL (Fin 3) F4) = 181440 := by
  rw [Matrix.card_GL_field, F4.card]
  simp [Fin.prod_univ_three]

theorem card_C2 : Nat.card C2 = 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

theorem card_C22 : Nat.card C22 = 4 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_prod, ZMod.card]

theorem card_Gam9 : Nat.card Gam9 = 2 ^ 7 * 2835 := by
  rw [SemidirectProduct.card, card_GL, card_C2]
  norm_num

theorem card_Gam : Nat.card Gam = 2 ^ 8 * 2835 := by
  rw [SemidirectProduct.card, card_GL, card_C22]
  norm_num

theorem factorization_two (k : ℕ) : (2 ^ k * 2835).factorization 2 = k := by
  rw [Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

@[expose] def um (a b c : F4) : Matrix (Fin 3) (Fin 3) F4 :=
  Matrix.of ![![1, a, b], ![0, 1, c], ![0, 0, 1]]

theorem um_mul (a b c a' b' c' : F4) :
    um a b c * um a' b' c' = um (a + a') (b + a * c' + b') (c + c') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [um, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem um_zero : um 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem add_self_F4 (x : F4) : x + x = 0 := by
  obtain ⟨a⟩ := x
  rw [mk_add_mk, zero_eq]
  congr 1
  revert a
  decide

theorem um_mul_inv (a b c : F4) : um a b c * um a (a * c + b) c = 1 := by
  rw [um_mul, add_self_F4, add_self_F4, ← um_zero]
  congr 1
  rw [← add_assoc, add_assoc b, add_self_F4, add_zero, add_self_F4]

@[expose] def uGL (a b c : F4) : GL (Fin 3) F4 :=
  ⟨um a b c, um a (a * c + b) c, um_mul_inv a b c, by
    have h := um_mul_inv a (a * c + b) c
    rwa [← add_assoc, add_self_F4, zero_add] at h⟩

theorem coe_uGL (a b c : F4) : (uGL a b c : Matrix (Fin 3) (Fin 3) F4) = um a b c := rfl

theorem coe_uGL_inv (a b c : F4) :
    ((uGL a b c)⁻¹ : GL (Fin 3) F4) = um a (a * c + b) c := rfl

theorem uGL_injective {a b c a' b' c' : F4} (h : uGL a b c = uGL a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have h' := congrArg (fun g : GL (Fin 3) F4 => (g : Matrix (Fin 3) (Fin 3) F4)) h
  simp only [coe_uGL] at h'
  exact ⟨congrFun (congrFun h' 0) 1, congrFun (congrFun h' 0) 2, congrFun (congrFun h' 1) 2⟩

@[expose] def U : Subgroup (GL (Fin 3) F4) where
  carrier := {g | ∃ a b c, g = uGL a b c}
  one_mem' := ⟨0, 0, 0, Units.ext (by rw [coe_uGL, um_zero, Units.val_one])⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨a + a', b + a * c' + b', c + c', Units.ext (by rw [Units.val_mul, coe_uGL, coe_uGL,
      coe_uGL, um_mul])⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, rfl⟩
    exact ⟨a, a * c + b, c, Units.ext (by rw [coe_uGL_inv, coe_uGL])⟩

theorem mem_U {g : GL (Fin 3) F4} : g ∈ U ↔ ∃ a b c, g = uGL a b c := Iff.rfl

theorem card_U : Nat.card U = 64 := by
  have e : (F4 × F4 × F4) ≃ U :=
    Equiv.ofBijective (fun x => ⟨uGL x.1 x.2.1 x.2.2, x.1, x.2.1, x.2.2, rfl⟩) (by
      constructor
      · rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
        obtain ⟨h1, h2, h3⟩ := uGL_injective (congrArg Subtype.val h)
        exact Prod.ext h1 (Prod.ext h2 h3)
      · rintro ⟨g, a, b, c, rfl⟩
        exact ⟨(a, b, c), rfl⟩)
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card, F4.card]

theorem frobGL_uGL (a b c : F4) : frobGL (uGL a b c) = uGL (cj a) (cj b) (cj c) := by
  apply Units.ext
  rw [coe_frobGL, coe_uGL, coe_uGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bar_apply, um, cj_zero, cj_one]

theorem grGL_uGL (a b c : F4) : grGL (uGL a b c) = uGL c (a * c + b) a := by
  apply Units.ext
  rw [grGL_apply, coe_grU, grM, coe_uGL_inv, coe_uGL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [w0, um, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct]

theorem frobGL_mem_U {g : GL (Fin 3) F4} (hg : g ∈ U) : frobGL g ∈ U := by
  obtain ⟨a, b, c, rfl⟩ := hg
  exact ⟨_, _, _, frobGL_uGL a b c⟩

theorem grGL_mem_U {g : GL (Fin 3) F4} (hg : g ∈ U) : grGL g ∈ U := by
  obtain ⟨a, b, c, rfl⟩ := hg
  exact ⟨_, _, _, grGL_uGL a b c⟩

theorem outAct9_mem_U (h : C2) {g : GL (Fin 3) F4} (hg : g ∈ U) : outAct9 h g ∈ U := by
  rw [outAct9, c2Hom_apply]
  split_ifs
  · exact hg
  · exact frobGL_mem_U hg

theorem outAct_mem_U (h : C22) {g : GL (Fin 3) F4} (hg : g ∈ U) : outAct h g ∈ U := by
  rw [outAct, c22Hom_apply, MulAut.mul_apply]
  split_ifs
  · exact hg
  · exact grGL_mem_U hg
  · exact frobGL_mem_U hg
  · exact frobGL_mem_U (grGL_mem_U hg)

@[expose] def Sig9 : Subgroup Gam9 where
  carrier := {x | x.left ∈ U}
  one_mem' := U.one_mem
  mul_mem' {x y} hx hy := by
    show x.left * outAct9 x.right y.left ∈ U
    exact U.mul_mem hx (outAct9_mem_U _ hy)
  inv_mem' {x} hx := by
    show outAct9 x.right⁻¹ x.left⁻¹ ∈ U
    exact outAct9_mem_U _ (U.inv_mem hx)

@[expose] def Sig : Subgroup Gam where
  carrier := {x | x.left ∈ U}
  one_mem' := U.one_mem
  mul_mem' {x y} hx hy := by
    show x.left * outAct x.right y.left ∈ U
    exact U.mul_mem hx (outAct_mem_U _ hy)
  inv_mem' {x} hx := by
    show outAct x.right⁻¹ x.left⁻¹ ∈ U
    exact outAct_mem_U _ (U.inv_mem hx)

theorem card_Sig9 : Nat.card Sig9 = 2 ^ 7 := by
  have e : Sig9 ≃ U × C2 :=
    { toFun := fun x => (⟨x.1.left, x.2⟩, x.1.right)
      invFun := fun y => ⟨⟨y.1.1, y.2⟩, y.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_prod, card_U, card_C2]
  norm_num

theorem card_Sig : Nat.card Sig = 2 ^ 8 := by
  have e : Sig ≃ U × C22 :=
    { toFun := fun x => (⟨x.1.left, x.2⟩, x.1.right)
      invFun := fun y => ⟨⟨y.1.1, y.2⟩, y.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_prod, card_U, card_C22]
  norm_num

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

@[expose] def sylSig9 : Sylow 2 Gam9 :=
  Sylow.ofCard Sig9 (by rw [card_Sig9, card_Gam9, factorization_two])

@[expose] def sylSig : Sylow 2 Gam :=
  Sylow.ofCard Sig (by rw [card_Sig, card_Gam, factorization_two])

theorem coe_sylSig9 : (sylSig9 : Subgroup Gam9) = Sig9 := rfl

theorem coe_sylSig : (sylSig : Subgroup Gam) = Sig := rfl

theorem exists_conj_le {Γ M : Type*} [Group Γ] [Finite Γ] [Group M] (ρ : Γ →* M)
    (P₀ : Sylow 2 Γ) {B : Subgroup M} (hB : B ≤ ρ.range) (h2 : IsPGroup 2 B) :
    ∃ g : Γ, B.map (MulAut.conj (ρ g)⁻¹).toMonoidHom ≤ (P₀ : Subgroup Γ).map ρ := by
  classical
  set Q := B.comap ρ with hQ
  let f : Q →* B := (ρ.domRestrict Q).codRestrict B fun x => x.2
  have hf : Function.Surjective f := by
    rintro ⟨b, hb⟩
    obtain ⟨g, rfl⟩ := hB hb
    exact ⟨⟨g, hb⟩, rfl⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 Q))
  have hPB : (P : Subgroup Q).map f = ⊤ := by
    have S := P.mapSurjective hf
    have htop : ((P.mapSurjective hf : Sylow 2 B) : Subgroup B) = ⊤ :=
      ((P.mapSurjective hf).is_maximal' (h2.to_subgroup ⊤) le_top).symm
    rwa [Sylow.coe_mapSurjective] at htop
  set P' := (P : Subgroup Q).map Q.subtype with hP'
  have hP'2 : IsPGroup 2 P' := P.isPGroup'.map _
  obtain ⟨R, hR⟩ := hP'2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ P₀ R
  have hBP : B ≤ P'.map ρ := by
    intro b hb
    have hb' : (⟨b, hb⟩ : B) ∈ (P : Subgroup Q).map f := hPB ▸ Subgroup.mem_top _
    obtain ⟨x, hx, hxb⟩ := hb'
    refine ⟨x, ⟨x, hx, rfl⟩, ?_⟩
    exact congrArg Subtype.val hxb
  have hRg : (R : Subgroup Γ) = (P₀ : Subgroup Γ).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  refine ⟨g, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  obtain ⟨x, hxP, hxb⟩ := hBP hb
  have hxR := hR hxP
  rw [hRg] at hxR
  obtain ⟨y, hy, rfl⟩ := hxR
  refine ⟨y, hy, ?_⟩
  rw [← hxb]
  simp [map_mul, map_inv, mul_assoc]

end CFSG.Quasithin.H13.Ch9.L34M
