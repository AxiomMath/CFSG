module

public import CFSG.Quasithin.MS93.S37RBg
public import CFSG.Quasithin.MS93.S37LCase2
public import CFSG.Quasithin.MS93.S37ALR2

public section

namespace CFSG.Quasithin.MS93.S37R

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2
open CFSG.Quasithin.MS93.S37 CFSG.Quasithin.MS93.S37L
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]

@[expose] def iota (v : (Fin 2 → F) × F) : Multiplicative (V4 F × F) :=
  Multiplicative.ofAdd (Sum.elim v.1 0, v.2)

theorem eq_one_of_comm_mem_A (C : Cfg M T L F) {t : G} (ht : t ∈ L ⊔ pCoreOf 2 M) {v : G}
    (hv : v ∈ Uq M T L)
    (hA : ⁅t, v⁆ ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G)) : ⁅t, v⁆ = 1 := by
  have hc := C.comm_mem_Uq_of_mem (C.sup_le_M ht) hv
  have h0 : C.N.co ⟨⁅t, v⁆, hc⟩ = 0 := (C.N.co_eq_zero_iff _).2 hA
  rw [C.co_comm_rho ht hv hc, sub_eq_zero] at h0
  have := C.conj_eq_of_fix ⟨t, ht⟩ hv h0
  rw [commutatorElement_def]
  calc t * v * t⁻¹ * v⁻¹ = (t * v * t⁻¹) * v⁻¹ := rfl
    _ = 1 := by rw [this, mul_inv_cancel]

theorem mem_Qt_iff (C : Cfg M T L F) (φ : MulAut ↥(T1 M T L))
    (hφ : fixSp (C.rhoIm (Ut M T L φ)) = ln₀ F)
    {v : G} (hv : v ∈ Uq M T L) : v ∈ Qt M φ ↔ C.N.co ⟨v, hv⟩ ∈ ln₀ F := by
  rw [C.Qt_eq C.pCore_le_T1 T1_le_T, ← hφ,
    C.co_mem_fixSp_iff ((tImage_le φ _).trans T1_le_sup) ⟨v, hv⟩]
  exact ⟨fun h => h.2, fun h => ⟨C.Uq_le_T1 hv, h⟩⟩

omit [Fintype F] in
theorem fv_add (x x' : Fin 2 → F) : fv (x + x') = fv x + fv x' := by
  funext i
  rcases i with i | i <;> simp [fv]

structure Dat (C : Cfg M T L F) where
  θ : MulAut ↥(T1 M T L)
  hT : C.T0bar = Q₁ F
  hq : 8 ≤ Nat.card F
  hcrit : ¬ Uq M T L ≤ Qt M θ
  hII : IsLine (fixSp (C.rhoIm (Ut M T L θ)))
  Ψ : Multiplicative (V4 F × F) →* G
  hU : ∀ w, Ψ w ∈ Uq M T L
  hs : ∀ u ∈ Uq M T L, ∃ w, Ψ w = u
  hk : ∀ w, Ψ w = 1 → (Multiplicative.toAdd w).1 = 0
  he : ∀ (l : G) (hl : l ∈ L) w, Ψ (omega5Act F (C.α ⟨l, hl⟩) w) = l * Ψ w * l⁻¹
  hβ : ∀ w (hw : Ψ w ∈ Uq M T L), C.N.co ⟨Ψ w, hw⟩ = (Multiplicative.toAdd w).1

namespace Dat

variable {C : Cfg M T L F} (D : Dat C)

@[expose] noncomputable def u (x : Fin 2 → F) : G := D.Ψ (Multiplicative.ofAdd (fv x, 0))

theorem u_mem (x : Fin 2 → F) : D.u x ∈ Uq M T L := D.hU _

theorem u_mem_T1 (x : Fin 2 → F) : D.u x ∈ T1 M T L := C.Uq_le_T1 (D.u_mem x)

@[expose] noncomputable def z (y : Fin 2 → F) : G :=
  ((D.θ ⟨D.u y, D.u_mem_T1 y⟩ : ↥(T1 M T L)) : G)

theorem z_mem_T1 (y : Fin 2 → F) : D.z y ∈ T1 M T L := (D.θ ⟨D.u y, D.u_mem_T1 y⟩).2

theorem z_mem_Ut (y : Fin 2 → F) : D.z y ∈ Ut M T L D.θ :=
  mem_tImage.2 ⟨D.u y, D.u_mem_T1 y, D.u_mem y, rfl⟩

@[expose] noncomputable def zi (x : Fin 2 → F) : G :=
  ((D.θ⁻¹ ⟨D.u x, D.u_mem_T1 x⟩ : ↥(T1 M T L)) : G)

theorem zi_mem_T1 (x : Fin 2 → F) : D.zi x ∈ T1 M T L := (D.θ⁻¹ ⟨D.u x, D.u_mem_T1 x⟩).2

theorem co_u (x : Fin 2 → F) : C.N.co ⟨D.u x, D.u_mem x⟩ = fv x := D.hβ _ _

theorem conj_Ψ {t : G} (ht : t ∈ L ⊔ pCoreOf 2 M) (w : Multiplicative (V4 F × F)) :
    t * D.Ψ w * t⁻¹ = D.Ψ (omega5Act F (C.rho ⟨t, ht⟩) w) := by
  obtain ⟨l, hl, q, hq, rfl⟩ := C.exists_mul_of_mem_sup ht
  have hqu : q * D.Ψ w * q⁻¹ = D.Ψ w := by
    rw [comm_of_mem_Uq C.h (D.hU w) hq, mul_inv_cancel_right]
  rw [C.rho_mul hl hq, D.he l hl, show l * q * D.Ψ w * (l * q)⁻¹ = l * (q * D.Ψ w * q⁻¹) * l⁻¹
    by group, hqu]

variable [CharP F 2]

omit [CharP F 2] in
include D in
theorem rho_mem_Q₁ {t : G} (ht : t ∈ T1 M T L) : C.rho ⟨t, T1_le_sup ht⟩ ∈ Q₁ F := by
  rw [← D.hT]
  exact ⟨⟨t, ht⟩, rfl⟩

theorem comm_u {t : G} (ht : t ∈ T1 M T L) (x : Fin 2 → F) :
    ⁅t, D.u x⁆ = D.Ψ (iota (lc (S5.q1Coord (C.rho ⟨t, T1_le_sup ht⟩)) x)) := by
  have h := omega5_comm_Q₁ (D.rho_mem_Q₁ ht) x
  rw [commutatorElement_def, u, D.conj_Ψ (T1_le_sup ht), ← map_inv, ← map_mul, h]
  rfl

@[expose] noncomputable def Φ (y : Fin 2 → F) : F × F × F :=
  S5.q1Coord (C.rho ⟨D.z y, T1_le_sup (D.z_mem_T1 y)⟩)

@[expose] noncomputable def Φ' (x : Fin 2 → F) : F × F × F :=
  S5.q1Coord (C.rho ⟨D.zi x, T1_le_sup (D.zi_mem_T1 x)⟩)

theorem comm_z (x y : Fin 2 → F) : ⁅D.z y, D.u x⁆ = D.Ψ (iota (lc (D.Φ y) x)) :=
  D.comm_u (D.z_mem_T1 y) x

theorem comm_zi (x y : Fin 2 → F) : ⁅D.zi x, D.u y⁆ = D.Ψ (iota (lc (D.Φ' x) y)) :=
  D.comm_u (D.zi_mem_T1 x) y

omit [CharP F 2] in
theorem comm_zi_mem (x y : Fin 2 → F) : ⁅D.zi x, D.u y⁆ ∈ T1 M T L :=
  (T1 M T L).mul_mem ((T1 M T L).mul_mem ((T1 M T L).mul_mem
      (D.zi_mem_T1 x) (D.u_mem_T1 y)) ((T1 M T L).inv_mem (D.zi_mem_T1 x)))
      ((T1 M T L).inv_mem (D.u_mem_T1 y))

omit [CharP F 2] in
theorem θ_comm_zi (x y : Fin 2 → F) :
    ((D.θ ⟨⁅D.zi x, D.u y⁆, D.comm_zi_mem x y⟩ : ↥(T1 M T L)) : G) = ⁅D.u x, D.z y⁆ := by
  have e : (⟨⁅D.zi x, D.u y⁆, D.comm_zi_mem x y⟩ : ↥(T1 M T L)) =
      ⁅D.θ⁻¹ ⟨D.u x, D.u_mem_T1 x⟩, (⟨D.u y, D.u_mem_T1 y⟩ : ↥(T1 M T L))⁆ := rfl
  rw [e, map_commutatorElement, MulAut.apply_inv_self]
  rfl

omit [CharP F 2] in
theorem fixSp_E : fixSp (C.rhoIm (Ut M T L D.θ)) = ln₀ F :=
  fixSp_eq_ln₀_of_line C D.hT D.θ D.hII

omit [CharP F 2] in
theorem fixSp_E' : fixSp (C.rhoIm (Ut M T L D.θ⁻¹)) = ln₀ F :=
  fixSp_inv_eq_ln₀ C D.hT D.θ D.hcrit D.hII

omit [CharP F 2] in
theorem u_add (x x' : Fin 2 → F) : D.u (x + x') = D.u x * D.u x' := by
  rw [u, u, u, ← map_mul]
  congr 1
  apply Multiplicative.toAdd.injective
  simp [fv_add]

omit [CharP F 2] in
theorem u_zero : D.u 0 = 1 := by
  rw [u, ← map_one D.Ψ]
  congr 1
  apply Multiplicative.toAdd.injective
  simp [fv]

omit [CharP F 2] in
theorem z_add (y y' : Fin 2 → F) : D.z (y + y') = D.z y * D.z y' := by
  have e : (⟨D.u (y + y'), D.u_mem_T1 _⟩ : ↥(T1 M T L)) =
      ⟨D.u y, D.u_mem_T1 y⟩ * ⟨D.u y', D.u_mem_T1 y'⟩ := Subtype.ext (D.u_add y y')
  rw [z, z, z, e, map_mul]
  rfl

omit [CharP F 2] in
theorem z_zero : D.z 0 = 1 := by
  have e : (⟨D.u 0, D.u_mem_T1 0⟩ : ↥(T1 M T L)) = 1 := Subtype.ext D.u_zero
  rw [z, e, map_one]
  rfl

omit [CharP F 2] in
theorem rho_z_add (y y' : Fin 2 → F) :
    C.rho ⟨D.z (y + y'), T1_le_sup (D.z_mem_T1 _)⟩ =
      C.rho ⟨D.z y, T1_le_sup (D.z_mem_T1 y)⟩ * C.rho ⟨D.z y', T1_le_sup (D.z_mem_T1 y')⟩ := by
  rw [← map_mul]
  congr 1
  exact Subtype.ext (D.z_add y y')

omit [Fintype F] [CharP F 2] in
theorem q1Coord_mul {g h : Sp4 F} (hg : g ∈ Q₁ F) (hh : h ∈ Q₁ F) :
    S5.q1Coord (g * h) = S5.q1Coord g + S5.q1Coord h := by
  simp only [S5.q1Coord, entry_mul_of_mem_Q₁ hg hh, Prod.mk_add_mk]

omit [Fintype F] [CharP F 2] in
theorem q1Coord_one : S5.q1Coord (1 : Sp4 F) = 0 := by
  simp only [S5.q1Coord, entry_one]
  rfl

omit [CharP F 2] in
theorem Φ_add (y y' : Fin 2 → F) : D.Φ (y + y') = D.Φ y + D.Φ y' := by
  rw [Φ, Φ, Φ, D.rho_z_add,
    q1Coord_mul (D.rho_mem_Q₁ (D.z_mem_T1 y)) (D.rho_mem_Q₁ (D.z_mem_T1 y'))]

omit [CharP F 2] in
theorem Φ_zero : D.Φ 0 = 0 := by
  rw [Φ, show C.rho ⟨D.z 0, T1_le_sup (D.z_mem_T1 0)⟩ = 1 by
    rw [← map_one C.rho]; congr 1; exact Subtype.ext D.z_zero, q1Coord_one]

@[expose] noncomputable def ΦHom : (Fin 2 → F) →+ F × F × F where
  toFun := D.Φ
  map_zero' := D.Φ_zero
  map_add' := D.Φ_add

omit [CharP F 2] in
theorem ΦHom_apply (y : Fin 2 → F) : D.ΦHom y = D.Φ y := rfl

omit [Fintype F] [CharP F 2] in
theorem eq_zero_of_fv_mem {y : Fin 2 → F} (h : fv y ∈ ln₀ F) : y = 0 := by
  rw [mem_ln₀] at h
  funext i
  fin_cases i
  · exact h.1
  · exact h.2

omit [CharP F 2] in
theorem Φ_inj {y : Fin 2 → F} (h : D.Φ y = 0) : y = 0 := by
  have h1 : C.rho ⟨D.z y, T1_le_sup (D.z_mem_T1 y)⟩ = 1 := by
    refine S5.q1Coord_injOn (D.rho_mem_Q₁ (D.z_mem_T1 y)) (Subgroup.one_mem _) ?_
    rw [q1Coord_one]
    exact h
  have hQ := (C.rho_eq_one_iff _).1 h1
  have hmem : D.u y ∈ Qt M D.θ⁻¹ := by
    refine mem_tImage.2 ⟨D.z y, D.z_mem_T1 y, hQ, ?_⟩
    show ((D.θ⁻¹ (D.θ ⟨D.u y, D.u_mem_T1 y⟩) : ↥(T1 M T L)) : G) = D.u y
    simp
  have := (mem_Qt_iff C D.θ⁻¹ D.fixSp_E' (D.u_mem y)).1 hmem
  rw [D.co_u] at this
  exact eq_zero_of_fv_mem this

theorem Ψ_iota_lc_eq_one (t : F × F × F) (x : Fin 2 → F) :
    D.Ψ (iota (lc t x)) = 1 ↔ mv t x = 0 := by
  constructor
  · intro h
    have h1 := D.hk _ h
    funext i
    have := congrFun h1 (.inl i)
    simpa [iota, lc] using this
  · intro h
    have hq : qv t x = 0 := by rw [qv_eq_dot, h, dot_zero_right]
    have e : iota (lc t x) = 1 := by
      apply Multiplicative.toAdd.injective
      simp only [iota, lc, h, hq, toAdd_ofAdd, toAdd_one]
      refine Prod.ext ?_ rfl
      funext i
      rcases i with i | i <;> simp
    rw [e, map_one]

omit [Finite G] [Fintype F] [CharP F 2] in
theorem comm_eq_one_comm {a b : G} : ⁅a, b⁆ = 1 ↔ ⁅b, a⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_mul_comm, commutatorElement_eq_one_iff_mul_comm, eq_comm]

theorem kernel_symm (x y : Fin 2 → F) : mv (D.Φ y) x = 0 ↔ mv (D.Φ' x) y = 0 := by
  rw [← D.Ψ_iota_lc_eq_one, ← D.Ψ_iota_lc_eq_one, ← D.comm_z, ← D.comm_zi, comm_eq_one_comm,
    ← D.θ_comm_zi]
  constructor
  · intro h
    have h' : D.θ _ = 1 := Subtype.ext h
    rw [map_eq_one_iff _ D.θ.injective] at h'
    exact congrArg Subtype.val h'
  · intro h
    have h' : (⟨⁅D.zi x, D.u y⁆, D.comm_zi_mem x y⟩ : ↥(T1 M T L)) = 1 := Subtype.ext h
    rw [h', map_one]
    rfl

@[expose] noncomputable def E₃ : AddSubgroup (F × F × F) := D.ΦHom.range

omit [CharP F 2] in
theorem card_E₃ : Nat.card D.E₃ = Nat.card F ^ 2 := by
  have hinj : Function.Injective D.ΦHom := by
    rw [injective_iff_map_eq_zero]
    exact fun y h => D.Φ_inj h
  rw [E₃, ← Nat.card_congr (AddMonoidHom.ofInjective hinj).toEquiv, Nat.card_fun,
    Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]

theorem hker (x : Fin 2 → F) (hx : x ≠ 0) (h : ∃ t ∈ D.E₃, t ≠ 0 ∧ mv t x = 0) (c : F) :
    c • ktr x ∈ D.E₃ := by
  obtain ⟨t, ⟨y₀, rfl⟩, ht0, hmv⟩ := h
  have hy₀ : y₀ ≠ 0 := fun h => ht0 (by rw [h, map_zero])
  have hsym : ∀ c : F, mv (D.Φ (c • y₀)) x = 0 := fun c => by
    rw [D.kernel_symm, mv_smul_right, (D.kernel_symm x y₀).1 hmv, smul_zero]
  choose f hf using fun c => eq_smul_ktr hx (hsym c)
  have hfinj : Function.Injective f := fun c c' h => by
    have e : D.Φ (c • y₀) = D.Φ (c' • y₀) := by rw [hf, hf, h]
    have e2 : D.Φ (c • y₀ - c' • y₀) = 0 := by
      rw [← D.ΦHom_apply, map_sub, D.ΦHom_apply, D.ΦHom_apply, e, sub_self]
    have e3 := D.Φ_inj e2
    rw [← sub_smul] at e3
    exact sub_eq_zero.1 ((smul_eq_zero.1 e3).resolve_right hy₀)
  obtain ⟨c₀, hc₀⟩ := (Finite.injective_iff_surjective.1 hfinj) c
  exact ⟨c₀ • y₀, by rw [D.ΦHom_apply, hf, hc₀]⟩

theorem exists_good_x {a : Fin 2 → F} (ha : a ≠ 0) {c : F} (hc : c ≠ 0) :
    ∃ x, dot x a = c ∧ ∀ b, ∃ y, mv (D.Φ y) x = b := by
  have hq : 2 < Nat.card F := by have := D.hq; omega
  obtain ⟨x, hxa, hgood⟩ := exists_good hq (le_of_eq D.card_E₃) D.hker ha hc
  refine ⟨x, hxa, ?_⟩
  let g : (Fin 2 → F) →+ (Fin 2 → F) :=
    { toFun := fun y => mv (D.Φ y) x
      map_zero' := by rw [D.Φ_zero, mv_zero]
      map_add' := fun y y' => by rw [D.Φ_add, mv_add] }
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    exact D.Φ_inj (hgood _ ⟨y, rfl⟩ hy)
  exact Finite.injective_iff_surjective.1 hginj

theorem exists_good_pair : ∃ x₁ x₂ : Fin 2 → F, x₁ 0 * x₂ 1 - x₁ 1 * x₂ 0 ≠ 0 ∧
    (∀ b, ∃ y, mv (D.Φ y) x₁ = b) ∧ (∀ b, ∃ y, mv (D.Φ y) x₂ = b) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have ha : (![1, 0] : Fin 2 → F) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
  obtain ⟨x₁, hx₁, hg₁⟩ := D.exists_good_x ha one_ne_zero
  have hx₁0 : x₁ ≠ 0 := fun h => by rw [h] at hx₁; simp [dot] at hx₁
  have ha' : (![x₁ 1, x₁ 0] : Fin 2 → F) ≠ 0 := fun h => hx₁0 (by
    funext i
    fin_cases i
    · simpa using congrFun h 1
    · simpa using congrFun h 0)
  obtain ⟨x₂, hx₂, hg₂⟩ := D.exists_good_x ha' one_ne_zero
  refine ⟨x₁, x₂, ?_, hg₁, hg₂⟩
  have e : x₁ 0 * x₂ 1 - x₁ 1 * x₂ 0 = dot x₂ ![x₁ 1, x₁ 0] := by
    simp only [dot, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination -(x₁ 1 * x₂ 0) * h2
  rw [e, hx₂]
  exact one_ne_zero

end Dat

end CFSG.Quasithin.MS93.S37R
