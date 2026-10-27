module

public import CFSG.Quasithin.Background.SmithB45MatIndM22
public import CFSG.Quasithin.Background.SmithB45MatIndArr
public import CFSG.Quasithin.Background.SmithB45MatIndCheck
public import CFSG.Quasithin.Background.SmithB45MatIndFrob

public section

namespace CFSG.Quasithin.B45Mat.Ind

open CFSG.QuasithinUnique.Setup.X3E CFSG.Quasithin.H.Mathieu CFSG.Quasithin.B45Mat.M22
  CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.H13.A5.M22Hat CFSG.Blueprint Module

abbrev m23pA : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
    List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
    List.formPerm [20, 21]

abbrev m23pB : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
    List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]

theorem psi23A_mem : psi23 m23pA ∈ mog23 :=
  ⟨mem_autPerm_of_hasArr psi23_a_arr m23_arrs_ok.1, (mem_stab_iff 0 _).2 rfl⟩

theorem psi23B_mem : psi23 m23pB ∈ mog23 :=
  ⟨mem_autPerm_of_hasArr psi23_b_arr m23_arrs_ok.2, (mem_stab_iff 0 _).2 rfl⟩

@[expose] noncomputable def m23g (z : Bool) : ↥mog23 :=
  if z then ⟨psi23 m23pB, psi23B_mem⟩ else ⟨psi23 m23pA, psi23A_mem⟩

theorem hasArr_m23g (z : Bool) :
    HasArr (m23g z : Equiv.Perm (Fin 24)) (m23Gen z) := by
  cases z
  · exact psi23_a_arr
  · exact psi23_b_arr

theorem range_bool {α : Type*} (f : Bool → α) : Set.range f = {f false, f true} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    cases z
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩

theorem closure_m23g :
    Subgroup.closure (Set.range m23g) = ⊤ := by
  have hK : mog23 = Subgroup.closure {psi23 m23pA, psi23 m23pB} := by
    rw [← map_psi23_M23, NativeSporadic.M23, MonoidHom.map_closure, Set.image_pair]
  rw [range_bool]
  exact CFSG.Sporadic.Mathieu.closure_pair_eq_top hK psi23A_mem psi23B_mem

@[expose] def m23W (k : ℕ) : List Bool := (m23CosC.map decW).getD k []

@[expose] noncomputable def m23t (k : ℕ) : ↥mog23 :=
  wordG (m23g false) (m23g true) (m23W k)

@[expose] def m23pi (z : Bool) (k : ℕ) : ℕ := (piArr m23Ts (m23Gen z) 1)[k]!

@[expose] def m23hArr (z : Bool) (k : ℕ) : Array ℕ :=
  (hArr m23Ts (m23Gen z) (piArr m23Ts (m23Gen z) 1))[k]!

@[expose] noncomputable def m23h (z : Bool) (k : ℕ) : ↥mog23 :=
  (m23t (m23pi z k))⁻¹ * m23g z * m23t k

theorem m23_coset_rel (z : Bool) (k : ℕ) :
    m23g z * m23t k = m23t (m23pi z k) * m23h z k := by
  rw [m23h]
  group

theorem m23Ts_size : m23Ts.size = 23 := by decide

theorem m23Ts_getElem {k : ℕ} (hk : k < 23) :
    m23Ts[k]! = wordArr m23AArr m23BArr (m23W k) := by
  have hlen : (m23CosC.map decW).length = 23 := by decide
  have hlen' : m23CosC.length = 23 := by decide
  rw [m23Ts, cosArr, getElem!_pos _ k (by simpa [hlen'] using hk), List.getElem_toArray,
    List.getElem_map, m23W, List.getD_eq_getElem _ _ (by rw [hlen]; exact hk)]

theorem hasArr_m23t {k : ℕ} (hk : k < 23) :
    HasArr (m23t k : Equiv.Perm (Fin 24)) m23Ts[k]! := by
  have h1 := map_wordG mog23.subtype (m23g false) (m23g true) (m23W k)
  simp only [Subgroup.coe_subtype] at h1
  rw [m23Ts_getElem hk, m23t, h1]
  exact hasArr_wordArr (hasArr_m23g false) (hasArr_m23g true) _

theorem m23_cosetFacts :
    CosetFacts m23Ts 23 1 (m23Gen false) ∧ CosetFacts m23Ts 23 1 (m23Gen true) :=
  cosetFacts_of_cosetOK m23_ind_checks.1

theorem m23_cosetFacts' (z : Bool) :
    CosetFacts m23Ts 23 1 (m23Gen z) := by
  cases z
  · exact m23_cosetFacts.1
  · exact m23_cosetFacts.2

theorem m23pi_lt (z : Bool) {k : ℕ} (hk : k < 23) :
    m23pi z k < 23 :=
  (m23_cosetFacts' z).pi_lt k hk

theorem m23t_point {k : ℕ} (hk : k < 23) :
    ((m23t k : Equiv.Perm (Fin 24)) 1 : ℕ) = (m23Ts[k]!)[1]! :=
  hasArr_m23t hk 1

theorem m23_pi_point (z : Bool)
    {k : ℕ} (hk : k < 23) :
    (m23g z : Equiv.Perm (Fin 24)) ((m23t k : Equiv.Perm (Fin 24)) 1) =
      (m23t (m23pi z k) : Equiv.Perm (Fin 24)) 1 := by
  apply Fin.ext
  rw [m23t_point (m23pi_lt z hk), m23pi, (m23_cosetFacts' z).pi_point k hk,
    getElem!_comp24_of_lt _ _ (by decide), ← m23t_point hk]
  exact hasArr_m23g z _

theorem m23pi_inj (z : Bool) :
    ∀ k < 23, ∀ k' < 23, m23pi z k = m23pi z k' → k = k' := by
  intro k hk k' hk' h
  have h1 := m23_pi_point z hk
  rw [h, ← m23_pi_point z hk'] at h1
  have h2 := (m23g z : Equiv.Perm (Fin 24)).injective h1
  refine (m23_cosetFacts' z).point_inj k hk k' hk' ?_
  rw [← m23t_point hk, ← m23t_point hk', h2]

theorem m23h_mem (z : Bool)
    {k : ℕ} (hk : k < 23) : (m23h z k : Equiv.Perm (Fin 24)) ∈ mog22 := by
  refine ⟨(m23h z k).2, (mem_stab_iff 1 _).2 ?_⟩
  have h1 := m23_pi_point z hk
  rw [m23h, Subgroup.coe_mul, Subgroup.coe_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1,
    Subgroup.coe_inv]
  simp

theorem hasArr_m23h (z : Bool)
    {k : ℕ} (hk : k < 23) : HasArr (m23h z k : Equiv.Perm (Fin 24)) (m23hArr z k) := by
  have hπ := m23pi_lt z hk
  have hsize : (Array.range m23Ts.size).size = 23 := by simp [m23Ts_size]
  rw [m23hArr, hArr, getElem!_pos _ k (by rw [Array.size_map, hsize]; exact hk),
    Array.getElem_map, Array.getElem_range]
  rw [m23h, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  refine hasArr_comp24 (hasArr_comp24 (hasArr_inv_of (hasArr_m23t hπ) ?_) (hasArr_m23g z))
    (hasArr_m23t hk)
  exact (m23_cosetFacts' z).inv_ok _ hπ

theorem lin_m23Std_code (z : Bool) :
    lin 11 (m23Std 1 z) = Matrix.toLin' (mulAutMat 11 (rhoC11 mog23 inf_le_left (m23g z))) :=
  lin_matOf_eq fun m => rhoC11_toW mog23 inf_le_left (m23g z) (hasArr_m23g z) m

theorem lin_m23Std_cocode (z : Bool) :
    lin 11 (m23Std 2 z) = Matrix.toLin' (mulAutMat 11 (rho11 mog23 inf_le_left (m23g z))) :=
  lin_matOf_eq fun m => rho11_toW mog23 inf_le_left (m23g z) (hasArr_m23g z) m

theorem lin_m23Std_one (z : Bool) : lin 1 (m23Std 0 z) = LinearMap.id :=
  lin_eq_id fun j hj => by
    have : j = 0 := by omega
    subst this
    rfl

theorem irredPair_m23Std {t : ℕ} (ht : t < 6) :
    IrredPair fun z => lin (m23Dim t) (m23Std t z) := by
  have h : ∀ t, 0 < t → t < 6 → m23NorOK t = true →
      IrredPair fun z => lin (m23Dim t) (m23Std t z) := by
    intro t _ _ hn
    have h1 := irredPair_of_nortonFastOK hn
    convert h1 using 2 with z
    cases z <;> rfl
  obtain ⟨h1, h2, h3, h4, h5⟩ := m23_norton_checks
  interval_cases t
  · exact irredPair_one _
  · exact h 1 (by norm_num) (by norm_num) h1
  · exact h 2 (by norm_num) (by norm_num) h2
  · exact h 3 (by norm_num) (by norm_num) h3
  · exact h 4 (by norm_num) (by norm_num) h4
  · exact h 5 (by norm_num) (by norm_num) h5

theorem irredPair_of_irr
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) ↥mog23 X)
    (hirr : ∀ U : Submodule (ZMod 2) X, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤) :
    IrredPair fun z => ρ (m23g z) := by
  have : Finite ↥mog23 := Subgroup.instFiniteSubtypeMem mog23
  intro U hU
  exact hirr U (isInvariant_of_gens ρ closure_m23g hU)

end CFSG.Quasithin.B45Mat.Ind
