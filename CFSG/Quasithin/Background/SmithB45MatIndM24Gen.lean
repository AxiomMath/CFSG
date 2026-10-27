module

public import CFSG.Quasithin.Background.SmithB45MatIndM23Gen

public section

namespace CFSG.Quasithin.B45Mat.Ind

open CFSG.QuasithinUnique.Setup.X3E CFSG.Quasithin.H.Mathieu CFSG.Quasithin.B45Mat.M22
  CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.H13.A5.M22Hat CFSG.Monster.Code Module

@[expose] noncomputable def m24g (z : Bool) : ↥AutPerm :=
  if z then ⟨bridgePB, bridgePB_mem⟩ else ⟨bridgePA, bridgePA_mem⟩

theorem hasArr_m24g (z : Bool) : HasArr (m24g z : Equiv.Perm (Fin 24)) (m24Gen z) := by
  have hA : ∀ i : Fin 24, bridgePAImage.toArray[(i : ℕ)]! = bridgePAImage.getD i 0 := by
    decide
  have hB : ∀ i : Fin 24, bridgePBImage.toArray[(i : ℕ)]! = bridgePBImage.getD i 0 := by
    decide
  cases z
  · exact fun i => (bridgePA_image i).trans (hA i).symm
  · exact fun i => (bridgePB_image i).trans (hB i).symm

theorem closure_m24g : Subgroup.closure (Set.range m24g) = ⊤ := by
  rw [range_bool]
  exact CFSG.Sporadic.Mathieu.closure_pair_eq_top AutPerm_eq_closure bridgePA_mem bridgePB_mem

@[expose] def m24W (k : ℕ) : List Bool := (m24CosC.map decW).getD k []

@[expose] noncomputable def m24t (k : ℕ) : ↥AutPerm := wordG (m24g false) (m24g true) (m24W k)

@[expose] def m24pi (z : Bool) (k : ℕ) : ℕ := (piArr m24Ts (m24Gen z) 0)[k]!

@[expose] def m24hArr (z : Bool) (k : ℕ) : Array ℕ :=
  (hArr m24Ts (m24Gen z) (piArr m24Ts (m24Gen z) 0))[k]!

@[expose] noncomputable def m24h (z : Bool) (k : ℕ) : ↥AutPerm :=
  (m24t (m24pi z k))⁻¹ * m24g z * m24t k

theorem m24_coset_rel (z : Bool) (k : ℕ) : m24g z * m24t k = m24t (m24pi z k) * m24h z k := by
  rw [m24h]
  group

theorem m24Ts_size : m24Ts.size = 24 := by decide

theorem m24Ts_getElem {k : ℕ} (hk : k < 24) :
    m24Ts[k]! = wordArr bridgePAImage.toArray bridgePBImage.toArray (m24W k) := by
  have hlen : (m24CosC.map decW).length = 24 := by decide
  have hlen' : m24CosC.length = 24 := by decide
  rw [m24Ts, cosArr, getElem!_pos _ k (by simpa [hlen'] using hk), List.getElem_toArray,
    List.getElem_map, m24W, List.getD_eq_getElem _ _ (by rw [hlen]; exact hk)]

theorem hasArr_m24t {k : ℕ} (hk : k < 24) :
    HasArr (m24t k : Equiv.Perm (Fin 24)) m24Ts[k]! := by
  have h1 := map_wordG AutPerm.subtype (m24g false) (m24g true) (m24W k)
  simp only [Subgroup.coe_subtype] at h1
  rw [m24Ts_getElem hk, m24t, h1]
  exact hasArr_wordArr (hasArr_m24g false) (hasArr_m24g true) _

theorem m24_cosetFacts (z : Bool) :
    CosetFacts m24Ts 24 0 (m24Gen z) := by
  have h := cosetFacts_of_cosetOK m24_ind_checks.1
  cases z
  · exact h.1
  · exact h.2

theorem m24pi_lt (z : Bool) {k : ℕ} (hk : k < 24) :
    m24pi z k < 24 :=
  (m24_cosetFacts z).pi_lt k hk

theorem m24t_point {k : ℕ} (hk : k < 24) :
    ((m24t k : Equiv.Perm (Fin 24)) 0 : ℕ) = (m24Ts[k]!)[0]! :=
  hasArr_m24t hk 0

theorem m24_pi_point (z : Bool) {k : ℕ} (hk : k < 24) :
    (m24g z : Equiv.Perm (Fin 24)) ((m24t k : Equiv.Perm (Fin 24)) 0) =
      (m24t (m24pi z k) : Equiv.Perm (Fin 24)) 0 := by
  apply Fin.ext
  rw [m24t_point (m24pi_lt z hk), m24pi, (m24_cosetFacts z).pi_point k hk,
    getElem!_comp24_of_lt _ _ (by decide), ← m24t_point hk]
  exact hasArr_m24g z _

theorem m24h_mem (z : Bool) {k : ℕ} (hk : k < 24) :
    (m24h z k : Equiv.Perm (Fin 24)) ∈ mog23 := by
  refine ⟨(m24h z k).2, (mem_stab_iff 0 _).2 ?_⟩
  have h1 := m24_pi_point z hk
  rw [m24h, Subgroup.coe_mul, Subgroup.coe_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1,
    Subgroup.coe_inv]
  simp

theorem hasArr_m24h (z : Bool) {k : ℕ} (hk : k < 24) :
    HasArr (m24h z k : Equiv.Perm (Fin 24)) (m24hArr z k) := by
  have hπ := m24pi_lt z hk
  have hsize : (Array.range m24Ts.size).size = 24 := by simp [m24Ts_size]
  rw [m24hArr, hArr, getElem!_pos _ k (by rw [Array.size_map, hsize]; exact hk),
    Array.getElem_map, Array.getElem_range]
  rw [m24h, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  refine hasArr_comp24 (hasArr_comp24 (hasArr_inv_of (hasArr_m24t hπ) ?_) (hasArr_m24g z))
    (hasArr_m24t hk)
  exact (m24_cosetFacts z).inv_ok _ hπ

theorem lin_m24Std_code (z : Bool) :
    lin 11 (m24Std 1 z) = Matrix.toLin' (mulAutMat 11 (rhoC11 AutPerm le_rfl (m24g z))) :=
  lin_matOf_eq fun m => rhoC11_toW AutPerm le_rfl (m24g z) (hasArr_m24g z) m

theorem lin_m24Std_cocode (z : Bool) :
    lin 11 (m24Std 2 z) = Matrix.toLin' (mulAutMat 11 (rho11 AutPerm le_rfl (m24g z))) :=
  lin_matOf_eq fun m => rho11_toW AutPerm le_rfl (m24g z) (hasArr_m24g z) m

theorem lin_m24Std_one (z : Bool) : lin 1 (m24Std 0 z) = LinearMap.id :=
  lin_eq_id fun j hj => by
    have : j = 0 := by omega
    subst this
    rfl

theorem irredPair_m24Std {t : ℕ} (ht : t < 6) :
    IrredPair fun z => lin (m24Dim t) (m24Std t z) := by
  have h : ∀ t, 0 < t → t < 6 → m24NorOK t = true →
      IrredPair fun z => lin (m24Dim t) (m24Std t z) := by
    intro t _ _ hn
    have h1 := irredPair_of_nortonFastOK hn
    convert h1 using 2 with z
    cases z <;> rfl
  obtain ⟨h1, h2, h3, h4, h5⟩ := m24_norton_checks
  interval_cases t
  · exact irredPair_one _
  · exact h 1 (by norm_num) (by norm_num) h1
  · exact h 2 (by norm_num) (by norm_num) h2
  · exact h 3 (by norm_num) (by norm_num) h3
  · exact h 4 (by norm_num) (by norm_num) h4
  · exact h 5 (by norm_num) (by norm_num) h5

theorem irredPair_of_irr24 {X : Type*} [AddCommGroup X]
    [Module (ZMod 2) X] (ρ : Representation (ZMod 2) ↥AutPerm X)
    (hirr : ∀ U : Submodule (ZMod 2) X, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤) :
    IrredPair fun z => ρ (m24g z) := by
  have : Finite ↥AutPerm := Subgroup.instFiniteSubtypeMem AutPerm
  intro U hU
  exact hirr U (isInvariant_of_gens ρ closure_m24g hU)

end CFSG.Quasithin.B45Mat.Ind
