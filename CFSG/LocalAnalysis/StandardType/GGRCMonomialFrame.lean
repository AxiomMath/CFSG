module

public import CFSG.LocalAnalysis.StandardType.GGRCMonomialRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nK43f_ext_basis {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {e₁ e₂ : V ≃ₗ[ZMod p] V} (h : ∀ k, e₁ (b k) = e₂ (b k)) : e₁ = e₂ := by
  apply LinearEquiv.ext
  intro v
  have h' : (e₁ : V →ₗ[ZMod p] V) = (e₂ : V →ₗ[ZMod p] V) := by
    apply Module.Basis.ext
    exact h
  exact congrArg (fun f : V →ₗ[ZMod p] V => f v) h'

private lemma l05nK43f_diagMap_apply {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (d : Fin n → (ZMod p)ˣ) (k : Fin n) :
    ZS.diagMap p b d (b k) = (d k : ZMod p) • b k := by
  apply b.equivFun.injective
  rw [map_smul]
  rw [ZS.diagMap, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  have hk : b.equivFun (b k) = Pi.single k 1 := by
    funext j
    rw [Module.Basis.equivFun_self, Pi.single_apply]
    by_cases h : k = j
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  rw [hk]
  funext j
  by_cases h : j = k
  · subst h; rfl
  · simp [Pi.single_apply, h]

private lemma l05nK43f_permMap_apply {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    ZS.permMap p b σ (b k) = b (σ k) := by
  simp only [ZS.permMap]
  exact Module.Basis.equiv_apply (b := b) k b σ

private lemma l05nK43f_permMap_mul {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (σ τ : Equiv.Perm (Fin n)) :
    ZS.permMap p b (σ * τ) = ZS.permMap p b σ * ZS.permMap p b τ := by
  rw [ZS.permMap, Equiv.Perm.mul_def, LinearEquiv.mul_eq_trans]
  exact (Module.Basis.equiv_trans b b b τ σ).symm

private lemma l05nK43f_permMap_one {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) :
    ZS.permMap p b (1 : Equiv.Perm (Fin n)) = 1 := by
  simp only [ZS.permMap, Equiv.Perm.one_def, Module.Basis.equiv_refl,
    LinearEquiv.one_eq_refl]

private lemma l05nK43f_permMap_refl {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) :
    ZS.permMap p b (Equiv.refl (Fin n)) = 1 := by
  rw [← Equiv.Perm.one_def, l05nK43f_permMap_one]

private noncomputable def l05nK43f_Tw {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j : Fin n)
    (u : (ZMod p)ˣ) : V ≃ₗ[ZMod p] V :=
  ZS.permMap p b (Equiv.swap i j) *
    ZS.diagMap p b (fun k => if k = i then u else if k = j then u⁻¹ else 1)

private lemma l05nK43f_Tw_apply {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j k : Fin n)
    (u : (ZMod p)ˣ) :
    l05nK43f_Tw b i j u (b k) =
      (if k = i then u else if k = j then u⁻¹ else 1) • b (Equiv.swap i j k) := by
  rw [l05nK43f_Tw, LinearEquiv.mul_apply, l05nK43f_diagMap_apply, map_smul,
    l05nK43f_permMap_apply]
  rw [Units.smul_def]

private lemma l05nK43f_Tw_symm {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n}
    (hij : i ≠ j) (u : (ZMod p)ˣ) :
    l05nK43f_Tw b j i u⁻¹ = l05nK43f_Tw b i j u := by
  apply l05nK43f_ext_basis (b := b)
  intro k
  rw [l05nK43f_Tw_apply, l05nK43f_Tw_apply]
  by_cases hk : k = i
  · subst k
    simp [hij]
  · by_cases hk' : k = j
    · subst k
      simp [hij, Ne.symm hij]
    · simp [Equiv.swap_comm, hk, hk']

private def l05nK43f_E {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (i j : Fin n) : Prop :=
  ∃ u : (ZMod p)ˣ, l05nK43f_Tw f i j u ∈ A

private lemma l05nK43f_E_symm {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)) {i j : Fin n} (hij : i ≠ j)
    (h : l05nK43f_E f A i j) : l05nK43f_E f A j i := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u⁻¹, by rw [l05nK43f_Tw_symm f hij u]; exact hu⟩

private def l05nK43f_Q {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (S : Finset (Fin n)) : Prop :=
  ∃ d : Fin n → (ZMod p)ˣ, ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
    ZS.permMap p (f.unitsSMul d) (Equiv.swap i j) ∈ A

private lemma l05nK43f_Q_singleton {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (i : Fin n) : l05nK43f_Q f A {i} := by
  refine ⟨1, ?_⟩
  intro a ha b hb hab
  rw [Finset.mem_singleton] at ha hb
  exact absurd (ha.trans hb.symm) hab

private lemma l05nK43f_permMap_unitsSMul_apply {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (d : Fin n → (ZMod p)ˣ) (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    ZS.permMap p (b.unitsSMul d) σ (b k) = ((d k)⁻¹ * d (σ k) : (ZMod p)ˣ) • b (σ k) := by
  have hfk : b k = ((d k)⁻¹ : (ZMod p)ˣ) • (b.unitsSMul d) k := by
    rw [Module.Basis.unitsSMul_apply, smul_smul, inv_mul_cancel, one_smul]
  rw [hfk, Units.smul_def, map_smul,
      show ZS.permMap p (b.unitsSMul d) σ ((b.unitsSMul d) k) = (b.unitsSMul d) (σ k) from
        Module.Basis.equiv_apply (b := b.unitsSMul d) k (b.unitsSMul d) σ,
      Module.Basis.unitsSMul_apply, Units.smul_def, smul_smul,
      Units.smul_def, Units.val_mul, Units.val_inv_eq_inv_val]

private lemma l05nK43f_permMap_unitsSMul_congr {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {d d' : Fin n → (ZMod p)ˣ} {σ : Equiv.Perm (Fin n)}
    (h : ∀ k, (d' k)⁻¹ * d' (σ k) = (d k)⁻¹ * d (σ k)) :
    ZS.permMap p (b.unitsSMul d') σ = ZS.permMap p (b.unitsSMul d) σ := by
  apply l05nK43f_ext_basis (b := b)
  intro k
  rw [l05nK43f_permMap_unitsSMul_apply, l05nK43f_permMap_unitsSMul_apply, h k]

private lemma l05nK43f_permMap_update_swap_eq {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) V)
    (d : Fin n → (ZMod p)ˣ) (z : (ZMod p)ˣ) {S : Finset (Fin n)} {w : Fin n} (i j : Fin n)
    (hi : i ∈ S) (hj : j ∈ S) (hw : w ∉ S) :
    ZS.permMap p (f.unitsSMul (Function.update d w z)) (Equiv.swap i j)
      = ZS.permMap p (f.unitsSMul d) (Equiv.swap i j) := by
  apply l05nK43f_permMap_unitsSMul_congr
  intro k
  by_cases hk : k = w
  · subst k
    have hwi : w ≠ i := fun h => hw (h ▸ hi)
    have hwj : w ≠ j := fun h => hw (h ▸ hj)
    rw [Equiv.swap_apply_of_ne_of_ne hwi hwj, Function.update_self]
    simp [inv_mul_cancel]
  · have hkw : Equiv.swap i j k ≠ w := by
      intro h
      have h' := congrArg (Equiv.swap i j) h
      rw [Equiv.swap_apply_self] at h'
      have hwi : w ≠ i := fun hh => hw (hh ▸ hi)
      have hwj : w ≠ j := fun hh => hw (hh ▸ hj)
      rw [Equiv.swap_apply_of_ne_of_ne hwi hwj] at h'
      exact hk h'
    rw [Function.update_of_ne hk, Function.update_of_ne hkw]

private lemma l05nK43f_permMap_update_swap_vw_eq_Tw {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) V)
    (d : Fin n → (ZMod p)ˣ) {v w : Fin n} (hvw : v ≠ w) (u : (ZMod p)ˣ) :
    ZS.permMap p (f.unitsSMul (Function.update d w (d v * u))) (Equiv.swap v w)
      = l05nK43f_Tw f v w u := by
  apply l05nK43f_ext_basis (b := f)
  intro k
  rw [l05nK43f_permMap_unitsSMul_apply, l05nK43f_Tw_apply]
  by_cases hk : k = v
  · subst k
    simp [hvw, Ne.symm hvw, inv_mul_cancel]
  · by_cases hk' : k = w
    · subst k
      simp [hvw, Ne.symm hvw, mul_inv_rev, inv_mul_cancel]
    · rw [Equiv.swap_apply_of_ne_of_ne hk hk']
      rw [Function.update_of_ne hk']
      rw [if_neg hk, if_neg hk']
      simp

private lemma l05nK43f_swap_mw_mem {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)) {S : Finset (Fin n)} {w m v : Fin n}
    (d' : Fin n → (ZMod p)ˣ) (hm : m ∈ S) (hw : w ∉ S)
    (hvw_mem : ZS.permMap p (f.unitsSMul d') (Equiv.swap v w) ∈ A)
    (hmv_mem : ZS.permMap p (f.unitsSMul d') (Equiv.swap m v) ∈ A) :
    ZS.permMap p (f.unitsSMul d') (Equiv.swap m w) ∈ A := by
  by_cases hmv : m = v
  · subst hmv; exact hvw_mem
  · have hmw : m ≠ w := fun h => hw (h ▸ hm)
    have hperm : ZS.permMap p (f.unitsSMul d') (Equiv.swap m w)
        = ZS.permMap p (f.unitsSMul d') (Equiv.swap v w * Equiv.swap m v * Equiv.swap v w) := by
      rw [Equiv.swap_mul_swap_mul_swap hmv hmw, Equiv.swap_comm]
    rw [hperm, l05nK43f_permMap_mul, l05nK43f_permMap_mul]
    exact A.mul_mem (A.mul_mem hvw_mem hmv_mem) hvw_mem

private lemma l05nK43f_Q_insert {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)) {S : Finset (Fin n)} {v w : Fin n}
    (hvw : v ≠ w) (hw : w ∉ S) (hv : v ∈ S)
    (hQ : l05nK43f_Q f A S) (hE : l05nK43f_E f A v w) :
    l05nK43f_Q f A (insert w S) := by
  classical
  obtain ⟨d, hd⟩ := hQ
  obtain ⟨u, hu⟩ := hE
  refine ⟨Function.update d w (d v * u), ?_⟩
  have hvw_mem : ZS.permMap p (f.unitsSMul (Function.update d w (d v * u)))
      (Equiv.swap v w) ∈ A := by
    rw [l05nK43f_permMap_update_swap_vw_eq_Tw f d hvw u]
    exact hu
  intro i hi j hj hij
  by_cases hiw : i = w
  · subst i
    have hjS : j ∈ S := by
      rcases Finset.mem_insert.mp hj with h | h
      · exact (hij h.symm).elim
      · exact h
    rw [Equiv.swap_comm]
    refine l05nK43f_swap_mw_mem f A (Function.update d w (d v * u)) hjS hw hvw_mem ?_
    by_cases hjv : j = v
    · subst j
      rw [Equiv.swap_self, l05nK43f_permMap_refl]
      exact A.one_mem
    · rw [l05nK43f_permMap_update_swap_eq f d (d v * u) j v hjS hv hw]
      exact hd j hjS v hv hjv
  · by_cases hjw : j = w
    · subst j
      have hiS : i ∈ S := by
        rcases Finset.mem_insert.mp hi with h | h
        · exact (hiw h).elim
        · exact h
      refine l05nK43f_swap_mw_mem f A (Function.update d w (d v * u)) hiS hw hvw_mem ?_
      by_cases hiv : i = v
      · subst i
        rw [Equiv.swap_self, l05nK43f_permMap_refl]
        exact A.one_mem
      · rw [l05nK43f_permMap_update_swap_eq f d (d v * u) i v hiS hv hw]
        exact hd i hiS v hv hiv
    · have hiS : i ∈ S := by
        rcases Finset.mem_insert.mp hi with h | h
        · exact (hiw h).elim
        · exact h
      have hjS : j ∈ S := by
        rcases Finset.mem_insert.mp hj with h | h
        · exact (hjw h).elim
        · exact h
      rw [l05nK43f_permMap_update_swap_eq f d (d v * u) i j hiS hjS hw]
      exact hd i hiS j hjS hij

private lemma l05nK43f_graph_connected {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (hirr : ZS.AbsIrred p A)
    (hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r})
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a (f i) = c i • f (σ i))
    (S : Set (Fin n))
    (hclosed : ∀ i j, i ∈ S → l05nK43f_E f A i j → j ∈ S)
    (hne : S.Nonempty) :
    S = Set.univ := by
  classical
  let W : Submodule (ZMod p) V := Submodule.span (ZMod p) (f '' S)
  have hsq_of_mul : ∀ (e : V ≃ₗ[ZMod p] V), e * e = 1 → ∀ v, e (e v) = v := by
    intro e he v
    have h := congrArg (fun g : V ≃ₗ[ZMod p] V => g v) he
    rw [LinearEquiv.mul_apply] at h
    simpa using h
  have hPres : ∀ r ∈ A, GGLinRefl r → W.map (r : V →ₗ[ZMod p] V) = W := by
    intro r hrA hrRefl
    obtain ⟨σ, c, hc, hrb⟩ := hmon r hrA
    rcases ggRC_monomial_refl_shape hp2 f r hrRefl σ c hc hrb with
      ⟨i, hσ, hci, hcj⟩ | ⟨i, j, hij, hσ, hcij, hck⟩
    · have hrb' : ∀ k, r (f k) = (if k = i then (-1 : ZMod p) else 1) • f k := by
        intro k
        rw [hrb k, hσ, Equiv.Perm.one_apply]
        by_cases hk : k = i
        · subst k
          rw [if_pos rfl, hci]
        · rw [if_neg hk, hcj k hk]
      have hsub : W.map (r : V →ₗ[ZMod p] V) ≤ W := by
        rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
        rintro x ⟨k, hkS, rfl⟩
        change r (f k) ∈ W
        rw [hrb' k]
        exact W.smul_mem _ (Submodule.subset_span ⟨k, hkS, rfl⟩)
      refine le_antisymm hsub ?_
      intro w hw
      refine Submodule.mem_map.mpr
        ⟨r w, hsub (Submodule.mem_map_of_mem hw), hsq_of_mul r hrRefl.1 w⟩
    · let u : (ZMod p)ˣ := Units.mk0 (c i) (hc i)
      have hcinv : c j = (c i)⁻¹ := (inv_eq_of_mul_eq_one_right hcij).symm
      have hrTw : r = l05nK43f_Tw f i j u := by
        apply l05nK43f_ext_basis (b := f)
        intro k
        rw [hrb k, hσ, l05nK43f_Tw_apply]
        by_cases hk : k = i
        · subst k
          simp [u, Units.smul_def, Units.val_mk0]
        · by_cases hk' : k = j
          · subst k
            simp [u, Units.smul_def, hcinv, Units.val_mk0, Units.val_inv_eq_inv_val, Ne.symm hij]
          · rw [Equiv.swap_apply_of_ne_of_ne hk hk', if_neg hk, if_neg hk',
              hck k hk hk']
            simp
      have hE : l05nK43f_E f A i j := ⟨u, by rw [← hrTw]; exact hrA⟩
      have hsub : W.map (r : V →ₗ[ZMod p] V) ≤ W := by
        rw [hrTw]
        rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
        rintro x ⟨k, hkS, rfl⟩
        change l05nK43f_Tw f i j u (f k) ∈ W
        rw [l05nK43f_Tw_apply]
        refine W.smul_mem _ ?_
        by_cases hk : k = i
        · subst k
          rw [Equiv.swap_apply_left]
          exact Submodule.subset_span ⟨j, hclosed i j hkS hE, rfl⟩
        · by_cases hk' : k = j
          · subst k
            rw [Equiv.swap_apply_right]
            exact Submodule.subset_span
              ⟨i, hclosed j i hkS (l05nK43f_E_symm f A hij hE), rfl⟩
          · rw [Equiv.swap_apply_of_ne_of_ne hk hk']
            exact Submodule.subset_span ⟨k, hkS, rfl⟩
      refine le_antisymm hsub ?_
      intro w hw
      refine Submodule.mem_map.mpr
        ⟨r w, hsub (Submodule.mem_map_of_mem hw), hsq_of_mul r hrRefl.1 w⟩
  have hA : ∀ a ∈ A, W.map (a : V →ₗ[ZMod p] V) = W := by
    let H : Subgroup (V ≃ₗ[ZMod p] V) :=
      { carrier := {a | W.map (a : V →ₗ[ZMod p] V) = W}
        one_mem' := by
          show W.map ((1 : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) = W
          rw [LinearEquiv.coe_toLinearMap_one, Submodule.map_id]
        mul_mem' := by
          intro x y hx hy
          show W.map ((x * y : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) = W
          rw [LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp, Submodule.map_comp, hy, hx]
        inv_mem' := by
          intro x hx
          show W.map ((x⁻¹ : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) = W
          have hcomp : (W.map (x : V →ₗ[ZMod p] V)).map
                ((x⁻¹ : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) =
              W.map (((x⁻¹ : V ≃ₗ[ZMod p] V) * x : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) := by
            rw [LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp, Submodule.map_comp]
          rw [hx, inv_mul_cancel, LinearEquiv.coe_toLinearMap_one, Submodule.map_id] at hcomp
          exact hcomp }
    have hle : Subgroup.closure {r | r ∈ A ∧ GGLinRefl r} ≤ H := by
      rw [Subgroup.closure_le]
      rintro r ⟨hrA, hrRefl⟩
      exact hPres r hrA hrRefl
    intro a ha
    exact hle (by rwa [← hgen])
  have hW : W = ⊥ ∨ W = ⊤ :=
    hirr.1 W fun a ha w hw => by
      have := hA a ha
      exact this ▸ Submodule.mem_map_of_mem hw
  have hWtop : W = ⊤ := by
    rcases hW with hbot | htop
    · exfalso
      obtain ⟨i, hiS⟩ := hne
      have : f i ∈ W := Submodule.subset_span ⟨i, hiS, rfl⟩
      rw [hbot] at this
      exact f.ne_zero i (by simpa using this)
    · exact htop
  ext j
  constructor
  · intro _; exact Set.mem_univ j
  · intro _
    by_contra hj
    have hmem : f j ∈ W := by rw [hWtop]; exact Submodule.mem_top
    have hspan : f j ∈ Submodule.span (ZMod p) (f '' S) := hmem
    exact hj ((Module.Basis.self_mem_span_image f).mp hspan)

private lemma l05nK43f_Q_univ {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (hirr : ZS.AbsIrred p A)
    (hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r})
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a (f i) = c i • f (σ i))
    (hn : 0 < n) : l05nK43f_Q f A Finset.univ := by
  classical
  let i₀ : Fin n := ⟨0, hn⟩
  have hbase : l05nK43f_Q f A {i₀} := l05nK43f_Q_singleton f A i₀
  obtain ⟨S, hSmem, hSmax⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun T => l05nK43f_Q f A T)) Finset.card
    ⟨{i₀}, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbase⟩⟩
  have hQS : l05nK43f_Q f A S := (Finset.mem_filter.mp hSmem).2
  have hcard1 : 1 ≤ S.card := by
    have h := hSmax {i₀} (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbase⟩)
    simpa using h
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hclosed : ∀ i j, i ∈ (↑S : Set (Fin n)) → l05nK43f_E f A i j →
      j ∈ (↑S : Set (Fin n)) := by
    intro i j hiS hEij
    by_contra hjS
    have hiS' : i ∈ S := Finset.mem_coe.mp hiS
    have hjS' : j ∉ S := fun h => hjS (Finset.mem_coe.mpr h)
    have hij : i ≠ j := fun h => hjS (h ▸ hiS)
    have hQins : l05nK43f_Q f A (insert j S) :=
      l05nK43f_Q_insert f A hij hjS' hiS' hQS hEij
    have hmem : insert j S ∈ Finset.univ.filter (fun T => l05nK43f_Q f A T) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQins⟩
    have hle := hSmax (insert j S) hmem
    have hcard' : (insert j S).card = S.card + 1 := Finset.card_insert_of_notMem hjS'
    omega
  have hSne' : (↑S : Set (Fin n)).Nonempty := by
    obtain ⟨i, hi⟩ := hSne
    exact ⟨i, Finset.mem_coe.mpr hi⟩
  have huniv := l05nK43f_graph_connected hp2 f A hirr hgen hmon (↑S) hclosed hSne'
  have hSuniv : S = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro j
    have hj : j ∈ (↑S : Set (Fin n)) := by rw [huniv]; exact Set.mem_univ j
    exact Finset.mem_coe.mp hj
  rwa [hSuniv] at hQS

private lemma l05nK43f_perms_mem {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (hQ : l05nK43f_Q f A Finset.univ) :
    ∃ d : Fin n → (ZMod p)ˣ, ∀ σ : Equiv.Perm (Fin n),
      ZS.permMap p (f.unitsSMul d) σ ∈ A := by
  obtain ⟨d, hd⟩ := hQ
  refine ⟨d, ?_⟩
  have hswap : ∀ i j : Fin n, i ≠ j →
      ZS.permMap p (f.unitsSMul d) (Equiv.swap i j) ∈ A :=
    fun i j hij => hd i (Finset.mem_univ i) j (Finset.mem_univ j) hij
  intro σ
  refine Equiv.Perm.swap_induction_on
    (motive := fun σ => ZS.permMap p (f.unitsSMul d) σ ∈ A) σ ?_ ?_
  · rw [l05nK43f_permMap_one]
    exact A.one_mem
  · intro τ x y hxy hτ
    rw [l05nK43f_permMap_mul]
    exact A.mul_mem (hswap x y hxy) hτ

private lemma l05nK43f_monomial_unitsSMul {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a (f i) = c i • f (σ i))
    (d : Fin n → (ZMod p)ˣ) :
    ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a ((f.unitsSMul d) i) = c i • (f.unitsSMul d) (σ i) := by
  intro a ha
  obtain ⟨σ, c, hc, hc'⟩ := hmon a ha
  let cu : Fin n → (ZMod p)ˣ := fun i => d i * Units.mk0 (c i) (hc i) * (d (σ i))⁻¹
  refine ⟨σ, fun i => (cu i : ZMod p), fun i => Units.ne_zero (cu i), ?_⟩
  intro i
  have hcoef : (cu i : ZMod p) * (d (σ i) : ZMod p) = (d i : ZMod p) * c i := by
    simp only [cu, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val]
    rw [mul_assoc, inv_mul_cancel₀ (Units.ne_zero (d (σ i))), mul_one]
  simp only [Module.Basis.unitsSMul_apply, Units.smul_def, map_smul, hc' i, smul_smul, hcoef]

theorem ggRC_monomial_frame {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (hirr : ZS.AbsIrred p A)
    (hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r})
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a (f i) = c i • f (σ i)) :
    ∃ b : Module.Basis (Fin n) (ZMod p) V,
      (∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
        (∀ i, c i ≠ 0) ∧ ∀ i, a (b i) = c i • b (σ i)) ∧
      (∀ σ : Equiv.Perm (Fin n), ZS.permMap p b σ ∈ A) ∧
      ∃ d : Fin n → (ZMod p)ˣ, b = f.unitsSMul d := by
  classical
  by_cases hn : n = 0
  · subst hn
    refine ⟨f, hmon, ?_, 1, Module.Basis.eq_of_apply_eq fun i => i.elim0⟩
    intro σ
    have hσ : σ = 1 := by
      ext i
      exact i.elim0
    subst hσ
    rw [l05nK43f_permMap_one]
    exact A.one_mem
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨d, hd⟩ := l05nK43f_perms_mem f A
      (l05nK43f_Q_univ hp2 f A hirr hgen hmon hnpos)
    exact ⟨f.unitsSMul d, l05nK43f_monomial_unitsSMul f A hmon d, hd, d, rfl⟩

end CFSG.StandardType
