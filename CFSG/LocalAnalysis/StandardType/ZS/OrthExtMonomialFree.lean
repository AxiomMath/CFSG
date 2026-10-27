module

public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtBadRefl
public import CFSG.LocalAnalysis.StandardType.ZS.Monomial

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  {G H B : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}

private theorem orbit_eq_of_fixedPointFree {σ : Equiv.Perm (Fin 3)} (hσ : ∀ l, σ l ≠ l)
    (m k : Fin 3) : k = m ∨ k = σ.symm m ∨ k = σ.symm (σ.symm m) := by
  revert σ m k
  decide

private theorem exists_perm_pair_of_fixedPointFree {σ : Equiv.Perm (Fin 3)} (hσ : ∀ l, σ l ≠ l)
    {m k : Fin 3} (hmk : m ≠ k) :
    ∃ j : Fin 3, (σ^[j] 0 = m ∧ σ^[j] 1 = k) ∨ (σ^[j] 0 = k ∧ σ^[j] 1 = m) := by
  revert σ m k
  decide

omit [Fact p.Prime] in
private theorem beta_const_of_fixedPointFree {β : Fin 3 → Fin 3 → ZMod p}
    {σ : Equiv.Perm (Fin 3)} (hσ : ∀ l, σ l ≠ l)
    (hβ : ∀ m k, β (σ m) (σ k) = β m k)
    (hsymm : ∀ m k, β m k = β k m) :
    ∀ m k, m ≠ k → β m k = β 0 1 := by
  have hbase : ∀ j : Fin 3, β (σ^[j] 0) (σ^[j] 1) = β 0 1 := by
    intro j
    fin_cases j
    · simp
    · simpa using hβ 0 1
    · have h1 : β (σ (σ 0)) (σ (σ 1)) = β (σ 0) (σ 1) := hβ (σ 0) (σ 1)
      have h2 : β (σ 0) (σ 1) = β 0 1 := hβ 0 1
      simpa [Function.iterate_succ] using h1.trans h2
  intro m k hmk
  obtain ⟨j, ⟨h0, h1⟩ | ⟨h0, h1⟩⟩ := exists_perm_pair_of_fixedPointFree hσ hmk
  · rw [← h0, ← h1]; exact hbase j
  · rw [← h0, ← h1, hsymm]; exact hbase j

private theorem exists_mem_fixed_and_coord_recurrence [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h)
    (hVB : HardMathSupport.Kantor79.commutatorSpace B =
      LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {x : U ≃ₗ[ZMod p] U} (hx : x ∈ H)
    {d : Fin 3 → (ZMod p)ˣ} {σ : Equiv.Perm (Fin 3)}
    (hxd : MonomialAction f x d σ) :
    ∃ (y : U) (_hyH : y ∈ centralizerSpace H)
      (hyB : y ∈ HardMathSupport.Kantor79.commutatorSpace B),
      y ≠ 0 ∧ ∀ m, f.repr ⟨y, hyB⟩ m =
        (d m : ZMod p) * f.repr ⟨y, hyB⟩ (σ.symm m) := by
  have hn : Module.finrank (ZMod p) U - 1 < Module.finrank (ZMod p) U := by
    have := hD.setting.four_le
    omega
  obtain ⟨y, hyH, hy0⟩ := hD.setting.sub.2.1.exists_mem_centralizerSpace_ne_zero hn
  have hyB : y ∈ HardMathSupport.Kantor79.commutatorSpace B := by
    rw [hVB]
    exact LinearMap.mem_ker.mpr (by
      have hfix := (mem_centralizerSpace.mp hyH) h hD.mem
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      exact hfix)
  refine ⟨y, hyH, hyB, hy0, ?_⟩
  intro m
  have hxmem : x y ∈ HardMathSupport.Kantor79.commutatorSpace B := by
    rw [hxd ⟨y, hyB⟩]
    exact ((diagMap p f d * permMap p f σ) ⟨y, hyB⟩).2
  have hxy : (⟨x y, hxmem⟩ : HardMathSupport.Kantor79.commutatorSpace B) = ⟨y, hyB⟩ := by
    ext
    change x y = y
    exact (mem_centralizerSpace.mp hyH) x hx
  have hxy' : (⟨x y, hxmem⟩ : HardMathSupport.Kantor79.commutatorSpace B) =
      (diagMap p f d * permMap p f σ) ⟨y, hyB⟩ := by
    ext
    exact hxd ⟨y, hyB⟩
  have hcoord : f.repr (⟨x y, hxmem⟩ : HardMathSupport.Kantor79.commutatorSpace B) m =
      (d m : ZMod p) * f.repr ⟨y, hyB⟩ (σ.symm m) := by
    rw [hxy']
    exact repr_diagMap_mul_permMap f d σ ⟨y, hyB⟩ m
  have h1 : f.repr ⟨y, hyB⟩ m =
      f.repr (⟨x y, hxmem⟩ : HardMathSupport.Kantor79.commutatorSpace B) m := by
    rw [hxy]
  rw [h1, hcoord]

private theorem exists_coord_ne_zero
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {y : U} (hy0 : y ≠ 0)
    (hyB : y ∈ HardMathSupport.Kantor79.commutatorSpace B) :
    ∃ m, f.repr ⟨y, hyB⟩ m ≠ 0 := by
  by_contra! h
  apply hy0
  have hsum : y = ∑ m, f.repr ⟨y, hyB⟩ m • (f m : U) := by
    have h' := f.sum_repr ⟨y, hyB⟩
    exact (congrArg Subtype.val h').symm
  rw [hsum]
  simp [h]

private theorem coord_ne_zero {c : Fin 3 → ZMod p} {d : Fin 3 → (ZMod p)ˣ}
    {σ : Equiv.Perm (Fin 3)} (hσ : ∀ l, σ l ≠ l)
    (hrec : ∀ m, c m = (d m : ZMod p) * c (σ.symm m))
    (h : ∃ m, c m ≠ 0) : ∀ m, c m ≠ 0 := by
  obtain ⟨m0, hm0⟩ := h
  intro m hm
  have hsymm : c (σ.symm m) = 0 := by
    have h := hrec m
    rw [hm] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (Units.ne_zero (d m))
  have h0 : ∀ k, c k = 0 := by
    intro k
    rcases orbit_eq_of_fixedPointFree hσ m k with hk | hk | hk
    · rw [hk]; exact hm
    · rw [hk]; exact hsymm
    · rw [hk]
      have h := hrec (σ.symm m)
      rw [hsymm] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (Units.ne_zero (d (σ.symm m)))
  exact hm0 (h0 m0)

private theorem apply_eq_of_coord_recurrence
    {b : Fin 3 → U} {c : Fin 3 → ZMod p}
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    (hb_def : ∀ m, b m = c m • (f m : U))
    {x : U ≃ₗ[ZMod p] U}
    {d : Fin 3 → (ZMod p)ˣ} {σ : Equiv.Perm (Fin 3)}
    (hxd : MonomialAction f x d σ)
    (hc_rec : ∀ m, c m = (d m : ZMod p) * c (σ.symm m)) :
    ∀ m, x (b m) = b (σ m) := by
  intro m
  have hx_f : x (f m : U) = ((diagMap p f d * permMap p f σ) (f m) : U) := hxd (f m)
  have hmono : ((diagMap p f d * permMap p f σ) (f m) : U) =
      (d (σ m) : ZMod p) • (f (σ m) : U) := by
    rw [LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis]
    simp
  rw [hb_def m]
  calc x (c m • (f m : U)) = c m • x (f m : U) := by rw [map_smul]
    _ = c m • ((diagMap p f d * permMap p f σ) (f m) : U) := by rw [hx_f]
    _ = c m • ((d (σ m) : ZMod p) • (f (σ m) : U)) := by rw [hmono]
    _ = (c m * (d (σ m) : ZMod p)) • (f (σ m) : U) := by rw [smul_smul]
    _ = ((d (σ m) : ZMod p) * c m) • (f (σ m) : U) := by rw [mul_comm]
    _ = c (σ m) • (f (σ m) : U) := by
      have h := (hc_rec (σ m)).symm
      rw [Equiv.symm_apply_apply] at h
      rw [h]
    _ = b (σ m) := by rw [hb_def (σ m)]

private theorem quadratic_and_polar_const
    {Q : QuadraticForm (ZMod p) U} {b : Fin 3 → U} {σ : Equiv.Perm (Fin 3)}
    {x : U ≃ₗ[ZMod p] U} (hσ : ∀ l, σ l ≠ l)
    (hxb : ∀ m, x (b m) = b (σ m)) (hIso : IsIsom p Q x) :
    (∀ m, Q (b m) = Q (b 0)) ∧
      (∀ m k, m ≠ k → QuadraticMap.polar Q (b m) (b k) =
        QuadraticMap.polar Q (b 0) (b 1)) := by
  have hQ_const : ∀ m, Q (b m) = Q (b 0) := by
    have hstep : ∀ m, Q (b (σ m)) = Q (b m) := by
      intro m
      rw [← hxb m, hIso]
    intro m
    rcases orbit_eq_of_fixedPointFree hσ m 0 with hk | hk | hk
    · rw [hk]
    · have hm : m = σ 0 := by rw [hk]; simp
      rw [hm, hstep 0]
    · have hm : m = σ (σ 0) := by rw [hk]; simp
      rw [hm, hstep (σ 0), hstep 0]
  refine ⟨hQ_const, ?_⟩
  have hβ_inv : ∀ u v, QuadraticMap.polar Q (x u) (x v) = QuadraticMap.polar Q u v :=
    fun u v => hIso.polar_apply u v
  have hβ_step : ∀ m k, QuadraticMap.polar Q (b (σ m)) (b (σ k)) =
      QuadraticMap.polar Q (b m) (b k) := by
    intro m k
    rw [← hxb m, ← hxb k]
    exact hβ_inv (b m) (b k)
  refine beta_const_of_fixedPointFree (β := fun m k => QuadraticMap.polar Q (b m) (b k))
    hσ hβ_step ?_
  intro m k
  exact QuadraticMap.polar_comm Q (b m) (b k)

private theorem polar_sub_apply_eq_zero
    {Q : QuadraticForm (ZMod p) U} {b : Fin 3 → U}
    (hQ_const : ∀ m, Q (b m) = Q (b 0))
    (hβ_const : ∀ m k, m ≠ k → QuadraticMap.polar Q (b m) (b k) =
      QuadraticMap.polar Q (b 0) (b 1))
    (h2A : 2 * Q (b 0) = QuadraticMap.polar Q (b 0) (b 1)) :
    ∀ m, QuadraticMap.polar Q (b 0 - b 1) (b m) = 0 := by
  intro m
  fin_cases m
  · simp only [Fin.zero_eta]
    rw [QuadraticMap.polar_sub_left,
      CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul,
      hβ_const 1 0 (by decide)]
    change 2 * Q (b 0) - QuadraticMap.polar Q (b 0) (b 1) = 0
    rw [← h2A, sub_self]
  · simp only [Fin.mk_one]
    rw [QuadraticMap.polar_sub_left,
      hβ_const 0 1 (by decide),
      CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul,
      hQ_const 1]
    change QuadraticMap.polar Q (b 0) (b 1) - 2 * Q (b 0) = 0
    rw [h2A, sub_self]
  · norm_num
    rw [hβ_const 0 2 (by decide), hβ_const 1 2 (by decide)]
    change QuadraticMap.polar Q (b 0) (b 1) -
      QuadraticMap.polar Q (b 0) (b 1) = 0
    rw [sub_self]

private theorem span_range_eq_and_polar_eq_zero
    {Q : QuadraticForm (ZMod p) U}
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {c : Fin 3 → ZMod p} (hc_ne : ∀ m, c m ≠ 0)
    {b : Fin 3 → U} (hb_mem : ∀ m, b m ∈ HardMathSupport.Kantor79.commutatorSpace B)
    (hb_def : ∀ m, b m = c m • (f m : U))
    (hβ_u_b : ∀ m, QuadraticMap.polar Q (b 0 - b 1) (b m) = 0) :
    (HardMathSupport.Kantor79.commutatorSpace B =
        Submodule.span (ZMod p) (Set.range b)) ∧
      ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace B,
        QuadraticMap.polar Q (b 0 - b 1) v = 0 := by
  have hspan : HardMathSupport.Kantor79.commutatorSpace B =
      Submodule.span (ZMod p) (Set.range b) := by
    apply le_antisymm
    · intro v hv
      have hf_mem : ∀ m, (f m : U) ∈ Submodule.span (ZMod p) (Set.range b) := by
        intro m
        have hc_inv : (c m)⁻¹ • b m = (f m : U) := by
          rw [hb_def m, smul_smul, inv_mul_cancel₀ (hc_ne m), one_smul]
        rw [← hc_inv]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self m))
      have hv_sum : v = ∑ m, f.repr ⟨v, hv⟩ m • (f m : U) := by
        have h := f.sum_repr ⟨v, hv⟩
        exact (congrArg Subtype.val h).symm
      rw [hv_sum]
      exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (hf_mem m)
    · rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      exact hb_mem m
  refine ⟨hspan, ?_⟩
  intro v hv
  rw [hspan] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨m, rfl⟩
    exact hβ_u_b m
  | zero => simp
  | add x y _ _ hx0 hy0 =>
    rw [QuadraticMap.polar_add_right, hx0, hy0, add_zero]
  | smul a x _ hx0 =>
    rw [QuadraticMap.polar_smul_right, hx0]
    simp

private theorem apply_sub_eq_self_and_polar_eq_zero
    {Q : QuadraticForm (ZMod p) U} {e : U}
    (hD : LemmaTwoSevenData p G H B h) (hoH : IsOrthOn p Q H)
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {c : Fin 3 → ZMod p} {b : Fin 3 → U}
    (hb_def : ∀ m, b m = c m • (f m : U))
    (hVB : HardMathSupport.Kantor79.commutatorSpace B =
      LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))
    (hhe : h e = -e) (hp : p ≠ 2) :
    h (b 0 - b 1) = b 0 - b 1 ∧
      QuadraticMap.polar Q (b 0 - b 1) e = 0 := by
  have hu_fix : h (b 0 - b 1) = b 0 - b 1 := by
    have hfix : ∀ m, h (b m) = b m := by
      intro m
      have hfm : h (f m : U) = (f m : U) := by
        have hker : (f m : U) ∈ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := by
          rw [← hVB]
          exact (f m).2
        exact sub_eq_zero.mp (LinearMap.mem_ker.mp hker)
      rw [hb_def m]
      rw [map_smul, hfm]
    change h (b 0 - b 1) = b 0 - b 1
    rw [map_sub, hfix 0, hfix 1]
  refine ⟨hu_fix, ?_⟩
  have h1 : QuadraticMap.polar Q (h (b 0 - b 1)) (h e) =
      QuadraticMap.polar Q (b 0 - b 1) e :=
    (hoH.isIsom hD.mem).polar_apply (b 0 - b 1) e
  rw [hu_fix, hhe] at h1
  rw [show -e = (-1 : ZMod p) • e from by simp,
    CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq] at h1
  rw [neg_one_mul] at h1
  exact eq_zero_of_eq_neg (ZMod.prime_ne_zero p 2 hp) h1.symm

private theorem sub_eq_zero_and_sub_ne_zero
    {Q : QuadraticForm (ZMod p) U} {e : U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {c : Fin 3 → ZMod p} (hc_ne : ∀ m, c m ≠ 0)
    {b : Fin 3 → U} (hb_mem : ∀ m, b m ∈ HardMathSupport.Kantor79.commutatorSpace B)
    (hb_def : ∀ m, b m = c m • (f m : U))
    (hβ_u_VB : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace B,
      QuadraticMap.polar Q (b 0 - b 1) v = 0)
    (hβ_u_e : QuadraticMap.polar Q (b 0 - b 1) e = 0)
    (hsup : HardMathSupport.Kantor79.commutatorSpace B ⊔ (ZMod p ∙ e) = ⊤) :
    b 0 - b 1 = 0 ∧ b 0 - b 1 ≠ 0 := by
  have hu_mem : b 0 - b 1 ∈ HardMathSupport.Kantor79.commutatorSpace B :=
    Submodule.sub_mem _ (hb_mem 0) (hb_mem 1)
  have hu_eq : b 0 - b 1 = 0 := by
    apply hQ.1 (b 0 - b 1)
    intro z
    rw [QuadraticMap.polarBilin_apply_apply]
    have hz : z ∈ HardMathSupport.Kantor79.commutatorSpace B ⊔ (ZMod p ∙ e) := by
      rw [hsup]; trivial
    obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp hz
    rw [QuadraticMap.polar_add_right, hβ_u_VB v hv]
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq, hβ_u_e, mul_zero, zero_add]
  refine ⟨hu_eq, ?_⟩
  intro hu0
  have huV : (⟨b 0 - b 1, hu_mem⟩ : HardMathSupport.Kantor79.commutatorSpace B) = 0 := by
    ext
    exact hu0
  have h := congrArg (fun x : HardMathSupport.Kantor79.commutatorSpace B => f.repr x 0) huV
  have hb0 : (⟨b 0, hb_mem 0⟩ : HardMathSupport.Kantor79.commutatorSpace B) =
      c 0 • f 0 := by
    ext
    exact hb_def 0
  have hb1 : (⟨b 1, hb_mem 1⟩ : HardMathSupport.Kantor79.commutatorSpace B) =
      c 1 • f 1 := by
    ext
    exact hb_def 1
  have huV' : (⟨b 0 - b 1, hu_mem⟩ : HardMathSupport.Kantor79.commutatorSpace B) =
      (⟨b 0, hb_mem 0⟩ : HardMathSupport.Kantor79.commutatorSpace B) -
        ⟨b 1, hb_mem 1⟩ := by
    ext
    rfl
  have h' : f.repr (⟨b 0 - b 1, hu_mem⟩ :
      HardMathSupport.Kantor79.commutatorSpace B) 0 = c 0 := by
    rw [huV', map_sub, hb0, hb1, map_smul, map_smul]
    simp
  rw [h'] at h
  simp at h
  exact hc_ne 0 h

private theorem exists_unit_mul_eq_and_mul_ne_one {c : Fin 3 → ZMod p} (hc_ne : ∀ m, c m ≠ 0)
    {ζ : (ZMod p)ˣ} (hζ : ζ * ζ ≠ 1) :
    ∃ (μ : (ZMod p)ˣ) (lam : ZMod p),
      μ ∈ Subgroup.zpowers ζ ∧ lam * c 1 = c 0 * (μ : ZMod p) ∧
      lam * (c 1 * ((μ : ZMod p)⁻¹)) = c 0 ∧ lam * lam ≠ 1 := by
  let r : ZMod p := c 0 / c 1
  let μ : (ZMod p)ˣ := if r * r = 1 then ζ else 1
  let lam : ZMod p := (μ : ZMod p) * r
  have hμ : μ ∈ Subgroup.zpowers ζ := by
    by_cases hr : r * r = 1
    · simp [μ, hr]
    · simp [μ, hr]
  have hlam : lam * lam ≠ 1 := by
    intro h
    by_cases hr : r * r = 1
    · have hmu : (μ : ZMod p) = (ζ : ZMod p) := by simp [μ, hr]
      have hζsq : (ζ : ZMod p) * (ζ : ZMod p) = 1 := by
        have h' : ((ζ : ZMod p) * r) * ((ζ : ZMod p) * r) = 1 := by
          simpa [lam, hmu] using h
        have h'' : ((ζ : ZMod p) * (ζ : ZMod p)) * (r * r) = 1 := by
          rw [← h']
          ring
        rwa [hr, mul_one] at h''
      have hζsq' : ζ * ζ = 1 := by
        apply Units.ext
        rw [Units.val_mul, Units.val_one]
        exact hζsq
      exact hζ hζsq'
    · have hmu : (μ : ZMod p) = 1 := by simp [μ, hr]
      have h' : r * r = 1 := by simpa [lam, hmu] using h
      exact hr h'
  have hlamc : lam * c 1 = c 0 * (μ : ZMod p) := by
    calc lam * c 1 = ((μ : ZMod p) * (c 0 / c 1)) * c 1 := rfl
      _ = (μ : ZMod p) * ((c 0 / c 1) * c 1) := by ring
      _ = (μ : ZMod p) * c 0 := by rw [div_mul_cancel₀ _ (hc_ne 1)]
      _ = c 0 * (μ : ZMod p) := by ring
  have hlamc' : lam * (c 1 * ((μ : ZMod p)⁻¹)) = c 0 := by
    calc lam * (c 1 * ((μ : ZMod p)⁻¹)) = (lam * c 1) * ((μ : ZMod p)⁻¹) := by ring
      _ = (c 0 * (μ : ZMod p)) * ((μ : ZMod p)⁻¹) := by rw [hlamc]
      _ = c 0 * ((μ : ZMod p) * ((μ : ZMod p)⁻¹)) := by ring
      _ = c 0 := by rw [mul_inv_cancel₀ (Units.ne_zero μ), mul_one]
  exact ⟨μ, lam, hμ, hlamc, hlamc', hlam⟩

private theorem exists_mem_and_apply_eq_of_mem_zpowers
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {i₀ i₁ : Fin 3} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ}
    (hB : gmmn p f i₀ i₁ ζ ≤ movedGroup B)
    {μ : (ZMod p)ˣ} (hμ : μ ∈ Subgroup.zpowers ζ) :
    ∃ (t : B) (tbar : HardMathSupport.Kantor79.commutatorSpace B ≃ₗ[ZMod p]
        HardMathSupport.Kantor79.commutatorSpace B),
      (∀ v : HardMathSupport.Kantor79.commutatorSpace B,
        (t : U ≃ₗ[ZMod p] U) (v : U) = (tbar v : U)) ∧
      tbar (f 0) = μ • f 1 ∧ tbar (f 1) = μ⁻¹ • f 0 ∧ tbar (f 2) = f 2 := by
  let tbar : HardMathSupport.Kantor79.commutatorSpace B ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace B :=
    diagMap p f (pairUnit p 1 0 μ) * permMap p f (Equiv.swap 0 1)
  have htbar_mem : tbar ∈ movedGroup B := by
    apply hB
    exact Subgroup.mul_mem _ (diagMap_pairUnit_mem_gmmn f hi (by decide) hμ)
      (Subgroup.subset_closure (Or.inl (Set.mem_range_self (Equiv.swap 0 1))))
  have htbar_mem' : tbar ∈ (restrictHom B (HardMathSupport.Kantor79.commutatorSpace B)
      (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)).range := by
    change tbar ∈ movedGroup B
    exact htbar_mem
  obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp htbar_mem'
  have ht_apply : ∀ v : HardMathSupport.Kantor79.commutatorSpace B,
      (t : U ≃ₗ[ZMod p] U) (v : U) = (tbar v : U) := by
    intro v
    rw [← restrictHom_apply B (HardMathSupport.Kantor79.commutatorSpace B)
      (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) t v, ht]
  have htbar_f0 : tbar (f 0) = μ • f 1 := by
    change (diagMap p f (pairUnit p 1 0 μ) * permMap p f (Equiv.swap 0 1)) (f 0) = μ • f 1
    rw [LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis]
    simp only [Equiv.swap_apply_left]
    rw [show pairUnit p 1 0 μ 1 = μ from rfl]
    rfl
  have htbar_f1 : tbar (f 1) = μ⁻¹ • f 0 := by
    change (diagMap p f (pairUnit p 1 0 μ) * permMap p f (Equiv.swap 0 1)) (f 1) = μ⁻¹ • f 0
    rw [LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis]
    simp only [Equiv.swap_apply_right]
    rw [show pairUnit p 1 0 μ 0 = μ⁻¹ from rfl]
    rfl
  have htbar_f2 : tbar (f 2) = f 2 := by
    change (diagMap p f (pairUnit p 1 0 μ) * permMap p f (Equiv.swap 0 1)) (f 2) = f 2
    rw [LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis]
    change ↑(pairUnit p 1 0 μ 2) • f 2 = f 2
    rw [show pairUnit p 1 0 μ 2 = 1 from rfl]
    rw [one_smul]
  exact ⟨t, tbar, ht_apply, htbar_f0, htbar_f1, htbar_f2⟩

private theorem exists_neg_and_fixed
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {b : Fin 3 → U} {c : Fin 3 → ZMod p}
    (hb_def : ∀ m, b m = c m • (f m : U))
    {t : B} {tbar : HardMathSupport.Kantor79.commutatorSpace B ≃ₗ[ZMod p]
        HardMathSupport.Kantor79.commutatorSpace B}
    (ht_apply : ∀ v : HardMathSupport.Kantor79.commutatorSpace B,
      (t : U ≃ₗ[ZMod p] U) (v : U) = (tbar v : U))
    {μ : (ZMod p)ˣ} {lam : ZMod p}
    (htbar_f0 : tbar (f 0) = μ • f 1)
    (htbar_f1 : tbar (f 1) = μ⁻¹ • f 0)
    (htbar_f2 : tbar (f 2) = f 2)
    (hlamc : lam * c 1 = c 0 * (μ : ZMod p))
    (hlamc' : lam * (c 1 * ((μ : ZMod p)⁻¹)) = c 0) :
    ∃ w v : U, (t : U ≃ₗ[ZMod p] U) w = -w ∧
      (t : U ≃ₗ[ZMod p] U) v = v ∧
      w = b 0 - lam • b 1 ∧ v = b 0 + lam • b 1 - (1 + lam) • b 2 := by
  let w : U := b 0 - lam • b 1
  let v : U := b 0 + lam • b 1 - (1 + lam) • b 2
  have h0 : (t : U ≃ₗ[ZMod p] U) (b 0) = (c 0 * (μ : ZMod p)) • (f 1 : U) := by
    rw [hb_def 0, map_smul, ht_apply (f 0), htbar_f0]
    change c 0 • ((μ : ZMod p) • (f 1 : U)) = (c 0 * (μ : ZMod p)) • (f 1 : U)
    rw [smul_smul]
  have h1 : (t : U ≃ₗ[ZMod p] U) (b 1) = (c 1 * ((μ : ZMod p)⁻¹)) • (f 0 : U) := by
    rw [hb_def 1, map_smul, ht_apply (f 1), htbar_f1]
    change c 1 • ((↑(μ⁻¹) : ZMod p) • (f 0 : U)) =
      (c 1 * ((μ : ZMod p)⁻¹)) • (f 0 : U)
    rw [Units.val_inv_eq_inv_val, smul_smul]
  have h2 : (t : U ≃ₗ[ZMod p] U) (b 2) = c 2 • (f 2 : U) := by
    rw [hb_def 2, map_smul, ht_apply (f 2), htbar_f2]
  have hw : w = c 0 • (f 0 : U) - lam • (c 1 • (f 1 : U)) := by
    rw [show w = b 0 - lam • b 1 from rfl, hb_def 0, hb_def 1, smul_smul]
  have hv : v = c 0 • (f 0 : U) + lam • (c 1 • (f 1 : U)) -
      (1 + lam) • (c 2 • (f 2 : U)) := by
    rw [show v = b 0 + lam • b 1 - (1 + lam) • b 2 from rfl,
      hb_def 0, hb_def 1, hb_def 2, smul_smul, smul_smul]
  have htw : (t : U ≃ₗ[ZMod p] U) w = -w := by
    conv_rhs => rw [hw]
    rw [map_sub, h0, map_smul, h1, smul_smul, hlamc']
    rw [show c 0 * (μ : ZMod p) = lam * c 1 from by rw [hlamc]]
    rw [← smul_smul]
    module
  have htv : (t : U ≃ₗ[ZMod p] U) v = v := by
    conv_rhs => rw [hv]
    rw [map_sub, map_add, h0, map_smul, h1, map_smul, h2, smul_smul, hlamc']
    rw [show c 0 * (μ : ZMod p) = lam * c 1 from by rw [hlamc]]
    rw [← smul_smul]
    module
  exact ⟨w, v, htw, htv, rfl, rfl⟩

private theorem mem_commutatorSpace_of_eq_sum [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    (hoH : IsOrthOn p Q H)
    {y : U} (hyH : y ∈ centralizerSpace H) (hy0 : y ≠ 0)
    {b : Fin 3 → U} {lam : ZMod p}
    (hQ_const : ∀ m, Q (b m) = Q (b 0))
    (hβ_const : ∀ m k, m ≠ k → QuadraticMap.polar Q (b m) (b k) =
      QuadraticMap.polar Q (b 0) (b 1))
    (hy_sum : y = b 0 + b 1 + b 2)
    {v : U} (hv_def : v = b 0 + lam • b 1 - (1 + lam) • b 2) :
    v ∈ HardMathSupport.Kantor79.commutatorSpace H := by
  have hfinH : Module.finrank (ZMod p) (centralizerSpace H) = 1 := by
    have h := SplitSupport.finrank_centralizerSpace hD.setting.sub.2.1
    omega
  have hspan_y : centralizerSpace H = ZMod p ∙ y :=
    eq_span_singleton_of_mem_of_finrank_eq_one hfinH hyH hy0
  have hv : v ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    rw [mem_commutatorSpace_iff_forall_polar_eq_zero hQ (fun g hg => hoH.isIsom hg)
      hD.setting.sub.2.1.1]
    intro u hu
    rw [hspan_y] at hu
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq]
    have hyv : QuadraticMap.polar Q y v = 0 := by
      rw [hy_sum, hv_def]
      simp only [QuadraticMap.polar_add_left,
        QuadraticMap.polar_add_right, QuadraticMap.polar_sub_right,
        QuadraticMap.polar_smul_right,
        CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul]
      rw [hQ_const 1, hQ_const 2,
        hβ_const 0 1 (by decide), hβ_const 0 2 (by decide),
        hβ_const 1 0 (by decide), hβ_const 1 2 (by decide),
        hβ_const 2 0 (by decide), hβ_const 2 1 (by decide)]
      ring
    rw [hyv, mul_zero]
  exact hv

private theorem polar_eq_mul_one_sub_sq
    {Q : QuadraticForm (ZMod p) U} {b : Fin 3 → U} {v w : U}
    (hQ_const : ∀ m, Q (b m) = Q (b 0))
    (hβ_const : ∀ m k, m ≠ k → QuadraticMap.polar Q (b m) (b k) =
      QuadraticMap.polar Q (b 0) (b 1))
    {lam : ZMod p} (hv_def : v = b 0 + lam • b 1 - (1 + lam) • b 2)
    (hw_def : w = b 0 - lam • b 1) :
    QuadraticMap.polar Q v w =
      (2 * Q (b 0) - QuadraticMap.polar Q (b 0) (b 1)) * (1 - lam * lam) := by
  rw [hv_def, hw_def]
  simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_sub_left,
    QuadraticMap.polar_sub_right,
    QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_left,
    CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul]
  rw [hQ_const 1,
    hβ_const 0 1 (by decide),
    hβ_const 1 0 (by decide),
    hβ_const 2 0 (by decide), hβ_const 2 1 (by decide)]
  ring

private theorem two_mul_ne_polar
    {Q : QuadraticForm (ZMod p) U} {e : U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hD : LemmaTwoSevenData p G H B h)
    (hoH : IsOrthOn p Q H)
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {c : Fin 3 → ZMod p} (hc_ne : ∀ m, c m ≠ 0)
    {b : Fin 3 → U} (hb_mem : ∀ m, b m ∈ HardMathSupport.Kantor79.commutatorSpace B)
    (hb_def : ∀ m, b m = c m • (f m : U))
    (hQ_const : ∀ m, Q (b m) = Q (b 0))
    (hβ_const : ∀ m k, m ≠ k → QuadraticMap.polar Q (b m) (b k) =
      QuadraticMap.polar Q (b 0) (b 1))
    (hVB : HardMathSupport.Kantor79.commutatorSpace B =
      LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))
    (hVB' : centralizerSpace B = HardMathSupport.Kantor79.movedSpace h)
    (hhe : h e = -e) (he0 : e ≠ 0) (hp : p ≠ 2) :
    2 * Q (b 0) ≠ QuadraticMap.polar Q (b 0) (b 1) := by
  intro h2A
  let u : U := b 0 - b 1
  have hβ_u_b : ∀ m, QuadraticMap.polar Q u (b m) = 0 := by
    have h := polar_sub_apply_eq_zero hQ_const hβ_const h2A
    intro m
    exact h m
  have hu_mem : u ∈ HardMathSupport.Kantor79.commutatorSpace B :=
    Submodule.sub_mem _ (hb_mem 0) (hb_mem 1)
  obtain ⟨-, hβ_u_VB⟩ := span_range_eq_and_polar_eq_zero hc_ne hb_mem hb_def hβ_u_b
  obtain ⟨hu_fix, hβ_u_e⟩ := apply_sub_eq_self_and_polar_eq_zero hD hoH hb_def hVB hhe hp
  have hspan_e : HardMathSupport.Kantor79.movedSpace h = ZMod p ∙ e :=
    IsRefl.movedSpace_eq_span hp hD.isRefl hhe he0
  have hsup : HardMathSupport.Kantor79.commutatorSpace B ⊔ (ZMod p ∙ e) = ⊤ := by
    rw [← hspan_e, ← hVB', hD.split.2.2.1.1.sup_eq_top]
  obtain ⟨hu_eq, hu_ne⟩ := sub_eq_zero_and_sub_ne_zero hQ hc_ne hb_mem hb_def hβ_u_VB hβ_u_e hsup
  exact hu_ne hu_eq

theorem false_of_apply_eq_diagMap_mul_permMap (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {i₀ i₁ : Fin 3} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (hζ : ζ * ζ ≠ 1)
    (hB : gmmn p f i₀ i₁ ζ ≤ movedGroup B) {x : U ≃ₗ[ZMod p] U} (hx : x ∈ H)
    {d : Fin 3 → (ZMod p)ˣ} {σ : Equiv.Perm (Fin 3)} (hσ : ∀ l, σ l ≠ l)
    (hxd : ∀ v : HardMathSupport.Kantor79.commutatorSpace B,
      x v = ((diagMap p f d * permMap p f σ) v : U)) : False := by
  have h3 : 3 ≤ Module.finrank (ZMod p) U := by omega
  obtain ⟨hVB, hVB'⟩ := commutatorSpace_eq_ker_of_isCentralizingSplit hp h3 hD.split hD.isRefl
  obtain ⟨Q, e, hQ, hoH, he0, hQe, hhe, heB, heH⟩ := exists_isOrthOn_root hp hD
  obtain ⟨y, hyH, hyB, hy0, hrec⟩ := exists_mem_fixed_and_coord_recurrence hD hVB hx hxd
  let c : Fin 3 → ZMod p := fun m => f.repr ⟨y, hyB⟩ m
  have hc_rec : ∀ m, c m = (d m : ZMod p) * c (σ.symm m) := hrec
  have hc_ne : ∀ m, c m ≠ 0 :=
    coord_ne_zero hσ hc_rec (exists_coord_ne_zero hy0 hyB)
  let b : Fin 3 → U := fun m => c m • (f m : U)
  have hb_mem : ∀ m, b m ∈ HardMathSupport.Kantor79.commutatorSpace B :=
    fun m => Submodule.smul_mem _ _ (f m).2
  have hxb : ∀ m, x (b m) = b (σ m) :=
    apply_eq_of_coord_recurrence (f := f) (fun m => rfl) hxd hc_rec
  obtain ⟨hQ_const, hβ_const⟩ := quadratic_and_polar_const (b := b) hσ hxb (hoH.isIsom hx)
  let A : ZMod p := Q (b 0)
  let A' : ZMod p := QuadraticMap.polar Q (b 0) (b 1)
  have h2A_ne : 2 * A ≠ A' := by
    simpa [A, A'] using two_mul_ne_polar hQ hD hoH hc_ne hb_mem (fun m => rfl) hQ_const hβ_const
      hVB hVB' hhe he0 hp
  obtain ⟨μ, lam, hμ, hlamc, hlamc', hlam⟩ := exists_unit_mul_eq_and_mul_ne_one hc_ne hζ
  obtain ⟨t, tbar, ht_apply, htbar_f0, htbar_f1, htbar_f2⟩ :=
    exists_mem_and_apply_eq_of_mem_zpowers (f := f) hi hB hμ
  obtain ⟨w, v, htw, htv, hw_def, hv_def⟩ :=
    exists_neg_and_fixed (f := f) (b := b) (c := c) (fun m => rfl) ht_apply htbar_f0 htbar_f1
      htbar_f2 hlamc hlamc'
  have hy_sum : y = b 0 + b 1 + b 2 := by
    have h := f.sum_repr ⟨y, hyB⟩
    have h' : y = ∑ m, b m := (congrArg Subtype.val h).symm
    rw [h']
    simp [Fin.sum_univ_three]
  have hv : v ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    mem_commutatorSpace_of_eq_sum hQ hD h4 hoH hyH hy0 hQ_const hβ_const hy_sum hv_def
  have hp5 : 5 ≤ p := (Fact.out : p.Prime).five_le_of_ne_two_of_ne_three hp
    (fun h3 => by have := hD.setting.five_le_of_eq_three h3; omega)
  have hvw : QuadraticMap.polar Q v w = 0 :=
    polar_eq_zero_of_apply_eq_neg_of_apply_eq hp5 hD hQ hoH t.2 htw hv htv
  have hvw' : QuadraticMap.polar Q v w = (2 * A - A') * (1 - lam * lam) := by
    have h := polar_eq_mul_one_sub_sq hQ_const hβ_const hv_def hw_def
    simpa [A, A'] using h
  rw [hvw'] at hvw
  exact mul_ne_zero (sub_ne_zero.mpr h2A_ne) (fun h => hlam (sub_eq_zero.mp h).symm) hvw

end CFSG.StandardType.ZS

end
