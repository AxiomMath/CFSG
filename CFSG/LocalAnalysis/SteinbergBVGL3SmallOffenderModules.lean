module

public import CFSG.LocalAnalysis.SteinbergBVGL3OffenderFactors
public import CFSG.LocalAnalysis.SteinbergBVGL3NaturalSelfExtension
public import CFSG.Quasithin.SteinbergBQPerfectOneFactorCentralQuotient

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

namespace CFSG.LocalAnalysis.SteinbergBV

open Module Matrix CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

namespace SmallOffender

open ThreeInvolutions SelfExtension

theorem isPerfect_GL3 : Group.IsPerfect (GL (Fin 3) (ZMod 2)) := by
  refine ⟨eq_top_iff.2 ?_⟩
  rw [← closure_tGL_eq_top, Subgroup.closure_le, commutator_def]
  rintro x (rfl | rfl | rfl)
  · rw [SetLike.mem_coe, T01_eq, ← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · rw [SetLike.mem_coe, T12_eq, ← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · rw [SetLike.mem_coe, T20_eq, ← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def glEquiv (hV : finrank (ZMod 2) V = 3) :
    (V ≃ₗ[ZMod 2] V) ≃* GL (Fin 3) (ZMod 2) :=
  haveI : Module.Finite (ZMod 2) V := Module.finite_of_finrank_eq_succ hV
  MulEquiv.ofBijective (FixedCodim.toGL (Module.finBasisOfFinrankEq (ZMod 2) V hV))
    ((FixedCodim.toGL_injective _).bijective_of_nat_card_le
      (by rw [FixedCodim.card_GL3, natCard_linearEquiv hV]))

theorem isPerfect_linearEquiv (hV : finrank (ZMod 2) V = 3) :
    Group.IsPerfect (V ≃ₗ[ZMod 2] V) := by
  have := isPerfect_GL3
  exact Group.IsPerfect.ofSurjective (f := (glEquiv hV).symm.toMonoidHom)
    (glEquiv hV).symm.surjective

@[expose] def dualHom :
    (V ≃ₗ[ZMod 2] V) →* (Module.Dual (ZMod 2) V ≃ₗ[ZMod 2] Module.Dual (ZMod 2) V) where
  toFun g := g.symm.dualMap
  map_one' := by
    ext f v
    rfl
  map_mul' _ _ := by
    ext f v
    rfl

theorem bijective_dualHom (hV : finrank (ZMod 2) V = 3) :
    Function.Bijective (dualHom (V := V)) := by
  have : FiniteDimensional (ZMod 2) V := Module.finite_of_finrank_eq_succ hV
  have hD : finrank (ZMod 2) (Module.Dual (ZMod 2) V) = 3 := by
    rw [Subspace.dual_finrank_eq, hV]
  have : Finite (Module.Dual (ZMod 2) V) := Module.finite_of_finite (ZMod 2)
  have : Finite (Module.Dual (ZMod 2) V ≃ₗ[ZMod 2] Module.Dual (ZMod 2) V) :=
    Finite.of_injective (fun e => (e : Module.Dual (ZMod 2) V → Module.Dual (ZMod 2) V))
      DFunLike.coe_injective
  refine Function.Injective.bijective_of_nat_card_le ?_ ?_
  · rw [injective_iff_map_eq_one]
    intro g hg
    refine LinearEquiv.ext fun v => ?_
    have h : ∀ f : Module.Dual (ZMod 2) V, f (g.symm v - v) = 0 := fun f => by
      have h1 := LinearEquiv.congr_fun hg f
      have h2 := LinearMap.congr_fun h1 v
      change f (g.symm v) = f v at h2
      rw [map_sub, h2, sub_self]
    have h3 := sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).1 h)
    calc g v = g (g.symm v) := by rw [h3]
      _ = v := g.apply_symm_apply v
  · rw [natCard_linearEquiv hD, natCard_linearEquiv hV]

@[expose] noncomputable def dualEquiv (hV : finrank (ZMod 2) V = 3) :
    (V ≃ₗ[ZMod 2] V) ≃* (Module.Dual (ZMod 2) V ≃ₗ[ZMod 2] Module.Dual (ZMod 2) V) :=
  MulEquiv.ofBijective dualHom (bijective_dualHom hV)

theorem dualEquiv_apply (hV : finrank (ZMod 2) V = 3) (g : V ≃ₗ[ZMod 2] V)
    (f : Module.Dual (ZMod 2) V) : dualEquiv hV g f = dualRep V g f :=
  rfl

theorem self_extension_splitting {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (hW : finrank (ZMod 2) W = 3) {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (ρ : Representation (ZMod 2) (W ≃ₗ[ZMod 2] W) E)
    (i : W →ₗ[ZMod 2] E) (π : E →ₗ[ZMod 2] W) (hi : ∀ g w, i (g w) = ρ g (i w))
    (hπ : ∀ g e, π (ρ g e) = g (π e)) (hinj : Function.Injective i)
    (hsurj : Function.Surjective π) (hker : LinearMap.ker π = LinearMap.range i) :
    Nonempty (ρ.Equiv ((natRep W).prod (natRep W))) := by
  classical
  have : Module.Finite (ZMod 2) W := Module.finite_of_finrank_eq_succ hW
  set b := Module.finBasisOfFinrankEq (ZMod 2) W hW with hb
  set eW : W ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) := b.equivFun with heW
  have hbij : Function.Bijective (FixedCodim.toGL b) :=
    (FixedCodim.toGL_injective b).bijective_of_nat_card_le
      (by rw [FixedCodim.card_GL3, natCard_linearEquiv hW])
  set γe := MulEquiv.ofBijective (FixedCodim.toGL b) hbij with hγe
  have hγ : ∀ (g : GL (Fin 3) (ZMod 2)) w,
      γe.symm g w = eW.symm ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ eW w) := by
    intro g w
    have h := FixedCodim.equivFun_apply_toGL b (γe.symm g) w
    have h2 : FixedCodim.toGL b (γe.symm g) = g := γe.apply_symm_apply g
    rw [h2] at h
    rw [heW, ← h, LinearEquiv.symm_apply_apply]
  let ρ' : Representation (ZMod 2) (GL (Fin 3) (ZMod 2)) E := ρ.comp γe.symm.toMonoidHom
  have hρ' : ∀ g e, ρ' g e = ρ (γe.symm g) e := fun _ _ => rfl
  let i' : (Fin 3 → ZMod 2) →ₗ[ZMod 2] E := i ∘ₗ eW.symm.toLinearMap
  let π' : E →ₗ[ZMod 2] (Fin 3 → ZMod 2) := eW.toLinearMap ∘ₗ π
  have hi' : ∀ (g : GL (Fin 3) (ZMod 2)) v,
      i' ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) = ρ' g (i' v) := by
    intro g v
    simp only [i', LinearMap.comp_apply, LinearEquiv.coe_coe, hρ']
    rw [← hi, hγ, LinearEquiv.apply_symm_apply]
  have hπ' : ∀ (g : GL (Fin 3) (ZMod 2)) e,
      π' (ρ' g e) = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ π' e := by
    intro g e
    simp only [π', LinearMap.comp_apply, LinearEquiv.coe_coe, hρ']
    rw [hπ, hγ, LinearEquiv.apply_symm_apply]
  have hinj' : Function.Injective i' := hinj.comp eW.symm.injective
  have hsurj' : Function.Surjective π' := eW.surjective.comp hsurj
  have hker' : LinearMap.ker π' = LinearMap.range i' := by
    ext e
    constructor
    · intro he
      have he' : e ∈ LinearMap.ker π := by
        rw [LinearMap.mem_ker] at he ⊢
        simpa [π'] using he
      rw [hker] at he'
      obtain ⟨w, rfl⟩ := he'
      exact ⟨eW w, by simp [i']⟩
    · rintro ⟨v, rfl⟩
      have h : i (eW.symm v) ∈ LinearMap.ker π := by
        rw [hker]
        exact ⟨eW.symm v, rfl⟩
      rw [LinearMap.mem_ker] at h ⊢
      simp [π', i', h]
  obtain ⟨-, -, -, φ', -, hφ'eq⟩ :=
    natural_binary_three_space_self_extension_splitting ρ' i' π' hi' hπ' hinj' hsurj' hker'
  let e : E ≃ₗ[ZMod 2] W × W := φ'.symm.trans (eW.symm.prodCongr eW.symm)
  refine ⟨Representation.Equiv.mk e fun g => LinearMap.ext fun x => ?_⟩
  obtain ⟨⟨v, w⟩, rfl⟩ := φ'.surjective x
  have hg : γe.symm (γe g) = g := γe.symm_apply_apply g
  have h1 : ρ g (φ' (v, w)) =
      φ' (((γe g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v,
        ((γe g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w) := by
    rw [hφ'eq, hρ', hg]
  change e (ρ g (φ' (v, w))) = (g (e (φ' (v, w))).1, g (e (φ' (v, w))).2)
  simp only [e, LinearEquiv.trans_apply, h1, LinearEquiv.symm_apply_apply,
    LinearEquiv.prodCongr_apply]
  conv_rhs => rw [← hg, hγ, hγ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem sum_eq_of_step : ∀ {n : ℕ} (x : Fin (n + 1) → ℕ) (d : Fin n → ℕ), x 0 = 0 →
    (∀ i : Fin n, d i + x i.castSucc = x i.succ) → ∑ i, d i = x (Fin.last n)
  | 0, x, _, hx0, _ => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact (show x (Fin.last 0) = 0 from hx0).symm
  | n + 1, x, d, hx0, h => by
    have ih := sum_eq_of_step (fun i => x i.castSucc) (fun i => d i.castSucc) hx0 fun i => by
      have := h i.castSucc
      rwa [Fin.succ_castSucc] at this
    have hl : d (Fin.last n) + x (Fin.last n).castSucc = x (Fin.last (n + 1)) := h (Fin.last n)
    rw [Fin.sum_univ_castSucc]
    beta_reduce at ih
    omega

section Chain

variable {k G E : Type*} [Field k] [Group G] [AddCommGroup E] [Module k E]
  [FiniteDimensional k E] {ρ : Representation k G E}

theorem finrank_eq_sum_factors {n : ℕ} (c : Fin (n + 1) → Subrepresentation ρ) (hc0 : c 0 = ⊥)
    (hcn : c (Fin.last n) = ⊤) (hmono : ∀ i : Fin n, c i.castSucc ≤ c i.succ) :
    finrank k E = ∑ i : Fin n, finrank k ((c i.succ).toSubmodule ⧸
      (inSubrep (c i.castSucc) (c i.succ)).toSubmodule) := by
  have h := sum_eq_of_step (fun j => finrank k (c j).toSubmodule)
    (fun i => finrank k ((c i.succ).toSubmodule ⧸
      (inSubrep (c i.castSucc) (c i.succ)).toSubmodule))
    (by rw [hc0]; exact finrank_bot k E)
    fun i => OffenderFactors.finrank_quotient_inSubrep_add (hmono i)
  beta_reduce at h
  rw [h, hcn]
  exact (finrank_top k E).symm

theorem isEmpty_equiv_trivial_of_ne {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N]
    [Module k N] {σ : Representation k G M} (h : ∃ s m, σ s m ≠ m) :
    IsEmpty (σ.Equiv (Representation.trivial k G N)) := by
  refine ⟨fun φ => ?_⟩
  obtain ⟨s, m, hm⟩ := h
  apply hm
  apply φ.toLinearEquiv.injective
  have h1 := Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap s m
  exact h1

omit [FiniteDimensional k E] in
theorem exists_exact_of_two_factors {W : Type*} [AddCommGroup W] [Module k W]
    {σ : Representation k G W} (c : Fin 3 → Subrepresentation ρ) (hc0 : c 0 = ⊥)
    (hc2 : c 2 = ⊤) (φ₀ : (inSubrep (c 0) (c 1)).quotient.Equiv σ)
    (φ₁ : (inSubrep (c 1) (c 2)).quotient.Equiv σ) :
    ∃ (i : W →ₗ[k] E) (π : E →ₗ[k] W), (∀ g w, i (σ g w) = ρ g (i w)) ∧
      (∀ g e, π (ρ g e) = σ g (π e)) ∧ Function.Injective i ∧ Function.Surjective π ∧
      LinearMap.ker π = LinearMap.range i := by
  have hbot : (inSubrep (c 0) (c 1)).toSubmodule = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    have hx' : (x : E) ∈ (c 0).toSubmodule := hx
    rw [hc0] at hx'
    exact Subtype.ext ((Submodule.mem_bot k).1 hx')
  have hmem2 : ∀ x : E, x ∈ (c 2).toSubmodule := fun x => by
    rw [hc2]
    exact Submodule.mem_top
  let e₀ := Submodule.quotEquivOfEqBot _ hbot
  let i : W →ₗ[k] E := (c 1).toSubmodule.subtype ∘ₗ e₀.toLinearMap ∘ₗ
    φ₀.symm.toLinearEquiv.toLinearMap
  let ι : E →ₗ[k] (c 2).toSubmodule := LinearMap.codRestrict _ LinearMap.id hmem2
  let π : E →ₗ[k] W := φ₁.toLinearEquiv.toLinearMap ∘ₗ
    (inSubrep (c 1) (c 2)).toSubmodule.mkQ ∘ₗ ι
  have hφ₀ : ∀ g q, φ₀.symm (σ g q) = (inSubrep (c 0) (c 1)).quotient g (φ₀.symm q) :=
    fun g q => Representation.IntertwiningMap.isIntertwining _ _ φ₀.symm.toIntertwiningMap g q
  have hφ₁ : ∀ g q, φ₁ ((inSubrep (c 1) (c 2)).quotient g q) = σ g (φ₁ q) :=
    fun g q => Representation.IntertwiningMap.isIntertwining _ _ φ₁.toIntertwiningMap g q
  refine ⟨i, π, fun g w => ?_, fun g e => ?_, ?_, ?_, ?_⟩
  · change ((e₀ (φ₀.symm (σ g w)) : (c 1).toSubmodule) : E) = ρ g ((e₀ (φ₀.symm w) :
      (c 1).toSubmodule) : E)
    rw [hφ₀]
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (φ₀.symm w)
    rw [← hx]
    rfl
  · change φ₁ (Submodule.Quotient.mk (ι (ρ g e))) = σ g (φ₁ (Submodule.Quotient.mk (ι e)))
    rw [← hφ₁]
    rfl
  · intro w w' h
    apply φ₀.symm.toLinearEquiv.injective
    apply e₀.injective
    exact Subtype.ext h
  · intro w
    obtain ⟨q, rfl⟩ := φ₁.toLinearEquiv.surjective w
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨(y : E), ?_⟩
    change φ₁ (Submodule.Quotient.mk (ι (y : E))) = φ₁ (Submodule.Quotient.mk y)
    rfl
  · ext e
    constructor
    · intro he
      have he' : Submodule.Quotient.mk (ι e) = (0 : (c 2).toSubmodule ⧸
          (inSubrep (c 1) (c 2)).toSubmodule) := by
        apply φ₁.toLinearEquiv.injective
        rw [map_zero]
        exact he
      rw [Submodule.Quotient.mk_eq_zero] at he'
      have he1 : e ∈ (c 1).toSubmodule := he'
      refine ⟨φ₀ (e₀.symm ⟨e, he1⟩), ?_⟩
      change (((e₀ (φ₀.symm (φ₀ (e₀.symm ⟨e, he1⟩)))) : (c 1).toSubmodule) : E) = e
      rw [show φ₀.symm (φ₀ (e₀.symm ⟨e, he1⟩)) = e₀.symm ⟨e, he1⟩ from
        φ₀.toLinearEquiv.symm_apply_apply _, LinearEquiv.apply_symm_apply]
    · rintro ⟨w, rfl⟩
      rw [LinearMap.mem_ker]
      change φ₁ (Submodule.Quotient.mk (ι ((e₀ (φ₀.symm w) : (c 1).toSubmodule) : E))) = 0
      rw [show Submodule.Quotient.mk (ι ((e₀ (φ₀.symm w) : (c 1).toSubmodule) : E)) =
          (0 : (c 2).toSubmodule ⧸ (inSubrep (c 1) (c 2)).toSubmodule) from
        (Submodule.Quotient.mk_eq_zero _).2 (e₀ (φ₀.symm w)).2, map_zero]

end Chain

end SmallOffender

open SmallOffender in
theorem small_GL3_offender_explicit_module_production {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (hV : finrank (ZMod 2) V = 3) {E : Type u} [AddCommGroup E]
    [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E] [Nontrivial E]
    (ρ : Representation (ZMod 2) (V ≃ₗ[ZMod 2] V) E) (hdim : finrank (ZMod 2) E ≤ 6)
    (hE : Submodule.span (ZMod 2) {w | ∃ (s : V ≃ₗ[ZMod 2] V) (v : E), w = ρ s v - v} = ⊤)
    (B : Subgroup (V ≃ₗ[ZMod 2] V)) (hBe : CFSG.Open.IsElemAbelian 2 B) (hB : B ≠ ⊥) (r : ℕ)
    (hr : Nat.card B = 2 ^ r)
    (hoff : finrank (ZMod 2) E -
      finrank (ZMod 2) (Representation.invariants (ρ.comp B.subtype)) ≤ r) :
    ((∃ φ : E →ₗ[ZMod 2] V, (∀ g e, φ (ρ g e) = natRep V g (φ e)) ∧ Function.Surjective φ ∧
        LinearMap.ker φ = Representation.invariants ρ) ∨
      (Nonempty (ρ.Equiv ((natRep V).prod (natRep V))) ∧ finrank (ZMod 2) E = 6) ∨
      (∃ φ : E →ₗ[ZMod 2] Module.Dual (ZMod 2) V, (∀ g e, φ (ρ g e) = dualRep V g (φ e)) ∧
        Function.Surjective φ ∧ LinearMap.ker φ = Representation.invariants ρ) ∨
      (Nonempty (ρ.Equiv ((dualRep V).prod (dualRep V))) ∧ finrank (ZMod 2) E = 6)) ∧
    (∃ e : (V ≃ₗ[ZMod 2] V) ≃* (V ≃ₗ[ZMod 2] V), ∀ g v, e g v = natRep V g v) ∧
    ∃ e : (V ≃ₗ[ZMod 2] V) ≃* (Module.Dual (ZMod 2) V ≃ₗ[ZMod 2] Module.Dual (ZMod 2) V),
      ∀ g f, e g f = dualRep V g f := by
  refine ⟨?_, ⟨MulEquiv.refl _, fun _ _ => rfl⟩, ⟨dualEquiv hV, dualEquiv_apply hV⟩⟩
  classical
  have : FiniteDimensional (ZMod 2) V := Module.finite_of_finrank_eq_succ hV
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V)) DFunLike.coe_injective
  have hD3 : finrank (ZMod 2) (Module.Dual (ZMod 2) V) = 3 := by
    rw [Subspace.dual_finrank_eq, hV]
  have hperf := isPerfect_linearEquiv hV
  obtain ⟨n, c, hc0, hcn, hc⟩ :=
    (irreducible_binary_GL3_module_production hV).2.2.2.2 E ρ (by omega)
  obtain ⟨hnotA, horient, hcount, htwo⟩ := GL3_offender_composition_factor_production hV ρ B hBe
    hB r hr hoff n c hc0 hcn fun i => ⟨(hc i).1, (hc i).2.1⟩
  have hdim1 : ∀ i, Nonempty ((subrepChainFactor c i).Equiv (trivRep V)) →
      finrank (ZMod 2) ((c i.succ).toSubmodule ⧸
        (inSubrep (c i.castSucc) (c i.succ)).toSubmodule) = 1 := by
    rintro i ⟨φ⟩
    rw [φ.toLinearEquiv.finrank_eq, finrank_self]
  have hdim3 : ∀ i, IsEmpty ((subrepChainFactor c i).Equiv (trivRep V)) →
      finrank (ZMod 2) ((c i.succ).toSubmodule ⧸
        (inSubrep (c i.castSucc) (c i.succ)).toSubmodule) = 3 := by
    intro i h
    rcases (hc i).2.2 with h' | h' | h'
    · exact absurd h' (not_nonempty_iff.2 h)
    · obtain ⟨φ⟩ := h'
      rw [φ.toLinearEquiv.finrank_eq, hV]
    · obtain ⟨φ⟩ := h'
      rw [φ.toLinearEquiv.finrank_eq, hD3]
  have hsum := finrank_eq_sum_factors c hc0 hcn fun i => (hc i).1.le
  have hcard : Nat.card {i : Fin n // IsEmpty ((subrepChainFactor c i).Equiv (trivRep V))} =
      (Finset.univ.filter fun i => IsEmpty ((subrepChainFactor c i).Equiv (trivRep V))).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  by_cases h2 : Nat.card {i : Fin n // IsEmpty ((subrepChainFactor c i).Equiv (trivRep V))} = 2
  ·
    have hall : ∀ i : Fin n, IsEmpty ((subrepChainFactor c i).Equiv (trivRep V)) := by
      by_contra hcon
      push Not at hcon
      obtain ⟨i₀, hi₀⟩ := hcon
      have hle : (Finset.univ.filter fun i =>
          IsEmpty ((subrepChainFactor c i).Equiv (trivRep V))).card * 3 + 1 ≤
          ∑ i : Fin n, finrank (ZMod 2) ((c i.succ).toSubmodule ⧸
            (inSubrep (c i.castSucc) (c i.succ)).toSubmodule) := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun i => IsEmpty ((subrepChainFactor c i).Equiv (trivRep V)))]
        have h3 : ∑ i ∈ Finset.univ.filter (fun i =>
            IsEmpty ((subrepChainFactor c i).Equiv (trivRep V))),
            finrank (ZMod 2) ((c i.succ).toSubmodule ⧸
              (inSubrep (c i.castSucc) (c i.succ)).toSubmodule) =
            (Finset.univ.filter fun i =>
              IsEmpty ((subrepChainFactor c i).Equiv (trivRep V))).card * 3 := by
          rw [Finset.card_eq_sum_ones, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [hdim3 i (Finset.mem_filter.1 hi).2, one_mul]
        have h1 : 1 ≤ ∑ i ∈ Finset.univ.filter (fun i =>
            ¬ IsEmpty ((subrepChainFactor c i).Equiv (trivRep V))),
            finrank (ZMod 2) ((c i.succ).toSubmodule ⧸
              (inSubrep (c i.castSucc) (c i.succ)).toSubmodule) := by
          have hmem : i₀ ∈ Finset.univ.filter (fun i =>
              ¬ IsEmpty ((subrepChainFactor c i).Equiv (trivRep V))) :=
            Finset.mem_filter.2 ⟨Finset.mem_univ _, not_isEmpty_iff.2 hi₀⟩
          refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem)
          rw [hdim1 i₀ hi₀]
        omega
      rw [← hcard, h2] at hle
      omega
    have hn : n = 2 := by
      have hfilt : (Finset.univ.filter fun i =>
          IsEmpty ((subrepChainFactor c i).Equiv (trivRep V))) = Finset.univ :=
        Finset.filter_true_of_mem fun i _ => hall i
      rw [hcard, hfilt, Finset.card_univ, Fintype.card_fin] at h2
      exact h2
    subst hn
    have h6 : finrank (ZMod 2) E = 6 := by
      rw [hsum, Fin.sum_univ_two, hdim3 0 (hall 0), hdim3 1 (hall 1)]
    have hc2 : c 2 = ⊤ := hcn
    rcases horient with hnat | hdual
    ·
      obtain ⟨φ₀⟩ := (hnat 0).resolve_left (not_nonempty_iff.2 (hall 0))
      obtain ⟨φ₁⟩ := (hnat 1).resolve_left (not_nonempty_iff.2 (hall 1))
      obtain ⟨i, π, hi, hπ, hinj, hsurj, hker⟩ := exists_exact_of_two_factors c hc0 hc2 φ₀ φ₁
      exact Or.inr (Or.inl ⟨self_extension_splitting hV ρ i π hi hπ hinj hsurj hker, h6⟩)
    ·
      obtain ⟨φ₀⟩ := (hdual 0).resolve_left (not_nonempty_iff.2 (hall 0))
      obtain ⟨φ₁⟩ := (hdual 1).resolve_left (not_nonempty_iff.2 (hall 1))
      obtain ⟨i, π, hi, hπ, hinj, hsurj, hker⟩ := exists_exact_of_two_factors c hc0 hc2 φ₀ φ₁
      set ρ' : Representation (ZMod 2)
          (Module.Dual (ZMod 2) V ≃ₗ[ZMod 2] Module.Dual (ZMod 2) V) E :=
        ρ.comp (dualEquiv hV).symm.toMonoidHom with hρ'
      have hρ'g : ∀ g : V ≃ₗ[ZMod 2] V, ρ' (dualEquiv hV g) = ρ g := fun g => by
        rw [hρ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      have hi' : ∀ h f, i (h f) = ρ' h (i f) := fun h f => by
        obtain ⟨g, rfl⟩ := (dualEquiv hV).surjective h
        rw [hρ'g, dualEquiv_apply, hi]
      have hπ' : ∀ h e, π (ρ' h e) = h (π e) := fun h e => by
        obtain ⟨g, rfl⟩ := (dualEquiv hV).surjective h
        rw [hρ'g, dualEquiv_apply, hπ]
      obtain ⟨Φ⟩ := self_extension_splitting hD3 ρ' i π hi' hπ' hinj hsurj hker
      refine Or.inr (Or.inr (Or.inr ⟨⟨Representation.Equiv.mk Φ.toLinearEquiv fun g =>
        LinearMap.ext fun x => ?_⟩, h6⟩))
      have h1 := Representation.IntertwiningMap.isIntertwining _ _ Φ.toIntertwiningMap
        (dualEquiv hV g) x
      rw [hρ'g] at h1
      exact h1
  ·
    have hone : ∀ i j : Fin n,
        (∃ s w, Quasithin.SteinbergCF.factorRep (c i.castSucc) (c i.succ) s w ≠ w) →
        (∃ s w, Quasithin.SteinbergCF.factorRep (c j.castSucc) (c j.succ) s w ≠ w) → i = j := by
      intro i j hi hj
      by_contra hij
      have hi' : IsEmpty ((subrepChainFactor c i).Equiv (trivRep V)) :=
        isEmpty_equiv_trivial_of_ne hi
      have hj' : IsEmpty ((subrepChainFactor c j).Equiv (trivRep V)) :=
        isEmpty_equiv_trivial_of_ne hj
      have hsub : ({i, j} : Finset (Fin n)) ⊆ Finset.univ.filter fun i =>
          IsEmpty ((subrepChainFactor c i).Equiv (trivRep V)) := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hi'⟩
        · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hj'⟩
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_pair hij, ← hcard] at h1
      omega
    obtain ⟨j, -, π, hπeq, hπsurj, hπker, -, -, hjnt⟩ :=
      Quasithin.perfect_one_factor_module_central_quotient ρ hperf hE c hc0 hcn
        (fun i => ⟨(hc i).1.le, (hc i).2.1⟩) hone
    have hjtriv : IsEmpty ((subrepChainFactor c j).Equiv (trivRep V)) :=
      isEmpty_equiv_trivial_of_ne hjnt
    rcases horient with hnat | hdual
    · rcases hnat j with h | h
      · exact absurd h (not_nonempty_iff.2 hjtriv)
      obtain ⟨φ⟩ := h
      refine Or.inl ⟨φ.toLinearEquiv.toLinearMap ∘ₗ π, fun g e => ?_, ?_, ?_⟩
      · change φ (π (ρ g e)) = natRep V g (φ (π e))
        rw [hπeq]
        exact Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g (π e)
      · exact φ.toLinearEquiv.surjective.comp hπsurj
      · rw [← hπker]
        ext x
        change φ.toLinearEquiv (π x) = 0 ↔ π x = 0
        exact φ.toLinearEquiv.map_eq_zero_iff
    · rcases hdual j with h | h
      · exact absurd h (not_nonempty_iff.2 hjtriv)
      obtain ⟨φ⟩ := h
      refine Or.inr (Or.inr (Or.inl ⟨φ.toLinearEquiv.toLinearMap ∘ₗ π, fun g e => ?_, ?_, ?_⟩))
      · change φ (π (ρ g e)) = dualRep V g (φ (π e))
        rw [hπeq]
        exact Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g (π e)
      · exact φ.toLinearEquiv.surjective.comp hπsurj
      · rw [← hπker]
        ext x
        change φ.toLinearEquiv (π x) = 0 ↔ π x = 0
        exact φ.toLinearEquiv.map_eq_zero_iff

end CFSG.LocalAnalysis.SteinbergBV
