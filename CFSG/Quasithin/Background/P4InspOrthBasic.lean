module

public import CFSG.Quasithin.Background.G12Ortho
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
public import CFSG.Adapters.ProjectiveSpecialLinear
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace G11

namespace P4InspOrth

section Generic

variable {G : Type*} [Group G]

theorem p4insporth_comm_le_self (O : Subgroup G) : ⁅O, O⁆ ≤ O :=
  Subgroup.commutator_le.2 fun g hg h hh => by
    rw [commutatorElement_def]
    exact O.mul_mem (O.mul_mem (O.mul_mem hg hh) (O.inv_mem hg)) (O.inv_mem hh)

theorem p4insporth_perfect_le {O K : Subgroup G} (hKO : K ≤ O) (hperf : Group.IsPerfect ↥K) :
    K ≤ ⁅O, O⁆ := by
  have h : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 hperf
  calc K = ⁅K, K⁆ := h.symm
    _ ≤ ⁅O, O⁆ := Subgroup.commutator_mono hKO hKO

theorem p4insporth_eq_commutator {O M K : Subgroup G} (hMO : M ≤ O) (hJM : ⁅O, O⁆ ≤ M)
    (hKM : K ≤ M) (hnorm : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hperf : Group.IsPerfect ↥K) (hK0 : K ≠ ⊥) (hsimple : IsSimpleGroup ↥⁅O, O⁆) :
    K = ⁅O, O⁆ := by
  have hKJ : K ≤ ⁅O, O⁆ := p4insporth_perfect_le (hKM.trans hMO) hperf
  have : (K.subgroupOf ⁅O, O⁆).Normal := by
    refine ⟨fun k hk j => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact hnorm j (hJM j.2) k hk
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf ⁅O, O⁆) with h | h
  · exfalso
    apply hK0
    rw [eq_bot_iff]
    intro k hk
    have hk' : (⟨k, hKJ hk⟩ : ↥⁅O, O⁆) ∈ K.subgroupOf ⁅O, O⁆ := hk
    rw [h] at hk'
    have := congrArg Subtype.val (Subgroup.mem_bot.1 hk')
    simpa using this
  · exact le_antisymm hKJ (Subgroup.subgroupOf_eq_top.1 h)

theorem p4insporth_perfect_eq_bot {O K : Subgroup G} (hKO : K ≤ O) (hsolv : Group.IsSolvable ↥O)
    (hperf : Group.IsPerfect ↥K) : K = ⊥ := by
  by_contra hne
  have : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).2 hne
  have : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKO)
      (Subgroup.inclusion_injective hKO)
  exact Group.IsPerfect.not_isSolvable ↥K ‹_›

end Generic

instance p4insporth_finite_glv {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U] :
    Finite (GLV U) :=
  Finite.of_injective _ DFunLike.coe_injective

section Orth

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] {f : LinearMap.BilinForm (ZMod 2) U}
  {q : U → ZMod 2}

theorem p4insporth_comm_le_omega [Finite U] (hf : IsSymplectic f)
    (hd : 4 ≤ Module.finrank (ZMod 2) U) (hq : ∀ x y, q (x + y) = q x + q y + f x y) :
    ⁅orthSub q, orthSub q⁆ ≤ omegaSub f q := by
  have hΩO : omegaSub f q ≤ orthSub q := g12o_omegaSub_le_orthSub hq hf
  have hnorm : ∀ x ∈ orthSub q, ∀ y ∈ omegaSub f q, x * y * x⁻¹ ∈ omegaSub f q :=
    fun x hx y hy => g12o_conj_mem_omegaSub hq hf hx hy
  rw [Subgroup.commutator_le]
  intro g hg h hh
  rw [commutatorElement_def]
  let S : Subgroup (GLV U) :=
    { carrier := {h | h ∈ orthSub q ∧ g * h * g⁻¹ * h⁻¹ ∈ omegaSub f q}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨(orthSub q).mul_mem ha hb, ?_⟩
        have e : g * (a * b) * g⁻¹ * (a * b)⁻¹ =
            (g * a * g⁻¹ * a⁻¹) * (a * (g * b * g⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e]
        exact (omegaSub f q).mul_mem ha' (hnorm a ha _ hb')
      one_mem' := ⟨(orthSub q).one_mem, by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨(orthSub q).inv_mem ha, ?_⟩
        have e : g * a⁻¹ * g⁻¹ * a⁻¹⁻¹ = a⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact hnorm a⁻¹ ((orthSub q).inv_mem ha) _ ((omegaSub f q).inv_mem ha') }
  have hΩS : omegaSub f q ≤ S := fun w hw =>
    ⟨hΩO hw, (omegaSub f q).mul_mem (hnorm g hg w hw) ((omegaSub f q).inv_mem hw)⟩
  have hgS : g ∈ S := ⟨hg, by
    have : g * g * g⁻¹ * g⁻¹ = 1 := by group
    rw [this]
    exact (omegaSub f q).one_mem⟩
  have hΓS : omegaSub f q ⊔ Subgroup.zpowers g ≤ S :=
    sup_le hΩS ((Subgroup.zpowers_le).2 hgS)
  rcases orthSub_index_le_two hf hd hq (Γ := omegaSub f q ⊔ Subgroup.zpowers g) le_sup_left
      (sup_le hΩO ((Subgroup.zpowers_le).2 hg)) with hΓ | hΓ
  · have hgΩ : g ∈ omegaSub f q := by
      rw [← hΓ]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
    have e : g * h * g⁻¹ * h⁻¹ = g * (h * g⁻¹ * h⁻¹) := by group
    rw [e]
    exact (omegaSub f q).mul_mem hgΩ (hnorm h hh _ ((omegaSub f q).inv_mem hgΩ))
  · exact (hΓS (by rw [hΓ]; exact hh)).2

theorem p4insporth_even_dim [Finite U] (hf : IsSymplectic f) :
    Even (Module.finrank (ZMod 2) U) :=
  LinearMap.BilinForm.IsAlt.even_finrank hf.1 hf.nondegenerate

theorem p4insporth_ne_bot {K : Subgroup (GLV U)} (hirr : IsIrr K ⊤)
    (hd : 1 < Module.finrank (ZMod 2) U) : K ≠ ⊥ := by
  intro hK
  obtain ⟨u, hu⟩ : ∃ u : U, u ≠ 0 := by
    by_contra h
    push Not at h
    have : Subsingleton U := ⟨fun a b => by rw [h a, h b]⟩
    have := Module.finrank_zero_of_subsingleton (R := ZMod 2) (M := U)
    omega
  have hinv : Invariant K (Submodule.span (ZMod 2) {u}) := by
    intro k hk x hx
    rw [hK, Subgroup.mem_bot] at hk
    rw [hk]
    exact hx
  rcases hirr.2.2 _ hinv bot_le le_top with h | h
  · apply hu
    have : u ∈ Submodule.span (ZMod 2) {u} := Submodule.mem_span_singleton_self u
    rw [h] at this
    exact (Submodule.mem_bot _).1 this
  · have h1 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {u}) = 1 := finrank_span_singleton hu
    rw [h, finrank_top] at h1
    omega

@[expose] noncomputable def p4insporth_quad (hq : ∀ x y, q (x + y) = q x + q y + f x y) :
    QuadraticForm (ZMod 2) U where
  toFun := q
  toFun_smul a x := by rw [g12o_q_smul hq, smul_eq_mul, g12o_mul_self]
  exists_companion' := ⟨f, hq⟩

theorem p4insporth_quad_apply (hq : ∀ x y, q (x + y) = q x + q y + f x y) (x : U) :
    p4insporth_quad hq x = q x := rfl

theorem p4insporth_polar_quad (hq : ∀ x y, q (x + y) = q x + q y + f x y) (x y : U) :
    QuadraticMap.polar (p4insporth_quad hq) x y = f x y := by
  rw [QuadraticMap.polar, p4insporth_quad_apply, p4insporth_quad_apply, p4insporth_quad_apply, hq]
  ring

theorem p4insporth_polarBilin_quad (hq : ∀ x y, q (x + y) = q x + q y + f x y) :
    QuadraticMap.polarBilin (p4insporth_quad hq) = f := by
  ext x y
  exact p4insporth_polar_quad hq x y

theorem p4insporth_nondegenerate_quad (hf : IsSymplectic f)
    (hq : ∀ x y, q (x + y) = q x + q y + f x y) :
    (QuadraticMap.polarBilin (p4insporth_quad hq)).Nondegenerate := by
  rw [p4insporth_polarBilin_quad hq]
  exact hf.nondegenerate

theorem p4insporth_orthogonalGroup_quad (hq : ∀ x y, q (x + y) = q x + q y + f x y) :
    TauCeti.QuadraticMap.orthogonalGroup (p4insporth_quad hq) = orthSub q := by
  ext g
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  exact Iff.rfl

end Orth

section Transport

variable {U V : Type} [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def p4insporth_cg (ι : U ≃ₗ[ZMod 2] V) : GLV U ≃* GLV V where
  toFun g := ι.symm.trans (g.trans ι)
  invFun g := ι.trans (g.trans ι.symm)
  left_inv g := by ext x; simp
  right_inv g := by ext x; simp
  map_mul' g h := by ext x; simp

theorem p4insporth_cg_apply (ι : U ≃ₗ[ZMod 2] V) (g : GLV U) (y : V) :
    p4insporth_cg ι g y = ι (g (ι.symm y)) := rfl

theorem p4insporth_cg_mem_orthSub {q : U → ZMod 2} {q' : V → ZMod 2} (ι : U ≃ₗ[ZMod 2] V)
    (hι : ∀ x, q' (ι x) = q x) (g : GLV U) :
    p4insporth_cg ι g ∈ orthSub q' ↔ g ∈ orthSub q := by
  constructor
  · intro h x
    have h1 := h (ι x)
    simp only [p4insporth_cg_apply, LinearEquiv.symm_apply_apply, hι] at h1
    exact h1
  · intro h y
    show q' (ι (g (ι.symm y))) = q' y
    have h2 : q (g (ι.symm y)) = q (ι.symm y) := h (ι.symm y)
    rw [hι, h2, ← hι, LinearEquiv.apply_symm_apply]

theorem p4insporth_map_cg_orthSub {q : U → ZMod 2} {q' : V → ZMod 2} (ι : U ≃ₗ[ZMod 2] V)
    (hι : ∀ x, q' (ι x) = q x) :
    (orthSub q).map (p4insporth_cg ι).toMonoidHom = orthSub q' := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (p4insporth_cg_mem_orthSub ι hι g).2 hg
  · intro hy
    refine ⟨(p4insporth_cg ι).symm y, ?_, by simp⟩
    rw [← p4insporth_cg_mem_orthSub ι hι]
    simpa using hy

theorem p4insporth_map_cg_commutator {q : U → ZMod 2} {q' : V → ZMod 2} (ι : U ≃ₗ[ZMod 2] V)
    (hι : ∀ x, q' (ι x) = q x) :
    (⁅orthSub q, orthSub q⁆).map (p4insporth_cg ι).toMonoidHom = ⁅orthSub q', orthSub q'⁆ := by
  rw [Subgroup.map_commutator, p4insporth_map_cg_orthSub ι hι]

theorem p4insporth_isSimpleGroup_commutator_of_iso {q : U → ZMod 2} {q' : V → ZMod 2}
    (ι : U ≃ₗ[ZMod 2] V) (hι : ∀ x, q' (ι x) = q x)
    (h : IsSimpleGroup ↥⁅orthSub q', orthSub q'⁆) : IsSimpleGroup ↥⁅orthSub q, orthSub q⁆ := by
  have e := Subgroup.equivMapOfInjective ⁅orthSub q, orthSub q⁆ (p4insporth_cg ι).toMonoidHom
    (p4insporth_cg ι).injective
  rw [p4insporth_map_cg_commutator ι hι] at e
  exact e.isSimpleGroup

end Transport

end P4InspOrth

end G11

end CFSG.Quasithin
