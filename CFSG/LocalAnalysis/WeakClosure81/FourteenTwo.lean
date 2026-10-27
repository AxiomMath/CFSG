module

public import CFSG.Quasithin.Background.B4Dual
public import CFSG.Quasithin.Background.F918E1
public import CFSG.LocalAnalysis.WeakClosure81.FourteenSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure
public import CFSG.Quasithin.Background.B1Key

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace FourteenTwoAbstract

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

open Submodule LinearMap

private theorem span_range_eq_top {ι : Type*} (f : ι → Module.Dual (ZMod 2) E)
    [FiniteDimensional (ZMod 2) E] (hf : ⨅ i, LinearMap.ker (f i) = ⊥) :
    Submodule.span (ZMod 2) (Set.range f) = ⊤ := by
  rw [eq_top_iff]
  intro K _
  refine FiniteDimensional.mem_span_of_iInf_ker_le_ker ?_
  rw [hf]; exact bot_le

private theorem smulRight_mem_span {ι M₁ : Type*} [AddCommGroup M₁] [Module (ZMod 2) M₁]
    (f : ι → Module.Dual (ZMod 2) E) [FiniteDimensional (ZMod 2) E]
    (hf : ⨅ i, LinearMap.ker (f i) = ⊥) (z : M₁) (g : Module.Dual (ZMod 2) E) :
    g.smulRight z ∈ Submodule.span (ZMod 2) (Set.range fun i => (f i).smulRight z) := by
  have hg : g ∈ Submodule.span (ZMod 2) (Set.range f) := by
    rw [span_range_eq_top f hf]; exact Submodule.mem_top
  let T : Module.Dual (ZMod 2) E →ₗ[ZMod 2] (E →ₗ[ZMod 2] M₁) :=
    { toFun := fun f => f.smulRight z
      map_add' := fun a b => by ext x; simp [add_smul]
      map_smul' := fun c a => by
        ext x
        show (c • a) x • z = c • (a x • z)
        rw [LinearMap.smul_apply, smul_eq_mul, mul_smul] }
  have hmap : T g ∈ Submodule.map T (Submodule.span (ZMod 2) (Set.range f)) :=
    ⟨g, hg, rfl⟩
  rw [Submodule.map_span] at hmap
  have hset : T '' Set.range f = Set.range (fun i => (f i).smulRight z) := by
    ext m; constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨f i, ⟨i, rfl⟩, rfl⟩
  rw [hset] at hmap
  exact hmap

private theorem span_smulRight_eq_top {N M₁ : Type*} [AddCommGroup N] [Module (ZMod 2) N]
    [AddCommGroup M₁] [Module (ZMod 2) M₁] [FiniteDimensional (ZMod 2) M₁]
    {ι : Type*} (f : ι → Module.Dual (ZMod 2) N)
    [FiniteDimensional (ZMod 2) N] (hf : ⨅ i, LinearMap.ker (f i) = ⊥) :
    Submodule.span (ZMod 2)
      {g : N →ₗ[ZMod 2] M₁ | ∃ i z, g = (f i).smulRight z} = ⊤ := by
  rw [eq_top_iff]
  intro φ _
  suffices H : ∀ r, ∀ φ : N →ₗ[ZMod 2] M₁,
      Module.finrank (ZMod 2) (LinearMap.range φ) = r →
      φ ∈ Submodule.span (ZMod 2) {g : N →ₗ[ZMod 2] M₁ | ∃ i z, g = (f i).smulRight z} by
    exact H _ φ rfl
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro φ hr
    by_cases hφ : φ = 0
    · rw [hφ]; exact Submodule.zero_mem _
    · have hrange : LinearMap.range φ ≠ ⊥ := by
        intro h
        exact hφ (LinearMap.range_eq_bot.mp h)
      obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hrange
      obtain ⟨lam, hlam⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hz0
      set ψ : N →ₗ[ZMod 2] M₁ := φ - (lam.comp φ).smulRight z with hψ
      have hψrange : LinearMap.range ψ ≤ LinearMap.range φ ⊓ LinearMap.ker lam := by
        rintro _ ⟨x, rfl⟩
        refine ⟨?_, ?_⟩
        · simp only [hψ, LinearMap.sub_apply, LinearMap.smulRight_apply]
          exact Submodule.sub_mem _ ⟨x, rfl⟩ (Submodule.smul_mem _ _ hz)
        · show lam (ψ x) = 0
          rw [hψ, LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.comp_apply, map_sub,
            map_smul, hlam, smul_eq_mul, mul_one]
          exact sub_self _
      have hproper : LinearMap.range φ ⊓ LinearMap.ker lam < LinearMap.range φ := by
        refine lt_of_le_of_ne inf_le_left ?_
        intro heq
        have hz_in : z ∈ LinearMap.range φ ⊓ LinearMap.ker lam := by rw [heq]; exact hz
        have hz_ker : z ∈ LinearMap.ker lam := hz_in.2
        rw [LinearMap.mem_ker, hlam] at hz_ker
        exact one_ne_zero hz_ker
      have hfin : Module.finrank (ZMod 2) (LinearMap.range ψ) < r := by
        rw [← hr]
        exact lt_of_le_of_lt (Submodule.finrank_mono hψrange)
          (Submodule.finrank_lt_finrank_of_lt hproper)
      have hψspan : ψ ∈ Submodule.span (ZMod 2)
          {g : N →ₗ[ZMod 2] M₁ | ∃ i z, g = (f i).smulRight z} :=
        ih _ hfin ψ rfl
      have hf₀span : (lam.comp φ).smulRight z ∈ Submodule.span (ZMod 2)
          {g : N →ₗ[ZMod 2] M₁ | ∃ i z, g = (f i).smulRight z} := by
        refine Submodule.span_mono ?_ (smulRight_mem_span (E := N) f hf z (lam.comp φ))
        rintro _ ⟨i, rfl⟩
        exact ⟨i, z, rfl⟩
      have : φ = ψ + (lam.comp φ).smulRight z := by rw [hψ]; abel
      rw [this]
      exact Submodule.add_mem _ hψspan hf₀span

private noncomputable def tMap (E₀ E₁ : Submodule (ZMod 2) E) (hE₁ : E₁ ≤ E₀)
    (φ : E ⧸ E₀ →ₗ[ZMod 2] E₁) : E →ₗ[ZMod 2] E :=
  LinearMap.id + E₁.subtype ∘ₗ (φ ∘ₗ E₀.mkQ)

private theorem tMap_apply (E₀ E₁ : Submodule (ZMod 2) E) (hE₁ : E₁ ≤ E₀)
    (φ : E ⧸ E₀ →ₗ[ZMod 2] E₁) (x : E) :
    tMap E₀ E₁ hE₁ φ x = x + (φ (E₀.mkQ x) : E) := rfl

private def Fam (E₀ E₂ : Submodule (ZMod 2) E) : Set (Submodule (ZMod 2) E) :=
  {F | F ⊔ E₀ = ⊤ ∧ F ⊓ E₀ = E₂}

private theorem isCompl_of_mem_Fam {E₀ E₁ E₂ F : Submodule (ZMod 2) E}
    (hE₁ : E₁ ≤ E₀) (hinf : E₁ ⊓ E₂ = ⊥) (hsup : E₁ ⊔ E₂ = E₀)
    (hF : F ∈ Fam E₀ E₂) : IsCompl F E₁ := by
  obtain ⟨hFtop, hFinf⟩ := hF
  have hE₂F : E₂ ≤ F := (le_of_eq hFinf.symm).trans inf_le_left
  refine ⟨?_, ?_⟩
  · have h : F ⊓ E₁ ≤ E₁ ⊓ E₂ :=
      le_inf inf_le_right ((le_inf inf_le_left (inf_le_right.trans hE₁)).trans (le_of_eq hFinf))
    rw [hinf] at h
    exact disjoint_iff.mpr (le_bot_iff.mp h)
  · have h : (F ⊔ E₁) ⊔ E₂ = ⊤ := by
      rw [sup_assoc, hsup, ← hFtop]
    rw [sup_eq_left.mpr (hE₂F.trans le_sup_left)] at h
    exact codisjoint_iff.mpr h

private theorem projectionOnto_eq_of_mem {E₀ E₁ E₂ F : Submodule (ZMod 2) E}
    (hE₁ : E₁ ≤ E₀) (hinf : E₁ ⊓ E₂ = ⊥) (hsup : E₁ ⊔ E₂ = E₀)
    (hF : F ∈ Fam E₀ E₂) {x a : E} (ha : a ∈ E₁) (hxa : x - a ∈ F) :
    E₁.projectionOnto F (isCompl_of_mem_Fam hE₁ hinf hsup hF).symm x = ⟨a, ha⟩ := by
  have hx : x = a + (x - a) := by abel
  rw [hx, map_add]
  have h1 : E₁.projectionOnto F (isCompl_of_mem_Fam hE₁ hinf hsup hF).symm a = ⟨a, ha⟩ :=
    Submodule.projectionOnto_apply_left _ ⟨a, ha⟩
  have h2 : E₁.projectionOnto F (isCompl_of_mem_Fam hE₁ hinf hsup hF).symm (x - a) = 0 := by
    rw [Submodule.projectionOnto_apply_eq_zero_iff]
    exact hxa
  rw [h1, h2, add_zero]

private theorem exists_tMap_map_eq (E₀ E₁ E₂ : Submodule (ZMod 2) E)
    (hE₁ : E₁ ≤ E₀) (hinf : E₁ ⊓ E₂ = ⊥) (hsup : E₁ ⊔ E₂ = E₀)
    {F F' : Submodule (ZMod 2) E} (hF : F ∈ Fam E₀ E₂) (hF' : F' ∈ Fam E₀ E₂) :
    ∃ φ : E ⧸ E₀ →ₗ[ZMod 2] E₁, F.map (tMap E₀ E₁ hE₁ φ) = F' := by
  have hc : IsCompl F E₁ := isCompl_of_mem_Fam hE₁ hinf hsup hF
  have hc' : IsCompl F' E₁ := isCompl_of_mem_Fam hE₁ hinf hsup hF'
  let p : E →ₗ[ZMod 2] E₁ := E₁.projectionOnto F hc.symm
  let p' : E →ₗ[ZMod 2] E₁ := E₁.projectionOnto F' hc'.symm
  let φ₀ : E →ₗ[ZMod 2] E₁ := p + p'
  have hφ₀ : ∀ x, φ₀ x = p x + p' x := fun x => rfl
  have hker : E₀ ≤ LinearMap.ker φ₀ := by
    intro x hx
    obtain ⟨a, ha, b, hb, hxab⟩ := Submodule.mem_sup.mp (hsup ▸ hx : x ∈ E₁ ⊔ E₂)
    have hbF : b ∈ F := (le_of_eq (hF.2).symm).trans inf_le_left hb
    have hbF' : b ∈ F' := (le_of_eq (hF'.2).symm).trans inf_le_left hb
    have hp : p x = ⟨a, ha⟩ := by
      rw [← hxab]
      exact projectionOnto_eq_of_mem hE₁ hinf hsup hF ha (by
        show a + b - a ∈ F
        rw [add_sub_cancel_left]; exact hbF)
    have hp' : p' x = ⟨a, ha⟩ := by
      rw [← hxab]
      exact projectionOnto_eq_of_mem hE₁ hinf hsup hF' ha (by
        show a + b - a ∈ F'
        rw [add_sub_cancel_left]; exact hbF')
    rw [LinearMap.mem_ker]
    show φ₀ x = 0
    rw [hφ₀, hp, hp']
    have h2 : (⟨a, ha⟩ : E₁) + ⟨a, ha⟩ = 0 := by
      rw [← two_smul (ZMod 2) (⟨a, ha⟩ : E₁), show (2 : ZMod 2) = 0 from by decide, zero_smul]
    exact h2
  let φ : E ⧸ E₀ →ₗ[ZMod 2] E₁ := E₀.liftQ φ₀ hker
  have hφ : φ ∘ₗ E₀.mkQ = φ₀ := Submodule.liftQ_mkQ _ _ _
  let f : E →ₗ[ZMod 2] E := LinearMap.id + E₁.subtype ∘ₗ φ₀
  have htm : tMap E₀ E₁ hE₁ φ = f := by rw [tMap, hφ]
  have hf_apply : ∀ x, f x = x + (φ₀ x : E) := fun x => rfl
  have hff : ∀ x, f (f x) = x := by
    intro x
    have hx0 : φ₀ ((φ₀ x : E₁) : E) = 0 :=
      LinearMap.mem_ker.mp (hker (hE₁ (φ₀ x).2))
    have h2 : (φ₀ x : E) + (φ₀ x : E) = 0 := by
      rw [← two_smul (ZMod 2) (φ₀ x : E), show (2 : ZMod 2) = 0 from by decide, zero_smul]
    rw [hf_apply, hf_apply, map_add, hx0, add_zero]
    rw [add_assoc, h2, add_zero]
  refine ⟨φ, ?_⟩
  rw [htm]
  have hle : F.map f ≤ F' := by
    rintro _ ⟨x, hx, rfl⟩
    have hpx : p x = 0 := by
      show E₁.projectionOnto F hc.symm x = 0
      rw [Submodule.projectionOnto_apply_eq_zero_iff]; exact hx
    have hfx : f x = x + (p' x : E) := by
      rw [hf_apply, hφ₀, hpx, zero_add]
    rw [hfx]
    have hxmem : x ∈ F' ⊔ E₁ := by rw [codisjoint_iff.mp hc'.2]; trivial
    obtain ⟨x', hx'F', z, hzE₁, hxz⟩ := Submodule.mem_sup.mp hxmem
    have hp'x : p' x = ⟨z, hzE₁⟩ := by
      rw [← hxz]
      exact projectionOnto_eq_of_mem hE₁ hinf hsup hF' hzE₁ (by
        show x' + z - z ∈ F'
        rw [add_sub_cancel_right]; exact hx'F')
    rw [hp'x, ← hxz, add_assoc]
    have h2 : z + z = 0 := by
      rw [← two_smul (ZMod 2) z, show (2 : ZMod 2) = 0 from by decide, zero_smul]
    rw [h2, add_zero]
    exact hx'F'
  have hle' : F'.map f ≤ F := by
    rintro _ ⟨x', hx', rfl⟩
    have hp'x : p' x' = 0 := by
      show E₁.projectionOnto F' hc'.symm x' = 0
      rw [Submodule.projectionOnto_apply_eq_zero_iff]; exact hx'
    have hfx : f x' = x' + (p x' : E) := by
      rw [hf_apply, hφ₀, hp'x, add_zero]
    rw [hfx]
    have hxmem : x' ∈ F ⊔ E₁ := by rw [codisjoint_iff.mp hc.2]; trivial
    obtain ⟨x, hxF, z, hzE₁, hxz⟩ := Submodule.mem_sup.mp hxmem
    have hpx : p x' = ⟨z, hzE₁⟩ := by
      rw [← hxz]
      exact projectionOnto_eq_of_mem hE₁ hinf hsup hF hzE₁ (by
        show x + z - z ∈ F
        rw [add_sub_cancel_right]; exact hxF)
    rw [hpx, ← hxz, add_assoc]
    have h2 : z + z = 0 := by
      rw [← two_smul (ZMod 2) z, show (2 : ZMod 2) = 0 from by decide, zero_smul]
    rw [h2, add_zero]
    exact hxF
  apply le_antisymm hle
  have hcomp : f ∘ₗ f = LinearMap.id := by ext x; exact hff x
  have hmono : (F'.map f).map f ≤ F.map f := Submodule.map_mono hle'
  rw [← Submodule.map_comp] at hmono
  rw [hcomp, Submodule.map_id] at hmono
  exact hmono

private theorem tMap_zero (E₀ E₁ : Submodule (ZMod 2) E) (hE₁ : E₁ ≤ E₀) :
    tMap E₀ E₁ hE₁ 0 = LinearMap.id := by
  ext x
  simp [tMap]

private theorem tMap_add (E₀ E₁ : Submodule (ZMod 2) E) (hE₁ : E₁ ≤ E₀)
    (φ ψ : E ⧸ E₀ →ₗ[ZMod 2] E₁) :
    tMap E₀ E₁ hE₁ (φ + ψ) = tMap E₀ E₁ hE₁ φ ∘ₗ tMap E₀ E₁ hE₁ ψ := by
  ext x
  have h0 : E₀.mkQ ((ψ (E₀.mkQ x) : E₁) : E) = 0 :=
    (Submodule.Quotient.mk_eq_zero E₀).2 (hE₁ (ψ (E₀.mkQ x)).2)
  simp only [tMap_apply, LinearMap.comp_apply, LinearMap.add_apply, Submodule.coe_add, map_add,
    h0, map_zero, ZeroMemClass.coe_zero, add_zero]
  abel

private theorem exists_dual_quot {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    (N₀ : Submodule R N) (f : Module.Dual R N) (h : N₀ ≤ LinearMap.ker f) :
    ∃ f' : Module.Dual R (N ⧸ N₀), ∀ x, f' (N₀.mkQ x) = f x :=
  ⟨N₀.liftQ f h, fun _ => rfl⟩

private theorem eq_top_of_smulRight_mem {N M₁ : Type*} [AddCommGroup N] [Module (ZMod 2) N]
    [FiniteDimensional (ZMod 2) N] [AddCommGroup M₁] [Module (ZMod 2) M₁]
    [FiniteDimensional (ZMod 2) M₁] {ι : Type*} (f : ι → Module.Dual (ZMod 2) N)
    (hf : ⨅ i, LinearMap.ker (f i) = ⊥) (Φ : Submodule (ZMod 2) (N →ₗ[ZMod 2] M₁))
    (hΦ : ∀ (i : ι) (z : M₁), (f i).smulRight z ∈ Φ) : Φ = ⊤ := by
  rw [eq_top_iff, ← span_smulRight_eq_top (M₁ := M₁) f hf, Submodule.span_le]
  rintro _ ⟨i, z, rfl⟩
  exact hΦ i z

end FourteenTwoAbstract

namespace FourteenTwo

variable {G : Type} [Group G] [Finite G]
variable {V : Subgroup G}

private abbrev E (V : Subgroup G) (hV : IsElemAbelian 2 V) := Additive (IntMod V hV)

private noncomputable instance instModuleE (V : Subgroup G) (hV : IsElemAbelian 2 V) :
    Module (ZMod 2) (E V hV) :=
  AddCommGroup.zmodModule (by
    intro x
    apply Additive.toMul.injective
    show Additive.toMul (2 • x) = Additive.toMul 0
    rw [two_nsmul, toMul_add, toMul_zero, ← pow_two]
    exact IntMod.sq_eq_one (Additive.toMul x))

private def ev {hV : IsElemAbelian 2 V} (x : E V hV) : G := (Additive.toMul x : IntMod V hV).val

private theorem ev_mem {hV : IsElemAbelian 2 V} (x : E V hV) : ev x ∈ V := IntMod.val_mem _

private theorem ev_add {hV : IsElemAbelian 2 V} (x y : E V hV) : ev (x + y) = ev x * ev y := rfl

private theorem ev_zero {hV : IsElemAbelian 2 V} : ev (0 : E V hV) = 1 := rfl

private theorem ev_injective {hV : IsElemAbelian 2 V} : Function.Injective (ev : E V hV → G) :=
  fun _ _ h => Additive.toMul.injective (IntMod.val_injective h)

private def ofG (hV : IsElemAbelian 2 V) (v : G) (hv : v ∈ V) : E V hV :=
  Additive.ofMul (IntMod.mk hV ⟨v, hv⟩)

private theorem ev_ofG {hV : IsElemAbelian 2 V} {v : G} (hv : v ∈ V) : ev (ofG hV v hv) = v := rfl

private noncomputable def submodEquiv (hV : IsElemAbelian 2 V) :
    Subgroup (IntMod V hV) ≃o Submodule (ZMod 2) (E V hV) :=
  (Subgroup.toAddSubgroup).trans (AddSubgroup.toZModSubmodule 2)

private noncomputable def submod (hV : IsElemAbelian 2 V) (U : Subgroup G) :
    Submodule (ZMod 2) (E V hV) :=
  submodEquiv hV (U.subgroupOf V)

private theorem mem_submod {hV : IsElemAbelian 2 V} {U : Subgroup G} {x : E V hV} :
    x ∈ submod hV U ↔ ev x ∈ U := Iff.rfl

private theorem submod_mono {hV : IsElemAbelian 2 V} {U U' : Subgroup G} (h : U ≤ U') :
    submod hV U ≤ submod hV U' := fun _ hx => mem_submod.2 (h (mem_submod.1 hx))

private theorem submod_sup {hV : IsElemAbelian 2 V} {U U' : Subgroup G}
    (hU : U ≤ V) (hU' : U' ≤ V) :
    submod hV (U ⊔ U') = submod hV U ⊔ submod hV U' := by
  rw [submod, submod, submod, Subgroup.subgroupOf_sup hU hU']
  exact (submodEquiv hV).map_sup _ _

private theorem submod_inf {hV : IsElemAbelian 2 V} (U U' : Subgroup G) :
    submod hV (U ⊓ U') = submod hV U ⊓ submod hV U' := by
  ext x
  exact Subgroup.mem_inf

private theorem submod_bot {hV : IsElemAbelian 2 V} : submod hV (⊥ : Subgroup G) = ⊥ := by
  ext x
  rw [mem_submod, Subgroup.mem_bot, Submodule.mem_bot]
  exact ⟨fun h => ev_injective (h.trans ev_zero.symm), fun h => by rw [h, ev_zero]⟩

private theorem submod_top {hV : IsElemAbelian 2 V} : submod hV V = ⊤ := by
  ext x
  exact ⟨fun _ => trivial, fun _ => mem_submod.2 (ev_mem x)⟩

private theorem submod_injOn {hV : IsElemAbelian 2 V} {U U' : Subgroup G} (hU : U ≤ V)
    (hU' : U' ≤ V) (h : submod hV U = submod hV U') : U = U' := by
  ext y
  constructor
  · intro hy
    have h1 : ofG hV y (hU hy) ∈ submod hV U := mem_submod.2 hy
    rw [h, mem_submod, ev_ofG] at h1
    exact h1
  · intro hy
    have h1 : ofG hV y (hU' hy) ∈ submod hV U' := mem_submod.2 hy
    rw [← h, mem_submod, ev_ofG] at h1
    exact h1


private noncomputable def cLin (hV : IsElemAbelian 2 V) (g : G)
    (hg : g ∈ Subgroup.normalizer (V : Set G)) : E V hV →ₗ[ZMod 2] E V hV :=
  AddMonoidHom.toZModLinearMap 2
    (AddMonoidHom.mk'
      (fun x => ofG hV (g * ev x * g⁻¹) ((Subgroup.mem_normalizer_iff.1 hg _).1 (ev_mem x)))
      (fun x y => ev_injective (by
        simp only [ev_ofG, ev_add]
        group)))

private theorem ev_cLin {hV : IsElemAbelian 2 V} {g : G} {hg : g ∈ Subgroup.normalizer (V : Set G)}
    (x : E V hV) : ev (cLin hV g hg x) = g * ev x * g⁻¹ := rfl

private theorem cLin_one (hV : IsElemAbelian 2 V) :
    cLin hV 1 (Subgroup.one_mem _) = LinearMap.id := by
  refine LinearMap.ext fun x => ev_injective ?_
  rw [ev_cLin]
  simp

private theorem cLin_mul (hV : IsElemAbelian 2 V) {g h : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (hh : h ∈ Subgroup.normalizer (V : Set G)) :
    cLin hV (g * h) (Subgroup.mul_mem _ hg hh) = cLin hV g hg ∘ₗ cLin hV h hh := by
  refine LinearMap.ext fun x => ev_injective ?_
  simp only [LinearMap.comp_apply, ev_cLin]
  group

@[expose] def PSub (M V₀ V : Subgroup G) : Subgroup G :=
  F11.CTilde M V₀ V ⊓ (M ⊓ Subgroup.centralizer (V₀ : Set G))

@[expose] def CFixQuot (P V₁ V : Subgroup G) : Subgroup G where
  carrier := {p | p ∈ P ∧ p ∈ Subgroup.normalizer (V₁ : Set G) ∧ CentralizesMod V₁ V p}
  mul_mem' := by
    rintro p q ⟨hpP, hpN, hp⟩ ⟨hqP, hqN, hq⟩
    refine ⟨P.mul_mem hpP hqP, Subgroup.mul_mem _ hpN hqN, fun v hv => ?_⟩
    have h1 : p * q * v * (p * q)⁻¹ * v⁻¹ =
        (p * (q * v * q⁻¹ * v⁻¹) * p⁻¹) * (p * v * p⁻¹ * v⁻¹) := by group
    rw [h1]
    exact V₁.mul_mem ((Subgroup.mem_normalizer_iff.1 hpN _).1 (hq v hv)) (hp v hv)
  one_mem' := ⟨P.one_mem, Subgroup.one_mem _, fun v _ => by simpa using V₁.one_mem⟩
  inv_mem' := by
    rintro p ⟨hpP, hpN, hp⟩
    refine ⟨P.inv_mem hpP, Subgroup.inv_mem _ hpN, fun v hv => ?_⟩
    have h1 : p⁻¹ * v * p⁻¹⁻¹ * v⁻¹ = (p⁻¹ * (p * v * p⁻¹ * v⁻¹) * p⁻¹⁻¹)⁻¹ := by group
    rw [h1]
    exact V₁.inv_mem ((Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hpN) _).1 (hp v hv))

@[expose] def FamV (V₀ V₂ V : Subgroup G) : Set (Subgroup G) :=
  {F | F ≤ V ∧ F ⊔ V₀ = V ∧ F ⊓ V₀ = V₂}

@[expose] def InducesTransvection (V W : Subgroup G) (z a : G) : Prop :=
  (∀ w ∈ W, a * w * a⁻¹ = w) ∧ ∀ v ∈ V, v ∉ W → a * v * a⁻¹ = z * v

theorem mem_cTilde_iff_comm {M V₀ V : Subgroup G} {x : G} :
    x ∈ F11.CTilde M V₀ V ↔
      x ∈ M ∧ x ∈ Subgroup.normalizer (V₀ : Set G) ∧ ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ V₀ := by
  unfold F11.CTilde
  simp only [Subgroup.mem_iInf]
  constructor
  · intro h
    have h1 := h 1 V.one_mem
    exact ⟨h1.1, h1.2.1, fun v hv => (h v hv).2.2⟩
  · rintro ⟨h1, h2, h3⟩ v hv
    exact ⟨h1, h2, h3 v hv⟩


private theorem exists_mem_CFixQuot_transvection {M V₀ V₁ V A W : Subgroup G}
    (hM : M ≤ Subgroup.normalizer (V : Set G)) (hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G))
    (hM₁ : M ≤ Subgroup.normalizer (V₁ : Set G)) (hV₁ : V₁ ≤ V₀)
    (hAP : A ≤ PSub M V₀ V) (hAV₁ : ∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ * v⁻¹ ∈ V₁)
    (hAW : ∀ z ∈ V₁, ∃ a ∈ A, InducesTransvection V W z a)
    {g z : G} (hg : g ∈ M) (hz : z ∈ V₁) :
    ∃ p ∈ CFixQuot (PSub M V₀ V) V₁ V,
      (∀ v ∈ V, g⁻¹ * v * g ∈ W → p * v * p⁻¹ = v) ∧
      (∀ v ∈ V, g⁻¹ * v * g ∉ W → p * v * p⁻¹ = z * v) := by
  have hz' : g⁻¹ * z * g ∈ V₁ := (Subgroup.mem_normalizer_iff''.1 (hM₁ hg) z).1 hz
  obtain ⟨a, haA, haW, haV⟩ := hAW _ hz'
  obtain ⟨haC, haMC⟩ := Subgroup.mem_inf.1 (hAP haA)
  obtain ⟨haM, haCV₀⟩ := Subgroup.mem_inf.1 haMC
  have hpM : g * a * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg haM) (M.inv_mem hg)
  have hgV : ∀ v ∈ V, g⁻¹ * v * g ∈ V := fun v hv =>
    (Subgroup.mem_normalizer_iff''.1 (hM hg) v).1 hv
  have hkey : ∀ v ∈ V, (g * a * g⁻¹) * v * (g * a * g⁻¹)⁻¹ * v⁻¹ ∈ V₁ := by
    intro v hv
    have h1 : (g * a * g⁻¹) * v * (g * a * g⁻¹)⁻¹ * v⁻¹ =
        g * (a * (g⁻¹ * v * g) * a⁻¹ * (g⁻¹ * v * g)⁻¹) * g⁻¹ := by group
    rw [h1]
    exact (Subgroup.mem_normalizer_iff.1 (hM₁ hg) _).1 (hAV₁ a haA _ (hgV v hv))
  refine ⟨g * a * g⁻¹, ⟨?_, hM₁ hpM, fun v hv => hkey v hv⟩, ?_, ?_⟩
  · refine Subgroup.mem_inf.2 ⟨mem_cTilde_iff_comm.2 ⟨hpM, hM₀ hpM, fun v hv => hV₁ (hkey v hv)⟩,
      Subgroup.mem_inf.2 ⟨hpM, ?_⟩⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : g⁻¹ * x * g ∈ V₀ := (Subgroup.mem_normalizer_iff''.1 (hM₀ hg) x).1 hx
    have hc := Subgroup.mem_centralizer_iff.1 haCV₀ _ hx'
    calc x * (g * a * g⁻¹) = g * ((g⁻¹ * x * g) * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * x * g)) * g⁻¹ := by rw [hc]
      _ = (g * a * g⁻¹) * x := by group
  · intro v hv hw
    have h1 := haW _ hw
    calc (g * a * g⁻¹) * v * (g * a * g⁻¹)⁻¹
        = g * (a * (g⁻¹ * v * g) * a⁻¹) * g⁻¹ := by group
      _ = v := by rw [h1]; group
  · intro v hv hw
    have h1 := haV _ (hgV v hv) hw
    calc (g * a * g⁻¹) * v * (g * a * g⁻¹)⁻¹
        = g * (a * (g⁻¹ * v * g) * a⁻¹) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
      _ = z * v := by group


open Classical in
private noncomputable def fW (hV : IsElemAbelian 2 V) (W : Subgroup G) (hW : W.relIndex V = 2) :
    Module.Dual (ZMod 2) (E V hV) where
  toFun x := if ev x ∈ W then 0 else 1
  map_add' x y := by
    have hxy : ev x * ev y ∈ W ↔ (ev x ∈ W ↔ ev y ∈ W) :=
      Subgroup.mul_mem_iff_of_index_two (H := W.subgroupOf V) hW
        (a := ⟨ev x, ev_mem x⟩) (b := ⟨ev y, ev_mem y⟩)
    show (if ev (x + y) ∈ W then (0 : ZMod 2) else 1) =
      (if ev x ∈ W then 0 else 1) + (if ev y ∈ W then 0 else 1)
    rw [ev_add]
    by_cases hx : ev x ∈ W <;> by_cases hy : ev y ∈ W
    · rw [if_pos (hxy.2 (iff_of_true hx hy)), if_pos hx, if_pos hy]; decide
    · rw [if_neg (fun h => hy ((hxy.1 h).1 hx)), if_pos hx, if_neg hy]; decide
    · rw [if_neg (fun h => hx ((hxy.1 h).2 hy)), if_neg hx, if_pos hy]; decide
    · rw [if_pos (hxy.2 (iff_of_false hx hy)), if_neg hx, if_neg hy]; decide
  map_smul' c x := by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · show (if ev ((0 : ZMod 2) • x) ∈ W then (0 : ZMod 2) else 1) = 0 * _
      rw [zero_smul, ev_zero, if_pos W.one_mem, zero_mul]
    · show (if ev ((1 : ZMod 2) • x) ∈ W then (0 : ZMod 2) else 1) = 1 * _
      rw [one_smul, one_mul]

private theorem fW_of_mem {hV : IsElemAbelian 2 V} {W : Subgroup G} {hW : W.relIndex V = 2}
    {x : E V hV} (h : ev x ∈ W) : fW hV W hW x = 0 := if_pos h

private theorem fW_of_not_mem {hV : IsElemAbelian 2 V} {W : Subgroup G} {hW : W.relIndex V = 2}
    {x : E V hV} (h : ev x ∉ W) : fW hV W hW x = 1 := if_neg h

private noncomputable def fConj (hV : IsElemAbelian 2 V) {W : Subgroup G}
    (hW : W.relIndex V = 2) {g : G} (hgN : g ∈ Subgroup.normalizer (V : Set G)) :
    Module.Dual (ZMod 2) (E V hV) :=
  (fW hV W hW).comp (cLin hV g⁻¹ (Subgroup.inv_mem _ hgN))

private theorem fConj_apply {hV : IsElemAbelian 2 V} {W : Subgroup G} {hW : W.relIndex V = 2}
    {g : G} {hgN : g ∈ Subgroup.normalizer (V : Set G)} (x : E V hV) :
    fConj hV hW hgN x = fW hV W hW (cLin hV g⁻¹ (Subgroup.inv_mem _ hgN) x) := rfl

private def Kinter (M V W : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ V ∧ ∀ g ∈ M, g⁻¹ * x * g ∈ W}
  mul_mem' := by
    rintro x y ⟨hxV, hx⟩ ⟨hyV, hy⟩
    refine ⟨V.mul_mem hxV hyV, fun g hg => ?_⟩
    have h1 : g⁻¹ * (x * y) * g = (g⁻¹ * x * g) * (g⁻¹ * y * g) := by group
    rw [h1]
    exact W.mul_mem (hx g hg) (hy g hg)
  one_mem' := ⟨V.one_mem, fun g _ => by simpa using W.one_mem⟩
  inv_mem' := by
    rintro x ⟨hxV, hx⟩
    refine ⟨V.inv_mem hxV, fun g hg => ?_⟩
    have h1 : g⁻¹ * x⁻¹ * g = (g⁻¹ * x * g)⁻¹ := by group
    rw [h1]
    exact W.inv_mem (hx g hg)

private theorem Kinter_le_V {M V W : Subgroup G} : Kinter M V W ≤ V := fun _ h => h.1

private theorem Kinter_le_W {M V W : Subgroup G} : Kinter M V W ≤ W := fun _ h => by
  simpa using h.2 1 M.one_mem

private theorem M_le_normalizer_Kinter {M V W : Subgroup G}
    (hM : M ≤ Subgroup.normalizer (V : Set G)) :
    M ≤ Subgroup.normalizer (Kinter M V W : Set G) := by
  have key : ∀ m ∈ M, ∀ x ∈ Kinter M V W, m * x * m⁻¹ ∈ Kinter M V W := by
    intro m hm x hx
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hM hm) x).1 hx.1, fun g hg => ?_⟩
    have h1 := hx.2 (m⁻¹ * g) (M.mul_mem (M.inv_mem hm) hg)
    have e : g⁻¹ * (m * x * m⁻¹) * g = (m⁻¹ * g)⁻¹ * x * (m⁻¹ * g) := by group
    rw [e]
    exact h1
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key m hm x, fun h => ?_⟩
  have h1 := key m⁻¹ (M.inv_mem hm) _ h
  have e : m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x := by group
  rw [e] at h1
  exact h1


private theorem ev_comm {hV : IsElemAbelian 2 V} (x y : E V hV) : ev x * ev y = ev y * ev x := by
  rw [← ev_add, ← ev_add, add_comm]

private theorem realisable_eq_top {M V₀ V₁ V A W : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV₁ : V₁ ≤ V₀) (hM : M ≤ Subgroup.normalizer (V : Set G))
    (hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G)) (hM₁ : M ≤ Subgroup.normalizer (V₁ : Set G))
    (hgen : ConjGenerated M V₀ V) (hAP : A ≤ PSub M V₀ V)
    (hAV₁ : ∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ * v⁻¹ ∈ V₁) (hWV : W ≤ V) (hV₀W : V₀ ≤ W)
    (hW : W.relIndex V = 2) (hAW : ∀ z ∈ V₁, ∃ a ∈ A, InducesTransvection V W z a)
    (φ : E V hV ⧸ submod hV V₀ →ₗ[ZMod 2] ↥(submod hV V₁)) :
    ∃ (p : G) (hp : p ∈ Subgroup.normalizer (V : Set G)), p ∈ CFixQuot (PSub M V₀ V) V₁ V ∧
      FourteenTwoAbstract.tMap (submod hV V₀) (submod hV V₁) (submod_mono hV₁) φ =
        cLin hV p hp := by
  classical
  set C := CFixQuot (PSub M V₀ V) V₁ V with hCdef
  have hCN : ∀ p ∈ C, p ∈ Subgroup.normalizer (V : Set G) := fun p hp =>
    hM (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hp.1).2).1
  have hker : ∀ g : ↥M, submod hV V₀ ≤ LinearMap.ker (fConj hV hW (hM g.2)) := by
    intro g x hx
    rw [LinearMap.mem_ker, fConj_apply]
    refine fW_of_mem (hV₀W ?_)
    rw [ev_cLin]
    exact (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hM₀ g.2)) _).1 (mem_submod.1 hx)
  choose f hf using fun g : ↥M =>
    FourteenTwoAbstract.exists_dual_quot (submod hV V₀) (fConj hV hW (hM g.2)) (hker g)
  have hKne : Kinter M V W ≠ V := by
    intro h
    have hVW : V ≤ W := h ▸ Kinter_le_W
    rw [le_antisymm hWV hVW, Subgroup.relIndex_self] at hW
    exact absurd hW (by norm_num)
  have hfker : ⨅ g : ↥M, LinearMap.ker (f g) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
    rw [Submodule.mem_iInf] at hy
    have hK : ev x ∈ Kinter M V W := ⟨ev_mem x, fun g hg => by
      have h0 := LinearMap.mem_ker.1 (hy ⟨g, hg⟩)
      rw [hf, fConj_apply] at h0
      by_contra hnot
      have h1 := fW_of_not_mem (hV := hV) (hW := hW)
        (x := cLin hV g⁻¹ (Subgroup.inv_mem _ (hM hg)) x) (by rw [ev_cLin, inv_inv]; exact hnot)
      rw [h1] at h0
      exact one_ne_zero h0⟩
    have hKV₀ : Kinter M V W ≤ V₀ :=
      le_of_normalizer_of_ne_of_conjGenerated hgen Kinter_le_V (M_le_normalizer_Kinter hM) hKne
    exact (Submodule.mem_bot (ZMod 2)).2
      ((Submodule.Quotient.mk_eq_zero _).2 (mem_submod.2 (hKV₀ hK)))
  let Φ : Submodule (ZMod 2) (E V hV ⧸ submod hV V₀ →ₗ[ZMod 2] ↥(submod hV V₁)) :=
    { carrier := {ψ | ∃ (p : G) (hp : p ∈ Subgroup.normalizer (V : Set G)), p ∈ C ∧
        FourteenTwoAbstract.tMap (submod hV V₀) (submod hV V₁) (submod_mono hV₁) ψ =
          cLin hV p hp}
      add_mem' := by
        rintro ψ₁ ψ₂ ⟨p, hp, hpC, h1⟩ ⟨q, hq, hqC, h2⟩
        exact ⟨p * q, Subgroup.mul_mem _ hp hq, C.mul_mem hpC hqC, by
          rw [FourteenTwoAbstract.tMap_add, h1, h2, cLin_mul]⟩
      zero_mem' := ⟨1, Subgroup.one_mem _, C.one_mem, by
        rw [FourteenTwoAbstract.tMap_zero, cLin_one]⟩
      smul_mem' := by
        rintro c ψ ⟨p, hp, hpC, h1⟩
        rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
        · exact ⟨1, Subgroup.one_mem _, C.one_mem, by
            rw [zero_smul, FourteenTwoAbstract.tMap_zero, cLin_one]⟩
        · exact ⟨p, hp, hpC, by rw [one_smul]; exact h1⟩ }
  have hΦ : Φ = ⊤ := FourteenTwoAbstract.eq_top_of_smulRight_mem f hfker Φ (by
    intro g zE
    obtain ⟨p, hpC, hp1, hp2⟩ := exists_mem_CFixQuot_transvection hM hM₀ hM₁ hV₁ hAP hAV₁ hAW
      g.2 (mem_submod.1 zE.2)
    refine ⟨p, hCN p hpC, hpC, ?_⟩
    refine LinearMap.ext fun x => ev_injective ?_
    have hc : f g ((submod hV V₀).mkQ x) =
        fW hV W hW (cLin hV g⁻¹ (Subgroup.inv_mem _ (hM g.2)) x) := by
      rw [hf]; rfl
    rw [FourteenTwoAbstract.tMap_apply, LinearMap.smulRight_apply, hc]
    by_cases hw : g⁻¹ * ev x * g ∈ W
    · have h0 : fW hV W hW (cLin hV g⁻¹ (Subgroup.inv_mem _ (hM g.2)) x) = 0 :=
        fW_of_mem (by rw [ev_cLin, inv_inv]; exact hw)
      rw [h0, zero_smul, ZeroMemClass.coe_zero, add_zero, ev_cLin]
      exact (hp1 _ (ev_mem x) hw).symm
    · have h1 : fW hV W hW (cLin hV g⁻¹ (Subgroup.inv_mem _ (hM g.2)) x) = 1 :=
        fW_of_not_mem (by rw [ev_cLin, inv_inv]; exact hw)
      rw [h1, one_smul, ev_add, ev_cLin, hp2 _ (ev_mem x) hw]
      exact ev_comm _ _)
  have hφ : φ ∈ Φ := by rw [hΦ]; exact Submodule.mem_top
  exact hφ


private theorem submod_mem_Fam {hV : IsElemAbelian 2 V} {V₀ V₂ F : Subgroup G} (hV₀ : V₀ ≤ V)
    (hF : F ∈ FamV V₀ V₂ V) :
    submod hV F ∈ FourteenTwoAbstract.Fam (submod hV V₀) (submod hV V₂) := by
  obtain ⟨hFV, hsup, hinf⟩ := hF
  refine ⟨?_, ?_⟩
  · rw [← submod_sup hFV hV₀, hsup, submod_top]
  · rw [← submod_inf, hinf]

private theorem map_cLin_submod {hV : IsElemAbelian 2 V} {p : G}
    (hp : p ∈ Subgroup.normalizer (V : Set G)) (F : Subgroup G) :
    (submod hV F).map (cLin hV p hp) = submod hV (conjSubgroup F p⁻¹) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_submod, ev_cLin, mem_conjSubgroup_iff]
    have e : p⁻¹ * (p * ev x * p⁻¹) * p⁻¹⁻¹ = ev x := by group
    rw [e]
    exact mem_submod.1 hx
  · intro hy
    rw [mem_submod, mem_conjSubgroup_iff, inv_inv] at hy
    have hv : p⁻¹ * ev y * p ∈ V := (Subgroup.mem_normalizer_iff''.1 hp _).1 (ev_mem y)
    refine ⟨ofG hV _ hv, mem_submod.2 (by rw [ev_ofG]; exact hy), ev_injective ?_⟩
    rw [ev_cLin, ev_ofG]
    group

theorem fourteen_two_transitive {M V₀ V₁ V₂ V A W : Subgroup G}
    (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V) (hV₁ : V₁ ≤ V₀) (hV₂ : V₁ ⊓ V₂ = ⊥)
    (hV₁₂ : V₁ ⊔ V₂ = V₀) (hM : M ≤ Subgroup.normalizer (V : Set G))
    (hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G)) (hM₁ : M ≤ Subgroup.normalizer (V₁ : Set G))
    (hgen : ConjGenerated M V₀ V) (hAP : A ≤ PSub M V₀ V)
    (hAV₁ : ∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ * v⁻¹ ∈ V₁) (hWV : W ≤ V) (hV₀W : V₀ ≤ W)
    (hW : W.relIndex V = 2) (hAW : ∀ z ∈ V₁, ∃ a ∈ A, InducesTransvection V W z a)
    {F F' : Subgroup G} (hF : F ∈ FamV V₀ V₂ V) (hF' : F' ∈ FamV V₀ V₂ V) :
    ∃ p ∈ CFixQuot (PSub M V₀ V) V₁ V, conjSubgroup F p = F' := by
  have hV₁V : V₁ ≤ V := hV₁.trans hV₀
  have hV₂V : V₂ ≤ V := (le_sup_right.trans hV₁₂.le).trans hV₀
  have hE₁ : submod hV V₁ ≤ submod hV V₀ := submod_mono hV₁
  have hinf : submod hV V₁ ⊓ submod hV V₂ = ⊥ := by rw [← submod_inf, hV₂, submod_bot]
  have hsup : submod hV V₁ ⊔ submod hV V₂ = submod hV V₀ := by
    rw [← submod_sup hV₁V hV₂V, hV₁₂]
  obtain ⟨φ, hφ⟩ := FourteenTwoAbstract.exists_tMap_map_eq (submod hV V₀) (submod hV V₁)
    (submod hV V₂) hE₁ hinf hsup (submod_mem_Fam hV₀ hF) (submod_mem_Fam hV₀ hF')
  obtain ⟨p, hpN, hpC, hpφ⟩ :=
    realisable_eq_top hV hV₁ hM hM₀ hM₁ hgen hAP hAV₁ hWV hV₀W hW hAW φ
  refine ⟨p⁻¹, (CFixQuot (PSub M V₀ V) V₁ V).inv_mem hpC, ?_⟩
  have hmap := map_cLin_submod (hV := hV) hpN F
  rw [← hpφ, hφ] at hmap
  have hconj : conjSubgroup F p⁻¹ ≤ V :=
    (E3.conjSubgroup_mono_left p⁻¹ hF.1).trans
      (le_of_eq (conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.inv_mem _ hpN)))
  exact (submod_injOn hconj hF'.1 hmap.symm)


private theorem CFixQuot_le {M V₀ V₁ V₂ V : Subgroup G} (hV₂ : V₂ ≤ V₀) :
    CFixQuot (PSub M V₀ V) V₁ V ≤ M ⊓ Subgroup.normalizer (V₂ : Set G) := by
  intro c hc
  obtain ⟨hP, -, -⟩ := hc
  obtain ⟨-, hMC⟩ := Subgroup.mem_inf.1 hP
  obtain ⟨hcM, hcC⟩ := Subgroup.mem_inf.1 hMC
  exact Subgroup.mem_inf.2 ⟨hcM, Subgroup.centralizer_le_normalizer _
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hV₂) hcC)⟩

private theorem conjSubgroup_mem_FamV {V₀ V₂ V F : Subgroup G} {x : G}
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hx₀ : x ∈ Subgroup.normalizer (V₀ : Set G))
    (hx₂ : x ∈ Subgroup.normalizer (V₂ : Set G)) (hF : F ∈ FamV V₀ V₂ V) :
    conjSubgroup F x ∈ FamV V₀ V₂ V := by
  obtain ⟨hFV, hsup, hinf⟩ := hF
  have hV : conjSubgroup V x = V := conjSubgroup_eq_iff_mem_normalizer.2 hxV
  have hV₀ : conjSubgroup V₀ x = V₀ := conjSubgroup_eq_iff_mem_normalizer.2 hx₀
  have hV₂ : conjSubgroup V₂ x = V₂ := conjSubgroup_eq_iff_mem_normalizer.2 hx₂
  refine ⟨(E3.conjSubgroup_mono_left x hFV).trans (le_of_eq hV), ?_, ?_⟩
  · have h : conjSubgroup (F ⊔ V₀) x = conjSubgroup F x ⊔ conjSubgroup V₀ x := by
      unfold conjSubgroup
      exact Subgroup.map_sup _ _ _
    rw [hsup, hV, hV₀] at h
    exact h.symm
  · have h := E3.conjSubgroup_inf F V₀ x
    rw [hinf, hV₂, hV₀] at h
    exact h.symm

theorem fourteen_two_product {M V₀ V₁ V₂ V A W : Subgroup G}
    (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V) (hV₁ : V₁ ≤ V₀) (hV₂ : V₁ ⊓ V₂ = ⊥)
    (hV₁₂ : V₁ ⊔ V₂ = V₀) (hM : M ≤ Subgroup.normalizer (V : Set G))
    (hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G)) (hM₁ : M ≤ Subgroup.normalizer (V₁ : Set G))
    (hgen : ConjGenerated M V₀ V) (hAP : A ≤ PSub M V₀ V)
    (hAV₁ : ∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ * v⁻¹ ∈ V₁) (hWV : W ≤ V) (hV₀W : V₀ ≤ W)
    (hW : W.relIndex V = 2) (hAW : ∀ z ∈ V₁, ∃ a ∈ A, InducesTransvection V W z a)
    {F : Subgroup G} (hF : F ∈ FamV V₀ V₂ V) :
    ((M ⊓ Subgroup.normalizer (V₂ : Set G) : Subgroup G) : Set G) =
      (CFixQuot (PSub M V₀ V) V₁ V : Set G) *
        ((M ⊓ Subgroup.normalizer (V₂ : Set G) ⊓ Subgroup.normalizer (F : Set G) :
          Subgroup G) : Set G) := by
  have hV₂₀ : V₂ ≤ V₀ := le_sup_right.trans hV₁₂.le
  have hCle := CFixQuot_le (M := M) (V₁ := V₁) (V := V) hV₂₀
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨hxM, hx₂⟩ := Subgroup.mem_inf.1 hx
    have hxV := hM hxM
    have hx₀ := hM₀ hxM
    have hF' : conjSubgroup F x⁻¹ ∈ FamV V₀ V₂ V :=
      conjSubgroup_mem_FamV (Subgroup.inv_mem _ hxV) (Subgroup.inv_mem _ hx₀)
        (Subgroup.inv_mem _ hx₂) hF
    obtain ⟨c, hc, hcF⟩ := fourteen_two_transitive hV hV₀ hV₁ hV₂ hV₁₂ hM hM₀ hM₁ hgen hAP hAV₁
      hWV hV₀W hW hAW hF hF'
    have hy : c * x ∈ Subgroup.normalizer (F : Set G) := by
      refine conjSubgroup_eq_iff_mem_normalizer.1 ?_
      rw [← conjSubgroup_conjSubgroup, hcF, E3.conjSubgroup_inv_conj]
    refine ⟨c⁻¹, (CFixQuot (PSub M V₀ V) V₁ V).inv_mem hc, c * x, ?_, by group⟩
    exact Subgroup.mem_inf.2 ⟨(M ⊓ Subgroup.normalizer (V₂ : Set G)).mul_mem (hCle hc) hx, hy⟩
  · rintro _ ⟨c, hc, y, hy, rfl⟩
    exact (M ⊓ Subgroup.normalizer (V₂ : Set G)).mul_mem (hCle hc)
      (Subgroup.mem_inf.1 hy).1


private theorem exists_eq_one_or_eq_of_card_eq_two {V₀ : Subgroup G} (h : Nat.card V₀ = 2) :
    ∃ z ∈ V₀, z ≠ 1 ∧ ∀ x ∈ V₀, x = 1 ∨ x = z := by
  obtain ⟨z, hz, hz'⟩ := (Nat.card_eq_two_iff' (1 : V₀)).1 h
  refine ⟨z, z.2, fun h1 => hz (Subtype.ext h1), fun x hx => ?_⟩
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  · exact Or.inr (congrArg Subtype.val (hz' ⟨x, hx⟩ fun h => hx1 (congrArg Subtype.val h)))

private theorem conj_eq_of_card_eq_two {M V₀ : Subgroup G}
    (hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G)) (h : Nat.card V₀ = 2) {g : G} (hg : g ∈ M)
    {x : G} (hx : x ∈ V₀) : g * x * g⁻¹ = x := by
  obtain ⟨z, hzV, hz1, hz⟩ := exists_eq_one_or_eq_of_card_eq_two h
  have hgz : g * z * g⁻¹ = z := by
    rcases hz _ ((Subgroup.mem_normalizer_iff.1 (hM₀ hg) z).1 hzV) with h1 | h1
    · exact absurd (conj_eq_one_iff.1 h1) hz1
    · exact h1
  rcases hz x hx with rfl | rfl
  · simp
  · exact hgz

private theorem exists_axis_of_transvection {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV₀ : V₀ ≤ V) (hcard : Nat.card V₀ = 2) (hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G))
    {a : G} (ha : a ∈ F11.CTilde M V₀ V) (hna : a ∉ Subgroup.centralizer (V : Set G)) :
    ∃ W : Subgroup G, W ≤ V ∧ V₀ ≤ W ∧ W.relIndex V = 2 ∧
      ∀ z ∈ V₀, ∃ a' ∈ Subgroup.zpowers a, InducesTransvection V W z a' := by
  obtain ⟨haM, -, haV⟩ := mem_cTilde_iff_comm.1 ha
  obtain ⟨z₀, hz₀V, hz₀1, hz₀⟩ := exists_eq_one_or_eq_of_card_eq_two hcard
  have hcomm : ∀ {x y : G}, x ∈ V → y ∈ V → x * y = y * x := fun {x y} hx hy => by
    simpa using hV.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
  have hmul : ∀ b ∈ V, ∀ v ∈ V,
      a * (b * v) * a⁻¹ * (b * v)⁻¹ = (a * b * a⁻¹ * b⁻¹) * (a * v * a⁻¹ * v⁻¹) := by
    intro b hb v hv
    have hbc : b⁻¹ * (a * v * a⁻¹ * v⁻¹) = (a * v * a⁻¹ * v⁻¹) * b⁻¹ :=
      hcomm (V.inv_mem hb) (hV₀ (haV v hv))
    calc a * (b * v) * a⁻¹ * (b * v)⁻¹
        = a * b * a⁻¹ * ((a * v * a⁻¹ * v⁻¹) * b⁻¹) := by group
      _ = a * b * a⁻¹ * (b⁻¹ * (a * v * a⁻¹ * v⁻¹)) := by rw [hbc]
      _ = (a * b * a⁻¹ * b⁻¹) * (a * v * a⁻¹ * v⁻¹) := by group
  set W : Subgroup G := V ⊓ Subgroup.centralizer ({a} : Set G) with hWdef
  have hWmem : ∀ v, v ∈ W ↔ v ∈ V ∧ a * v * a⁻¹ = v := by
    intro v
    rw [hWdef, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h
      exact mul_inv_eq_iff_eq_mul.2 h.symm
    · intro h
      exact (mul_inv_eq_iff_eq_mul.1 h).symm
  have hmemW : ∀ v ∈ W, a * v * a⁻¹ = v := fun v hv => ((hWmem v).1 hv).2
  have hnotW : ∀ v ∈ V, v ∉ W → a * v * a⁻¹ * v⁻¹ = z₀ := by
    intro v hv hvW
    rcases hz₀ _ (haV v hv) with h | h
    · exact absurd ((hWmem v).2 ⟨hv, mul_inv_eq_one.1 h⟩) hvW
    · exact h
  have hz₀W : ∀ v ∈ V, v ∉ W → a * v * a⁻¹ = z₀ * v := by
    intro v hv hvW
    calc a * v * a⁻¹ = (a * v * a⁻¹ * v⁻¹) * v := by group
      _ = z₀ * v := by rw [hnotW v hv hvW]
  obtain ⟨v₁, hv₁V, hv₁W⟩ : ∃ v₁ ∈ V, v₁ ∉ W := by
    by_contra hall
    push Not at hall
    refine hna (Subgroup.mem_centralizer_iff.2 fun v hv => ?_)
    exact (mul_inv_eq_iff_eq_mul.1 ((hWmem v).1 (hall v hv)).2).symm
  have hz₀sq : z₀ * z₀ = 1 := by
    rw [← pow_two]
    exact hV.2 z₀ (hV₀ hz₀V)
  have hrel : W.relIndex V = 2 := by
    refine Subgroup.relIndex_eq_two_iff.2 ⟨v₁, hv₁V, fun b hb => ?_⟩
    have hbv := hmul b hb v₁ hv₁V
    have hc₁ := hnotW v₁ hv₁V hv₁W
    by_cases hbW : b ∈ W
    · have hnot : b * v₁ ∉ W := by
        intro hW'
        have h1 : a * (b * v₁) * a⁻¹ * (b * v₁)⁻¹ = 1 := mul_inv_eq_one.2 (hmemW _ hW')
        rw [hbv, mul_inv_eq_one.2 (hmemW b hbW), hc₁, one_mul] at h1
        exact hz₀1 h1
      exact Or.inr ⟨hbW, hnot⟩
    · have hmem : b * v₁ ∈ W := by
        refine (hWmem _).2 ⟨V.mul_mem hb hv₁V, ?_⟩
        have h1 : a * (b * v₁) * a⁻¹ * (b * v₁)⁻¹ = 1 := by
          rw [hbv, hnotW b hb hbW, hc₁, hz₀sq]
        exact mul_inv_eq_one.1 h1
      exact Or.inl ⟨hmem, hbW⟩
  have hV₀W : V₀ ≤ W := fun x hx =>
    (hWmem x).2 ⟨hV₀ hx, conj_eq_of_card_eq_two hM₀ hcard haM hx⟩
  refine ⟨W, inf_le_left, hV₀W, hrel, fun z hz => ?_⟩
  rcases hz₀ z hz with rfl | rfl
  · exact ⟨1, Subgroup.one_mem _, fun w _ => by simp, fun v _ _ => by simp⟩
  · exact ⟨a, Subgroup.mem_zpowers a, hmemW, hz₀W⟩


@[expose] def S14c (M V₀ V : Subgroup G) : Prop :=
  ∀ U : Subgroup G, U ≤ V → U ≠ ⊥ →
    M ⊓ Subgroup.centralizer (V : Set G) ≤ M ⊓ Subgroup.normalizer (U : Set G) →
    (∀ m ∈ M, ∃ x ∈ M ⊓ Subgroup.normalizer (U : Set G), ∃ c ∈ F11.CTilde M V₀ V, m = x * c) →
    Subgroup.normalizer (U : Set G) ≤ M

private theorem one_lt_enat_natCast_iff (n : ℕ) : 1 < (n : ℕ∞) ↔ 1 < n := by
  rw [← ENat.natCast_one, ENat.natCast_lt_natCast]

private theorem two_le_enat_natCast_iff (n : ℕ) : 2 ≤ (n : ℕ∞) ↔ 2 ≤ n := by
  rw [show (2 : ℕ∞) = ((2 : ℕ) : ℕ∞) from rfl, ENat.natCast_le_natCast]

private theorem one_lt_of_two_le_enat {x : ℕ∞} (h : 2 ≤ x) : 1 < x := by
  induction x using ENat.recTopCoe with
  | top => exact ENat.one_lt_top
  | coe n =>
    rw [two_le_enat_natCast_iff] at h
    rw [one_lt_enat_natCast_iff]
    omega

theorem rMV_gt_one_iff {M V : Subgroup G} :
    1 < rMV M V ↔ ∀ U : Subgroup G, U ≤ V → E3.mQuot V U ≤ 1 → centralizer (U : Set G) ≤ M := by
  unfold rMV
  constructor
  · intro h U hUV hle
    by_contra hnot
    have h1 : (⨅ U ∈ {U : Subgroup G | U ≤ V ∧ ¬centralizer (U : Set G) ≤ M},
        (E3.mQuot V U : ℕ∞)) ≤ (E3.mQuot V U : ℕ∞) :=
      le_trans (iInf_le _ U) (iInf_le _ ⟨hUV, hnot⟩)
    have h2 : 1 < (E3.mQuot V U : ℕ∞) := lt_of_lt_of_le h h1
    rw [one_lt_enat_natCast_iff] at h2
    omega
  · intro h
    refine one_lt_of_two_le_enat ?_
    refine le_iInf fun U => le_iInf fun hU => ?_
    rw [two_le_enat_natCast_iff]
    by_contra hle
    push Not at hle
    exact hU.2 (h U hU.1 (by omega))


theorem fourteen_three {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (hcard : Nat.card V₀ = 2) (hM : M ≤ Subgroup.normalizer (V : Set G))
    (hMV₀ : M = Subgroup.normalizer (V₀ : Set G)) (hgen : ConjGenerated M V₀ V)
    (hS : S14c M V₀ V)
    (ha : ∃ a ∈ F11.CTilde M V₀ V, a ∉ Subgroup.centralizer (V : Set G)) :
    ∀ U : Subgroup G, U ≤ V → E3.mQuot V U ≤ 1 → Subgroup.centralizer (U : Set G) ≤ M := by
  intro U hUV hmU
  have hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G) := hMV₀.le
  have hC₀ : Subgroup.centralizer (V₀ : Set G) ≤ M :=
    (Subgroup.centralizer_le_normalizer _).trans hMV₀.ge
  by_cases hU₀ : V₀ ≤ U
  · exact (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hU₀)).trans hC₀
  obtain ⟨a, haC, hna⟩ := ha
  obtain ⟨W, hWV, hV₀W, hW, hAW⟩ := exists_axis_of_transvection hV hV₀ hcard hM₀ haC hna
  obtain ⟨haM, -, -⟩ := mem_cTilde_iff_comm.1 haC
  have hpV : IsPGroup 2 V := fun y => ⟨1, Subtype.ext (by simpa using hV.2 y y.2)⟩
  have hinf : U ⊓ V₀ = ⊥ := by
    obtain ⟨z, -, -, hz⟩ := exists_eq_one_or_eq_of_card_eq_two hcard
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxU, hxV₀⟩ := Subgroup.mem_inf.1 hx
    rcases hz x hxV₀ with h | h
    · exact Subgroup.mem_bot.2 h
    · exfalso
      refine hU₀ fun y hy => ?_
      rcases hz y hy with rfl | rfl
      · exact U.one_mem
      · rw [← h]
        exact hxU
  have hsup : U ⊔ V₀ = V := by
    have hle : U ⊔ V₀ ≤ V := sup_le hUV hV₀
    have hne : U ≠ U ⊔ V₀ := fun h => hU₀ (by rw [h]; exact le_sup_right)
    have hpos : E3.mQuot (U ⊔ V₀) U ≠ 0 := fun h0 =>
      hne ((E3.mQuot_eq_zero_iff (hpV.to_le hle) le_sup_left).1 h0)
    have hadd := E3.mQuot_add le_sup_left hle
    have h0 : E3.mQuot V (U ⊔ V₀) = 0 := by omega
    exact (E3.mQuot_eq_zero_iff hpV hle).1 h0
  have hF : U ∈ FamV V₀ ⊥ V := ⟨hUV, hsup, hinf⟩
  have hAP : Subgroup.zpowers a ≤ PSub M V₀ V := by
    refine Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨haC, Subgroup.mem_inf.2 ⟨haM, ?_⟩⟩)
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    exact (mul_inv_eq_iff_eq_mul.1 (conj_eq_of_card_eq_two hM₀ hcard haM hh)).symm
  have hAV₁ : ∀ a' ∈ Subgroup.zpowers a, ∀ v ∈ V, a' * v * a'⁻¹ * v⁻¹ ∈ V₀ := fun a' ha' v hv =>
    (mem_cTilde_iff_comm.1 (Subgroup.zpowers_le.2 haC ha')).2.2 v hv
  have hprod := fourteen_two_product (A := Subgroup.zpowers a) hV hV₀ le_rfl (inf_bot_eq _)
    (sup_bot_eq _) hM hM₀ hM₀ hgen hAP hAV₁ hWV hV₀W hW hAW hF
  have hUbot : U ≠ ⊥ := by
    intro h
    rw [h, bot_sup_eq] at hsup
    have hVW : V ≤ W := hsup ▸ hV₀W
    rw [le_antisymm hWV hVW, Subgroup.relIndex_self] at hW
    exact absurd hW (by norm_num)
  have hNbot : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ := Subgroup.normalizer_eq_top _
  refine (Subgroup.centralizer_le_normalizer _).trans (hS U hUV hUbot ?_ ?_)
  · exact inf_le_inf_left M
      ((Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hUV)).trans
        (Subgroup.centralizer_le_normalizer _))
  · intro m hm
    have hm' : m⁻¹ ∈ ((M ⊓ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) : Subgroup G) :
        Set G) := Subgroup.mem_inf.2 ⟨M.inv_mem hm, by rw [hNbot]; exact Subgroup.mem_top _⟩
    rw [hprod] at hm'
    obtain ⟨c, hc, y, hy, hcy⟩ := hm'
    have hcy' : c * y = m⁻¹ := hcy
    obtain ⟨hyMN, hyU⟩ := Subgroup.mem_inf.1 hy
    have hyM : y ∈ M := (Subgroup.mem_inf.1 hyMN).1
    refine ⟨y⁻¹, Subgroup.mem_inf.2 ⟨M.inv_mem hyM, Subgroup.inv_mem _ hyU⟩, c⁻¹,
      (F11.CTilde M V₀ V).inv_mem (Subgroup.mem_inf.1 hc.1).1, ?_⟩
    rw [← mul_inv_rev, hcy', inv_inv]

theorem fourteen_three_rMV {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (hcard : Nat.card V₀ = 2) (hM : M ≤ Subgroup.normalizer (V : Set G))
    (hMV₀ : M = Subgroup.normalizer (V₀ : Set G)) (hgen : ConjGenerated M V₀ V)
    (hS : S14c M V₀ V)
    (ha : ∃ a ∈ F11.CTilde M V₀ V, a ∉ Subgroup.centralizer (V : Set G)) :
    1 < rMV M V :=
  rMV_gt_one_iff.2 (fourteen_three hV hV₀ hcard hM hMV₀ hgen hS ha)

end FourteenTwo

end CFSG.LocalAnalysis.WeakClosure81
