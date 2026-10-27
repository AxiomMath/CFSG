module

public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LieType.Steinberg.CentralExt.SLMilnor
public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import TauCeti.GroupTheory.QuotientGroup.KerEquiv
public import CFSG.Assembly.Subnormal
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.StandardType.TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

section Central

variable {G : Type*} [Group G]

theorem commutatorElement_mul_central {a b z w : G} (hz : z ∈ Subgroup.center G)
    (hw : w ∈ Subgroup.center G) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz' := Subgroup.mem_center_iff.mp hz
  have hw' := Subgroup.mem_center_iff.mp hw
  have hzw : z * w * z⁻¹ = w := by rw [← hz' w, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
      = a * (z * b) * w * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by group
    _ = a * b * (z * w * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by rw [← hz' b]; group
    _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by rw [hzw]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [← hw' a⁻¹]; group

theorem eq_of_inv_mul_mem_center {S : Type*} [Group S] (hS : commutator S = ⊤) (α β : S →* G)
    (h : ∀ s, (α s)⁻¹ * β s ∈ Subgroup.center G) : α = β := by
  let f : S →* G :=
    { toFun := fun s => (α s)⁻¹ * β s
      map_one' := by simp
      map_mul' := fun s t => by
        have hc := Subgroup.mem_center_iff.mp (h s)
        simp only [map_mul, _root_.mul_inv_rev]
        calc (α t)⁻¹ * (α s)⁻¹ * (β s * β t) = (α t)⁻¹ * ((α s)⁻¹ * β s) * β t := by group
          _ = ((α s)⁻¹ * β s) * (α t)⁻¹ * β t := by rw [hc (α t)⁻¹]
          _ = (α s)⁻¹ * β s * ((α t)⁻¹ * β t) := by group }
  have hf : ∀ s, f s = (α s)⁻¹ * β s := fun _ => rfl
  have hker : commutator S ≤ f.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (h b)) (f a)
  ext s
  have h1 : f s = 1 := hker (hS ▸ Subgroup.mem_top s)
  rw [hf] at h1
  exact inv_mul_eq_one.mp h1

end Central

section LiftAction

variable {d : ℕ} {K : Type*} [Field K] {L' : Type*} [Group L']
  {φ : SpecialLinearGroup (Fin d) K →* L'}

theorem act_of_lift_of_mulAut (hperfSL : commutator (SpecialLinearGroup (Fin d) K) = ⊤)
    {ψ : L' →* projectiveSL d K} (hker : ψ.ker ≤ Subgroup.center L')
    (hφ : ∀ g, ψ (φ g) = proj d K g)
    {a : MulAut L'} {γ : MulAut (SpecialLinearGroup (Fin d) K)}
    {ψA : MulAut (projectiveSL d K)}
    (hψ : ∀ s, ψA (proj d K s) = proj d K (γ s))
    (hind : ∀ l, ψA (ψ l) = ψ (a l)) :
    ∀ s, a (φ s) = φ (γ s) := by
  have h1 := eq_of_inv_mul_mem_center hperfSL ((a : L' →* L').comp φ)
    (φ.comp γ.toMonoidHom) (fun s => hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      change (ψ (a (φ s)))⁻¹ * ψ (φ (γ s)) = 1
      rw [← hind, hφ, hφ, hψ, inv_mul_cancel]))
  intro s
  exact congrArg (fun f : SpecialLinearGroup (Fin d) K →* L' => f s) h1

end LiftAction

variable {d : ℕ} {K : Type} [Field K]

variable (d K) in
@[expose] def SLHasSections : Prop :=
  ∀ (E : Type) [Group E] (π : E →* SpecialLinearGroup (Fin d) K), Function.Surjective π →
    π.ker ≤ Subgroup.center E → ∃ σ : SpecialLinearGroup (Fin d) K →* E, ∀ g, π (σ g) = g

theorem slHasSections_of_five_le [Finite K] (hd : 5 ≤ d) : SLHasSections d K := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  intro E _ π hπ hcen
  exact CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_four_le (by omega) hπ hcen

theorem slHasSections_of_card [Finite K] (hd : 3 ≤ d) (h2 : Nat.card K ≠ 2)
    (h34 : ¬(d = 3 ∧ Nat.card K = 4)) (h43 : ¬(d = 4 ∧ Nat.card K = 3)) : SLHasSections d K := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  intro E _ π hπ hcen
  exact CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_separating (by omega)
    (CFSG.LieType.Steinberg.CentralExt.SLClosed.separating_of_card (by omega) h2 (by omega)
      (by omega)) hπ hcen

theorem exists_sl_cover (hsec : SLHasSections d K) {L' : Type} [Group L']
    (ψ : L' →* projectiveSL d K) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) :
    ∃ φ : SpecialLinearGroup (Fin d) K →* L', Function.Surjective φ ∧
      ∀ g, ψ (φ g) = proj d K g := by
  let E : Subgroup (L' × SpecialLinearGroup (Fin d) K) :=
    MonoidHom.eqLocus (ψ.comp (MonoidHom.fst L' (SpecialLinearGroup (Fin d) K)))
      ((proj d K).comp (MonoidHom.snd L' (SpecialLinearGroup (Fin d) K)))
  let π : E →* SpecialLinearGroup (Fin d) K :=
    (MonoidHom.snd L' (SpecialLinearGroup (Fin d) K)).comp E.subtype
  have hπ : Function.Surjective π := by
    intro s
    obtain ⟨l, hl⟩ := hψ (proj d K s)
    exact ⟨⟨(l, s), hl⟩, rfl⟩
  have hcen : π.ker ≤ Subgroup.center E := by
    rintro ⟨⟨l, s⟩, hx⟩ hk
    have hs : s = 1 := hk
    have hx' : ψ l = proj d K s := hx
    have hl : l ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, hx', hs, map_one]
    rw [Subgroup.mem_center_iff]
    rintro ⟨⟨l', s'⟩, hy⟩
    apply Subtype.ext
    change (l' * l, s' * s) = (l * l', s * s')
    rw [hs, one_mul, mul_one, (Subgroup.mem_center_iff.mp (hker hl)) l']
  obtain ⟨σ, hσ⟩ := hsec E π hπ hcen
  let φ : SpecialLinearGroup (Fin d) K →* L' :=
    (MonoidHom.fst L' (SpecialLinearGroup (Fin d) K)).comp (E.subtype.comp σ)
  have hφ : ∀ g, ψ (φ g) = proj d K g := by
    intro g
    have h1 : ψ ((σ g : L' × SpecialLinearGroup (Fin d) K).1) =
        proj d K ((σ g : L' × SpecialLinearGroup (Fin d) K).2) := (σ g).2
    have h2 : (σ g : L' × SpecialLinearGroup (Fin d) K).2 = g := hσ g
    change ψ ((σ g : L' × SpecialLinearGroup (Fin d) K).1) = _
    rw [h1, h2]
  refine ⟨φ, ?_, hφ⟩
  have hdecomp : ∀ l : L', ∃ s, (φ s)⁻¹ * l ∈ Subgroup.center L' := by
    intro l
    obtain ⟨s, hs⟩ := proj_surjective d K (ψ l)
    refine ⟨s, hker ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, hs, inv_mul_cancel]
  have htop : (⊤ : Subgroup L') ≤ φ.range := by
    rw [← hperf, _root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨s, hs⟩ := hdecomp a
    obtain ⟨t, ht⟩ := hdecomp b
    refine ⟨⁅s, t⁆, ?_⟩
    rw [map_commutatorElement]
    have ha : a = φ s * ((φ s)⁻¹ * a) := by group
    have hb : b = φ t * ((φ t)⁻¹ * b) := by group
    rw [ha, hb, commutatorElement_mul_central hs ht]
  intro l
  exact htop (Subgroup.mem_top l)

section ScalarKernel

variable {d : ℕ} {K : Type} [Field K] {L : Type} [Group L]

theorem comap_center_eq_of_scalarKernel (hd : 3 ≤ d)
    (χ : SpecialLinearGroup (Fin d) K →* L) (hχ : Function.Surjective χ)
    (hker : χ.ker ≤ scalars d K) :
    (Subgroup.center L).comap χ = Subgroup.center (SpecialLinearGroup (Fin d) K) := by
  have hperf : Group.IsPerfect (SpecialLinearGroup (Fin d) K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le hd
  exact CFSG.LocalCores.comap_center_eq_of_perfect hperf χ hχ
    (hker.trans (scalars_le_center (n := d) (K := K)))

theorem ker_mk_center_comp_of_scalarKernel (hd : 3 ≤ d)
    (χ : SpecialLinearGroup (Fin d) K →* L) (hχ : Function.Surjective χ)
    (hker : χ.ker ≤ scalars d K) :
    ((QuotientGroup.mk' (Subgroup.center L)).comp χ).ker = scalars d K := by
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
    comap_center_eq_of_scalarKernel hd χ hχ hker, scalars_eq_center]

@[expose] noncomputable def centerQuotEquivOfScalarKernel (hd : 3 ≤ d)
    (χ : SpecialLinearGroup (Fin d) K →* L) (hχ : Function.Surjective χ)
    (hker : χ.ker ≤ scalars d K) :
    projectiveSL d K ≃* L ⧸ Subgroup.center L :=
  (QuotientGroup.quotientMulEquivOfEq
      (ker_mk_center_comp_of_scalarKernel hd χ hχ hker).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((QuotientGroup.mk'_surjective (Subgroup.center L)).comp hχ))

theorem centerQuotEquivOfScalarKernel_proj (hd : 3 ≤ d)
    (χ : SpecialLinearGroup (Fin d) K →* L) (hχ : Function.Surjective χ)
    (hker : χ.ker ≤ scalars d K) (g : SpecialLinearGroup (Fin d) K) :
    centerQuotEquivOfScalarKernel hd χ hχ hker (proj d K g) =
      QuotientGroup.mk' (Subgroup.center L) (χ g) := by
  rw [centerQuotEquivOfScalarKernel, MulEquiv.trans_apply,
    show proj d K g = QuotientGroup.mk g from rfl,
    QuotientGroup.quotientMulEquivOfEq_mk]
  exact TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk _ _ g

end ScalarKernel

end CFSG.StandardType.TypeA
