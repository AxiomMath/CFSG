module

public import CFSG.Quasithin.EmptyFaithful.S153EDefs
public import CFSG.Quasithin.EmptyFaithful.S153EO4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E

section Basic

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem Q_le_T (cx : Ctx15350 T Mc M V₁ V₂ t) : pCoreOf 2 Mc ≤ T :=
  pCoreOf_two_le_of_isSylowTwoOf cx.hF.sylow_H

theorem U_le_Q (cx : Ctx15350 T Mc M V₁ V₂ t) : UH153 T M V₁ Mc ≤ pCoreOf 2 Mc :=
  cx.hF.conjClosure_Vp_le_pCoreOf

theorem U_le_T (cx : Ctx15350 T Mc M V₁ V₂ t) : UH153 T M V₁ Mc ≤ T :=
  (U_le_Q cx).trans (Q_le_T cx)

theorem T_le_Mc (cx : Ctx15350 T Mc M V₁ V₂ t) : T ≤ Mc := cx.hF.T_le_H

theorem T_le_M (cx : Ctx15350 T Mc M V₁ V₂ t) : T ≤ M := cx.c.hyp.T_le

theorem T_le_N (cx : Ctx15350 T Mc M V₁ V₂ t) : T ≤ Subgroup.normalizer (VZ T M : Set G) :=
  (T_le_M cx).trans cx.c.hyp.le_normalizer

theorem Q_le_N (cx : Ctx15350 T Mc M V₁ V₂ t) : pCoreOf 2 Mc ≤ Subgroup.normalizer (VZ T M : Set G) :=
  (Q_le_T cx).trans (T_le_N cx)

theorem U_le_N (cx : Ctx15350 T Mc M V₁ V₂ t) : UH153 T M V₁ Mc ≤ Subgroup.normalizer (VZ T M : Set G) :=
  (U_le_T cx).trans (T_le_N cx)

omit [Finite G] in
theorem U_conj_mem {g u : G} (hg : g ∈ Mc) (hu : u ∈ UH153 T M V₁ Mc) :
    g * u * g⁻¹ ∈ UH153 T M V₁ Mc :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ hg) u).mp hu

theorem Z_le_centralizer (cx : Ctx15350 T Mc M V₁ V₂ t) :
    quasithinOmegaOneCenter T ≤ Subgroup.centralizer (VZ T M : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact B2F.isElemAbelian_comm cx.c.hyp.elemAbelian hv (cx.c.hyp.Z_le_VZ hz)

theorem ZS_le_U (_cx : Ctx15350 T Mc M V₁ V₂ t) : ZS153 T M V₁ ≤ UH153 T M V₁ Mc :=
  le_conjClosure _ _

theorem ZS_le_V (_cx : Ctx15350 T Mc M V₁ V₂ t) : ZS153 T M V₁ ≤ VZ T M := inf_le_left

theorem Z_le_ZS (cx : Ctx15350 T Mc M V₁ V₂ t) : quasithinOmegaOneCenter T ≤ ZS153 T M V₁ :=
  cx.hF.V₁_le_Vp

theorem commutator_U_mem (cx : Ctx15350 T Mc M V₁ V₂ t) {u u' : G} (hu : u ∈ UH153 T M V₁ Mc)
    (hu' : u' ∈ UH153 T M V₁ Mc) : u * u' * u⁻¹ * u'⁻¹ ∈ quasithinOmegaOneCenter T :=
  cx.hF.commutator_conjClosure_le u hu u' (U_le_Q cx hu')

theorem sq_U_mem (cx : Ctx15350 T Mc M V₁ V₂ t) {u : G} (hu : u ∈ UH153 T M V₁ Mc) :
    u * u ∈ quasithinOmegaOneCenter T := by
  have := cx.hF.sq_mem_conjClosure u hu
  rwa [pow_two] at this

end Basic

section Bar

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem autI_U_le_T (cx : Ctx15350 T Mc M V₁ V₂ t) :
    autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc) ≤ autI cx.c.hyp.elemAbelian T :=
  autI_mono _ (U_le_T cx)

theorem autI_U_normal (cx : Ctx15350 T Mc M V₁ V₂ t) {h n : MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian)}
    (hh : h ∈ autI cx.c.hyp.elemAbelian T) (hn : n ∈ autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc)) :
    h * n * h⁻¹ ∈ autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc) := by
  obtain ⟨g, hgT, rfl⟩ := (mem_autI cx.c.hyp.elemAbelian).1 hh
  obtain ⟨u, huU, rfl⟩ := (mem_autI cx.c.hyp.elemAbelian).1 hn
  have hmem : (g : G) * u * (g : G)⁻¹ ∈ UH153 T M V₁ Mc := U_conj_mem (T_le_Mc cx hgT) huU
  have hN : (g : G) * u * (g : G)⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) :=
    (Subgroup.normalizer (VZ T M : Set G)).mul_mem
      ((Subgroup.normalizer (VZ T M : Set G)).mul_mem g.2 u.2)
      ((Subgroup.normalizer (VZ T M : Set G)).inv_mem g.2)
  have := convI_mem_autI cx.c.hyp.elemAbelian hmem hN
  have e : (⟨(g : G) * u * (g : G)⁻¹, hN⟩ : Subgroup.normalizer (VZ T M : Set G)) = g * u * g⁻¹ :=
    Subtype.ext rfl
  rw [e, map_mul, map_mul, map_inv] at this
  exact this

theorem autI_U_comm (cx : Ctx15350 T Mc M V₁ V₂ t) {a b : MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian)}
    (ha : a ∈ autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc))
    (hb : b ∈ autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc)) : a * b = b * a := by
  obtain ⟨u, hu, rfl⟩ := (mem_autI cx.c.hyp.elemAbelian).1 ha
  obtain ⟨u', hu', rfl⟩ := (mem_autI cx.c.hyp.elemAbelian).1 hb
  have hc := Z_le_centralizer cx (commutator_U_mem cx hu hu')
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement,
    convI_eq_one_iff cx.c.hyp.elemAbelian]
  simpa [commutatorElement_def] using hc

theorem autI_U_sq (cx : Ctx15350 T Mc M V₁ V₂ t) {a : MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian)}
    (ha : a ∈ autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc)) : a * a = 1 := by
  obtain ⟨u, hu, rfl⟩ := (mem_autI cx.c.hyp.elemAbelian).1 ha
  have hc := Z_le_centralizer cx (sq_U_mem cx hu)
  rw [← map_mul, convI_eq_one_iff cx.c.hyp.elemAbelian]
  simpa using hc

theorem exists_ne_one_autI_U (cx : Ctx15350 T Mc M V₁ V₂ t) (h1 : ¬ VZ T M ≤ pCoreOf 2 Mc) :
    ∃ n ∈ autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc), n ≠ 1 := by
  by_contra hcon
  push Not at hcon
  apply h1
  refine cx.hF.le_pCoreOf_iff_le_centralizer.mpr fun v hv =>
    ⟨cx.hF.V_le_H hv, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  have hN : u ∈ Subgroup.normalizer (VZ T M : Set G) := U_le_N cx hu
  have h2 : convI cx.c.hyp.elemAbelian ⟨u, hN⟩ = 1 :=
    hcon _ (convI_mem_autI cx.c.hyp.elemAbelian hu hN)
  exact ((Subgroup.mem_centralizer_iff.mp ((convI_eq_one_iff cx.c.hyp.elemAbelian _).1 h2) v hv)).symm

end Bar


section Parts

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem not_le_pCoreOf (cx : Ctx15350 T Mc M V₁ V₂ t) (hn : NonabelianVH153 T M Mc) :
    ¬ VZ T M ≤ pCoreOf 2 Mc := by
  intro hVQ
  have hab : IsElemAbelian 2 (conjClosure (VZ T M) Mc) := by
    refine HypF91.isElemAbelian_conjClosure_of_forall cx.c.hyp.elemAbelian fun k hk => ?_
    have h1 : conjSub k (VZ T M) ≤ pCoreOf 2 Mc := cx.hF.conjSub_le_pCoreOf hVQ hk
    have h2 : conjSub k (VZ T M) ≤ M := h1.trans ((Q_le_T cx).trans (T_le_M cx))
    have h3 : conjSubgroup (VZ T M) k⁻¹ ≤ M := by
      rw [← conjSub_inv_eq_conjSubgroup, inv_inv]
      exact h2
    have h4 := cx.r46.conj_le_centralizer k⁻¹ h3
    rw [← conjSub_inv_eq_conjSubgroup, inv_inv] at h4
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (h4 hy) v hv).symm
  obtain ⟨a, ha, b, hb, hne⟩ := hn
  exact hne (B2F.isElemAbelian_comm hab ha hb)

theorem four_Q (cx : Ctx15350 T Mc M V₁ V₂ t) : ⁅VZ T M, pCoreOf 2 Mc⁆ ≤ VZ T M ⊓ pCoreOf 2 Mc :=
  F7.commutator_le_inf_of_normalizes
    (cx.hF.V_le_H.trans (le_normalizer_pCoreOf 2 Mc)) (Q_le_N cx)

theorem four_U (cx : Ctx15350 T Mc M V₁ V₂ t) :
    ⁅VZ T M, UH153 T M V₁ Mc⁆ ≤ VZ T M ⊓ UH153 T M V₁ Mc :=
  F7.commutator_le_inf_of_normalizes
    (cx.hF.V_le_H.trans (le_normalizer_conjClosure _ _)) (U_le_N cx)

theorem exists_bar_model (cx : Ctx15350 T Mc M V₁ V₂ t) :
    ∃ (L₁ L₂ : Subgroup (MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian)))
      (tb s₁ s₂ τ : MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian))
      (a₁ a₂ : IntMod (VZ T M) cx.c.hyp.elemAbelian),
      OfourStruct (autI cx.c.hyp.elemAbelian M) L₁ L₂ tb ∧
      OfourStruct.SylowFacts L₁ L₂ (autI cx.c.hyp.elemAbelian T) s₁ s₂ τ a₁ a₂ ∧
      (commV L₁).map (inclMod cx.c.hyp.elemAbelian) = V₁ ∧
      (commV L₂).map (inclMod cx.c.hyp.elemAbelian) = V₂ := by
  obtain ⟨hV, L₁, L₂, tb, hS, hV₁, hV₂, -⟩ := cx.c.decomp.model
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF⟩ := hS.exists_sylowFacts cx.c.hyp.isSylowTwoOf_autI
  exact ⟨L₁, L₂, tb, s₁, s₂, τ, a₁, a₂, hS, hF, hV₁.symm, hV₂.symm⟩

theorem mul_mem_autI_U (cx : Ctx15350 T Mc M V₁ V₂ t) (h1 : ¬ VZ T M ≤ pCoreOf 2 Mc)
    {L₁ L₂ : Subgroup (MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian))}
    {tb s₁ s₂ τ : MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian)}
    {a₁ a₂ : IntMod (VZ T M) cx.c.hyp.elemAbelian}
    (hS : OfourStruct (autI cx.c.hyp.elemAbelian M) L₁ L₂ tb)
    (hF : OfourStruct.SylowFacts L₁ L₂ (autI cx.c.hyp.elemAbelian T) s₁ s₂ τ a₁ a₂) :
    s₁ * s₂ ∈ autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc) :=
  mul_mem_of_normal_ne_bot hS cx.c.hyp.isSylowTwoOf_autI hF (autI_U_le_T cx)
    (fun _ hh _ hn => autI_U_normal cx hh hn) (exists_ne_one_autI_U cx h1)

theorem centerOf_le_autI_U (cx : Ctx15350 T Mc M V₁ V₂ t) (h1 : ¬ VZ T M ≤ pCoreOf 2 Mc)
    {L₁ L₂ : Subgroup (MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian))}
    {tb s₁ s₂ τ : MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian)}
    {a₁ a₂ : IntMod (VZ T M) cx.c.hyp.elemAbelian}
    (hS : OfourStruct (autI cx.c.hyp.elemAbelian M) L₁ L₂ tb)
    (hF : OfourStruct.SylowFacts L₁ L₂ (autI cx.c.hyp.elemAbelian T) s₁ s₂ τ a₁ a₂) :
    centerOf (autI cx.c.hyp.elemAbelian T) ≤ autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc) := by
  intro z hz
  have hcen : ∀ x ∈ autI cx.c.hyp.elemAbelian T, x * z = z * x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp hz.2 x hx
  rcases eq_one_or_mul_of_central hS cx.c.hyp.isSylowTwoOf_autI hF hz.1 hcen with h | h
  · rw [h]
    exact Subgroup.one_mem _
  · rw [h]
    exact mul_mem_autI_U cx h1 hS hF

end Parts

end S153E

end CFSG.Quasithin
