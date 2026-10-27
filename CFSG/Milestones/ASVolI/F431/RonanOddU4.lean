module

public import CFSG.Milestones.ASVolI.F4Conjugacy
public import CFSG.Quasithin.Background.RonanF438Ctx
public import CFSG.Quasithin.Background.RonanF57Flags
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Quasithin.Background.RonanF57Outer

public section

namespace CFSG.ASVolI

open scoped Pointwise
open Matrix CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.Quasithin.RonanF57

section Flag

private theorem ronOdd_parabolic_desc {E : Type} [Group E] {Gp : Subgroup E}
    (m₁ : ClassicalRoots.Marking .U4 2 1 ↥Gp) (second : Bool) (F : Set (Fin 4))
    (hF : (if second then ClassicalRoots.flagTwo .U4 else ClassicalRoots.flagOne .U4) = F)
    (P : Subgroup E) (hP : (m₁.parabolic second).map Gp.subtype = P) (x : ↥Gp) :
    (x : E) ∈ P ↔ ∃ s : ↥(StatedSU 4 2 m₁.field), m₁.identification (QuotientGroup.mk s) = x ∧
      ∀ u : Fin 4 → m₁.field, ((s : GL (Fin 4) m₁.field) : Matrix (Fin 4) (Fin 4) m₁.field) *ᵥ u ∈
          ((fun v => (m₁.basis : Matrix (Fin 4) (Fin 4) m₁.field) *ᵥ v) ''
            {v : Fin 4 → m₁.field | ∀ pos, pos ∉ F → v pos = 0}) ↔
        u ∈ ((fun v => (m₁.basis : Matrix (Fin 4) (Fin 4) m₁.field) *ᵥ v) ''
            {v : Fin 4 → m₁.field | ∀ pos, pos ∉ F → v pos = 0}) := by
  subst hF
  rw [← hP]
  constructor
  · rintro ⟨y, ⟨s, hs, rfl⟩, hy⟩
    refine ⟨s, Subtype.ext hy, ?_⟩
    exact (burnsideF4d_Y1_mem_rawStabilizer (K := m₁.field) (index := Fin 4) _
      (s : GL (Fin 4) m₁.field)).1 hs
  · rintro ⟨s, hsx, hstab⟩
    refine ⟨m₁.transport s, ⟨s, (burnsideF4d_Y1_mem_rawStabilizer (K := m₁.field) (index := Fin 4) _
      (s : GL (Fin 4) m₁.field)).2 hstab, rfl⟩, ?_⟩
    rw [← hsx]
    rfl

private theorem ronOdd_parabolicAt {E : Type} [Group E] {Gp : Subgroup E}
    (m₁ : ClassicalRoots.Marking .U4 2 1 ↥Gp) (second : Bool) (F : Set (Fin 4))
    (hF : (if second then ClassicalRoots.flagTwo .U4 else ClassicalRoots.flagOne .U4) = F)
    (P : Subgroup E) (hPG : P ≤ Gp) (hP : (m₁.parabolic second).map Gp.subtype = P)
    (space : Submodule m₁.field (Fin 4 → m₁.field))
    (hspace : (space : Set (Fin 4 → m₁.field)) =
      (fun v => (m₁.basis : Matrix (Fin 4) (Fin 4) m₁.field) *ᵥ v) ''
        {v : Fin 4 → m₁.field | ∀ pos, pos ∉ F → v pos = 0}) :
    CFSG.Quasithin.SimsF5.U42ParabolicAt Gp P
      (m₁.identification.symm : ↥Gp ≃* StatedProj (StatedSU 4 2 m₁.field)) space := by
  have hmem : ∀ w : Fin 4 → m₁.field, w ∈ space ↔
      w ∈ ((fun v => (m₁.basis : Matrix (Fin 4) (Fin 4) m₁.field) *ᵥ v) ''
        {v : Fin 4 → m₁.field | ∀ pos, pos ∉ F → v pos = 0}) := fun w => by
    rw [← SetLike.mem_coe, hspace]
  refine ⟨hPG, fun element => ?_⟩
  rw [ronOdd_parabolic_desc m₁ second F hF P hP element]
  simp only [hmem]
  constructor
  · rintro ⟨s, hsx, hstab⟩
    exact ⟨s, (MulEquiv.symm_apply_eq _).2 hsx.symm, hstab⟩
  · rintro ⟨s, hsx, hstab⟩
    exact ⟨s, ((MulEquiv.symm_apply_eq _).1 hsx).symm, hstab⟩

theorem ronOdd_exists_flag {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4g .U4 2 1 Gp M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      ∃ σ : K →+* K, (∀ x, σ x = x ^ 2) ∧
        ∃ (m : ↥Gp ≃* StatedProj (StatedSU 4 2 K)) (point plane : Submodule K (Fin 4 → K)),
          Module.finrank K point = 1 ∧ Module.finrank K plane = 2 ∧ point ≤ plane ∧
          (∀ v ∈ plane, ∀ w ∈ plane, CFSG.Quasithin.SimsF5.U42Hermitian K v w = 0) ∧
          CFSG.Quasithin.SimsF5.U42ParabolicAt Gp (Gp ⊓ M₁) m point ∧
          CFSG.Quasithin.SimsF5.U42ParabolicAt Gp (Gp ⊓ M₂) m plane := by
  classical
  obtain ⟨m₁, hm1, hm2⟩ := burnsideF4g_marking (c := .U4) hyp
  have hK₁ : Nat.card m₁.field = 4 := by simpa using m₁.field_card
  have h₁ := unitaryFieldData_of_card hK₁
  have hB₁ : ((m₁.basis : Matrix (Fin 4) (Fin 4) m₁.field).map h₁.bar)ᵀ *
      (m₁.basis : Matrix (Fin 4) (Fin 4) m₁.field) = antiDiag4 m₁.field := by
    rw [← bar_fun_eq h₁]
    exact m₁.basis_compatible
  have hP1 : (m₁.parabolic false).map Gp.subtype = Gp ⊓ M₁ := by
    rw [← hm1, Subgroup.subgroupOf_map_subtype, inf_comm]
  have hP2 : (m₁.parabolic true).map Gp.subtype = Gp ⊓ M₂ := by
    rw [← hm2, Subgroup.subgroupOf_map_subtype, inf_comm]
  refine ⟨m₁.field, inferInstance, inferInstance, hK₁, h₁.bar, bar_eq_sq h₁,
    (m₁.identification.symm : ↥Gp ≃* StatedProj (StatedSU 4 2 m₁.field)),
    wPoint (m₁.basis : Matrix (Fin 4) (Fin 4) m₁.field),
    wPlane (m₁.basis : Matrix (Fin 4) (Fin 4) m₁.field), finrank_wPoint _, finrank_wPlane _,
    wPoint_le_wPlane _, wPlane_isotropic h₁ hB₁, ?_, ?_⟩
  · exact ronOdd_parabolicAt m₁ false {0} rfl (Gp ⊓ M₁) inf_le_left hP1 _ (wPoint_coe _)
  · exact ronOdd_parabolicAt m₁ true {0, 1} rfl (Gp ⊓ M₂) inf_le_left hP2 _ (wPlane_coe _)

end Flag

theorem isL43_of_lieModel {M : Type} [Group M] (h : CFSG.Blueprint.LieModel M .PSL 4 3 1) :
    IsL43 M := by
  rcases h with ⟨-, -, K, iK, fK, hK, hiso⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact ⟨K, iK, fK, by simpa using hK, hiso⟩
  all_goals exact absurd h (by norm_num)

@[expose] def OddIndexU4 : Prop :=
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 GLKind.U4 1 Gp M₁ M₂ β ε z → ¬ IsL43 M → Odd Gp.index

@[expose] def LieOfAutCtx : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M₁ M₂ : Subgroup G) (z : G),
    CFSG.Quasithin.H13.F431.U42Aut.AutCtx G M₁ M₂ z → CFSG.Blueprint.LieModel G .PSL 4 3 1

section Main


theorem ctx_of_even_index_U4 {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
    {β : Cpl M₁ M₂ Y} {M : Type} [Group M] [Finite M] {ε : Y →* M} {z : M}
    (hyp : HypF_4_31 GLKind.U4 1 Gp M₁ M₂ β ε z) (hev : ¬ Odd Gp.index) :
    Nonempty (CFSG.Quasithin.H13.F431.U42Aut.AutCtx M (MiOne β ε) (MiTwo β ε) z) := by
  classical
  haveI := hyp.amalgam.finite
  haveI := hyp.amalgam.normal
  have hne : Gp ≠ ⊤ := fun h => hev (by rw [h, Subgroup.index_top]; exact odd_one)
  have hout : ∃ n ∈ M₁ ⊓ M₂, n ∉ Gp := by
    obtain ⟨e, he⟩ : ∃ e : E, e ∉ Gp := by
      by_contra h
      push Not at h
      exact hne (eq_top_iff.2 fun x _ => h x)
    obtain ⟨n, hn, h, hh, rfl⟩ := hyp.amalgam.split e
    exact ⟨h, hh, fun hG => he (Gp.mul_mem hn hG)⟩
  obtain ⟨K, iK, fK, hKc, σ, hσ, m, point, plane, hp1, hp2, hpp, hiso, hpar1, hpar2⟩ :=
    ronOdd_exists_flag hyp.amalgam.toHypF_4_4g
  obtain ⟨Θ, hY, h1, h2⟩ := CFSG.Quasithin.RonanF438.exists_fullIso
    hyp.amalgam.centralizer_trivial hne hout hKc hσ m point plane hp1 hp2 hpp hiso hpar1 hpar2
  have hinj₁ : Function.Injective (burnsideF4d_bOne β ε) :=
    (burnsideF4d_amalgIsoM β hyp.faithful ε hyp.inj).inj₁
  have hinj₂ : Function.Injective (burnsideF4d_bTwo β ε) :=
    (burnsideF4d_amalgIsoM β hyp.faithful ε hyp.inj).inj₂
  have hzmem : z ∈ ctr (oPPrime 2 (((Gp ⊓ M₁).subgroupOf M₁).map (burnsideF4d_bOne β ε))) := by
    have := hyp.z_mem.1 (fun h => by cases h)
    rw [burnsideF4d_GiOne_eq] at this
    exact this
  rw [CFSG.Quasithin.SimsF5.nm_oPPrime_map hinj₁, CFSG.Quasithin.SimsF5.nm_ctr_map hinj₁] at hzmem
  obtain ⟨zb, hzb, hzbz⟩ := hzmem
  have hzb1 : zb ≠ 1 := by
    rintro rfl
    exact hyp.z_inv.1 (by rw [← hzbz, map_one])
  have hΘz := CFSG.Quasithin.RonanF438.theta_zb hY h1 hzb hzb1
  obtain ⟨hN1, hN2⟩ := CFSG.Quasithin.RonanF438.hypF431_normalizers hyp
    (CFSG.Quasithin.RonanF438.nmCompat_of_full hY h1 h2)
  have hres : pResidual 2 M = ⊤ :=
    CFSG.Quasithin.SimsF5.br_pResidual_eq_top
      (hyp.he.resolve_right fun h => by rcases h.2 with h | h | h <;> cases h)
  let T := burnsideF4d_amalgIsoM β hyp.faithful ε hyp.inj
  exact ⟨CFSG.Quasithin.RonanF438.autCtx_of_compat Θ h1 h2 (burnsideF4d_bOne β ε)
    (burnsideF4d_bTwo β ε) hinj₁ hinj₂ T.range₁ T.range₂ T.agree T.inter zb hzbz hΘz hres
    hyp.hb hN1 hN2⟩

theorem oddIndex_U4_of_lie (hlie : LieOfAutCtx) : OddIndexU4 := by
  intro E _ Gp M₁ M₂ Y _ β M _ ε z hyp hL
  by_contra hev
  haveI := hyp.finite_M
  obtain ⟨c⟩ := ctx_of_even_index_U4 hyp hev
  exact hL (isL43_of_lieModel (hlie M _ _ z c))

end Main

@[expose] def F437FourIIU4 : Prop :=
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M)
    (hyp : HypF_4_31 GLKind.U4 1 Gp M₁ M₂ β ε z),
    ∀ Tb : Subgroup E, ChF.IsSylowOf 2 Tb (M₁ ⊓ M₂) →
    ∀ fb : ↥(M₁ ⊓ M₂), (fb : E) ∈ Tb →
      (fb : E) ∉ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) → (fb : E) * (fb : E) = 1 →
      ¬ hyp.amalgam.toHypF_4_4g.chart.IsTypeIIIInv (fb : E) →
      ChF.IsSylowOf 2
        (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({(fb : E)} : Set E))
        (cenIn Gp (fb : E)) →
      ¬ ChF.IsSylowOf 2 (imB β ε Tb ⊓ Subgroup.centralizer ({bM β ε fb} : Set M))
          (Subgroup.centralizer ({bM β ε fb} : Set M)) →
      Nonempty (E ≃* MulAut ↥Gp) ∧ Nonempty (E ≃* β.G0) ∧ IsL43 M

end CFSG.ASVolI
