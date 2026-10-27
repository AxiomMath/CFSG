module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.Claim5D
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.SevenB

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher Equiv
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem claim4 : Vn β ≤ oTwoRes (stab α') ⊔ Qv α' ∧ (Qv α').relIndex (Vn β) = 4 := by
  refine ⟨fun y hy => ?_, C.claim5.2.1⟩
  have hd : CosetGeom.dist α' β + 1 = bMin H M := by
    rw [CosetGeom.dist_comm]; exact C.hc.dist_eq'
  exact C.mem_oTwoRes_sup_of_relIndex_four C.vtype_alpha' hd C.claim5.2.1 hy

theorem claim6 {μ : Geo H M} (hμ : μ ∈ nbrs α') (hVQ : Vn β ≤ Qv μ) :
    stab α' ⊓ stab μ ≤ Subgroup.normalizer ((⁅Vn β, Vn α'⁆ ⊔ Zv α' : Subgroup G) : Set G) := by
  have hδ := C.vtype_alpha'
  obtain ⟨hN, θ, βm, hθs, hθk, hsd⟩ := C.exists_secData hδ
  have hc8 := C.card_map_edge hδ hμ hθk
  have hc4 : Nat.card (((Vn β).subgroupOf (stab α')).map θ) = 4 := by
    rw [C.card_map_theta hθk C.Vn_beta_le_stab]; exact C.claim5.2.1
  have hQμ : Qv μ ≤ stab α' ⊓ stab μ := by
    have := Qv_le_inf C.hA (mem_nbrs_comm hμ)
    rwa [inf_comm] at this
  have hsub : ((Vn β).subgroupOf (stab α')).map θ ≤
      ((stab α' ⊓ stab μ).subgroupOf (stab α')).map θ :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono _ (hVQ.trans hQμ))
  set A := ((Vn β).subgroupOf (stab α')).map θ with hA
  set D := ((stab α' ⊓ stab μ).subgroupOf (stab α')).map θ with hD
  have hAD : (A.subgroupOf D).index = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := A) (K := D)
    rw [inf_of_le_left hsub, hc4, hc8] at h1
    exact (show A.relIndex D = 2 by omega)
  have hnorm : (A.subgroupOf D).Normal := Subgroup.normal_of_index_eq_two hAD
  have hconj : ∀ g ∈ stab α' ⊓ stab μ, ∀ v ∈ Vn β, ∃ v' ∈ Vn β, ∃ q ∈ Qv α',
      g * v * g⁻¹ = v' * q := by
    intro g hg v hv
    have hgs : g ∈ stab α' := hg.1
    have hvs : v ∈ stab α' := C.Vn_beta_le_stab hv
    have hgD : θ ⟨g, hgs⟩ ∈ D := ⟨⟨g, hgs⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
    have hvA : θ ⟨v, hvs⟩ ∈ A := ⟨⟨v, hvs⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩
    have hcj := hnorm.conj_mem ⟨θ ⟨v, hvs⟩, hsub hvA⟩ (Subgroup.mem_subgroupOf.mpr hvA)
      ⟨θ ⟨g, hgs⟩, hgD⟩
    have hcj' : θ ⟨g, hgs⟩ * θ ⟨v, hvs⟩ * (θ ⟨g, hgs⟩)⁻¹ ∈ A := by
      simpa [Subgroup.mem_subgroupOf] using hcj
    obtain ⟨u, hu, hue⟩ := hcj'
    have hu' : (u : G) ∈ Vn β := Subgroup.mem_subgroupOf.mp hu
    refine ⟨u, hu', (u : G)⁻¹ * (g * v * g⁻¹), ?_, by simp⟩
    have hker : u⁻¹ * (⟨g, hgs⟩ * ⟨v, hvs⟩ * ⟨g, hgs⟩⁻¹ : ↥(stab α')) ∈ θ.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv, hue]
      group
    rw [hθk, Subgroup.mem_subgroupOf] at hker
    simpa using hker
  have hZc : ∀ z ∈ Zv α', ∀ h ∈ stab α', h * z * h⁻¹ = z := fun z hz h hh => by
    have := Subgroup.mem_centralizer_iff.mp (C.Zv_le_center hδ hz).2 h hh
    rw [this]; simp
  have hkey : ∀ g ∈ stab α' ⊓ stab μ, ∀ x ∈ (⁅Vn β, Vn α'⁆ ⊔ Zv α' : Subgroup G),
      g * x * g⁻¹ ∈ (⁅Vn β, Vn α'⁆ ⊔ Zv α' : Subgroup G) := by
    intro g hg
    have hgs := hg.1
    have hle : (⁅Vn β, Vn α'⁆ ⊔ Zv α' : Subgroup G) ≤
        (⁅Vn β, Vn α'⁆ ⊔ Zv α' : Subgroup G).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le ?_ ?_
      · rw [Subgroup.commutator_le]
        intro v hv y hy
        show g * ⁅v, y⁆ * g⁻¹ ∈ (⁅Vn β, Vn α'⁆ ⊔ Zv α' : Subgroup G)
        obtain ⟨v', hv', q, hq, hvq⟩ := hconj g hg v hv
        have hy' : g * y * g⁻¹ ∈ Vn α' :=
          (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn α' hgs) y).mp hy
        have e : g * ⁅v, y⁆ * g⁻¹ = ⁅g * v * g⁻¹, g * y * g⁻¹⁆ := by
          simp only [commutatorElement_def]; group
        rw [e, hvq]
        have h1 : ⁅v' * q, g * y * g⁻¹⁆ =
            v' * ⁅q, g * y * g⁻¹⁆ * v'⁻¹ * ⁅v', g * y * g⁻¹⁆ := by
          simp only [commutatorElement_def]; group
        have hqy : ⁅q, g * y * g⁻¹⁆ ∈ Zv α' := by
          rw [← C.comm_Vn_Qv_eq hδ, Subgroup.commutator_comm]
          exact Subgroup.commutator_mem_commutator hq hy'
        rw [h1, hZc _ hqy v' (C.Vn_beta_le_stab hv')]
        exact mul_mem (Subgroup.mem_sup_right hqy)
          (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hv' hy'))
      · intro z hz
        show g * z * g⁻¹ ∈ (⁅Vn β, Vn α'⁆ ⊔ Zv α' : Subgroup G)
        rw [hZc z hz g hgs]; exact Subgroup.mem_sup_right hz
    intro x hx; exact hle hx
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hkey g hg x, fun hx => ?_⟩
  have := hkey g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

end Ctx

theorem claim4Spec : Claim4Spec H M S := fun C => C.claim4.1

theorem claim6Spec : Claim6Spec H M S := fun C _ hμ hVQ => C.claim6 hμ hVQ

end CFSG.Quasithin.Kleidman.F53Hss36
