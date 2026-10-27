module

public import CFSG.Quasithin.Background.C118Class

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Quasithin
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

namespace IsSeed

theorem not_Zfix_le_center (h : IsSeed S ρ (Ecore G) ψ) : ¬ Zfix S ≤ Subgroup.center G := by
  intro hZ
  apply h.not_le
  have hker : (S : Subgroup G) ≤ ρ.ker := fun s hs => by
    rw [MonoidHom.mem_ker]
    apply eq_one_of_forall_smul_eq'
    intro w
    obtain ⟨v, hvV, hvw⟩ := h.ψ_Vmod_surj (Multiplicative.ofAdd w)
    have hcv : s * (v : G) * s⁻¹ ∈ Ecore G := (inferInstance : (Ecore G).Normal).conj_mem v v.2 s
    have hcomm : s * (v : G) * s⁻¹ * (v : G)⁻¹ ∈ Zfix S := by
      rw [← h.sylow_commutator_Vmod]
      have hmem := Subgroup.commutator_mem_commutator hs hvV
      rwa [commutatorElement_def] at hmem
    have h1 : ψ (⟨s * (v : G) * s⁻¹, hcv⟩ * v⁻¹) = 1 := h.ψ_eq_one_iff.mpr (hZ hcomm)
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    have h2 := h.ψ_equiv s v ⟨s * (v : G) * s⁻¹, hcv⟩ rfl
    rw [h1, hvw, toAdd_ofAdd] at h2
    rw [Matrix.SpecialLinearGroup.smul_def]
    exact h2.symm
  have hSQ : (S : Subgroup G) ≤ CFSG.pCore 2 G := by
    rw [← h.sylow_inf_ker]
    exact le_inf le_rfl hker
  exact (thompsonJ_le_self' _).trans hSQ

theorem le_center_of_le_Hone (h : IsSeed S ρ (Ecore G) ψ) {Y : Subgroup G}
    (hY : Y ≤ Hone S ⊓ Subgroup.centralizer (Hone S : Set G))
    (hYS : ∀ s ∈ (S : Subgroup G), ∀ y ∈ Y, s * y = y * s) : Y ≤ Subgroup.center G := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Hone S ⊔ CFSG.pCore 2 G := by
    rw [h.Hone_sup_core]
    trivial
  obtain ⟨j, hj, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  have hzj : j * z = z * j := Subgroup.mem_centralizer_iff.mp (hY hz).2 j hj
  have hzq : q * z = z * q := hYS q (core_le_sylow S hq) z hz
  calc j * q * z = j * (q * z) := by group
    _ = j * (z * q) := by rw [hzq]
    _ = (j * z) * q := by group
    _ = (z * j) * q := by rw [hzj]
    _ = z * (j * q) := by group

end IsSeed

end CFSG.QuasithinUnique.Setup.Campbell

namespace CFSG.Quasithin

open Subgroup CFSG CFSG.QuasithinUnique.Setup.Campbell

namespace SeedData

variable {T : Type} [Group T]

theorem partnerData_in (X₁ X₂ : SeedData T) :
    PartnerData (X₂.S : Subgroup X₂.G) (X₁.Qh.map X₂.f) (X₁.Fh.map X₂.f) (X₁.Vh.map X₂.f)
      (X₁.Zh.map X₂.f) (Nat.card X₁.k) := by
  have h := X₁.partnerData.map X₂.f_injective
  rwa [X₂.map_top] at h

theorem Vh_le_Qh_of_commutator_eq_bot (X₁ X₂ : SeedData T) (h : ⁅X₁.Vh, X₂.Vh⁆ = ⊥) :
    X₁.Vh ≤ X₂.Qh := fun s hs =>
  X₂.partnerData.nat.cent_le s trivial fun v hv =>
    CFSG.QuasithinUnique.Setup.Campbell.mul_comm_of_commutator_eq_bot h hs hv

theorem Fh_le_of_Vh_le_Qh (X₁ X₂ : SeedData T) (hV : X₁.Vh ≤ X₂.Qh)
    (hZ : ¬ X₁.Zh.map X₂.f ≤ Subgroup.center X₂.G) : X₁.Fh ≤ X₂.Fh := by
  have hpd := partnerData_in X₁ X₂
  have hVQ : X₁.Vh.map X₂.f ≤ CFSG.pCore 2 X₂.G := by
    rw [← X₂.map_Qh]
    exact Subgroup.map_mono hV
  have hFQ := PartnerData.fp_le_core X₂.seed hpd hVQ
  by_contra hF
  apply hZ
  refine X₂.seed.le_center_of_le_Hone ?_ hpd.core.zcentral
  refine PartnerCore.partner_centrality X₂.seed hpd.core hFQ fun hle => hF ?_
  rw [← X₂.map_Fh] at hle
  exact (Subgroup.map_le_map_iff_of_injective X₂.f_injective).mp hle

theorem campbell_lemma23 (X₁ X₂ : SeedData T) :
    X₁.Fh = X₂.Fh ∨ ⁅X₁.Vh, X₂.Vh⁆ ≠ ⊥ ∨ X₁.Zh.map X₂.f ≤ Subgroup.center X₂.G := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hF, hV, hZ⟩ := hcon
  have h12 : X₁.Fh ≤ X₂.Fh := Fh_le_of_Vh_le_Qh X₁ X₂ (Vh_le_Qh_of_commutator_eq_bot X₁ X₂ hV) hZ
  have hV' : ⁅X₂.Vh, X₁.Vh⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hV
  have hpd := partnerData_in X₂ X₁
  have hVQ : X₂.Vh.map X₁.f ≤ CFSG.pCore 2 X₁.G := by
    rw [← X₁.map_Qh]
    exact Subgroup.map_mono (Vh_le_Qh_of_commutator_eq_bot X₂ X₁ hV')
  have hZ₂ : X₂.Zh.map X₁.f ≤ Subgroup.center X₁.G := by
    refine X₁.seed.le_center_of_le_Hone ?_ hpd.core.zcentral
    refine PartnerCore.partner_centrality X₁.seed hpd.core (PartnerData.fp_le_core X₁.seed hpd hVQ)
      fun hle => hF (le_antisymm h12 ?_)
    rw [← X₁.map_Fh] at hle
    exact (Subgroup.map_le_map_iff_of_injective X₁.f_injective).mp hle
  have hF12 : Fcore X₁.G ≤ X₂.Fh.map X₁.f := by
    rw [← X₁.map_Fh]
    exact Subgroup.map_mono h12
  obtain ⟨A, hA, hAQ⟩ := X₁.seed.exists_max_outside
  apply X₁.seed.not_Zfix_le_center
  calc Zfix X₁.S = ⁅A, Fcore X₁.G⁆ := (X₁.seed.commutator_A_Fcore hA hAQ).symm
    _ ≤ ⁅A, X₂.Fh.map X₁.f⁆ := Subgroup.commutator_mono le_rfl hF12
    _ ≤ X₂.Zh.map X₁.f := hpd.core.commA_le hA
    _ ≤ Subgroup.center X₁.G := hZ₂

end SeedData

end CFSG.Quasithin
