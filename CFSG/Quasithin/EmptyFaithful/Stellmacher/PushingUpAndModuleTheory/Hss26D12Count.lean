module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Index
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss26ShapeCases

public section

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.Quasithin.F7 CFSG.Quasithin.F53Push CosetGeom
open CFSG.QuasithinUnique (IsSylowTwoOf)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem le_normalizer_sup_of {K B C : Subgroup G} (hB : K ≤ Subgroup.normalizer (B : Set G))
    (hC : K ≤ Subgroup.normalizer (C : Set G)) :
    K ≤ Subgroup.normalizer ((B ⊔ C : Subgroup G) : Set G) := fun g hg =>
  mem_normalizer_of_cj_le (by
    have : cj g (B ⊔ C) = cj g B ⊔ cj g C := Subgroup.map_sup _ _ _
    rw [this, cj_eq_of_mem_normalizer (hB hg), cj_eq_of_mem_normalizer (hC hg)])

theorem relIndex_ne_zero_fin (A B : Subgroup G) : A.relIndex B ≠ 0 :=
  Subgroup.index_ne_zero_of_finite

namespace SitSigma

variable {δ μ : Geo H M} {X : Subgroup G}

theorem inf_inf_Qv_le_core (h : SitSigma δ μ X) :
    Qv μ ⊓ X ⊓ Qv δ ≤ pCoreOf 2 X := fun _ hx => h.inf_Qv_le_R ⟨hx.1.2, hx.2⟩

theorem Qv_le_edge (hA : F53Amalgam H M S) (h : SitSigma δ μ X) : Qv δ ≤ stab δ ⊓ stab μ :=
  Qv_le_inf hA h.adj

theorem Qv_le_normalizer_core (hA : F53Amalgam H M S) (h : SitSigma δ μ X)
    (hPn : stab μ ≤ Subgroup.normalizer ((Qv μ ⊓ X : Subgroup G) : Set G)) :
    Qv δ ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) := by
  intro a ha
  refine mem_normalizer_of_cj_le fun x hx => ?_
  rw [mem_cj] at hx
  set q := a⁻¹ * x * a with hq
  have hqQ : q ∈ pCoreOf 2 X := hx
  have hqP : q ∈ Qv μ ⊓ X := h.R_le_P hqQ
  have hqX : q ∈ X := hqP.2
  have haμ : a ∈ stab μ := (h.Qv_le_edge hA ha).2
  have hxeq : x = a * q * a⁻¹ := by rw [hq]; group
  have h1 : a * q * a⁻¹ ∈ Qv μ ⊓ X := by
    exact (Subgroup.mem_normalizer_iff.mp (hPn haμ) q).mp hqP
  have h2 : a * q * a⁻¹ * q⁻¹ ∈ Qv μ ⊓ X := (Qv μ ⊓ X).mul_mem h1 ((Qv μ ⊓ X).inv_mem hqP)
  have h3 : a * q * a⁻¹ * q⁻¹ ∈ Qv δ := by
    have hqδ : q ∈ stab δ := h.le_stab hqX
    have hn : q * a⁻¹ * q⁻¹ ∈ Qv δ := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (stab δ) hqδ) (a⁻¹)).mp ((Qv δ).inv_mem ha)
    have : a * (q * a⁻¹ * q⁻¹) ∈ Qv δ := (Qv δ).mul_mem ha (by simpa [mul_assoc] using hn)
    simpa [mul_assoc] using this
  have h4 : a * q * a⁻¹ * q⁻¹ ∈ pCoreOf 2 X := h.inf_inf_Qv_le_core ⟨h2, h3⟩
  have : x = (a * q * a⁻¹ * q⁻¹) * q := by rw [hxeq]; group
  rw [this]
  exact (pCoreOf 2 X).mul_mem h4 hqQ

omit [Finite G] in
theorem P_le_normalizer_core (μ : Geo H M) (X : Subgroup G) :
    Qv μ ⊓ X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
  inf_le_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)

theorem isPGroup_edge (hA : F53Amalgam H M S) (h : SitSigma δ μ X) :
    IsPGroup 2 ↥(stab δ ⊓ stab μ) := (sylow_stab_inf_left hA h.adj).2.1

theorem not_edge_le_normalizer_sup (hA : F53Amalgam H M S) (h : SitSigma δ μ X)
    (hQ0 : ¬ pCoreOf 2 X ≤ Qv δ) :
    ¬ stab δ ⊓ stab μ ≤ Subgroup.normalizer ((pCoreOf 2 X ⊔ Qv δ : Subgroup G) : Set G) := by
  intro hE
  have hXn : X ≤ Subgroup.normalizer ((pCoreOf 2 X ⊔ Qv δ : Subgroup G) : Set G) :=
    le_normalizer_sup_of (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
      (h.le_stab.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (stab δ)))
  have hδ : stab δ ≤ Subgroup.normalizer ((pCoreOf 2 X ⊔ Qv δ : Subgroup G) : Set G) := by
    rw [← h.gen]; exact sup_le hXn hE
  have hle : pCoreOf 2 X ⊔ Qv δ ≤ stab δ ⊓ stab μ :=
    sup_le ((h.R_le_P).trans (h.P_le_edge hA)) (h.Qv_le_edge hA)
  have hp : IsPGroup 2 ↥(pCoreOf 2 X ⊔ Qv δ) := (h.isPGroup_edge hA).to_le hle
  have hc := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (hle.trans inf_le_left) hδ hp
  exact hQ0 (le_sup_left.trans hc)

theorem counts (hA : F53Amalgam H M S) (h : SitSigma δ μ X)
    (hPn : stab μ ≤ Subgroup.normalizer ((Qv μ ⊓ X : Subgroup G) : Set G))
    (hQ0 : ¬ pCoreOf 2 X ≤ Qv δ) :
    vtype δ = false ∧ (pCoreOf 2 X).relIndex (Qv μ ⊓ X) = 2 ∧
      (Qv μ ⊓ X ⊓ Qv δ).relIndex (pCoreOf 2 X) = 2 ∧
      (Qv δ ⊔ (Qv μ ⊓ X)).relIndex (stab δ ⊓ stab μ) = 2 := by
  have hQP : pCoreOf 2 X ≤ Qv μ ⊓ X := h.R_le_P
  have hPE : Qv μ ⊓ X ≤ stab δ ⊓ stab μ := h.P_le_edge hA
  have hAE : Qv δ ≤ stab δ ⊓ stab μ := h.Qv_le_edge hA
  have hPA : Qv μ ⊓ X ⊓ Qv δ ≤ pCoreOf 2 X := h.inf_inf_Qv_le_core
  have hPnA : Qv μ ⊓ X ≤ Subgroup.normalizer (Qv δ : Set G) :=
    (hPE.trans inf_le_left).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (stab δ))
  have hPQ := P_le_normalizer_core (H := H) (M := M) μ X
  have hAP : Qv δ ⊔ (Qv μ ⊓ X) ≤ stab δ ⊓ stab μ := sup_le hAE hPE
  have hE1 := h.not_edge_le_normalizer_sup hA hQ0
  have hAPn : Qv δ ⊔ (Qv μ ⊓ X) ≤
      Subgroup.normalizer ((pCoreOf 2 X ⊔ Qv δ : Subgroup G) : Set G) :=
    sup_le (le_sup_right.trans Subgroup.le_normalizer) (le_normalizer_sup_of hPQ hPnA)
  have c1 : (Qv δ).relIndex (stab δ ⊓ stab μ) =
      (Qv δ).relIndex (Qv δ ⊔ (Qv μ ⊓ X)) * (Qv δ ⊔ (Qv μ ⊓ X)).relIndex (stab δ ⊓ stab μ) :=
    (Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left hAP).symm
  have c2 : (Qv δ).relIndex (Qv δ ⊔ (Qv μ ⊓ X)) = (Qv δ ⊓ (Qv μ ⊓ X)).relIndex (Qv μ ⊓ X) :=
    relIndex_sup_eq_relIndex_inf_right hPnA
  have hAPQ : Qv δ ⊓ (Qv μ ⊓ X) ≤ pCoreOf 2 X := by
    rw [inf_comm]; exact hPA
  have c3 : (Qv δ ⊓ (Qv μ ⊓ X)).relIndex (Qv μ ⊓ X) =
      (Qv δ ⊓ (Qv μ ⊓ X)).relIndex (pCoreOf 2 X) * (pCoreOf 2 X).relIndex (Qv μ ⊓ X) :=
    (Subgroup.relIndex_mul_relIndex _ _ _ hAPQ hQP).symm
  have b1 : 2 ≤ (pCoreOf 2 X).relIndex (Qv μ ⊓ X) := by
    have h0 : (pCoreOf 2 X).relIndex (Qv μ ⊓ X) ≠ 0 := relIndex_ne_zero_fin _ _
    have h1 : (pCoreOf 2 X).relIndex (Qv μ ⊓ X) ≠ 1 := fun h1 =>
      h.not_le_pCore hA hPn (Subgroup.relIndex_eq_one.mp h1)
    omega
  have b2 : 2 ≤ (Qv δ ⊓ (Qv μ ⊓ X)).relIndex (pCoreOf 2 X) := by
    have h0 : (Qv δ ⊓ (Qv μ ⊓ X)).relIndex (pCoreOf 2 X) ≠ 0 := relIndex_ne_zero_fin _ _
    have h1 : (Qv δ ⊓ (Qv μ ⊓ X)).relIndex (pCoreOf 2 X) ≠ 1 := fun h1 =>
      hQ0 (fun x hx => (Subgroup.relIndex_eq_one.mp h1 hx).1)
    omega
  have b3 : 2 ≤ (Qv δ ⊔ (Qv μ ⊓ X)).relIndex (stab δ ⊓ stab μ) := by
    have h0 : (Qv δ ⊔ (Qv μ ⊓ X)).relIndex (stab δ ⊓ stab μ) ≠ 0 := relIndex_ne_zero_fin _ _
    have h1 : (Qv δ ⊔ (Qv μ ⊓ X)).relIndex (stab δ ⊓ stab μ) ≠ 1 := fun h1 =>
      hE1 ((Subgroup.relIndex_eq_one.mp h1).trans hAPn)
    omega
  rw [c2, c3] at c1
  cases hv : vtype δ with
  | true =>
    have h2 := relIndex_Qv_inf_true hA h.adj hv
    rw [h2] at c1
    nlinarith
  | false =>
    have h8 := relIndex_Qv_inf_false hA h.adj hv
    rw [h8] at c1
    refine ⟨rfl, ?_⟩
    have e1 : (pCoreOf 2 X).relIndex (Qv μ ⊓ X) ≤ 2 := by nlinarith
    have e2 : (Qv δ ⊓ (Qv μ ⊓ X)).relIndex (pCoreOf 2 X) ≤ 2 := by nlinarith
    have e3 : (Qv δ ⊔ (Qv μ ⊓ X)).relIndex (stab δ ⊓ stab μ) ≤ 2 := by nlinarith
    refine ⟨by omega, ?_, by omega⟩
    rw [inf_comm]; omega

end SitSigma

end CFSG.Quasithin.F53
