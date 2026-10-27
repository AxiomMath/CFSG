module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5D4
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChSyl
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.B5

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem cent_Vn_le_Zv (hC : Ch.Ctx H M S) {γ : Geo H M} (hγ : vtype γ = false) :
    Vn γ ⊓ Subgroup.centralizer (Qv γ : Set G) ≤ Zv γ := by
  have hS := hC.sit
  set U : Subgroup G := Vn γ ⊓ Subgroup.centralizer (Qv γ : Set G) with hU
  have hZU : Zv γ ≤ U := by
    intro x hx
    refine ⟨Zv_le_Vn_S5 hS hγ hx, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    have hc := Subgroup.mem_centralizer_iff.mp (Zv_central hS hγ hx).2
    exact hc h (Ch.Qv_le_stab' γ hh)
  have key : ∀ g ∈ stab γ, ∀ x ∈ U, g * x * g⁻¹ ∈ U := by
    intro g hg x hx
    have hgV := Subgroup.mem_normalizer_iff.mp (Vn_normal γ hg)
    have hgQ := Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab γ) hg)
    refine ⟨(hgV x).mp hx.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    have hxc := Subgroup.mem_centralizer_iff.mp hx.2
    have h1 : g⁻¹ * h * g ∈ Qv γ := by
      have h2 : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
      exact (hgQ (g⁻¹ * h * g)).mpr (by rw [h2]; exact hh)
    have h3 := hxc _ h1
    calc h * (g * x * g⁻¹) = g * ((g⁻¹ * h * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * h * g)) * g⁻¹ := by rw [h3]
      _ = g * x * g⁻¹ * h := by group
  have hnorm : stab γ ≤ Subgroup.normalizer (U : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key g hg x, fun hx => ?_⟩
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    have := key g⁻¹ ((stab γ).inv_mem hg) _ hx
    rwa [e] at this
  rcases (hC.orthZ γ hγ).irred U hZU inf_le_left hnorm with h | h
  · exact h.le
  · exfalso
    have hle : Vn γ ≤ Subgroup.centralizer (Qv γ : Set G) := by
      rw [← h]; exact inf_le_right
    have h0 : ⁅Vn γ, Qv γ⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
    rw [comm_Vn_Qv hS hγ] at h0
    exact Zv_ne_bot hS.glob.amalg γ h0

theorem comm_le_centralizer {β α' γ : Geo H M} (hS : Sit H M S)
    (hβW : Vn β ≤ Wb γ) (hαW : Vn α' ≤ Wb γ)
    (hβ : ∀ q ∈ Qv γ, ∀ y ∈ Vn β, q * y * q⁻¹ * y⁻¹ ∈ Vn γ)
    (hα : ∀ q ∈ Qv γ, ∀ y ∈ Vn α', q * y * q⁻¹ * y⁻¹ ∈ Vn γ) :
    ⁅Vn β, Vn α'⁆ ≤ Subgroup.centralizer (Qv γ : Set G) := by
  have hcomm : ∀ c ∈ Vn γ, ∀ w ∈ Wb γ, Commute c w := by
    intro c hc w hw
    have h1 := Subgroup.commutator_mem_commutator hc hw
    rw [comm_Vn_Wb hS γ, Subgroup.mem_bot, commutatorElement_def] at h1
    exact (commute_iff_eq _ _).mpr (by
      calc c * w = (c * w * c⁻¹ * w⁻¹) * w * c := by group
        _ = w * c := by rw [h1]; simp)
  have hVc : ∀ c ∈ Vn γ, ∀ d ∈ Vn γ, Commute c d := fun c hc d hd =>
    (commute_iff_eq _ _).mpr
      (EmptyFaithful.Stellmacher.OrdinaryProofs.comm_of_mem_isMulCommutative
        (Vn_isElemAbelian hS γ).1 hc hd)
  rw [Subgroup.commutator_le]
  intro v hv u hu
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have c1 := hβ q hq v hv
  have c2 := hα q hq u hu
  have e1 : q * v * q⁻¹ = (q * v * q⁻¹ * v⁻¹) * v := by group
  have e2 : q * u * q⁻¹ = (q * u * q⁻¹ * u⁻¹) * u := by group
  have hv' := hβW hv
  have hu' := hαW hu
  have key : q * ⁅v, u⁆ * q⁻¹ = ⁅v, u⁆ := by
    rw [conj_comm, e1, e2]
    exact comm_mul_mul (hcomm _ c1 v hv') (hcomm _ c1 u hu')
      (hcomm _ c2 v hv') (hcomm _ c2 u hu') (hVc _ c1 _ c2)
  calc q * ⁅v, u⁆ = (q * ⁅v, u⁆ * q⁻¹) * q := by group
    _ = ⁅v, u⁆ * q := by rw [key]

end S35.B5

end F53.Stellmacher

end CFSG.Quasithin
