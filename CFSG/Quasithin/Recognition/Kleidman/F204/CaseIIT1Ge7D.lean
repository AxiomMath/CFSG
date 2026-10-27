module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT1Ge7C
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT1Ge7B

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem inv_mul_mem_of_relIndex_le_two {Y Q : Subgroup G} (h : (Y ⊓ Q).relIndex Y ≤ 2) {a u : G}
    (ha : a ∈ Y) (hu : u ∈ Y) (haQ : a ∉ Q) (huQ : u ∉ Q) : a⁻¹ * u ∈ Q := by
  have h0 : (Y ⊓ Q).relIndex Y ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : (Y ⊓ Q).relIndex Y ≠ 1 := by
    intro h1
    have := Subgroup.relIndex_eq_one.mp h1
    exact haQ (Subgroup.mem_inf.mp (this ha)).2
  have h2 : ((Y ⊓ Q).subgroupOf Y).index = 2 := by
    show (Y ⊓ Q).relIndex Y = 2; omega
  have key := Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨a, ha⟩ : Y)⁻¹) (b := ⟨u, hu⟩)
  have hna : ¬ ((⟨a, ha⟩ : Y)⁻¹ ∈ (Y ⊓ Q).subgroupOf Y) := by
    intro hm
    rw [Subgroup.inv_mem_iff, Subgroup.mem_subgroupOf] at hm
    exact haQ (Subgroup.mem_inf.mp hm).2
  have hnu : ¬ ((⟨u, hu⟩ : Y) ∈ (Y ⊓ Q).subgroupOf Y) := by
    intro hm
    rw [Subgroup.mem_subgroupOf] at hm
    exact huQ (Subgroup.mem_inf.mp hm).2
  have hm : (⟨a, ha⟩ : Y)⁻¹ * ⟨u, hu⟩ ∈ (Y ⊓ Q).subgroupOf Y := key.mpr (iff_of_false hna hnu)
  rw [Subgroup.mem_subgroupOf] at hm
  exact (Subgroup.mem_inf.mp hm).2

section CaseII

variable (F : Frame L1 L2 S D X) (hT1 : ConfigT1 L1 L2 S)
  {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hc : IsCritData α β α') (hII : Zv α' ≤ Qv α)
include F hT1 hc hII

theorem Zv_inf_Vn_ne_bot : Zv α' ⊓ Vn β ≠ ⊥ := by
  have hA := Amal.of_frame F
  obtain ⟨hα, hβ, hα', -, hb3⟩ := t1II_setup F hT1 hc hII
  obtain ⟨hVβ, hWβ⟩ := t1II_Vn_le_stab F hT1 hc hII
  obtain ⟨k, hk, w, hw, hkw⟩ := t1II_comm_ne F hT1 hc hII
  obtain ⟨hkV, hkQ⟩ := Subgroup.mem_inf.mp hk
  obtain ⟨μ, hμ, z, hz, hkz⟩ : ∃ μ ∈ nbrs α', ∃ z ∈ Zv μ, k * z ≠ z * k := by
    by_contra h
    push Not at h
    apply hkw
    have hle : Vn α' ≤ Subgroup.centralizer {k} := iSup₂_le fun μ hμ x hx => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (h μ hμ x hx).symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hw)).symm
  have hα'μ : α' ∈ nbrs μ := mem_nbrs_symm hμ
  have hμt : vtype μ = true := by
    have := vtype_ne_of_adj (show (graph _ _ _).Adj α' μ from hμ)
    rw [hα'] at this
    cases h : vtype μ <;> simp_all
  have hZab : ∀ a ∈ Zv μ, ∀ b ∈ Zv μ, a * b = b * a := fun a ha b hb =>
    (hA.isElemAbelian_Zv μ).1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩ |> congrArg Subtype.val
  have hkμ : k ∈ stab μ := hA.Qv_le_stab_of_mem_nbrs hμ hkQ
  have hkN : k ∈ Subgroup.normalizer (Zv μ : Set G) := hA.stab_le_normalizer_Zv μ hkμ
  set σ := commMap hZab hkN with hσ
  set R : Subgroup G := σ.range.map (Zv μ).subtype with hR
  have hmemR : ∀ r, r ∈ R ↔ ∃ y ∈ Zv μ, r = k * y * k⁻¹ * y⁻¹ := by
    intro r
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨σ ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, rfl⟩
  have hRne : R ≠ ⊥ := by
    intro hb
    have hm : k * z * k⁻¹ * z⁻¹ ∈ R := (hmemR _).mpr ⟨z, hz, rfl⟩
    rw [hb, Subgroup.mem_bot] at hm
    apply hkz
    calc k * z = (k * z * k⁻¹ * z⁻¹) * z * k := by group
      _ = z * k := by rw [hm, one_mul]
  have hRV : R ≤ Vn β := by
    intro r hr
    obtain ⟨y, hy, rfl⟩ := (hmemR r).mp hr
    have hyβ : y ∈ stab β := hWβ (hA.Zv_le_Vn hμ hy)
    have h1 : y * k⁻¹ * y⁻¹ ∈ Vn β :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn β hyβ) _).mp ((Vn β).inv_mem hkV)
    have e : k * y * k⁻¹ * y⁻¹ = k * (y * k⁻¹ * y⁻¹) := by group
    rw [e]
    exact (Vn β).mul_mem hkV h1
  have hRQ : R ≤ Qv α' := fun r hr => by
    obtain ⟨y, hy, rfl⟩ := (hmemR r).mp hr
    exact Zv_le_Qv_of_mem_nbrs F hα'μ ((Zv μ).mul_mem ((Subgroup.mem_normalizer_iff.mp hkN y).mp hy)
      ((Zv μ).inv_mem hy))
  have hconj : ∀ q ∈ Qv α', ∀ r ∈ R, q * r * q⁻¹ ∈ R := by
    intro q hq r hr
    obtain ⟨y, hy, rfl⟩ := (hmemR r).mp hr
    have hqμ : q ∈ stab μ := hA.Qv_le_stab_of_mem_nbrs hμ hq
    have hy' : q * y * q⁻¹ ∈ Zv μ := (Subgroup.mem_normalizer_iff.mp
      (hA.stab_le_normalizer_Zv μ hqμ) y).mp hy
    have hc' : q * k * q⁻¹ * k⁻¹ ∈ Qv μ := comm_mem_Qv_of_mem_nbrs F hμt hα'μ hq hkQ
    have hky : k * (q * y * q⁻¹) * k⁻¹ ∈ Zv μ := (Subgroup.mem_normalizer_iff.mp hkN _).mp hy'
    have hcomm := Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv μ hky).2 _ hc'
    refine (hmemR _).mpr ⟨q * y * q⁻¹, hy', ?_⟩
    calc q * (k * y * k⁻¹ * y⁻¹) * q⁻¹
        = (q * k * q⁻¹ * k⁻¹) * (k * (q * y * q⁻¹) * k⁻¹) * (q * k * q⁻¹ * k⁻¹)⁻¹ *
            (q * y * q⁻¹)⁻¹ := by group
      _ = (k * (q * y * q⁻¹) * k⁻¹) * (q * k * q⁻¹ * k⁻¹) * (q * k * q⁻¹ * k⁻¹)⁻¹ *
            (q * y * q⁻¹)⁻¹ := by rw [hcomm]
      _ = k * (q * y * q⁻¹) * k⁻¹ * (q * y * q⁻¹)⁻¹ := by group
  have hRn : Qv α' ≤ Subgroup.normalizer (R : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨hconj q hq r, fun h => ?_⟩
    have := hconj q⁻¹ ((Qv α').inv_mem hq) _ h
    rwa [show q⁻¹ * (q * r * q⁻¹) * q⁻¹⁻¹ = r by group] at this
  obtain ⟨r, hrR, hr1, hrc⟩ := exists_ne_one_centralizer (p := 2) (pCoreOf_isPGroup 2 _) hRQ hRn hRne
  have hrZ : r ∈ Zv α' := by
    rw [Zv_eq_inf_centralizer F hT1 hμt hα'μ]
    obtain ⟨y, hy, rfl⟩ := (hmemR _).mp hrR
    exact Subgroup.mem_inf.mpr ⟨(Zv μ).mul_mem ((Subgroup.mem_normalizer_iff.mp hkN y).mp hy)
      ((Zv μ).inv_mem hy), hrc⟩
  intro hb
  have : r ∈ Zv α' ⊓ Vn β := Subgroup.mem_inf.mpr ⟨hrZ, hRV hrR⟩
  rw [hb, Subgroup.mem_bot] at this
  exact hr1 this

end CaseII

end CFSG.Quasithin.Kleidman.F204
