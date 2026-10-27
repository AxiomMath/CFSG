module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocSylG
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

namespace Ctx

variable {G : Type} [Group G]
  (C : Ctx G)

@[expose] noncomputable def ψT : ↥T →* G := C.φ1.comp (Subgroup.inclusion T_le_P1)

@[expose] noncomputable def pre1T (A : Subgroup G) : Subgroup Y := (A.comap C.ψT).map T.subtype

theorem mem_pre1T {A : Subgroup G} {y : Y} : y ∈ C.pre1T A ↔ y ∈ T ∧ C.Φ1 y ∈ A := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : C.ψT x = C.Φ1 (x : Y) := (C.Φ1_of_mem (T_le_P1 x.2)).symm
    refine ⟨x.2, ?_⟩
    show C.Φ1 (x : Y) ∈ A
    rw [← this]
    exact hx
  · rintro ⟨hy, hA⟩
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    have : C.ψT ⟨y, hy⟩ = C.Φ1 y := (C.Φ1_of_mem (T_le_P1 hy)).symm
    show C.ψT ⟨y, hy⟩ ∈ A
    rw [this]
    exact hA

theorem pre1T_le {A : Subgroup G} : C.pre1T A ≤ T := fun _ hy => (C.mem_pre1T.1 hy).1

theorem card_pre1T {A : Subgroup G} (hA : A ≤ C.TG) : Nat.card (C.pre1T A) = Nat.card A := by
  have hinj : Function.Injective C.ψT := by
    intro x y hxy
    have h1 : C.Φ1 (x : Y) = C.Φ1 (y : Y) := by
      rw [C.Φ1_of_mem (T_le_P1 x.2), C.Φ1_of_mem (T_le_P1 y.2)]
      exact hxy
    exact Subtype.ext (C.Φ1_inj (T_le_P1 x.2) (T_le_P1 y.2) h1)
  have hr : A ≤ C.ψT.range := by
    intro g hg
    obtain ⟨s, hs, rfl⟩ := C.mem_TG.1 (hA hg)
    exact ⟨⟨s, hs⟩, (C.Φ1_of_mem (T_le_P1 hs)).symm⟩
  rw [pre1T, Subgroup.card_map_of_injective T.subtype_injective]
  have := Subgroup.card_map_of_injective hinj (K := A.comap C.ψT)
  rw [Subgroup.map_comap_eq_self hr] at this
  exact this.symm

variable [Finite G]

theorem weakly_closed (S : Sylow 2 G) (hS : (S : Subgroup G) = C.TG) :
    IsWeaklyClosedIn C.V2 (S : Subgroup G) := by
  intro g hg
  rw [hS] at hg
  set E := conjSubgroup C.V2 g with hE
  have hmemE : ∀ x, x ∈ E ↔ g * x * g⁻¹ ∈ C.V2 := fun x => mem_conjSubgroup_iff
  have hcardE : Nat.card E = Nat.card C.V2 := by
    rw [hE, conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  have hE' : C.pre1T E = Vsub := by
    refine eq_Vsub_of_elemAbelian (C.pre1T_le) ?_ ?_ ?_
    · intro a ha b hb
      obtain ⟨haT, haE⟩ := C.mem_pre1T.1 ha
      obtain ⟨hbT, hbE⟩ := C.mem_pre1T.1 hb
      have := C.V2_comm ((hmemE _).1 haE) ((hmemE _).1 hbE)
      have h2 : C.Φ1 a * C.Φ1 b = C.Φ1 b * C.Φ1 a := by
        have e : g * (C.Φ1 a * C.Φ1 b) * g⁻¹ = g * (C.Φ1 b * C.Φ1 a) * g⁻¹ := by
          calc g * (C.Φ1 a * C.Φ1 b) * g⁻¹
              = (g * C.Φ1 a * g⁻¹) * (g * C.Φ1 b * g⁻¹) := by group
            _ = (g * C.Φ1 b * g⁻¹) * (g * C.Φ1 a * g⁻¹) := this
            _ = g * (C.Φ1 b * C.Φ1 a) * g⁻¹ := by group
        exact mul_left_cancel (mul_right_cancel e)
      rw [← C.Φ1_mul (T_le_P1 haT) (T_le_P1 hbT), ← C.Φ1_mul (T_le_P1 hbT) (T_le_P1 haT)] at h2
      exact C.Φ1_inj (P1.mul_mem (T_le_P1 haT) (T_le_P1 hbT))
        (P1.mul_mem (T_le_P1 hbT) (T_le_P1 haT)) h2
    · intro a ha
      obtain ⟨haT, haE⟩ := C.mem_pre1T.1 ha
      have h1 := C.V2_sq ((hmemE _).1 haE)
      have h2 : C.Φ1 a * C.Φ1 a = 1 := by
        have : g * (C.Φ1 a * C.Φ1 a) * g⁻¹ = 1 := by
          calc g * (C.Φ1 a * C.Φ1 a) * g⁻¹ = (g * C.Φ1 a * g⁻¹) * (g * C.Φ1 a * g⁻¹) := by group
            _ = 1 := h1
        simpa using this
      rw [← C.Φ1_mul (T_le_P1 haT) (T_le_P1 haT), ← C.Φ1_one] at h2
      exact C.Φ1_inj (P1.mul_mem (T_le_P1 haT) (T_le_P1 haT)) P1.one_mem h2
    · rw [C.card_pre1T hg, hcardE, C.card_V2]
  have hEV : E = C.V2 := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) hcardE.ge
    obtain ⟨y, hy, rfl⟩ := C.mem_TG.1 (hg hx)
    have : y ∈ C.pre1T E := C.mem_pre1T.2 ⟨hy, hx⟩
    rw [hE'] at this
    exact C.Φ1_mem_V2 this
  exact hEV

omit [Finite G] in
theorem V2_le_TG : C.V2 ≤ C.TG := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := C.mem_V2.1 hx
  rw [← C.Φ1_eq_Φ2 (T_le_B0 (Vsub_le_T hv))]
  exact C.Φ1_mem_TG (Vsub_le_T hv)

theorem isConj_of_conj_z {v : Y} (hv : v ∈ Vsub) {g : G} (hg : C.Φ2 v = g * C.z * g⁻¹) :
    IsConj xY v := by
  obtain ⟨S, hS⟩ := C.exists_sylow_TG
  have hW := C.weakly_closed S hS
  have hWS : C.V2 ≤ (S : Subgroup G) := hS ▸ C.V2_le_TG
  have hxc : C.Φ2 v ∈ Subgroup.centralizer (C.V2 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact C.V2_comm hh (C.Φ2_mem_V2 hv)
  have hzV : C.z ∈ C.V2 := C.z_mem_V2
  have hzc : C.z ∈ Subgroup.centralizer (C.V2 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact C.V2_comm hh hzV
  have hg' : g⁻¹ * C.Φ2 v * g = C.z := by
    rw [hg]
    group
  obtain ⟨n, hn, hnv⟩ := burnside_fusion_lemma_centralizer S hWS hW hxc hzc hg'
  obtain ⟨e, he⟩ := C.norm n hn
  have hnE : n = C.Φ2 (e : Y) := by rw [← he, C.Φ2_of_mem e.2]
  have hvP : v ∈ P2 := Vsub_le_P2 hv
  have h1 : C.Φ2 ((e : Y)⁻¹ * v * (e : Y)) = C.Φ2 xY := by
    rw [C.Φ2_mul (P2.mul_mem (P2.inv_mem e.2) hvP) e.2, C.Φ2_mul (P2.inv_mem e.2) hvP,
      C.Φ2_inv e.2, ← hnE, hnv, ← C.z_eq]
  have h2 : (e : Y)⁻¹ * v * (e : Y) = xY :=
    C.Φ2_inj (P2.mul_mem (P2.mul_mem (P2.inv_mem e.2) hvP) e.2) mem_P2_xY h1
  refine isConj_iff.2 ⟨(e : Y), ?_⟩
  calc (e : Y) * xY * (e : Y)⁻¹ = (e : Y) * ((e : Y)⁻¹ * v * (e : Y)) * (e : Y)⁻¹ := by rw [h2]
    _ = v := by group

theorem not_conj_z {v : Y} (hv : v ∈ Vsub) (hnc : ¬ IsConj xY v) (g : G) :
    C.Φ2 v ≠ g * C.z * g⁻¹ := fun h => hnc (C.isConj_of_conj_z hv h)

end Ctx

end CFSG.Quasithin.H13.F431.U42
