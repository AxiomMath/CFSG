module

public import CFSG.Quasithin.Vol2.Ch4Sec2CentKCoreA

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.Quasithin CFSG.Quasithin.A4 CFSG.Assembly.LowTwoRank Matrix
open CFSG.Open hiding StatedSL
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

variable {R Rp H K Q LH V : Subgroup G} {F : Type} [Field F] [Fintype F]
  {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)}

private theorem comm_claim_coreB {x s t v : G} (hxt : x * t = t * x) (hvs : v * s = s * v)
    (hvy : v * (t * s * t⁻¹) = t * s * t⁻¹ * v) (hv : v = x * s * x⁻¹ * s⁻¹) :
    ⁅x, t * s * t⁻¹ * s⁻¹⁆ = ⁅t, v⁆ := by
  have hxs : x * s * x⁻¹ = v * s := by rw [hv]; group
  have hA : x * (t * s * t⁻¹) * x⁻¹ = t * (v * s) * t⁻¹ := by
    calc x * (t * s * t⁻¹) * x⁻¹ = (x * t) * s * (x * t)⁻¹ := by group
      _ = (t * x) * s * (t * x)⁻¹ := by rw [hxt]
      _ = t * (x * s * x⁻¹) * t⁻¹ := by group
      _ = t * (v * s) * t⁻¹ := by rw [hxs]
  have hB : x * s⁻¹ * x⁻¹ = s⁻¹ * v⁻¹ := by
    calc x * s⁻¹ * x⁻¹ = (x * s * x⁻¹)⁻¹ := by group
      _ = (v * s)⁻¹ := by rw [hxs]
      _ = s⁻¹ * v⁻¹ := by group
  have hsv : s⁻¹ * v⁻¹ * s = v⁻¹ := by
    have h1 : s⁻¹ * v * s = v := by
      calc s⁻¹ * v * s = s⁻¹ * (v * s) := by group
        _ = s⁻¹ * (s * v) := by rw [hvs]
        _ = v := by group
    calc s⁻¹ * v⁻¹ * s = (s⁻¹ * v * s)⁻¹ := by group
      _ = v⁻¹ := by rw [h1]
  have hw : t * s * t⁻¹ * v⁻¹ = v⁻¹ * (t * s * t⁻¹) :=
    ((show Commute v (t * s * t⁻¹) from hvy).inv_left.eq).symm
  have key : s * t⁻¹ * v⁻¹ * t * s⁻¹ = t⁻¹ * v⁻¹ * t := by
    calc s * t⁻¹ * v⁻¹ * t * s⁻¹ = t⁻¹ * ((t * s * t⁻¹) * v⁻¹) * (t * s⁻¹ * t⁻¹) * t := by
          group
      _ = t⁻¹ * (v⁻¹ * (t * s * t⁻¹)) * (t * s⁻¹ * t⁻¹) * t := by rw [hw]
      _ = t⁻¹ * v⁻¹ * t := by group
  rw [commutatorElement_def, commutatorElement_def]
  calc x * (t * s * t⁻¹ * s⁻¹) * x⁻¹ * (t * s * t⁻¹ * s⁻¹)⁻¹
      = (x * (t * s * t⁻¹) * x⁻¹) * (x * s⁻¹ * x⁻¹) * (s * t * s⁻¹ * t⁻¹) := by group
    _ = (t * (v * s) * t⁻¹) * (s⁻¹ * v⁻¹) * (s * t * s⁻¹ * t⁻¹) := by rw [hA, hB]
    _ = t * v * (s * t⁻¹ * (s⁻¹ * v⁻¹ * s) * t * s⁻¹) * t⁻¹ := by group
    _ = t * v * (s * t⁻¹ * v⁻¹ * t * s⁻¹) * t⁻¹ := by rw [hsv]
    _ = t * v * (t⁻¹ * v⁻¹ * t) * t⁻¹ := by rw [key]
    _ = t * v * t⁻¹ * v⁻¹ := by group

theorem exists_good (h : CoreHyp R Rp H K Q LH V F α β)
    (hZC : omegaOneCenterOf R ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥) (hRlt : R < Rp) :
    ∃ s' t z : G, InR2 R Rp V s' ∧ t ∈ LH ∧ t * t ∈ R ∧
      z ∈ omegaOneCenterOf R ⊓ Subgroup.centralizer (K : Set G) ∧ ⁅z, s'⁆ ≠ 1 ∧
      ∀ z' ∈ omegaOneCenterOf R ⊓ Subgroup.centralizer (K : Set G), ∃ q ∈ V, ⁅z', s'⁆ = ⁅t, q⁆ := by
  obtain ⟨s, hs, hsR⟩ := exists_inR2_not_mem h hZC hRlt
  have hz : ∃ z ∈ omegaOneCenterOf R ⊓ Subgroup.centralizer (K : Set G), ⁅z, s⁆ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsC : s ∈ Subgroup.centralizer
        ((omegaOneCenterOf R ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun z hzZ =>
        commutatorElement_eq_one_iff_mul_comm.mp (hcon z hzZ)
    have hsH : s ∈ H := h.NZ hZC (Subgroup.centralizer_le_normalizer _ hsC)
    exact hsR (h.RpH (Subgroup.mem_inf.mpr ⟨hs.1, hsH⟩))
  obtain ⟨z, hzZ, hzs⟩ := hz
  have hav : ⁅z, s⁆ ∈ V := hs.2.2 z (Subgroup.mem_inf.mp hzZ).1
  obtain ⟨t, htLH, htt, hta⟩ : ∃ t ∈ LH, t * t ∈ R ∧ t * ⁅z, s⁆ ≠ ⁅z, s⁆ * t := by
    by_contra hcon
    push Not at hcon
    exact hzs (h.CV _ hav hcon)
  have hs' : InR2 R Rp V (t * s * t⁻¹ * s⁻¹) :=
    inR2_mul h (inR2_conj h hs htLH) (inR2_inv h hs)
  have htK : t ∈ K := h.LHK htLH
  have hts : t * s * t⁻¹ ∈ Rp :=
    (Subgroup.mem_normalizer_iff.mp (h.LHRp htLH) s).mp hs.1
  have claim : ∀ z' ∈ omegaOneCenterOf R ⊓ Subgroup.centralizer (K : Set G),
      ⁅z', t * s * t⁻¹ * s⁻¹⁆ = ⁅t, ⁅z', s⁆⁆ := by
    intro z' hz'
    have hzt : t * z' = z' * t :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz').2 t htK
    have hav' : ⁅z', s⁆ ∈ V := hs.2.2 z' (Subgroup.mem_inf.mp hz').1
    have hvs : ⁅z', s⁆ * s = s * ⁅z', s⁆ :=
      Subgroup.mem_centralizer_iff.mp (h.VRp hs.1) ⁅z', s⁆ hav'
    have hvy : ⁅z', s⁆ * (t * s * t⁻¹) = t * s * t⁻¹ * ⁅z', s⁆ :=
      Subgroup.mem_centralizer_iff.mp (h.VRp hts) ⁅z', s⁆ hav'
    exact comm_claim_coreB hzt.symm hvs hvy rfl
  refine ⟨t * s * t⁻¹ * s⁻¹, t, z, hs', htLH, htt, hzZ, ?_, ?_⟩
  · rw [claim z hzZ]
    intro h1
    exact hta (commutatorElement_eq_one_iff_mul_comm.mp h1)
  · intro z' hz'
    exact ⟨⁅z', s⁆, hs.2.2 z' (Subgroup.mem_inf.mp hz').1, claim z' hz'⟩

end CFSG.Quasithin.H13.Ch4.CentK
