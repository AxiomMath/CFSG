module

public import CFSG.Quasithin.Vol2.Ch10Reselect.ActML2
public import CFSG.Quasithin.Vol2.Ch10Reselect.ModelAlgNorm

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10 CFSG.Quasithin.Vol2.Ch10.SecA
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {K : Type} [Field K]

theorem exists_corrector (hAut : AutSL2Exists)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hlt : L < fsuL0 T L) (hA : Concl326A T L I) [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (M : RModel T L I K) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {γ : G} (hγ : γ ∈ fsuML T L) {g : Matrix.SpecialLinearGroup (Fin 2) K} {B : GL (Fin 2) K}
    (hφ : actML M ⟨γ, hγ⟩ = phi K g 1 B) :
    ∃ (z : G) (hz : z ∈ fsuML T L) (σ : RingAut K) (B₂ : GL (Fin 2) K),
      actML M ⟨z, hz⟩ = bPerm K B ∧
      actML M ⟨t * z * t⁻¹, conj_mem_fsuML h37 h38 hfsu hlt (le_fsuM T L ht) hz⟩ = phi K 1 σ B₂ := by
  have hγ' : t * γ * t⁻¹ ∈ fsuML T L := conj_mem_fsuML h37 h38 hfsu hlt (le_fsuM T L ht) hγ
  obtain ⟨g₂, σ, B₂, hγ₂⟩ :=
    normStruct hAut hK (actML M ⟨t * γ * t⁻¹, hγ'⟩) (actML_add M _) (actML_hnorm M _)
  obtain ⟨a, ha⟩ := M.γ_surj g
  obtain ⟨y, hy⟩ := M.γ_surj g₂
  have haN : (a : G) ∈ fsuML T L := L_le_fsuML a.2
  have hyN : (y : G) ∈ fsuML T L := L_le_fsuML y.2
  have hb : t⁻¹ * (y : G) * t ∈ CFSG.conjugate L t := by
    rw [mem_conjugate_iff]
    have e : t * (t⁻¹ * (y : G) * t) * t⁻¹ = (y : G) := by group
    rw [e]
    exact y.2
  have hbN : t⁻¹ * (y : G) * t ∈ fsuML T L := conjugate_le_fsuML h37 h38 hfsu hlt ht htn hb
  have hz : (a : G)⁻¹ * (t⁻¹ * (y : G) * t)⁻¹ * γ ∈ fsuML T L :=
    (fsuML T L).mul_mem ((fsuML T L).mul_mem ((fsuML T L).inv_mem haN)
      ((fsuML T L).inv_mem hbN)) hγ
  refine ⟨(a : G)⁻¹ * (t⁻¹ * (y : G) * t)⁻¹ * γ, hz, σ, B₂, ?_, ?_⟩
  ·
    have e : (⟨(a : G)⁻¹ * (t⁻¹ * (y : G) * t)⁻¹ * γ, hz⟩ : ↥(fsuML T L)) =
        (⟨(a : G), haN⟩ : ↥(fsuML T L))⁻¹ * (⟨t⁻¹ * (y : G) * t, hbN⟩ : ↥(fsuML T L))⁻¹ *
          (⟨γ, hγ⟩ : ↥(fsuML T L)) := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
    have hA1 : actML M ⟨(a : G), haN⟩ = rhoSL K g := by
      rw [← ha]
      exact actML_of_mem_L M a
    have hB1 : actML M ⟨t⁻¹ * (y : G) * t, hbN⟩ = 1 :=
      actML_eq_one_of_mem_conjugate h37 h38 hfsu hlt hA ht htn M hb
    rw [e, map_mul, map_mul, map_inv, map_inv, hA1, hB1, hφ, inv_one, mul_one,
      ← map_inv (rhoSL K) g, rhoSL_mul_phi, inv_mul_cancel, bPerm_eq_phi]
  ·
    have hTa : t * (a : G) * t⁻¹ ∈ CFSG.conjugate L t :=
      mul_mem_conjugate_of_mem h37 h38 hfsu hlt ht htn a.2
    have hTaN : t * (a : G) * t⁻¹ ∈ fsuML T L := conjugate_le_fsuML h37 h38 hfsu hlt ht htn hTa
    have e : (⟨t * ((a : G)⁻¹ * (t⁻¹ * (y : G) * t)⁻¹ * γ) * t⁻¹,
        conj_mem_fsuML h37 h38 hfsu hlt (le_fsuM T L ht) hz⟩ : ↥(fsuML T L)) =
        (⟨t * (a : G) * t⁻¹, hTaN⟩ : ↥(fsuML T L))⁻¹ *
          (⟨(y : G), hyN⟩ : ↥(fsuML T L))⁻¹ * (⟨t * γ * t⁻¹, hγ'⟩ : ↥(fsuML T L)) := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hTa1 : actML M ⟨t * (a : G) * t⁻¹, hTaN⟩ = 1 :=
      actML_eq_one_of_mem_conjugate h37 h38 hfsu hlt hA ht htn M hTa
    have hY : actML M ⟨(y : G), hyN⟩ = rhoSL K g₂ := by
      rw [← hy]
      exact actML_of_mem_L M y
    rw [e, map_mul, map_mul, map_inv, map_inv, hTa1, hY, hγ₂, inv_one, one_mul,
      ← map_inv (rhoSL K) g₂, rhoSL_mul_phi, inv_mul_cancel]

end CFSG.Quasithin.Vol2.Ch10Reselect
