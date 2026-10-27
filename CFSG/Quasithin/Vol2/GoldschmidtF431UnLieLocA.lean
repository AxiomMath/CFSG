module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.CentralizerZ2
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieFld

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.LL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.EvenBN.U4 CFSG.Quasithin.H13.F431.Un.OL

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

section Groups

@[expose] def ucGL : Subgroup (GL (Fin 4) K) where
  carrier := {g | ∃ c, h.bar c = c ∧ g = miyamotoXGL h 0 0 c 0}
  mul_mem' := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
    refine ⟨c + c', by rw [map_add, hc, hc'], ?_⟩
    rw [miyamotoXGL_mul_A1 h (map_zero _), add_zero]
  one_mem' := ⟨0, map_zero _, Units.ext (by simp [coe_miyamotoXGL, miyamotoX_zero])⟩
  inv_mem' := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, hc, inv_eq_of_mul_eq_one_right (miyamotoXGL_A1_mul_self h (map_zero _))⟩

theorem miyamotoXGL_mem_ucGL {c : K} (hc : h.bar c = c) : miyamotoXGL h 0 0 c 0 ∈ ucGL h :=
  ⟨c, hc, rfl⟩

theorem ucGL_le : ucGL h ≤ miyamotoA1 h ⊓ miyamotoCu h := by
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨(miyamotoXGL_mem_A1 h).2 ⟨rfl, map_zero _, map_zero _⟩,
    (miyamotoXGL_mem_Cu h).2 ⟨map_zero _, map_zero _, hc, map_zero _⟩⟩

abbrev Vx : Subgroup (Xg h) := sg h (miyamotoA1 h ⊓ miyamotoCu h)

abbrev Ux : Subgroup (Xg h) := sg h (ucGL h)

abbrev Kx : Subgroup (Xg h) :=
  sg h ((miyamotoA1 h ⊓ miyamotoCu h) ⊔ (miyamotoN1 h ⊓ miyamotoCu h))

abbrev Cx : Subgroup (Xg h) := Subgroup.centralizer ({z2X h} : Set (Xg h))

theorem cent_z2X : Cx h = sg h (miyamotoA1 h ⊔ miyamotoN1F h) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, ← centralizer_miyamotoZ2 h]
  constructor
  · intro hg
    refine ⟨g.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact congrArg Subtype.val hg
  · rintro ⟨-, hg⟩
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hg)

end Groups

section Central

theorem N1Hom_comm_uc {m : SpecialLinearGroup (Fin 2) K}
    (hm : ∀ i j, h.bar ((m : Matrix (Fin 2) (Fin 2) K) i j) = (m : Matrix (Fin 2) (Fin 2) K) i j)
    {c : K} (hc : h.bar c = c) :
    miyamotoN1Hom h m * miyamotoXGL h 0 0 c 0 = miyamotoXGL h 0 0 c 0 * miyamotoN1Hom h m := by
  have key := miyamotoN1Hom_conj_A1 h m (b := 0) (c := c) (d := 0) (map_zero _) (map_zero _)
  have hdet := m.2
  rw [Matrix.det_fin_two] at hdet
  have e : (miyamotoN1Hom h m)⁻¹ * miyamotoXGL h 0 0 c 0 * miyamotoN1Hom h m =
      miyamotoXGL h 0 0 c 0 := by
    rw [key, miyamotoXGL_inj]
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simp only [hm, hc]
      ring
    · simp only [hm, hc]
      linear_combination c * hdet
    · simp only [hm, hc]
      ring
  calc miyamotoN1Hom h m * miyamotoXGL h 0 0 c 0
      = miyamotoN1Hom h m * ((miyamotoN1Hom h m)⁻¹ * miyamotoXGL h 0 0 c 0 *
          miyamotoN1Hom h m) := by rw [e]
    _ = miyamotoXGL h 0 0 c 0 * miyamotoN1Hom h m := by group

theorem exists_of_mem_Cx {s : Xg h} (hs : s ∈ Cx h) :
    ∃ b c d : K, h.bar b = b ∧ h.bar d = d ∧ ∃ m : SpecialLinearGroup (Fin 2) K,
      (∀ i j, h.bar ((m : Matrix (Fin 2) (Fin 2) K) i j) = (m : Matrix (Fin 2) (Fin 2) K) i j) ∧
        (s : GL (Fin 4) K) = miyamotoXGL h 0 b c d * miyamotoN1Hom h m := by
  rw [cent_z2X h, Subgroup.mem_subgroupOf, ← centralizer_miyamotoZ2 h] at hs
  exact exists_of_mem_centralizer_miyamotoZ2 h hs

theorem Ux_central {s u : Xg h} (hs : s ∈ Cx h) (hu : u ∈ Ux h) : s * u = u * s := by
  obtain ⟨c, hc, hu'⟩ := Subgroup.mem_subgroupOf.1 hu
  obtain ⟨b, c', d, hb, hd, m, hm, hsm⟩ := exists_of_mem_Cx h hs
  apply Subtype.ext
  show (s : GL (Fin 4) K) * (u : GL (Fin 4) K) = (u : GL (Fin 4) K) * (s : GL (Fin 4) K)
  have hb0 : h.bar (0 : K) = 0 := map_zero _
  calc (s : GL (Fin 4) K) * (u : GL (Fin 4) K)
      = miyamotoXGL h 0 b c' d * (miyamotoN1Hom h m * miyamotoXGL h 0 0 c 0) := by
        rw [hsm, hu', mul_assoc]
    _ = miyamotoXGL h 0 b c' d * (miyamotoXGL h 0 0 c 0 * miyamotoN1Hom h m) := by
        rw [N1Hom_comm_uc h hm hc]
    _ = (miyamotoXGL h 0 0 c 0 * miyamotoXGL h 0 b c' d) * miyamotoN1Hom h m := by
        rw [← mul_assoc, miyamotoXGL_mul_A1 h hb, miyamotoXGL_mul_A1 h hb0, add_comm b, add_comm c',
          add_comm d]
    _ = (u : GL (Fin 4) K) * (s : GL (Fin 4) K) := by rw [hsm, hu', mul_assoc]

theorem Cx_normalizes_Vx {s v : Xg h} (hs : s ∈ Cx h) (hv : v ∈ Vx h) : s * v * s⁻¹ ∈ Vx h := by
  obtain ⟨b, c', d, hb, hd, m, hm, hsm⟩ := exists_of_mem_Cx h hs
  have hv' := Subgroup.mem_subgroupOf.1 hv
  have hN := miyamotoN1Hom_mem_N1_inf_Cu h hm
  have hw := (Subgroup.mem_normalizer_iff.1 (miyamotoN1Cu_le_normalizer h hN)
    (v : GL (Fin 4) K)).1 hv'
  have hx : miyamotoXGL h 0 b c' d ∈ miyamotoA1 h := (miyamotoXGL_mem_A1 h).2 ⟨rfl, hb, hd⟩
  refine Subgroup.mem_subgroupOf.2 ?_
  show (s : GL (Fin 4) K) * (v : GL (Fin 4) K) * (s : GL (Fin 4) K)⁻¹ ∈ _
  have e : (s : GL (Fin 4) K) * (v : GL (Fin 4) K) * (s : GL (Fin 4) K)⁻¹ =
      miyamotoXGL h 0 b c' d * (miyamotoN1Hom h m * (v : GL (Fin 4) K) *
        (miyamotoN1Hom h m)⁻¹) * (miyamotoXGL h 0 b c' d)⁻¹ := by
    rw [hsm]
    group
  rw [e, mul_inv_eq_iff_eq_mul.2 (mul_comm_of_mem_miyamotoA1 h hx hw.1)]
  exact hw

end Central

end CFSG.Quasithin.H13.F431.Un.LL
