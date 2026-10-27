module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieFld
public import CFSG.LocalAnalysis.EvenBN.U4.Model.CentralizerZ2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.I43Dihedral.GroupLemmas
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLocDatum

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem mem_normalizer_sg_iff {M : Subgroup (GL (Fin 4) K)} (hM : M ≤ gramSU h (miyamotoJ4 K))
    {x : Xg h} : x ∈ Subgroup.normalizer ((sg h M : Subgroup (Xg h)) : Set (Xg h)) ↔
      (x : GL (Fin 4) K) ∈ Subgroup.normalizer (M : Set (GL (Fin 4) K)) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hx y
    constructor
    · intro hy
      exact (hx ⟨y, hM hy⟩).1 hy
    · intro hy
      have hyS : y ∈ gramSU h (miyamotoJ4 K) := by
        have := mul_mem (mul_mem (inv_mem x.2) (hM hy)) x.2
        simpa [mul_assoc] using this
      exact (hx ⟨y, hyS⟩).2 hy
  · intro hx y
    exact hx (y : GL (Fin 4) K)

theorem mem_Pt_iff {x : Xg h} :
    x ∈ Pt h ↔ (x : GL (Fin 4) K) ∈ Subgroup.normalizer (miyamotoA2 h : Set (GL (Fin 4) K)) :=
  mem_normalizer_sg_iff h (miyamotoUnipotent_le_SU h false true)

theorem mem_Ln_iff {x : Xg h} :
    x ∈ Ln h ↔ (x : GL (Fin 4) K) ∈ Subgroup.normalizer (miyamotoA1 h : Set (GL (Fin 4) K)) :=
  mem_normalizer_sg_iff h (miyamotoUnipotent_le_SU h true false)

theorem mem_Pt_iff_levi {x : Xg h} :
    x ∈ Pt h ↔ (x : GL (Fin 4) K) ∈ miyamotoA2 h ⊔ (miyamotoI2 h ⊔ miyamotoN2 h) := by
  rw [mem_Pt_iff, ← normalizer_miyamotoA2 h]
  exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩

theorem mem_Ln_iff_levi {x : Xg h} :
    x ∈ Ln h ↔ (x : GL (Fin 4) K) ∈ miyamotoA1 h ⊔ (miyamotoI1 h ⊔ miyamotoN1 h) := by
  rw [mem_Ln_iff, ← normalizer_miyamotoA1 h]
  exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩

theorem cls_Xg (x : Xg h) (hx : orderOf x = 2) : IsConj (z1X h) x ∨ IsConj (z2X h) x := by
  have hxGL : orderOf (x : GL (Fin 4) K) = 2 :=
    (orderOf_injective (gramSU h (miyamotoJ4 K)).subtype (Subgroup.subtype_injective _)
      x).trans hx
  obtain ⟨g, hg, hc⟩ := miyamoto_involutions h x.2 hxGL
  rcases hc with hc | hc
  · refine Or.inl (isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext ?_⟩)
    show g * miyamotoZ1 K * g⁻¹ = (x : GL (Fin 4) K)
    rw [← hc]
    group
  · refine Or.inr (isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext ?_⟩)
    show g * LocalAnalysis.miyamotoZ2 K * g⁻¹ = (x : GL (Fin 4) K)
    rw [← hc]
    group

theorem noconj_Xg (α : MulAut (Xg h)) : α (z1X h) ≠ z2X h := by
  intro e
  obtain ⟨s, hs⟩ := exists_eq_conj_mul_fieldAut h α
  rw [hs, MulAut.mul_apply, show miyamotoFieldAut h (miyamotoFieldFactor h α) = fa h _ from rfl,
    fa_z1X, MulAut.conj_apply] at e
  have e' := congrArg (fun x : Xg h => (x : GL (Fin 4) K)) e
  refine miyamotoZ1_not_conj_Z2 (K := K) (s : GL (Fin 4) K)⁻¹ ?_
  rw [inv_inv]
  exact e'

theorem commute_Z_of_commute_z1 {g : GL (Fin 4) K}
    (hc : g * miyamotoXGL h 0 0 0 1 = miyamotoXGL h 0 0 0 1 * g) (d : K) :
    miyamotoXGL h 0 0 0 d * g = g * miyamotoXGL h 0 0 0 d := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_miyamotoXGL]
  have hc' : Commute (g : Matrix (Fin 4) (Fin 4) K) (miyamotoX h 0 0 0 1) := by
    have := congrArg Units.val hc
    simp only [Units.val_mul, coe_miyamotoXGL] at this
    exact this
  have hX : miyamotoX h 0 0 0 d = 1 + d • (miyamotoX h 0 0 0 1 - 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [miyamotoX]
  rw [hX]
  exact ((Commute.one_right _).add_right
    ((hc'.sub_right (Commute.one_right _)).smul_right d)).symm.eq

theorem cz_Xg : Subgroup.centralizer ({z1X h} : Set (Xg h)) ≤ Pt h := by
  intro g hg
  rw [mem_Pt_iff]
  have hc : (g : GL (Fin 4) K) * miyamotoXGL h 0 0 0 1 = miyamotoXGL h 0 0 0 1 * g := by
    have := congrArg (fun x : Xg h => (x : GL (Fin 4) K))
      (Subgroup.mem_centralizer_singleton_iff.1 hg)
    simpa [coe_z1X] using this
  have hC : (g : GL (Fin 4) K) ∈ Subgroup.centralizer (miyamotoZ h : Set (GL (Fin 4) K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨d, -, rfl⟩
    exact commute_Z_of_commute_z1 h hc d
  have hN : (g : GL (Fin 4) K) ∈ Subgroup.normalizer (miyamotoZ h : Set (GL (Fin 4) K)) :=
    centralizer_le_normalizer _ hC
  exact ((normalizer_miyamotoZ h).le (Subgroup.mem_inf.2 ⟨g.2, hN⟩)).2

theorem ct_Xg : Subgroup.centralizer ({z2X h} : Set (Xg h)) ≤ Ln h := by
  intro g hg
  rw [mem_Ln_iff]
  have hc : (g : GL (Fin 4) K) * LocalAnalysis.miyamotoZ2 K = LocalAnalysis.miyamotoZ2 K * g := by
    have := congrArg (fun x : Xg h => (x : GL (Fin 4) K))
      (Subgroup.mem_centralizer_singleton_iff.1 hg)
    exact this
  have hmem : (g : GL (Fin 4) K) ∈ gramSU h (miyamotoJ4 K) ⊓
      Subgroup.centralizer ({LocalAnalysis.miyamotoZ2 K} : Set (GL (Fin 4) K)) :=
    Subgroup.mem_inf.2 ⟨g.2, Subgroup.mem_centralizer_singleton_iff.2 hc⟩
  rw [centralizer_miyamotoZ2 h] at hmem
  exact (sup_le Subgroup.le_normalizer
    ((miyamotoN1F_le_N1 h).trans (miyamotoN1_le_normalizer_A1 h))) hmem

@[expose] def r1X : Xg h := ⟨miyamotoR1 K, miyamotoR1_mem_gramSU h⟩

@[expose] def r2X : Xg h := ⟨miyamotoR2 K, miyamotoR2_mem_gramSU h⟩

theorem r2X_mem_centralizer_z1X : r2X h ∈ Subgroup.centralizer ({z1X h} : Set (Xg h)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  show miyamotoR2 K * miyamotoZ1 K = miyamotoZ1 K * miyamotoR2 K
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [miyamotoR2, miyamotoZ1, Matrix.mul_apply, Fin.sum_univ_four]

theorem r1X_mem_centralizer_z2X : r1X h ∈ Subgroup.centralizer ({z2X h} : Set (Xg h)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  show miyamotoR1 K * LocalAnalysis.miyamotoZ2 K = LocalAnalysis.miyamotoZ2 K * miyamotoR1 K
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [miyamotoR1, LocalAnalysis.miyamotoZ2, Matrix.mul_apply, Fin.sum_univ_four]

theorem r1X_mem_Ln : r1X h ∈ Ln h :=
  (mem_Ln_iff h).2 (miyamotoN1_le_normalizer_A1 h (miyamotoR1_mem_N1 h))

theorem r2X_mem_Pt : r2X h ∈ Pt h :=
  (mem_Pt_iff h).2 (miyamotoN2_le_normalizer_A2 h (miyamotoR2_mem_N2 h))

theorem r2X_not_mem_Ln : r2X h ∉ Ln h := by
  intro hr
  have h1 := (shapeOne_of_mem_normalizer_A1 h ((mem_Ln_iff h).1 hr)).2.2.1
  simp [r2X, miyamotoR2] at h1

theorem r1X_not_mem_Pt : r1X h ∉ Pt h := by
  intro hr
  have hN := normalizer_A2_le_normalizer_Z h ((mem_Pt_iff h).1 hr)
  have h1 := (shapeTwo_of_mem_normalizer_Z h hN).2.2
  simp [r1X, miyamotoR1] at h1

theorem nz_Xg : ¬ Subgroup.centralizer ({z1X h} : Set (Xg h)) ≤ Ln h := fun hle =>
  r2X_not_mem_Ln h (hle (r2X_mem_centralizer_z1X h))

theorem nt_Xg : ¬ Subgroup.centralizer ({z2X h} : Set (Xg h)) ≤ Pt h := fun hle =>
  r1X_not_mem_Pt h (hle (r1X_mem_centralizer_z2X h))

end CFSG.Quasithin.H13.F431.Un.OL
