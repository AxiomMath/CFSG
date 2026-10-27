module

public import CFSG.Quasithin.Vol2.Ch11SecO3CXa
public import CFSG.Quasithin.Vol2.Ch11SecFQ2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF.O3CX

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.QuasithinUnique.C5 (conjSubgroup_eq_self)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ V₂ V₃ : Subgroup G}

theorem wH_le_normalizer_fsuV (hF : Sp4Facts) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h1154 : Stmt11_5_4) (h1156 : Stmt11_5_6)
    (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) (hk : KindSp4 L (fsuV T I) n) :
    wH T I V₁ ≤ Subgroup.normalizer (fsuV T I : Set G) :=
  ((conjClosure_le_pCoreOf (fsuV_le_pCoreOf_normalizer hF h1102 h1103 h1141 h1143 h1154 h1156
    h hV₁ hk)).trans (pCoreOf_normalizer_V₁_le_T h hV₁)).trans (SecA.T_le_normalizer_fsuV T I)

omit [Finite G] in
theorem conj_le_normalizer {W V : Subgroup G} {y : G} (hW : W ≤ Subgroup.normalizer (V : Set G))
    (hy : y ∈ Subgroup.normalizer (V : Set G)) :
    conjSubgroup W y ≤ Subgroup.normalizer (V : Set G) := by
  intro w hw
  have h1 : y * w * y⁻¹ ∈ Subgroup.normalizer (V : Set G) := hW (mem_conjSubgroup_iff.mp hw)
  have e : w = y⁻¹ * (y * w * y⁻¹) * y := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hy) h1) hy

theorem inf_le_centralizer (hF : Sp4Facts) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1113 : Stmt11_1_3) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h1154 : Stmt11_5_4)
    (h1156 : Stmt11_5_6) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hV₂ : IsVi T L I n 2 V₂) (hV₃ : IsVi T L I n 3 V₃) (hk : KindSp4 L (fsuV T I) n)
    (hV₁₃ : V₁ ≤ V₃) {y : G} (hy : y ∈ L) (hopp : conjSubgroup V₁ y ⊓ V₃ = ⊥) :
    wH T I V₁ ⊓ conjSubgroup (wH T I V₁) y ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  have hVW := commutator_fsuV_conjClosure_le hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁
    hV₂ hV₃ hk
  have hyV := SecA.L_le_normalizer_fsuV h hy
  intro d hd
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 : ⁅v, d⁆ ∈ V₁ := hVW (Subgroup.commutator_mem_commutator hv hd.1)
  have h2 : ⁅v, d⁆ ∈ conjSubgroup V₁ y := by
    rw [mem_conjSubgroup_iff]
    have hv' : y * v * y⁻¹ ∈ fsuV T I := (Subgroup.mem_normalizer_iff.mp hyV v).mp hv
    have e : y * ⁅v, d⁆ * y⁻¹ = ⁅y * v * y⁻¹, y * d * y⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hVW (Subgroup.commutator_mem_commutator hv' (mem_conjSubgroup_iff.mp hd.2))
  have h3 : ⁅v, d⁆ ∈ conjSubgroup V₁ y ⊓ V₃ := ⟨h2, hV₁₃ h1⟩
  rw [hopp, Subgroup.mem_bot] at h3
  exact commutatorElement_eq_one_iff_mul_comm.mp h3

theorem frame_of (hF : Sp4Facts) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1113 : Stmt11_1_3) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h1154 : Stmt11_5_4)
    (h1156 : Stmt11_5_6) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hV₂ : IsVi T L I n 2 V₂) (hV₃ : IsVi T L I n 3 V₃) (hk : KindSp4 L (fsuV T I) n)
    (hV₁₃ : V₁ ≤ V₃) {y : G} (hy : y ∈ L) (hopp : conjSubgroup V₁ y ⊓ V₃ = ⊥) :
    Frame (wH T I V₁) (conjSubgroup (wH T I V₁) y) (Subgroup.centralizer (fsuV T I : Set G)) := by
  have hWW := commutator_wH_le hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁ hV₂ hV₃ hk
  have hWV := wH_le_normalizer_fsuV hF h1102 h1103 h1141 h1143 h1154 h1156 h hV₁ hk
  have hyV := SecA.L_le_normalizer_fsuV h hy
  have hV₁V := SecA.IsVi.le_fsuV hV₁
  have hVW : fsuV T I ≤ wH T I V₁ := le_conjClosure_self _ _
  have hVW' : fsuV T I ≤ conjSubgroup (wH T I V₁) y := fsuV_le_conj_wH h hy
  have hVy : conjSubgroup (fsuV T I) y = fsuV T I := conjSubgroup_eq_self hyV
  have hconj : ∀ x : G, y * x * y⁻¹ ∈ V₁ → x ∈ wH T I V₁ := fun x hx => by
    have h1 : x ∈ conjSubgroup (fsuV T I) y := mem_conjSubgroup_iff.mpr (hV₁V hx)
    rw [hVy] at h1
    exact hVW h1
  refine
    { cW := centralizer_le_normalizer_wH hV₁
      cW' := centralizer_le_normalizer_conj_wH h hV₁ hy
      wC := fun w hw => mem_normalizer_centralizer' (hWV hw)
      w'C := fun w hw => mem_normalizer_centralizer' (conj_le_normalizer hWV hyV hw)
      ww := fun a ha b hb => hVW' (hV₁V (hWW (Subgroup.commutator_mem_commutator ha hb)))
      w'w' := fun a ha b hb => hconj _ ?_
      sqw := fun a ha => by
        rw [← sq]
        exact hVW' (hV₁V (sq_mem_of_mem_wH hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁
          hV₂ hV₃ hk hV₁₃ ha))
      sqw' := fun a ha => hconj _ ?_
      dC := inf_le_centralizer hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁ hV₂ hV₃ hk
        hV₁₃ hy hopp
      qq := fun a ha b hb => commutator_qOf_le hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁
        hV₂ hV₃ hk hy (Subgroup.commutator_mem_commutator ha hb)
      sqq := fun a ha => by
        rw [← sq]
        exact sq_mem_of_mem_qOf hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁ hV₂ hV₃ hk
          hV₁₃ hy ha }
  · have h1 := hWW (Subgroup.commutator_mem_commutator (mem_conjSubgroup_iff.mp ha)
      (mem_conjSubgroup_iff.mp hb))
    have e : ⁅y * a * y⁻¹, y * b * y⁻¹⁆ = y * (a * b * a⁻¹ * b⁻¹) * y⁻¹ := by
      simp only [commutatorElement_def]
      group
    rwa [e] at h1
  · have h1 := sq_mem_of_mem_wH hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁ hV₂ hV₃ hk
      hV₁₃ (mem_conjSubgroup_iff.mp ha)
    have e : (y * a * y⁻¹) ^ 2 = y * (a * a) * y⁻¹ := by
      simp only [sq]
      group
    rwa [e] at h1

end CFSG.Quasithin.Vol2.Ch11.SecF.O3CX
