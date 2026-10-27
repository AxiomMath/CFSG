module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab8Lab
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3SNbr

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab6
  CFSG.Quasithin.F6.GoldAmLab7

namespace F6

namespace GoldAmLab8

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {V V₂ : Subgroup D} {z c : D}

theorem false_of_two_slides (d : Doubled A B z V c V₂) (h3 : GoldAmL3.GoldHyp3 A B z V) {m : ℕ}
    (hm : 2 ≤ m)
    (hreach : ∀ x y : CosetGeom (A ⊔ B) A B, CosetGeom.dist x y < m + 2 →
      Nm A B V V₂ x ≤ ballStab 1 y)
    {r : ℕ → CosetGeom (A ⊔ B) A B} (hr : IsGeo r (m + 2))
    {μ ν : CosetGeom (A ⊔ B) A B} (hμ : (graph (A ⊔ B) A B).Adj (r (m + 2)) μ)
    (hμn : ¬ Nm A B V V₂ μ ≤ ballStab 1 (r 1))
    (hν : (graph (A ⊔ B) A B).Adj (r 0) ν)
    (hνn : ¬ Nm A B V V₂ ν ≤ ballStab 1 (r (m + 1))) : False := by
  have h := d.sys
  have hdist : ∀ i j, i ≤ j → j ≤ m + 2 → CosetGeom.dist (r i) (r j) = j - i := hr
  have hadj : ∀ i, i < m + 2 → (graph (A ⊔ B) A B).Adj (r i) (r (i + 1)) := fun i hi => hr.adj hi
  have hμd : CosetGeom.dist μ (r (m + 2)) = 1 := by
    rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr hμ
  have hμ2 : CosetGeom.dist μ (r 2) < m + 2 := by
    have h1 := CosetGeom.dist_triangle (G₁ := A) (G₂ := B) rfl μ (r (m + 2)) (r 2)
    have h2 := hdist 2 (m + 2) (by omega) le_rfl
    rw [CosetGeom.dist_comm] at h2
    omega
  have hle1 : Nm A B V V₂ μ ≤ stab (r 1) := fun n hn =>
    ballStab_le_stab_of_dist_le (n := 1) (γ := r 2) (δ := r 1)
      (dist_eq_one_iff_adj.mpr (hadj 1 (by omega)).symm).le (hreach μ (r 2) hμ2 hn)
  have hnot1 : ¬ Nm A B V V₂ (r 1) ≤ ballStab 1 μ :=
    not_nm_le_symm (goodV_all h μ) (goodV_all h (r 1)) hle1 hμn
  have hxq : Nm A B V V₂ (r 1) ≤ ballStab 1 (r (m + 2)) :=
    hreach (r 1) (r (m + 2)) (by have := hdist 1 (m + 2) (by omega) le_rfl; omega)
  obtain ⟨t, htx, hty⟩ := exists_isLab_pair h (x := r 1) (y := μ) (p := r 2) (q := r (m + 2))
    hμ.symm (hadj 1 (by omega)).symm hxq (hreach μ (r 2) hμ2) hnot1
  obtain ⟨g, hgN, hgn⟩ := IsConcreteLE.not_le_iff_exists.mp hνn
  have hν2 : CosetGeom.dist ν (r 2) < m + 2 := by
    have h1 := CosetGeom.dist_triangle (G₁ := A) (G₂ := B) rfl ν (r 0) (r 2)
    have h2 := hdist 0 2 (by omega) (by omega)
    have h3' : CosetGeom.dist ν (r 0) = 1 := by
      rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr hν
    omega
  have hνm : CosetGeom.dist ν (r m) < m + 2 := by
    have h1 := CosetGeom.dist_triangle (G₁ := A) (G₂ := B) rfl ν (r 0) (r m)
    have h2 := hdist 0 m (by omega) (by omega)
    have h3' : CosetGeom.dist ν (r 0) = 1 := by
      rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr hν
    omega
  have hg2 : g ∈ stab (r 2) := ballStab_le_stab 1 (r 2) (hreach ν (r 2) hν2 hgN)
  have hgm : g ∈ ballStab 1 (r m) := hreach ν (r m) hνm hgN
  have hgm' : g ∈ stab (r m) := ballStab_le_stab 1 (r m) hgm
  have hgm1 : g ∈ stab (r (m + 1)) :=
    ballStab_le_stab_of_dist_le (n := 1) (γ := r m) (δ := r (m + 1))
      (dist_eq_one_iff_adj.mpr (hadj m (by omega))).le hgm
  have hgG : g ∈ A ⊔ B := stab_le (r 2) hg2
  have hfixm : (⟨g, hgG⟩ : ↥(A ⊔ B)) • r (m + 1) = r (m + 1) := smul_eq_of_mem_stab hgm1
  have hfix := eq_of_isLab d htx hty (hadj (m + 1) (by omega)) ⟨g, hgG⟩ hg2 hfixm
  have hgn' : g ∈ stab (r (m + 2)) := mem_stab_of_smul_eq hfix
  exact hgn (h3.mem_ballStab_one_of_fix_two' (u := r (m + 1)) (v := r m) (w := r (m + 2))
    (hadj m (by omega)).symm (hadj (m + 1) (by omega)) (hr.ne (i := m) (j := m + 2) (by omega)
      le_rfl) hgm1 hgm' hgn')

end GoldAmLab8

end F6

end CFSG.Quasithin
