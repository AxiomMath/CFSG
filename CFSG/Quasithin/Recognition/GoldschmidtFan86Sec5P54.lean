module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P53b
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PGlue

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem Line.involution_mem_edgeCirc (ℓ : Line Γ) {z : G} (hzz : z * z = 1) {i : ℤ}
    (h1 : z • ℓ.vert i = ℓ.vert i) (h2 : z • ℓ.vert (i + 1) = ℓ.vert (i + 1)) :
    z ∈ ℓ.edgeCirc (G := G) i := by
  have hz' : z ∈ ℓ.edgeStab (G := G) i :=
    ⟨MulAction.mem_stabilizer_iff.2 h1, MulAction.mem_stabilizer_iff.2 h2⟩
  unfold Line.edgeCirc
  split_ifs
  · exact ⟨hz', by rw [hzz]; exact one_mem _⟩
  · exact ⟨⟨hz'.2, hz'.1⟩, by rw [hzz]; exact one_mem _⟩

theorem fan54_right_b (F : FanTree Γ G) (h36 : Fan36 F) (h40 : Fan40 F) (ℓ : Line Γ) {z : G}
    (hzz : z * z = 1) {a b : ℤ} (hcore : ℓ.IsCoreC z a b) :
    ∀ x ∈ MulAction.stabilizer G (ℓ.vert b), x ∉ MulAction.stabilizer G (ℓ.vert (b - 1)) →
      x * z ≠ z * x := by
  intro x hx hxm hxz
  obtain ⟨hab, hfix, hcen, -, hmax⟩ := hcore
  have hxb : x • ℓ.vert b = ℓ.vert b := MulAction.mem_stabilizer_iff.1 hx
  have hxm' : x • ℓ.vert (b - 1) ≠ ℓ.vert (b - 1) := fun h =>
    hxm (MulAction.mem_stabilizer_iff.2 h)
  have hzb1 : z • ℓ.vert (b - 1) = ℓ.vert (b - 1) := hfix (b - 1) (by omega) (by omega)
  have hzb : z • ℓ.vert b = ℓ.vert b := hfix b hab.le le_rfl
  have hcen' : ∀ s ∈ ℓ.edgeCirc (G := G) (b - 1), s * z = z * s := (hcen (b - 1) (by omega)
    (by omega)).2
  set L := ℓ.glue b x F hxb hxm' with hL
  have hs := not_lineSingLe_of_fan40 h40 L (n := 2 - 1) (by norm_num)
  obtain ⟨y, hyH, hyo⟩ := fan51a F h36 h40 L (b - 1) 2 le_rfl hs 1 le_rfl (by norm_num)
  have e1 : b - 1 + ((1 : ℕ) : ℤ) = b := by push_cast; ring
  have e2 : b - 1 + ((2 - 1 : ℕ) : ℤ) = b := by norm_num
  have hLb : L.vert b = ℓ.vert b := by
    rw [hL]
    exact ℓ.glue_vert_le b x F hxb hxm' le_rfl
  rw [e2] at hyH
  rw [e1] at hyo
  rw [hLb] at hyH hyo
  have hyC : y ∈ Subgroup.centralizer ({z} : Set G) := by
    refine closure_le_centralizer (S := L.edgeCirc (b - 1) ∪ L.edgeCirc b) ?_ hyH.1
    rintro s (hs | hs)
    · rw [hL, ℓ.glue_edgeCirc_le b x F hxb hxm' (i := b - 1) (by omega)] at hs
      exact hcen' s hs
    · exact ℓ.glue_edgeCirc_cen b x F hxb hxm' hxz (i := b) (j := b - 1) le_rfl (by omega) hcen'
        s hs
  have hcy : Commute y z := (Subgroup.mem_centralizer_iff.1 hyC z rfl).symm
  have hadj : Γ.Adj (ℓ.vert b) (ℓ.vert (b - 1)) := by
    have := (ℓ.adj (b - 1)).symm
    rwa [show b - 1 + 1 = b by omega] at this
  have hadj' : Γ.Adj (ℓ.vert b) (ℓ.vert (b + 1)) := ℓ.adj b
  obtain ⟨i, hi⟩ := F.exists_pow_smul_eq hyH.2 hyo hadj hadj'
  have hci : Commute (y ^ i) z := hcy.pow_left i
  have hzb2 : z • ℓ.vert (b + 1) = ℓ.vert (b + 1) := by
    rw [← hi, ← mul_smul, ← hci.eq, mul_smul, hzb1]
  refine hmax ⟨hzb, ?_, fun h hh => ?_⟩
  · exact ℓ.involution_mem_edgeCirc hzz hzb hzb2
  · have hyb : (y ^ i)⁻¹ • ℓ.vert b = ℓ.vert b := by
      rw [inv_smul_eq_iff]
      exact (MulAction.mem_stabilizer_iff.1 ((MulAction.stabilizer G (ℓ.vert b)).pow_mem
        hyH.2 i)).symm
    have hyb1 : (y ^ i)⁻¹ • ℓ.vert (b + 1) = ℓ.vert (b - 1) := by
      rw [inv_smul_eq_iff, hi]
    have h1 := F.Ecirc_smul (y ^ i)⁻¹ (show h ∈ Ecirc Γ G (ℓ.vert b) (ℓ.vert (b + 1)) from hh)
    rw [hyb, hyb1, F.Ecirc_comm hadj] at h1
    have h1' : (y ^ i)⁻¹ * h * (y ^ i)⁻¹⁻¹ ∈ ℓ.edgeCirc (G := G) (b - 1) := by
      rw [Line.edgeCirc_eq_Ecirc, show b - 1 + 1 = b by omega]
      exact h1
    have h2 : Commute ((y ^ i)⁻¹ * h * (y ^ i)⁻¹⁻¹) z := hcen' _ h1'
    have h3 := (hci.mul_left h2).mul_left hci.inv_left
    rw [show y ^ i * ((y ^ i)⁻¹ * h * (y ^ i)⁻¹⁻¹) * (y ^ i)⁻¹ = h by group] at h3
    exact h3.eq

theorem fan54_right_c (F : FanTree Γ G) (h36 : Fan36 F) (h40 : Fan40 F) (ℓ : Line Γ) {z : G}
    {a b : ℤ} (hcore : ℓ.IsCoreC z a b) :
    ∀ x ∈ MulAction.stabilizer G (ℓ.vert (b + 1)), x ∉ MulAction.stabilizer G (ℓ.vert b) →
      x * z ≠ z * x := by
  intro x hx hxm hxz
  obtain ⟨hab, hfix, hcen, -, hmax⟩ := hcore
  have hxc : x • ℓ.vert (b + 1) = ℓ.vert (b + 1) := MulAction.mem_stabilizer_iff.1 hx
  have hxm' : x • ℓ.vert (b + 1 - 1) ≠ ℓ.vert (b + 1 - 1) := by
    rw [show b + 1 - 1 = b by omega]
    exact fun h => hxm (MulAction.mem_stabilizer_iff.2 h)
  have hzb : z • ℓ.vert b = ℓ.vert b := hfix b hab.le le_rfl
  have hzb1 : z • ℓ.vert (b - 1) = ℓ.vert (b - 1) := hfix (b - 1) (by omega) (by omega)
  have hcen' : ∀ s ∈ ℓ.edgeCirc (G := G) (b - 1), s * z = z * s :=
    (hcen (b - 1) (by omega) (by omega)).2
  set L := ℓ.glue (b + 1) x F hxc hxm' with hL
  have hs := not_lineSingLe_of_fan40 h40 L (n := 4 - 1) (by norm_num)
  have hH : Subgroup.closure (L.edgeCirc (G := G) (b - 1) ∪
      L.edgeCirc (b - 1 + ((4 - 1 : ℕ) : ℤ))) ≤ Subgroup.centralizer ({z} : Set G) := by
    refine closure_le_centralizer ?_
    rintro s (hs | hs)
    · rw [hL, ℓ.glue_edgeCirc_le (b + 1) x F hxc hxm' (i := b - 1) (by omega)] at hs
      exact hcen' s hs
    · rw [show b - 1 + ((4 - 1 : ℕ) : ℤ) = b + 2 by norm_num; omega] at hs
      exact ℓ.glue_edgeCirc_cen (b + 1) x F hxc hxm' hxz (i := b + 2) (j := b - 1) (by omega)
        (by omega) hcen' s hs
  obtain ⟨y1, hy1, hy1o⟩ := fan51a F h36 h40 L (b - 1) 4 (by norm_num) hs 1 le_rfl (by norm_num)
  obtain ⟨y2, hy2, hy2o⟩ :=
    fan51a F h36 h40 L (b - 1) 4 (by norm_num) hs 2 (by norm_num) (by norm_num)
  have hL1 : L.vert (b - 1 + ((1 : ℕ) : ℤ)) = ℓ.vert b := by
    rw [hL, show b - 1 + ((1 : ℕ) : ℤ) = b by push_cast; ring]
    exact ℓ.glue_vert_le (b + 1) x F hxc hxm' (by omega)
  have hL2 : L.vert (b - 1 + ((2 : ℕ) : ℤ)) = ℓ.vert (b + 1) := by
    rw [hL, show b - 1 + ((2 : ℕ) : ℤ) = b + 1 by push_cast; ring]
    exact ℓ.glue_vert_le (b + 1) x F hxc hxm' le_rfl
  rw [hL1] at hy1 hy1o
  rw [hL2] at hy2 hy2o
  have l1 := F.locTr_of_pow (hH hy1.1) hy1.2 hy1o
  have l2 := F.locTr_of_pow (hH hy2.1) hy2.2 hy2o
  have hadj : Γ.Adj (ℓ.vert b) (ℓ.vert (b - 1)) := by
    have := (ℓ.adj (b - 1)).symm
    rwa [show b - 1 + 1 = b by omega] at this
  have hzb2 : z • ℓ.vert (b + 1) = ℓ.vert (b + 1) := by
    obtain ⟨c, hcC, -, hc⟩ := l1 (ℓ.vert (b - 1)) (ℓ.vert (b + 1)) hadj (ℓ.adj b)
    have hcz : c * z = z * c := (Subgroup.mem_centralizer_iff.1 hcC z rfl).symm
    rw [← hc, ← mul_smul, ← hcz, mul_smul, hzb1]
  have hz1 : z = 1 := F.eq_one_of_locTr_centralizer (ℓ.adj b) hzb hzb2 l1 l2
  refine hmax ⟨hzb, ?_⟩
  rw [hz1]
  exact ℓ.one_mem_cen_edgeCirc b

theorem fan54 (F : FanTree Γ G) (h36 : Fan36 F) : Fan54 F := by
  intro h40 ℓ z a b hz hcore δ α hδα x hx hxα
  have hzz : z * z = 1 := hz.1
  have hrev := hcore.rev F
  rcases hδα with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1] at hx
    rw [h2] at hxα
    exact fan54_right_b F h36 h40 ℓ hzz hcore x hx hxα
  · rw [h1] at hx
    rw [h2] at hxα
    exact fan54_right_c F h36 h40 ℓ hcore x hx hxα
  · have e0 : ℓ.rev.vert (-a) = ℓ.vert a := by simp
    have e1 : ℓ.rev.vert (-a - 1) = ℓ.vert (a + 1) := by
      simp only [Line.rev_vert]
      congr 1
      omega
    rw [h1] at hx
    rw [h2] at hxα
    exact fan54_right_b F h36 h40 ℓ.rev hzz hrev x (by rw [e0]; exact hx)
      (by rw [e1]; exact hxα)
  · have e0 : ℓ.rev.vert (-a + 1) = ℓ.vert (a - 1) := by
      simp only [Line.rev_vert]
      congr 1
      omega
    have e1 : ℓ.rev.vert (-a) = ℓ.vert a := by simp
    rw [h1] at hx
    rw [h2] at hxα
    exact fan54_right_c F h36 h40 ℓ.rev hrev x (by rw [e0]; exact hx) (by rw [e1]; exact hxα)

end CFSG.Quasithin.Fan86
