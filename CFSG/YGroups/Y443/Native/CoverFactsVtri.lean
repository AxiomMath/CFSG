module

public import CFSG.YGroups.Y443.Native.CoverFactsCx
public import CFSG.YGroups.Y443.Tri.CosetCover

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.GMS CFSG.Open
open CFSG.Monster.Tri (baseVertex coe_baseVertex longTri coxeter_conj coxeter_sq)

section Coxeter

variable {G : Type*} [Group G]

theorem vtri_braid {a b : G} (ha : a * a = 1) (hb : b * b = 1) (h : (a * b) ^ 3 = 1) :
    a * b * a = b * a * b := by
  have h' : a * (b * (a * (b * (a * b)))) = 1 := by
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using h
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h3 : a * b * a = (b * a * b)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by simpa only [mul_assoc] using h')
  rw [h3]
  simp only [mul_inv_rev, hai, hbi, mul_assoc]

theorem vtri_cube_swap {a b : G} (ha : a * a = 1) (hb : b * b = 1) (h : (a * b) ^ 3 = 1) :
    (b * a) ^ 3 = 1 := by
  have hn : (a * b)⁻¹ = b * a := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]
  rw [← hn, inv_pow, h, inv_one]

theorem vtri_comm_of_sq {a b : G} (ha : a * a = 1) (hb : b * b = 1) (h : (a * b) ^ 2 = 1) :
    a * b = b * a := by
  have hn : (a * b)⁻¹ = b * a := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]
  have h2 : a * b = (a * b)⁻¹ := by
    have : a * b * (a * b) = 1 := by rw [← pow_two]; exact h
    exact eq_inv_of_mul_eq_one_left this
  rw [h2, hn]

theorem vtri_algebra {c x y b a : G} (hc : c * c = 1) (hy : y * y = 1) (hb : b * b = 1)
    (ha : a * a = 1) (hyb : (y * b) ^ 3 = 1) (hba : (b * a) ^ 3 = 1)
    (kcy : c * y = y * c) (kcb : c * b = b * c) (kca : c * a = a * c)
    (kxa : x * a = a * x) (kya : y * a = a * y) (hc1 : c ≠ 1) :
    (b * (y * a) * b) * c = c * (b * (y * a) * b) ∧
      (b * (y * a) * b) * y * (b * (y * a) * b)⁻¹ = a ∧
      (x * c * y * x) * a = a * (x * c * y * x) ∧ a ≠ c * y := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : Commute c b := kcb
    have h2 : Commute c y := kcy
    have h3 : Commute c a := kca
    exact ((h1.mul_right (h2.mul_right h3)).mul_right h1).eq.symm
  · have hu : b * (y * a) * b * (b * (y * a) * b) = 1 := by
      have := coxeter_sq hb hy ha kya
      simpa only [mul_assoc] using this
    have hui : (b * (y * a) * b)⁻¹ = b * (y * a) * b := inv_eq_of_mul_eq_one_right hu
    rw [hui]
    have := coxeter_conj hb hy ha kya hyb hba
    simpa only [mul_assoc] using this
  · have h1 : Commute a x := kxa.symm
    have h2 : Commute a c := kca.symm
    have h3 : Commute a y := kya.symm
    exact (((h1.mul_right h2).mul_right h3).mul_right h1).eq.symm
  · intro h
    have hbr1 : b * a * b = a * b * a := vtri_braid hb ha hba
    have hbr2 : y * b * y = b * y * b := vtri_braid hy hb hyb
    subst h
    have hlhs : b * (c * y) * b = c * (b * y * b) := by
      calc b * (c * y) * b = (b * c) * y * b := by simp only [mul_assoc]
        _ = (c * b) * y * b := by rw [← kcb]
        _ = c * (b * y * b) := by simp only [mul_assoc]
    have hrhs : c * y * b * (c * y) = y * b * y := by
      calc c * y * b * (c * y) = c * y * (b * c) * y := by simp only [mul_assoc]
        _ = c * y * (c * b) * y := by rw [← kcb]
        _ = c * (y * c) * b * y := by simp only [mul_assoc]
        _ = c * (c * y) * b * y := by rw [← kcy]
        _ = (c * c) * y * b * y := by simp only [mul_assoc]
        _ = y * b * y := by rw [hc, one_mul]
    rw [hlhs, hrhs, hbr2] at hbr1
    exact hc1 (mul_right_cancel (hbr1.trans (one_mul _).symm))

end Coxeter

theorem y443Y_eq_Tl : y443Y = y443Tl 3 := by
  have h := y443GenOfLetter_letterOfGen y443D1
  rw [y443LetterOfGen_D1] at h
  rw [y443Y, y443Tl, h]

theorem y443X_eq_Tl : y443X = y443Tl 4 := by
  have h := y443GenOfLetter_letterOfGen y443E1
  rw [y443LetterOfGen_E1] at h
  rw [y443X, y443Tl, h]

theorem fM_tl_mul_self
    (k : ℕ) : fM (y443Tl k) * fM (y443Tl k) = 1 := by
  rw [← map_mul, y443Tl_mul_self, map_one]

theorem fM_tl_cube
    {s t : ℕ} (hst : s < t) (ht : t < 12) (h : pairExp 4 4 3 s t = 3) :
    (fM (y443Tl s) * fM (y443Tl t)) ^ 3 = 1 := by
  have := y443Tl_pair_pow hst ht
  rw [h] at this
  rw [← map_mul, ← map_pow, this, map_one]

theorem fM_tl_comm
    {s t : ℕ} (hst : s < t) (ht : t < 12) (h : pairExp 4 4 3 s t = 2) :
    fM (y443Tl s) * fM (y443Tl t) = fM (y443Tl t) * fM (y443Tl s) := by
  have h1 := y443Tl_pair_pow hst ht
  rw [h] at h1
  exact vtri_comm_of_sq (fM_tl_mul_self s) (fM_tl_mul_self t)
    (by rw [← map_mul, ← map_pow, h1, map_one])

theorem fM_c_comm_tl
    {k : ℕ} (hk : k < 12) (hk4 : k ≠ 4) :
    fM y443C * fM (y443Tl k) = fM (y443Tl k) * fM y443C := by
  rw [← map_mul, ← map_mul, (y443C_comm_H (y443Tl_mem_H hk hk4))]

@[expose] noncomputable def y443H2 : MonsterY443Derived :=
  y443Tl 2 * (y443Y * y443Tl 1) * y443Tl 2

theorem y443H2_mem_H' : y443H2 ∈ y443H' :=
  mul_mem (mul_mem (y443Tl_mem_H' (by norm_num) (by norm_num))
    (mul_mem y443Y_mem_H' (y443Tl_mem_H' (by norm_num) (by norm_num))))
    (y443Tl_mem_H' (by norm_num) (by norm_num))

theorem fM_vtri_algebra :
    fM y443H2 * fM y443C = fM y443C * fM y443H2 ∧
      fM y443H2 * fM y443Y * (fM y443H2)⁻¹ = fM (y443Tl 1) ∧
      fM y443S * fM (y443Tl 1) = fM (y443Tl 1) * fM y443S ∧
      fM (y443Tl 1) ≠ fM y443C * fM y443Y := by
  have hY : fM y443Y = fM (y443Tl 3) := by rw [y443Y_eq_Tl]
  have hX : fM y443X = fM (y443Tl 4) := by rw [y443X_eq_Tl]
  have hYY : fM y443Y * fM y443Y = 1 := by rw [hY]; exact fM_tl_mul_self 3
  have hyb : (fM y443Y * fM (y443Tl 2)) ^ 3 = 1 := by
    rw [hY]
    exact vtri_cube_swap (fM_tl_mul_self 2) (fM_tl_mul_self 3)
      (fM_tl_cube (by norm_num) (by norm_num) (by decide))
  have hba : (fM (y443Tl 2) * fM (y443Tl 1)) ^ 3 = 1 :=
    vtri_cube_swap (fM_tl_mul_self 1) (fM_tl_mul_self 2)
      (fM_tl_cube (by norm_num) (by norm_num) (by decide))
  have kcy : fM y443C * fM y443Y = fM y443Y * fM y443C := by
    rw [← map_mul, ← map_mul, y443_Y_comm_C.symm]
  have kxa : fM y443X * fM (y443Tl 1) = fM (y443Tl 1) * fM y443X := by
    rw [hX]
    exact (fM_tl_comm (by norm_num) (by norm_num) (by decide)).symm
  have kya : fM y443Y * fM (y443Tl 1) = fM (y443Tl 1) * fM y443Y := by
    rw [hY]
    exact (fM_tl_comm (by norm_num) (by norm_num) (by decide)).symm
  have h := vtri_algebra (x := fM y443X) fM_c_mul_self hYY (fM_tl_mul_self 2) (fM_tl_mul_self 1)
    hyb hba kcy (fM_c_comm_tl (by norm_num) (by norm_num))
    (fM_c_comm_tl (by norm_num) (by norm_num)) kxa kya fM_c_ne_one
  simp only [y443H2, y443S, map_mul]
  exact h

theorem y443_Vtri
    (hcx : (fM y443C * fM y443X) ^ 3 = 1)
    (hcy : IsConj (fM y443C) (fM y443C * fM y443Y)) :
    ∃ β γ : ConjVert (fM y443C), longTri (fM y443C) (baseVertex (fM y443C)) β γ ∧
      (∃ h ∈ y443H', fM h • baseVertex (fM y443C) = baseVertex (fM y443C) ∧
        fM h • (fM y443S • baseVertex (fM y443C)) = β) ∧
      (∃ h ∈ y443H', fM h • baseVertex (fM y443C) = baseVertex (fM y443C) ∧
        fM h • (fM y443S • baseVertex (fM y443C)) = γ) ∧
      (∃ h ∈ y443H', fM h • baseVertex (fM y443C) = β ∧
        fM h • (fM y443S • baseVertex (fM y443C)) = γ) := by
  obtain ⟨hu_c, hu_y, hS_a, hne⟩ := fM_vtri_algebra
  have hone : ∀ v : ConjVert (fM y443C), fM (1 : MonsterY443Derived) • v = v := fun v => by
    rw [map_one, one_smul]
  have hadj := y443_adj hcx hcy
  have hβc : ((fM y443S • baseVertex (fM y443C) : ConjVert (fM y443C)) : Gmat) = fM y443Y :=
    coe_fM_S_smul hcx
  have hγc : ((fM y443H2 • (fM y443S • baseVertex (fM y443C)) : ConjVert (fM y443C)) : Gmat) =
      fM (y443Tl 1) := by
    rw [coe_smul_conjVert, hβc]
    exact hu_y
  have hu_base : fM y443H2 • baseVertex (fM y443C) = baseVertex (fM y443C) := by
    apply Subtype.ext
    rw [coe_smul_conjVert, coe_baseVertex]
    exact mul_inv_eq_iff_eq_mul.2 hu_c
  have hS_γ : fM y443S • (fM y443H2 • (fM y443S • baseVertex (fM y443C))) =
      fM y443H2 • (fM y443S • baseVertex (fM y443C)) := by
    apply Subtype.ext
    rw [coe_smul_conjVert, hγc]
    exact mul_inv_eq_iff_eq_mul.2 hS_a
  have hk₃b : fM (y443S * y443H2) • baseVertex (fM y443C) =
      fM y443S • baseVertex (fM y443C) := by
    rw [map_mul, mul_smul, hu_base]
  have hk₃β : fM (y443S * y443H2) • (fM y443S • baseVertex (fM y443C)) =
      fM y443H2 • (fM y443S • baseVertex (fM y443C)) := by
    rw [map_mul, mul_smul, hS_γ]
  refine ⟨fM y443S • baseVertex (fM y443C),
    fM y443H2 • (fM y443S • baseVertex (fM y443C)), ⟨hadj, ?_, ?_, ?_⟩,
    ⟨1, one_mem _, ?_, ?_⟩, ⟨y443H2, y443H2_mem_H', hu_base, rfl⟩,
    ⟨y443S * y443H2, mul_mem y443S_mem_H' y443H2_mem_H', hk₃b, hk₃β⟩⟩
  · have := twoAGraph_adj_smul (fM (y443S * y443H2)) hadj
    rwa [hk₃b, hk₃β] at this
  · have := twoAGraph_adj_smul (fM y443H2) hadj.symm
    rwa [hu_base] at this
  · rw [hγc, coe_baseVertex, hβc]
    exact hne
  · exact hone _
  · exact hone _

theorem y443_Vtri_native :
    ∃ β γ : ConjVert (fM y443C), longTri (fM y443C) (baseVertex (fM y443C)) β γ ∧
      (∃ h ∈ y443H', fM h • baseVertex (fM y443C) = baseVertex (fM y443C) ∧
        fM h • (fM y443S • baseVertex (fM y443C)) = β) ∧
      (∃ h ∈ y443H', fM h • baseVertex (fM y443C) = baseVertex (fM y443C) ∧
        fM h • (fM y443S • baseVertex (fM y443C)) = γ) ∧
      (∃ h ∈ y443H', fM h • baseVertex (fM y443C) = β ∧
        fM h • (fM y443S • baseVertex (fM y443C)) = γ) :=
  y443_Vtri fM_cx_cube fM_cy_conj

end CFSG.YGroups.Y443
