module

public import CFSG.Quasithin.EmptyFaithful.S153PA1a

public section

namespace CFSG.Quasithin

open scoped commutatorElement Pointwise

namespace S153P

namespace PA1

section Chars

variable {G : Type} [Group G] {U Z Mc : Subgroup G} {z y : G} (A : Abs56 U Z Mc z y)
include A

theorem mem_cent_V0_iff {g : G} :
    g ∈ Subgroup.centralizer (V0g Z y : Set G) ↔ z * g = g * z ∧ zp z y * g = g * zp z y := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨h z (z_mem_V0 A), h _ (zp_mem_V0 A)⟩
  · rintro ⟨h1, h2⟩ v hv
    rcases (mem_V0_iff A).mp hv with h | h | h | h
    · rw [h]; simp
    · rw [h]; exact h1
    · rw [h]; exact h2
    · rw [h]
      calc z * zp z y * g = z * (zp z y * g) := mul_assoc _ _ _
        _ = z * (g * zp z y) := by rw [h2]
        _ = z * g * zp z y := (mul_assoc _ _ _).symm
        _ = g * z * zp z y := by rw [h1]
        _ = g * (z * zp z y) := mul_assoc _ _ _

theorem mem_conj_Mc_iff {g : G} : g ∈ conjSubgroup Mc y ↔ zp z y * g = g * zp z y := by
  rw [mem_conjSubgroup_iff, mem_Mc_iff A]
  have h1 : z * (y * g * y⁻¹) = y * (zp z y * g) * y⁻¹ := by simp only [zp]; group
  have h2 : y * g * y⁻¹ * z = y * (g * zp z y) * y⁻¹ := by simp only [zp]; group
  rw [h1, h2, conj_cancel_iff]

theorem zp_comm_U' {x : G} (hx : x ∈ conjSubgroup U y) : zp z y * x = x * zp z y := by
  rw [mem_conjSubgroup_iff] at hx
  have h := A.Z_central _ hx
  have h1 : y * x * y⁻¹ * z = y * (x * zp z y) * y⁻¹ := by simp only [zp]; group
  have h2 : z * (y * x * y⁻¹) = y * (zp z y * x) * y⁻¹ := by simp only [zp]; group
  rw [h1, h2, conj_cancel_iff] at h
  exact h.symm

theorem z_mem_U' : z ∈ conjSubgroup U y := by
  rw [mem_conjSubgroup_iff, A.yz]
  exact mul_mem A.z_mem A.zp_mem

theorem zp_mem_U' : zp z y ∈ conjSubgroup U y := by
  rw [mem_conjSubgroup_iff, y_zp z y]
  exact A.z_mem

theorem U'_comm {a b : G} (ha : a ∈ conjSubgroup U y) (hb : b ∈ conjSubgroup U y) :
    ⁅a, b⁆ ∈ conjSubgroup Z y := by
  rw [mem_conjSubgroup_iff] at ha hb ⊢
  have h := A.U_comm _ ha _ hb
  have e : y * ⁅a, b⁆ * y⁻¹ = ⁅y * a * y⁻¹, y * b * y⁻¹⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]; exact h

theorem U'_sq {a : G} (ha : a ∈ conjSubgroup U y) : a * a ∈ conjSubgroup Z y := by
  rw [mem_conjSubgroup_iff] at ha ⊢
  have h := A.U_sq _ ha
  have e : y * (a * a) * y⁻¹ = (y * a * y⁻¹) * (y * a * y⁻¹) := by group
  rw [e]; exact h

theorem mem_Fg_iff {f : G} :
    f ∈ Fg U Mc y ↔ f ∈ U ∧ f ∈ Subgroup.centralizer (V0g Z y : Set G) := by
  rw [Subgroup.mem_inf, mem_conj_Mc_iff A, mem_cent_V0_iff A]
  constructor
  · rintro ⟨hu, h⟩
    exact ⟨hu, (A.Z_central f hu).symm, h⟩
  · rintro ⟨hu, -, h⟩
    exact ⟨hu, h⟩

theorem conj_zp_iff {x : G} (hx : zp z y * x = x * zp z y) :
    zp z y * (y * x * y⁻¹) = y * x * y⁻¹ * zp z y ↔ z * x = x * z := by
  have h1 : zp z y * (y * x * y⁻¹) = y * ((y⁻¹ * zp z y * y) * x) * y⁻¹ := by
    simp only [zp]; group
  have h2 : y * x * y⁻¹ * zp z y = y * (x * (y⁻¹ * zp z y * y)) * y⁻¹ := by
    simp only [zp]; group
  rw [yinv_zp A] at h1 h2
  rw [h1, h2, conj_cancel_iff]
  have e1 : z * zp z y * x = z * x * zp z y := by rw [mul_assoc, hx, ← mul_assoc]
  have e2 : x * (z * zp z y) = x * z * zp z y := (mul_assoc _ _ _).symm
  rw [e1, e2]
  exact mul_left_inj _

theorem mem_Xg_iff {x : G} :
    x ∈ Xg U Mc y ↔ x ∈ conjSubgroup U y ∧ x ∈ Subgroup.centralizer (V0g Z y : Set G) := by
  constructor
  · intro hx
    have hx' : y * x * y⁻¹ ∈ Fg U Mc y := mem_conjSubgroup_iff.mp hx
    obtain ⟨hxU, hxC⟩ := (mem_Fg_iff A).mp hx'
    have hxU' : x ∈ conjSubgroup U y := mem_conjSubgroup_iff.mpr hxU
    refine ⟨hxU', (mem_cent_V0_iff A).mpr ⟨?_, zp_comm_U' A hxU'⟩⟩
    exact (conj_zp_iff A (zp_comm_U' A hxU')).mp ((mem_cent_V0_iff A).mp hxC).2
  · rintro ⟨hxU', hxC⟩
    have hxU : y * x * y⁻¹ ∈ U := mem_conjSubgroup_iff.mp hxU'
    refine mem_conjSubgroup_iff.mpr ((mem_Fg_iff A).mpr ⟨hxU, (mem_cent_V0_iff A).mpr
      ⟨(A.Z_central _ hxU).symm, ?_⟩⟩)
    exact (conj_zp_iff A (zp_comm_U' A hxU')).mpr ((mem_cent_V0_iff A).mp hxC).1

theorem mem_Eg_iff {e : G} : e ∈ Eg U Mc y ↔ e ∈ U ∧ e ∈ conjSubgroup U y := by
  rw [Subgroup.mem_inf, mem_Fg_iff A, mem_Xg_iff A]
  constructor
  · rintro ⟨⟨h1, -⟩, h2, -⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have hC : e ∈ Subgroup.centralizer (V0g Z y : Set G) :=
      (mem_cent_V0_iff A).mpr ⟨(A.Z_central e h1).symm, zp_comm_U' A h2⟩
    exact ⟨⟨h1, hC⟩, h2, hC⟩

theorem z_mem_Eg : z ∈ Eg U Mc y := (mem_Eg_iff A).mpr ⟨A.z_mem, z_mem_U' A⟩

theorem zp_mem_Eg : zp z y ∈ Eg U Mc y := (mem_Eg_iff A).mpr ⟨A.zp_mem, zp_mem_U' A⟩

theorem Z_le_Eg : Z ≤ Eg U Mc y := by
  intro x hx
  rcases (mem_Z_iff A).mp hx with h | h
  · rw [h]; exact one_mem _
  · rw [h]; exact z_mem_Eg A

theorem conjZ_le_Eg : conjSubgroup Z y ≤ Eg U Mc y := by
  intro x hx
  rcases (mem_conjZ_iff A).mp hx with h | h
  · rw [h]; exact one_mem _
  · rw [h]; exact zp_mem_Eg A

theorem V0_le_Eg : V0g Z y ≤ Eg U Mc y := sup_le (Z_le_Eg A) (conjZ_le_Eg A)

theorem cent_mem_Mc {g : G} (hg : g ∈ Subgroup.centralizer (V0g Z y : Set G)) : g ∈ Mc :=
  (mem_Mc_iff A).mpr ((mem_cent_V0_iff A).mp hg).1

theorem cent_mem_conjMc {g : G} (hg : g ∈ Subgroup.centralizer (V0g Z y : Set G)) :
    g ∈ conjSubgroup Mc y :=
  (mem_conj_Mc_iff A).mpr ((mem_cent_V0_iff A).mp hg).2

theorem conjMc_conj_U' {g x : G} (hg : g ∈ conjSubgroup Mc y) (hx : x ∈ conjSubgroup U y) :
    g * x * g⁻¹ ∈ conjSubgroup U y := by
  rw [mem_conjSubgroup_iff] at hg hx ⊢
  have h := A.U_norm _ hg _ hx
  have e : y * (g * x * g⁻¹) * y⁻¹ = y * g * y⁻¹ * (y * x * y⁻¹) * (y * g * y⁻¹)⁻¹ := by group
  rw [e]; exact h

end Chars

section Commutators

variable {G : Type} [Group G] {U Z Mc : Subgroup G} {z y : G} (A : Abs56 U Z Mc z y)
include A

theorem U_conj_Fg {u f : G} (hu : u ∈ U) (hf : f ∈ Fg U Mc y) : u * f * u⁻¹ ∈ Fg U Mc y := by
  rw [mem_Fg_iff A] at hf ⊢
  obtain ⟨hfU, hfC⟩ := hf
  exact ⟨mul_mem (mul_mem hu hfU) (inv_mem hu), conj_mem_centralizer (U_le_normV0 A hu) hfC⟩

theorem U'_conj_Xg {u x : G} (hu : u ∈ conjSubgroup U y) (hx : x ∈ Xg U Mc y) :
    u * x * u⁻¹ ∈ Xg U Mc y := by
  rw [mem_Xg_iff A] at hx ⊢
  obtain ⟨hxU, hxC⟩ := hx
  exact ⟨mul_mem (mul_mem hu hxU) (inv_mem hu), conj_mem_centralizer (U'_le_normV0 A hu) hxC⟩

theorem K1 {u x : G} (hu : u ∈ U) (hx : x ∈ Xg U Mc y) : ⁅u, x⁆ ∈ Fg U Mc y := by
  rw [mem_Xg_iff A] at hx
  obtain ⟨-, hxC⟩ := hx
  rw [mem_Fg_iff A]
  refine ⟨?_, comm_mem_centralizer (U_le_normV0 A hu) hxC⟩
  have h1 : x * u⁻¹ * x⁻¹ ∈ U := A.U_norm x (cent_mem_Mc A hxC) u⁻¹ (inv_mem hu)
  have e : ⁅u, x⁆ = u * (x * u⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]; exact mul_mem hu h1

theorem K2 {u f : G} (hu : u ∈ conjSubgroup U y) (hf : f ∈ Fg U Mc y) : ⁅u, f⁆ ∈ Xg U Mc y := by
  rw [mem_Fg_iff A] at hf
  obtain ⟨-, hfC⟩ := hf
  rw [mem_Xg_iff A]
  refine ⟨?_, comm_mem_centralizer (U'_le_normV0 A hu) hfC⟩
  have h1 : f * u⁻¹ * f⁻¹ ∈ conjSubgroup U y :=
    conjMc_conj_U' A (cent_mem_conjMc A hfC) (inv_mem hu)
  have e : ⁅u, f⁆ = u * (f * u⁻¹ * f⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]; exact mul_mem hu h1

theorem K3 {f x : G} (hf : f ∈ Fg U Mc y) (hx : x ∈ Xg U Mc y) : ⁅f, x⁆ ∈ Eg U Mc y := by
  rw [mem_Fg_iff A] at hf
  rw [mem_Xg_iff A] at hx
  obtain ⟨hfU, hfC⟩ := hf
  obtain ⟨hxU', hxC⟩ := hx
  rw [mem_Eg_iff A]
  constructor
  · have h1 : x * f⁻¹ * x⁻¹ ∈ U := A.U_norm x (cent_mem_Mc A hxC) f⁻¹ (inv_mem hfU)
    have e : ⁅f, x⁆ = f * (x * f⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]; exact mul_mem hfU h1
  · have h1 : f * x * f⁻¹ ∈ conjSubgroup U y :=
      conjMc_conj_U' A (cent_mem_conjMc A hfC) hxU'
    exact mul_mem h1 (inv_mem hxU')

theorem Fg_le_normXg : Fg U Mc y ≤ Subgroup.normalizer (Xg U Mc y : Set G) := by
  apply le_normalizer_of_conj
  intro f hf x hx
  rw [mem_Fg_iff A] at hf
  rw [mem_Xg_iff A] at hx ⊢
  obtain ⟨-, hfC⟩ := hf
  obtain ⟨hxU', hxC⟩ := hx
  exact ⟨conjMc_conj_U' A (cent_mem_conjMc A hfC) hxU', mul_mem (mul_mem hfC hxC) (inv_mem hfC)⟩

theorem mem_Ng_iff {r : G} : r ∈ Ng U Mc y ↔ ∃ f ∈ Fg U Mc y, ∃ x ∈ Xg U Mc y, r = f * x := by
  have h := Subgroup.coe_mul_of_left_le_normalizer_right (Fg U Mc y) (Xg U Mc y)
    (Fg_le_normXg A)
  have h1 : r ∈ Ng U Mc y ↔ r ∈ (Fg U Mc y : Set G) * (Xg U Mc y : Set G) := by
    rw [← h]; rfl
  rw [h1, Set.mem_mul]
  constructor
  · rintro ⟨f, hf, x, hx, rfl⟩
    exact ⟨f, hf, x, hx, rfl⟩
  · rintro ⟨f, hf, x, hx, rfl⟩
    exact ⟨f, hf, x, hx, rfl⟩

theorem U_le_normN : U ≤ Subgroup.normalizer (Ng U Mc y : Set G) := by
  apply le_normalizer_of_conj
  intro u hu n hn
  obtain ⟨f, hf, x, hx, rfl⟩ := (mem_Ng_iff A).mp hn
  have h1 : u * f * u⁻¹ ∈ Fg U Mc y := U_conj_Fg A hu hf
  have h2 : ⁅u, x⁆ ∈ Fg U Mc y := K1 A hu hx
  have e : u * (f * x) * u⁻¹ = (u * f * u⁻¹) * (⁅u, x⁆ * x) := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left h1) (mul_mem (Subgroup.mem_sup_left h2)
    (Subgroup.mem_sup_right hx))

theorem U'_le_normN : conjSubgroup U y ≤ Subgroup.normalizer (Ng U Mc y : Set G) := by
  apply le_normalizer_of_conj
  intro u hu n hn
  obtain ⟨f, hf, x, hx, rfl⟩ := (mem_Ng_iff A).mp hn
  have h1 : ⁅u, f⁆ ∈ Xg U Mc y := K2 A hu hf
  have h2 : u * x * u⁻¹ ∈ Xg U Mc y := U'_conj_Xg A hu hx
  have e : u * (f * x) * u⁻¹ = (⁅u, f⁆ * f) * (u * x * u⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact mul_mem (mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hf))
    (Subgroup.mem_sup_right h2)

end Commutators

end PA1

namespace Abs56

variable {G : Type} [Group G] {U Z Mc : Subgroup G} {z y : G} (A : Abs56 U Z Mc z y)
include A

theorem N_prod : ∀ r ∈ Ng U Mc y, ∃ f ∈ Fg U Mc y, ∃ x ∈ Xg U Mc y, r = f * x :=
  fun _ hr => (PA1.mem_Ng_iff A).mp hr

theorem N_normal : ∀ j ∈ Jg U y, ∀ n ∈ Ng U Mc y, j * n * j⁻¹ ∈ Ng U Mc y := by
  intro j hj n hn
  have hJ : Jg U y ≤ Subgroup.normalizer (Ng U Mc y : Set G) :=
    sup_le (PA1.U_le_normN A) (PA1.U'_le_normN A)
  exact (Subgroup.mem_normalizer_iff.mp (hJ hj) n).mp hn

theorem N_le_J : Ng U Mc y ≤ Jg U y := by
  have hF : Fg U Mc y ≤ U := fun f hf => ((PA1.mem_Fg_iff A).mp hf).1
  have hX : Xg U Mc y ≤ conjSubgroup U y := fun x hx => ((PA1.mem_Xg_iff A).mp hx).1
  exact sup_le_sup hF hX

theorem N_le_cent : Ng U Mc y ≤ Subgroup.centralizer ((V0g Z y : Subgroup G) : Set G) := by
  apply sup_le
  · exact fun f hf => ((PA1.mem_Fg_iff A).mp hf).2
  · exact fun x hx => ((PA1.mem_Xg_iff A).mp hx).2

theorem N_sq : ∀ a ∈ Ng U Mc y, a * a ∈ Eg U Mc y := by
  intro a ha
  obtain ⟨f, hf, x, hx, rfl⟩ := N_prod A a ha
  have hfU : f ∈ U := ((PA1.mem_Fg_iff A).mp hf).1
  have hxU' : x ∈ conjSubgroup U y := ((PA1.mem_Xg_iff A).mp hx).1
  have h1 : f * f ∈ Eg U Mc y := PA1.Z_le_Eg A (A.U_sq f hfU)
  have h2 : ⁅f⁻¹, x⁆ ∈ Eg U Mc y := PA1.K3 A (inv_mem hf) hx
  have h3 : x * x ∈ Eg U Mc y := PA1.conjZ_le_Eg A (PA1.U'_sq A hxU')
  have e : f * x * (f * x) = f * f * ⁅f⁻¹, x⁆ * (x * x) := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact mul_mem (mul_mem h1 h2) h3

theorem N_isPGroup : IsPGroup 2 ↥(Ng U Mc y) := by
  intro a
  refine ⟨3, ?_⟩
  have h1 : (a : G) * a ∈ Eg U Mc y := N_sq A _ a.2
  have h2 : (a : G) * a * ((a : G) * a) ∈ Z := A.U_sq _ ((PA1.mem_Eg_iff A).mp h1).1
  have h3 : (a : G) * a * ((a : G) * a) * ((a : G) * a * ((a : G) * a)) = 1 := by
    rcases (PA1.mem_Z_iff A).mp h2 with h | h
    · rw [h]; simp
    · rw [h]; exact A.z_sq
  have key : ∀ g : G, g ^ 8 = g * g * (g * g) * (g * g * (g * g)) := fun g => by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  apply Subtype.ext
  show (a : G) ^ 8 = 1
  rw [key]
  exact h3

end Abs56

end S153P

end CFSG.Quasithin
