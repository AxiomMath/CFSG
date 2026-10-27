module

public import CFSG.Quasithin.H13.GoldschmidtU43DOrb
public import CFSG.Quasithin.H13.GoldschmidtU43DUz

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

open Classical in
@[expose] noncomputable def jco (z y : G) : ZMod 2 := if y ∈ Uz z then 0 else 1

namespace Swap

variable [Finite G] {z t w a : G} (s : Swap z t w) (ha : Good z t a)
include s ha

omit [Finite G] in
theorem m_not_mem_U : w⁻¹ * a * w ∉ Uz z := by
  intro hU
  apply s.m_notV ha
  exact (s.mem_N1_inf_N2 _).1 ⟨⟨hU, (s.m_mem_B ha).2⟩, m_mem_N2 ha⟩

theorem E_mem_U_or {y : G} (hy : y ∈ Eg z t w a) : y ∈ Uz z ∨ y * (w⁻¹ * a * w) ∈ Uz z := by
  obtain ⟨v, hv, i, j, rfl⟩ := (s.mem_Eg_iff ha y).1 hy
  have hvU : v ∈ Uz z := s.Vg_le_U hv
  have hai : zp a i ∈ Uz z := by
    rcases zmod_two_cases i with rfl | rfl
    · rw [zp_zero]; exact one_mem _
    · rw [zp_one]; exact ha.mem.1
  have hm2 : (w⁻¹ * a * w) * (w⁻¹ * a * w) = 1 := m_sq ha
  rcases zmod_two_cases j with rfl | rfl
  · left
    rw [zp_zero, mul_one]
    exact mul_mem hvU hai
  · right
    rw [zp_one]
    have e : v * zp a i * (w⁻¹ * a * w) * (w⁻¹ * a * w) = v * zp a i := by
      rw [mul_assoc, hm2, mul_one]
    rw [e]
    exact mul_mem hvU hai

theorem jco_mul {y y' : G} (hy : y ∈ Eg z t w a) (hy' : y' ∈ Eg z t w a) :
    jco z (y * y') = jco z y + jco z y' := by
  classical
  have hm : w⁻¹ * a * w ∈ Eg z t w a := m_mem_Eg
  have hcomm : ∀ u u' : G, u ∈ Eg z t w a → u' ∈ Eg z t w a → u * u' = u' * u :=
    fun u u' hu hu' => (s.Eg_comm_sq ha hu hu').1
  have hm2 : (w⁻¹ * a * w) * (w⁻¹ * a * w) = 1 := m_sq ha
  have hU : ∀ u : G, u ∈ Uz z → jco z u = 0 := fun u hu => by simp [jco, hu]
  have hnU : ∀ u : G, u ∉ Uz z → jco z u = 1 := fun u hu => by simp [jco, hu]
  by_cases h1 : y ∈ Uz z <;> by_cases h2 : y' ∈ Uz z
  · rw [hU _ (mul_mem h1 h2), hU _ h1, hU _ h2]
    decide
  · have h3 : y * y' ∉ Uz z := fun h3 => h2 (by
      have : y' = y⁻¹ * (y * y') := by group
      rw [this]
      exact mul_mem ((Uz z).inv_mem h1) h3)
    rw [hnU _ h3, hU _ h1, hnU _ h2]
    decide
  · have h3 : y * y' ∉ Uz z := fun h3 => h1 (by
      have : y = (y * y') * y'⁻¹ := by group
      rw [this]
      exact mul_mem h3 ((Uz z).inv_mem h2))
    rw [hnU _ h3, hnU _ h1, hU _ h2]
    decide
  · have h3 : y * y' ∈ Uz z := by
      have hA : y * (w⁻¹ * a * w) ∈ Uz z := (s.E_mem_U_or ha hy).resolve_left h1
      have hB : y' * (w⁻¹ * a * w) ∈ Uz z := (s.E_mem_U_or ha hy').resolve_left h2
      have hB' : (w⁻¹ * a * w) * y' ∈ Uz z := by
        rw [hcomm _ _ hm hy']
        exact hB
      have e : y * y' = (y * (w⁻¹ * a * w)) * ((w⁻¹ * a * w) * y') := by
        calc y * y' = y * ((w⁻¹ * a * w) * (w⁻¹ * a * w)) * y' := by rw [hm2, mul_one]
          _ = (y * (w⁻¹ * a * w)) * ((w⁻¹ * a * w) * y') := by simp only [mul_assoc]
      rw [e]
      exact mul_mem hA hB'
    rw [hU _ h3, hnU _ h1, hnU _ h2]
    decide

end Swap

open Classical in
@[expose] noncomputable def Fv (z t w a : G) (c d : V4) : ZMod 2 :=
  if c = 0 then 0 else
    if crd (Swap.gE z t w a) d ∈ Uz (crd (Swap.gE z t w a) c) then 0 else 1

namespace Swap

variable [Finite G] {z t w a : G} (s : Swap z t w) (ha : Good z t a)
include s ha

theorem psi_ne_one {c : V4} (hc : c ≠ 0) : crd (gE z t w a) c ≠ 1 :=
  fun h => hc (s.crd_gE_indep ha h)

theorem psi_add (c d : V4) :
    crd (gE z t w a) (c + d) = crd (gE z t w a) c * crd (gE z t w a) d :=
  (s.comm4_gE ha).crd_add c d

theorem exists_k {c : V4} (hc : c ≠ 0) :
    ∃ k ∈ Subgroup.normalizer (Eg z t w a : Set G), k * z * k⁻¹ = crd (gE z t w a) c :=
  s.exists_conj_to_z ha (crd_gE_mem c) (s.psi_ne_one ha hc)

omit [Finite G] s ha in
theorem conj_inv_mem_E {k y : G} (hk : k ∈ Subgroup.normalizer (Eg z t w a : Set G))
    (hy : y ∈ Eg z t w a) : k⁻¹ * y * k ∈ Eg z t w a :=
  (Subgroup.mem_normalizer_iff''.mp hk y).mp hy

omit [Finite G] s ha in
theorem Fv_eq_jco {c : V4} (hc : c ≠ 0) {k : G} (hkc : k * z * k⁻¹ = crd (gE z t w a) c)
    (d : V4) : Fv z t w a c d = jco z (k⁻¹ * crd (gE z t w a) d * k) := by
  classical
  unfold Fv jco
  simp only [hc, ↓reduceIte]
  rw [← hkc, mem_Uz_conj]

theorem Fv_add_right (c d d' : V4) : Fv z t w a c (d + d') = Fv z t w a c d + Fv z t w a c d' := by
  by_cases hc : c = 0
  · subst hc
    simp [Fv]
  · obtain ⟨k, hk, hkc⟩ := s.exists_k ha hc
    rw [Fv_eq_jco hc hkc, Fv_eq_jco hc hkc, Fv_eq_jco hc hkc, s.psi_add ha]
    have e : k⁻¹ * (crd (gE z t w a) d * crd (gE z t w a) d') * k =
        (k⁻¹ * crd (gE z t w a) d * k) * (k⁻¹ * crd (gE z t w a) d' * k) := by group
    rw [e]
    exact s.jco_mul ha (conj_inv_mem_E hk (crd_gE_mem d))
      (conj_inv_mem_E hk (crd_gE_mem d'))

theorem Fv_self (c : V4) : Fv z t w a c c = 0 := by
  by_cases hc : c = 0
  · subst hc
    simp [Fv]
  · obtain ⟨k, hk, hkc⟩ := s.exists_k ha hc
    rw [Fv_eq_jco hc hkc, ← hkc]
    have e : k⁻¹ * (k * z * k⁻¹) * k = z := by group
    rw [e]
    simp [jco, s.hyp.z_mem]

theorem mem_Uz_symm {c d : V4} (hc : c ≠ 0) (hd : d ≠ 0)
    (h : crd (gE z t w a) d ∈ Uz (crd (gE z t w a) c)) :
    crd (gE z t w a) c ∈ Uz (crd (gE z t w a) d) := by
  obtain ⟨k, hk, hkc⟩ := s.exists_k ha hc
  have h1 : k⁻¹ * crd (gE z t w a) d * k ∈ Uz z := by
    rw [← hkc] at h
    exact mem_Uz_conj.mp h
  have hy'E : k⁻¹ * crd (gE z t w a) d * k ∈ Eg z t w a := conj_inv_mem_E hk (crd_gE_mem d)
  have hpd : crd (gE z t w a) d = k * (k⁻¹ * crd (gE z t w a) d * k) * k⁻¹ := by group
  have hkc' : k⁻¹ * crd (gE z t w a) c * k = z := by rw [← hkc]; group
  generalize k⁻¹ * crd (gE z t w a) d * k = y' at h1 hy'E hpd
  by_cases hy1 : y' = 1
  · exfalso
    apply s.psi_ne_one ha hd
    rw [hpd, hy1]
    group
  by_cases hyz : y' = z
  · have hdc : crd (gE z t w a) d = crd (gE z t w a) c := by rw [hpd, hyz, hkc]
    rw [hdc, ← hkc, mem_Uz_conj]
    have e : k⁻¹ * (k * z * k⁻¹) * k = z := by group
    rw [e]
    exact s.hyp.z_mem
  · have hyS : y' ∈ S z := ⟨h1, (s.Eg_comm_sq ha hy'E hy'E).2, hy1, hyz⟩
    have hz := s.hyp.z_mem_Uz_of_mem_S hyS
    rw [hpd, mem_Uz_conj, hkc']
    exact hz

theorem Fv_symm (c d : V4) : Fv z t w a c d = Fv z t w a d c := by
  classical
  by_cases hc : c = 0
  · subst hc
    simp [Fv, crd_zero]
  by_cases hd : d = 0
  · subst hd
    simp [Fv, crd_zero]
  unfold Fv
  simp only [hc, hd, ↓reduceIte]
  by_cases h1 : crd (gE z t w a) d ∈ Uz (crd (gE z t w a) c)
  · have h2 := s.mem_Uz_symm ha hc hd h1
    simp only [h1, h2, ↓reduceIte]
  · have h2 : ¬ crd (gE z t w a) c ∈ Uz (crd (gE z t w a) d) := fun h2 =>
      h1 (s.mem_Uz_symm ha hd hc h2)
    simp only [h1, h2, ↓reduceIte]

theorem Fv_nondeg {c : V4} (hc : c ≠ 0) : ∃ d, Fv z t w a c d = 1 := by
  obtain ⟨k, hk, hkc⟩ := s.exists_k ha hc
  have hm : k * (w⁻¹ * a * w) * k⁻¹ ∈ Eg z t w a :=
    (Subgroup.mem_normalizer_iff.mp hk _).mp m_mem_Eg
  obtain ⟨d, hd⟩ := s.exists_crd ha hm
  refine ⟨d, ?_⟩
  rw [Fv_eq_jco hc hkc, ← hd]
  have e : k⁻¹ * (k * (w⁻¹ * a * w) * k⁻¹) * k = w⁻¹ * a * w := by group
  rw [e]
  simp [jco, s.m_not_mem_U ha]

theorem Fv_conj_inv {k : G} (M : Fin 4 → V4)
    (hM : ∀ c, k * crd (gE z t w a) c * k⁻¹ = crd (gE z t w a) (app M c)) (c d : V4) :
    Fv z t w a (app M c) (app M d) = Fv z t w a c d := by
  classical
  have hMc : ∀ c, app M c = 0 ↔ c = 0 := by
    intro c
    constructor
    · intro h0
      apply s.crd_gE_indep ha
      have h1 := hM c
      rw [h0, crd_zero] at h1
      calc crd (gE z t w a) c = k⁻¹ * (k * crd (gE z t w a) c * k⁻¹) * k := by group
        _ = 1 := by rw [h1]; group
    · rintro rfl
      exact app_zero M
  by_cases hc : c = 0
  · subst hc
    rw [app_zero]
    simp [Fv]
  · have hc' : app M c ≠ 0 := fun h => hc ((hMc c).1 h)
    unfold Fv
    simp only [hc, hc', ↓reduceIte]
    rw [← hM c, ← hM d, mem_Uz_conj]
    have e : k⁻¹ * (k * crd (gE z t w a) d * k⁻¹) * k = crd (gE z t w a) d := by group
    rw [e]

end Swap

end CFSG.Quasithin.H13.U43
