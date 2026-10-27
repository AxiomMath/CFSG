module

public import CFSG.Quasithin.EmptyFaithful.S153PBa

public section

namespace CFSG.Quasithin

namespace S153P

namespace PB

variable {G : Type} [Group G] {z zp u₀ u₀' : G}

def pt (z zp : G) : Fin 3 → G := ![z, zp, z * zp]

theorem pt_zero : pt z zp 0 = z := by simp [pt]

theorem pt_one : pt z zp 1 = zp := by simp [pt]

theorem pt_two : pt z zp 2 = z * zp := by simp [pt]

open Classical in
noncomputable def lab (z zp x : G) : Fin 3 := if x = z then 0 else if x = zp then 1 else 2

omit [Group G] in
theorem lab_z : lab z zp z = 0 := by
  simp [lab]

theorem lab_zp (hP : Pts z zp u₀ u₀') : lab z zp zp = 1 := by
  simp [lab, hP.z_ne_zp.symm]

theorem lab_zzp (hP : Pts z zp u₀ u₀') : lab z zp (z * zp) = 2 := by
  simp [lab, hP.zp_ne_one, hP.z_ne_one]

theorem lab_pt (hP : Pts z zp u₀ u₀') (i : Fin 3) : lab z zp (pt z zp i) = i := by
  fin_cases i
  · exact lab_z
  · exact lab_zp hP
  · exact lab_zzp hP

theorem pt_mem (i : Fin 3) : pt z zp i ∈ V0of z zp := by
  fin_cases i
  · exact mem_z
  · exact mem_zp
  · exact mem_zzp

theorem pt_ne_one (hP : Pts z zp u₀ u₀') (i : Fin 3) : pt z zp i ≠ 1 := by
  fin_cases i
  · exact hP.z_ne_one
  · exact hP.zp_ne_one
  · intro h
    exact hP.z_ne_zp ((eq_inv_of_mul_eq_one_left h).trans (zp_inv hP))

theorem pt_lab (hP : Pts z zp u₀ u₀') {x : G} (hx : x ∈ V0of z zp) (hx1 : x ≠ 1) :
    pt z zp (lab z zp x) = x := by
  rcases (mem_V0of hP).1 hx with h | h | h | h
  · exact absurd h hx1
  · rw [h, lab_z, pt_zero]
  · rw [h, lab_zp hP, pt_one]
  · rw [h, lab_zzp hP, pt_two]

abbrev NV (z zp : G) : Subgroup G := Subgroup.normalizer ((V0of z zp : Subgroup G) : Set G)

theorem conj_mem_V0 {g : G} (hg : g ∈ NV z zp) (i : Fin 3) : g * pt z zp i * g⁻¹ ∈ V0of z zp :=
  (Subgroup.mem_normalizer_iff.1 hg (pt z zp i)).1 (pt_mem i)

theorem conj_ne_one (hP : Pts z zp u₀ u₀') (g : G) (i : Fin 3) : g * pt z zp i * g⁻¹ ≠ 1 := by
  intro h
  exact pt_ne_one hP i (by simpa using h)

noncomputable def fwd (z zp g : G) (i : Fin 3) : Fin 3 := lab z zp (g * pt z zp i * g⁻¹)

theorem pt_fwd (hP : Pts z zp u₀ u₀') {g : G} (hg : g ∈ NV z zp) (i : Fin 3) :
    pt z zp (fwd z zp g i) = g * pt z zp i * g⁻¹ :=
  pt_lab hP (conj_mem_V0 hg i) (conj_ne_one hP g i)

theorem fwd_one (hP : Pts z zp u₀ u₀') (i : Fin 3) : fwd z zp 1 i = i := by
  unfold fwd
  rw [one_mul, inv_one, mul_one, lab_pt hP]

theorem fwd_mul (hP : Pts z zp u₀ u₀') {g h : G} (hh : h ∈ NV z zp) (i : Fin 3) :
    fwd z zp (g * h) i = fwd z zp g (fwd z zp h i) := by
  unfold fwd
  rw [pt_lab hP (conj_mem_V0 hh i) (conj_ne_one hP h i)]
  congr 1
  group

noncomputable def actEquiv (hP : Pts z zp u₀ u₀') (g : ↥(NV z zp)) : Equiv.Perm (Fin 3) where
  toFun := fwd z zp (g : G)
  invFun := fwd z zp (g : G)⁻¹
  left_inv i := by
    rw [← fwd_mul hP g.2, inv_mul_cancel, fwd_one hP]
  right_inv i := by
    rw [← fwd_mul hP (inv_mem g.2), mul_inv_cancel, fwd_one hP]

noncomputable def act (hP : Pts z zp u₀ u₀') : ↥(NV z zp) →* Equiv.Perm (Fin 3) :=
  MonoidHom.mk' (actEquiv hP) fun g h => by
    refine Equiv.ext fun i => ?_
    exact fwd_mul (g := (g : G)) hP h.2 i

theorem act_eq_one_iff (hP : Pts z zp u₀ u₀') (g : ↥(NV z zp)) :
    act hP g = 1 ↔ (g : G) ∈ Subgroup.centralizer ((V0of z zp : Subgroup G) : Set G) := by
  rw [mem_centralizer_V0 hP]
  constructor
  · intro h
    have key : ∀ i : Fin 3, (g : G) * pt z zp i * (g : G)⁻¹ = pt z zp i := by
      intro i
      have h1 : fwd z zp (g : G) i = i := by
        have h2 : act hP g i = (1 : Equiv.Perm (Fin 3)) i := by rw [h]
        exact h2
      rw [← pt_fwd hP g.2 i, h1]
    exact ⟨key 0, key 1⟩
  · rintro ⟨h1, h2⟩
    have key : ∀ i : Fin 3, (g : G) * pt z zp i * (g : G)⁻¹ = pt z zp i := by
      intro i
      fin_cases i
      · exact h1
      · exact h2
      · show (g : G) * (z * zp) * (g : G)⁻¹ = z * zp
        rw [conj_mul, h1, h2]
    refine Equiv.ext fun i => ?_
    show fwd z zp (g : G) i = i
    unfold fwd
    rw [key i, lab_pt hP]

theorem u₀_mem (hP : Pts z zp u₀ u₀') : u₀ ∈ NV z zp :=
  mem_normalizer_V0 hP (by rw [hP.u₀_z]; exact mem_z) (by rw [hP.u₀_zp]; exact mem_zzp)

theorem u₀'_mem (hP : Pts z zp u₀ u₀') : u₀' ∈ NV z zp :=
  mem_normalizer_V0 hP (by rw [hP.u₀'_z]; exact mem_zzp) (by rw [hP.u₀'_zp]; exact mem_zp)

theorem fwd_u₀_zero (hP : Pts z zp u₀ u₀') : fwd z zp u₀ 0 = 0 := by
  unfold fwd
  rw [pt_zero, hP.u₀_z, lab_z]

theorem fwd_u₀_one (hP : Pts z zp u₀ u₀') : fwd z zp u₀ 1 = 2 := by
  unfold fwd
  rw [pt_one, hP.u₀_zp, lab_zzp hP]

theorem fwd_u₀_two (hP : Pts z zp u₀ u₀') : fwd z zp u₀ 2 = 1 := by
  unfold fwd
  rw [pt_two, conj_mul, hP.u₀_z, hP.u₀_zp, z_mul_zzp hP, lab_zp hP]

theorem fwd_u₀'_zero (hP : Pts z zp u₀ u₀') : fwd z zp u₀' 0 = 2 := by
  unfold fwd
  rw [pt_zero, hP.u₀'_z, lab_zzp hP]

theorem fwd_u₀'_one (hP : Pts z zp u₀ u₀') : fwd z zp u₀' 1 = 1 := by
  unfold fwd
  rw [pt_one, hP.u₀'_zp, lab_zp hP]

theorem fwd_u₀'_two (hP : Pts z zp u₀ u₀') : fwd z zp u₀' 2 = 0 := by
  unfold fwd
  rw [pt_two, conj_mul, hP.u₀'_z, hP.u₀'_zp, zzp_mul_zp hP, lab_z]

theorem act_u₀ (hP : Pts z zp u₀ u₀') : act hP ⟨u₀, u₀_mem hP⟩ = Equiv.swap 1 2 := by
  have h0 : (Equiv.swap (1 : Fin 3) 2) 0 = 0 := by decide
  have h1 : (Equiv.swap (1 : Fin 3) 2) 1 = 2 := by decide
  have h2 : (Equiv.swap (1 : Fin 3) 2) 2 = 1 := by decide
  refine Equiv.ext fun i => ?_
  fin_cases i
  · exact (fwd_u₀_zero hP).trans h0.symm
  · exact (fwd_u₀_one hP).trans h1.symm
  · exact (fwd_u₀_two hP).trans h2.symm

theorem act_u₀' (hP : Pts z zp u₀ u₀') : act hP ⟨u₀', u₀'_mem hP⟩ = Equiv.swap 0 2 := by
  have h0 : (Equiv.swap (0 : Fin 3) 2) 0 = 2 := by decide
  have h1 : (Equiv.swap (0 : Fin 3) 2) 1 = 1 := by decide
  have h2 : (Equiv.swap (0 : Fin 3) 2) 2 = 0 := by decide
  refine Equiv.ext fun i => ?_
  fin_cases i
  · exact (fwd_u₀'_zero hP).trans h0.symm
  · exact (fwd_u₀'_one hP).trans h1.symm
  · exact (fwd_u₀'_two hP).trans h2.symm

theorem perm_fin3_words : ∀ σ : Equiv.Perm (Fin 3),
    σ = 1 ∨ σ = Equiv.swap 1 2 ∨ σ = Equiv.swap 0 2 ∨ σ = Equiv.swap 1 2 * Equiv.swap 0 2 ∨
      σ = Equiv.swap 0 2 * Equiv.swap 1 2 ∨
      σ = Equiv.swap 1 2 * Equiv.swap 0 2 * Equiv.swap 1 2 := by
  decide

theorem act_mul_mk (hP : Pts z zp u₀ u₀') {a b : G} (ha : a ∈ NV z zp) (hb : b ∈ NV z zp) :
    act hP ⟨a * b, mul_mem ha hb⟩ = act hP ⟨a, ha⟩ * act hP ⟨b, hb⟩ :=
  map_mul (act hP) ⟨a, ha⟩ ⟨b, hb⟩

theorem exists_perm_word (hP : Pts z zp u₀ u₀') (J : Subgroup G) (h₀ : u₀ ∈ J) (h₀' : u₀' ∈ J)
    (σ : Equiv.Perm (Fin 3)) : ∃ w : G, w ∈ J ∧ ∃ hw : w ∈ NV z zp, act hP ⟨w, hw⟩ = σ := by
  have hu := u₀_mem hP
  have hu' := u₀'_mem hP
  rcases perm_fin3_words σ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, one_mem J, one_mem _, map_one (act hP)⟩
  · exact ⟨u₀, h₀, hu, act_u₀ hP⟩
  · exact ⟨u₀', h₀', hu', act_u₀' hP⟩
  · refine ⟨u₀ * u₀', mul_mem h₀ h₀', mul_mem hu hu', ?_⟩
    rw [act_mul_mk hP hu hu', act_u₀ hP, act_u₀' hP]
  · refine ⟨u₀' * u₀, mul_mem h₀' h₀, mul_mem hu' hu, ?_⟩
    rw [act_mul_mk hP hu' hu, act_u₀ hP, act_u₀' hP]
  · refine ⟨u₀ * u₀' * u₀, mul_mem (mul_mem h₀ h₀') h₀, mul_mem (mul_mem hu hu') hu, ?_⟩
    rw [act_mul_mk hP (mul_mem hu hu') hu, act_mul_mk hP hu hu', act_u₀ hP, act_u₀' hP]

end PB

section Facts

variable {G : Type} [Group G]

theorem Pts.exists_beta {z zp u₀ u₀' : G} (hP : Pts z zp u₀ u₀') (J : Subgroup G) (h₀ : u₀ ∈ J) (h₀' : u₀' ∈ J)
    (hJ : J ≤ Subgroup.normalizer (V0of z zp : Set G)) :
    ∃ β : ↥J →* Equiv.Perm (Fin 3), Function.Surjective β ∧
      ∀ x : ↥J, β x = 1 ↔ (x : G) ∈ Subgroup.centralizer (V0of z zp : Set G) := by
  refine ⟨(PB.act hP).comp (Subgroup.inclusion hJ), ?_, ?_⟩
  · intro σ
    obtain ⟨w, hwJ, _, hw⟩ := PB.exists_perm_word hP J h₀ h₀' σ
    exact ⟨⟨w, hwJ⟩, hw⟩
  · intro x
    exact PB.act_eq_one_iff hP (Subgroup.inclusion hJ x)

theorem Pts.exists_word {z zp u₀ u₀' : G} (hP : Pts z zp u₀ u₀') (J : Subgroup G) (h₀ : u₀ ∈ J) (h₀' : u₀' ∈ J) :
    ∀ n ∈ Subgroup.normalizer (V0of z zp : Set G),
      ∃ w ∈ J, w⁻¹ * n ∈ Subgroup.centralizer (V0of z zp : Set G) := by
  intro n hn
  obtain ⟨w, hwJ, hwN, hw⟩ := PB.exists_perm_word hP J h₀ h₀' (PB.act hP ⟨n, hn⟩)
  refine ⟨w, hwJ, ?_⟩
  have hmem : w⁻¹ * n ∈ PB.NV z zp := mul_mem (inv_mem hwN) hn
  have h1 : PB.act hP ⟨w⁻¹ * n, hmem⟩ = 1 := by
    have e : (⟨w⁻¹ * n, hmem⟩ : ↥(PB.NV z zp)) = (⟨w, hwN⟩ : ↥(PB.NV z zp))⁻¹ * ⟨n, hn⟩ := rfl
    rw [e, map_mul, map_inv, hw, inv_mul_cancel]
  exact (PB.act_eq_one_iff hP ⟨w⁻¹ * n, hmem⟩).1 h1

end Facts

end S153P

end CFSG.Quasithin
