module

public import CFSG.Monster.GMS.ThreeAFi23Of
public import CFSG.Monster.GMS.Fi23FusionBasic
public import CFSG.Monster.GMS.Fi23FusionCert
public import CFSG.Sporadic.Fi23.S12

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Fi23 Equiv Equiv.Perm

theorem exists_three_of_isConj_t2
    {u : J} (h : IsConj t2 u) :
    ∃ x ∈ D23, ∃ y ∈ D23, ∃ z ∈ D23, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ x * y = y * x ∧ x * z = z * x ∧
      y * z = z * y ∧ u = x * y * z := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  obtain ⟨-, hc39d, hc39d1⟩ := three_commuting
  have hd1 := d1_mem_localClass
  have hcd : d * c39 = c39 * d := hc39d.2.2.symm
  have hcd1 : d1 * c39 = c39 * d1 := hc39d1.2.2.symm
  have hdd1 : d * d1 = d1 * d := hd1.2.2.symm
  refine ⟨c * d * c⁻¹, conj_mem_D23 c d (IsConj.refl d), c * d1 * c⁻¹, conj_mem_D23 c d1 hd1.1,
    c * c39 * c⁻¹, conj_mem_D23 c c39 hc39d.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hxy
    exact hd1.2.1 (mul_left_cancel (mul_right_cancel hxy)).symm
  · intro hxy
    exact hc39d.2.1 (mul_left_cancel (mul_right_cancel hxy)).symm
  · intro hxy
    exact hc39d1.2.1 (mul_left_cancel (mul_right_cancel hxy)).symm
  · calc c * d * c⁻¹ * (c * d1 * c⁻¹) = c * (d * d1) * c⁻¹ := by group
      _ = c * (d1 * d) * c⁻¹ := by rw [hdd1]
      _ = c * d1 * c⁻¹ * (c * d * c⁻¹) := by group
  · calc c * d * c⁻¹ * (c * c39 * c⁻¹) = c * (d * c39) * c⁻¹ := by group
      _ = c * (c39 * d) * c⁻¹ := by rw [hcd]
      _ = c * c39 * c⁻¹ * (c * d * c⁻¹) := by group
  · calc c * d1 * c⁻¹ * (c * c39 * c⁻¹) = c * (d1 * c39) * c⁻¹ := by group
      _ = c * (c39 * d1) * c⁻¹ := by rw [hcd1]
      _ = c * c39 * c⁻¹ * (c * d1 * c⁻¹) := by group
  · rw [← hc]
    show c * (d * d1 * c39) * c⁻¹ = _
    group

section Transfer

variable {d₀ : B} {G : Type} [Group G] [Finite G] {a z₀ : G}

theorem exists_fi23Transfer
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hS : BabyFi22Slice) :
    ∃ e : J → G, (∀ u v, e (u * v) = e u * e v) ∧ Function.Injective e ∧
      (∀ u, e u * a = a * e u) ∧
      (∀ x ∈ D23, ∀ y ∈ D23, x ≠ y → x * y = y * x → IsConj a (e (x * y))) ∧
      (∀ x ∈ D23, ∀ y ∈ D23, ∀ z ∈ D23, x ≠ y → x ≠ z → y ≠ z → x * y = y * x → x * z = z * x →
        y * z = z * y → IsConj z₀ (e (x * y * z))) := by
  obtain ⟨x', hx'o, hx'k⟩ :=
    s348_exists I.sls I.tableV I.leech I.leechOddPair I.tableIV hG (IsConj.refl a) 0
  have hx' : x' ∈ typeSet a z₀ a .threeA := ⟨hx'o, hx'k⟩
  have hxA : IsConj a x' := isConj_of_mem_typeSet hx'
  have hord : orderOf (a * x') = 3 := by
    obtain ⟨⟨-, -, -, w, hw, hwB⟩, hty⟩ := hx'
    exact (s348_card hty hw hwB).1
  obtain ⟨φ₀, hφ₀⟩ := threeAFi23_of I hG hS a x' (IsConj.refl a) hx'
  let e : J → G := fun u => (φ₀.symm (fi23EquivJ.symm u)).1
  have hmul : ∀ u v, e (u * v) = e u * e v := by
    intro u v
    show (φ₀.symm (fi23EquivJ.symm (u * v))).1 = _
    rw [map_mul, map_mul]
    rfl
  have hinj : Function.Injective e := fun u v h =>
    fi23EquivJ.symm.injective (φ₀.symm.injective (Subtype.ext h))
  have hD : ∀ x ∈ D23, e x ∈ twoANbr a a ∩ twoANbr a x' := by
    intro x hx
    obtain ⟨c, hc⟩ := isConj_iff.1 hx
    have hconj : IsConj dFi23 (fi23EquivJ.symm x) := by
      refine isConj_iff.2 ⟨fi23EquivJ.symm c, ?_⟩
      show fi23EquivJ.symm c * fi23EquivJ.symm d * (fi23EquivJ.symm c)⁻¹ = fi23EquivJ.symm x
      rw [← hc, map_mul, map_mul, map_inv]
    refine (hφ₀ (φ₀.symm (fi23EquivJ.symm x))).2 ?_
    rw [MulEquiv.apply_symm_apply]
    exact hconj
  refine ⟨e, hmul, hinj, fun u => ?_, ?_, ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.mem_inf.mp (φ₀.symm (fi23EquivJ.symm u)).2).1
  · intro x hx y hy hne hc
    have h := Fi23Fusion.commute_mem_twoBNbr I hG (IsConj.refl a) hxA hord (hD x hx) (hD y hy)
      (fun h => hne (hinj h)) (by rw [← hmul, ← hmul, hc])
    rw [hmul]
    exact h.1.1
  · intro x hx y hy z hz hxy hxz hyz cxy cxz cyz
    have h := Fi23Fusion.mul_mul_mem_twoBBNbr I hG (IsConj.refl a) hxA hord (hD x hx) (hD y hy)
      (hD z hz) (fun h => hxy (hinj h)) (fun h => hxz (hinj h)) (fun h => hyz (hinj h))
      (by rw [← hmul, ← hmul, cxy]) (by rw [← hmul, ← hmul, cxz])
      (by rw [← hmul, ← hmul, cyz])
    rw [hmul, hmul]
    exact h.1.1

end Transfer

namespace A12Fi23

open CFSG.Permutation.SymmetricCoxeter

theorem cycleType_mul_swap {σ : Perm (Fin 12)} {c e : Fin 12} (hce : c ≠ e) (hc : σ c = c)
    (he : σ e = e) : (σ * swap c e).cycleType = σ.cycleType + {2} := by
  have hdisj : Disjoint σ (swap c e) := by
    intro x
    by_cases hxc : x = c
    · exact Or.inl (hxc ▸ hc)
    by_cases hxe : x = e
    · exact Or.inl (hxe ▸ he)
    exact Or.inr (swap_apply_of_ne_of_ne hxc hxe)
  rw [hdisj.cycleType_mul, isSwap_iff_cycleType.mp ⟨c, e, hce, rfl⟩]

@[expose] def sigma2 : Perm (Fin 12) := adjSwap 11 0 * adjSwap 11 2

@[expose] def sigma4 : Perm (Fin 12) := sigma2 * adjSwap 11 4 * adjSwap 11 6

@[expose] def sigma6 : Perm (Fin 12) := sigma4 * adjSwap 11 8 * adjSwap 11 10

theorem sigma2_eq : sigma2 = swap (0 : Fin 12) 1 * swap 2 3 := by
  unfold sigma2
  rw [adjSwap_of_lt (n := 11) (i := 0) (by norm_num), adjSwap_of_lt (n := 11) (i := 2)
    (by norm_num)]
  rfl

theorem sigma4_eq :
    sigma4 = swap (0 : Fin 12) 1 * swap 2 3 * swap 4 5 * swap 6 7 := by
  unfold sigma4
  rw [sigma2_eq, adjSwap_of_lt (n := 11) (i := 4) (by norm_num),
    adjSwap_of_lt (n := 11) (i := 6) (by norm_num)]
  rfl

theorem sigma6_eq :
    sigma6 = swap (0 : Fin 12) 1 * swap 2 3 * swap 4 5 * swap 6 7 * swap 8 9 * swap 10 11 := by
  unfold sigma6
  rw [sigma4_eq, adjSwap_of_lt (n := 11) (i := 8) (by norm_num),
    adjSwap_of_lt (n := 11) (i := 10) (by norm_num)]
  rfl

theorem cycleType_sigma2 : sigma2.cycleType = {2, 2} := by
  have h2 := cycleType_mul_swap (σ := swap (0 : Fin 12) 1) (c := 2) (e := 3) (by decide)
    (by decide) (by decide)
  have h0 : (swap (0 : Fin 12) 1).cycleType = {2} := isSwap_iff_cycleType.mp ⟨0, 1, by decide, rfl⟩
  rw [sigma2_eq, h2, h0]
  rfl

theorem cycleType_sigma4 : sigma4.cycleType = {2, 2, 2, 2} := by
  have h2 := cycleType_mul_swap (σ := swap (0 : Fin 12) 1) (c := 2) (e := 3) (by decide)
    (by decide) (by decide)
  have h4 := cycleType_mul_swap (σ := swap (0 : Fin 12) 1 * swap 2 3) (c := 4) (e := 5)
    (by decide) (by decide) (by decide)
  have h6 := cycleType_mul_swap (σ := swap (0 : Fin 12) 1 * swap 2 3 * swap 4 5) (c := 6) (e := 7)
    (by decide) (by decide) (by decide)
  have h0 : (swap (0 : Fin 12) 1).cycleType = {2} := isSwap_iff_cycleType.mp ⟨0, 1, by decide, rfl⟩
  rw [sigma4_eq, h6, h4, h2, h0]
  rfl

theorem cycleType_sigma6 : sigma6.cycleType = {2, 2, 2, 2, 2, 2} := by
  have h2 := cycleType_mul_swap (σ := swap (0 : Fin 12) 1) (c := 2) (e := 3) (by decide)
    (by decide) (by decide)
  have h4 := cycleType_mul_swap (σ := swap (0 : Fin 12) 1 * swap 2 3) (c := 4) (e := 5)
    (by decide) (by decide) (by decide)
  have h6 := cycleType_mul_swap (σ := swap (0 : Fin 12) 1 * swap 2 3 * swap 4 5) (c := 6) (e := 7)
    (by decide) (by decide) (by decide)
  have h8 := cycleType_mul_swap (σ := swap (0 : Fin 12) 1 * swap 2 3 * swap 4 5 * swap 6 7)
    (c := 8) (e := 9) (by decide) (by decide) (by decide)
  have h10 := cycleType_mul_swap
    (σ := swap (0 : Fin 12) 1 * swap 2 3 * swap 4 5 * swap 6 7 * swap 8 9) (c := 10) (e := 11)
    (by decide) (by decide) (by decide)
  have h0 : (swap (0 : Fin 12) 1).cycleType = {2} := isSwap_iff_cycleType.mp ⟨0, 1, by decide, rfl⟩
  rw [sigma6_eq, h10, h8, h6, h4, h2, h0]
  rfl

theorem injective_comp_alternating {n : ℕ} (hn : 5 ≤ n) {H : Type*} [Group H]
    (ψ : Perm (Fin n) →* H) {σ : Perm (Fin n)} (hσ : σ ∈ alternatingGroup (Fin n))
    (hne : ψ σ ≠ 1) : Function.Injective (ψ.comp (alternatingGroup (Fin n)).subtype) := by
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (ψ.comp (alternatingGroup (Fin n)).subtype).ker with h | h
  · exact h
  · exfalso
    have h1 : (ψ.comp (alternatingGroup (Fin n)).subtype) ⟨σ, hσ⟩ = 1 :=
      MonoidHom.mem_ker.1 (by rw [h]; exact Subgroup.mem_top _)
    exact hne h1

end A12Fi23

open A12Fi23

theorem exists_a12Fusion_of_fi22Slice
    {d₀ : B} {G : Type} [Group G] [Finite G] {a z₀ : G}
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hS : BabyFi22Slice) :
    ∃ φ : alternatingGroup (Fin 12) →* G, S36Lines.A12Fusion a z₀ φ := by
  obtain ⟨e, he_mul, he_inj, he_comm, he_A, he_Z⟩ := exists_fi23Transfer I hG hS
  obtain ⟨ψ, hψ⟩ := exists_hom_s12
  have hψ2 : ψ sigma2 = sEl 0 * sEl 2 := by
    rw [sigma2, map_mul, hψ 0 (by norm_num), hψ 2 (by norm_num)]
  have hψ4 : ψ sigma4 = sEl 0 * sEl 2 * sEl 4 * sEl 6 := by
    rw [sigma4, map_mul, map_mul, hψ2, hψ 4 (by norm_num), hψ 6 (by norm_num)]
  have hψ6 : ψ sigma6 = sEl 0 * sEl 2 * sEl 4 * sEl 6 * sEl 8 * sEl 10 := by
    rw [sigma6, map_mul, map_mul, hψ4, hψ 8 (by norm_num), hψ 10 (by norm_num)]
  have hmem2 : sigma2 ∈ alternatingGroup (Fin 12) := by
    rw [mem_alternatingGroup, sigma2_eq]
    decide
  have hne2 : ψ sigma2 ≠ 1 := by
    rw [hψ2]
    exact sEl_zero_mul_two_ne_one
  have hinj := injective_comp_alternating (by norm_num : 5 ≤ 12) ψ hmem2 hne2
  let φ : alternatingGroup (Fin 12) →* G := MonoidHom.mk' (fun σ => e (ψ (σ : Perm (Fin 12))))
    (fun σ τ => by rw [Subgroup.coe_mul, map_mul, he_mul])
  refine ⟨φ, fun σ τ h => hinj (he_inj h), fun σ => he_comm _, ?_, ?_⟩
  · intro σ hσ
    have hconj : IsConj (ψ sigma2) (ψ (σ : Perm (Fin 12))) ∨
        IsConj (ψ sigma6) (ψ (σ : Perm (Fin 12))) := by
      rcases hσ with h | h
      · exact Or.inl (MonoidHom.map_isConj ψ
          (isConj_iff_cycleType_eq.2 (cycleType_sigma2.trans h.symm)))
      · exact Or.inr (MonoidHom.map_isConj ψ
          (isConj_iff_cycleType_eq.2 (cycleType_sigma6.trans h.symm)))
    have hJ : IsConj (d * d1) (ψ (σ : Perm (Fin 12))) := by
      rcases hconj with h | h
      · rw [hψ2] at h
        exact isConj_d_mul_d1_s2.trans h
      · rw [hψ6] at h
        exact isConj_d_mul_d1_s6.trans h
    obtain ⟨x, hx, y, hy, hxy, hc, hu⟩ := exists_two_of_isConj_d_mul_d1 hJ
    show IsConj a (e (ψ (σ : Perm (Fin 12))))
    rw [hu]
    exact he_A x hx y hy hxy hc
  · intro σ hσ
    have hconj : IsConj (ψ sigma4) (ψ (σ : Perm (Fin 12))) :=
      MonoidHom.map_isConj ψ (isConj_iff_cycleType_eq.2 (cycleType_sigma4.trans hσ.symm))
    rw [hψ4] at hconj
    obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz, cxy, cxz, cyz, hu⟩ :=
      exists_three_of_isConj_t2 (isConj_t2_s4.trans hconj)
    show IsConj z₀ (e (ψ (σ : Perm (Fin 12))))
    rw [hu]
    exact he_Z x hx y hy z hz hxy hxz hyz cxy cxz cyz

end CFSG.Monster.GMS
