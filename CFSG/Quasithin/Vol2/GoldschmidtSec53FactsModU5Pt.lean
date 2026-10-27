module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5Stab
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryAutomorphismCover
public import CFSG.LocalAnalysis.EvenBN.U5.ModelLevi
public import CFSG.LocalAnalysis.EvenBN.U5.ModelSylowRank
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5Gen

public section

namespace CFSG.Quasithin.H13.Sec53F.Unit

open scoped Pointwise commutatorElement
open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem N₂sub_le_u5PtStab {h : UnitaryFieldData 2 f K} : N₂sub h ≤ u5PtStab h := by
  intro g hg
  rw [mem_u5PtStab_iff]
  intro a ha
  rw [(mem_N₂sub.mp hg).1 a, one_apply_ne ha]

theorem N₂sub_le_perfectCore_u5PtStab {h : UnitaryFieldData 2 f K} (hf : 2 ≤ f) :
    N₂sub h ≤ perfectCore (u5PtStab h) := by
  rw [← range_embSU]
  exact range_le_perfectCore
    (CFSG.ShultStronglyClosedTI.UnitaryAutomorphism.isPerfect_hypSU h (two_lt_two_pow hf))
    (embSU h) (by rw [range_embSU]; exact N₂sub_le_u5PtStab)

theorem exists_torus_point {h : UnitaryFieldData 2 f K} (hf : 2 ≤ f) :
    ∃ t ∈ Isub h, t ∈ N₂sub h ∧ ∀ p ∈ sZP, mat t p.1 p.1 ≠ mat t p.2 p.2 := by
  obtain ⟨ω, hω⟩ := exists_unit_generator h
  obtain ⟨t, htI, e1, e2, e3, e4, e5⟩ := exists_torus_zpow h ω 0 1
  refine ⟨t, htI, mem_N₂sub_of_torus htI (by rw [e1]; simp) (by rw [e4]; simp), ?_⟩
  intro p hp
  simp only [sZP, Finset.mem_insert, Finset.mem_singleton] at hp
  have key : ∀ {m n : ℤ}, m ≠ n → m - n ≤ 2 * ((2 ^ f : ℕ) : ℤ) →
      n - m ≤ 2 * ((2 ^ f : ℕ) : ℤ) → ((ω ^ m : Kˣ) : K) ≠ ((ω ^ n : Kˣ) : K) :=
    fun h0 h1 h2 => zpow_val_ne_of_le hω hf h0 h1 h2
  have hq := four_le_q hf
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [e1, e2, e3, e4, e5] <;> exact key (by omega) (by omega) (by omega)

theorem exists_commutator_ZPsub {h : UnitaryFieldData 2 f K} {z : hypSU h 2 1}
    (hz : z ∈ ZPsub h) : ∃ x ∈ hypUnitriangular h 2 1, ∃ y ∈ hypUnitriangular h 2 1,
      x * y * x⁻¹ * y⁻¹ = z := by
  have := h.charP
  have hcF := bar_eq_of_mem_ZPsub hz
  obtain ⟨b, hb⟩ := trace_surj (hK := h) hcF
  obtain ⟨y, hy, hya⟩ := exists_rootI₁ h 1
  obtain ⟨x, hx, hxb⟩ := exists_rootI₄ h b
  obtain ⟨hyU, y1, y2, y3, y4, y5, y6, y7, y8⟩ := mem_patSub_sI₁.1 hy
  obtain ⟨hxU, x1, x2, x3, x4, x5, x6, x7, x8⟩ := mem_patSub_sI₄.1 hx
  obtain ⟨ry1, -, -, -, -, -⟩ := U_rel hyU
  have rx4 : mat x ιe₂ ιf₁ = h.bar b := by
    have := (U_rel hxU).2.2.2.1
    rw [hxb, x1, x3, x5] at this
    simpa using this
  rw [hya, map_one] at ry1
  have hcomm : ⁅x, y⁆ ∈ ZPsub h := by
    refine (commutator_mem_ZPsub_iff hxU hyU).2 (forall_upper.2 ?_)
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun hne => absurd rfl hne, fun _ => ?_,
      fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · rw [mul_e₁e₂ hxU hyU, mul_e₁e₂ hyU hxU]; simp [x1, hya, add_comm]
    · rw [mul_e₁z hxU hyU, mul_e₁z hyU hxU]; simp [x1, x3, x5, y1, y3]
    · rw [mul_e₁f₂ hxU hyU, mul_e₁f₂ hyU hxU]; simp [x1, x3, x6, x7, y1, y4, y5, y7, hxb, hya]
    · rw [mul_e₂z hxU hyU, mul_e₂z hyU hxU]; simp [x5, y3]
    · rw [mul_e₂f₂ hxU hyU, mul_e₂f₂ hyU hxU]; simp [x5, x6, x7, y3, y4, y7]
    · rw [mul_e₂f₁ hxU hyU, mul_e₂f₁ hyU hxU]
      simp [x4, x7, y3, y6, y7, rx4, ry1, x2, x5]
    · rw [mul_zf₂ hxU hyU, mul_zf₂ hyU hxU]; simp [x6, y4]
    · rw [mul_zf₁ hxU hyU, mul_zf₁ hyU hxU]; simp [x2, x4, x6, y2, y4, ry1]
    · rw [mul_f₂f₁ hxU hyU, mul_f₂f₁ hyU hxU]; simp [x2, ry1, add_comm]
  have hyx : y * x ∈ hypUnitriangular h 2 1 := mul_mem hyU hxU
  have hent := (mul_ZPsub_entries hcomm hyx).2
  rw [commutatorElement_def] at hcomm hent
  rw [show x * y * x⁻¹ * y⁻¹ * (y * x) = x * y by group, mul_e₁f₁ hxU hyU,
    mul_e₁f₁ hyU hxU] at hent
  simp only [x1, x3, x4, x8, y1, y2, y5, y8, y6, hxb, hya, rx4, ry1] at hent
  refine ⟨x, hxU, y, hyU, eq_of_mem_ZPsub hcomm hz ?_⟩
  linear_combination hb - hent - CharTwo.add_self_eq_zero (h.bar b)

theorem U_le_perfectCore_u5PtStab {h : UnitaryFieldData 2 f K} (hf : 2 ≤ f) :
    hypUnitriangular h 2 1 ≤ perfectCore (u5PtStab h) := by
  have : Finite (hypSU h 2 1) := by have := h.finite; infer_instance
  obtain ⟨t, htI, htN, hne⟩ := exists_torus_point (h := h) hf
  have htP : t ∈ perfectCore (u5PtStab h) := N₂sub_le_perfectCore_u5PtStab hf htN
  have hUP : hypUnitriangular h 2 1 ≤ u5PtStab h :=
    (hypUnitriangular_le_hypBorel h).trans (hypBorel_le_isoStabilizer h le_rfl (by norm_num))
  have hnorm : ∀ g ∈ u5PtStab h, ∀ n ∈ perfectCore (u5PtStab h),
      g * n * g⁻¹ ∈ perfectCore (u5PtStab h) := by
    intro g hg n hn
    have := normalizer_le_normalizer_perfectCore (u5PtStab h) (Subgroup.le_normalizer hg)
    exact (Subgroup.mem_normalizer_iff.mp this n).mp hn
  have hfix : ∀ v ∈ hypUnitriangular h 2 1, ∀ z ∈ ZPsub h, t * v * t⁻¹ = v * z →
      v ∈ ZPsub h := by
    intro v hv z hz e
    obtain ⟨l1, -⟩ := mul_ZPsub_entries_right hz hv
    refine mem_patSub.2 ⟨hv, fun p hp => ?_⟩
    have hpos := isPattern_sZP.upper p hp
    have hpne : p ≠ (ιe₁, ιf₁) := by
      rintro rfl
      revert hp
      decide
    have e1 : mat (t * v * t⁻¹) p.1 p.2 = mat (v * z) p.1 p.2 := by rw [e]
    rw [torus_conj_apply htI, l1 p.1 p.2 hpos hpne] at e1
    have hb := torus_ne_zero htI p.2
    have : mat v p.1 p.2 * (mat t p.1 p.1 - mat t p.2 p.2) = 0 := by
      field_simp at e1
      linear_combination e1
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 (hne p hp))
  have key := exists_commutator_mul (U := hypUnitriangular h 2 1) (Z := ZPsub h)
    (fun z hz u hu => (ZPsub_commute hz hu).symm) (t := t)
    (fun u hu => torus_conj_mem_U htI hu)
    (fun z hz => torus_conj_mem_patSub isPattern_sZP htI hz) hfix
  have hcU : ∀ u ∈ hypUnitriangular h 2 1, u * t * u⁻¹ * t⁻¹ ∈ hypUnitriangular h 2 1 := by
    intro u hu
    have := mul_mem hu (torus_conj_mem_U htI (inv_mem hu))
    simpa [mul_assoc] using this
  have hcN : ∀ u ∈ hypUnitriangular h 2 1, u * t * u⁻¹ * t⁻¹ ∈ perfectCore (u5PtStab h) :=
    fun u hu => mul_mem (hnorm u (hUP hu) t htP) (inv_mem htP)
  have hZN : ZPsub h ≤ perfectCore (u5PtStab h) := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_commutator_ZPsub hz
    obtain ⟨u₁, hu₁, z₁, hz₁, hx'⟩ := key x hx
    obtain ⟨u₂, hu₂, z₂, hz₂, hy'⟩ := key y hy
    rw [hx', hy', commutator_mul_mul_of_commute]
    · exact mul_mem (mul_mem (mul_mem (hcN u₁ hu₁) (hcN u₂ hu₂)) (inv_mem (hcN u₁ hu₁)))
        (inv_mem (hcN u₂ hu₂))
    · exact ZPsub_commute hz₁ (mul_mem (hcU u₂ hu₂) (ZPsub_le_U hz₂))
    · exact ZPsub_commute hz₂ (hcU u₁ hu₁)
  intro g hg
  obtain ⟨u, hu, z, hz, rfl⟩ := key g hg
  exact mul_mem (hcN u hu) (hZN hz)

theorem mat_ZPsub {z : hypSU h 2 1} (hz : z ∈ ZPsub h) :
    mat z = 1 + Matrix.single ιe₁ ιf₁ (mat z ιe₁ ιf₁) := by
  obtain ⟨hzU, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := mem_ZPsub.1 hz
  obtain ⟨⟨d1, d2, d3, d4, d5⟩, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩⟩ := U_entries hzU
  ext a b
  rcases hypIndex_cases a with rfl | rfl | rfl | rfl | rfl <;>
    rcases hypIndex_cases b with rfl | rfl | rfl | rfl | rfl <;>
    simp [ιe₁, ιe₂, ιz, ιf₁, ιf₂, *]

theorem conj_single_ptStab {g : hypSU h 2 1} (hg : g ∈ u5PtStab h) (c : K) :
    mat g * Matrix.single ιe₁ ιf₁ c * mat g⁻¹ =
      Matrix.single ιe₁ ιf₁ (mat g ιe₁ ιe₁ * h.bar (mat g ιe₁ ιe₁) * c) := by
  have hcol := (mem_u5PtStab_iff g).1 hg
  ext a b
  have e1 : (mat g * Matrix.single ιe₁ ιf₁ c * mat g⁻¹) a b =
      mat g a ιe₁ * c * mat g⁻¹ ιf₁ b := by
    simp [Matrix.mul_apply, Matrix.single_apply]
  rw [e1, mat_inv_apply]
  have hp : hypPartner ιf₁ = ιe₁ := rfl
  rw [hp]
  by_cases ha : a = ιe₁
  · subst ha
    by_cases hb : b = ιf₁
    · subst hb
      simp only [hp, Matrix.single_apply_same]
      ring
    · have hne : hypPartner b ≠ ιe₁ := fun e => hb (by
        rw [← hypPartner_hypPartner b, e]; rfl)
      rw [hcol _ hne]
      simp [Ne.symm hb]
  · rw [hcol a ha]
    simp [Ne.symm ha]

theorem conj_mem_ZPsub_of_mem_u5PtStab {g z : hypSU h 2 1} (hg : g ∈ u5PtStab h)
    (hz : z ∈ ZPsub h) : g * z * g⁻¹ ∈ ZPsub h := by
  have hcF := bar_eq_of_mem_ZPsub hz
  have hc' : h.bar (mat g ιe₁ ιe₁ * h.bar (mat g ιe₁ ιe₁) * mat z ιe₁ ιf₁) =
      mat g ιe₁ ιe₁ * h.bar (mat g ιe₁ ιe₁) * mat z ιe₁ ιf₁ := by
    rw [map_mul, map_mul, h.bar_bar, hcF]
    ring
  obtain ⟨z', hz', hz'c⟩ := exists_rootZP h hc'
  have : g * z * g⁻¹ = z' := by
    apply mat_injective
    rw [mat_mul, mat_mul, mat_ZPsub hz, mat_ZPsub hz', hz'c, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, ← mat_mul, mul_inv_cancel, mat_one, conj_single_ptStab hg]
  rw [this]
  exact hz'

theorem exists_conj_ZPsub {z z' : hypSU h 2 1} (hz : z ∈ ZPsub h) (hz' : z' ∈ ZPsub h)
    (h1 : z ≠ 1) (h1' : z' ≠ 1) : ∃ m ∈ Isub h, m * z * m⁻¹ = z' := by
  obtain ⟨-, hc⟩ := ZPsub_eq_conj_z₁ h
  obtain ⟨t₁, ht₁, e₁⟩ := hc z hz h1
  obtain ⟨t₂, ht₂, e₂⟩ := hc z' hz' h1'
  refine ⟨t₂⁻¹ * t₁, mul_mem (inv_mem (mem_I₂sub.1 ht₂).1) (mem_I₂sub.1 ht₁).1, ?_⟩
  rw [e₁, e₂]
  group

end CFSG.Quasithin.H13.Sec53F.Unit
