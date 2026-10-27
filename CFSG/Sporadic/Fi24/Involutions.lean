module

public import CFSG.Sporadic.Fi24.Generate

public section

namespace CFSG.Sporadic.Fi24

open CFSG.Blueprint.Fischer CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_conj_eq_tR
    {x : R} (hx : x ∈ D24) : ∃ g : J, jR g * x * (jR g)⁻¹ = tR := by
  obtain ⟨k, rfl⟩ := exists_cls hx
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq J root k
  refine ⟨g⁻¹, ?_⟩
  rw [cls_smul_root, map_inv]
  group

theorem exists_conj_star
    {f f' : R} (hf : f ∈ LocalClass D24 tR) (hf' : f' ∈ LocalClass D24 tR) :
    ∃ m ∈ MR, m * f * m⁻¹ = f' := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (Pair.isConj Fi23.pair_J (starEquiv ⟨f, hf⟩).2
    (starEquiv ⟨f', hf'⟩).2)
  set m := fi23EquivJMR.symm c
  have hm : (m : R) ∈ MR := m.2
  have hmf : (m : R) * f * (m : R)⁻¹ ∈ LocalClass D24 tR :=
    conj_mem_localClass_of_commute pair_R (commute_tR_of_mem_MR hm) hf
  refine ⟨m, hm, ?_⟩
  have e1 := starEquiv_conj hm ⟨f, hf⟩ hmf
  have e2 : fi23EquivJMR ⟨(m : R), hm⟩ = c := by
    show fi23EquivJMR m = c
    exact MulEquiv.apply_symm_apply _ _
  rw [e2, hc] at e1
  have := starEquiv.injective (Subtype.ext e1)
  have h' := Subtype.ext_iff.1 this
  exact h'

theorem exists_conj_pair
    {f f' : R} (hf : f ∈ D24) (hf' : f' ∈ LocalClass D24 f) :
    ∃ g : J, jR g * f * (jR g)⁻¹ = tR ∧ jR g * f' * (jR g)⁻¹ = xb := by
  obtain ⟨g₁, hg₁⟩ := exists_conj_eq_tR hf
  have h1 : jR g₁ * f' * (jR g₁)⁻¹ ∈ LocalClass D24 tR := by
    rw [← hg₁]
    exact (Pair.conj_mem_localClass_iff pair_R (jR g₁)).2 hf'
  obtain ⟨m, hm, hmf⟩ := exists_conj_star h1 xb_mem_localClass
  obtain ⟨m', hm', rfl⟩ := Subgroup.mem_map.1 hm
  refine ⟨m' * g₁, ?_, ?_⟩
  · rw [map_mul, show jR m' * jR g₁ * f * (jR m' * jR g₁)⁻¹ =
      jR m' * (jR g₁ * f * (jR g₁)⁻¹) * (jR m')⁻¹ by group, hg₁, commute_tR_of_mem_MR
      (Subgroup.mem_map.2 ⟨m', hm', rfl⟩), mul_inv_cancel_right]
  · rw [map_mul, show jR m' * jR g₁ * f' * (jR m' * jR g₁)⁻¹ =
      jR m' * (jR g₁ * f' * (jR g₁)⁻¹) * (jR m')⁻¹ by group]
    exact hmf

section Classes

variable (hPF : PolarFacts) {d1 t2 : Fi23.J} (hd1 : d1 ∈ LocalClass Fi23.D23 Fi23.d)
  (hcover : ∀ g : Fi23.J, g ^ 2 = 1 → g ≠ 1 →
    IsConj Fi23.d g ∨ IsConj (Fi23.d * d1) g ∨ IsConj t2 g)
include hPF hd1 hcover

theorem isConj_tJ_or_r2
    {s : J} (hs : s * s = 1) (hs1 : s ≠ 1) :
    IsConj s tJ ∨ IsConj s (fi23EquivM.symm t2 : J) := by
  have hs' : jR s * jR s = 1 := by rw [← map_mul, hs, map_one]
  obtain ⟨x, hx, hsx⟩ := exists_commute_D24 hPF hs'
  obtain ⟨g, hg⟩ := exists_conj_eq_tR hx
  set s' := g * s * g⁻¹ with hs'def
  have hs'M : s' ∈ M := by
    apply (commute_tR_iff s').1
    rw [← hg, hs'def, map_mul, map_mul, map_inv]
    calc jR g * jR s * (jR g)⁻¹ * (jR g * x * (jR g)⁻¹) = jR g * (jR s * x) * (jR g)⁻¹ := by
          group
      _ = jR g * (x * jR s) * (jR g)⁻¹ := by rw [hsx]
      _ = jR g * x * (jR g)⁻¹ * (jR g * jR s * (jR g)⁻¹) := by group
  have hss' : IsConj s s' := (isConj_iff (α := J)).2 ⟨g, rfl⟩
  set m : M := ⟨s', hs'M⟩
  have hm2 : fi23EquivM m ^ 2 = 1 := by
    rw [← map_pow, sq]
    have : m * m = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, OneMemClass.coe_one]
      show g * s * g⁻¹ * (g * s * g⁻¹) = 1
      rw [show g * s * g⁻¹ * (g * s * g⁻¹) = g * (s * s) * g⁻¹ by group, hs, mul_one,
        mul_inv_cancel])
    rw [this, map_one]
  have hm1 : fi23EquivM m ≠ 1 := by
    rw [Ne, MulEquiv.map_eq_one_iff]
    intro h
    apply hs1
    have h' : s' = 1 := by
      have := Subtype.ext_iff.1 h
      rw [OneMemClass.coe_one] at this
      exact this
    calc s = g⁻¹ * s' * g := by rw [hs'def]; group
      _ = 1 := by rw [h']; group
  have hconjM : ∀ {u : Fi23.J} {v : J} (hv : v ∈ M), IsConj u (fi23EquivM m) →
      fi23EquivM ⟨v, hv⟩ = u → IsConj s v := by
    intro u v hv huv hvu
    obtain ⟨c, hc⟩ := isConj_iff.1 huv
    have this : (fi23EquivM.symm c)⁻¹ * m * fi23EquivM.symm c = ⟨v, hv⟩ := by
      apply fi23EquivM.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← hc, hvu]
      group
    have h' := Subtype.ext_iff.1 this
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h'
    refine hss'.trans ((isConj_iff (α := J)).2 ⟨((fi23EquivM.symm c : M) : J)⁻¹, ?_⟩)
    rw [inv_inv]
    exact h'
  rcases hcover _ hm2 hm1 with h | h | h
  ·
    left
    have hsb := (Pair.isConj Fi23.pair_J (IsConj.refl Fi23.d) sb_mem_D23)
    exact hconjM tJ_mem_M ((hsb.symm.trans h)) fi23EquivM_tJ
  ·
    left
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    have hy : c * Fi23.d * c⁻¹ ∈ Fi23.D23 := Pair.conj_mem Fi23.pair_J (IsConj.refl Fi23.d) c
    have hy' : c * d1 * c⁻¹ ∈ LocalClass Fi23.D23 (c * Fi23.d * c⁻¹) :=
      (Pair.conj_mem_localClass_iff Fi23.pair_J c).2 hd1
    obtain ⟨f, hf⟩ := starEquiv.surjective ⟨_, hy⟩
    obtain ⟨f', hf'⟩ := starEquiv.surjective ⟨_, hy'.1⟩
    have hff' : (f' : R) ∈ LocalClass D24 f := by
      refine ⟨f'.2.1, fun e => hy'.2.1 ?_, ?_⟩
      · have := Subtype.ext_iff.1 (congrArg starEquiv (Subtype.ext e : f' = f))
        rw [hf, hf'] at this
        exact this
      · have := (localPoints_tR.comm f' f).2
        apply this
        show ((starEquiv f' : Fi23.D23) : Fi23.J) * starEquiv f = starEquiv f * starEquiv f'
        rw [hf, hf']
        exact hy'.2.2
    have hprod : jR s' = f * f' := by
      have e1 : fi23EquivJMR ⟨(f : R) * tR, mul_tR_mem_MR f.2⟩ *
          fi23EquivJMR ⟨(f' : R) * tR, mul_tR_mem_MR f'.2⟩ = fi23EquivM m := by
        rw [← starEquiv_val, ← starEquiv_val, hf, hf', ← hc]
        show c * Fi23.d * c⁻¹ * (c * d1 * c⁻¹) = c * (Fi23.d * d1) * c⁻¹
        group
      rw [← map_mul] at e1
      have e2 : mREquiv (⟨(f : R) * tR, mul_tR_mem_MR f.2⟩ *
          ⟨(f' : R) * tR, mul_tR_mem_MR f'.2⟩) = m := fi23EquivM.injective e1
      have e3 : jR ((mREquiv (⟨(f : R) * tR, mul_tR_mem_MR f.2⟩ *
          ⟨(f' : R) * tR, mul_tR_mem_MR f'.2⟩) : M) : J) = jR s' := by
        rw [e2]
      have e4 : ∀ z : MR, jR ((mREquiv z : M) : J) = z := fun z => by
        show ((M.equivMapOfInjective jR jR_injective) (mREquiv z) : R) = z
        rw [show mREquiv = (M.equivMapOfInjective jR jR_injective).symm from rfl,
          MulEquiv.apply_symm_apply]
      rw [← e3, e4, Subgroup.coe_mul]
      exact mul_tR_mul_mul_tR f'.2
    obtain ⟨h, h1, h2⟩ := exists_conj_pair f.2.1 hff'
    refine hss'.trans ((isConj_iff (α := J)).2 ⟨h, ?_⟩)
    apply jR_injective
    rw [map_mul, map_mul, map_inv, hprod, jR_tJ]
    calc jR h * ((f : R) * f') * (jR h)⁻¹ =
        (jR h * f * (jR h)⁻¹) * (jR h * f' * (jR h)⁻¹) := by group
      _ = tR * xb := by rw [h1, h2]
  ·
    right
    exact hconjM (fi23EquivM.symm t2).2 h (MulEquiv.apply_symm_apply _ _)

end Classes

end CFSG.Sporadic.Fi24
