module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtOrthGenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LieType.BorelTits

open CFSG.Quasithin.JonesParshall


private noncomputable def w183Sym {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Φ : QuadForm K (ι → K)) (v : ι → K) : orthGroup Φ.Q := by
  classical
  exact
    if hv : Φ.Q v ≠ 0 then
      ⟨Classical.choose (exists_mem_orthGroup_mulVec Φ.Q (Φ.reflect v) (Φ.reflect v)
          (Φ.reflect_reflect hv) (Φ.reflect_reflect hv) (Φ.Q_reflect v)),
        (Classical.choose_spec (exists_mem_orthGroup_mulVec Φ.Q (Φ.reflect v) (Φ.reflect v)
          (Φ.reflect_reflect hv) (Φ.reflect_reflect hv) (Φ.Q_reflect v))).1⟩
    else 1

private theorem w183Sym_apply {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Φ : QuadForm K (ι → K)) {v : ι → K} (hv : Φ.Q v ≠ 0) (x : ι → K) :
    Matrix.mulVec ((w183Sym Φ v : GL ι K) : Matrix ι ι K) x = Φ.reflect v x := by
  rw [w183Sym, dif_pos hv]
  exact (Classical.choose_spec (exists_mem_orthGroup_mulVec Φ.Q (Φ.reflect v) (Φ.reflect v)
    (Φ.reflect_reflect hv) (Φ.reflect_reflect hv) (Φ.Q_reflect v))).2.1 x

private theorem w183_eq_of_apply_eq {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {H : Subgroup (GL ι K)} {A B : H}
    (h : ∀ x : ι → K, Matrix.mulVec ((A : GL ι K) : Matrix ι ι K) x =
      Matrix.mulVec ((B : GL ι K) : Matrix ι ι K) x) : A = B := by
  apply natRep_injective H
  refine LinearMap.ext fun x => ?_
  rw [natRep_apply, natRep_apply, h x]

private theorem w183_natRep_apply {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Algebra (ZMod 2) K] {Γ : Subgroup (GL ι K)} (A : Γ) (x : ι → K) :
    s16ntNatRep Γ A x = Matrix.mulVec ((A : GL ι K) : Matrix ι ι K) x := rfl

private theorem w183_reflect_conj {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Φ : QuadForm K V) {g g' : V →ₗ[K] V} (hgg' : ∀ v, g (g' v) = v)
    (hg : ∀ v, Φ.Q (g v) = Φ.Q v) (w v : V) :
    g (Φ.reflect w (g' v)) = Φ.reflect (g w) v := by
  have hβ : Φ.polar.β w (g' v) = Φ.polar.β (g w) v := by
    rw [← Φ.polar_map_of_Q hg w (g' v), hgg']
  rw [Φ.reflect_apply, map_sub, map_smul, hgg', hβ, ← hg w, Φ.reflect_apply]

private theorem w183_eq_zero_or_one {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (a : K) : a = 0 ∨ a = 1 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    have hcard : Nat.card Kˣ = 1 := by
      have h := Nat.card_eq_card_units_add_one (α := K)
      omega
    haveI : Subsingleton Kˣ := (Finite.card_le_one_iff_subsingleton).mp (le_of_eq hcard)
    exact congrArg Units.val (Subsingleton.elim (Units.mk0 a ha) 1)

private theorem w183_add_self {ι : Type} {K : Type} [Field K] [Algebra (ZMod 2) K]
    (y : ι → K) : y + y = 0 := by
  haveI : CharP K 2 := (Algebra.charP_iff (ZMod 2) K 2).mp inferInstance
  funext i
  simpa using CharTwo.add_self_eq_zero (y i)

private theorem w183_s16ntPolar_eq {ι : Type} {K : Type} [Field K]
    (Φ : QuadForm K (ι → K)) (u w : ι → K) :
    s16ntPolar Φ.Q u w = Φ.polar.β u w := by
  rw [s16ntPolar, Φ.Q_add]
  abel

private theorem w183_independent {K V : Type} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] (Φ : QuadForm K V) {v w : V} (hv : Φ.Q v = 1) (hw : Φ.Q w = 1)
    (hvw : v ≠ w) : ∀ a b : K, a • v = b • w → a = 0 ∧ b = 0 := by
  intro a b hab
  have hv0 : v ≠ 0 := fun h => by rw [h, Φ.Q_zero] at hv; exact one_ne_zero hv.symm
  have hw0 : w ≠ 0 := fun h => by rw [h, Φ.Q_zero] at hw; exact one_ne_zero hw.symm
  by_cases ha : a = 0
  · rw [ha, zero_smul] at hab
    exact ⟨ha, (smul_eq_zero.mp hab.symm).resolve_right hw0⟩
  · exfalso
    have hb : b ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hab
      exact ha ((smul_eq_zero.mp hab).resolve_right hv0)
    have h1 : (a⁻¹ * b) • w = v := by
      rw [mul_smul, ← hab, smul_smul, inv_mul_cancel₀ ha, one_smul]
    have hc : v = (b / a) • w := by
      rw [div_eq_mul_inv, mul_comm]
      exact h1.symm
    have hcsq : (b / a) ^ 2 = 1 := by
      have h := Φ.Q_smul (b / a) w
      rw [← hc, hv, hw, mul_one] at h
      exact h.symm
    have hc1 : b / a = 1 := CharTwo.sq_inj.mp (by rw [hcsq, one_pow])
    exact hvw (by rw [hc, hc1, one_smul])

private theorem w183_cocycle_one {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Algebra (ZMod 2) K] (Φ : QuadForm K (ι → K))
    (c : Z1 (s16ntNatRep (orthGroup Φ.Q))) :
    (c : orthGroup Φ.Q → ι → K) 1 = 0 := by
  have h := c.2 1 1
  rw [one_mul, map_one, Module.End.one_apply] at h
  rw [w183_add_self] at h
  exact h

private theorem w183_span_normOne_eq_top {ι : Type} [Fintype ι] {K : Type} [Field K] [Finite K]
    [Algebra (ZMod 2) K] (hK : Nat.card K = 2) (Φ : QuadForm K (ι → K))
    (h3 : 3 ≤ Fintype.card ι) :
    Submodule.span K {v : ι → K | Φ.Q v = 1} = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  by_cases hx1 : Φ.Q x = 1
  · exact Submodule.subset_span hx1
  · rcases w183_eq_zero_or_one hK (Φ.Q x) with hx0 | hx1'
    · by_cases hx : x = 0
      · subst hx; exact Submodule.zero_mem _
      · obtain ⟨w, hwx, hQw⟩ := Φ.exists_polar_eq_zero_Q_ne_zero (by
            rw [Module.finrank_fintype_fun_eq_card]; exact h3) x
        have hw1 : Φ.Q w = 1 := by
          rcases w183_eq_zero_or_one hK (Φ.Q w) with h | h
          · exact absurd h hQw
          · exact h
        have hwx1 : Φ.Q (w + x) = 1 := by
          rw [Φ.Q_add, hw1, hx0, Φ.polar_symm w x, hwx, add_zero, add_zero]
        have hxw : x = w + (w + x) := by
          funext i
          rw [Pi.add_apply, Pi.add_apply, ← add_assoc,
            show w i + w i = 0 from by
              haveI : CharP K 2 := (Algebra.charP_iff (ZMod 2) K 2).mp inferInstance
              exact CharTwo.add_self_eq_zero (w i),
            zero_add]
        rw [hxw]
        exact Submodule.add_mem _ (Submodule.subset_span hw1) (Submodule.subset_span hwx1)
    · exact absurd hx1' hx1

private theorem w183_neg_eq_self {ι : Type} {K : Type} [Field K] [Algebra (ZMod 2) K]
    (y : ι → K) : -y = y := by
  haveI : CharP K 2 := (Algebra.charP_iff (ZMod 2) K 2).mp inferInstance
  funext i
  exact CharTwo.neg_eq (y i)

private theorem w183_sub_smul_eq_add {ι : Type} {K : Type} [Field K] [Algebra (ZMod 2) K]
    (x : ι → K) (a : K) (v : ι → K) : x - a • v = x + a • v := by
  haveI : CharP K 2 := (Algebra.charP_iff (ZMod 2) K 2).mp inferInstance
  rw [sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]

private theorem w183_add_eq_zero {ι : Type} {K : Type} [Field K] [Algebra (ZMod 2) K]
    {y z : ι → K} : y + z = 0 ↔ y = z := by
  constructor
  · intro h
    have h2 : y + z + z = 0 + z := congrArg (· + z) h
    rw [zero_add] at h2
    rwa [add_assoc, w183_add_self z, add_zero] at h2
  · intro h
    rw [h, w183_add_self z]

private theorem w183Sym_mul_self {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Φ : QuadForm K (ι → K)) {v : ι → K} (hv : Φ.Q v ≠ 0) :
    w183Sym Φ v * w183Sym Φ v = 1 := by
  apply w183_eq_of_apply_eq
  intro x
  rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, w183Sym_apply Φ hv,
    w183Sym_apply Φ hv, Φ.reflect_reflect hv]
  rw [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]

private theorem w183Sym_three {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Algebra (ZMod 2) K] (Φ : QuadForm K (ι → K)) {v w : ι → K}
    (hv : Φ.Q v = 1) (hw : Φ.Q w = 1) (hβ : Φ.polar.β v w = 1) :
    w183Sym Φ v * w183Sym Φ w * w183Sym Φ v = w183Sym Φ (v + w) := by
  haveI : CharP K 2 := (Algebra.charP_iff (ZMod 2) K 2).mp inferInstance
  have hvne : Φ.Q v ≠ 0 := by rw [hv]; exact one_ne_zero
  have hwne : Φ.Q w ≠ 0 := by rw [hw]; exact one_ne_zero
  have hvw1 : Φ.Q (v + w) = 1 := by
    rw [Φ.Q_add, hv, hw, hβ, CharTwo.add_self_eq_zero (1:K), zero_add]
  have hvwne : Φ.Q (v + w) ≠ 0 := by rw [hvw1]; exact one_ne_zero
  apply w183_eq_of_apply_eq
  intro x
  rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul, Units.val_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, w183Sym_apply Φ hvne, w183Sym_apply Φ hwne,
    w183Sym_apply Φ hvne,
    w183_reflect_conj Φ (Φ.reflect_reflect hvne) (Φ.Q_reflect v) w x]
  rw [show Φ.reflect v w = w + v by
    rw [Φ.reflect_apply, hv, div_one, hβ, w183_sub_smul_eq_add, one_smul]]
  rw [w183Sym_apply Φ hvwne, add_comm]

private theorem w183Sym_comm {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Algebra (ZMod 2) K] (Φ : QuadForm K (ι → K)) {v w : ι → K}
    (hv : Φ.Q v = 1) (hw : Φ.Q w = 1) (hβ : Φ.polar.β v w = 0) :
    w183Sym Φ v * w183Sym Φ w = w183Sym Φ w * w183Sym Φ v := by
  haveI : CharP K 2 := (Algebra.charP_iff (ZMod 2) K 2).mp inferInstance
  have hvne : Φ.Q v ≠ 0 := by rw [hv]; exact one_ne_zero
  have hwne : Φ.Q w ≠ 0 := by rw [hw]; exact one_ne_zero
  have h3 : w183Sym Φ v * w183Sym Φ w * w183Sym Φ v = w183Sym Φ w := by
    apply w183_eq_of_apply_eq
    intro x
    rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, w183Sym_apply Φ hvne, w183Sym_apply Φ hwne,
      w183Sym_apply Φ hvne,
      w183_reflect_conj Φ (Φ.reflect_reflect hvne) (Φ.Q_reflect v) w x]
    rw [show Φ.reflect v w = w by
      rw [Φ.reflect_apply, hv, div_one, hβ, zero_smul, sub_zero]]
    rw [w183Sym_apply Φ hwne]
  calc w183Sym Φ v * w183Sym Φ w
      = w183Sym Φ v * w183Sym Φ w * 1 := by rw [mul_one]
    _ = w183Sym Φ v * w183Sym Φ w * (w183Sym Φ v * w183Sym Φ v) := by
          rw [w183Sym_mul_self Φ hvne]
    _ = (w183Sym Φ v * w183Sym Φ w * w183Sym Φ v) * w183Sym Φ v := by group
    _ = w183Sym Φ w * w183Sym Φ v := by rw [h3]

private theorem w183_algebraMap_surjective {K : Type} [Field K] [Finite K] [Algebra (ZMod 2) K]
    (hK : Nat.card K = 2) : Function.Surjective (algebraMap (ZMod 2) K) := by
  intro c
  rcases w183_eq_zero_or_one hK c with h | h
  · exact ⟨0, by rw [h, map_zero]⟩
  · exact ⟨1, by rw [h, map_one]⟩

private theorem w183_span_eq {ι : Type} [Fintype ι] {K : Type} [Field K] [Finite K]
    [Algebra (ZMod 2) K] (hK : Nat.card K = 2) (v : ι → K) :
    (Submodule.span K ({v} : Set (ι → K)) : Set (ι → K)) =
      (Submodule.span (ZMod 2) ({v} : Set (ι → K)) : Set (ι → K)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨i, rfl⟩ := w183_algebraMap_surjective hK c
    rw [IsScalarTower.algebraMap_smul]
    exact Submodule.smul_mem _ i (Submodule.subset_span (Set.mem_singleton v))
  · intro x hx
    obtain ⟨i, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [← IsScalarTower.algebraMap_smul (A := K) i v]
    exact Submodule.smul_mem _ (algebraMap (ZMod 2) K i)
      (Submodule.subset_span (Set.mem_singleton v))

private theorem w183_cocycle_sym_mem_span {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] [Algebra (ZMod 2) K] (hK : Nat.card K = 2)
    (Φ : QuadForm K (ι → K)) {v : ι → K} (hv : Φ.Q v = 1)
    (c : Z1 (s16ntNatRep (orthGroup Φ.Q))) :
    (c : orthGroup Φ.Q → ι → K) (w183Sym Φ v) ∈
      Submodule.span (ZMod 2) ({v} : Set (ι → K)) := by
  haveI : CharP K 2 := (Algebra.charP_iff (ZMod 2) K 2).mp inferInstance
  have hvne : Φ.Q v ≠ 0 := by rw [hv]; exact one_ne_zero
  have hv0 : v ≠ 0 := fun h => by rw [h, Φ.Q_zero] at hv; exact one_ne_zero hv.symm
  set A := w183Sym Φ v with hAdef
  have hApp : ∀ x, Matrix.mulVec ((A : GL ι K) : Matrix ι ι K) x = Φ.reflect v x :=
    fun x => w183Sym_apply Φ hvne x
  have hA2 : A * A = 1 := w183Sym_mul_self Φ hvne
  have hcA : c.1 A = s16ntNatRep (orthGroup Φ.Q) A (c.1 A) := by
    have h := c.2 A A
    rw [hA2, w183_cocycle_one Φ c] at h
    exact w183_add_eq_zero.mp h.symm
  have hAv : Φ.polar.β v (c.1 A) = 0 := by
    have h1 : Φ.reflect v (c.1 A) = c.1 A := by
      rw [← hApp, ← w183_natRep_apply, ← hcA]
    have h3 : (Φ.polar.β v (c.1 A) / Φ.Q v) • v = 0 := by
      have h := h1.symm
      rw [Φ.reflect_apply] at h
      exact sub_eq_self.mp h.symm
    rw [hv, div_one] at h3
    exact (smul_eq_zero.mp h3).resolve_right hv0
  have hcomm0 : ∀ w, Φ.Q w = 1 → Φ.polar.β v w = 0 → w ≠ v →
      Φ.polar.β (c.1 A) w = 0 := by
    intro w hw hvw hwv
    have hwne : Φ.Q w ≠ 0 := by rw [hw]; exact one_ne_zero
    set B := w183Sym Φ w with hBdef
    have hAB : A * B = B * A := w183Sym_comm Φ hv hw hvw
    have hrel : Φ.polar.β v (c.1 B) • v = Φ.polar.β w (c.1 A) • w := by
      have h1 := c.2 A B
      have h2 := c.2 B A
      rw [hAB] at h1
      have h3 : c.1 A + Φ.reflect v (c.1 B) = c.1 B + Φ.reflect w (c.1 A) := by
        have hh := h1.symm.trans h2
        rw [w183_natRep_apply, w183_natRep_apply, hApp, w183Sym_apply Φ hwne] at hh
        exact hh
      rw [Φ.reflect_apply, Φ.reflect_apply, hv, hw, div_one, div_one,
        w183_sub_smul_eq_add, w183_sub_smul_eq_add] at h3
      have h4 : (Φ.polar.β v (c.1 B)) • v = (Φ.polar.β w (c.1 A)) • w := by
        have h := h3
        rw [← add_assoc, ← add_assoc, add_comm (c.1 B) (c.1 A)] at h
        exact add_left_cancel h
      exact h4
    have hind := w183_independent Φ hv hw (Ne.symm hwv)
      (Φ.polar.β v (c.1 B)) (Φ.polar.β w (c.1 A)) hrel
    rw [Φ.polar_symm]
    exact hind.2
  have hm : ∀ z, Φ.polar.β v z = 0 → Φ.polar.β (c.1 A) z = 0 := by
    intro z hvz
    by_cases hzv : z = v
    · subst hzv; rw [Φ.polar_symm]; exact hAv
    · by_cases hz0 : z = 0
      · subst hz0; rw [Φ.polar.β_zero_right]
      · rcases w183_eq_zero_or_one hK (Φ.Q z) with hQz | hQz
        · have hzv1 : Φ.Q (z + v) = 1 := by
            rw [Φ.Q_add, hQz, hv, Φ.polar_symm z v, hvz, add_zero, zero_add]
          have hzvne : z + v ≠ v :=
            fun h => hz0 (add_right_cancel (by rw [zero_add]; exact h))
          have hβzv : Φ.polar.β v (z + v) = 0 := by
            rw [Φ.polar.add_right, hvz, Φ.polar_self, hv, mul_one, CharTwo.two_eq_zero, add_zero]
          have h1 := hcomm0 (z + v) hzv1 hβzv hzvne
          rw [Φ.polar.add_right, Φ.polar_symm (c.1 A) v, hAv, add_zero] at h1
          exact h1
        · exact hcomm0 z hQz hvz hzv
  have hmem : c.1 A ∈ Φ.polar.perp (Φ.polar.perp (Submodule.span K ({v} : Set (ι → K)))) := by
    rw [Φ.polar.mem_perp]
    intro z hz
    rw [Φ.polar.mem_perp_span_singleton] at hz
    rw [Φ.polar_symm]
    exact hm z hz
  have hmemK : c.1 A ∈ (Submodule.span K ({v} : Set (ι → K)) : Set (ι → K)) := by
    rw [Φ.polar.perp_perp] at hmem
    exact hmem
  rw [w183_span_eq hK v] at hmemK
  exact hmemK

private theorem w183_mulVec_inv_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (A : GL ι K) (x : ι → K) :
    Matrix.mulVec (A : Matrix ι ι K) (Matrix.mulVec ((A⁻¹ : GL ι K) : Matrix ι ι K) x) = x := by
  rw [Matrix.mulVec_mulVec]
  have h : (A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [h, Matrix.one_mulVec]

private theorem w183Sym_conj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Φ : QuadForm K (ι → K)) (A : orthGroup Φ.Q) {v : ι → K} (hv : Φ.Q v ≠ 0) :
    A * w183Sym Φ v * A⁻¹ =
      w183Sym Φ (Matrix.mulVec ((A : GL ι K) : Matrix ι ι K) v) := by
  have hAv : Φ.Q (Matrix.mulVec ((A : GL ι K) : Matrix ι ι K) v) ≠ 0 := by
    rw [orthGroup_preserves Φ.Q A.2 v]; exact hv
  apply w183_eq_of_apply_eq
  intro x
  have h1 : Matrix.mulVec (((A * w183Sym Φ v * A⁻¹ : orthGroup Φ.Q) : GL ι K) :
      Matrix ι ι K) x =
      Matrix.mulVec ((A : GL ι K) : Matrix ι ι K)
        (Φ.reflect v (Matrix.mulVec ((A⁻¹ : orthGroup Φ.Q) : GL ι K) x)) := by
    rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, w183Sym_apply Φ hv]
  rw [h1, w183Sym_apply Φ hAv]
  rw [Φ.reflect_apply, Φ.reflect_apply, Matrix.mulVec_sub, Matrix.mulVec_smul]
  have hinv : Matrix.mulVec ((A : GL ι K) : Matrix ι ι K)
      (Matrix.mulVec ((A⁻¹ : orthGroup Φ.Q) : GL ι K) x) = x :=
    w183_mulVec_inv_mulVec (A : GL ι K) x
  have hβ : Φ.polar.β v (Matrix.mulVec ((A⁻¹ : orthGroup Φ.Q) : GL ι K) x) =
      Φ.polar.β (Matrix.mulVec ((A : GL ι K) : Matrix ι ι K) v) x := by
    rw [← Φ.polar_map_of_Q (g := Matrix.mulVecLin ((A : GL ι K) : Matrix ι ι K))
      (fun y => orthGroup_preserves Φ.Q A.2 y) v
      (Matrix.mulVec ((A⁻¹ : orthGroup Φ.Q) : GL ι K) x)]
    simp only [Matrix.mulVecLin_apply]
    rw [hinv]
  rw [hinv, hβ, orthGroup_preserves Φ.Q A.2 v]

private noncomputable def w183Evaluation {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] [Algebra (ZMod 2) K] (hK : Nat.card K = 2)
    (Φ : QuadForm K (ι → K)) {S : Set (ι → K)} (hS : ∀ v ∈ S, Φ.Q v = 1) :
    Z1 (s16ntNatRep (orthGroup Φ.Q)) →ₗ[ZMod 2]
      ((v : S) → Submodule.span (ZMod 2) ({v.1} : Set (ι → K))) where
  toFun c := fun v => ⟨c.1 (w183Sym Φ v.1), w183_cocycle_sym_mem_span hK Φ (hS v.1 v.2) c⟩
  map_add' c d := by
    funext v
    apply Subtype.ext
    rfl
  map_smul' a c := by
    funext v
    apply Subtype.ext
    rfl

private theorem w183Evaluation_injective {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] [Algebra (ZMod 2) K] (hK : Nat.card K = 2) (h3 : 3 ≤ Fintype.card ι)
    (Φ : QuadForm K (ι → K)) {S : Set (ι → K)} (hS : ∀ v ∈ S, Φ.Q v = 1)
    (hgen : S16ntNormOneGen Φ.Q S) :
    Function.Injective (w183Evaluation hK Φ hS) := by
  haveI : CharP K 2 := (Algebra.charP_iff (ZMod 2) K 2).mp inferInstance
  intro c d hcd
  let f : Z1 (s16ntNatRep (orthGroup Φ.Q)) := c - d
  have hSzero : ∀ v : S, f.1 (w183Sym Φ v.1) = 0 := by
    intro v
    have hval : c.1 (w183Sym Φ v.1) = d.1 (w183Sym Φ v.1) := by
      simpa only [w183Evaluation, LinearMap.coe_mk, AddHom.coe_mk] using
        congrArg (fun z : Submodule.span (ZMod 2) ({v.1} : Set (ι → K)) => (z : ι → K))
          (congrFun hcd v)
    have hf : f.1 (w183Sym Φ v.1) = c.1 (w183Sym Φ v.1) - d.1 (w183Sym Φ v.1) :=
      Pi.sub_apply c.1 d.1 (w183Sym Φ v.1)
    rw [hf, hval, sub_self]
  have hvan : ∀ v : ι → K, Φ.Q v = 1 → f.1 (w183Sym Φ v) = 0 := by
    intro v hv
    let T : Set (ι → K) := {u | Φ.Q u = 1 ∧ f.1 (w183Sym Φ u) = 0}
    have hST : S ⊆ T := fun u hu => ⟨hS u hu, hSzero ⟨u, hu⟩⟩
    have hcl : ∀ u ∈ T, ∀ w ∈ T, Φ.Q u = 1 → Φ.Q w = 1 → s16ntPolar Φ.Q u w = 1 →
        u + w ∈ T := by
      intro u hu w hw hu1 hw1 huvw
      have hβ : Φ.polar.β u w = 1 := by
        rw [← w183_s16ntPolar_eq Φ u w]; exact huvw
      refine ⟨?_, ?_⟩
      · rw [Φ.Q_add, hu1, hw1, hβ, CharTwo.add_self_eq_zero (1:K), zero_add]
      · rw [← w183Sym_three Φ hu1 hw1 hβ]
        have h1 := f.2 (w183Sym Φ u) (w183Sym Φ w * w183Sym Φ u)
        have h2 := f.2 (w183Sym Φ w) (w183Sym Φ u)
        simp only [hu.2, hw.2, map_zero, add_zero] at h2
        simp only [hu.2, h2, map_zero, add_zero] at h1
        rwa [← mul_assoc] at h1
    exact (hgen T hST hcl hv).2
  have hfzero : f = 0 := by
    apply Subtype.ext
    funext A
    have hbase : ∀ w : ι → K, Φ.Q w = 1 → Φ.polar.β (f.1 A)
        (Matrix.mulVec ((A : GL ι K) : Matrix ι ι K) w) = 0 := by
      intro w hw
      have hwne : Φ.Q w ≠ 0 := by rw [hw]; exact one_ne_zero
      have hAw1 : Φ.Q (Matrix.mulVec ((A : GL ι K) : Matrix ι ι K) w) = 1 := by
        rw [orthGroup_preserves Φ.Q A.2 w]; exact hw
      have hAwne : Φ.Q (Matrix.mulVec ((A : GL ι K) : Matrix ι ι K) w) ≠ 0 := by
        rw [hAw1]; exact one_ne_zero
      have hAs : A * w183Sym Φ w =
          w183Sym Φ (Matrix.mulVec ((A : GL ι K) : Matrix ι ι K) w) * A := by
        rw [← w183Sym_conj Φ A hwne]
        group
      have h1 := f.2 A (w183Sym Φ w)
      have h2 := f.2 (w183Sym Φ (Matrix.mulVec ((A : GL ι K) : Matrix ι ι K) w)) A
      rw [hAs] at h1
      rw [hvan w hw, map_zero, add_zero] at h1
      rw [hvan _ hAw1, zero_add] at h2
      have h3 : f.1 A = s16ntNatRep (orthGroup Φ.Q)
          (w183Sym Φ (Matrix.mulVec ((A : GL ι K) : Matrix ι ι K) w)) (f.1 A) :=
        h1.symm.trans h2
      rw [w183_natRep_apply, w183Sym_apply Φ hAwne] at h3
      have h4 : (Φ.polar.β (Matrix.mulVec ((A : GL ι K) : Matrix ι ι K) w) (f.1 A) /
          Φ.Q (Matrix.mulVec ((A : GL ι K) : Matrix ι ι K) w)) •
          (Matrix.mulVec ((A : GL ι K) : Matrix ι ι K) w) = 0 := by
        have h := h3
        rw [Φ.reflect_apply] at h
        exact sub_eq_self.mp h.symm
      rw [hAw1, div_one] at h4
      have h5 : Φ.polar.β (Matrix.mulVec ((A : GL ι K) : Matrix ι ι K) w) (f.1 A) = 0 :=
        (smul_eq_zero.mp h4).resolve_right (fun h => by
          rw [h, Φ.Q_zero] at hAw1; exact one_ne_zero hAw1.symm)
      rwa [Φ.polar_symm] at h5
    have hAβ : ∀ u : ι → K, Φ.polar.β (f.1 A)
        (Matrix.mulVec ((A : GL ι K) : Matrix ι ι K) u) = 0 := by
      intro u
      have hu : u ∈ Submodule.span K {w : ι → K | Φ.Q w = 1} := by
        rw [w183_span_normOne_eq_top hK Φ h3]; trivial
      induction hu using Submodule.span_induction with
      | mem w hw => exact hbase w hw
      | zero => rw [Matrix.mulVec_zero, Φ.polar.β_zero_right]
      | add a b _ _ ha hb =>
          rw [Matrix.mulVec_add, Φ.polar.add_right, ha, hb, add_zero]
      | smul c' a _ ha =>
          rw [Matrix.mulVec_smul, Φ.polar.smul_right, ha, mul_zero]
    have hβ : ∀ x : ι → K, Φ.polar.β (f.1 A) x = 0 := by
      intro x
      have hx : Matrix.mulVec ((A : GL ι K) : Matrix ι ι K)
          (Matrix.mulVec ((A⁻¹ : orthGroup Φ.Q) : GL ι K) x) = x :=
        w183_mulVec_inv_mulVec (A : GL ι K) x
      rw [← hx]
      exact hAβ _
    exact Φ.polar.nondeg (f.1 A) hβ
  exact sub_eq_zero.mp (show c - d = 0 from hfzero)

private theorem w183_coboundary_injective {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] [Algebra (ZMod 2) K] (hK : Nat.card K = 2) (h3 : 3 ≤ Fintype.card ι)
    (Φ : QuadForm K (ι → K)) :
    Function.Injective (coboundary (s16ntNatRep (orthGroup Φ.Q))) := by
  intro x y hxy
  have hzero : coboundary (s16ntNatRep (orthGroup Φ.Q)) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hfix : ∀ g : orthGroup Φ.Q, s16ntNatRep (orthGroup Φ.Q) g (x - y) = x - y := by
    intro g
    have h := congrFun hzero g
    simp only [coboundary, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h
    exact sub_eq_zero.mp h
  have hβ : ∀ u : ι → K, Φ.polar.β (x - y) u = 0 := by
    intro u
    have hu : u ∈ Submodule.span K {v : ι → K | Φ.Q v = 1} := by
      rw [w183_span_normOne_eq_top hK Φ h3]; trivial
    induction hu using Submodule.span_induction with
    | mem v hv =>
      have hv1 : Φ.Q v = 1 := hv
      have hvne : Φ.Q v ≠ 0 := by rw [hv1]; exact one_ne_zero
      have h1 := hfix (w183Sym Φ v)
      rw [w183_natRep_apply, w183Sym_apply Φ hvne] at h1
      have h2 : (Φ.polar.β v (x - y) / Φ.Q v) • v = 0 := by
        have h := h1
        rw [Φ.reflect_apply] at h
        exact sub_eq_self.mp h
      rw [hv1, div_one] at h2
      have h3 : Φ.polar.β v (x - y) = 0 :=
        (smul_eq_zero.mp h2).resolve_right (fun h => by
          rw [h, Φ.Q_zero] at hv1; exact one_ne_zero hv1.symm)
      rwa [Φ.polar_symm] at h3
    | zero => rw [Φ.polar.β_zero_right]
    | add a b _ _ ha hb => rw [Φ.polar.add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [Φ.polar.smul_right, ha, mul_zero]
  exact sub_eq_zero.mp (Φ.polar.nondeg (x - y) hβ)

theorem w183_orth_natural_h1_bound
    {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K] [Algebra (ZMod 2) K]
    (hK : Nat.card K = 2) (h3 : 3 ≤ Fintype.card ι)
    (Φ : QuadForm K (ι → K)) {S : Set (ι → K)}
    (hS : ∀ v ∈ S, Φ.Q v = 1) (hgen : S16ntNormOneGen Φ.Q S) :
    Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1
      (s16ntNatRep (orthGroup Φ.Q))) + Fintype.card ι ≤ S.ncard := by
  classical
  haveI : CharP K 2 := (Algebra.charP_iff (ZMod 2) K 2).mp inferInstance
  haveI : Fintype S := Fintype.ofFinite S
  let ρ := s16ntNatRep (orthGroup Φ.Q)
  have hZle : Module.finrank (ZMod 2) (Z1 ρ) ≤ S.ncard := by
    have hevInj : Function.Injective (w183Evaluation hK Φ hS) :=
      w183Evaluation_injective hK h3 Φ hS hgen
    haveI : ∀ v : S, Module.Free (ZMod 2)
        (Submodule.span (ZMod 2) ({v.1} : Set (ι → K))) :=
      fun v => Module.Free.of_divisionRing (ZMod 2) _
    have h1 : ∀ v : S, Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) ({v.1} : Set (ι → K))) = 1 := by
      intro v
      have hv1 := hS v.1 v.2
      have hv0 : v.1 ≠ 0 := fun h => by
        rw [h, Φ.Q_zero] at hv1
        exact one_ne_zero hv1.symm
      exact finrank_span_singleton hv0
    calc Module.finrank (ZMod 2) (Z1 ρ)
        ≤ Module.finrank (ZMod 2) ((v : S) → Submodule.span (ZMod 2) ({v.1} : Set (ι → K))) :=
          LinearMap.finrank_le_finrank_of_injective (R := ZMod 2) hevInj
      _ = ∑ v : S, Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({v.1} : Set (ι → K))) :=
          Module.finrank_pi_fintype (R := ZMod 2)
      _ = ∑ _ : S, (1 : ℕ) := Finset.sum_congr rfl (fun v _ => h1 v)
      _ = S.ncard := by simp
  have hVfin : Module.finrank (ZMod 2) (ι → K) = Fintype.card ι := by
    have hK1 : Module.finrank (ZMod 2) K = 1 := by
      have h := FiniteField.pow_finrank_eq_natCard 2 K
      rw [hK] at h
      have h2 : 2 ^ Module.finrank (ZMod 2) K = 2 ^ 1 := by rw [h]; norm_num
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2
    rw [Module.finrank_pi_fintype (R := ZMod 2)]
    simp [hK1]
  have hB1 : Module.finrank (ZMod 2) (B1 ρ) = Fintype.card ι := by
    rw [B1, LinearMap.finrank_range_of_inj (w183_coboundary_injective hK h3 Φ), hVfin]
  have hq := Submodule.finrank_quotient_add_finrank ((B1 ρ).comap (Z1 ρ).subtype)
  have hBcomap : Module.finrank (ZMod 2) ((B1 ρ).comap (Z1 ρ).subtype) =
      Module.finrank (ZMod 2) (B1 ρ) := by
    rw [← Submodule.finrank_map_subtype_eq (Z1 ρ) ((B1 ρ).comap (Z1 ρ).subtype),
      Submodule.map_comap_subtype, inf_eq_right.mpr (B1_le_Z1 ρ)]
  rw [hBcomap, hB1] at hq
  change Module.finrank (ZMod 2) (↥(Z1 ρ) ⧸ (B1 ρ).comap (Z1 ρ).subtype) +
    Fintype.card ι ≤ S.ncard
  omega


end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
