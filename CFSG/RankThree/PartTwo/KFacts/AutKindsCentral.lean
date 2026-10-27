module

public import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree
public import CFSG.RankThree.PartTwo.KFacts.AutPSUOrderThree

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

section Perfect

variable {S : Type*} [Group S]

theorem eq_one_of_forall_mul_inv_mem_center [Group.IsPerfect S] {τ : MulAut S}
    (h : ∀ s : S, s⁻¹ * τ s ∈ Subgroup.center S) : τ = 1 := by
  let z : S →* S :=
    { toFun := fun s => s⁻¹ * τ s
      map_one' := by simp
      map_mul' := fun s t => by
        have ht := Subgroup.mem_center_iff.mp (h s)
        calc (s * t)⁻¹ * τ (s * t) = t⁻¹ * (s⁻¹ * τ s) * τ t := by
              rw [map_mul]
              group
          _ = s⁻¹ * τ s * (t⁻¹ * τ t) := by
              rw [ht t⁻¹]
              group }
  have hzc : ∀ s, z s ∈ Subgroup.center S := h
  have hcomm : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ ≤ z.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    have hab := Subgroup.mem_center_iff.mp (hzc a) (z b)
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hab.symm
  have htop : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤ := Group.IsPerfect.commutator_eq_top
  rw [htop] at hcomm
  refine MulEquiv.ext fun s => ?_
  have hs : z s = 1 := hcomm (Subgroup.mem_top s)
  change s⁻¹ * τ s = 1 at hs
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.mp hs).symm

theorem isInnerAut_of_forall_mem_center [Group.IsPerfect S] {τ : MulAut S} (g : S)
    (h : ∀ s : S, (g * s * g⁻¹)⁻¹ * τ s ∈ Subgroup.center S) : IsInnerAut τ := by
  refine ⟨g, inv_mul_eq_one.mp (eq_one_of_forall_mul_inv_mem_center fun s => ?_)⟩
  have h4 : g⁻¹ * ((g * s * g⁻¹)⁻¹ * τ s) * g⁻¹⁻¹ ∈ Subgroup.center S :=
    (inferInstance : (Subgroup.center S).Normal).conj_mem _ (h s) g⁻¹
  rw [inv_inv] at h4
  rw [MulAut.mul_apply, ← map_inv, MulAut.conj_apply, inv_inv,
    show s⁻¹ * (g⁻¹ * τ s * g) = g⁻¹ * ((g * s * g⁻¹)⁻¹ * τ s) * g by group]
  exact h4

theorem centerDescend_conj (g : S) :
    centerDescend S (MulAut.conj g) = MulAut.conj (g : S ⧸ Subgroup.center S) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H y => rfl

theorem isInnerAut_congr_centerDescend {M : Type*} [Group M] (e : S ⧸ Subgroup.center S ≃* M)
    {τ : MulAut S} (hτ : IsInnerAut τ) : IsInnerAut (MulAut.congr e (centerDescend S τ)) := by
  obtain ⟨g, rfl⟩ := hτ
  rw [centerDescend_conj, congr_mulAutConj]
  exact isInnerAut_conj _

theorem isInnerAut_of_isInnerAut_centerDescend [Group.IsPerfect S] {τ : MulAut S}
    (hτ : IsInnerAut (centerDescend S τ)) : IsInnerAut τ := by
  obtain ⟨x, hx⟩ := hτ
  induction x using QuotientGroup.induction_on with
  | H g =>
    refine isInnerAut_of_forall_mem_center g fun s => ?_
    have h1 := congrArg (fun φ : MulAut (S ⧸ Subgroup.center S) =>
      φ (s : S ⧸ Subgroup.center S)) hx
    simp only [MulAut.conj_apply, centerDescend_mk] at h1
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      QuotientGroup.eq] at h1
    exact h1

end Perfect

section Linear

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {K : Type*} [Field K]

theorem descendAut_conj (g : Matrix.SpecialLinearGroup (Fin n) K) :
    descendAut n K (MulAut.conj g) = MulAut.conj (proj n K g) := by
  ext x
  obtain ⟨y, rfl⟩ := proj_surjective n K x
  rw [descendAut_proj, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem isInnerAut_descendAut {τ : MulAut (Matrix.SpecialLinearGroup (Fin n) K)}
    (hτ : IsInnerAut τ) : IsInnerAut (descendAut n K τ) := by
  obtain ⟨g, rfl⟩ := hτ
  exact ⟨proj n K g, (descendAut_conj g).symm⟩

theorem isInnerAut_descendAut_iff (hn : 3 ≤ n)
    {τ : MulAut (Matrix.SpecialLinearGroup (Fin n) K)} :
    IsInnerAut (descendAut n K τ) ↔ IsInnerAut τ := by
  refine ⟨fun hτ => ?_, isInnerAut_descendAut⟩
  have := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := K) hn
  obtain ⟨x, hx⟩ := hτ
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  refine isInnerAut_of_forall_mem_center g fun s => ?_
  have h1 := congrArg (fun φ : MulAut (projectiveSL n K) => φ (proj n K s)) hx
  simp only [MulAut.conj_apply, descendAut_proj] at h1
  rw [← map_inv, ← map_mul, ← map_mul, proj_eq_proj_iff] at h1
  exact scalars_le_center n K h1

end Linear

section Unitary

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

include h in
theorem isPerfect_unitarySU_three (hq : 2 < p ^ f) : Group.IsPerfect (unitarySU p f K 3) := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hcard : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  exact CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hcard le_rfl
    (by intro hh; simp only [Prod.mk.injEq, true_and] at hh; omega)

theorem isInnerAut_congr_centerDescend_iff (hq : 2 < p ^ f) {τ : MulAut (unitarySU p f K 3)} :
    IsInnerAut (MulAut.congr (suCenterEquiv h hq) (centerDescend _ τ)) ↔ IsInnerAut τ := by
  refine ⟨fun hτ => ?_, isInnerAut_congr_centerDescend _⟩
  have := isPerfect_unitarySU_three h hq
  exact isInnerAut_of_isInnerAut_centerDescend ((isInnerAut_congr _ _).mp hτ)

end Unitary

section Induced

variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

section Linear

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {K : Type*} [Field K] [Finite K]

theorem inducesKindSL_inner_iff (hn : 3 ≤ n)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* Matrix.SpecialLinearGroup (Fin n) K) (x : G) :
    InducesKindSL n K L x .inner ↔
      x ∈ Subgroup.normalizer (L : Set G) ∧ ¬ InducesOuterTheta x L := by
  rw [inducesKindSL_iff L hn e x .inner]
  constructor
  · rintro ⟨hx, hin⟩
    exact ⟨hx, fun hout => (not_isInnerAut_inducedAutHom_iff L e hx).mpr hout
      ((isInnerAut_descendAut_iff hn).mp hin)⟩
  · rintro ⟨hx, hout⟩
    refine ⟨hx, (isInnerAut_descendAut_iff hn).mpr ?_⟩
    by_contra hin
    exact hout ((not_isInnerAut_inducedAutHom_iff L e hx).mp hin)

theorem inducesKindSL_diagonal_or_field (hn : 3 ≤ n) {x : G} (hx3 : x ^ 3 = 1)
    (hout : InducesOuterTheta x L)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* Matrix.SpecialLinearGroup (Fin n) K) :
    InducesKindSL n K L x .diagonal ∨ InducesKindSL n K L x .field := by
  obtain ⟨hx, -⟩ := id hout
  have hin : ¬ IsInnerAut (descendAut n K (inducedAutHom L e ⟨x, hx⟩)) := fun hin =>
    (not_isInnerAut_inducedAutHom_iff L e hx).mpr hout ((isInnerAut_descendAut_iff hn).mp hin)
  rcases inducesKindSL_inner_or_diagonal_or_field L hn hx hx3 e with h | h | h
  · exact absurd h hin
  · exact Or.inl ⟨e, hx, h⟩
  · exact Or.inr ⟨e, hx, h⟩

end Linear

section Unitary

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem inducesKindSU3_inner_iff (hq : 2 < p ^ f)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* unitarySU p f K 3) (x : G) :
    InducesKindSU3 h L hq x .inner ↔
      x ∈ Subgroup.normalizer (L : Set G) ∧ ¬ InducesOuterTheta x L := by
  rw [inducesKindSU3_iff L hq e x .inner]
  constructor
  · rintro ⟨hx, hin⟩
    exact ⟨hx, fun hout => (not_isInnerAut_inducedAutHom_iff L e hx).mpr hout
      ((isInnerAut_congr_centerDescend_iff h hq).mp hin)⟩
  · rintro ⟨hx, hout⟩
    refine ⟨hx, (isInnerAut_congr_centerDescend_iff h hq).mpr ?_⟩
    by_contra hin
    exact hout ((not_isInnerAut_inducedAutHom_iff L e hx).mp hin)

theorem inducesKindSU3_diagonal_or_field (hq : 2 < p ^ f) {x : G} (hx3 : x ^ 3 = 1)
    (hout : InducesOuterTheta x L) (e : L ⧸ aschbacherSolvableCore 3 L ≃* unitarySU p f K 3) :
    InducesKindSU3 h L hq x .diagonal ∨ InducesKindSU3 h L hq x .field := by
  obtain ⟨hx, -⟩ := id hout
  have hin : ¬ IsInnerAut (MulAut.congr (suCenterEquiv h hq)
      (centerDescend _ (inducedAutHom L e ⟨x, hx⟩))) := fun hin =>
    (not_isInnerAut_inducedAutHom_iff L e hx).mpr hout
      ((isInnerAut_congr_centerDescend_iff h hq).mp hin)
  rcases inducesKindSU3_inner_or_diagonal_or_field (h := h) L hq hx hx3 e with h' | h' | h'
  · exact absurd h' hin
  · exact Or.inl ⟨e, hx, h'⟩
  · exact Or.inr ⟨e, hx, h'⟩

end Unitary

end Induced

end CFSG.RankThree.PartTwo.KFacts
