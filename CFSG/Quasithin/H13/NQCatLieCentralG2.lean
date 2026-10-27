module

public import CFSG.Quasithin.H13.NQCatLieCentralCore
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieG2Facts

public section

namespace CFSG.Quasithin.H13.NQCat.LieCentral.G2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
open scoped commutatorElement

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem gX_mem_posUnipotent
    {d : Fin Tag.G2.rank → ℤ} (hd : d = rA ∨ d = rR ∨ d = rU ∨ d = rV ∨ d = rB ∨ d = rC) (c : K) :
    gX d c ∈ posUnipotent Tag.G2 K :=
  pinnedX_mem_rootSpan (S := {α | IsRoot Tag.G2 α ∧ 0 < height α}) (isRoot_pos_iff.2 hd) c

omit [CharP K 2] in
theorem exists_eq_prod_of_mem_posUnipotent
    {x : ModGL Tag.G2 K} (hx : x ∈ posUnipotent Tag.G2 K) :
    ∃ a r u v b c : K,
      x = gX rA a * (gX rR r * (gX rU u * (gX rV v * (gX rB b * gX rC c)))) := by
  have hinj : Function.Injective ![rA, rR, rU, rV, rB, rC] := by decide
  have hpos : ∀ α ∈ {α : Fin Tag.G2.rank → ℤ | IsRoot Tag.G2 α ∧ 0 < height α},
      IsRoot Tag.G2 α ∧ 0 < height α := fun α hα => hα
  have hclosed : ∀ α ∈ {α : Fin Tag.G2.rank → ℤ | IsRoot Tag.G2 α ∧ 0 < height α},
      ∀ β ∈ {α : Fin Tag.G2.rank → ℤ | IsRoot Tag.G2 α ∧ 0 < height α}, ∀ a b : ℕ,
        1 ≤ a → 1 ≤ b → IsRoot Tag.G2 (a • α + b • β) →
          a • α + b • β ∈ {α : Fin Tag.G2.rank → ℤ | IsRoot Tag.G2 α ∧ 0 < height α} := by
    intro α hα β hβ a b ha hb hr
    refine ⟨hr, ?_⟩
    have h1 : height (a • α + b • β) = a * height α + b * height β := by
      simp only [height, Pi.add_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply,
        Finset.sum_add_distrib, Finset.mul_sum]
    rw [h1]
    have := hα.2
    have := hβ.2
    positivity
  have hrange : Set.range ![rA, rR, rU, rV, rB, rC] =
      {α : Fin Tag.G2.rank → ℤ | IsRoot Tag.G2 α ∧ 0 < height α} := by
    ext α
    simp only [Set.mem_range, Set.mem_ofPred_eq, isRoot_pos_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩]
  obtain ⟨t, -, ht⟩ := (bijOn_prod_pinnedX K hpos hclosed ![rA, rR, rU, rV, rB, rC] hinj
    hrange).surjOn hx
  refine ⟨t 0, t 1, t 2, t 3, t 4, t 5, ?_⟩
  rw [← ht]
  simp [List.ofFn_succ]

theorem conj_A_B
    (x y : K) :
    MulAut.conj (gX rA x) (gX rB y) = gX rC (x * y) * gX rB y :=
  conj_eq_of_commutator (rel_ab x y)

theorem conj_R_V
    (x y : K) :
    MulAut.conj (gX rR x) (gX rV y) = gX rB (x * y) * gX rV y :=
  conj_eq_of_commutator (rel_rv x y)

theorem conj_U_V
    (x y : K) :
    MulAut.conj (gX rU x) (gX rV y) = gX rC (x * y) * gX rV y :=
  conj_eq_of_commutator (rel_uv x y)

theorem conj_V_U
    (x y : K) :
    MulAut.conj (gX rV x) (gX rU y) = gX rC (y * x) * gX rU y := by
  rw [conj_eq_of_commutator' (rel_uv y x), gX_inv]

theorem conj_B_A
    (x y : K) :
    MulAut.conj (gX rB x) (gX rA y) = gX rC (y * x) * gX rA y := by
  rw [conj_eq_of_commutator' (rel_ab y x), gX_inv]

theorem a_eq_zero_of_commute
    {a r u v b c y : K} (hy : y ≠ 0)
    (h : gX rB y * (gX rA a * (gX rR r * (gX rU u * (gX rV v * (gX rB b * gX rC c))))) =
      gX rA a * (gX rR r * (gX rU u * (gX rV v * (gX rB b * gX rC c)))) * gX rB y) :
    a = 0 := by
  have hw : Commute (gX rR r * (gX rU u * (gX rV v * (gX rB b * gX rC c)))) (gX rB y) :=
    (comm_rb r y).mul_left ((comm_ub u y).mul_left ((comm_vb v y).mul_left
      ((gX_comm_self rB b y).mul_left (comm_bc y c).symm)))
  have h1 : MulAut.conj (gX rA a * (gX rR r * (gX rU u * (gX rV v * (gX rB b * gX rC c)))))
      (gX rB y) = gX rB y := by
    rw [MulAut.conj_apply, ← h, mul_inv_cancel_right]
  rw [map_mul, MulAut.mul_apply, conj_eq_of_commute hw, conj_A_B] at h1
  exact (mul_eq_zero.1 (gX_eq_one (mul_eq_right.1 h1))).resolve_right hy

theorem r_eq_zero_of_commute
    {a r u v b c y : K} (hy : y ≠ 0)
    (h : gX rV y * (gX rA a * (gX rR r * (gX rU u * (gX rV v * (gX rB b * gX rC c))))) =
      gX rA a * (gX rR r * (gX rU u * (gX rV v * (gX rB b * gX rC c)))) * gX rV y) :
    r = 0 ∧ u = 0 := by
  have hw : Commute (gX rV v * (gX rB b * gX rC c)) (gX rV y) :=
    (gX_comm_self rV v y).mul_left ((comm_vb y b).symm.mul_left (comm_vc y c).symm)
  have h1 : MulAut.conj (gX rA a * (gX rR r * (gX rU u * (gX rV v * (gX rB b * gX rC c)))))
      (gX rV y) = gX rV y := by
    rw [MulAut.conj_apply, ← h, mul_inv_cancel_right]
  rw [map_mul, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply,
    conj_eq_of_commute hw, conj_U_V, map_mul, conj_eq_of_commute (comm_rc r (u * y)),
    conj_R_V, map_mul, map_mul, conj_eq_of_commute (comm_ac a (u * y)), conj_A_B,
    conj_eq_of_commute (comm_av a y)] at h1
  have h3' : gX rC (u * y) * (gX rC (a * (r * y)) * gX rB (r * y)) * gX rV y = gX rV y := by
    calc gX rC (u * y) * (gX rC (a * (r * y)) * gX rB (r * y)) * gX rV y =
        gX rC (u * y) * (gX rC (a * (r * y)) * gX rB (r * y) * gX rV y) := by group
      _ = gX rV y := h1
  have h3 := mul_eq_right.1 h3'
  have h2 : gX rB (r * y) * gX rC (u * y + a * (r * y)) = 1 := by
    rw [gX_add]
    calc gX rB (r * y) * (gX rC (u * y) * gX rC (a * (r * y))) =
        gX rC (u * y) * (gX rC (a * (r * y)) * gX rB (r * y)) := by
          rw [← mul_assoc, (comm_bc _ _).eq, mul_assoc, (comm_bc _ _).eq]
      _ = 1 := h3
  obtain ⟨h4, h5⟩ := prod_bc_eq_one h2
  have hr : r = 0 := (mul_eq_zero.1 h4).resolve_right hy
  subst hr
  simp only [zero_mul, mul_zero, add_zero] at h5
  exact ⟨rfl, (mul_eq_zero.1 h5).resolve_right hy⟩

theorem v_eq_zero_of_commute
    {a u v b c y : K} (hy : y ≠ 0)
    (h : gX rU y * (gX rA a * (gX rU u * (gX rV v * (gX rB b * gX rC c)))) =
      gX rA a * (gX rU u * (gX rV v * (gX rB b * gX rC c))) * gX rU y) :
    v = 0 := by
  have hw : Commute (gX rB b * gX rC c) (gX rU y) :=
    (comm_ub y b).symm.mul_left (comm_uc y c).symm
  have h1 : MulAut.conj (gX rA a * (gX rU u * (gX rV v * (gX rB b * gX rC c))))
      (gX rU y) = gX rU y := by
    rw [MulAut.conj_apply, ← h, mul_inv_cancel_right]
  rw [map_mul, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply,
    conj_eq_of_commute hw, conj_V_U, map_mul, conj_eq_of_commute (comm_uc u (y * v)),
    conj_eq_of_commute (gX_comm_self rU u y), map_mul, conj_eq_of_commute (comm_ac a (y * v)),
    conj_eq_of_commute (comm_au a y)] at h1
  have h2 := gX_eq_one (mul_eq_right.1 h1)
  exact (mul_eq_zero.1 h2).resolve_left hy

theorem b_eq_zero_of_commute
    {a b c y : K} (hy : y ≠ 0)
    (h : gX rA y * (gX rA a * (gX rB b * gX rC c)) =
      gX rA a * (gX rB b * gX rC c) * gX rA y) :
    b = 0 := by
  have h1 : MulAut.conj (gX rA a * (gX rB b * gX rC c)) (gX rA y) = gX rA y := by
    rw [MulAut.conj_apply, ← h, mul_inv_cancel_right]
  rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply,
    conj_eq_of_commute (comm_ac y c).symm, conj_B_A, map_mul,
    conj_eq_of_commute (comm_ac a (y * b)), conj_eq_of_commute (gX_comm_self rA a y)] at h1
  have h2 := gX_eq_one (mul_eq_right.1 h1)
  exact (mul_eq_zero.1 h2).resolve_left hy

theorem gX_rC_mem_centralizer
    (c : K) :
    gX rC c ∈ Subgroup.centralizer (posUnipotent Tag.G2 K : Set (ModGL Tag.G2 K)) := by
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  obtain ⟨a, r, u, v, b, c', rfl⟩ := exists_eq_prod_of_mem_posUnipotent hy
  have hc : Commute (gX rA a * (gX rR r * (gX rU u * (gX rV v * (gX rB b * gX rC c')))))
      (gX rC c) :=
    (comm_ac a c).mul_left ((comm_rc r c).mul_left ((comm_uc u c).mul_left
      ((comm_vc v c).mul_left ((comm_bc b c).mul_left (gX_comm_self rC c' c)))))
  exact hc.eq

theorem centralIndex_g2
    [Finite K] (hK : 4 ≤ Nat.card K) :
    CentralIndex ↥(adjointGroup Tag.G2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hUC : posUnipotent Tag.G2 K ≤ adjointGroup Tag.G2 K := posUnipotent_le_adjointGroup
  have hU : IsSylowTwoOf (posUnipotent Tag.G2 K) (adjointGroup Tag.G2 K) :=
    isSylowTwoOf_iff_isSylowOf.2 (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1
  refine centralIndex_of_le hUC hU fun x hx hidx => ?_
  let ψ : (Fin Tag.G2.rank → ℤ) → Multiplicative K →* ModGL Tag.G2 K := fun d =>
    { toFun := fun t => gX d (Multiplicative.toAdd t)
      map_one' := gX_zero d
      map_mul' := fun s t => gX_add d _ _ }
  have hψ : ∀ d, Function.Injective (ψ d) := fun d s t hst =>
    Multiplicative.toAdd.injective (pinnedX_injective Tag.G2 K d hst)
  have hcomm : ∀ d, (d = rA ∨ d = rR ∨ d = rU ∨ d = rV ∨ d = rB ∨ d = rC) →
      ∃ y : K, y ≠ 0 ∧ gX d y * x = x * gX d y := fun d hd =>
    exists_ne_zero_commute_of_hom (P := posUnipotent Tag.G2 K) (ψ d) (hψ d)
      (fun t => gX_mem_posUnipotent hd _) (by omega) hidx
  obtain ⟨a, r, u, v, b, c, rfl⟩ := exists_eq_prod_of_mem_posUnipotent hx
  obtain ⟨yB, hyB, hB⟩ := hcomm rB (by simp)
  have ha := a_eq_zero_of_commute hyB hB
  obtain ⟨yV, hyV, hV⟩ := hcomm rV (by simp)
  obtain ⟨hr, hu⟩ := r_eq_zero_of_commute hyV hV
  subst ha hr hu
  simp only [gX_zero, one_mul] at *
  obtain ⟨yU, hyU, hU'⟩ := hcomm rU (by simp)
  have hv := v_eq_zero_of_commute (a := 0) (u := 0) hyU (by simpa [gX_zero] using hU')
  subst hv
  simp only [gX_zero, one_mul] at *
  obtain ⟨yA, hyA, hA⟩ := hcomm rA (by simp)
  have hb := b_eq_zero_of_commute (a := 0) hyA (by simpa [gX_zero] using hA)
  subst hb
  simp only [gX_zero, one_mul]
  exact gX_rC_mem_centralizer c

end CFSG.Quasithin.H13.NQCat.LieCentral.G2
