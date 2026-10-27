module

public import CFSG.Timmesfeld.ARS.CaseHMoufang

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

section Counts

theorem notMem_lambdaSet_self (x : Subgroup G) : x ∉ lambdaSet R x := fun hx => hx.1.2.1 rfl

theorem notMem_omegaSet_self (x : Subgroup G) : x ∉ omegaSet R x := fun hop => hop.2.1 rfl

theorem mem_psiSet_comm {x y : Subgroup G} (hx : x ∈ R) (hy : y ∈ psiSet R x) :
    x ∈ psiSet R y := ⟨hx, hy.2.symm⟩

theorem setOf_lambda_lambda_self {x : Subgroup G} (hx : x ∈ R) :
    {z | z ∈ lambdaSet R x ∧ x ∈ lambdaSet R z} = lambdaSet R x := by
  ext z
  exact ⟨fun hz => hz.1, fun hz => ⟨hz, mem_lambdaSet_comm hx hz⟩⟩

variable (h : Hyp G R)
include h

theorem notMem_psiSet_self {x : Subgroup G} (hx : x ∈ R) : x ∉ psiSet R x := fun hs =>
  Special.not_commuting h.root hs.2 (h.root.commuting_self hx)

theorem notMem_psiSet_of_mem_lambdaSet {x y : Subgroup G} (hy : y ∈ lambdaSet R x) :
    y ∉ psiSet R x := fun hs => Special.not_commuting h.root hs.2 hy.1.2.2

theorem notMem_omegaSet_of_mem_lambdaSet {x y : Subgroup G} (hx : x ∈ R)
    (hy : y ∈ lambdaSet R x) : y ∉ omegaSet R x := fun hop =>
  hop.2.not_commuting (h.root.ne_bot x hx) hy.1.2.2

theorem notMem_omegaSet_of_mem_psiSet {x y : Subgroup G} (hx : x ∈ R) (hy : y ∈ psiSet R x) :
    y ∉ omegaSet R x := fun hop => Special.not_opposite h.root hx hy.2 hop.2

theorem setOf_lambda_lambda_of_omega {x y : Subgroup G} (hx : x ∈ R) (hy : y ∈ omegaSet R x) :
    {z | z ∈ lambdaSet R x ∧ y ∈ lambdaSet R z} = ∅ := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hz hyz
  exact notMem_lambdaSet_of_opposite h hx hy.2 hz (mem_lambdaSet_comm hz.1.1 hyz)

theorem setOf_lambda_lambda_of_psi {x y : Subgroup G} (hx : x ∈ R) (hy : y ∈ psiSet R x) :
    {z | z ∈ lambdaSet R x ∧ y ∈ lambdaSet R z} = {⁅x, y⁆} := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hz, hyz⟩
    exact eq_commutator h hx hy.1 hy.2 hz (mem_lambdaSet_comm hz.1.1 hyz)
  · rintro rfl
    obtain ⟨h1, h2⟩ := commutator_mem_lambdaSet h hx hy.1 hy.2
    exact ⟨h1, mem_lambdaSet_comm hy.1 h2⟩

theorem setOf_lambda_psi_self {x : Subgroup G} (hx : x ∈ R) :
    {z | z ∈ lambdaSet R x ∧ x ∈ psiSet R z} = ∅ := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hz hxz
  exact notMem_psiSet_of_mem_lambdaSet h (mem_lambdaSet_comm hx hz) hxz

variable (hH : SigmaEqLambda R)
include hH

theorem eq_or_mem_of_mem {x y : Subgroup G} (hx : x ∈ R) (hy : y ∈ R) :
    y = x ∨ y ∈ lambdaSet R x ∨ y ∈ psiSet R x ∨ y ∈ omegaSet R x := by
  by_cases hyx : y = x
  · exact Or.inl hyx
  right
  rcases h.root.rel x hx y hy (Ne.symm hyx) with hc | hop | hs
  · exact Or.inl (mem_lambdaSet_of_commuting hH hx hy hyx hc)
  · exact Or.inr (Or.inr ⟨hy, hop⟩)
  · exact Or.inr (Or.inl ⟨hy, hs⟩)

theorem setOf_lambda_lambda_of_lambda {x y : Subgroup G} (hx : x ∈ R) (hy : y ∈ lambdaSet R x) :
    {z | z ∈ lambdaSet R x ∧ y ∈ lambdaSet R z} = pointsOn R (x ⊔ y) \ {x, y} := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hyR : y ∈ R := hy.1.1
  ext z
  constructor
  · rintro ⟨hz, hyz⟩
    have hzR : z ∈ R := hz.1.1
    refine ⟨⟨hzR, le_line h hH hx hy hx le_sup_left hyR le_sup_right hy.1.2.1.symm hzR
      hz.1.2.2.symm hyz.1.2.2⟩, ?_⟩
    rintro (rfl | rfl)
    · exact hz.1.2.1 rfl
    · exact hyz.1.2.1 rfl
  · rintro ⟨⟨hzR, hzle⟩, hzxy⟩
    have hzx : z ≠ x := fun e => hzxy (Or.inl e)
    have hzy : z ≠ y := fun e => hzxy (Or.inr e)
    exact ⟨(mem_lambdaSet_of_le_sup hR hiso hx hy hx le_sup_left hzR hzle (Ne.symm hzx)).1,
      (mem_lambdaSet_of_le_sup hR hiso hx hy hzR hzle hyR le_sup_right hzy).1⟩

theorem setOf_lambda_psi_of_lambda {x y : Subgroup G} (hx : x ∈ R) (hy : y ∈ lambdaSet R x) :
    {z | z ∈ lambdaSet R x ∧ y ∈ psiSet R z} = lambdaSet R x \ pointsOn R (y ⊔ x) := by
  rw [← setOf_psiSet_lambdaSet h hH hy.1.1 (mem_lambdaSet_comm hx hy)]
  ext z
  constructor
  · rintro ⟨hz, hyz⟩
    exact ⟨mem_psiSet_comm hz.1.1 hyz, hz⟩
  · rintro ⟨hzy, hz⟩
    exact ⟨hz, mem_psiSet_comm hy.1.1 hzy⟩

theorem setOf_lambda_psi_of_psi {x y : Subgroup G} (hx : x ∈ R) (hy : y ∈ psiSet R x) :
    {z | z ∈ lambdaSet R x ∧ y ∈ psiSet R z} = pointsOn R (x ⊔ ⁅y, x⁆) \ {x, ⁅y, x⁆} := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hyR : y ∈ R := hy.1
  have hxy : x ∈ psiSet R y := mem_psiSet_comm hx hy
  obtain ⟨hcy, hcx⟩ := commutator_mem_lambdaSet h hyR hx hxy.2
  have hcR : ⁅y, x⁆ ∈ R := hcx.1.1
  have hset := setOf_omegaSet_lambdaSet h hH hyR hxy
  ext z
  constructor
  · rintro ⟨hz, hyz⟩
    have hzy : z ∈ psiSet R y := mem_psiSet_comm hz.1.1 hyz
    have hzle : z ≤ x ⊔ ⁅y, x⁆ := by
      by_contra hnle
      have hmem : z ∈ lambdaSet R x \ pointsOn R (x ⊔ ⁅y, x⁆) := ⟨hz, fun hp => hnle hp.2⟩
      rw [← hset] at hmem
      exact notMem_omegaSet_of_mem_psiSet h hyR hzy hmem.1
    refine ⟨⟨hz.1.1, hzle⟩, ?_⟩
    rintro (rfl | rfl)
    · exact hz.1.2.1 rfl
    · exact notMem_psiSet_of_mem_lambdaSet h hcy hzy
  · rintro ⟨⟨hzR, hzle⟩, hzxc⟩
    have hzx : z ≠ x := fun e => hzxc (Or.inl e)
    have hzc : z ≠ ⁅y, x⁆ := fun e => hzxc (Or.inr e)
    have hzl : z ∈ lambdaSet R x :=
      (mem_lambdaSet_of_le_sup hR hiso hx hcx hx le_sup_left hzR hzle (Ne.symm hzx)).1
    have hzlc : z ∈ lambdaSet R ⁅y, x⁆ :=
      (mem_lambdaSet_of_le_sup hR hiso hx hcx hcR le_sup_right hzR hzle (Ne.symm hzc)).1
    have hzny : z ∉ lambdaSet R y := fun hzy => hzc (eq_commutator h hyR hx hxy.2 hzy hzl)
    have hzney : z ≠ y := by
      rintro rfl
      exact notMem_psiSet_of_mem_lambdaSet h hzl hy
    exact ⟨hzl, mem_psiSet_comm hyR ⟨hzR, (special_of_mem_lambdaSet h hH hyR hcy hzlc hzny
      hzney).1⟩⟩

omit hH in
theorem ncard_lambda_psi_of_omega {x y : Subgroup G} (hx : x ∈ R) (hy : y ∈ omegaSet R x) :
    {z | z ∈ lambdaSet R x ∧ y ∈ psiSet R z}.ncard = (linesThrough R x).ncard := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  refine Set.ncard_congr (fun z _ => x ⊔ z) (fun z hz => (mem_linesThrough_iff h hx).2
    ⟨z, hz.1, rfl⟩) (fun z z' hz hz' e => ?_) (fun V hV => ?_)
  · obtain ⟨D, -, huniq⟩ := existsUnique_mem_psiSet_of_le hR hiso hx hy.1 hy.2 hz.1
    refine (huniq z ⟨hz.1.1.1, le_sup_right, mem_psiSet_comm hz.1.1.1 hz.2⟩).trans
      (huniq z' ⟨hz'.1.1.1, ?_, mem_psiSet_comm hz'.1.1.1 hz'.2⟩).symm
    rw [e]
    exact le_sup_right
  · obtain ⟨D, hD, rfl⟩ := (mem_linesThrough_iff h hx).1 hV
    obtain ⟨D', ⟨hD'R, hD'le, hD'ψ⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hx hy.1 hy.2 hD
    have hD'x : x ≠ D' := by
      rintro rfl
      exact notMem_omegaSet_of_mem_psiSet h hy.1 hD'ψ (show x ∈ omegaSet R y from ⟨hx, hy.2.symm⟩)
    obtain ⟨hD'l, hline⟩ := mem_lambdaSet_of_le_sup hR hiso hx hD hx le_sup_left hD'R hD'le hD'x
    exact ⟨D', ⟨hD'l, mem_psiSet_comm hy.1 hD'ψ⟩, hline⟩

theorem ncard_lambda_lambda_of_lambda {x y : Subgroup G} (hx : x ∈ R) (hy : y ∈ lambdaSet R x) :
    {z | z ∈ lambdaSet R x ∧ y ∈ lambdaSet R z}.ncard = Nat.card x - 1 := by
  have := h.finite
  rw [setOf_lambda_lambda_of_lambda h hH hx hy, Set.ncard_sdiff (fun z hz => by
      rcases hz with rfl | rfl
      exacts [⟨hx, le_sup_left⟩, ⟨hy.1.1, le_sup_right⟩]),
    ncard_pointsOn h hx hy, Set.ncard_pair hy.1.2.1.symm]
  omega

theorem ncard_lambda_psi_of_psi {x y : Subgroup G} (hx : x ∈ R) (hy : y ∈ psiSet R x) :
    {z | z ∈ lambdaSet R x ∧ y ∈ psiSet R z}.ncard = Nat.card x - 1 := by
  have := h.finite
  obtain ⟨-, hcx⟩ := commutator_mem_lambdaSet h hy.1 hx (mem_psiSet_comm hx hy).2
  rw [setOf_lambda_psi_of_psi h hH hx hy, Set.ncard_sdiff (fun z hz => by
      rcases hz with rfl | rfl
      exacts [⟨hx, le_sup_left⟩, ⟨hcx.1.1, le_sup_right⟩]),
    ncard_pointsOn h hx hcx, Set.ncard_pair hcx.1.2.1.symm]
  omega

theorem ncard_lambda_psi_of_lambda {x y : Subgroup G} (hx : x ∈ R) (hy : y ∈ lambdaSet R x) :
    {z | z ∈ lambdaSet R x ∧ y ∈ psiSet R z}.ncard = (lambdaSet R x).ncard - Nat.card x := by
  rw [setOf_lambda_psi_of_lambda h hH hx hy, ncard_lambdaSet_diff_pointsOn h hy.1.1
    (mem_lambdaSet_comm hx hy), ncard_lambdaSet_eq h.root hy.1.1 hx, h.root.card_eq hy.1.1 hx]

end Counts

section Matrices

open Matrix

theorem card_filter_eq_ncard [Fintype R] (P : Subgroup G → Prop) [DecidablePred fun z : R => P z.1]
    (hP : ∀ B, P B → B ∈ R) :
    (Finset.univ.filter fun z : R => P z.1).card = {B | P B}.ncard := by
  rw [← Set.ncard_coe_finset]
  have e : {B | P B} = Subtype.val '' (↑(Finset.univ.filter fun z : R => P z.1) : Set R) := by
    ext B
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_image,
      Subtype.exists, exists_and_right, exists_eq_right]
    exact ⟨fun hB => ⟨hP B hB, hB⟩, fun ⟨_, hB⟩ => hB⟩
  rw [e, Set.ncard_image_of_injective _ Subtype.val_injective]

open scoped Classical in
noncomputable def collMat (R : Set (Subgroup G)) : Matrix R R ℚ :=
  Matrix.of fun x y => if y.1 ∈ lambdaSet R x.1 then 1 else 0

open scoped Classical in
noncomputable def psiMat (R : Set (Subgroup G)) : Matrix R R ℚ :=
  Matrix.of fun x y => if y.1 ∈ psiSet R x.1 then 1 else 0

theorem collMat_apply (x y : R) [Decidable (y.1 ∈ lambdaSet R x.1)] :
    collMat R x y = if y.1 ∈ lambdaSet R x.1 then 1 else 0 := by
  simp only [collMat, Matrix.of_apply]
  congr

theorem psiMat_apply (x y : R) [Decidable (y.1 ∈ psiSet R x.1)] :
    psiMat R x y = if y.1 ∈ psiSet R x.1 then 1 else 0 := by
  simp only [psiMat, Matrix.of_apply]
  congr

theorem collMat_mul_collMat_apply [Fintype R] (x y : R) :
    (collMat R * collMat R) x y = ({z | z ∈ lambdaSet R x.1 ∧ y.1 ∈ lambdaSet R z}.ncard : ℚ) := by
  classical
  rw [Matrix.mul_apply]
  simp only [collMat_apply, ite_zero_mul_ite_zero, mul_one]
  rw [Finset.sum_boole, card_filter_eq_ncard (fun z => z ∈ lambdaSet R x.1 ∧ y.1 ∈ lambdaSet R z)
    fun B hB => hB.1.1.1]

theorem collMat_mul_psiMat_apply [Fintype R] (x y : R) :
    (collMat R * psiMat R) x y = ({z | z ∈ lambdaSet R x.1 ∧ y.1 ∈ psiSet R z}.ncard : ℚ) := by
  classical
  rw [Matrix.mul_apply]
  simp only [collMat_apply, psiMat_apply, ite_zero_mul_ite_zero, mul_one]
  rw [Finset.sum_boole, card_filter_eq_ncard (fun z => z ∈ lambdaSet R x.1 ∧ y.1 ∈ psiSet R z)
    fun B hB => hB.1.1.1]

theorem collMat_mul_one_apply [Fintype R] (x y : R) :
    (collMat R * (Matrix.of fun _ _ => (1 : ℚ) : Matrix R R ℚ)) x y =
      ((lambdaSet R x.1).ncard : ℚ) := by
  classical
  rw [Matrix.mul_apply]
  simp only [collMat_apply, Matrix.of_apply, mul_one]
  rw [Finset.sum_boole, card_filter_eq_ncard (fun z => z ∈ lambdaSet R x.1) fun B hB => hB.1.1]
  rfl

theorem false_of_relations {n : Type*} [Fintype n] [DecidableEq n] (A A₂ J : Matrix n n ℚ)
    (h1 : A * A = (10 : ℕ) • (1 : Matrix n n ℚ) + A + A₂)
    (h2 : A * A₂ = (8 : ℕ) • A + A₂ + (5 : ℕ) • (J - 1 - A - A₂))
    (h3 : A * J = (10 : ℕ) • J) (htA : A.trace = 0) (htA₂ : A₂.trace = 0)
    (htJ : J.trace = 219) (hcard : Fintype.card n = 219) : False := by
  have hA₂ : A₂ = A * A - (10 : ℕ) • (1 : Matrix n n ℚ) - A := by rw [h1]; abel
  have h5J : (5 : ℕ) • J =
      A * A * A + (3 : ℕ) • (A * A) - (17 : ℕ) • A - (35 : ℕ) • (1 : Matrix n n ℚ) := by
    have e : (5 : ℕ) • J =
        A * A₂ - (3 : ℕ) • A + (4 : ℕ) • A₂ + (5 : ℕ) • (1 : Matrix n n ℚ) := by
      rw [h2]; abel
    rw [e, hA₂]
    noncomm_ring
  have hp : A * A * A * A - (7 : ℕ) • (A * A * A) - (47 : ℕ) • (A * A) + (135 : ℕ) • A +
      (350 : ℕ) • (1 : Matrix n n ℚ) = 0 := by
    have e : (A - (10 : ℕ) • (1 : Matrix n n ℚ)) * ((5 : ℕ) • J) = 0 := by
      rw [sub_mul, smul_mul_assoc, Matrix.one_mul, mul_smul_comm, h3, smul_comm, sub_self]
    rw [h5J] at e
    rw [← e]
    noncomm_ring
  set E := A * A * A - (12 : ℕ) • (A * A) + (13 : ℕ) • A + (70 : ℕ) • (1 : Matrix n n ℚ) with hE
  have hEE : E * E = (-420 : ℚ) • E := by
    have e : E * E + (420 : ℕ) • E = (A * A * A * A - (7 : ℕ) • (A * A * A) -
        (47 : ℕ) • (A * A) + (135 : ℕ) • A + (350 : ℕ) • (1 : Matrix n n ℚ)) *
        (A * A - (17 : ℕ) • A + (98 : ℕ) • (1 : Matrix n n ℚ)) := by
      rw [hE]; noncomm_ring
    rw [hp, zero_mul] at e
    rw [eq_neg_of_add_eq_zero_left e, neg_smul, ← Nat.cast_smul_eq_nsmul ℚ]
    norm_num
  set F := (-1 / 420 : ℚ) • E with hF
  have hFF : F * F = F := by
    rw [hF, smul_mul_smul_comm, hEE, smul_smul]
    norm_num
  have htAA : (A * A).trace = 2190 := by
    rw [h1, trace_add, trace_add, trace_smul, trace_one, htA, htA₂, hcard]
    norm_num
  have htAAA : (A * A * A).trace = 2190 := by
    have e : A * A * A = (5 : ℕ) • J - (3 : ℕ) • (A * A) + (17 : ℕ) • A +
        (35 : ℕ) • (1 : Matrix n n ℚ) := by
      rw [h5J]; abel
    rw [e, trace_add, trace_add, trace_sub, trace_smul, trace_smul, trace_smul, trace_smul,
      trace_one, htJ, htAA, htA, hcard]
    norm_num
  have htF : F.trace = 146 / 7 := by
    rw [hF, trace_smul, hE, trace_add, trace_add, trace_sub, trace_smul, trace_smul, trace_smul,
      trace_one, htAAA, htAA, htA, hcard]
    norm_num
  have hidem : IsIdempotentElem (Matrix.toLin' F) := by
    change Matrix.toLin' F * Matrix.toLin' F = Matrix.toLin' F
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hFF]
  have htr := (LinearMap.IsIdempotentElem.isProj_range _ hidem).trace
  rw [Matrix.trace_toLin'_eq, htF] at htr
  have h7 : (7 * Module.finrank ℚ (LinearMap.range (Matrix.toLin' F)) : ℚ) = 146 := by
    rw [← htr]; norm_num
  norm_cast at h7
  omega

end Matrices

theorem ncard_linesThrough_ne_five (h : Hyp G R) (hH : SigmaEqLambda R) {A : Subgroup G}
    (hA : A ∈ R) (hq : Nat.card A = 2) : (linesThrough R A).ncard ≠ 5 := by
  classical
  intro hL
  have := h.finite
  have hR := h.root
  have : Fintype R := Fintype.ofFinite _
  have hq' : ∀ x ∈ R, Nat.card x = 2 := fun x hx => (hR.card_eq hx hA).trans hq
  have hL' : ∀ x ∈ R, (linesThrough R x).ncard = 5 := fun x hx =>
    (ncard_linesThrough_eq h hA hx).trans hL
  have hΛ : ∀ x ∈ R, (lambdaSet R x).ncard = 10 := fun x hx => by
    rw [ncard_lambdaSet h hx, hL' x hx, hq' x hx]
  have hcard : Fintype.card R = 219 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, ncard_eq h hH hA hq hL]
    norm_num
  set J : Matrix R R ℚ := Matrix.of fun _ _ => 1 with hJ
  refine false_of_relations (collMat R) (psiMat R) J ?_ ?_ ?_ ?_ ?_ ?_ hcard
  ·
    ext x y
    rw [collMat_mul_collMat_apply, Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, collMat_apply, psiMat_apply]
    rcases eq_or_mem_of_mem h hH x.2 y.2 with hxy | hxy | hxy | hxy
    · have hxy' : x = y := (Subtype.ext hxy).symm
      subst hxy'
      rw [setOf_lambda_lambda_self x.2, hΛ x.1 x.2, ite_eq_left rfl,
        ite_eq_right (notMem_lambdaSet_self x.1), ite_eq_right (notMem_psiSet_self h x.2)]
      norm_num
    · have hne : x ≠ y := fun e => notMem_lambdaSet_self (R := R) y.1 (e ▸ hxy)
      rw [ncard_lambda_lambda_of_lambda h hH x.2 hxy, hq' x.1 x.2, ite_eq_right hne, ite_eq_left hxy,
        ite_eq_right (notMem_psiSet_of_mem_lambdaSet h hxy)]
      norm_num
    · have hne : x ≠ y := fun e => notMem_psiSet_self h x.2 (e ▸ hxy)
      rw [setOf_lambda_lambda_of_psi h x.2 hxy, Set.ncard_singleton, ite_eq_right hne,
        ite_eq_right fun hl => notMem_psiSet_of_mem_lambdaSet h hl hxy, ite_eq_left hxy]
      norm_num
    · have hne : x ≠ y := fun e => notMem_omegaSet_self (R := R) y.1 (e ▸ hxy)
      rw [setOf_lambda_lambda_of_omega h x.2 hxy, Set.ncard_empty, ite_eq_right hne,
        ite_eq_right fun hl => notMem_omegaSet_of_mem_lambdaSet h x.2 hl hxy,
        ite_eq_right fun hs => notMem_omegaSet_of_mem_psiSet h x.2 hs hxy]
      norm_num
  ·
    ext x y
    rw [collMat_mul_psiMat_apply, Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.smul_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply,
      collMat_apply, psiMat_apply, hJ, Matrix.of_apply]
    rcases eq_or_mem_of_mem h hH x.2 y.2 with hxy | hxy | hxy | hxy
    · have hxy' : x = y := (Subtype.ext hxy).symm
      subst hxy'
      rw [setOf_lambda_psi_self h x.2, Set.ncard_empty, ite_eq_left rfl,
        ite_eq_right (notMem_lambdaSet_self x.1), ite_eq_right (notMem_psiSet_self h x.2)]
      norm_num
    · have hne : x ≠ y := fun e => notMem_lambdaSet_self (R := R) y.1 (e ▸ hxy)
      rw [ncard_lambda_psi_of_lambda h hH x.2 hxy, hΛ x.1 x.2, hq' x.1 x.2, ite_eq_right hne,
        ite_eq_left hxy, ite_eq_right (notMem_psiSet_of_mem_lambdaSet h hxy)]
      norm_num
    · have hne : x ≠ y := fun e => notMem_psiSet_self h x.2 (e ▸ hxy)
      rw [ncard_lambda_psi_of_psi h hH x.2 hxy, hq' x.1 x.2, ite_eq_right hne,
        ite_eq_right fun hl => notMem_psiSet_of_mem_lambdaSet h hl hxy, ite_eq_left hxy]
      norm_num
    · have hne : x ≠ y := fun e => notMem_omegaSet_self (R := R) y.1 (e ▸ hxy)
      rw [ncard_lambda_psi_of_omega h x.2 hxy, hL' x.1 x.2, ite_eq_right hne,
        ite_eq_right fun hl => notMem_omegaSet_of_mem_lambdaSet h x.2 hl hxy,
        ite_eq_right fun hs => notMem_omegaSet_of_mem_psiSet h x.2 hs hxy]
      norm_num
  ·
    ext x y
    rw [hJ, collMat_mul_one_apply, Matrix.smul_apply, Matrix.of_apply, hΛ x.1 x.2]
    norm_num
  ·
    rw [Matrix.trace]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Matrix.diag_apply, collMat_apply, ite_eq_right (notMem_lambdaSet_self x.1)]
  ·
    rw [Matrix.trace]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Matrix.diag_apply, psiMat_apply, ite_eq_right (notMem_psiSet_self h x.2)]
  ·
    rw [Matrix.trace, hJ]
    simp only [Matrix.diag_apply, Matrix.of_apply, Finset.sum_const, Finset.card_univ, hcard]
    norm_num

end CaseH

end CFSG.Timmesfeld.ARS
