module

public import CFSG.RankThree.Coprime.SolvableFixedCommutator
public import CFSG.RankThree.GroupTheory.SteinbergCDCentralizerCoreIntersection

public section

namespace CFSG.RankThree.GroupTheory

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped IsMulCommutative

section Norm

variable {B H : Type*} [Group B] [Group H] [MulDistribMulAction B H]

theorem smul_mem_center_of_mem_center (b : B) {z : H} (hz : z ∈ center H) :
    b • z ∈ center H := by
  rw [mem_center_iff] at hz ⊢
  intro g
  calc g * (b • z) = b • ((b⁻¹ • g) * z) := by rw [smul_mul', smul_inv_smul]
    _ = b • (z * (b⁻¹ • g)) := by rw [hz]
    _ = (b • z) * g := by rw [smul_mul', smul_inv_smul]

@[expose] def centralNormFactor {z : H} (hz : z ∈ center H) (b : B) : center H :=
  ⟨b • z, smul_mem_center_of_mem_center b hz⟩

variable (B) [Fintype B]

open _root_.Classical in
noncomputable def centralNorm (z : H) : H :=
  if hz : z ∈ center H then (((∏ b : B, centralNormFactor hz b) : center H) : H) else 1

variable {B}

theorem centralNorm_of_mem {z : H} (hz : z ∈ center H) :
    centralNorm B z = (((∏ b : B, centralNormFactor hz b) : center H) : H) := by
  rw [centralNorm, dite_eq_left_of_eq_true (eq_true hz)]

theorem centralNorm_mul {z w : H} (hz : z ∈ center H) (hw : w ∈ center H) :
    centralNorm B (z * w) = centralNorm B z * centralNorm B w := by
  rw [centralNorm_of_mem (mul_mem hz hw), centralNorm_of_mem hz, centralNorm_of_mem hw,
    ← Subgroup.coe_mul, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun b _ => Subtype.ext ?_
  simp [centralNormFactor, smul_mul']

theorem centralNorm_one : centralNorm B (1 : H) = 1 := by
  have h := centralNorm_mul (B := B) (one_mem (center H)) (one_mem (center H))
  rw [mul_one] at h
  exact left_eq_mul.mp h

theorem centralNorm_inv {z : H} (hz : z ∈ center H) :
    centralNorm B z⁻¹ = (centralNorm B z)⁻¹ := by
  have h := centralNorm_mul (B := B) (inv_mem hz) hz
  rw [inv_mul_cancel, centralNorm_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem centralNorm_smul (b : B) {z : H} (hz : z ∈ center H) :
    centralNorm B (b • z) = centralNorm B z := by
  rw [centralNorm_of_mem (smul_mem_center_of_mem_center b hz), centralNorm_of_mem hz]
  congr 1
  exact Fintype.prod_equiv (Equiv.mulRight b) _ _ fun a => Subtype.ext (by
    simp [centralNormFactor, mul_smul])

theorem centralNorm_inv_mul_smul (b : B) {z : H} (hz : z ∈ center H) :
    centralNorm B (z⁻¹ * (b • z)) = 1 := by
  rw [centralNorm_mul (inv_mem hz) (smul_mem_center_of_mem_center b hz), centralNorm_inv hz,
    centralNorm_smul b hz, inv_mul_cancel]

theorem smul_centralNorm (a : B) (z : H) : a • centralNorm B z = centralNorm B z := by
  by_cases hz : z ∈ center H
  · rw [centralNorm_of_mem hz]
    let φ : center H →* center H :=
      { toFun := fun w => ⟨a • (w : H), smul_mem_center_of_mem_center a w.2⟩
        map_one' := Subtype.ext (smul_one a)
        map_mul' := fun w w' => Subtype.ext (smul_mul' a (w : H) w') }
    have h1 : a • (((∏ b : B, centralNormFactor hz b) : center H) : H) =
        ((φ (∏ b : B, centralNormFactor hz b)) : H) := rfl
    rw [h1, map_prod]
    congr 1
    exact Fintype.prod_equiv (Equiv.mulLeft a) _ _ fun b => Subtype.ext (by
      simp [φ, centralNormFactor, mul_smul])
  · rw [centralNorm, dite_eq_right_of_eq_false (eq_false hz), smul_one]

theorem centralNorm_of_fixed {z : H} (hz : z ∈ center H) (hfix : ∀ b : B, b • z = z) :
    centralNorm B z = z ^ Fintype.card B := by
  rw [centralNorm_of_mem hz]
  have h : ∀ b : B, centralNormFactor hz b = ⟨z, hz⟩ := fun b => Subtype.ext (hfix b)
  simp only [h, Finset.prod_const, Finset.card_univ, Subgroup.coe_pow]

theorem centralNorm_mem {S : Subgroup H} (hS : ∀ b : B, ∀ x ∈ S, b • x ∈ S) {z : H} (hzS : z ∈ S) :
    centralNorm B z ∈ S := by
  by_cases hz : z ∈ center H
  · rw [centralNorm_of_mem hz]
    have hmem : (∏ b : B, centralNormFactor hz b) ∈ S.comap (center H).subtype :=
      prod_mem fun b _ => hS b z hzS
    exact hmem
  · rw [centralNorm, dite_eq_right_of_eq_false (eq_false hz)]
    exact one_mem S

omit [Fintype B] in
theorem centralNorm_smul_mul_inv [Fintype B] (b : B) {z : H} (hz : z ∈ center H) :
    centralNorm B ((b • z) * z⁻¹) = 1 := by
  rw [centralNorm_mul (smul_mem_center_of_mem_center b hz) (inv_mem hz), centralNorm_inv hz,
    centralNorm_smul b hz, mul_inv_cancel]

end Norm

section Commutators

variable {H : Type*} [Group H]

open scoped commutatorElement

theorem commutatorElement_mul_left_of_mem_center {y y' h : H} (hc : ⁅y', h⁆ ∈ center H) :
    ⁅y * y', h⁆ = ⁅y', h⁆ * ⁅y, h⁆ := by
  have e : ⁅y * y', h⁆ = y * ⁅y', h⁆ * (h * y⁻¹ * h⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e, (mem_center_iff.mp hc y), commutatorElement_def, commutatorElement_def]
  group

theorem commutatorElement_mul_right_of_mem_center {y h h' : H} (hc : ⁅y, h'⁆ ∈ center H) :
    ⁅y, h * h'⁆ = ⁅y, h⁆ * ⁅y, h'⁆ := by
  have e : ⁅y, h * h'⁆ = y * h * y⁻¹ * ⁅y, h'⁆ * h⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e, mul_assoc (y * h * y⁻¹), (mem_center_iff.mp hc h⁻¹).symm, commutatorElement_def,
    commutatorElement_def]
  group

theorem commutatorElement_inv_left_of_mem_center {y h : H} (hc : ⁅y, h⁆ ∈ center H) :
    ⁅y⁻¹, h⁆ = ⁅y, h⁆⁻¹ := by
  have h1 := commutatorElement_mul_left_of_mem_center (y := y⁻¹) (y' := y) (h := h) hc
  rw [inv_mul_cancel, commutatorElement_one_left] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

theorem commutatorElement_inv_right_of_mem_center {y h : H} (hc : ⁅y, h⁆ ∈ center H) :
    ⁅y, h⁻¹⁆ = ⁅y, h⁆⁻¹ := by
  have h1 := commutatorElement_mul_right_of_mem_center (y := y) (h := h⁻¹) (h' := h) hc
  rw [inv_mul_cancel, commutatorElement_one_right] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

theorem smul_commutatorElement {B : Type*} [Group B] [MulDistribMulAction B H] (b : B)
    (y h : H) : b • ⁅y, h⁆ = ⁅b • y, b • h⁆ := by
  simp only [commutatorElement_def, smul_mul', smul_inv']

end Commutators

section Action

variable {p : ℕ} [Fact p.Prime] {B : Type*} [Group B] [Finite B] [IsElementaryAbelian p B]
  {H : Type*} [Group H] [MulDistribMulAction B H]

omit [Fact p.Prime] [Finite B] [IsElementaryAbelian p B] in
theorem mem_fixedPointSubgroup_subgroup_iff (D : Subgroup B) (x : H) :
    x ∈ fixedPointSubgroup D H ↔ ∀ d ∈ D, d • x = x :=
  ⟨fun h d hd => h ⟨d, hd⟩, fun h d => h d d.2⟩

omit [Fact p.Prime] [Finite B] [IsElementaryAbelian p B] in
theorem smul_mem_fixedPointSubgroup [IsMulCommutative B] (D : Subgroup B) (b : B) {x : H}
    (hx : x ∈ fixedPointSubgroup D H) : b • x ∈ fixedPointSubgroup D H := by
  rw [mem_fixedPointSubgroup_subgroup_iff] at hx ⊢
  intro d hd
  rw [← mul_smul, IsMulCommutative.is_comm.comm d b, mul_smul, hx d hd]

omit [Fact p.Prime] [Finite B] [IsElementaryAbelian p B] in
theorem actionCommutator_mono {S S' : Subgroup H} (h : S ≤ S') :
    actionCommutator B S ≤ actionCommutator B S' :=
  closure_mono fun _ ⟨x, hx, a, hxa⟩ => ⟨x, h hx, a, hxa⟩

omit [Fact p.Prime] [Finite B] [IsElementaryAbelian p B] in
theorem actionCommutator_le_of_invariant {S : Subgroup H} (hS : ∀ b : B, ∀ x ∈ S, b • x ∈ S) :
    actionCommutator B S ≤ S :=
  (closure_le _).mpr fun _ ⟨x, hx, a, hxa⟩ => hxa ▸ mul_mem (inv_mem hx) (hS a x hx)

omit [Fact p.Prime] [Finite B] [IsElementaryAbelian p B] in
theorem smul_mem_actionCommutator {S : Subgroup H} (hS : ∀ b : B, ∀ x ∈ S, b • x ∈ S) (b : B)
    {x : H} (hx : x ∈ actionCommutator B S) : b • x ∈ actionCommutator B S := by
  have hle : actionCommutator B S ≤
      (actionCommutator B S).comap (MulDistribMulAction.toMonoidHom H b) := by
    refine (closure_le _).mpr ?_
    rintro _ ⟨q, hq, a, rfl⟩
    change b • (q⁻¹ * (a • q)) ∈ actionCommutator B S
    have h : b • (q⁻¹ * (a • q)) = (b • q)⁻¹ * ((b * a * b⁻¹) • (b • q)) := by
      rw [smul_mul', smul_inv', ← mul_smul, ← mul_smul, inv_mul_cancel_right]
    rw [h]
    exact gen_mem_actionCommutator (hS b q hq) _
  exact hle hx

omit [Fact p.Prime] [Finite B] [IsElementaryAbelian p B] in
theorem map_actionCommutator_top_le (Q : Subgroup H) [CFSG.IsInvariant B H Q] :
    (actionCommutator B (⊤ : Subgroup Q)).map Q.subtype ≤ actionCommutator B Q := by
  rw [actionCommutator, MonoidHom.map_closure]
  refine (closure_le _).mpr ?_
  rintro _ ⟨_, ⟨q, -, a, rfl⟩, rfl⟩
  exact subset_closure ⟨q, q.2, a, rfl⟩

theorem le_closure_fixed_hyperplane_commutator [Nontrivial B] [Finite H]
    (hH : Group.IsSolvable H) (hp : ¬ p ∣ Nat.card H) (X : Subgroup H)
    (hX : ∀ b : B, ∀ x ∈ X, b • x ∈ X) :
    X ≤ closure {x | (x ∈ X ∧ x ∈ fixedPointSubgroup B H) ∨
      ∃ D : Subgroup B, D.index = p ∧ x ∈ actionCommutator B (X ⊓ fixedPointSubgroup D H)} := by
  set S := {x | (x ∈ X ∧ x ∈ fixedPointSubgroup B H) ∨
      ∃ D : Subgroup B, D.index = p ∧ x ∈ actionCommutator B (X ⊓ fixedPointSubgroup D H)}
  have hcopB : ∀ n : ℕ, n ∣ Nat.card H → Nat.Coprime n (Nat.card B) := by
    intro n hn
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (IsElementaryAbelian.isPGroup p B)
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_comm.mp
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr fun h => hp (h.trans hn))))
  have h1 : ∀ D : Subgroup B, D.index = p → X ⊓ fixedPointSubgroup D H ≤ closure S := by
    intro D hD
    set Q := X ⊓ fixedPointSubgroup D H with hQdef
    have hQinv : ∀ b : B, ∀ x ∈ Q, b • x ∈ Q := fun b x hx =>
      ⟨hX b x hx.1, smul_mem_fixedPointSubgroup D b hx.2⟩
    have : CFSG.IsInvariant B H Q := ⟨fun a g => ⟨fun hg => hQinv a g hg, fun hg => by
      simpa using hQinv a⁻¹ _ hg⟩⟩
    have hQsolv : Group.IsSolvable Q := by
      have := hH
      infer_instance
    obtain ⟨-, -, hfac, -⟩ :=
      CFSG.RankThree.Coprime.solvable_coprime_fixed_commutator_factorization (A := B) (H := Q)
        hQsolv (hcopB _ (Subgroup.card_subgroup_dvd_card Q))
    intro x hx
    obtain ⟨d, hd, c, hc, hdc⟩ := hfac ⟨x, hx⟩
    have hx' : x = (d : H) * (c : H) := congrArg Subtype.val hdc
    rw [hx']
    refine mul_mem (subset_closure (Or.inr ⟨D, hD, map_actionCommutator_top_le Q ⟨d, hd, rfl⟩⟩))
      (subset_closure (Or.inl ⟨c.2.1, fun b => ?_⟩))
    exact congrArg Subtype.val (hc b)
  have : CFSG.IsInvariant B H X := ⟨fun a g => ⟨fun hg => hX a g hg, fun hg => by
    simpa using hX a⁻¹ _ hg⟩⟩
  have hpX : ¬ p ∣ Nat.card X := fun h => hp (h.trans (Subgroup.card_subgroup_dvd_card X))
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (A := B) (H := X) hpX
  intro x hx
  have hmem : (⟨x, hx⟩ : X) ∈ ⨆ (D : Subgroup B) (_ : D.index = p), fixedPointSubgroup D X := by
    rw [hgen]
    exact mem_top _
  have hle : ⨆ (D : Subgroup B) (_ : D.index = p), fixedPointSubgroup D X ≤
      (closure S).comap X.subtype := by
    refine iSup₂_le fun D hD => ?_
    intro y hy
    refine h1 D hD ⟨y.2, (mem_fixedPointSubgroup_subgroup_iff D (y : H)).mpr fun d hd => ?_⟩
    exact congrArg Subtype.val (hy ⟨d, hd⟩)
  exact hle hmem

end Action

section Key

variable {p : ℕ} [Fact p.Prime] {B : Type*} [Group B] [Finite B] [IsElementaryAbelian p B]
  {H : Type*} [Group H] [MulDistribMulAction B H]

open scoped commutatorElement

omit [Finite B] [IsElementaryAbelian p B] in
theorem exists_mul_eq_of_index_eq_of_ne [IsMulCommutative B] {D E : Subgroup B}
    (hD : D.index = p) (hE : E.index = p) (hDE : D ≠ E) (b : B) :
    ∃ d ∈ D, ∃ e ∈ E, d * e = b := by
  have hDc : IsCoatom D := isCoatom_of_index_prime (hD ▸ Fact.out)
  have hEc : IsCoatom E := isCoatom_of_index_prime (hE ▸ Fact.out)
  have hsup : D ⊔ E = ⊤ := by
    rcases hDc.le_iff.mp (le_sup_left : D ≤ D ⊔ E) with h | h
    · exact h
    · have hED : E ≤ D := h ▸ le_sup_right
      rcases hEc.le_iff.mp hED with h' | h'
      · exact absurd h' hDc.1
      · exact absurd h' hDE
  have : E.Normal := normal_of_isMulCommutative E
  have hb : b ∈ ((D ⊔ E : Subgroup B) : Set B) := by rw [hsup]; exact mem_top b
  rw [mul_normal] at hb
  obtain ⟨d, hd, e, he, rfl⟩ := hb
  exact ⟨d, hd, e, he, rfl⟩

theorem commutator_inf_fixed_le_hyperplane_join [Nontrivial B] [Finite H]
    (hH : Group.IsSolvable H) (hp : ¬ p ∣ Nat.card H)
    (htop : actionCommutator B (⊤ : Subgroup H) = ⊤) (Y : Subgroup H)
    (hY : ∀ b : B, ∀ y ∈ Y, b • y ∈ Y) (hYc : ⁅Y, (⊤ : Subgroup H)⁆ ≤ center H) :
    ⁅Y, (⊤ : Subgroup H)⁆ ⊓ fixedPointSubgroup B H ≤
      ⨆ (D : Subgroup B) (_ : D.index = p),
        actionCommutator B (fixedPointSubgroup D H) ⊓ fixedPointSubgroup B H := by
  classical
  have : Fintype B := Fintype.ofFinite B
  set T := ⨆ (D : Subgroup B) (_ : D.index = p),
    actionCommutator B (fixedPointSubgroup D H) ⊓ fixedPointSubgroup B H with hT
  have hc : ∀ y ∈ Y, ∀ h : H, ⁅y, h⁆ ∈ center H := fun y hy h =>
    hYc (commutator_mem_commutator hy (mem_top h))
  have hCinv : ∀ D : Subgroup B, ∀ b : B, ∀ x ∈ fixedPointSubgroup D H,
      b • x ∈ fixedPointSubgroup D H := fun D b _ hx => smul_mem_fixedPointSubgroup D b hx
  have hYDinv : ∀ D : Subgroup B, ∀ b : B, ∀ x ∈ Y ⊓ fixedPointSubgroup D H,
      b • x ∈ Y ⊓ fixedPointSubgroup D H := fun D b x hx => ⟨hY b x hx.1, hCinv D b x hx.2⟩
  have hYD : ∀ D : Subgroup B, actionCommutator B (Y ⊓ fixedPointSubgroup D H) ≤ Y := fun D =>
    (actionCommutator_le_of_invariant (hYDinv D)).trans inf_le_left
  have stepA : ∀ y ∈ Y, (∀ b : B, b • y = y) → ∀ h : H, centralNorm B ⁅y, h⁆ = 1 := by
    intro y hy hyfix h
    have hh : h ∈ actionCommutator B (⊤ : Subgroup H) := by rw [htop]; exact mem_top h
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g, -, a, rfl⟩ := hx
      rw [commutatorElement_mul_right_of_mem_center (hc y hy _),
        commutatorElement_inv_right_of_mem_center (hc y hy g)]
      have hya : ⁅y, a • g⁆ = a • ⁅y, g⁆ := by rw [smul_commutatorElement, hyfix a]
      rw [hya]
      exact centralNorm_inv_mul_smul a (hc y hy g)
    | one => rw [commutatorElement_one_right, centralNorm_one]
    | mul x x' _ _ hx hx' =>
      rw [commutatorElement_mul_right_of_mem_center (hc y hy x'),
        centralNorm_mul (hc y hy x) (hc y hy x'), hx, hx', mul_one]
    | inv x _ hx =>
      rw [commutatorElement_inv_right_of_mem_center (hc y hy x), centralNorm_inv (hc y hy x), hx,
        inv_one]
  have stepBC : ∀ D E : Subgroup B, (∀ b : B, ∃ d ∈ D, ∃ e ∈ E, d * e = b) →
      ∀ h : H, (∀ e ∈ E, e • h = h) →
        ∀ y ∈ actionCommutator B (Y ⊓ fixedPointSubgroup D H), centralNorm B ⁅y, h⁆ = 1 := by
    intro D E hDE h hh y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g, hg, b, rfl⟩ := hx
      obtain ⟨d, hd, e, he, rfl⟩ := hDE b
      have hge : (d * e) • g = e • g := by
        rw [mul_smul, (mem_fixedPointSubgroup_subgroup_iff D _).mp
          (smul_mem_fixedPointSubgroup D e hg.2) d hd]
      rw [hge, commutatorElement_mul_left_of_mem_center (hc _ (hY e g hg.1) h),
        commutatorElement_inv_left_of_mem_center (hc g hg.1 h)]
      have hgh : ⁅e • g, h⁆ = e • ⁅g, h⁆ := by rw [smul_commutatorElement, hh e he]
      rw [hgh]
      exact centralNorm_smul_mul_inv e (hc g hg.1 h)
    | one => rw [commutatorElement_one_left, centralNorm_one]
    | mul x x' hx hx' ihx ihx' =>
      rw [commutatorElement_mul_left_of_mem_center (hc x' (hYD D hx') h),
        centralNorm_mul (hc x' (hYD D hx') h) (hc x (hYD D hx) h), ihx, ihx', mul_one]
    | inv x hx ihx =>
      rw [commutatorElement_inv_left_of_mem_center (hc x (hYD D hx) h),
        centralNorm_inv (hc x (hYD D hx) h), ihx, inv_one]
  have stepD : ∀ D : Subgroup B, D.index = p →
      ∀ y ∈ actionCommutator B (Y ⊓ fixedPointSubgroup D H),
      ∀ h ∈ actionCommutator B (fixedPointSubgroup D H), centralNorm B ⁅y, h⁆ ∈ T := by
    intro D hD y hy h hh
    have hyK : y ∈ actionCommutator B (fixedPointSubgroup D H) :=
      actionCommutator_mono inf_le_right hy
    have hcK : ⁅y, h⁆ ∈ actionCommutator B (fixedPointSubgroup D H) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hyK hh) (inv_mem hyK)) (inv_mem hh)
    have hmem : centralNorm B ⁅y, h⁆ ∈
        actionCommutator B (fixedPointSubgroup D H) ⊓ fixedPointSubgroup B H :=
      ⟨centralNorm_mem (fun b x hx => smul_mem_actionCommutator (hCinv D) b hx) hcK,
        fun b => smul_centralNorm b _⟩
    exact le_iSup₂ (f := fun (D : Subgroup B) (_ : D.index = p) =>
      actionCommutator B (fixedPointSubgroup D H) ⊓ fixedPointSubgroup B H) D hD hmem
  have hgenH := le_closure_fixed_hyperplane_commutator (B := B) hH hp (⊤ : Subgroup H)
    (fun _ _ _ => mem_top _)
  have stepE : ∀ D : Subgroup B, D.index = p →
      ∀ y ∈ actionCommutator B (Y ⊓ fixedPointSubgroup D H), ∀ h : H, centralNorm B ⁅y, h⁆ ∈ T := by
    intro D hD y hy h
    have hyY : y ∈ Y := hYD D hy
    induction (hgenH (mem_top h)) using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨-, hxB⟩ | ⟨E, hE, hxE⟩
      · rw [stepBC D ⊤ (fun b => ⟨1, one_mem D, b, mem_top b, one_mul b⟩) x
          (fun e _ => hxB e) y hy]
        exact one_mem T
      · rw [top_inf_eq] at hxE
        by_cases hED : E = D
        · subst hED
          exact stepD E hD y hy x hxE
        · have hxfix : ∀ e ∈ E, e • x = x :=
            (mem_fixedPointSubgroup_subgroup_iff E x).mp
              (actionCommutator_le_of_invariant (hCinv E) hxE)
          rw [stepBC D E (exists_mul_eq_of_index_eq_of_ne hD hE (Ne.symm hED)) x hxfix y hy]
          exact one_mem T
    | one => rw [commutatorElement_one_right, centralNorm_one]; exact one_mem T
    | mul x x' _ _ hx hx' =>
      rw [commutatorElement_mul_right_of_mem_center (hc y hyY x'),
        centralNorm_mul (hc y hyY x) (hc y hyY x')]
      exact mul_mem hx hx'
    | inv x _ hx =>
      rw [commutatorElement_inv_right_of_mem_center (hc y hyY x), centralNorm_inv (hc y hyY x)]
      exact inv_mem hx
  have hgenY := le_closure_fixed_hyperplane_commutator (B := B) hH hp Y hY
  have hclY : closure {x | (x ∈ Y ∧ x ∈ fixedPointSubgroup B H) ∨ ∃ D : Subgroup B,
      D.index = p ∧ x ∈ actionCommutator B (Y ⊓ fixedPointSubgroup D H)} ≤ Y := by
    refine (closure_le _).mpr ?_
    rintro x (⟨hx, -⟩ | ⟨D, -, hx⟩)
    · exact hx
    · exact hYD D hx
  have stepF' : ∀ y ∈ closure {x | (x ∈ Y ∧ x ∈ fixedPointSubgroup B H) ∨ ∃ D : Subgroup B,
      D.index = p ∧ x ∈ actionCommutator B (Y ⊓ fixedPointSubgroup D H)},
      ∀ h : H, centralNorm B ⁅y, h⁆ ∈ T := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨hxY, hxB⟩ | ⟨D, hD, hxD⟩
      · intro h
        rw [stepA x hxY hxB h]
        exact one_mem T
      · exact stepE D hD x hxD
    | one => intro h; rw [commutatorElement_one_left, centralNorm_one]; exact one_mem T
    | mul x x' hx hx' ihx ihx' =>
      intro h
      rw [commutatorElement_mul_left_of_mem_center (hc x' (hclY hx') h),
        centralNorm_mul (hc x' (hclY hx') h) (hc x (hclY hx) h)]
      exact mul_mem (ihx' h) (ihx h)
    | inv x hx ihx =>
      intro h
      rw [commutatorElement_inv_left_of_mem_center (hc x (hclY hx) h),
        centralNorm_inv (hc x (hclY hx) h)]
      exact inv_mem (ihx h)
  have stepF : ∀ y ∈ Y, ∀ h : H, centralNorm B ⁅y, h⁆ ∈ T := fun y hy => stepF' y (hgenY hy)
  have hnormZ : ∀ z ∈ ⁅Y, (⊤ : Subgroup H)⁆, centralNorm B z ∈ T := by
    intro z hz
    rw [Subgroup.commutator_def] at hz
    induction hz using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨y, hy, h, -, rfl⟩ := hx
      exact stepF y hy h
    | one => rw [centralNorm_one]; exact one_mem T
    | mul x x' hx hx' ihx ihx' =>
      rw [← Subgroup.commutator_def] at hx hx'
      rw [centralNorm_mul (hYc hx) (hYc hx')]
      exact mul_mem ihx ihx'
    | inv x hx ihx =>
      rw [← Subgroup.commutator_def] at hx
      rw [centralNorm_inv (hYc hx)]
      exact inv_mem ihx
  rintro x ⟨hxZ, hxB⟩
  have hN : centralNorm B x = x ^ Fintype.card B := centralNorm_of_fixed (hYc hxZ) hxB
  have hcop : Nat.Coprime (Fintype.card B) (orderOf x) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (IsElementaryAbelian.isPGroup p B)
    rw [Fintype.card_eq_nat_card, hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr fun h =>
      hp (h.trans (orderOf_dvd_natCard x)))
  have hxT : x ^ Fintype.card B ∈ T := hN ▸ hnormZ x hxZ
  exact (zpowers_le.mpr hxT) (mem_zpowers_pow_iff.mpr hcop)

end Key

section Lifting

theorem exists_fixed_mem_coset {p : ℕ} [Fact p.Prime] {A H : Type*} [Group A] [Finite A]
    [Group H] [Finite H] [MulDistribMulAction A H] (hA : IsPGroup p A) (N : Subgroup H)
    (hN : ∀ (a : A) (x : H), x ∈ N → a • x ∈ N) (hNp : ¬ p ∣ Nat.card N) (g : H)
    (hg : ∀ a : A, g⁻¹ * (a • g) ∈ N) : ∃ c : H, (∀ a : A, a • c = c) ∧ g⁻¹ * c ∈ N := by
  obtain ⟨c, hc, hcfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed p hA
    (MulDistribMulAction.toMulAut A H) N hNp g).2 (by
      intro a x hx
      change g⁻¹ * (a • x) ∈ N
      have h : g⁻¹ * (a • x) = (g⁻¹ * (a • g)) * (a • (g⁻¹ * x)) := by
        rw [smul_mul', smul_inv']
        group
      rw [h]
      exact mul_mem (hg a) (hN a _ hx))
  exact ⟨c, hcfix, hc⟩

variable {B H : Type*} [Group B] [Group H] [MulDistribMulAction B H]

theorem map_actionCommutator_quotient (Z : Subgroup H) [Z.Normal]
    (hZ : CFSG.IsInvariant B H Z) (S : Subgroup H) :
    letI : MulDistribMulAction B (H ⧸ Z) := CFSG.quotientMulDistribMulAction (A := B) Z hZ
    (actionCommutator B S).map (QuotientGroup.mk' Z) =
      actionCommutator B (S.map (QuotientGroup.mk' Z)) := by
  let : MulDistribMulAction B (H ⧸ Z) := CFSG.quotientMulDistribMulAction (A := B) Z hZ
  apply le_antisymm
  · rw [actionCommutator, MonoidHom.map_closure]
    refine (closure_le _).mpr ?_
    rintro _ ⟨_, ⟨h, hh, a, rfl⟩, rfl⟩
    exact subset_closure ⟨(h : H ⧸ Z), ⟨h, hh, rfl⟩, a, rfl⟩
  · refine (closure_le _).mpr ?_
    rintro _ ⟨_, ⟨h, hh, rfl⟩, a, rfl⟩
    exact ⟨h⁻¹ * (a • h), subset_closure ⟨h, hh, a, rfl⟩, rfl⟩

end Lifting

section Main

variable {p : ℕ} [Fact p.Prime] {B : Type*} [Group B] [Finite B] [IsElementaryAbelian p B]

open scoped commutatorElement

theorem fixedPointSubgroup_le_hyperplane_join_aux [Nontrivial B] :
    ∀ (n : ℕ) (H : Type*) [Group H] [Finite H] [MulDistribMulAction B H], Nat.card H = n →
      Group.IsNilpotent H → ¬ p ∣ Nat.card H → actionCommutator B (⊤ : Subgroup H) = ⊤ →
      fixedPointSubgroup B H ≤ ⨆ (D : Subgroup B) (_ : D.index = p),
        actionCommutator B (fixedPointSubgroup D H) ⊓ fixedPointSubgroup B H := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H _ _ _ hn hnil hp htop
  classical
  have : Fintype B := Fintype.ofFinite B
  have hBp : IsPGroup p B := IsElementaryAbelian.isPGroup p B
  have hcopx : ∀ x : H, Nat.Coprime (Fintype.card B) (orderOf x) := by
    intro x
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hBp
    rw [Fintype.card_eq_nat_card, hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr fun h =>
      hp (h.trans (orderOf_dvd_natCard x)))
  have hTfix : (⨆ (D : Subgroup B) (_ : D.index = p),
      actionCommutator B (fixedPointSubgroup D H) ⊓ fixedPointSubgroup B H) ≤
        fixedPointSubgroup B H := iSup₂_le fun _ _ => inf_le_right
  have hsolv : Group.IsSolvable H := inferInstance
  by_cases hc2 : Group.nilpotencyClass H < 2
  ·
    have hΓ : (⊤ : Subgroup H).lowerCentralSeries 1 = ⊥ :=
      (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le (G := H) (n := 1)).mpr (by omega)
    have hcent : ∀ x : H, x ∈ center H := by
      intro x
      rw [mem_center_iff]
      intro g
      have hmem : ⁅g, x⁆ ∈ (⊤ : Subgroup H).lowerCentralSeries 1 := by
        rw [Subgroup.top_lowerCentralSeries_one]
        exact commutator_mem_commutator (mem_top g) (mem_top x)
      rw [hΓ, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    have hN1 : ∀ h ∈ actionCommutator B (⊤ : Subgroup H), centralNorm B h = 1 := by
      intro h hh
      induction hh using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨g, -, a, rfl⟩ := hx
        exact centralNorm_inv_mul_smul a (hcent g)
      | one => exact centralNorm_one
      | mul x x' _ _ hx hx' => rw [centralNorm_mul (hcent x) (hcent x'), hx, hx', mul_one]
      | inv x _ hx => rw [centralNorm_inv (hcent x), hx, inv_one]
    intro x hx
    have hxpow : x ^ Fintype.card B = 1 := by
      rw [← centralNorm_of_fixed (hcent x) hx]
      exact hN1 x (by rw [htop]; exact mem_top x)
    have hx1 : x = 1 := by
      rw [← orderOf_eq_one_iff]
      exact Nat.Coprime.eq_one_of_dvd (hcopx x).symm (orderOf_dvd_of_pow_eq_one hxpow)
    rw [hx1]
    exact one_mem _
  push Not at hc2
  set c := Group.nilpotencyClass H with hcdef
  set Y := (⊤ : Subgroup H).lowerCentralSeries (c - 2) with hYdef
  set Z := (⊤ : Subgroup H).lowerCentralSeries (c - 1) with hZdef
  have hZY : Z = ⁅Y, (⊤ : Subgroup H)⁆ := by
    rw [hZdef, hYdef, show c - 1 = c - 2 + 1 by omega, Subgroup.lowerCentralSeries_succ]
  have hZc : Z ≤ center H := by
    intro z hz
    rw [mem_center_iff]
    intro g
    have hmem : ⁅z, g⁆ ∈ (⊤ : Subgroup H).lowerCentralSeries c := by
      rw [show c = c - 1 + 1 by omega, Subgroup.lowerCentralSeries_succ]
      exact commutator_mem_commutator hz (mem_top g)
    rw [Subgroup.lowerCentralSeries_nilpotencyClass, mem_bot,
      commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem.symm
  have hZne : Z ≠ ⊥ := by
    intro h
    have := (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le (G := H) (n := c - 1)).mp h
    omega
  have hYinv : ∀ b : B, ∀ y ∈ Y, b • y ∈ Y := fun b y hy =>
    (mem_iff_smul_mem_of_characteristic Y b y).mp hy
  have hZinv : ∀ (b : B) (z : H), z ∈ Z ↔ b • z ∈ Z := fun b z =>
    mem_iff_smul_mem_of_characteristic Z b z
  have hZinv' : CFSG.IsInvariant B H Z := ⟨hZinv⟩
  have hkey := commutator_inf_fixed_le_hyperplane_join (B := B) hsolv hp htop Y hYinv
    (hZY ▸ hZc)
  rw [← hZY] at hkey
  let : MulDistribMulAction B (H ⧸ Z) := CFSG.quotientMulDistribMulAction (A := B) Z hZinv'
  have hsmul : ∀ (b : B) (g : H), b • (g : H ⧸ Z) = ((b • g : H) : H ⧸ Z) := fun _ _ => rfl
  have hZp : ¬ p ∣ Nat.card Z := fun h => hp (h.trans (Subgroup.card_subgroup_dvd_card Z))
  have hcardQ : Nat.card (H ⧸ Z) < n := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    have h2 : 1 < Nat.card Z := (Subgroup.one_lt_card_iff_ne_bot Z).mpr hZne
    rw [← hn, h1]
    exact lt_mul_of_one_lt_right Nat.card_pos h2
  have hnilQ : Group.IsNilpotent (H ⧸ Z) := Group.nilpotent_quotient_of_nilpotent Z
  have hpQ : ¬ p ∣ Nat.card (H ⧸ Z) := fun h => hp (h.trans (Subgroup.card_quotient_dvd_card Z))
  have htopQ : actionCommutator B (⊤ : Subgroup (H ⧸ Z)) = ⊤ := by
    have h := map_actionCommutator_quotient Z hZinv' (⊤ : Subgroup H)
    rw [htop, ← MonoidHom.range_eq_map, QuotientGroup.range_mk'] at h
    exact h.symm
  have hIH := ih _ hcardQ (H ⧸ Z) rfl hnilQ hpQ htopQ
  have hTQ : (⨆ (D : Subgroup B) (_ : D.index = p),
      actionCommutator B (fixedPointSubgroup D (H ⧸ Z)) ⊓ fixedPointSubgroup B (H ⧸ Z)) ≤
      (⨆ (D : Subgroup B) (_ : D.index = p),
        actionCommutator B (fixedPointSubgroup D H) ⊓ fixedPointSubgroup B H).map
          (QuotientGroup.mk' Z) := by
    refine iSup₂_le fun D hD => ?_
    have hDp : IsPGroup p D := hBp.to_subgroup D
    have hCD : fixedPointSubgroup D (H ⧸ Z) ≤
        (fixedPointSubgroup D H).map (QuotientGroup.mk' Z) := by
      intro q hq
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      have hg : ∀ d : D, g⁻¹ * (d • g) ∈ Z := fun d => by
        have h := hq d
        change (d : B) • (g : H ⧸ Z) = (g : H ⧸ Z) at h
        rw [hsmul] at h
        exact QuotientGroup.eq.mp h.symm
      obtain ⟨c, hcfix, hcg⟩ := exists_fixed_mem_coset hDp Z (fun d x hx => (hZinv d x).mp hx)
        hZp g hg
      exact ⟨c, hcfix, (QuotientGroup.eq.mpr hcg).symm⟩
    intro q ⟨hqK, hqB⟩
    have hqK' : q ∈ (actionCommutator B (fixedPointSubgroup D H)).map (QuotientGroup.mk' Z) := by
      rw [map_actionCommutator_quotient Z hZinv']
      exact actionCommutator_mono hCD hqK
    obtain ⟨x, hxK, rfl⟩ := hqK'
    have hKinv : ∀ (b : B) (y : H), y ∈ actionCommutator B (fixedPointSubgroup D H) →
        b • y ∈ actionCommutator B (fixedPointSubgroup D H) := fun b y hy =>
      smul_mem_actionCommutator (fun b' z hz => smul_mem_fixedPointSubgroup D b' hz) b hy
    have hx : ∀ b : B, x⁻¹ * (b • x) ∈ actionCommutator B (fixedPointSubgroup D H) ⊓ Z := by
      intro b
      refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hxK) (hKinv b x hxK), ?_⟩
      have h := hqB b
      change b • (x : H ⧸ Z) = (x : H ⧸ Z) at h
      rw [hsmul] at h
      exact QuotientGroup.eq.mp h.symm
    have hNp : ¬ p ∣ Nat.card (actionCommutator B (fixedPointSubgroup D H) ⊓ Z : Subgroup H) :=
      fun h => hp (h.trans (Subgroup.card_subgroup_dvd_card _))
    obtain ⟨c, hcfix, hcx⟩ := exists_fixed_mem_coset hBp _
      (fun b y hy => Subgroup.mem_inf.mpr ⟨hKinv b y (Subgroup.mem_inf.mp hy).1,
        (hZinv b y).mp (Subgroup.mem_inf.mp hy).2⟩) hNp x hx
    have hcK : c ∈ actionCommutator B (fixedPointSubgroup D H) := by
      have := mul_mem hxK hcx.1
      rwa [mul_inv_cancel_left] at this
    refine ⟨c, ?_, (QuotientGroup.eq.mpr hcx.2).symm⟩
    exact le_iSup₂ (f := fun (D : Subgroup B) (_ : D.index = p) =>
      actionCommutator B (fixedPointSubgroup D H) ⊓ fixedPointSubgroup B H) D hD ⟨hcK, hcfix⟩
  intro x hx
  have hxQ : (x : H ⧸ Z) ∈ fixedPointSubgroup B (H ⧸ Z) := fun b => by
    rw [hsmul, hx b]
  obtain ⟨t, htT, htx⟩ := hTQ (hIH hxQ)
  have hzZ : t⁻¹ * x ∈ Z := QuotientGroup.eq.mp htx
  have hzB : t⁻¹ * x ∈ fixedPointSubgroup B H := mul_mem (inv_mem (hTfix htT)) hx
  have := mul_mem htT (hkey ⟨hzZ, hzB⟩)
  rwa [mul_inv_cancel_left] at this

theorem nilpotent_hyperplane_commutator_fixed_generation (hB : p ^ 2 ≤ Nat.card B) {H : Type*}
    [Group H] [Finite H] [MulDistribMulAction B H] (hH : Group.IsNilpotent H)
    (hp : ¬ p ∣ Nat.card H) (htop : actionCommutator B (⊤ : Subgroup H) = ⊤) :
    fixedPointSubgroup B H = ⨆ (D : Subgroup B) (_ : D.index = p),
        actionCommutator B (fixedPointSubgroup D H) ⊓ fixedPointSubgroup B H ∧
      (Nat.card B = p ^ 2 → fixedPointSubgroup B H = ⨆ (b : B) (_ : b ≠ 1),
        actionCommutator B (fixedPointSubgroup (zpowers b) H) ⊓ fixedPointSubgroup B H) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have : Nontrivial B :=
    Finite.one_lt_card_iff_nontrivial.mp (lt_of_lt_of_le (Nat.one_lt_pow two_ne_zero hp1) hB)
  have hmain : fixedPointSubgroup B H = ⨆ (D : Subgroup B) (_ : D.index = p),
      actionCommutator B (fixedPointSubgroup D H) ⊓ fixedPointSubgroup B H :=
    le_antisymm (fixedPointSubgroup_le_hyperplane_join_aux _ H rfl hH hp htop)
      (iSup₂_le fun _ _ => inf_le_right)
  refine ⟨hmain, fun hcard => hmain.trans ?_⟩
  have hord : ∀ b : B, b ≠ 1 → orderOf b = p := fun b hb =>
    orderOf_eq_prime (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p B) b) hb
  have hzp : ∀ b : B, b ≠ 1 → (zpowers b).index = p := by
    intro b hb
    have h := (zpowers b).index_mul_card
    rw [Nat.card_zpowers, hord b hb, hcard, sq] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.Prime.pos Fact.out) h
  apply le_antisymm
  · refine iSup₂_le fun D hD => ?_
    have hDcard : Nat.card D = p := by
      have h := D.index_mul_card
      rw [hD, hcard, sq] at h
      exact Nat.eq_of_mul_eq_mul_left (Nat.Prime.pos Fact.out) h
    obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp
      ((Subgroup.one_lt_card_iff_ne_bot D).mp (hDcard ▸ hp1)))
    have hDb : zpowers (b : B) = D := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr b.2) (by
      rw [hDcard, Nat.card_zpowers, hord b (fun h => hb1 (Subtype.ext h))])
    have hb1' : (b : B) ≠ 1 := fun h => hb1 (Subtype.ext h)
    rw [← hDb]
    exact le_iSup₂ (f := fun (b : B) (_ : b ≠ 1) =>
      actionCommutator B (fixedPointSubgroup (zpowers b) H) ⊓ fixedPointSubgroup B H) (b : B) hb1'
  · refine iSup₂_le fun b hb => ?_
    exact le_iSup₂ (f := fun (D : Subgroup B) (_ : D.index = p) =>
      actionCommutator B (fixedPointSubgroup D H) ⊓ fixedPointSubgroup B H) (zpowers b)
        (hzp b hb)

end Main

end CFSG.RankThree.GroupTheory
