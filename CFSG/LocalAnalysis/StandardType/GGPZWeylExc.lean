module

public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.GroupTheory.Coxeter.Matrix
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.Subgroup.Center
public import CFSG.LieType.Chevalley.LatticeWeylGroup
public import CFSG.LieType.Chevalley.ConnectedDiagram
public import CFSG.LieType.Chevalley.LongestElement
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLFaithful

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem

private def pnx_word (τ : Tag) : List (Fin τ.rank) :=
  (RootOps.longestWord τ).map τ.idx

private theorem pnx_wordProd_smul {τ : Tag} (ω : List (Fin τ.rank))
    (v : Fin τ.rank → ℤ) :
    (coxeterSystem τ).wordProd ω • v = ω.foldr (fun i v => reflect τ i v) v := by
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul]; rfl
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_smul, ih]
    exact simple_smul i _

private def pnx_w (τ : Tag) : WeylGroup τ :=
  (coxeterSystem τ).wordProd (pnx_word τ)

private theorem pnx_w_smul {τ : Tag} (v : Fin τ.rank → ℤ) :
    pnx_w τ • v = (pnx_word τ).foldr (fun i v => reflect τ i v) v :=
  pnx_wordProd_smul (pnx_word τ) v

private theorem pnx_simple_smul_self {τ : Tag} (i : Fin τ.rank) :
    simple τ i • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single i 1 := by
  rw [simple_smul, reflect_single_self]

private theorem pnx_simple_smul_single {τ : Tag} {i j : Fin τ.rank} :
    simple τ i • (Pi.single j 1 : Fin τ.rank → ℤ) =
      Pi.single j 1 - τ.cartan i j • (Pi.single i 1 : Fin τ.rank → ℤ) := by
  rw [simple_smul, reflect]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

private theorem pnx_smul_eq_neg_of_single {τ : Tag} {w : WeylGroup τ}
    (h : ∀ i, w • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single i 1)
    (v : Fin τ.rank → ℤ) : w • v = -v := by
  have hlin : weylAction (isFiniteType_cartan τ) w = -LinearMap.id := by
    refine LinearMap.pi_ext fun i x => ?_
    rw [← mul_one x, ← smul_eq_mul, Pi.single_smul, map_smul, ← smul_def, h i]
    simp
  rw [smul_def, hlin]
  simp

private theorem pnx_mul_comm_of_neg {τ : Tag} {w₀ : WeylGroup τ}
    (hw₀ : ∀ v : Fin τ.rank → ℤ, w₀ • v = -v) (w : WeylGroup τ) : w * w₀ = w₀ * w := by
  refine ext_single fun i => ?_
  rw [mul_smul, mul_smul, hw₀, hw₀, smul_neg]

private theorem pnx_sum_single {τ : Tag} (v : Fin τ.rank → ℤ) :
    ∑ i, v i • (Pi.single i 1 : Fin τ.rank → ℤ) = v := by
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hi), smul_zero]
  · intro hj
    simp at hj

private theorem pnx_smul_zsmul {τ : Tag} (w : WeylGroup τ) (n : ℤ) (x : Fin τ.rank → ℤ) :
    w • (n • x) = n • (w • x) :=
  AddMonoidHom.map_zsmul
    (DistribMulAction.toAddMonoidEnd (WeylGroup τ) (Fin τ.rank → ℤ) w) n x

private theorem pnx_center_smul_single_diag {τ : Tag} {z : WeylGroup τ}
    (hz : z ∈ Subgroup.center (WeylGroup τ)) (i : Fin τ.rank) :
    z • (Pi.single i 1 : Fin τ.rank → ℤ) =
      ((z • (Pi.single i 1 : Fin τ.rank → ℤ)) i) • (Pi.single i 1 : Fin τ.rank → ℤ) := by
  have hcenter : simple τ i * z = z * simple τ i :=
    (Subgroup.mem_center_iff.mp hz) (simple τ i)
  have hcomm : simple τ i • (z • (Pi.single i 1 : Fin τ.rank → ℤ)) =
      -(z • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
    calc simple τ i • (z • (Pi.single i 1 : Fin τ.rank → ℤ))
        = (simple τ i * z) • (Pi.single i 1 : Fin τ.rank → ℤ) := by rw [mul_smul]
      _ = (z * simple τ i) • (Pi.single i 1 : Fin τ.rank → ℤ) := by rw [hcenter]
      _ = z • (simple τ i • (Pi.single i 1 : Fin τ.rank → ℤ)) := by rw [mul_smul]
      _ = z • (-Pi.single i 1) := by rw [pnx_simple_smul_self]
      _ = -(z • (Pi.single i 1 : Fin τ.rank → ℤ)) := by rw [smul_neg]
  have hreflect : simple τ i • (z • (Pi.single i 1 : Fin τ.rank → ℤ)) =
      (z • (Pi.single i 1 : Fin τ.rank → ℤ)) -
        (∑ j, τ.cartan i j * (z • (Pi.single i 1 : Fin τ.rank → ℤ)) j) •
          (Pi.single i 1 : Fin τ.rank → ℤ) := by
    rw [simple_smul, reflect]
  rw [hreflect] at hcomm
  funext k
  by_cases hk : k = i
  · subst hk; simp
  · have hcoord := congrFun hcomm k
    rw [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.single_eq_of_ne hk, smul_zero,
      sub_zero] at hcoord
    have hvk : (z • (Pi.single i 1 : Fin τ.rank → ℤ)) k = 0 := by omega
    rw [hvk, Pi.smul_apply, Pi.single_eq_of_ne hk, smul_zero]

private theorem pnx_center_smul_single_unit {τ : Tag} {z : WeylGroup τ}
    (hz : z ∈ Subgroup.center (WeylGroup τ)) (i : Fin τ.rank) :
    (z • (Pi.single i 1 : Fin τ.rank → ℤ)) i = 1 ∨
      (z • (Pi.single i 1 : Fin τ.rank → ℤ)) i = -1 := by
  set c : ℤ := (z • (Pi.single i 1 : Fin τ.rank → ℤ)) i with hc
  set d : ℤ := (z⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) i with hd
  have hz' : z⁻¹ ∈ Subgroup.center (WeylGroup τ) := Subgroup.inv_mem _ hz
  have hdiag : z • (Pi.single i 1 : Fin τ.rank → ℤ) =
      c • (Pi.single i 1 : Fin τ.rank → ℤ) := pnx_center_smul_single_diag hz i
  have hdiag' : z⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ) =
      d • (Pi.single i 1 : Fin τ.rank → ℤ) := pnx_center_smul_single_diag hz' i
  have h1 : (Pi.single i 1 : Fin τ.rank → ℤ) =
      z⁻¹ • (z • (Pi.single i 1 : Fin τ.rank → ℤ)) := (inv_smul_smul z _).symm
  have h2 : z⁻¹ • (z • (Pi.single i 1 : Fin τ.rank → ℤ)) =
      (c * d) • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    rw [hdiag, pnx_smul_zsmul z⁻¹ c (Pi.single i 1 : Fin τ.rank → ℤ), hdiag', ← smul_smul]
  have h3 : (1 : ℤ) = c * d := by
    have := congrFun (h1.trans h2) i
    simpa [Pi.smul_apply] using this
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp h3.symm with ⟨hcl, -⟩ | ⟨hcl, -⟩
  · exact Or.inl hcl
  · exact Or.inr hcl

private theorem pnx_center_sign_eq {τ : Tag} {z : WeylGroup τ}
    (hz : z ∈ Subgroup.center (WeylGroup τ)) {i j : Fin τ.rank}
    (hij : (dynkinGraph τ).Adj i j) :
    (z • (Pi.single i 1 : Fin τ.rank → ℤ)) i =
      (z • (Pi.single j 1 : Fin τ.rank → ℤ)) j := by
  obtain ⟨hij_ne, hij_prod⟩ := hij
  have hcenter : simple τ i * z = z * simple τ i :=
    (Subgroup.mem_center_iff.mp hz) (simple τ i)
  have hcommut : z • (simple τ i • (Pi.single j 1 : Fin τ.rank → ℤ)) =
      simple τ i • (z • (Pi.single j 1 : Fin τ.rank → ℤ)) := by
    rw [← mul_smul, ← mul_smul, hcenter]
  have hL : z • (simple τ i • (Pi.single j 1 : Fin τ.rank → ℤ)) =
      ((z • (Pi.single j 1 : Fin τ.rank → ℤ)) j) • (Pi.single j 1 : Fin τ.rank → ℤ) -
        τ.cartan i j • (((z • (Pi.single i 1 : Fin τ.rank → ℤ)) i) •
          (Pi.single i 1 : Fin τ.rank → ℤ)) := by
    conv_lhs =>
      rw [pnx_simple_smul_single, smul_sub,
        pnx_smul_zsmul z (τ.cartan i j) (Pi.single i 1 : Fin τ.rank → ℤ),
        pnx_center_smul_single_diag hz j, pnx_center_smul_single_diag hz i]
  have hR : simple τ i • (z • (Pi.single j 1 : Fin τ.rank → ℤ)) =
      ((z • (Pi.single j 1 : Fin τ.rank → ℤ)) j) • (Pi.single j 1 : Fin τ.rank → ℤ) -
        ((z • (Pi.single j 1 : Fin τ.rank → ℤ)) j) •
          (τ.cartan i j • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
    conv_lhs =>
      rw [pnx_center_smul_single_diag hz j,
        pnx_smul_zsmul (simple τ i) ((z • (Pi.single j 1 : Fin τ.rank → ℤ)) j)
          (Pi.single j 1 : Fin τ.rank → ℤ),
        pnx_simple_smul_single, smul_sub]
  have hEq := (hL.symm.trans hcommut).trans hR
  have hcoord := congrFun hEq i
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hij_ne, Pi.single_eq_same,
    mul_zero, mul_one, smul_eq_mul, zero_sub] at hcoord
  have ha : τ.cartan i j ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hij_prod
    exact lt_irrefl 0 hij_prod
  rw [mul_comm ((z • (Pi.single j 1 : Fin τ.rank → ℤ)) j) (τ.cartan i j)] at hcoord
  exact mul_left_cancel₀ ha (neg_inj.mp hcoord)

private theorem pnx_reachable_sign {τ : Tag} {c : Fin τ.rank → ℤ}
    (h : ∀ i j, (dynkinGraph τ).Adj i j → c i = c j) :
    ∀ i j, (dynkinGraph τ).Reachable i j → c i = c j := by
  intro i j hw
  obtain ⟨w⟩ := hw
  induction w with
  | nil => rfl
  | cons hab p ih => exact (h _ _ hab).trans ih

private theorem pnx_center_scalar {τ : Tag} {z : WeylGroup τ}
    (hz : z ∈ Subgroup.center (WeylGroup τ)) :
    ∃ c : ℤ, (c = 1 ∨ c = -1) ∧ ∀ v : Fin τ.rank → ℤ, z • v = c • v := by
  let i0 : Fin τ.rank := ⟨0, τ.rank_pos⟩
  have hdiag : ∀ i, z • (Pi.single i 1 : Fin τ.rank → ℤ) =
      ((z • (Pi.single i 1 : Fin τ.rank → ℤ)) i) • (Pi.single i 1 : Fin τ.rank → ℤ) :=
    fun i => pnx_center_smul_single_diag hz i
  have hadj : ∀ i j, (dynkinGraph τ).Adj i j →
      (z • (Pi.single i 1 : Fin τ.rank → ℤ)) i =
        (z • (Pi.single j 1 : Fin τ.rank → ℤ)) j :=
    fun i j hij => pnx_center_sign_eq hz hij
  have hconn : ∀ i, (dynkinGraph τ).Reachable i i0 :=
    fun i => (dynkinGraph_connected τ).preconnected i i0
  have hall : ∀ i, (z • (Pi.single i 1 : Fin τ.rank → ℤ)) i =
      (z • (Pi.single i0 1 : Fin τ.rank → ℤ)) i0 :=
    fun i => pnx_reachable_sign hadj i i0 (hconn i)
  refine ⟨(z • (Pi.single i0 1 : Fin τ.rank → ℤ)) i0,
    pnx_center_smul_single_unit hz i0, fun v => ?_⟩
  calc z • v = z • (∑ i, v i • (Pi.single i 1 : Fin τ.rank → ℤ)) := by rw [pnx_sum_single]
    _ = ∑ i, z • (v i • (Pi.single i 1 : Fin τ.rank → ℤ)) := by rw [Finset.smul_sum]
    _ = ∑ i, v i • (z • (Pi.single i 1 : Fin τ.rank → ℤ)) :=
        Finset.sum_congr rfl fun i _ => pnx_smul_zsmul z (v i) _
    _ = ∑ i, v i • ((z • (Pi.single i0 1 : Fin τ.rank → ℤ)) i0 •
          (Pi.single i 1 : Fin τ.rank → ℤ)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hdiag i, hall i]
    _ = (z • (Pi.single i0 1 : Fin τ.rank → ℤ)) i0 •
          (∑ i, v i • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        calc v i • ((z • (Pi.single i0 1 : Fin τ.rank → ℤ)) i0 •
              (Pi.single i 1 : Fin τ.rank → ℤ))
            = (v i * (z • (Pi.single i0 1 : Fin τ.rank → ℤ)) i0) •
                (Pi.single i 1 : Fin τ.rank → ℤ) := by rw [← smul_smul]
          _ = ((z • (Pi.single i0 1 : Fin τ.rank → ℤ)) i0 * v i) •
                (Pi.single i 1 : Fin τ.rank → ℤ) := by rw [mul_comm]
          _ = (z • (Pi.single i0 1 : Fin τ.rank → ℤ)) i0 •
                (v i • (Pi.single i 1 : Fin τ.rank → ℤ)) := by rw [smul_smul]
    _ = (z • (Pi.single i0 1 : Fin τ.rank → ℤ)) i0 • v := by rw [pnx_sum_single]

private theorem pnx_card_center_eq_of_mulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) :
    Nat.card ↥(Subgroup.center G) = Nat.card ↥(Subgroup.center H) :=
  Nat.card_congr (Subgroup.centerCongr e).toEquiv

private theorem pnx_center_eq_bot_of_no_neg {τ : Tag}
    (hno : ¬ ∃ w : WeylGroup τ, ∀ v : Fin τ.rank → ℤ, w • v = -v) :
    Subgroup.center (WeylGroup τ) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun z hz => ?_
  obtain ⟨c, hc, hv⟩ := pnx_center_scalar hz
  rcases hc with hc | hc
  · refine ext_single fun i => ?_
    simp [hv, hc]
  · exact absurd ⟨z, fun v => by rw [hv, hc]; simp⟩ hno

private theorem pnx_center_eq_zpowers_of_neg {τ : Tag} {w : WeylGroup τ}
    (hw : ∀ v : Fin τ.rank → ℤ, w • v = -v) :
    Subgroup.center (WeylGroup τ) = Subgroup.zpowers w := by
  have hwmem : w ∈ Subgroup.center (WeylGroup τ) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact pnx_mul_comm_of_neg hw g
  refine le_antisymm ?_ (Subgroup.zpowers_le.mpr hwmem)
  intro z hz
  obtain ⟨c, hc, hv⟩ := pnx_center_scalar hz
  rcases hc with hc | hc
  · have hz1 : z = 1 := by
      refine ext_single fun i => ?_
      simp [hv, hc]
    rw [hz1]
    exact Subgroup.one_mem _
  · have hzw : z = w := by
      refine ext_single fun i => ?_
      simp [hv, hc, hw]
    rw [hzw]
    exact Subgroup.mem_zpowers w

private theorem pnx_sq_eq_one_of_neg {τ : Tag} {w : WeylGroup τ}
    (hw : ∀ v : Fin τ.rank → ℤ, w • v = -v) : w ^ 2 = 1 := by
  refine ext_single fun i => ?_
  rw [pow_two, mul_smul, hw, hw, neg_neg, one_smul]

private theorem pnx_center_card_two {τ : Tag}
    (hw : ∀ v : Fin τ.rank → ℤ, pnx_w τ • v = -v) :
    Nat.card ↥(Subgroup.center (WeylGroup τ)) = 2 := by
  have hne : pnx_w τ ≠ (1 : WeylGroup τ) := by
    intro h1
    have h2 := hw (Pi.single ⟨0, τ.rank_pos⟩ 1)
    rw [h1, one_smul] at h2
    have h3 := congrFun h2 ⟨0, τ.rank_pos⟩
    simp at h3
  rw [pnx_center_eq_zpowers_of_neg hw, Nat.card_zpowers]
  exact orderOf_eq_prime (pnx_sq_eq_one_of_neg hw) hne

private theorem pnx_ggIntCartan_E6 : GGIntCartan CoxeterMatrix.E₆ (Tag.cartan .E6) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i <;> decide
  · fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide

private theorem pnx_ggIntCartan_E7 : GGIntCartan CoxeterMatrix.E₇ (Tag.cartan .E7) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i <;> decide
  · fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide

private theorem pnx_ggIntCartan_E8 : GGIntCartan CoxeterMatrix.E₈ (Tag.cartan .E8) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i <;> decide
  · fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide

private theorem pnx_ggIntCartan_F4 : GGIntCartan CoxeterMatrix.F₄ (Tag.cartan .F4) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i <;> decide
  · fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide

private theorem pnx_ggIntCartan_G2 : GGIntCartan CoxeterMatrix.G₂ (Tag.cartan .G2) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i <;> decide
  · fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide

private theorem pnx_hmat_E6 :
    CoxeterMatrix.E₆ = coxeterMatrix (isFiniteType_cartan .E6) :=
  (coxeterMatrix_eq_of_ggIntCartan (isFiniteType_cartan .E6) pnx_ggIntCartan_E6).symm

private theorem pnx_hmat_E7 :
    CoxeterMatrix.E₇ = coxeterMatrix (isFiniteType_cartan .E7) :=
  (coxeterMatrix_eq_of_ggIntCartan (isFiniteType_cartan .E7) pnx_ggIntCartan_E7).symm

private theorem pnx_hmat_E8 :
    CoxeterMatrix.E₈ = coxeterMatrix (isFiniteType_cartan .E8) :=
  (coxeterMatrix_eq_of_ggIntCartan (isFiniteType_cartan .E8) pnx_ggIntCartan_E8).symm

private theorem pnx_hmat_F4 :
    CoxeterMatrix.F₄ = coxeterMatrix (isFiniteType_cartan .F4) :=
  (coxeterMatrix_eq_of_ggIntCartan (isFiniteType_cartan .F4) pnx_ggIntCartan_F4).symm

private theorem pnx_hmat_G2 :
    CoxeterMatrix.G₂ = coxeterMatrix (isFiniteType_cartan .G2) :=
  (coxeterMatrix_eq_of_ggIntCartan (isFiniteType_cartan .G2) pnx_ggIntCartan_G2).symm

private theorem pnx_neg_word {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4 ∨ τ = .G2)
    (v : Fin τ.rank → ℤ) : pnx_w τ • v = -v := by
  rcases hτ with rfl | rfl | rfl | rfl
  all_goals
    refine pnx_smul_eq_neg_of_single (fun i => ?_) v
    rw [pnx_w_smul]
    fin_cases i <;> decide +kernel

private theorem pnx_no_neg_one_E6 :
    ¬ ∃ w : WeylGroup Tag.E6, ∀ v : Fin Tag.E6.rank → ℤ, w • v = -v := by
  rintro ⟨w, hw⟩
  have hsingle : ∀ i, height (pnx_w .E6 • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) < 0 := by
    intro i
    rw [pnx_w_smul]
    fin_cases i <;> decide +kernel
  have hrev : ReversesSigns (pnx_w .E6) :=
    fun α hα hpos => height_smul_neg_of_forall_single hsingle hα hpos
  have hwrev : ReversesSigns w := by
    intro α hα hpos
    rw [hw α, height_neg]
    omega
  have heq : w = pnx_w .E6 := ReversesSigns.eq hwrev hrev
  have hnot : pnx_w .E6 • (Pi.single (⟨0, by decide⟩ : Fin Tag.E6.rank) 1 :
        Fin Tag.E6.rank → ℤ) ≠
      -(Pi.single (⟨0, by decide⟩ : Fin Tag.E6.rank) 1 : Fin Tag.E6.rank → ℤ) := by
    rw [pnx_w_smul]
    decide +kernel
  rw [heq] at hw
  exact hnot (hw _)

theorem ggCoxeterE6_center :
    Nat.card ↥(Subgroup.center CoxeterMatrix.E₆.Group) = 1 := by
  have hgroup : WeylGroup Tag.E6 ≃* CoxeterMatrix.E₆.Group :=
    MulEquiv.cast (M := fun A => A.Group) pnx_hmat_E6.symm
  rw [← pnx_card_center_eq_of_mulEquiv hgroup]
  have hbot : Subgroup.center (WeylGroup Tag.E6) = ⊥ :=
    pnx_center_eq_bot_of_no_neg pnx_no_neg_one_E6
  rw [hbot, Subgroup.card_bot]

theorem ggCoxeterE7_center : Nat.card ↥(Subgroup.center CoxeterMatrix.E₇.Group) = 2 := by
  have hgroup : WeylGroup Tag.E7 ≃* CoxeterMatrix.E₇.Group :=
    MulEquiv.cast (M := fun A => A.Group) pnx_hmat_E7.symm
  rw [← pnx_card_center_eq_of_mulEquiv hgroup]
  exact pnx_center_card_two (pnx_neg_word (Or.inl rfl))

theorem ggCoxeterE8_center : Nat.card ↥(Subgroup.center CoxeterMatrix.E₈.Group) = 2 := by
  have hgroup : WeylGroup Tag.E8 ≃* CoxeterMatrix.E₈.Group :=
    MulEquiv.cast (M := fun A => A.Group) pnx_hmat_E8.symm
  rw [← pnx_card_center_eq_of_mulEquiv hgroup]
  exact pnx_center_card_two (pnx_neg_word (Or.inr (Or.inl rfl)))

theorem ggCoxeterF4_center : Nat.card ↥(Subgroup.center CoxeterMatrix.F₄.Group) = 2 := by
  have hgroup : WeylGroup Tag.F4 ≃* CoxeterMatrix.F₄.Group :=
    MulEquiv.cast (M := fun A => A.Group) pnx_hmat_F4.symm
  rw [← pnx_card_center_eq_of_mulEquiv hgroup]
  exact pnx_center_card_two (pnx_neg_word (Or.inr (Or.inr (Or.inl rfl))))

theorem ggCoxeterG2_center : Nat.card ↥(Subgroup.center CoxeterMatrix.G₂.Group) = 2 := by
  have hgroup : WeylGroup Tag.G2 ≃* CoxeterMatrix.G₂.Group :=
    MulEquiv.cast (M := fun A => A.Group) pnx_hmat_G2.symm
  rw [← pnx_card_center_eq_of_mulEquiv hgroup]
  exact pnx_center_card_two (pnx_neg_word (Or.inr (Or.inr (Or.inr rfl))))

end CFSG.StandardType

end
