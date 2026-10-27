module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestInvQV
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalRoots
public import CFSG.LieType.Chevalley.HeightSeries
public import CFSG.LieType.Chevalley.BruhatCellFactorization
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
public import CFSG.LieType.Chevalley.RootCommutatorReduction

public section

namespace CFSG.StandardType.GGSixE6Two

open scoped IsMulCommutative

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint

private theorem e6ia_F2_eq_zero_or_one (c : F2) : c = 0 ∨ c = 1 := by
  have hK : Nat.card F2 = 2 := GaloisField.card 2 1 (by omega)
  have : Finite F2 := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype F2 := Fintype.ofFinite F2
  have h := FiniteField.pow_card c
  rw [← Nat.card_eq_fintype_card, hK, sq] at h
  have h' : c * (c - 1) = 0 := by rw [mul_sub, h, mul_one, sub_self]
  rcases mul_eq_zero.1 h' with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.1 h1)

private theorem e6ia_xr_mul_self
    (γ : Fin Tag.E6.rank → ℤ) : xr γ * xr γ = 1 := by
  apply Subtype.ext
  show pinnedX .E6 F2 γ 1 * pinnedX .E6 F2 γ 1 = 1
  rw [← pinnedX_add, show (1 : F2) + 1 = 0 by rw [one_add_one_eq_two, gf2_two], pinnedX_zero]

private theorem e6ia_xr_inv
    (γ : Fin Tag.E6.rank → ℤ) : (xr γ)⁻¹ = xr γ := by
  rw [inv_eq_iff_mul_eq_one]
  exact e6ia_xr_mul_self γ

private def e6ia_zList : List (Fin Tag.E6.rank → ℤ) :=
  [![0, -1, 0, -1, 0, 0], ![0, -1, 0, 0, 0, 0], ![0, 0, 1, 1, 1, 0], ![0, 0, 1, 1, 1, 1],
    ![1, 0, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 1], ![1, 1, 2, 2, 2, 1], ![1, 1, 2, 3, 2, 1]]

private def e6ia_zRt (i : Fin 8) : Fin Tag.E6.rank → ℤ := e6ia_zList.getD i.val 0

private theorem e6ia_zRt_injective : Function.Injective e6ia_zRt := by decide

private theorem e6ia_level_le_two
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β) :
    iform β lamE ≤ 2 := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E6)] at hβ
  obtain ⟨k, hk, rfl⟩ := hβ
  have hcheck : ((List.range Tag.E6.rootCertificate.roots.length).all (fun k =>
      decide (iform (Tag.E6.rootCertificate.root k) lamE ≤ 2))) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.1 hcheck k (List.mem_range.2 hk))

private theorem e6ia_level1_mem
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β)
    (hlev : iform β lamE = 1) : β ∈ mu1List ++ mu2List := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E6)] at hβ
  obtain ⟨k, hk, rfl⟩ := hβ
  have hcheck : ((List.range Tag.E6.rootCertificate.roots.length).all (fun k =>
      !(decide (iform (Tag.E6.rootCertificate.root k) lamE = 1)) ||
        decide ((Tag.E6.rootCertificate.root k) ∈ (mu1List ++ mu2List)))) = true := by decide
  have := List.all_eq_true.1 hcheck k (List.mem_range.2 hk)
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
  rcases this with h | h
  · exact absurd hlev (of_decide_eq_false h)
  · exact h

private theorem e6ia_level1_exists
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β)
    (hlev : iform β lamE = 1) : ∃ i : Fin 16, l1Root i = β := by
  have hmem := e6ia_level1_mem hβ hlev
  rw [List.mem_iff_get] at hmem
  obtain ⟨i, hi⟩ := hmem
  refine ⟨⟨i.val, ?_⟩, ?_⟩
  · have hlen : (mu1List ++ mu2List).length = 16 := rfl
    omega
  · simp only [l1Root]
    rw [List.getD_eq_getElem _ _ i.isLt]
    exact hi

private theorem e6ia_level2_mem
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β)
    (hlev : iform β lamE = 2) : β ∈ e6ia_zList := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E6)] at hβ
  obtain ⟨k, hk, rfl⟩ := hβ
  have hcheck : ((List.range Tag.E6.rootCertificate.roots.length).all (fun k =>
      !(decide (iform (Tag.E6.rootCertificate.root k) lamE = 2)) ||
        decide ((Tag.E6.rootCertificate.root k) ∈ e6ia_zList))) = true := by decide
  have := List.all_eq_true.1 hcheck k (List.mem_range.2 hk)
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
  rcases this with h | h
  · exact absurd hlev (of_decide_eq_false h)
  · exact h

private theorem e6ia_level2_exists
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β)
    (hlev : iform β lamE = 2) : ∃ i : Fin 8, e6ia_zRt i = β := by
  have hmem := e6ia_level2_mem hβ hlev
  rw [List.mem_iff_get] at hmem
  obtain ⟨i, hi⟩ := hmem
  refine ⟨⟨i.val, ?_⟩, ?_⟩
  · have hlen : e6ia_zList.length = 8 := rfl
    omega
  · simp only [e6ia_zRt]
    rw [List.getD_eq_getElem _ _ i.isLt]
    exact hi

private noncomputable def e6ia_zElt
    (i : Fin 8) : EC :=
  xr (e6ia_zRt i)

private theorem e6ia_zRt_mem_zRoots
    (i : Fin 8) : e6ia_zRt i ∈ zRoots := by
  fin_cases i <;>
    exact ⟨by rw [← CFSG.LieType.Chevalley.RootOps.isRootB_iff]; decide, by decide⟩

private theorem e6ia_zElt_mem_z0E
    (i : Fin 8) : e6ia_zElt i ∈ z0E := by
  rw [show z0E = (rootSpan .E6 F2 zRoots).subgroupOf (adjointGroup .E6 F2) from rfl,
    Subgroup.mem_subgroupOf]
  simpa only [e6ia_zElt, xr] using pinnedX_mem_rootSpan (e6ia_zRt_mem_zRoots i) (1 : F2)

private theorem e6ia_zElt_mul_self
    (i : Fin 8) : e6ia_zElt i * e6ia_zElt i = 1 :=
  by simpa only [e6ia_zElt] using e6ia_xr_mul_self (e6ia_zRt i)

private theorem e6ia_zElt_comm
    (i j : Fin 8) :
    e6ia_zElt i * e6ia_zElt j = e6ia_zElt j * e6ia_zElt i := by
  exact (Subgroup.mem_centralizer_iff.1
    (z0E_central (e6ia_zElt_mem_z0E i)) (e6ia_zElt j)
    (z0E_le_qE (e6ia_zElt_mem_z0E j))).symm

private theorem e6ia_rootSpan_conj_mem
    (γ : Fin Tag.E6.rank → ℤ) (hγ : IsRoot .E6 γ)
    (S : Set (Fin Tag.E6.rank → ℤ)) (hS : ∀ α ∈ S, IsRoot .E6 α)
    (hSne : ∀ α ∈ S, γ ≠ α) (hSne' : ∀ α ∈ S, γ ≠ -α)
    (hSadd : ∀ α ∈ S, ∀ _ : IsRoot .E6 (γ + α), γ + α ∈ S) {x : ModGL .E6 F2}
    (hx : x ∈ rootSpan .E6 F2 S) :
    pinnedX .E6 F2 γ 1 * x * (pinnedX .E6 F2 γ 1)⁻¹ ∈ rootSpan .E6 F2 S := by
  rw [rootSpan_eq_closure F2 S] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, c, rfl⟩ := hy
    have hne : γ ≠ α := hSne α hα
    have hne' : γ ≠ -α := hSne' α hα
    by_cases hr : IsRoot .E6 (γ + α)
    · rw [CFSG.LieType.Chevalley.EvenOddRadical.pinnedX_conj_of_isRoot (Or.inr (Or.inl rfl))
        gf2_two hγ (hS α hα) hne hne' hr 1 c]
      exact mul_mem (pinnedX_mem_rootSpan (hSadd α hα hr) (1 * c))
        (pinnedX_mem_rootSpan hα c)
    · rw [CFSG.LieType.Chevalley.EvenOddRadical.pinnedX_conj_of_not (Or.inr (Or.inl rfl))
        hγ (hS α hα) hne hne' hr 1 c]
      exact pinnedX_mem_rootSpan hα c
  | one => rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  | mul y z hy hz ihy ihz =>
    rw [show pinnedX .E6 F2 γ 1 * (y * z) * (pinnedX .E6 F2 γ 1)⁻¹ =
        (pinnedX .E6 F2 γ 1 * y * (pinnedX .E6 F2 γ 1)⁻¹) *
          (pinnedX .E6 F2 γ 1 * z * (pinnedX .E6 F2 γ 1)⁻¹) by group]
    exact mul_mem ihy ihz
  | inv y hy ihy =>
    rw [show pinnedX .E6 F2 γ 1 * y⁻¹ * (pinnedX .E6 F2 γ 1)⁻¹ =
        (pinnedX .E6 F2 γ 1 * y * (pinnedX .E6 F2 γ 1)⁻¹)⁻¹ by group]
    exact inv_mem ihy

private theorem e6ia_qRoots_add
    {γ α : Fin Tag.E6.rank → ℤ} (hγ0 : iform γ lamE = 0) (hα : α ∈ qRoots)
    (h : IsRoot .E6 (γ + α)) : γ + α ∈ qRoots :=
  ⟨h, by rw [iform_add_left, hγ0, zero_add]; exact hα.2⟩

private theorem e6ia_zRoots_add
    {γ α : Fin Tag.E6.rank → ℤ} (hγ0 : iform γ lamE = 0) (hα : α ∈ zRoots)
    (h : IsRoot .E6 (γ + α)) : γ + α ∈ zRoots :=
  ⟨h, by rw [iform_add_left, hγ0, zero_add]; exact hα.2⟩

private theorem e6ia_qRoots_ne 
    {γ α : Fin Tag.E6.rank → ℤ} (hγ0 : iform γ lamE = 0) (hα : α ∈ qRoots) : γ ≠ α := by
  intro h; rw [h] at hγ0
  have hpos : 0 < iform α lamE := hα.2
  omega

private theorem e6ia_qRoots_ne_neg 
    {γ α : Fin Tag.E6.rank → ℤ} (hγ0 : iform γ lamE = 0) (hα : α ∈ qRoots) : γ ≠ -α := by
  intro h
  have h3 : iform γ lamE = iform (-α) lamE := congrArg (fun v => iform v lamE) h
  rw [hγ0, iform_neg_left] at h3
  have hpos : 0 < iform α lamE := hα.2
  omega

private theorem e6ia_zRoots_ne 
    {γ α : Fin Tag.E6.rank → ℤ} (hγ0 : iform γ lamE = 0) (hα : α ∈ zRoots) : γ ≠ α := by
  intro h; rw [h] at hγ0
  have hpos : iform α lamE = 2 := hα.2
  omega

private theorem e6ia_zRoots_ne_neg 
    {γ α : Fin Tag.E6.rank → ℤ} (hγ0 : iform γ lamE = 0) (hα : α ∈ zRoots) : γ ≠ -α := by
  intro h
  have h3 : iform γ lamE = iform (-α) lamE := congrArg (fun v => iform v lamE) h
  rw [hγ0, iform_neg_left] at h3
  have hpos : iform α lamE = 2 := hα.2
  omega

private theorem e6ia_qE_conj_mem
    (γ : Fin Tag.E6.rank → ℤ) (hγ : IsRoot .E6 γ) (hγ0 : iform γ lamE = 0) {q : EC}
    (hq : q ∈ qE) : xr γ * q * (xr γ)⁻¹ ∈ qE := by
  rw [show qE = (rootSpan .E6 F2 qRoots).subgroupOf (adjointGroup .E6 F2) from rfl,
    Subgroup.mem_subgroupOf] at hq ⊢
  simpa only [xr, Subgroup.coe_mul, Subgroup.coe_inv] using
    e6ia_rootSpan_conj_mem γ hγ qRoots (fun _ h => h.1)
      (fun _ h => e6ia_qRoots_ne hγ0 h) (fun _ h => e6ia_qRoots_ne_neg hγ0 h)
      (fun _ h hh => e6ia_qRoots_add hγ0 h hh) hq

private theorem e6ia_z0E_conj_mem
    (γ : Fin Tag.E6.rank → ℤ) (hγ : IsRoot .E6 γ) (hγ0 : iform γ lamE = 0) {q : EC}
    (hq : q ∈ z0E) : xr γ * q * (xr γ)⁻¹ ∈ z0E := by
  rw [show z0E = (rootSpan .E6 F2 zRoots).subgroupOf (adjointGroup .E6 F2) from rfl,
    Subgroup.mem_subgroupOf] at hq ⊢
  simpa only [xr, Subgroup.coe_mul, Subgroup.coe_inv] using
    e6ia_rootSpan_conj_mem γ hγ zRoots (fun _ h => h.1)
      (fun _ h => e6ia_zRoots_ne hγ0 h) (fun _ h => e6ia_zRoots_ne_neg hγ0 h)
      (fun _ h hh => e6ia_zRoots_add hγ0 h hh) hq

@[expose] noncomputable def e6TwoRestInvWord :
    Fin 14 → EC :=
  ![xr ![1, 2, 2, 3, 2, 1],
    xr ![-1, -2, -2, -3, -2, -1],
    xr ![0, 0, 0, 1, 0, 0],
    xr ![0, 0, 0, -1, 0, 0],
    xr ![1, 0, 0, 0, 0, 0] * xr ![-1, 0, 0, 0, 0, 0],
    xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1],
    xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1],
    xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1],
    xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1],
    xr ![0, 0, 0, 0, 0, 1] * xr ![0, 0, 0, 0, 0, -1],
    xr ![1, 1, 1, 2, 1, 1] * xr ![0, 1, 1, 2, 1, 0],
    xr ![1, 1, 1, 1, 1, 1] * xr ![0, 1, 1, 1, 1, 0],
    xr ![0, -1, -1, -1, -1, 0] * xr ![-1, -1, -1, -1, -1, -1],
    xr ![0, -1, -1, -2, -1, 0] * xr ![-1, -1, -1, -2, -1, -1]]

private theorem e6ia_z0E_comm
    (a b : ↥z0E) : a * b = b * a :=
  Subtype.ext (Subgroup.mem_centralizer_iff.1 (z0E_central a.2) (b : EC)
    (z0E_le_qE b.2)).symm

private noncomputable instance e6ia_z0E_commMonoid :
    CommMonoid ↥z0E :=
  { toMonoid := inferInstance, mul_comm := e6ia_z0E_comm }

private noncomputable def e6ia_zPow
    (v : Fin 8 → ZMod 2) : EC :=
  ↑(∏ i : Fin 8, (⟨e6ia_zElt i, e6ia_zElt_mem_z0E i⟩ : ↥z0E) ^ (v i).val)

private theorem e6ia_zPow_zero :
    e6ia_zPow 0 = 1 := by
  simp [e6ia_zPow]

private theorem e6ia_zPow_single
    (i : Fin 8) : e6ia_zPow (Pi.single i 1) = e6ia_zElt i := by
  rw [e6ia_zPow]
  rw [Finset.prod_eq_single i]
  · rw [Pi.single_eq_same, ZMod.val_one 2, pow_one]
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem e6ia_zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c; decide

private theorem e6ia_zmod2_val_zero : (0 : ZMod 2).val = 0 := rfl
private theorem e6ia_zmod2_val_one : (1 : ZMod 2).val = 1 := rfl
private theorem e6ia_zmod2_val_two : ((1 : ZMod 2) + 1).val = 0 := rfl

private theorem e6ia_pow_val_add
    (i : Fin 8) (a b : ZMod 2) :
    e6ia_zElt i ^ ((a + b).val) = e6ia_zElt i ^ a.val * e6ia_zElt i ^ b.val := by
  rcases e6ia_zmod2_eq_zero_or_one a with rfl | rfl <;>
    rcases e6ia_zmod2_eq_zero_or_one b with rfl | rfl
  · simp only [add_zero, zero_add, e6ia_zmod2_val_zero, pow_zero, mul_one]
  · simp only [zero_add, e6ia_zmod2_val_zero, e6ia_zmod2_val_one, pow_zero, pow_one, one_mul]
  · simp only [add_zero, e6ia_zmod2_val_zero, e6ia_zmod2_val_one, pow_zero, pow_one, mul_one]
  · rw [e6ia_zmod2_val_two, e6ia_zmod2_val_one, pow_zero, pow_one, e6ia_zElt_mul_self]

private theorem e6ia_zPow_add
    (v w : Fin 8 → ZMod 2) :
    e6ia_zPow (v + w) = e6ia_zPow v * e6ia_zPow w := by
  rw [e6ia_zPow, e6ia_zPow, e6ia_zPow, ← Subgroup.coe_mul]
  congr 1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_mul]
  rw [Pi.add_apply, e6ia_pow_val_add]

private noncomputable def e6ia_zMat (γ : Fin Tag.E6.rank → ℤ) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  fun i j => (if i = j then 1 else 0) + (if e6ia_zRt i = e6ia_zRt j + γ then 1 else 0)

private theorem e6ia_conj_zElt
    (γ : Fin Tag.E6.rank → ℤ) (hγ : IsRoot .E6 γ) (hγ0 : iform γ lamE = 0) (i : Fin 8) :
    xr γ * e6ia_zElt i * (xr γ)⁻¹ =
      e6ia_zPow (Matrix.mulVec (e6ia_zMat γ) (Pi.single i 1)) := by
  have hzi : IsRoot .E6 (e6ia_zRt i) := (e6ia_zRt_mem_zRoots i).1
  have hzi2 : iform (e6ia_zRt i) lamE = 2 := (e6ia_zRt_mem_zRoots i).2
  have hne : γ ≠ e6ia_zRt i := by intro h; rw [h] at hγ0; omega
  have hne' : γ ≠ -e6ia_zRt i := by
    intro h
    have h3 : iform γ lamE = iform (-(e6ia_zRt i)) lamE := congrArg (fun v => iform v lamE) h
    rw [hγ0, iform_neg_left] at h3
    omega
  by_cases hr : IsRoot .E6 (γ + e6ia_zRt i)
  · have hlev : iform (γ + e6ia_zRt i) lamE = 2 := by
      rw [iform_add_left, hγ0, zero_add]; exact hzi2
    obtain ⟨j, hj⟩ := e6ia_level2_exists hr hlev
    have hj' : e6ia_zRt j = e6ia_zRt i + γ := by rw [hj, add_comm]
    have hcol : Matrix.mulVec (e6ia_zMat γ) (Pi.single i 1) = Pi.single i 1 + Pi.single j 1 := by
      rw [Matrix.mulVec_single_one]
      funext i'
      have hiff : (e6ia_zRt i' = e6ia_zRt i + γ) ↔ (i' = j) := by
        constructor
        · intro h; exact e6ia_zRt_injective (h.trans hj'.symm)
        · intro h; rw [h]; exact hj'
      simp only [e6ia_zMat, Pi.add_apply, Pi.single_apply, Matrix.col_apply, hiff]
    rw [hcol, e6ia_zPow_add, e6ia_zPow_single, e6ia_zPow_single]
    apply Subtype.ext
    show pinnedX .E6 F2 γ 1 * pinnedX .E6 F2 (e6ia_zRt i) 1 * (pinnedX .E6 F2 γ 1)⁻¹ =
      pinnedX .E6 F2 (e6ia_zRt i) 1 * pinnedX .E6 F2 (e6ia_zRt j) 1
    rw [CFSG.LieType.Chevalley.EvenOddRadical.pinnedX_conj_of_isRoot (Or.inr (Or.inl rfl)) gf2_two
      hγ hzi hne hne' hr 1 1]
    simp only [one_mul]
    rw [← hj]
    exact congrArg Subtype.val (e6ia_zElt_comm j i)
  · have hcol : Matrix.mulVec (e6ia_zMat γ) (Pi.single i 1) = Pi.single i 1 := by
      rw [Matrix.mulVec_single_one]
      funext i'
      have h2 : ¬ (e6ia_zRt i' = e6ia_zRt i + γ) := by
        intro h
        apply hr
        rw [add_comm γ (e6ia_zRt i), ← h]
        exact (e6ia_zRt_mem_zRoots i').1
      simp only [e6ia_zMat, Pi.add_apply, Pi.single_apply, Matrix.col_apply, h2, if_false, add_zero]
    rw [hcol, e6ia_zPow_single]
    apply Subtype.ext
    show pinnedX .E6 F2 γ 1 * pinnedX .E6 F2 (e6ia_zRt i) 1 * (pinnedX .E6 F2 γ 1)⁻¹ =
      pinnedX .E6 F2 (e6ia_zRt i) 1
    exact CFSG.LieType.Chevalley.EvenOddRadical.pinnedX_conj_of_not (Or.inr (Or.inl rfl))
      hγ hzi hne hne' hr (1 : F2) (1 : F2)

private theorem e6ia_sum_single_supp (v : Fin 8 → ZMod 2) :
    (∑ i ∈ Finset.univ.filter (fun i => v i ≠ 0), Pi.single i 1) = v := by
  funext j
  rw [Finset.sum_apply]
  by_cases hj : v j = 0
  · rw [hj]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Finset.mem_filter] at hi
    simp only [Pi.single_apply]
    rw [if_neg]
    intro h; exact hi.2 (h ▸ hj)
  · have hvj : v j = 1 := (e6ia_zmod2_eq_zero_or_one (v j)).resolve_left hj
    rw [hvj]
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same]
    · intro i _ hij
      simp only [Pi.single_apply]
      rw [if_neg]
      intro h; exact hij h.symm
    · intro h; exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ j, hj⟩) h

private theorem e6ia_conj_zPow_supp
    (γ : Fin Tag.E6.rank → ℤ) (hγ : IsRoot .E6 γ) (hγ0 : iform γ lamE = 0)
    (s : Finset (Fin 8)) :
    xr γ * e6ia_zPow (∑ i ∈ s, Pi.single i 1) * (xr γ)⁻¹ =
      e6ia_zPow (Matrix.mulVec (e6ia_zMat γ) (∑ i ∈ s, Pi.single i 1)) := by
  induction s using Finset.induction with
  | empty => simp [e6ia_zPow_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    rw [Matrix.mulVec_add, e6ia_zPow_add, e6ia_zPow_add, e6ia_zPow_single]
    rw [show xr γ * (e6ia_zElt i * e6ia_zPow (∑ j ∈ s, Pi.single j 1)) * (xr γ)⁻¹ =
        (xr γ * e6ia_zElt i * (xr γ)⁻¹) *
          (xr γ * e6ia_zPow (∑ j ∈ s, Pi.single j 1) * (xr γ)⁻¹) by group]
    rw [e6ia_conj_zElt γ hγ hγ0 i, ih]

private theorem e6ia_conj_zPow
    (γ : Fin Tag.E6.rank → ℤ) (hγ : IsRoot .E6 γ) (hγ0 : iform γ lamE = 0)
    (v : Fin 8 → ZMod 2) :
    xr γ * e6ia_zPow v * (xr γ)⁻¹ =
      e6ia_zPow (Matrix.mulVec (e6ia_zMat γ) v) := by
  rw [← e6ia_sum_single_supp v]
  exact e6ia_conj_zPow_supp γ hγ hγ0 _

private def e6ia_vR1 : Fin 8 → ZMod 2 := Pi.single 4 1 + Pi.single 3 1

private def e6ia_vR2 : Fin 8 → ZMod 2 := Pi.single 5 1 + Pi.single 2 1 + Pi.single 3 1

private theorem e6ia_zPow_vR1 :
    e6ia_zPow e6ia_vR1 = rOne 0 2 := by
  rw [e6ia_vR1, e6ia_zPow_add, e6ia_zPow_single, e6ia_zPow_single]
  rfl

private theorem e6ia_zPow_vR2 :
    e6ia_zPow e6ia_vR2 = rOmega 0 2 := by
  rw [e6ia_vR2, e6ia_zPow_add, e6ia_zPow_add, e6ia_zPow_single, e6ia_zPow_single,
    e6ia_zPow_single]
  rfl

private theorem e6ia_conj_mem_rE_of_gens
    (g : EC) (hg : ∀ y ∈ ({rOne 0 2, rOmega 0 2} : Set EC), g * y * g⁻¹ ∈ rE)
    {h : EC} (hh : h ∈ rE) : g * h * g⁻¹ ∈ rE := by
  rw [show rE = Subgroup.closure ({rOne 0 2, rOmega 0 2} : Set EC) from rfl] at hh
  induction hh using Subgroup.closure_induction with
  | mem y hy => exact hg y hy
  | one => rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  | mul y z hy hz ihy ihz =>
    rw [show g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) by group]
    exact mul_mem ihy ihz
  | inv y hy ihy =>
    rw [show g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ by group]
    exact inv_mem ihy

theorem invWord_mem_normalizer_rE
    (k : Fin 14) : e6TwoRestInvWord k ∈ Subgroup.normalizer (rE : Set EC) := by
  fin_cases k
  · show xr ![1, 2, 2, 3, 2, 1] ∈ Subgroup.normalizer (rE : Set EC)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · refine e6ia_conj_mem_rE_of_gens (xr ![1, 2, 2, 3, 2, 1]) ?_
      intro y hy
      rcases hy with rfl | rfl
      ·
        rw [← e6ia_zPow_vR1, e6ia_conj_zPow ![1, 2, 2, 3, 2, 1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
        rw [show Matrix.mulVec (e6ia_zMat ![1, 2, 2, 3, 2, 1]) e6ia_vR1 = e6ia_vR1 from by decide]
        rw [e6ia_zPow_vR1]
        exact Subgroup.subset_closure (Or.inl rfl)
      ·
        rw [← e6ia_zPow_vR2, e6ia_conj_zPow ![1, 2, 2, 3, 2, 1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
        rw [show Matrix.mulVec (e6ia_zMat ![1, 2, 2, 3, 2, 1]) e6ia_vR2 = e6ia_vR2 from by decide]
        rw [e6ia_zPow_vR2]
        exact Subgroup.subset_closure (Or.inr rfl)
    · intro hh
      have h2 := e6ia_conj_mem_rE_of_gens (xr ![1, 2, 2, 3, 2, 1])⁻¹ ?_ hh
      · rwa [show (xr ![1, 2, 2, 3, 2, 1])⁻¹ * ((xr ![1, 2, 2, 3, 2, 1]) * h * (xr ![1, 2, 2, 3, 2, 1])⁻¹) * (xr ![1, 2, 2, 3, 2, 1])⁻¹⁻¹ = h by group] at h2
      · intro y hy
        rcases hy with rfl | rfl
        ·
          rw [e6ia_xr_inv ![1, 2, 2, 3, 2, 1]]
          rw [← e6ia_zPow_vR1, e6ia_conj_zPow ![1, 2, 2, 3, 2, 1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
          rw [show Matrix.mulVec (e6ia_zMat ![1, 2, 2, 3, 2, 1]) e6ia_vR1 = e6ia_vR1 from by decide]
          rw [e6ia_zPow_vR1]
          exact Subgroup.subset_closure (Or.inl rfl)
        ·
          rw [e6ia_xr_inv ![1, 2, 2, 3, 2, 1]]
          rw [← e6ia_zPow_vR2, e6ia_conj_zPow ![1, 2, 2, 3, 2, 1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
          rw [show Matrix.mulVec (e6ia_zMat ![1, 2, 2, 3, 2, 1]) e6ia_vR2 = e6ia_vR2 from by decide]
          rw [e6ia_zPow_vR2]
          exact Subgroup.subset_closure (Or.inr rfl)
  · show xr ![-1, -2, -2, -3, -2, -1] ∈ Subgroup.normalizer (rE : Set EC)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · refine e6ia_conj_mem_rE_of_gens (xr ![-1, -2, -2, -3, -2, -1]) ?_
      intro y hy
      rcases hy with rfl | rfl
      ·
        rw [← e6ia_zPow_vR1, e6ia_conj_zPow ![-1, -2, -2, -3, -2, -1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
        rw [show Matrix.mulVec (e6ia_zMat ![-1, -2, -2, -3, -2, -1]) e6ia_vR1 = e6ia_vR1 from by decide]
        rw [e6ia_zPow_vR1]
        exact Subgroup.subset_closure (Or.inl rfl)
      ·
        rw [← e6ia_zPow_vR2, e6ia_conj_zPow ![-1, -2, -2, -3, -2, -1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
        rw [show Matrix.mulVec (e6ia_zMat ![-1, -2, -2, -3, -2, -1]) e6ia_vR2 = e6ia_vR2 from by decide]
        rw [e6ia_zPow_vR2]
        exact Subgroup.subset_closure (Or.inr rfl)
    · intro hh
      have h2 := e6ia_conj_mem_rE_of_gens (xr ![-1, -2, -2, -3, -2, -1])⁻¹ ?_ hh
      · rwa [show (xr ![-1, -2, -2, -3, -2, -1])⁻¹ * ((xr ![-1, -2, -2, -3, -2, -1]) * h * (xr ![-1, -2, -2, -3, -2, -1])⁻¹) * (xr ![-1, -2, -2, -3, -2, -1])⁻¹⁻¹ = h by group] at h2
      · intro y hy
        rcases hy with rfl | rfl
        ·
          rw [e6ia_xr_inv ![-1, -2, -2, -3, -2, -1]]
          rw [← e6ia_zPow_vR1, e6ia_conj_zPow ![-1, -2, -2, -3, -2, -1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
          rw [show Matrix.mulVec (e6ia_zMat ![-1, -2, -2, -3, -2, -1]) e6ia_vR1 = e6ia_vR1 from by decide]
          rw [e6ia_zPow_vR1]
          exact Subgroup.subset_closure (Or.inl rfl)
        ·
          rw [e6ia_xr_inv ![-1, -2, -2, -3, -2, -1]]
          rw [← e6ia_zPow_vR2, e6ia_conj_zPow ![-1, -2, -2, -3, -2, -1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
          rw [show Matrix.mulVec (e6ia_zMat ![-1, -2, -2, -3, -2, -1]) e6ia_vR2 = e6ia_vR2 from by decide]
          rw [e6ia_zPow_vR2]
          exact Subgroup.subset_closure (Or.inr rfl)
  · show xr ![0, 0, 0, 1, 0, 0] ∈ Subgroup.normalizer (rE : Set EC)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · refine e6ia_conj_mem_rE_of_gens (xr ![0, 0, 0, 1, 0, 0]) ?_
      intro y hy
      rcases hy with rfl | rfl
      ·
        rw [← e6ia_zPow_vR1, e6ia_conj_zPow ![0, 0, 0, 1, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
        rw [show Matrix.mulVec (e6ia_zMat ![0, 0, 0, 1, 0, 0]) e6ia_vR1 = e6ia_vR1 from by decide]
        rw [e6ia_zPow_vR1]
        exact Subgroup.subset_closure (Or.inl rfl)
      ·
        rw [← e6ia_zPow_vR2, e6ia_conj_zPow ![0, 0, 0, 1, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
        rw [show Matrix.mulVec (e6ia_zMat ![0, 0, 0, 1, 0, 0]) e6ia_vR2 = e6ia_vR2 from by decide]
        rw [e6ia_zPow_vR2]
        exact Subgroup.subset_closure (Or.inr rfl)
    · intro hh
      have h2 := e6ia_conj_mem_rE_of_gens (xr ![0, 0, 0, 1, 0, 0])⁻¹ ?_ hh
      · rwa [show (xr ![0, 0, 0, 1, 0, 0])⁻¹ * ((xr ![0, 0, 0, 1, 0, 0]) * h * (xr ![0, 0, 0, 1, 0, 0])⁻¹) * (xr ![0, 0, 0, 1, 0, 0])⁻¹⁻¹ = h by group] at h2
      · intro y hy
        rcases hy with rfl | rfl
        ·
          rw [e6ia_xr_inv ![0, 0, 0, 1, 0, 0]]
          rw [← e6ia_zPow_vR1, e6ia_conj_zPow ![0, 0, 0, 1, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
          rw [show Matrix.mulVec (e6ia_zMat ![0, 0, 0, 1, 0, 0]) e6ia_vR1 = e6ia_vR1 from by decide]
          rw [e6ia_zPow_vR1]
          exact Subgroup.subset_closure (Or.inl rfl)
        ·
          rw [e6ia_xr_inv ![0, 0, 0, 1, 0, 0]]
          rw [← e6ia_zPow_vR2, e6ia_conj_zPow ![0, 0, 0, 1, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
          rw [show Matrix.mulVec (e6ia_zMat ![0, 0, 0, 1, 0, 0]) e6ia_vR2 = e6ia_vR2 from by decide]
          rw [e6ia_zPow_vR2]
          exact Subgroup.subset_closure (Or.inr rfl)
  · show xr ![0, 0, 0, -1, 0, 0] ∈ Subgroup.normalizer (rE : Set EC)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · refine e6ia_conj_mem_rE_of_gens (xr ![0, 0, 0, -1, 0, 0]) ?_
      intro y hy
      rcases hy with rfl | rfl
      ·
        rw [← e6ia_zPow_vR1, e6ia_conj_zPow ![0, 0, 0, -1, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
        rw [show Matrix.mulVec (e6ia_zMat ![0, 0, 0, -1, 0, 0]) e6ia_vR1 = e6ia_vR1 from by decide]
        rw [e6ia_zPow_vR1]
        exact Subgroup.subset_closure (Or.inl rfl)
      ·
        rw [← e6ia_zPow_vR2, e6ia_conj_zPow ![0, 0, 0, -1, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
        rw [show Matrix.mulVec (e6ia_zMat ![0, 0, 0, -1, 0, 0]) e6ia_vR2 = e6ia_vR2 from by decide]
        rw [e6ia_zPow_vR2]
        exact Subgroup.subset_closure (Or.inr rfl)
    · intro hh
      have h2 := e6ia_conj_mem_rE_of_gens (xr ![0, 0, 0, -1, 0, 0])⁻¹ ?_ hh
      · rwa [show (xr ![0, 0, 0, -1, 0, 0])⁻¹ * ((xr ![0, 0, 0, -1, 0, 0]) * h * (xr ![0, 0, 0, -1, 0, 0])⁻¹) * (xr ![0, 0, 0, -1, 0, 0])⁻¹⁻¹ = h by group] at h2
      · intro y hy
        rcases hy with rfl | rfl
        ·
          rw [e6ia_xr_inv ![0, 0, 0, -1, 0, 0]]
          rw [← e6ia_zPow_vR1, e6ia_conj_zPow ![0, 0, 0, -1, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
          rw [show Matrix.mulVec (e6ia_zMat ![0, 0, 0, -1, 0, 0]) e6ia_vR1 = e6ia_vR1 from by decide]
          rw [e6ia_zPow_vR1]
          exact Subgroup.subset_closure (Or.inl rfl)
        ·
          rw [e6ia_xr_inv ![0, 0, 0, -1, 0, 0]]
          rw [← e6ia_zPow_vR2, e6ia_conj_zPow ![0, 0, 0, -1, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
          rw [show Matrix.mulVec (e6ia_zMat ![0, 0, 0, -1, 0, 0]) e6ia_vR2 = e6ia_vR2 from by decide]
          rw [e6ia_zPow_vR2]
          exact Subgroup.subset_closure (Or.inr rfl)
  · show xr ![1, 0, 0, 0, 0, 0] * xr ![-1, 0, 0, 0, 0, 0] ∈ Subgroup.normalizer (rE : Set EC)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · refine e6ia_conj_mem_rE_of_gens (xr ![1, 0, 0, 0, 0, 0] * xr ![-1, 0, 0, 0, 0, 0]) ?_
      intro y hy
      rcases hy with rfl | rfl
      ·
        rw [← e6ia_zPow_vR1]
        rw [show (xr ![1, 0, 0, 0, 0, 0] * xr ![-1, 0, 0, 0, 0, 0]) * e6ia_zPow e6ia_vR1 * (xr ![1, 0, 0, 0, 0, 0] * xr ![-1, 0, 0, 0, 0, 0])⁻¹ =
            xr ![1, 0, 0, 0, 0, 0] * (xr ![-1, 0, 0, 0, 0, 0] * e6ia_zPow e6ia_vR1 * (xr ![-1, 0, 0, 0, 0, 0])⁻¹) * (xr ![1, 0, 0, 0, 0, 0])⁻¹ by group]
        rw [e6ia_conj_zPow ![-1, 0, 0, 0, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
        rw [e6ia_conj_zPow ![1, 0, 0, 0, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
        rw [show Matrix.mulVec (e6ia_zMat ![1, 0, 0, 0, 0, 0]) (Matrix.mulVec (e6ia_zMat ![-1, 0, 0, 0, 0, 0]) e6ia_vR1) = e6ia_vR2 from by decide]
        rw [e6ia_zPow_vR2]
        exact Subgroup.subset_closure (Or.inr rfl)
      ·
        rw [← e6ia_zPow_vR2]
        rw [show (xr ![1, 0, 0, 0, 0, 0] * xr ![-1, 0, 0, 0, 0, 0]) * e6ia_zPow e6ia_vR2 * (xr ![1, 0, 0, 0, 0, 0] * xr ![-1, 0, 0, 0, 0, 0])⁻¹ =
            xr ![1, 0, 0, 0, 0, 0] * (xr ![-1, 0, 0, 0, 0, 0] * e6ia_zPow e6ia_vR2 * (xr ![-1, 0, 0, 0, 0, 0])⁻¹) * (xr ![1, 0, 0, 0, 0, 0])⁻¹ by group]
        rw [e6ia_conj_zPow ![-1, 0, 0, 0, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
        rw [e6ia_conj_zPow ![1, 0, 0, 0, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
        rw [show Matrix.mulVec (e6ia_zMat ![1, 0, 0, 0, 0, 0]) (Matrix.mulVec (e6ia_zMat ![-1, 0, 0, 0, 0, 0]) e6ia_vR2) = e6ia_vR1 + e6ia_vR2 from by decide]
        rw [e6ia_zPow_add, e6ia_zPow_vR1, e6ia_zPow_vR2]
        exact mul_mem (Subgroup.subset_closure (Or.inl rfl)) (Subgroup.subset_closure (Or.inr rfl))
    · intro hh
      have h2 := e6ia_conj_mem_rE_of_gens (xr ![1, 0, 0, 0, 0, 0] * xr ![-1, 0, 0, 0, 0, 0])⁻¹ ?_ hh
      · rwa [show (xr ![1, 0, 0, 0, 0, 0] * xr ![-1, 0, 0, 0, 0, 0])⁻¹ * ((xr ![1, 0, 0, 0, 0, 0] * xr ![-1, 0, 0, 0, 0, 0]) * h * (xr ![1, 0, 0, 0, 0, 0] * xr ![-1, 0, 0, 0, 0, 0])⁻¹) * (xr ![1, 0, 0, 0, 0, 0] * xr ![-1, 0, 0, 0, 0, 0])⁻¹⁻¹ = h by group] at h2
      · intro y hy
        rcases hy with rfl | rfl
        ·
          rw [show (xr ![1, 0, 0, 0, 0, 0] * xr ![-1, 0, 0, 0, 0, 0])⁻¹ = xr ![-1, 0, 0, 0, 0, 0] * xr ![1, 0, 0, 0, 0, 0] by
            rw [mul_inv_rev, e6ia_xr_inv ![-1, 0, 0, 0, 0, 0], e6ia_xr_inv ![1, 0, 0, 0, 0, 0]]]
          rw [← e6ia_zPow_vR1]
          rw [show (xr ![-1, 0, 0, 0, 0, 0] * xr ![1, 0, 0, 0, 0, 0]) * e6ia_zPow e6ia_vR1 * (xr ![-1, 0, 0, 0, 0, 0] * xr ![1, 0, 0, 0, 0, 0])⁻¹ =
              xr ![-1, 0, 0, 0, 0, 0] * (xr ![1, 0, 0, 0, 0, 0] * e6ia_zPow e6ia_vR1 * (xr ![1, 0, 0, 0, 0, 0])⁻¹) * (xr ![-1, 0, 0, 0, 0, 0])⁻¹ by group]
          rw [e6ia_conj_zPow ![1, 0, 0, 0, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
          rw [e6ia_conj_zPow ![-1, 0, 0, 0, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
          rw [show Matrix.mulVec (e6ia_zMat ![-1, 0, 0, 0, 0, 0]) (Matrix.mulVec (e6ia_zMat ![1, 0, 0, 0, 0, 0]) e6ia_vR1) = e6ia_vR1 + e6ia_vR2 from by decide]
          rw [e6ia_zPow_add, e6ia_zPow_vR1, e6ia_zPow_vR2]
          exact mul_mem (Subgroup.subset_closure (Or.inl rfl)) (Subgroup.subset_closure (Or.inr rfl))
        ·
          rw [show (xr ![1, 0, 0, 0, 0, 0] * xr ![-1, 0, 0, 0, 0, 0])⁻¹ = xr ![-1, 0, 0, 0, 0, 0] * xr ![1, 0, 0, 0, 0, 0] by
            rw [mul_inv_rev, e6ia_xr_inv ![-1, 0, 0, 0, 0, 0], e6ia_xr_inv ![1, 0, 0, 0, 0, 0]]]
          rw [← e6ia_zPow_vR2]
          rw [show (xr ![-1, 0, 0, 0, 0, 0] * xr ![1, 0, 0, 0, 0, 0]) * e6ia_zPow e6ia_vR2 * (xr ![-1, 0, 0, 0, 0, 0] * xr ![1, 0, 0, 0, 0, 0])⁻¹ =
              xr ![-1, 0, 0, 0, 0, 0] * (xr ![1, 0, 0, 0, 0, 0] * e6ia_zPow e6ia_vR2 * (xr ![1, 0, 0, 0, 0, 0])⁻¹) * (xr ![-1, 0, 0, 0, 0, 0])⁻¹ by group]
          rw [e6ia_conj_zPow ![1, 0, 0, 0, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
          rw [e6ia_conj_zPow ![-1, 0, 0, 0, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
          rw [show Matrix.mulVec (e6ia_zMat ![-1, 0, 0, 0, 0, 0]) (Matrix.mulVec (e6ia_zMat ![1, 0, 0, 0, 0, 0]) e6ia_vR2) = e6ia_vR1 from by decide]
          rw [e6ia_zPow_vR1]
          exact Subgroup.subset_closure (Or.inl rfl)
  · show xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1] ∈ Subgroup.normalizer (rE : Set EC)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · refine e6ia_conj_mem_rE_of_gens (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1]) ?_
      intro y hy
      rcases hy with rfl | rfl
      ·
        rw [← e6ia_zPow_vR1]
        rw [show (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1]) * e6ia_zPow e6ia_vR1 * (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1])⁻¹ =
            xr ![1, 0, 0, 0, 0, 0] * (xr ![0, 0, 0, 0, 0, 1] * e6ia_zPow e6ia_vR1 * (xr ![0, 0, 0, 0, 0, 1])⁻¹) * (xr ![1, 0, 0, 0, 0, 0])⁻¹ by group]
        rw [e6ia_conj_zPow ![0, 0, 0, 0, 0, 1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
        rw [e6ia_conj_zPow ![1, 0, 0, 0, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
        rw [show Matrix.mulVec (e6ia_zMat ![1, 0, 0, 0, 0, 0]) (Matrix.mulVec (e6ia_zMat ![0, 0, 0, 0, 0, 1]) e6ia_vR1) = e6ia_vR1 from by decide]
        rw [e6ia_zPow_vR1]
        exact Subgroup.subset_closure (Or.inl rfl)
      ·
        rw [← e6ia_zPow_vR2]
        rw [show (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1]) * e6ia_zPow e6ia_vR2 * (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1])⁻¹ =
            xr ![1, 0, 0, 0, 0, 0] * (xr ![0, 0, 0, 0, 0, 1] * e6ia_zPow e6ia_vR2 * (xr ![0, 0, 0, 0, 0, 1])⁻¹) * (xr ![1, 0, 0, 0, 0, 0])⁻¹ by group]
        rw [e6ia_conj_zPow ![0, 0, 0, 0, 0, 1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
        rw [e6ia_conj_zPow ![1, 0, 0, 0, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
        rw [show Matrix.mulVec (e6ia_zMat ![1, 0, 0, 0, 0, 0]) (Matrix.mulVec (e6ia_zMat ![0, 0, 0, 0, 0, 1]) e6ia_vR2) = e6ia_vR1 + e6ia_vR2 from by decide]
        rw [e6ia_zPow_add, e6ia_zPow_vR1, e6ia_zPow_vR2]
        exact mul_mem (Subgroup.subset_closure (Or.inl rfl)) (Subgroup.subset_closure (Or.inr rfl))
    · intro hh
      have h2 := e6ia_conj_mem_rE_of_gens (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1])⁻¹ ?_ hh
      · rwa [show (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1])⁻¹ * ((xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1]) * h * (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1])⁻¹) * (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1])⁻¹⁻¹ = h by group] at h2
      · intro y hy
        rcases hy with rfl | rfl
        ·
          rw [show (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1])⁻¹ = xr ![0, 0, 0, 0, 0, 1] * xr ![1, 0, 0, 0, 0, 0] by
            rw [mul_inv_rev, e6ia_xr_inv ![0, 0, 0, 0, 0, 1], e6ia_xr_inv ![1, 0, 0, 0, 0, 0]]]
          rw [← e6ia_zPow_vR1]
          rw [show (xr ![0, 0, 0, 0, 0, 1] * xr ![1, 0, 0, 0, 0, 0]) * e6ia_zPow e6ia_vR1 * (xr ![0, 0, 0, 0, 0, 1] * xr ![1, 0, 0, 0, 0, 0])⁻¹ =
              xr ![0, 0, 0, 0, 0, 1] * (xr ![1, 0, 0, 0, 0, 0] * e6ia_zPow e6ia_vR1 * (xr ![1, 0, 0, 0, 0, 0])⁻¹) * (xr ![0, 0, 0, 0, 0, 1])⁻¹ by group]
          rw [e6ia_conj_zPow ![1, 0, 0, 0, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
          rw [e6ia_conj_zPow ![0, 0, 0, 0, 0, 1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
          rw [show Matrix.mulVec (e6ia_zMat ![0, 0, 0, 0, 0, 1]) (Matrix.mulVec (e6ia_zMat ![1, 0, 0, 0, 0, 0]) e6ia_vR1) = e6ia_vR1 from by decide]
          rw [e6ia_zPow_vR1]
          exact Subgroup.subset_closure (Or.inl rfl)
        ·
          rw [show (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1])⁻¹ = xr ![0, 0, 0, 0, 0, 1] * xr ![1, 0, 0, 0, 0, 0] by
            rw [mul_inv_rev, e6ia_xr_inv ![0, 0, 0, 0, 0, 1], e6ia_xr_inv ![1, 0, 0, 0, 0, 0]]]
          rw [← e6ia_zPow_vR2]
          rw [show (xr ![0, 0, 0, 0, 0, 1] * xr ![1, 0, 0, 0, 0, 0]) * e6ia_zPow e6ia_vR2 * (xr ![0, 0, 0, 0, 0, 1] * xr ![1, 0, 0, 0, 0, 0])⁻¹ =
              xr ![0, 0, 0, 0, 0, 1] * (xr ![1, 0, 0, 0, 0, 0] * e6ia_zPow e6ia_vR2 * (xr ![1, 0, 0, 0, 0, 0])⁻¹) * (xr ![0, 0, 0, 0, 0, 1])⁻¹ by group]
          rw [e6ia_conj_zPow ![1, 0, 0, 0, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
          rw [e6ia_conj_zPow ![0, 0, 0, 0, 0, 1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
          rw [show Matrix.mulVec (e6ia_zMat ![0, 0, 0, 0, 0, 1]) (Matrix.mulVec (e6ia_zMat ![1, 0, 0, 0, 0, 0]) e6ia_vR2) = e6ia_vR1 + e6ia_vR2 from by decide]
          rw [e6ia_zPow_add, e6ia_zPow_vR1, e6ia_zPow_vR2]
          exact mul_mem (Subgroup.subset_closure (Or.inl rfl)) (Subgroup.subset_closure (Or.inr rfl))
  · show xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1] ∈ Subgroup.normalizer (rE : Set EC)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · refine e6ia_conj_mem_rE_of_gens (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1]) ?_
      intro y hy
      rcases hy with rfl | rfl
      ·
        rw [← e6ia_zPow_vR1]
        rw [show (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1]) * e6ia_zPow e6ia_vR1 * (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1])⁻¹ =
            xr ![1, 0, 0, 0, 0, 0] * (xr ![0, 0, 0, 0, 0, -1] * e6ia_zPow e6ia_vR1 * (xr ![0, 0, 0, 0, 0, -1])⁻¹) * (xr ![1, 0, 0, 0, 0, 0])⁻¹ by group]
        rw [e6ia_conj_zPow ![0, 0, 0, 0, 0, -1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
        rw [e6ia_conj_zPow ![1, 0, 0, 0, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
        rw [show Matrix.mulVec (e6ia_zMat ![1, 0, 0, 0, 0, 0]) (Matrix.mulVec (e6ia_zMat ![0, 0, 0, 0, 0, -1]) e6ia_vR1) = e6ia_vR2 from by decide]
        rw [e6ia_zPow_vR2]
        exact Subgroup.subset_closure (Or.inr rfl)
      ·
        rw [← e6ia_zPow_vR2]
        rw [show (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1]) * e6ia_zPow e6ia_vR2 * (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1])⁻¹ =
            xr ![1, 0, 0, 0, 0, 0] * (xr ![0, 0, 0, 0, 0, -1] * e6ia_zPow e6ia_vR2 * (xr ![0, 0, 0, 0, 0, -1])⁻¹) * (xr ![1, 0, 0, 0, 0, 0])⁻¹ by group]
        rw [e6ia_conj_zPow ![0, 0, 0, 0, 0, -1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
        rw [e6ia_conj_zPow ![1, 0, 0, 0, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
        rw [show Matrix.mulVec (e6ia_zMat ![1, 0, 0, 0, 0, 0]) (Matrix.mulVec (e6ia_zMat ![0, 0, 0, 0, 0, -1]) e6ia_vR2) = e6ia_vR1 from by decide]
        rw [e6ia_zPow_vR1]
        exact Subgroup.subset_closure (Or.inl rfl)
    · intro hh
      have h2 := e6ia_conj_mem_rE_of_gens (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1])⁻¹ ?_ hh
      · rwa [show (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1])⁻¹ * ((xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1]) * h * (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1])⁻¹) * (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1])⁻¹⁻¹ = h by group] at h2
      · intro y hy
        rcases hy with rfl | rfl
        ·
          rw [show (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1])⁻¹ = xr ![0, 0, 0, 0, 0, -1] * xr ![1, 0, 0, 0, 0, 0] by
            rw [mul_inv_rev, e6ia_xr_inv ![0, 0, 0, 0, 0, -1], e6ia_xr_inv ![1, 0, 0, 0, 0, 0]]]
          rw [← e6ia_zPow_vR1]
          rw [show (xr ![0, 0, 0, 0, 0, -1] * xr ![1, 0, 0, 0, 0, 0]) * e6ia_zPow e6ia_vR1 * (xr ![0, 0, 0, 0, 0, -1] * xr ![1, 0, 0, 0, 0, 0])⁻¹ =
              xr ![0, 0, 0, 0, 0, -1] * (xr ![1, 0, 0, 0, 0, 0] * e6ia_zPow e6ia_vR1 * (xr ![1, 0, 0, 0, 0, 0])⁻¹) * (xr ![0, 0, 0, 0, 0, -1])⁻¹ by group]
          rw [e6ia_conj_zPow ![1, 0, 0, 0, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
          rw [e6ia_conj_zPow ![0, 0, 0, 0, 0, -1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
          rw [show Matrix.mulVec (e6ia_zMat ![0, 0, 0, 0, 0, -1]) (Matrix.mulVec (e6ia_zMat ![1, 0, 0, 0, 0, 0]) e6ia_vR1) = e6ia_vR2 from by decide]
          rw [e6ia_zPow_vR2]
          exact Subgroup.subset_closure (Or.inr rfl)
        ·
          rw [show (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1])⁻¹ = xr ![0, 0, 0, 0, 0, -1] * xr ![1, 0, 0, 0, 0, 0] by
            rw [mul_inv_rev, e6ia_xr_inv ![0, 0, 0, 0, 0, -1], e6ia_xr_inv ![1, 0, 0, 0, 0, 0]]]
          rw [← e6ia_zPow_vR2]
          rw [show (xr ![0, 0, 0, 0, 0, -1] * xr ![1, 0, 0, 0, 0, 0]) * e6ia_zPow e6ia_vR2 * (xr ![0, 0, 0, 0, 0, -1] * xr ![1, 0, 0, 0, 0, 0])⁻¹ =
              xr ![0, 0, 0, 0, 0, -1] * (xr ![1, 0, 0, 0, 0, 0] * e6ia_zPow e6ia_vR2 * (xr ![1, 0, 0, 0, 0, 0])⁻¹) * (xr ![0, 0, 0, 0, 0, -1])⁻¹ by group]
          rw [e6ia_conj_zPow ![1, 0, 0, 0, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
          rw [e6ia_conj_zPow ![0, 0, 0, 0, 0, -1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
          rw [show Matrix.mulVec (e6ia_zMat ![0, 0, 0, 0, 0, -1]) (Matrix.mulVec (e6ia_zMat ![1, 0, 0, 0, 0, 0]) e6ia_vR2) = e6ia_vR1 from by decide]
          rw [e6ia_zPow_vR1]
          exact Subgroup.subset_closure (Or.inl rfl)
  · show xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1] ∈ Subgroup.normalizer (rE : Set EC)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · refine e6ia_conj_mem_rE_of_gens (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1]) ?_
      intro y hy
      rcases hy with rfl | rfl
      ·
        rw [← e6ia_zPow_vR1]
        rw [show (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1]) * e6ia_zPow e6ia_vR1 * (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1])⁻¹ =
            xr ![-1, 0, 0, 0, 0, 0] * (xr ![0, 0, 0, 0, 0, 1] * e6ia_zPow e6ia_vR1 * (xr ![0, 0, 0, 0, 0, 1])⁻¹) * (xr ![-1, 0, 0, 0, 0, 0])⁻¹ by group]
        rw [e6ia_conj_zPow ![0, 0, 0, 0, 0, 1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
        rw [e6ia_conj_zPow ![-1, 0, 0, 0, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
        rw [show Matrix.mulVec (e6ia_zMat ![-1, 0, 0, 0, 0, 0]) (Matrix.mulVec (e6ia_zMat ![0, 0, 0, 0, 0, 1]) e6ia_vR1) = e6ia_vR1 + e6ia_vR2 from by decide]
        rw [e6ia_zPow_add, e6ia_zPow_vR1, e6ia_zPow_vR2]
        exact mul_mem (Subgroup.subset_closure (Or.inl rfl)) (Subgroup.subset_closure (Or.inr rfl))
      ·
        rw [← e6ia_zPow_vR2]
        rw [show (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1]) * e6ia_zPow e6ia_vR2 * (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1])⁻¹ =
            xr ![-1, 0, 0, 0, 0, 0] * (xr ![0, 0, 0, 0, 0, 1] * e6ia_zPow e6ia_vR2 * (xr ![0, 0, 0, 0, 0, 1])⁻¹) * (xr ![-1, 0, 0, 0, 0, 0])⁻¹ by group]
        rw [e6ia_conj_zPow ![0, 0, 0, 0, 0, 1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
        rw [e6ia_conj_zPow ![-1, 0, 0, 0, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
        rw [show Matrix.mulVec (e6ia_zMat ![-1, 0, 0, 0, 0, 0]) (Matrix.mulVec (e6ia_zMat ![0, 0, 0, 0, 0, 1]) e6ia_vR2) = e6ia_vR2 from by decide]
        rw [e6ia_zPow_vR2]
        exact Subgroup.subset_closure (Or.inr rfl)
    · intro hh
      have h2 := e6ia_conj_mem_rE_of_gens (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1])⁻¹ ?_ hh
      · rwa [show (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1])⁻¹ * ((xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1]) * h * (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1])⁻¹) * (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1])⁻¹⁻¹ = h by group] at h2
      · intro y hy
        rcases hy with rfl | rfl
        ·
          rw [show (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1])⁻¹ = xr ![0, 0, 0, 0, 0, 1] * xr ![-1, 0, 0, 0, 0, 0] by
            rw [mul_inv_rev, e6ia_xr_inv ![0, 0, 0, 0, 0, 1], e6ia_xr_inv ![-1, 0, 0, 0, 0, 0]]]
          rw [← e6ia_zPow_vR1]
          rw [show (xr ![0, 0, 0, 0, 0, 1] * xr ![-1, 0, 0, 0, 0, 0]) * e6ia_zPow e6ia_vR1 * (xr ![0, 0, 0, 0, 0, 1] * xr ![-1, 0, 0, 0, 0, 0])⁻¹ =
              xr ![0, 0, 0, 0, 0, 1] * (xr ![-1, 0, 0, 0, 0, 0] * e6ia_zPow e6ia_vR1 * (xr ![-1, 0, 0, 0, 0, 0])⁻¹) * (xr ![0, 0, 0, 0, 0, 1])⁻¹ by group]
          rw [e6ia_conj_zPow ![-1, 0, 0, 0, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
          rw [e6ia_conj_zPow ![0, 0, 0, 0, 0, 1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
          rw [show Matrix.mulVec (e6ia_zMat ![0, 0, 0, 0, 0, 1]) (Matrix.mulVec (e6ia_zMat ![-1, 0, 0, 0, 0, 0]) e6ia_vR1) = e6ia_vR1 + e6ia_vR2 from by decide]
          rw [e6ia_zPow_add, e6ia_zPow_vR1, e6ia_zPow_vR2]
          exact mul_mem (Subgroup.subset_closure (Or.inl rfl)) (Subgroup.subset_closure (Or.inr rfl))
        ·
          rw [show (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1])⁻¹ = xr ![0, 0, 0, 0, 0, 1] * xr ![-1, 0, 0, 0, 0, 0] by
            rw [mul_inv_rev, e6ia_xr_inv ![0, 0, 0, 0, 0, 1], e6ia_xr_inv ![-1, 0, 0, 0, 0, 0]]]
          rw [← e6ia_zPow_vR2]
          rw [show (xr ![0, 0, 0, 0, 0, 1] * xr ![-1, 0, 0, 0, 0, 0]) * e6ia_zPow e6ia_vR2 * (xr ![0, 0, 0, 0, 0, 1] * xr ![-1, 0, 0, 0, 0, 0])⁻¹ =
              xr ![0, 0, 0, 0, 0, 1] * (xr ![-1, 0, 0, 0, 0, 0] * e6ia_zPow e6ia_vR2 * (xr ![-1, 0, 0, 0, 0, 0])⁻¹) * (xr ![0, 0, 0, 0, 0, 1])⁻¹ by group]
          rw [e6ia_conj_zPow ![-1, 0, 0, 0, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
          rw [e6ia_conj_zPow ![0, 0, 0, 0, 0, 1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
          rw [show Matrix.mulVec (e6ia_zMat ![0, 0, 0, 0, 0, 1]) (Matrix.mulVec (e6ia_zMat ![-1, 0, 0, 0, 0, 0]) e6ia_vR2) = e6ia_vR2 from by decide]
          rw [e6ia_zPow_vR2]
          exact Subgroup.subset_closure (Or.inr rfl)
  · show xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1] ∈ Subgroup.normalizer (rE : Set EC)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · refine e6ia_conj_mem_rE_of_gens (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1]) ?_
      intro y hy
      rcases hy with rfl | rfl
      ·
        rw [← e6ia_zPow_vR1]
        rw [show (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1]) * e6ia_zPow e6ia_vR1 * (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1])⁻¹ =
            xr ![-1, 0, 0, 0, 0, 0] * (xr ![0, 0, 0, 0, 0, -1] * e6ia_zPow e6ia_vR1 * (xr ![0, 0, 0, 0, 0, -1])⁻¹) * (xr ![-1, 0, 0, 0, 0, 0])⁻¹ by group]
        rw [e6ia_conj_zPow ![0, 0, 0, 0, 0, -1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
        rw [e6ia_conj_zPow ![-1, 0, 0, 0, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
        rw [show Matrix.mulVec (e6ia_zMat ![-1, 0, 0, 0, 0, 0]) (Matrix.mulVec (e6ia_zMat ![0, 0, 0, 0, 0, -1]) e6ia_vR1) = e6ia_vR1 from by decide]
        rw [e6ia_zPow_vR1]
        exact Subgroup.subset_closure (Or.inl rfl)
      ·
        rw [← e6ia_zPow_vR2]
        rw [show (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1]) * e6ia_zPow e6ia_vR2 * (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1])⁻¹ =
            xr ![-1, 0, 0, 0, 0, 0] * (xr ![0, 0, 0, 0, 0, -1] * e6ia_zPow e6ia_vR2 * (xr ![0, 0, 0, 0, 0, -1])⁻¹) * (xr ![-1, 0, 0, 0, 0, 0])⁻¹ by group]
        rw [e6ia_conj_zPow ![0, 0, 0, 0, 0, -1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
        rw [e6ia_conj_zPow ![-1, 0, 0, 0, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
        rw [show Matrix.mulVec (e6ia_zMat ![-1, 0, 0, 0, 0, 0]) (Matrix.mulVec (e6ia_zMat ![0, 0, 0, 0, 0, -1]) e6ia_vR2) = e6ia_vR1 + e6ia_vR2 from by decide]
        rw [e6ia_zPow_add, e6ia_zPow_vR1, e6ia_zPow_vR2]
        exact mul_mem (Subgroup.subset_closure (Or.inl rfl)) (Subgroup.subset_closure (Or.inr rfl))
    · intro hh
      have h2 := e6ia_conj_mem_rE_of_gens (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1])⁻¹ ?_ hh
      · rwa [show (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1])⁻¹ * ((xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1]) * h * (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1])⁻¹) * (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1])⁻¹⁻¹ = h by group] at h2
      · intro y hy
        rcases hy with rfl | rfl
        ·
          rw [show (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1])⁻¹ = xr ![0, 0, 0, 0, 0, -1] * xr ![-1, 0, 0, 0, 0, 0] by
            rw [mul_inv_rev, e6ia_xr_inv ![0, 0, 0, 0, 0, -1], e6ia_xr_inv ![-1, 0, 0, 0, 0, 0]]]
          rw [← e6ia_zPow_vR1]
          rw [show (xr ![0, 0, 0, 0, 0, -1] * xr ![-1, 0, 0, 0, 0, 0]) * e6ia_zPow e6ia_vR1 * (xr ![0, 0, 0, 0, 0, -1] * xr ![-1, 0, 0, 0, 0, 0])⁻¹ =
              xr ![0, 0, 0, 0, 0, -1] * (xr ![-1, 0, 0, 0, 0, 0] * e6ia_zPow e6ia_vR1 * (xr ![-1, 0, 0, 0, 0, 0])⁻¹) * (xr ![0, 0, 0, 0, 0, -1])⁻¹ by group]
          rw [e6ia_conj_zPow ![-1, 0, 0, 0, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
          rw [e6ia_conj_zPow ![0, 0, 0, 0, 0, -1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
          rw [show Matrix.mulVec (e6ia_zMat ![0, 0, 0, 0, 0, -1]) (Matrix.mulVec (e6ia_zMat ![-1, 0, 0, 0, 0, 0]) e6ia_vR1) = e6ia_vR1 from by decide]
          rw [e6ia_zPow_vR1]
          exact Subgroup.subset_closure (Or.inl rfl)
        ·
          rw [show (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1])⁻¹ = xr ![0, 0, 0, 0, 0, -1] * xr ![-1, 0, 0, 0, 0, 0] by
            rw [mul_inv_rev, e6ia_xr_inv ![0, 0, 0, 0, 0, -1], e6ia_xr_inv ![-1, 0, 0, 0, 0, 0]]]
          rw [← e6ia_zPow_vR2]
          rw [show (xr ![0, 0, 0, 0, 0, -1] * xr ![-1, 0, 0, 0, 0, 0]) * e6ia_zPow e6ia_vR2 * (xr ![0, 0, 0, 0, 0, -1] * xr ![-1, 0, 0, 0, 0, 0])⁻¹ =
              xr ![0, 0, 0, 0, 0, -1] * (xr ![-1, 0, 0, 0, 0, 0] * e6ia_zPow e6ia_vR2 * (xr ![-1, 0, 0, 0, 0, 0])⁻¹) * (xr ![0, 0, 0, 0, 0, -1])⁻¹ by group]
          rw [e6ia_conj_zPow ![-1, 0, 0, 0, 0, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
          rw [e6ia_conj_zPow ![0, 0, 0, 0, 0, -1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
          rw [show Matrix.mulVec (e6ia_zMat ![0, 0, 0, 0, 0, -1]) (Matrix.mulVec (e6ia_zMat ![-1, 0, 0, 0, 0, 0]) e6ia_vR2) = e6ia_vR1 + e6ia_vR2 from by decide]
          rw [e6ia_zPow_add, e6ia_zPow_vR1, e6ia_zPow_vR2]
          exact mul_mem (Subgroup.subset_closure (Or.inl rfl)) (Subgroup.subset_closure (Or.inr rfl))
  · show xr ![0, 0, 0, 0, 0, 1] * xr ![0, 0, 0, 0, 0, -1] ∈ Subgroup.normalizer (rE : Set EC)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · refine e6ia_conj_mem_rE_of_gens (xr ![0, 0, 0, 0, 0, 1] * xr ![0, 0, 0, 0, 0, -1]) ?_
      intro y hy
      rcases hy with rfl | rfl
      ·
        rw [← e6ia_zPow_vR1]
        rw [show (xr ![0, 0, 0, 0, 0, 1] * xr ![0, 0, 0, 0, 0, -1]) * e6ia_zPow e6ia_vR1 * (xr ![0, 0, 0, 0, 0, 1] * xr ![0, 0, 0, 0, 0, -1])⁻¹ =
            xr ![0, 0, 0, 0, 0, 1] * (xr ![0, 0, 0, 0, 0, -1] * e6ia_zPow e6ia_vR1 * (xr ![0, 0, 0, 0, 0, -1])⁻¹) * (xr ![0, 0, 0, 0, 0, 1])⁻¹ by group]
        rw [e6ia_conj_zPow ![0, 0, 0, 0, 0, -1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
        rw [e6ia_conj_zPow ![0, 0, 0, 0, 0, 1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
        rw [show Matrix.mulVec (e6ia_zMat ![0, 0, 0, 0, 0, 1]) (Matrix.mulVec (e6ia_zMat ![0, 0, 0, 0, 0, -1]) e6ia_vR1) = e6ia_vR1 + e6ia_vR2 from by decide]
        rw [e6ia_zPow_add, e6ia_zPow_vR1, e6ia_zPow_vR2]
        exact mul_mem (Subgroup.subset_closure (Or.inl rfl)) (Subgroup.subset_closure (Or.inr rfl))
      ·
        rw [← e6ia_zPow_vR2]
        rw [show (xr ![0, 0, 0, 0, 0, 1] * xr ![0, 0, 0, 0, 0, -1]) * e6ia_zPow e6ia_vR2 * (xr ![0, 0, 0, 0, 0, 1] * xr ![0, 0, 0, 0, 0, -1])⁻¹ =
            xr ![0, 0, 0, 0, 0, 1] * (xr ![0, 0, 0, 0, 0, -1] * e6ia_zPow e6ia_vR2 * (xr ![0, 0, 0, 0, 0, -1])⁻¹) * (xr ![0, 0, 0, 0, 0, 1])⁻¹ by group]
        rw [e6ia_conj_zPow ![0, 0, 0, 0, 0, -1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
        rw [e6ia_conj_zPow ![0, 0, 0, 0, 0, 1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
        rw [show Matrix.mulVec (e6ia_zMat ![0, 0, 0, 0, 0, 1]) (Matrix.mulVec (e6ia_zMat ![0, 0, 0, 0, 0, -1]) e6ia_vR2) = e6ia_vR1 from by decide]
        rw [e6ia_zPow_vR1]
        exact Subgroup.subset_closure (Or.inl rfl)
    · intro hh
      have h2 := e6ia_conj_mem_rE_of_gens (xr ![0, 0, 0, 0, 0, 1] * xr ![0, 0, 0, 0, 0, -1])⁻¹ ?_ hh
      · rwa [show (xr ![0, 0, 0, 0, 0, 1] * xr ![0, 0, 0, 0, 0, -1])⁻¹ * ((xr ![0, 0, 0, 0, 0, 1] * xr ![0, 0, 0, 0, 0, -1]) * h * (xr ![0, 0, 0, 0, 0, 1] * xr ![0, 0, 0, 0, 0, -1])⁻¹) * (xr ![0, 0, 0, 0, 0, 1] * xr ![0, 0, 0, 0, 0, -1])⁻¹⁻¹ = h by group] at h2
      · intro y hy
        rcases hy with rfl | rfl
        ·
          rw [show (xr ![0, 0, 0, 0, 0, 1] * xr ![0, 0, 0, 0, 0, -1])⁻¹ = xr ![0, 0, 0, 0, 0, -1] * xr ![0, 0, 0, 0, 0, 1] by
            rw [mul_inv_rev, e6ia_xr_inv ![0, 0, 0, 0, 0, -1], e6ia_xr_inv ![0, 0, 0, 0, 0, 1]]]
          rw [← e6ia_zPow_vR1]
          rw [show (xr ![0, 0, 0, 0, 0, -1] * xr ![0, 0, 0, 0, 0, 1]) * e6ia_zPow e6ia_vR1 * (xr ![0, 0, 0, 0, 0, -1] * xr ![0, 0, 0, 0, 0, 1])⁻¹ =
              xr ![0, 0, 0, 0, 0, -1] * (xr ![0, 0, 0, 0, 0, 1] * e6ia_zPow e6ia_vR1 * (xr ![0, 0, 0, 0, 0, 1])⁻¹) * (xr ![0, 0, 0, 0, 0, -1])⁻¹ by group]
          rw [e6ia_conj_zPow ![0, 0, 0, 0, 0, 1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
          rw [e6ia_conj_zPow ![0, 0, 0, 0, 0, -1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
          rw [show Matrix.mulVec (e6ia_zMat ![0, 0, 0, 0, 0, -1]) (Matrix.mulVec (e6ia_zMat ![0, 0, 0, 0, 0, 1]) e6ia_vR1) = e6ia_vR2 from by decide]
          rw [e6ia_zPow_vR2]
          exact Subgroup.subset_closure (Or.inr rfl)
        ·
          rw [show (xr ![0, 0, 0, 0, 0, 1] * xr ![0, 0, 0, 0, 0, -1])⁻¹ = xr ![0, 0, 0, 0, 0, -1] * xr ![0, 0, 0, 0, 0, 1] by
            rw [mul_inv_rev, e6ia_xr_inv ![0, 0, 0, 0, 0, -1], e6ia_xr_inv ![0, 0, 0, 0, 0, 1]]]
          rw [← e6ia_zPow_vR2]
          rw [show (xr ![0, 0, 0, 0, 0, -1] * xr ![0, 0, 0, 0, 0, 1]) * e6ia_zPow e6ia_vR2 * (xr ![0, 0, 0, 0, 0, -1] * xr ![0, 0, 0, 0, 0, 1])⁻¹ =
              xr ![0, 0, 0, 0, 0, -1] * (xr ![0, 0, 0, 0, 0, 1] * e6ia_zPow e6ia_vR2 * (xr ![0, 0, 0, 0, 0, 1])⁻¹) * (xr ![0, 0, 0, 0, 0, -1])⁻¹ by group]
          rw [e6ia_conj_zPow ![0, 0, 0, 0, 0, 1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
          rw [e6ia_conj_zPow ![0, 0, 0, 0, 0, -1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
          rw [show Matrix.mulVec (e6ia_zMat ![0, 0, 0, 0, 0, -1]) (Matrix.mulVec (e6ia_zMat ![0, 0, 0, 0, 0, 1]) e6ia_vR2) = e6ia_vR1 + e6ia_vR2 from by decide]
          rw [e6ia_zPow_add, e6ia_zPow_vR1, e6ia_zPow_vR2]
          exact mul_mem (Subgroup.subset_closure (Or.inl rfl)) (Subgroup.subset_closure (Or.inr rfl))
  · show xr ![1, 1, 1, 2, 1, 1] * xr ![0, 1, 1, 2, 1, 0] ∈ Subgroup.normalizer (rE : Set EC)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · refine e6ia_conj_mem_rE_of_gens (xr ![1, 1, 1, 2, 1, 1] * xr ![0, 1, 1, 2, 1, 0]) ?_
      intro y hy
      rcases hy with rfl | rfl
      ·
        rw [← e6ia_zPow_vR1]
        rw [show (xr ![1, 1, 1, 2, 1, 1] * xr ![0, 1, 1, 2, 1, 0]) * e6ia_zPow e6ia_vR1 * (xr ![1, 1, 1, 2, 1, 1] * xr ![0, 1, 1, 2, 1, 0])⁻¹ =
            xr ![1, 1, 1, 2, 1, 1] * (xr ![0, 1, 1, 2, 1, 0] * e6ia_zPow e6ia_vR1 * (xr ![0, 1, 1, 2, 1, 0])⁻¹) * (xr ![1, 1, 1, 2, 1, 1])⁻¹ by group]
        rw [e6ia_conj_zPow ![0, 1, 1, 2, 1, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
        rw [e6ia_conj_zPow ![1, 1, 1, 2, 1, 1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
        rw [show Matrix.mulVec (e6ia_zMat ![1, 1, 1, 2, 1, 1]) (Matrix.mulVec (e6ia_zMat ![0, 1, 1, 2, 1, 0]) e6ia_vR1) = e6ia_vR1 from by decide]
        rw [e6ia_zPow_vR1]
        exact Subgroup.subset_closure (Or.inl rfl)
      ·
        rw [← e6ia_zPow_vR2]
        rw [show (xr ![1, 1, 1, 2, 1, 1] * xr ![0, 1, 1, 2, 1, 0]) * e6ia_zPow e6ia_vR2 * (xr ![1, 1, 1, 2, 1, 1] * xr ![0, 1, 1, 2, 1, 0])⁻¹ =
            xr ![1, 1, 1, 2, 1, 1] * (xr ![0, 1, 1, 2, 1, 0] * e6ia_zPow e6ia_vR2 * (xr ![0, 1, 1, 2, 1, 0])⁻¹) * (xr ![1, 1, 1, 2, 1, 1])⁻¹ by group]
        rw [e6ia_conj_zPow ![0, 1, 1, 2, 1, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
        rw [e6ia_conj_zPow ![1, 1, 1, 2, 1, 1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
        rw [show Matrix.mulVec (e6ia_zMat ![1, 1, 1, 2, 1, 1]) (Matrix.mulVec (e6ia_zMat ![0, 1, 1, 2, 1, 0]) e6ia_vR2) = e6ia_vR2 from by decide]
        rw [e6ia_zPow_vR2]
        exact Subgroup.subset_closure (Or.inr rfl)
    · intro hh
      have h2 := e6ia_conj_mem_rE_of_gens (xr ![1, 1, 1, 2, 1, 1] * xr ![0, 1, 1, 2, 1, 0])⁻¹ ?_ hh
      · rwa [show (xr ![1, 1, 1, 2, 1, 1] * xr ![0, 1, 1, 2, 1, 0])⁻¹ * ((xr ![1, 1, 1, 2, 1, 1] * xr ![0, 1, 1, 2, 1, 0]) * h * (xr ![1, 1, 1, 2, 1, 1] * xr ![0, 1, 1, 2, 1, 0])⁻¹) * (xr ![1, 1, 1, 2, 1, 1] * xr ![0, 1, 1, 2, 1, 0])⁻¹⁻¹ = h by group] at h2
      · intro y hy
        rcases hy with rfl | rfl
        ·
          rw [show (xr ![1, 1, 1, 2, 1, 1] * xr ![0, 1, 1, 2, 1, 0])⁻¹ = xr ![0, 1, 1, 2, 1, 0] * xr ![1, 1, 1, 2, 1, 1] by
            rw [mul_inv_rev, e6ia_xr_inv ![0, 1, 1, 2, 1, 0], e6ia_xr_inv ![1, 1, 1, 2, 1, 1]]]
          rw [← e6ia_zPow_vR1]
          rw [show (xr ![0, 1, 1, 2, 1, 0] * xr ![1, 1, 1, 2, 1, 1]) * e6ia_zPow e6ia_vR1 * (xr ![0, 1, 1, 2, 1, 0] * xr ![1, 1, 1, 2, 1, 1])⁻¹ =
              xr ![0, 1, 1, 2, 1, 0] * (xr ![1, 1, 1, 2, 1, 1] * e6ia_zPow e6ia_vR1 * (xr ![1, 1, 1, 2, 1, 1])⁻¹) * (xr ![0, 1, 1, 2, 1, 0])⁻¹ by group]
          rw [e6ia_conj_zPow ![1, 1, 1, 2, 1, 1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
          rw [e6ia_conj_zPow ![0, 1, 1, 2, 1, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
          rw [show Matrix.mulVec (e6ia_zMat ![0, 1, 1, 2, 1, 0]) (Matrix.mulVec (e6ia_zMat ![1, 1, 1, 2, 1, 1]) e6ia_vR1) = e6ia_vR1 from by decide]
          rw [e6ia_zPow_vR1]
          exact Subgroup.subset_closure (Or.inl rfl)
        ·
          rw [show (xr ![1, 1, 1, 2, 1, 1] * xr ![0, 1, 1, 2, 1, 0])⁻¹ = xr ![0, 1, 1, 2, 1, 0] * xr ![1, 1, 1, 2, 1, 1] by
            rw [mul_inv_rev, e6ia_xr_inv ![0, 1, 1, 2, 1, 0], e6ia_xr_inv ![1, 1, 1, 2, 1, 1]]]
          rw [← e6ia_zPow_vR2]
          rw [show (xr ![0, 1, 1, 2, 1, 0] * xr ![1, 1, 1, 2, 1, 1]) * e6ia_zPow e6ia_vR2 * (xr ![0, 1, 1, 2, 1, 0] * xr ![1, 1, 1, 2, 1, 1])⁻¹ =
              xr ![0, 1, 1, 2, 1, 0] * (xr ![1, 1, 1, 2, 1, 1] * e6ia_zPow e6ia_vR2 * (xr ![1, 1, 1, 2, 1, 1])⁻¹) * (xr ![0, 1, 1, 2, 1, 0])⁻¹ by group]
          rw [e6ia_conj_zPow ![1, 1, 1, 2, 1, 1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
          rw [e6ia_conj_zPow ![0, 1, 1, 2, 1, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
          rw [show Matrix.mulVec (e6ia_zMat ![0, 1, 1, 2, 1, 0]) (Matrix.mulVec (e6ia_zMat ![1, 1, 1, 2, 1, 1]) e6ia_vR2) = e6ia_vR2 from by decide]
          rw [e6ia_zPow_vR2]
          exact Subgroup.subset_closure (Or.inr rfl)
  · show xr ![1, 1, 1, 1, 1, 1] * xr ![0, 1, 1, 1, 1, 0] ∈ Subgroup.normalizer (rE : Set EC)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · refine e6ia_conj_mem_rE_of_gens (xr ![1, 1, 1, 1, 1, 1] * xr ![0, 1, 1, 1, 1, 0]) ?_
      intro y hy
      rcases hy with rfl | rfl
      ·
        rw [← e6ia_zPow_vR1]
        rw [show (xr ![1, 1, 1, 1, 1, 1] * xr ![0, 1, 1, 1, 1, 0]) * e6ia_zPow e6ia_vR1 * (xr ![1, 1, 1, 1, 1, 1] * xr ![0, 1, 1, 1, 1, 0])⁻¹ =
            xr ![1, 1, 1, 1, 1, 1] * (xr ![0, 1, 1, 1, 1, 0] * e6ia_zPow e6ia_vR1 * (xr ![0, 1, 1, 1, 1, 0])⁻¹) * (xr ![1, 1, 1, 1, 1, 1])⁻¹ by group]
        rw [e6ia_conj_zPow ![0, 1, 1, 1, 1, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
        rw [e6ia_conj_zPow ![1, 1, 1, 1, 1, 1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
        rw [show Matrix.mulVec (e6ia_zMat ![1, 1, 1, 1, 1, 1]) (Matrix.mulVec (e6ia_zMat ![0, 1, 1, 1, 1, 0]) e6ia_vR1) = e6ia_vR1 from by decide]
        rw [e6ia_zPow_vR1]
        exact Subgroup.subset_closure (Or.inl rfl)
      ·
        rw [← e6ia_zPow_vR2]
        rw [show (xr ![1, 1, 1, 1, 1, 1] * xr ![0, 1, 1, 1, 1, 0]) * e6ia_zPow e6ia_vR2 * (xr ![1, 1, 1, 1, 1, 1] * xr ![0, 1, 1, 1, 1, 0])⁻¹ =
            xr ![1, 1, 1, 1, 1, 1] * (xr ![0, 1, 1, 1, 1, 0] * e6ia_zPow e6ia_vR2 * (xr ![0, 1, 1, 1, 1, 0])⁻¹) * (xr ![1, 1, 1, 1, 1, 1])⁻¹ by group]
        rw [e6ia_conj_zPow ![0, 1, 1, 1, 1, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
        rw [e6ia_conj_zPow ![1, 1, 1, 1, 1, 1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
        rw [show Matrix.mulVec (e6ia_zMat ![1, 1, 1, 1, 1, 1]) (Matrix.mulVec (e6ia_zMat ![0, 1, 1, 1, 1, 0]) e6ia_vR2) = e6ia_vR2 from by decide]
        rw [e6ia_zPow_vR2]
        exact Subgroup.subset_closure (Or.inr rfl)
    · intro hh
      have h2 := e6ia_conj_mem_rE_of_gens (xr ![1, 1, 1, 1, 1, 1] * xr ![0, 1, 1, 1, 1, 0])⁻¹ ?_ hh
      · rwa [show (xr ![1, 1, 1, 1, 1, 1] * xr ![0, 1, 1, 1, 1, 0])⁻¹ * ((xr ![1, 1, 1, 1, 1, 1] * xr ![0, 1, 1, 1, 1, 0]) * h * (xr ![1, 1, 1, 1, 1, 1] * xr ![0, 1, 1, 1, 1, 0])⁻¹) * (xr ![1, 1, 1, 1, 1, 1] * xr ![0, 1, 1, 1, 1, 0])⁻¹⁻¹ = h by group] at h2
      · intro y hy
        rcases hy with rfl | rfl
        ·
          rw [show (xr ![1, 1, 1, 1, 1, 1] * xr ![0, 1, 1, 1, 1, 0])⁻¹ = xr ![0, 1, 1, 1, 1, 0] * xr ![1, 1, 1, 1, 1, 1] by
            rw [mul_inv_rev, e6ia_xr_inv ![0, 1, 1, 1, 1, 0], e6ia_xr_inv ![1, 1, 1, 1, 1, 1]]]
          rw [← e6ia_zPow_vR1]
          rw [show (xr ![0, 1, 1, 1, 1, 0] * xr ![1, 1, 1, 1, 1, 1]) * e6ia_zPow e6ia_vR1 * (xr ![0, 1, 1, 1, 1, 0] * xr ![1, 1, 1, 1, 1, 1])⁻¹ =
              xr ![0, 1, 1, 1, 1, 0] * (xr ![1, 1, 1, 1, 1, 1] * e6ia_zPow e6ia_vR1 * (xr ![1, 1, 1, 1, 1, 1])⁻¹) * (xr ![0, 1, 1, 1, 1, 0])⁻¹ by group]
          rw [e6ia_conj_zPow ![1, 1, 1, 1, 1, 1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
          rw [e6ia_conj_zPow ![0, 1, 1, 1, 1, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
          rw [show Matrix.mulVec (e6ia_zMat ![0, 1, 1, 1, 1, 0]) (Matrix.mulVec (e6ia_zMat ![1, 1, 1, 1, 1, 1]) e6ia_vR1) = e6ia_vR1 from by decide]
          rw [e6ia_zPow_vR1]
          exact Subgroup.subset_closure (Or.inl rfl)
        ·
          rw [show (xr ![1, 1, 1, 1, 1, 1] * xr ![0, 1, 1, 1, 1, 0])⁻¹ = xr ![0, 1, 1, 1, 1, 0] * xr ![1, 1, 1, 1, 1, 1] by
            rw [mul_inv_rev, e6ia_xr_inv ![0, 1, 1, 1, 1, 0], e6ia_xr_inv ![1, 1, 1, 1, 1, 1]]]
          rw [← e6ia_zPow_vR2]
          rw [show (xr ![0, 1, 1, 1, 1, 0] * xr ![1, 1, 1, 1, 1, 1]) * e6ia_zPow e6ia_vR2 * (xr ![0, 1, 1, 1, 1, 0] * xr ![1, 1, 1, 1, 1, 1])⁻¹ =
              xr ![0, 1, 1, 1, 1, 0] * (xr ![1, 1, 1, 1, 1, 1] * e6ia_zPow e6ia_vR2 * (xr ![1, 1, 1, 1, 1, 1])⁻¹) * (xr ![0, 1, 1, 1, 1, 0])⁻¹ by group]
          rw [e6ia_conj_zPow ![1, 1, 1, 1, 1, 1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
          rw [e6ia_conj_zPow ![0, 1, 1, 1, 1, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
          rw [show Matrix.mulVec (e6ia_zMat ![0, 1, 1, 1, 1, 0]) (Matrix.mulVec (e6ia_zMat ![1, 1, 1, 1, 1, 1]) e6ia_vR2) = e6ia_vR2 from by decide]
          rw [e6ia_zPow_vR2]
          exact Subgroup.subset_closure (Or.inr rfl)
  · show xr ![0, -1, -1, -1, -1, 0] * xr ![-1, -1, -1, -1, -1, -1] ∈ Subgroup.normalizer (rE : Set EC)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · refine e6ia_conj_mem_rE_of_gens (xr ![0, -1, -1, -1, -1, 0] * xr ![-1, -1, -1, -1, -1, -1]) ?_
      intro y hy
      rcases hy with rfl | rfl
      ·
        rw [← e6ia_zPow_vR1]
        rw [show (xr ![0, -1, -1, -1, -1, 0] * xr ![-1, -1, -1, -1, -1, -1]) * e6ia_zPow e6ia_vR1 * (xr ![0, -1, -1, -1, -1, 0] * xr ![-1, -1, -1, -1, -1, -1])⁻¹ =
            xr ![0, -1, -1, -1, -1, 0] * (xr ![-1, -1, -1, -1, -1, -1] * e6ia_zPow e6ia_vR1 * (xr ![-1, -1, -1, -1, -1, -1])⁻¹) * (xr ![0, -1, -1, -1, -1, 0])⁻¹ by group]
        rw [e6ia_conj_zPow ![-1, -1, -1, -1, -1, -1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
        rw [e6ia_conj_zPow ![0, -1, -1, -1, -1, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
        rw [show Matrix.mulVec (e6ia_zMat ![0, -1, -1, -1, -1, 0]) (Matrix.mulVec (e6ia_zMat ![-1, -1, -1, -1, -1, -1]) e6ia_vR1) = e6ia_vR1 from by decide]
        rw [e6ia_zPow_vR1]
        exact Subgroup.subset_closure (Or.inl rfl)
      ·
        rw [← e6ia_zPow_vR2]
        rw [show (xr ![0, -1, -1, -1, -1, 0] * xr ![-1, -1, -1, -1, -1, -1]) * e6ia_zPow e6ia_vR2 * (xr ![0, -1, -1, -1, -1, 0] * xr ![-1, -1, -1, -1, -1, -1])⁻¹ =
            xr ![0, -1, -1, -1, -1, 0] * (xr ![-1, -1, -1, -1, -1, -1] * e6ia_zPow e6ia_vR2 * (xr ![-1, -1, -1, -1, -1, -1])⁻¹) * (xr ![0, -1, -1, -1, -1, 0])⁻¹ by group]
        rw [e6ia_conj_zPow ![-1, -1, -1, -1, -1, -1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
        rw [e6ia_conj_zPow ![0, -1, -1, -1, -1, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
        rw [show Matrix.mulVec (e6ia_zMat ![0, -1, -1, -1, -1, 0]) (Matrix.mulVec (e6ia_zMat ![-1, -1, -1, -1, -1, -1]) e6ia_vR2) = e6ia_vR2 from by decide]
        rw [e6ia_zPow_vR2]
        exact Subgroup.subset_closure (Or.inr rfl)
    · intro hh
      have h2 := e6ia_conj_mem_rE_of_gens (xr ![0, -1, -1, -1, -1, 0] * xr ![-1, -1, -1, -1, -1, -1])⁻¹ ?_ hh
      · rwa [show (xr ![0, -1, -1, -1, -1, 0] * xr ![-1, -1, -1, -1, -1, -1])⁻¹ * ((xr ![0, -1, -1, -1, -1, 0] * xr ![-1, -1, -1, -1, -1, -1]) * h * (xr ![0, -1, -1, -1, -1, 0] * xr ![-1, -1, -1, -1, -1, -1])⁻¹) * (xr ![0, -1, -1, -1, -1, 0] * xr ![-1, -1, -1, -1, -1, -1])⁻¹⁻¹ = h by group] at h2
      · intro y hy
        rcases hy with rfl | rfl
        ·
          rw [show (xr ![0, -1, -1, -1, -1, 0] * xr ![-1, -1, -1, -1, -1, -1])⁻¹ = xr ![-1, -1, -1, -1, -1, -1] * xr ![0, -1, -1, -1, -1, 0] by
            rw [mul_inv_rev, e6ia_xr_inv ![-1, -1, -1, -1, -1, -1], e6ia_xr_inv ![0, -1, -1, -1, -1, 0]]]
          rw [← e6ia_zPow_vR1]
          rw [show (xr ![-1, -1, -1, -1, -1, -1] * xr ![0, -1, -1, -1, -1, 0]) * e6ia_zPow e6ia_vR1 * (xr ![-1, -1, -1, -1, -1, -1] * xr ![0, -1, -1, -1, -1, 0])⁻¹ =
              xr ![-1, -1, -1, -1, -1, -1] * (xr ![0, -1, -1, -1, -1, 0] * e6ia_zPow e6ia_vR1 * (xr ![0, -1, -1, -1, -1, 0])⁻¹) * (xr ![-1, -1, -1, -1, -1, -1])⁻¹ by group]
          rw [e6ia_conj_zPow ![0, -1, -1, -1, -1, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
          rw [e6ia_conj_zPow ![-1, -1, -1, -1, -1, -1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
          rw [show Matrix.mulVec (e6ia_zMat ![-1, -1, -1, -1, -1, -1]) (Matrix.mulVec (e6ia_zMat ![0, -1, -1, -1, -1, 0]) e6ia_vR1) = e6ia_vR1 from by decide]
          rw [e6ia_zPow_vR1]
          exact Subgroup.subset_closure (Or.inl rfl)
        ·
          rw [show (xr ![0, -1, -1, -1, -1, 0] * xr ![-1, -1, -1, -1, -1, -1])⁻¹ = xr ![-1, -1, -1, -1, -1, -1] * xr ![0, -1, -1, -1, -1, 0] by
            rw [mul_inv_rev, e6ia_xr_inv ![-1, -1, -1, -1, -1, -1], e6ia_xr_inv ![0, -1, -1, -1, -1, 0]]]
          rw [← e6ia_zPow_vR2]
          rw [show (xr ![-1, -1, -1, -1, -1, -1] * xr ![0, -1, -1, -1, -1, 0]) * e6ia_zPow e6ia_vR2 * (xr ![-1, -1, -1, -1, -1, -1] * xr ![0, -1, -1, -1, -1, 0])⁻¹ =
              xr ![-1, -1, -1, -1, -1, -1] * (xr ![0, -1, -1, -1, -1, 0] * e6ia_zPow e6ia_vR2 * (xr ![0, -1, -1, -1, -1, 0])⁻¹) * (xr ![-1, -1, -1, -1, -1, -1])⁻¹ by group]
          rw [e6ia_conj_zPow ![0, -1, -1, -1, -1, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
          rw [e6ia_conj_zPow ![-1, -1, -1, -1, -1, -1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
          rw [show Matrix.mulVec (e6ia_zMat ![-1, -1, -1, -1, -1, -1]) (Matrix.mulVec (e6ia_zMat ![0, -1, -1, -1, -1, 0]) e6ia_vR2) = e6ia_vR2 from by decide]
          rw [e6ia_zPow_vR2]
          exact Subgroup.subset_closure (Or.inr rfl)
  · show xr ![0, -1, -1, -2, -1, 0] * xr ![-1, -1, -1, -2, -1, -1] ∈ Subgroup.normalizer (rE : Set EC)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · refine e6ia_conj_mem_rE_of_gens (xr ![0, -1, -1, -2, -1, 0] * xr ![-1, -1, -1, -2, -1, -1]) ?_
      intro y hy
      rcases hy with rfl | rfl
      ·
        rw [← e6ia_zPow_vR1]
        rw [show (xr ![0, -1, -1, -2, -1, 0] * xr ![-1, -1, -1, -2, -1, -1]) * e6ia_zPow e6ia_vR1 * (xr ![0, -1, -1, -2, -1, 0] * xr ![-1, -1, -1, -2, -1, -1])⁻¹ =
            xr ![0, -1, -1, -2, -1, 0] * (xr ![-1, -1, -1, -2, -1, -1] * e6ia_zPow e6ia_vR1 * (xr ![-1, -1, -1, -2, -1, -1])⁻¹) * (xr ![0, -1, -1, -2, -1, 0])⁻¹ by group]
        rw [e6ia_conj_zPow ![-1, -1, -1, -2, -1, -1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
        rw [e6ia_conj_zPow ![0, -1, -1, -2, -1, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
        rw [show Matrix.mulVec (e6ia_zMat ![0, -1, -1, -2, -1, 0]) (Matrix.mulVec (e6ia_zMat ![-1, -1, -1, -2, -1, -1]) e6ia_vR1) = e6ia_vR1 from by decide]
        rw [e6ia_zPow_vR1]
        exact Subgroup.subset_closure (Or.inl rfl)
      ·
        rw [← e6ia_zPow_vR2]
        rw [show (xr ![0, -1, -1, -2, -1, 0] * xr ![-1, -1, -1, -2, -1, -1]) * e6ia_zPow e6ia_vR2 * (xr ![0, -1, -1, -2, -1, 0] * xr ![-1, -1, -1, -2, -1, -1])⁻¹ =
            xr ![0, -1, -1, -2, -1, 0] * (xr ![-1, -1, -1, -2, -1, -1] * e6ia_zPow e6ia_vR2 * (xr ![-1, -1, -1, -2, -1, -1])⁻¹) * (xr ![0, -1, -1, -2, -1, 0])⁻¹ by group]
        rw [e6ia_conj_zPow ![-1, -1, -1, -2, -1, -1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
        rw [e6ia_conj_zPow ![0, -1, -1, -2, -1, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
        rw [show Matrix.mulVec (e6ia_zMat ![0, -1, -1, -2, -1, 0]) (Matrix.mulVec (e6ia_zMat ![-1, -1, -1, -2, -1, -1]) e6ia_vR2) = e6ia_vR2 from by decide]
        rw [e6ia_zPow_vR2]
        exact Subgroup.subset_closure (Or.inr rfl)
    · intro hh
      have h2 := e6ia_conj_mem_rE_of_gens (xr ![0, -1, -1, -2, -1, 0] * xr ![-1, -1, -1, -2, -1, -1])⁻¹ ?_ hh
      · rwa [show (xr ![0, -1, -1, -2, -1, 0] * xr ![-1, -1, -1, -2, -1, -1])⁻¹ * ((xr ![0, -1, -1, -2, -1, 0] * xr ![-1, -1, -1, -2, -1, -1]) * h * (xr ![0, -1, -1, -2, -1, 0] * xr ![-1, -1, -1, -2, -1, -1])⁻¹) * (xr ![0, -1, -1, -2, -1, 0] * xr ![-1, -1, -1, -2, -1, -1])⁻¹⁻¹ = h by group] at h2
      · intro y hy
        rcases hy with rfl | rfl
        ·
          rw [show (xr ![0, -1, -1, -2, -1, 0] * xr ![-1, -1, -1, -2, -1, -1])⁻¹ = xr ![-1, -1, -1, -2, -1, -1] * xr ![0, -1, -1, -2, -1, 0] by
            rw [mul_inv_rev, e6ia_xr_inv ![-1, -1, -1, -2, -1, -1], e6ia_xr_inv ![0, -1, -1, -2, -1, 0]]]
          rw [← e6ia_zPow_vR1]
          rw [show (xr ![-1, -1, -1, -2, -1, -1] * xr ![0, -1, -1, -2, -1, 0]) * e6ia_zPow e6ia_vR1 * (xr ![-1, -1, -1, -2, -1, -1] * xr ![0, -1, -1, -2, -1, 0])⁻¹ =
              xr ![-1, -1, -1, -2, -1, -1] * (xr ![0, -1, -1, -2, -1, 0] * e6ia_zPow e6ia_vR1 * (xr ![0, -1, -1, -2, -1, 0])⁻¹) * (xr ![-1, -1, -1, -2, -1, -1])⁻¹ by group]
          rw [e6ia_conj_zPow ![0, -1, -1, -2, -1, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR1]
          rw [e6ia_conj_zPow ![-1, -1, -1, -2, -1, -1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
          rw [show Matrix.mulVec (e6ia_zMat ![-1, -1, -1, -2, -1, -1]) (Matrix.mulVec (e6ia_zMat ![0, -1, -1, -2, -1, 0]) e6ia_vR1) = e6ia_vR1 from by decide]
          rw [e6ia_zPow_vR1]
          exact Subgroup.subset_closure (Or.inl rfl)
        ·
          rw [show (xr ![0, -1, -1, -2, -1, 0] * xr ![-1, -1, -1, -2, -1, -1])⁻¹ = xr ![-1, -1, -1, -2, -1, -1] * xr ![0, -1, -1, -2, -1, 0] by
            rw [mul_inv_rev, e6ia_xr_inv ![-1, -1, -1, -2, -1, -1], e6ia_xr_inv ![0, -1, -1, -2, -1, 0]]]
          rw [← e6ia_zPow_vR2]
          rw [show (xr ![-1, -1, -1, -2, -1, -1] * xr ![0, -1, -1, -2, -1, 0]) * e6ia_zPow e6ia_vR2 * (xr ![-1, -1, -1, -2, -1, -1] * xr ![0, -1, -1, -2, -1, 0])⁻¹ =
              xr ![-1, -1, -1, -2, -1, -1] * (xr ![0, -1, -1, -2, -1, 0] * e6ia_zPow e6ia_vR2 * (xr ![0, -1, -1, -2, -1, 0])⁻¹) * (xr ![-1, -1, -1, -2, -1, -1])⁻¹ by group]
          rw [e6ia_conj_zPow ![0, -1, -1, -2, -1, 0] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) e6ia_vR2]
          rw [e6ia_conj_zPow ![-1, -1, -1, -2, -1, -1] (by exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide)]
          rw [show Matrix.mulVec (e6ia_zMat ![-1, -1, -1, -2, -1, -1]) (Matrix.mulVec (e6ia_zMat ![0, -1, -1, -2, -1, 0]) e6ia_vR2) = e6ia_vR2 from by decide]
          rw [e6ia_zPow_vR2]
          exact Subgroup.subset_closure (Or.inr rfl)

private theorem e6ia_l1Root_isRoot
    (i : Fin 16) : IsRoot .E6 (l1Root i) := by
  fin_cases i <;>
    exact CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)

private theorem e6ia_l1Root_level 
    (i : Fin 16) : iform (l1Root i) lamE = 1 := by
  fin_cases i <;> decide

private theorem e6ia_qE_closure :
    qE = Subgroup.closure {g : EC | ∃ β ∈ qRoots, xr β = g} := by
  ext q
  constructor
  · intro hq
    have hq' : (q : ModGL .E6 F2) ∈ rootSpan .E6 F2 qRoots := by
      rwa [show qE = (rootSpan .E6 F2 qRoots).subgroupOf (adjointGroup .E6 F2) from rfl,
        Subgroup.mem_subgroupOf] at hq
    have hmap : (q : ModGL .E6 F2) ∈
        (Subgroup.closure {g : EC | ∃ β ∈ qRoots, xr β = g}).map
          (adjointGroup .E6 F2).subtype := by
      have hle : rootSpan .E6 F2 qRoots ≤
          (Subgroup.closure {g : EC | ∃ β ∈ qRoots, xr β = g}).map
            (adjointGroup .E6 F2).subtype := by
        refine iSup₂_le fun β hβ => ?_
        rw [rootSubgroup, Subgroup.closure_le]
        rintro g ⟨c, rfl⟩
        rcases e6ia_F2_eq_zero_or_one c with rfl | rfl
        · exact ⟨1, Subgroup.one_mem _, by rw [pinnedX_zero .E6 F2 β]; rfl⟩
        · exact ⟨xr β, Subgroup.subset_closure ⟨β, hβ, rfl⟩, rfl⟩
      exact hle hq'
    rw [Subgroup.mem_map] at hmap
    obtain ⟨x, hx, hxq⟩ := hmap
    have hxq' : x = q := Subtype.ext hxq
    rwa [← hxq']
  · intro hq
    have hle : Subgroup.closure {g : EC | ∃ β ∈ qRoots, xr β = g} ≤ qE := by
      refine (Subgroup.closure_le _).2 ?_
      rintro g ⟨β, hβ, rfl⟩
      change (xr β : ModGL .E6 F2) ∈ rootSpan .E6 F2 qRoots
      simpa only [xr] using pinnedX_mem_rootSpan hβ (1 : F2)
    have hqE : q ∈ qE := hle hq
    rwa [show qE = (rootSpan .E6 F2 qRoots).subgroupOf (adjointGroup .E6 F2) from rfl,
      Subgroup.mem_subgroupOf] at hqE

private def e6ia_shiftMat (γ : Fin Tag.E6.rank → ℤ) : Matrix (Fin 16) (Fin 16) (ZMod 2) :=
  fun i j => (if i = j then 1 else 0) + (if l1Root i = l1Root j + γ then 1 else 0)

private theorem e6ia_l1Root_injective : Function.Injective l1Root := by decide

private theorem e6ia_l1Root_add_exists
    {γ : Fin Tag.E6.rank → ℤ} (hγ0 : iform γ lamE = 0) (j : Fin 16)
    (h : IsRoot .E6 (l1Root j + γ)) : ∃ i : Fin 16, l1Root i = l1Root j + γ :=
  e6ia_level1_exists h (by rw [iform_add_left, e6ia_l1Root_level j, hγ0, add_zero])

private theorem e6ia_l1Root_ne 
    {γ : Fin Tag.E6.rank → ℤ} (hγ0 : iform γ lamE = 0) (j : Fin 16) : l1Root j ≠ γ := by
  intro h
  have h1 : iform (l1Root j) lamE = 1 := e6ia_l1Root_level j
  rw [h, hγ0] at h1
  omega

private theorem e6ia_l1Root_ne_neg 
    {γ : Fin Tag.E6.rank → ℤ} (hγ0 : iform γ lamE = 0) (j : Fin 16) : l1Root j ≠ -γ := by
  intro h
  have h1 : iform (l1Root j) lamE = 1 := e6ia_l1Root_level j
  rw [h, iform_neg_left, hγ0, neg_zero] at h1
  omega

private theorem e6ia_l1Root_ne' 
    {γ : Fin Tag.E6.rank → ℤ} (hγ0 : iform γ lamE = 0) (j : Fin 16) : γ ≠ l1Root j :=
  (e6ia_l1Root_ne hγ0 j).symm

private theorem e6ia_l1Root_ne_neg' 
    {γ : Fin Tag.E6.rank → ℤ} (hγ0 : iform γ lamE = 0) (j : Fin 16) : γ ≠ -l1Root j := by
  intro h
  exact e6ia_l1Root_ne_neg hγ0 j (by rw [h, neg_neg])

private theorem e6ia_xr_conj_of_isRoot
    {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β) (hne : α ≠ β)
    (hne' : α ≠ -β) (h : IsRoot .E6 (α + β)) :
    xr α * xr β * (xr α)⁻¹ = xr (α + β) * xr β := by
  apply Subtype.ext
  show pinnedX .E6 F2 α 1 * pinnedX .E6 F2 β 1 * (pinnedX .E6 F2 α 1)⁻¹ =
    pinnedX .E6 F2 (α + β) 1 * pinnedX .E6 F2 β 1
  rw [CFSG.LieType.Chevalley.EvenOddRadical.pinnedX_conj_of_isRoot (Or.inr (Or.inl rfl)) gf2_two
    hα hβ hne hne' h 1 1, one_mul]

private theorem e6ia_xr_conj_of_not
    {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β) (hne : α ≠ β)
    (hne' : α ≠ -β) (h : ¬ IsRoot .E6 (α + β)) :
    xr α * xr β * (xr α)⁻¹ = xr β := by
  apply Subtype.ext
  show pinnedX .E6 F2 α 1 * pinnedX .E6 F2 β 1 * (pinnedX .E6 F2 α 1)⁻¹ = pinnedX .E6 F2 β 1
  exact CFSG.LieType.Chevalley.EvenOddRadical.pinnedX_conj_of_not (Or.inr (Or.inl rfl))
    hα hβ hne hne' h 1 1

private theorem e6ia_shiftMat_col_root 
    {γ : Fin Tag.E6.rank → ℤ} {j i : Fin 16} (hi : l1Root i = l1Root j + γ) :
    Matrix.mulVec (e6ia_shiftMat γ) (Pi.single j 1) = Pi.single j 1 + Pi.single i 1 := by
  rw [Matrix.mulVec_single_one]
  funext i'
  simp only [e6ia_shiftMat, Matrix.col_apply, Pi.add_apply, Pi.single_apply]
  by_cases h : i' = i
  · subst h
    rw [if_pos hi, if_pos rfl]
  · have h2 : ¬ (l1Root i' = l1Root j + γ) := by
      intro hh; exact h (e6ia_l1Root_injective (hh.trans hi.symm))
    rw [if_neg h2, if_neg h]

private theorem e6ia_shiftMat_col_not
    {γ : Fin Tag.E6.rank → ℤ} {j : Fin 16} (hr : ¬ IsRoot .E6 (l1Root j + γ)) :
    Matrix.mulVec (e6ia_shiftMat γ) (Pi.single j 1) = Pi.single j 1 := by
  rw [Matrix.mulVec_single_one]
  funext i'
  simp only [e6ia_shiftMat, Matrix.col_apply, Pi.add_apply, Pi.single_apply]
  have h2 : ¬ (l1Root i' = l1Root j + γ) := by
    intro h
    exact hr (h ▸ e6ia_l1Root_isRoot i')
  rw [if_neg h2, add_zero]

private theorem e6ia_c_eq_one_of_mem_z0E
    {c : ↥qE →* Multiplicative e6TwoRestQV} (hc : IsQCoord c) {x : ↥qE} (hx : (x : EC) ∈ z0E) :
    c x = 1 := by
  rw [← MonoidHom.mem_ker, hc.2.1]
  exact hx

private theorem e6ia_shiftMat_action
    (γ : Fin Tag.E6.rank → ℤ) (hγ : IsRoot .E6 γ) (hγ0 : iform γ lamE = 0)
    (c : ↥qE →* Multiplicative e6TwoRestQV) (hc : IsQCoord c) (j : Fin 16) :
    ∃ h : xr γ * xr (l1Root j) * (xr γ)⁻¹ ∈ qE,
      c ⟨xr γ * xr (l1Root j) * (xr γ)⁻¹, h⟩ =
        Multiplicative.ofAdd (Matrix.mulVec (e6ia_shiftMat γ) (Pi.single j 1)) := by
  refine ⟨e6ia_qE_conj_mem γ hγ hγ0 (xr_l1Root_mem_qE j), ?_⟩
  by_cases hr : IsRoot .E6 (l1Root j + γ)
  · obtain ⟨i, hi⟩ := e6ia_l1Root_add_exists hγ0 j hr
    have hmem : xr (γ + l1Root j) * xr (l1Root j) ∈ qE := by
      rw [← e6ia_xr_conj_of_isRoot hγ (e6ia_l1Root_isRoot j) (e6ia_l1Root_ne' hγ0 j)
        (e6ia_l1Root_ne_neg' hγ0 j) (by rw [add_comm]; exact hr)]
      exact e6ia_qE_conj_mem γ hγ hγ0 (xr_l1Root_mem_qE j)
    have hconj : (⟨xr γ * xr (l1Root j) * (xr γ)⁻¹,
          e6ia_qE_conj_mem γ hγ hγ0 (xr_l1Root_mem_qE j)⟩ : ↥qE) =
        ⟨xr (γ + l1Root j) * xr (l1Root j), hmem⟩ :=
      Subtype.ext (e6ia_xr_conj_of_isRoot hγ (e6ia_l1Root_isRoot j) (e6ia_l1Root_ne' hγ0 j)
        (e6ia_l1Root_ne_neg' hγ0 j) (by rw [add_comm]; exact hr))
    rw [hconj, e6ia_shiftMat_col_root hi]
    rw [show (⟨xr (γ + l1Root j) * xr (l1Root j), hmem⟩ : ↥qE) =
        ⟨xr (l1Root i), xr_l1Root_mem_qE i⟩ * ⟨xr (l1Root j), xr_l1Root_mem_qE j⟩
        from Subtype.ext (show xr (γ + l1Root j) * xr (l1Root j) = xr (l1Root i) * xr (l1Root j) by
          rw [show γ + l1Root j = l1Root i from by rw [add_comm]; exact hi.symm]),
      map_mul, hc.2.2 i, hc.2.2 j, ofAdd_add, mul_comm]
  · have hconj : (⟨xr γ * xr (l1Root j) * (xr γ)⁻¹,
          e6ia_qE_conj_mem γ hγ hγ0 (xr_l1Root_mem_qE j)⟩ : ↥qE) =
        ⟨xr (l1Root j), xr_l1Root_mem_qE j⟩ :=
      Subtype.ext (e6ia_xr_conj_of_not hγ (e6ia_l1Root_isRoot j) (e6ia_l1Root_ne' hγ0 j)
        (e6ia_l1Root_ne_neg' hγ0 j) (by rw [add_comm]; exact hr))
    rw [hconj, e6ia_shiftMat_col_not hr, hc.2.2 j]

private noncomputable def e6ia_shiftHom
    (γ : Fin Tag.E6.rank → ℤ) (c : ↥qE →* Multiplicative e6TwoRestQV) : ↥qE →* Multiplicative e6TwoRestQV where
  toFun q := Multiplicative.ofAdd (Matrix.mulVec (e6ia_shiftMat γ) (Multiplicative.toAdd (c q)))
  map_one' := by simp
  map_mul' q r := by
    simp only [map_mul, toAdd_mul, Matrix.mulVec_add, ofAdd_add]

private theorem e6ia_toAdd_one : Multiplicative.toAdd (1 : Multiplicative e6TwoRestQV) = 0 := rfl

private theorem e6ia_shiftMat_action_qE
    (γ : Fin Tag.E6.rank → ℤ) (hγ : IsRoot .E6 γ) (hγ0 : iform γ lamE = 0)
    (c : ↥qE →* Multiplicative e6TwoRestQV) (hc : IsQCoord c) (q : ↥qE) :
    ∃ h : xr γ * (q : EC) * (xr γ)⁻¹ ∈ qE,
      c ⟨xr γ * (q : EC) * (xr γ)⁻¹, h⟩ = e6ia_shiftHom γ c q := by
  refine ⟨e6ia_qE_conj_mem γ hγ hγ0 q.2, ?_⟩
  have key : ∀ g ∈ Subgroup.closure {g : EC | ∃ β ∈ qRoots, xr β = g},
      ∀ (hg : g ∈ qE),
        c ⟨xr γ * g * (xr γ)⁻¹, e6ia_qE_conj_mem γ hγ hγ0 hg⟩ =
          e6ia_shiftHom γ c ⟨g, hg⟩ := by
    intro g hgS
    induction hgS using Subgroup.closure_induction with
    | mem y hy =>
      intro hg
      obtain ⟨β, hβ, rfl⟩ := hy
      have hβle : iform β lamE ≤ 2 := e6ia_level_le_two hβ.1
      have hβpos : 0 < iform β lamE := hβ.2
      rcases (by omega : iform β lamE = 1 ∨ iform β lamE = 2) with hlev | hlev
      · obtain ⟨j, hj⟩ := e6ia_level1_exists hβ.1 hlev
        subst hj
        obtain ⟨h1, h2⟩ := e6ia_shiftMat_action γ hγ hγ0 c hc j
        have hsub1 : (⟨xr (l1Root j), hg⟩ : ↥qE) =
            ⟨xr (l1Root j), xr_l1Root_mem_qE j⟩ := Subtype.ext rfl
        have hsub2 : (⟨xr γ * xr (l1Root j) * (xr γ)⁻¹, e6ia_qE_conj_mem γ hγ hγ0 hg⟩ : ↥qE) =
            ⟨xr γ * xr (l1Root j) * (xr γ)⁻¹, e6ia_qE_conj_mem γ hγ hγ0 (xr_l1Root_mem_qE j)⟩ :=
          Subtype.ext rfl
        have hshift : e6ia_shiftHom γ c ⟨xr (l1Root j), xr_l1Root_mem_qE j⟩ =
            Multiplicative.ofAdd (Matrix.mulVec (e6ia_shiftMat γ) (Pi.single j 1)) := by
          show Multiplicative.ofAdd (Matrix.mulVec (e6ia_shiftMat γ)
            (Multiplicative.toAdd (c ⟨xr (l1Root j), xr_l1Root_mem_qE j⟩))) = _
          rw [hc.2.2 j, toAdd_ofAdd]
        rw [hsub1, hshift, hsub2]
        exact h2
      · have hz : xr β ∈ z0E := by
          rw [show z0E = (rootSpan .E6 F2 zRoots).subgroupOf (adjointGroup .E6 F2) from rfl,
            Subgroup.mem_subgroupOf]
          simpa only [xr] using pinnedX_mem_rootSpan (S := zRoots) ⟨hβ.1, hlev⟩ (1 : F2)
        have h1 : c ⟨xr β, hg⟩ = 1 := e6ia_c_eq_one_of_mem_z0E hc hz
        have h2 : c ⟨xr γ * xr β * (xr γ)⁻¹, e6ia_qE_conj_mem γ hγ hγ0 hg⟩ = 1 :=
          e6ia_c_eq_one_of_mem_z0E hc (e6ia_z0E_conj_mem γ hγ hγ0 hz)
        have h3 : e6ia_shiftHom γ c ⟨xr β, hg⟩ = 1 := by
          show Multiplicative.ofAdd (Matrix.mulVec (e6ia_shiftMat γ)
            (Multiplicative.toAdd (c ⟨xr β, hg⟩))) = 1
          rw [h1, e6ia_toAdd_one, Matrix.mulVec_zero, ofAdd_zero]
        rw [h2, h3]
    | one =>
      intro hg
      rw [show (⟨1, hg⟩ : ↥qE) = 1 from Subtype.ext rfl]
      rw [show (⟨xr γ * 1 * (xr γ)⁻¹, e6ia_qE_conj_mem γ hγ hγ0 hg⟩ : ↥qE) = 1 from
        Subtype.ext (by rw [Subgroup.coe_one]; group)]
      rw [map_one, map_one]
    | mul y z hy hz ihy ihz =>
      intro hg
      have hy' : y ∈ qE := e6ia_qE_closure ▸ hy
      have hz' : z ∈ qE := e6ia_qE_closure ▸ hz
      have h1 : (⟨y * z, hg⟩ : ↥qE) = ⟨y, hy'⟩ * ⟨z, hz'⟩ := Subtype.ext rfl
      have h2 : (⟨xr γ * (y * z) * (xr γ)⁻¹, e6ia_qE_conj_mem γ hγ hγ0 hg⟩ : ↥qE) =
          ⟨xr γ * y * (xr γ)⁻¹, e6ia_qE_conj_mem γ hγ hγ0 hy'⟩ *
            ⟨xr γ * z * (xr γ)⁻¹, e6ia_qE_conj_mem γ hγ hγ0 hz'⟩ :=
        Subtype.ext (by simp only [Subgroup.coe_mul]; group)
      rw [h1, h2, map_mul, map_mul, ihy hy', ihz hz']
    | inv y hy ihy =>
      intro hg
      have hy' : y ∈ qE := e6ia_qE_closure ▸ hy
      have h1 : (⟨y⁻¹, hg⟩ : ↥qE) = (⟨y, hy'⟩)⁻¹ := Subtype.ext rfl
      have h2 : (⟨xr γ * y⁻¹ * (xr γ)⁻¹, e6ia_qE_conj_mem γ hγ hγ0 hg⟩ : ↥qE) =
          (⟨xr γ * y * (xr γ)⁻¹, e6ia_qE_conj_mem γ hγ hγ0 hy'⟩)⁻¹ :=
        Subtype.ext (by simp only [Subgroup.coe_inv]; group)
      rw [h1, h2, map_inv, map_inv, ihy hy']
  exact key (q : EC) (e6ia_qE_closure ▸ q.2) q.2

private theorem e6ia_shiftMat_mul_action
    (γ₁ γ₂ : Fin Tag.E6.rank → ℤ) (hγ₁ : IsRoot .E6 γ₁) (hγ₁0 : iform γ₁ lamE = 0)
    (hγ₂ : IsRoot .E6 γ₂) (hγ₂0 : iform γ₂ lamE = 0)
    (c : ↥qE →* Multiplicative e6TwoRestQV) (hc : IsQCoord c) (q : ↥qE) :
    ∃ h : xr γ₁ * xr γ₂ * (q : EC) * (xr γ₁ * xr γ₂)⁻¹ ∈ qE,
      c ⟨xr γ₁ * xr γ₂ * (q : EC) * (xr γ₁ * xr γ₂)⁻¹, h⟩ =
        Multiplicative.ofAdd ((e6ia_shiftMat γ₁ * e6ia_shiftMat γ₂).mulVec
          (Multiplicative.toAdd (c q))) := by
  obtain ⟨h₂, eq₂⟩ := e6ia_shiftMat_action_qE γ₂ hγ₂ hγ₂0 c hc q
  obtain ⟨h₁, eq₁⟩ := e6ia_shiftMat_action_qE γ₁ hγ₁ hγ₁0 c hc
    ⟨xr γ₂ * (q : EC) * (xr γ₂)⁻¹, h₂⟩
  have hterm : xr γ₁ * (xr γ₂ * (q : EC) * (xr γ₂)⁻¹) * (xr γ₁)⁻¹ =
      xr γ₁ * xr γ₂ * (q : EC) * (xr γ₁ * xr γ₂)⁻¹ := by group
  have hB : xr γ₁ * xr γ₂ * (q : EC) * (xr γ₁ * xr γ₂)⁻¹ ∈ qE := by
    rw [← hterm]; exact h₁
  refine ⟨hB, ?_⟩
  have hsub : (⟨xr γ₁ * xr γ₂ * (q : EC) * (xr γ₁ * xr γ₂)⁻¹, hB⟩ : ↥qE) =
      ⟨xr γ₁ * (xr γ₂ * (q : EC) * (xr γ₂)⁻¹) * (xr γ₁)⁻¹, h₁⟩ :=
    Subtype.ext hterm.symm
  rw [hsub, eq₁]
  change Multiplicative.ofAdd (Matrix.mulVec (e6ia_shiftMat γ₁)
      (Multiplicative.toAdd (c ⟨xr γ₂ * (q : EC) * (xr γ₂)⁻¹, h₂⟩))) =
    Multiplicative.ofAdd ((e6ia_shiftMat γ₁ * e6ia_shiftMat γ₂).mulVec
      (Multiplicative.toAdd (c q)))
  rw [eq₂]
  change Multiplicative.ofAdd (Matrix.mulVec (e6ia_shiftMat γ₁)
      (Multiplicative.toAdd (Multiplicative.ofAdd (Matrix.mulVec (e6ia_shiftMat γ₂)
        (Multiplicative.toAdd (c q)))))) =
    Multiplicative.ofAdd ((e6ia_shiftMat γ₁ * e6ia_shiftMat γ₂).mulVec
      (Multiplicative.toAdd (c q)))
  rw [toAdd_ofAdd, Matrix.mulVec_mulVec]

private theorem e6ia_invMat_0 : invMat 0 = e6ia_shiftMat ![1, 2, 2, 3, 2, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

private theorem e6ia_invMat_1 : invMat 1 = e6ia_shiftMat ![-1, -2, -2, -3, -2, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

private theorem e6ia_invMat_2 : invMat 2 = e6ia_shiftMat ![0, 0, 0, 1, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

private theorem e6ia_invMat_3 : invMat 3 = e6ia_shiftMat ![0, 0, 0, -1, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

private theorem e6ia_invMat_4 : invMat 4 =
    e6ia_shiftMat ![1, 0, 0, 0, 0, 0] * e6ia_shiftMat ![-1, 0, 0, 0, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

private theorem e6ia_invMat_5 : invMat 5 =
    e6ia_shiftMat ![1, 0, 0, 0, 0, 0] * e6ia_shiftMat ![0, 0, 0, 0, 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

private theorem e6ia_invMat_6 : invMat 6 =
    e6ia_shiftMat ![1, 0, 0, 0, 0, 0] * e6ia_shiftMat ![0, 0, 0, 0, 0, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

private theorem e6ia_invMat_7 : invMat 7 =
    e6ia_shiftMat ![-1, 0, 0, 0, 0, 0] * e6ia_shiftMat ![0, 0, 0, 0, 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

private theorem e6ia_invMat_8 : invMat 8 =
    e6ia_shiftMat ![-1, 0, 0, 0, 0, 0] * e6ia_shiftMat ![0, 0, 0, 0, 0, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

private theorem e6ia_invMat_9 : invMat 9 =
    e6ia_shiftMat ![0, 0, 0, 0, 0, 1] * e6ia_shiftMat ![0, 0, 0, 0, 0, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

private theorem e6ia_invMat_10 : invMat 10 =
    e6ia_shiftMat ![1, 1, 1, 2, 1, 1] * e6ia_shiftMat ![0, 1, 1, 2, 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

private theorem e6ia_invMat_11 : invMat 11 =
    e6ia_shiftMat ![1, 1, 1, 1, 1, 1] * e6ia_shiftMat ![0, 1, 1, 1, 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

private theorem e6ia_invMat_12 : invMat 12 =
    e6ia_shiftMat ![0, -1, -1, -1, -1, 0] * e6ia_shiftMat ![-1, -1, -1, -1, -1, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

private theorem e6ia_invMat_13 : invMat 13 =
    e6ia_shiftMat ![0, -1, -1, -2, -1, 0] * e6ia_shiftMat ![-1, -1, -1, -2, -1, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem invWord_action
    {c : ↥qE →* Multiplicative e6TwoRestQV} (hc : IsQCoord c) (k : Fin 14) (q : ↥qE) :
    ∃ h : e6TwoRestInvWord k * (q : EC) * (e6TwoRestInvWord k)⁻¹ ∈ qE,
      c ⟨e6TwoRestInvWord k * (q : EC) * (e6TwoRestInvWord k)⁻¹, h⟩ =
        Multiplicative.ofAdd ((invMat k).mulVec (Multiplicative.toAdd (c q))) := by
  fin_cases k
  · show ∃ h : xr ![1, 2, 2, 3, 2, 1] * (q : EC) * (xr ![1, 2, 2, 3, 2, 1])⁻¹ ∈ qE,
        c ⟨xr ![1, 2, 2, 3, 2, 1] * (q : EC) * (xr ![1, 2, 2, 3, 2, 1])⁻¹, h⟩ =
          Multiplicative.ofAdd ((invMat 0).mulVec (Multiplicative.toAdd (c q)))
    rw [e6ia_invMat_0]
    exact e6ia_shiftMat_action_qE ![1, 2, 2, 3, 2, 1]
      (CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) c hc q
  · show ∃ h : xr ![-1, -2, -2, -3, -2, -1] * (q : EC) * (xr ![-1, -2, -2, -3, -2, -1])⁻¹ ∈ qE,
        c ⟨xr ![-1, -2, -2, -3, -2, -1] * (q : EC) * (xr ![-1, -2, -2, -3, -2, -1])⁻¹, h⟩ =
          Multiplicative.ofAdd ((invMat 1).mulVec (Multiplicative.toAdd (c q)))
    rw [e6ia_invMat_1]
    exact e6ia_shiftMat_action_qE ![-1, -2, -2, -3, -2, -1]
      (CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) c hc q
  · show ∃ h : xr ![0, 0, 0, 1, 0, 0] * (q : EC) * (xr ![0, 0, 0, 1, 0, 0])⁻¹ ∈ qE,
        c ⟨xr ![0, 0, 0, 1, 0, 0] * (q : EC) * (xr ![0, 0, 0, 1, 0, 0])⁻¹, h⟩ =
          Multiplicative.ofAdd ((invMat 2).mulVec (Multiplicative.toAdd (c q)))
    rw [e6ia_invMat_2]
    exact e6ia_shiftMat_action_qE ![0, 0, 0, 1, 0, 0]
      (CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) c hc q
  · show ∃ h : xr ![0, 0, 0, -1, 0, 0] * (q : EC) * (xr ![0, 0, 0, -1, 0, 0])⁻¹ ∈ qE,
        c ⟨xr ![0, 0, 0, -1, 0, 0] * (q : EC) * (xr ![0, 0, 0, -1, 0, 0])⁻¹, h⟩ =
          Multiplicative.ofAdd ((invMat 3).mulVec (Multiplicative.toAdd (c q)))
    rw [e6ia_invMat_3]
    exact e6ia_shiftMat_action_qE ![0, 0, 0, -1, 0, 0]
      (CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) c hc q
  · show ∃ h : xr ![1, 0, 0, 0, 0, 0] * xr ![-1, 0, 0, 0, 0, 0] * (q : EC) * (xr ![1, 0, 0, 0, 0, 0] * xr ![-1, 0, 0, 0, 0, 0])⁻¹ ∈ qE,
        c ⟨xr ![1, 0, 0, 0, 0, 0] * xr ![-1, 0, 0, 0, 0, 0] * (q : EC) * (xr ![1, 0, 0, 0, 0, 0] * xr ![-1, 0, 0, 0, 0, 0])⁻¹, h⟩ =
          Multiplicative.ofAdd ((invMat 4).mulVec (Multiplicative.toAdd (c q)))
    rw [e6ia_invMat_4]
    exact e6ia_shiftMat_mul_action ![1, 0, 0, 0, 0, 0] ![-1, 0, 0, 0, 0, 0]
      (CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) (CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) c hc q
  · show ∃ h : xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1] * (q : EC) * (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1])⁻¹ ∈ qE,
        c ⟨xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1] * (q : EC) * (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1])⁻¹, h⟩ =
          Multiplicative.ofAdd ((invMat 5).mulVec (Multiplicative.toAdd (c q)))
    rw [e6ia_invMat_5]
    exact e6ia_shiftMat_mul_action ![1, 0, 0, 0, 0, 0] ![0, 0, 0, 0, 0, 1]
      (CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) (CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) c hc q
  · show ∃ h : xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1] * (q : EC) * (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1])⁻¹ ∈ qE,
        c ⟨xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1] * (q : EC) * (xr ![1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1])⁻¹, h⟩ =
          Multiplicative.ofAdd ((invMat 6).mulVec (Multiplicative.toAdd (c q)))
    rw [e6ia_invMat_6]
    exact e6ia_shiftMat_mul_action ![1, 0, 0, 0, 0, 0] ![0, 0, 0, 0, 0, -1]
      (CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) (CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) c hc q
  · show ∃ h : xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1] * (q : EC) * (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1])⁻¹ ∈ qE,
        c ⟨xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1] * (q : EC) * (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, 1])⁻¹, h⟩ =
          Multiplicative.ofAdd ((invMat 7).mulVec (Multiplicative.toAdd (c q)))
    rw [e6ia_invMat_7]
    exact e6ia_shiftMat_mul_action ![-1, 0, 0, 0, 0, 0] ![0, 0, 0, 0, 0, 1]
      (CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) (CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) c hc q
  · show ∃ h : xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1] * (q : EC) * (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1])⁻¹ ∈ qE,
        c ⟨xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1] * (q : EC) * (xr ![-1, 0, 0, 0, 0, 0] * xr ![0, 0, 0, 0, 0, -1])⁻¹, h⟩ =
          Multiplicative.ofAdd ((invMat 8).mulVec (Multiplicative.toAdd (c q)))
    rw [e6ia_invMat_8]
    exact e6ia_shiftMat_mul_action ![-1, 0, 0, 0, 0, 0] ![0, 0, 0, 0, 0, -1]
      (CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) (CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) c hc q
  · show ∃ h : xr ![0, 0, 0, 0, 0, 1] * xr ![0, 0, 0, 0, 0, -1] * (q : EC) * (xr ![0, 0, 0, 0, 0, 1] * xr ![0, 0, 0, 0, 0, -1])⁻¹ ∈ qE,
        c ⟨xr ![0, 0, 0, 0, 0, 1] * xr ![0, 0, 0, 0, 0, -1] * (q : EC) * (xr ![0, 0, 0, 0, 0, 1] * xr ![0, 0, 0, 0, 0, -1])⁻¹, h⟩ =
          Multiplicative.ofAdd ((invMat 9).mulVec (Multiplicative.toAdd (c q)))
    rw [e6ia_invMat_9]
    exact e6ia_shiftMat_mul_action ![0, 0, 0, 0, 0, 1] ![0, 0, 0, 0, 0, -1]
      (CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) (CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) c hc q
  · show ∃ h : xr ![1, 1, 1, 2, 1, 1] * xr ![0, 1, 1, 2, 1, 0] * (q : EC) * (xr ![1, 1, 1, 2, 1, 1] * xr ![0, 1, 1, 2, 1, 0])⁻¹ ∈ qE,
        c ⟨xr ![1, 1, 1, 2, 1, 1] * xr ![0, 1, 1, 2, 1, 0] * (q : EC) * (xr ![1, 1, 1, 2, 1, 1] * xr ![0, 1, 1, 2, 1, 0])⁻¹, h⟩ =
          Multiplicative.ofAdd ((invMat 10).mulVec (Multiplicative.toAdd (c q)))
    rw [e6ia_invMat_10]
    exact e6ia_shiftMat_mul_action ![1, 1, 1, 2, 1, 1] ![0, 1, 1, 2, 1, 0]
      (CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) (CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) c hc q
  · show ∃ h : xr ![1, 1, 1, 1, 1, 1] * xr ![0, 1, 1, 1, 1, 0] * (q : EC) * (xr ![1, 1, 1, 1, 1, 1] * xr ![0, 1, 1, 1, 1, 0])⁻¹ ∈ qE,
        c ⟨xr ![1, 1, 1, 1, 1, 1] * xr ![0, 1, 1, 1, 1, 0] * (q : EC) * (xr ![1, 1, 1, 1, 1, 1] * xr ![0, 1, 1, 1, 1, 0])⁻¹, h⟩ =
          Multiplicative.ofAdd ((invMat 11).mulVec (Multiplicative.toAdd (c q)))
    rw [e6ia_invMat_11]
    exact e6ia_shiftMat_mul_action ![1, 1, 1, 1, 1, 1] ![0, 1, 1, 1, 1, 0]
      (CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) (CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) c hc q
  · show ∃ h : xr ![0, -1, -1, -1, -1, 0] * xr ![-1, -1, -1, -1, -1, -1] * (q : EC) * (xr ![0, -1, -1, -1, -1, 0] * xr ![-1, -1, -1, -1, -1, -1])⁻¹ ∈ qE,
        c ⟨xr ![0, -1, -1, -1, -1, 0] * xr ![-1, -1, -1, -1, -1, -1] * (q : EC) * (xr ![0, -1, -1, -1, -1, 0] * xr ![-1, -1, -1, -1, -1, -1])⁻¹, h⟩ =
          Multiplicative.ofAdd ((invMat 12).mulVec (Multiplicative.toAdd (c q)))
    rw [e6ia_invMat_12]
    exact e6ia_shiftMat_mul_action ![0, -1, -1, -1, -1, 0] ![-1, -1, -1, -1, -1, -1]
      (CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) (CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) c hc q
  · show ∃ h : xr ![0, -1, -1, -2, -1, 0] * xr ![-1, -1, -1, -2, -1, -1] * (q : EC) * (xr ![0, -1, -1, -2, -1, 0] * xr ![-1, -1, -1, -2, -1, -1])⁻¹ ∈ qE,
        c ⟨xr ![0, -1, -1, -2, -1, 0] * xr ![-1, -1, -1, -2, -1, -1] * (q : EC) * (xr ![0, -1, -1, -2, -1, 0] * xr ![-1, -1, -1, -2, -1, -1])⁻¹, h⟩ =
          Multiplicative.ofAdd ((invMat 13).mulVec (Multiplicative.toAdd (c q)))
    rw [e6ia_invMat_13]
    exact e6ia_shiftMat_mul_action ![0, -1, -1, -2, -1, 0] ![-1, -1, -1, -2, -1, -1]
      (CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) (CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (by decide)) (by decide) c hc q

end CFSG.StandardType.GGSixE6Two
