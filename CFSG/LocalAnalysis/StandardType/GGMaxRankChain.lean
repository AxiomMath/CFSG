module

public import CFSG.LocalAnalysis.StandardType.GGMaxRankWeyl
public import CFSG.LocalAnalysis.StandardType.GGMaxRankChainAux
public import CFSG.LocalAnalysis.StandardType.GGCoxReflConv

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.Assembly
open CFSG.LieType.RootSystem


private lemma l6m7_reindex_refl {ι : Type} (M : CoxeterMatrix ι) :
    M = M.reindex (Equiv.refl ι) := by
  apply CoxeterMatrix.ext
  ext i j
  rw [CoxeterMatrix.reindex_apply]
  simp

private lemma l6m7_isWeylMatrix_E8 : GGIsWeylMatrix CoxeterMatrix.E₈ :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, l6m7_reindex_refl _⟩)))

private lemma l6m7_le_three_E8 (i j : Fin 8) (hij : i ≠ j) :
    (CoxeterMatrix.E₈).M i j ≤ 3 := by
  fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₈]

private lemma l6m7_M_three_iff_adj (i j : Fin 8) (hij : i ≠ j) :
    (CoxeterMatrix.A 8).M i j = 3 ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  fin_cases i <;> fin_cases j <;> decide

private lemma l6m7_M_two_or_three (i j : Fin 8) (hij : i ≠ j) :
    (CoxeterMatrix.A 8).M i j = 2 ∨ (CoxeterMatrix.A 8).M i j = 3 := by
  fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.A]

private lemma l6m7_cartanA_eq_neg_one_of_M_three (i j : Fin 8) (hij : i ≠ j)
    (hm : (CoxeterMatrix.A 8).M i j = 3) : CartanMatrix.A 8 i j = -1 := by
  fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.A, CartanMatrix.A]

private lemma l6m7_cartanA_eq_zero_of_M_two (i j : Fin 8) (hij : i ≠ j)
    (hm : (CoxeterMatrix.A 8).M i j = 2) : CartanMatrix.A 8 i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.A, CartanMatrix.A]

private lemma l6m7_cartanA_self (i : Fin 8) : CartanMatrix.A 8 i i = 2 := by
  simp [CartanMatrix.A]

private theorem l6m7_ggE8Equiv_inv (w : CoxeterMatrix.E₈.Group) :
    ggE8Equiv w⁻¹ = (ggE8Equiv w)⁻¹ := by
  have h : ggE8Equiv (w * w⁻¹) = 1 := by
    have h1 : ggE8Equiv (w * w⁻¹) * ggE8Equiv w = ggE8Equiv w := by
      rw [← map_mul ggE8Equiv (w * w⁻¹) w]
      congr 1
      group
    exact mul_right_cancel (h1.trans (one_mul (ggE8Equiv w)).symm)
  have h2 : ggE8Equiv w * ggE8Equiv w⁻¹ = 1 := by
    rw [← map_mul ggE8Equiv w w⁻¹, h]
  exact eq_inv_of_mul_eq_one_right h2

theorem ggMaxRank_chainRoots
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (f : CoxeterMatrix.E₈.Group ≃* ↥(ggAutomizer X Bs))
    (hrefl : ∀ i, GGIsReflection p ((f (CoxeterMatrix.E₈.simple i) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs))
    (hnt : ∀ g ∈ ggAutomizer X Bs, ¬ GGIsTransvection p g)
    (eJ : (CoxeterMatrix.A 8).Group ≃* ↥(ggAutomizer J Bs))
    (heJ : ∀ i, GGIsReflection p
      ((eJ ((CoxeterMatrix.A 8).simple i) : ↥(ggAutomizer J Bs)) : MulAut ↥Bs))
    (hJX : ggAutomizer J Bs ≤ ggAutomizer X Bs) :
    ∃ c : Fin 8 → (Fin Tag.E8.rank → ℤ), (∀ i, IsRoot .E8 (c i)) ∧
      (∀ i j, iform (τ := .E8) (c i) (c j) = CartanMatrix.A 8 i j) ∧
      ∀ i, ∃ s : WeylGroup .E8,
        (∀ v : Fin Tag.E8.rank → ℤ, s • v = v - iform (τ := .E8) v (c i) • c i) ∧
        ((eJ ((CoxeterMatrix.A 8).simple i) : ↥(ggAutomizer J Bs)) : MulAut ↥Bs) =
          ((f (ggE8Equiv.symm s) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) := by
  classical
  have hp : p.Prime := Fact.out
  let r : Fin 8 → MulAut ↥Bs := fun i =>
    ((eJ ((CoxeterMatrix.A 8).simple i) : ↥(ggAutomizer J Bs)) : MulAut ↥Bs)
  have hrA : ∀ i, r i ∈ ggAutomizer X Bs := fun i =>
    hJX (eJ ((CoxeterMatrix.A 8).simple i)).2
  have hpres : GGCoxeterPres p (ggAutomizer X Bs) CoxeterMatrix.E₈ f :=
    ⟨l6m7_isWeylMatrix_E8, hrefl⟩
  have hmem : ∀ i, r i ∈ ggCoxRefl CoxeterMatrix.E₈ f := fun i =>
    ggCoxRefl_of_isReflection hp hp2 hBs hpres l6m7_le_three_E8 hnt (hrA i) (heJ i)
  choose w k hwk using hmem
  let kk : Fin 8 → Fin Tag.E8.rank := fun i => (k i : Fin Tag.E8.rank)
  let β : Fin 8 → (Fin Tag.E8.rank → ℤ) := fun i =>
    weylAction (isFiniteType_cartan .E8) (ggE8Equiv (w i)) (Pi.single (kk i) (1 : ℤ))
  let s : Fin 8 → WeylGroup .E8 := fun i =>
    ggE8Equiv (w i) * simple .E8 (kk i) * (ggE8Equiv (w i))⁻¹
  have hgg : ∀ i, ggE8Equiv (w i * CoxeterMatrix.E₈.simple (k i) * (w i)⁻¹) = s i := by
    intro i
    rw [map_mul ggE8Equiv (w i * CoxeterMatrix.E₈.simple (k i)) (w i)⁻¹,
      map_mul ggE8Equiv (w i) (CoxeterMatrix.E₈.simple (k i)),
      l6m7_ggE8Equiv_inv, ggE8Equiv_simple (k i)]
  have hrs : ∀ i, r i = ((f (ggE8Equiv.symm (s i)) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) := by
    intro i
    rw [hwk i]
    congr 1
    rw [← hgg i, MulEquiv.symm_apply_apply]
  have hR : ∀ i, weylAction (isFiniteType_cartan .E8) (s i) = l6m7_R (β i) := by
    intro i
    show weylAction (isFiniteType_cartan .E8)
      (ggE8Equiv (w i) * simple .E8 (kk i) * (ggE8Equiv (w i))⁻¹) = l6m7_R (β i)
    rw [l6m7_weylAction_conj_eq_R (ggE8Equiv (w i)) (kk i)]
  have hsβ : ∀ i (v : Fin Tag.E8.rank → ℤ),
      s i • v = v - iform (τ := .E8) v (β i) • β i := by
    intro i v
    rw [smul_def, hR i, l6m7_R_apply, l6m7_form_apply]
  have hβnorm : ∀ i, iform (τ := .E8) (β i) (β i) = 2 := by
    intro i
    have h1 : iform (τ := .E8) (β i) (β i) =
        iform (τ := .E8) (Pi.single (kk i) 1) (Pi.single (kk i) 1) := by
      rw [show β i = ggE8Equiv (w i) • (Pi.single (kk i) 1) by rw [smul_def]]
      exact l6m7_iform_smul (ggE8Equiv (w i)) _ _
    rw [h1, iform_single_single, l6m7_symmetrizer_E8 (kk i), mul_one]
  have hβroot : ∀ i, IsRoot .E8 (β i) := by
    intro i
    rw [show β i = ggE8Equiv (w i) • (Pi.single (kk i) 1) by rw [smul_def]]
    exact IsRoot.smul (IsRoot.basis (kk i)) (ggE8Equiv (w i))
  have hssq : ∀ i, s i * s i = 1 := by
    intro i
    apply weylAction_injective (hA := isFiniteType_cartan .E8)
    rw [show weylAction (isFiniteType_cartan .E8) (s i * s i) =
          weylAction (isFiniteType_cartan .E8) (s i) *
            weylAction (isFiniteType_cartan .E8) (s i) from map_mul _ _ _,
      map_one, hR i, l6m7_R_sq (β i) (hβnorm i)]
  have horder : ∀ i j, i ≠ j → orderOf (s i * s j) = (CoxeterMatrix.A 8).M i j := by
    intro i j hij
    have h1 : orderOf (r i * r j) = orderOf (s i * s j) := by
      rw [hrs i, hrs j, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
        Subgroup.orderOf_coe, MulEquiv.orderOf_eq, MulEquiv.orderOf_eq]
    have h2 : orderOf (r i * r j) = (CoxeterMatrix.A 8).M i j := by
      have hrr : r i * r j =
          ((eJ ((CoxeterMatrix.A 8).simple i * (CoxeterMatrix.A 8).simple j) :
            ↥(ggAutomizer J Bs)) : MulAut ↥Bs) := by
        simp [r]
      rw [hrr, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      change orderOf ((CoxeterMatrix.A 8).toCoxeterSystem.simple i *
        (CoxeterMatrix.A 8).toCoxeterSystem.simple j) = (CoxeterMatrix.A 8).M i j
      rw [(CoxeterMatrix.A 8).toCoxeterSystem.orderOf_simple_mul_simple]
    exact h1.symm.trans h2
  have hcomm : ∀ i j, iform (τ := .E8) (β i) (β j) = 0 → s i * s j = s j * s i := by
    intro i j h
    apply weylAction_injective (hA := isFiniteType_cartan .E8)
    rw [show weylAction (isFiniteType_cartan .E8) (s i * s j) =
          weylAction (isFiniteType_cartan .E8) (s i) *
            weylAction (isFiniteType_cartan .E8) (s j) from map_mul _ _ _,
      show weylAction (isFiniteType_cartan .E8) (s j * s i) =
          weylAction (isFiniteType_cartan .E8) (s j) *
            weylAction (isFiniteType_cartan .E8) (s i) from map_mul _ _ _,
      hR i, hR j, l6m7_R_comm_of_form_zero (β i) (β j) (hβnorm i) (hβnorm j) h]
  have hsq : ∀ i j, iform (τ := .E8) (β i) (β j) = 0 → (s i * s j) ^ 2 = 1 := by
    intro i j h
    calc (s i * s j) ^ 2 = (s i * s j) * (s i * s j) := by rw [pow_two]
      _ = s i * (s j * s i) * s j := by group
      _ = s i * (s i * s j) * s j := by rw [hcomm i j h]
      _ = (s i * s i) * (s j * s j) := by group
      _ = 1 := by rw [hssq i, hssq j, mul_one]
  have hbound : ∀ i j, i ≠ j → iform (τ := .E8) (β i) (β j) ^ 2 ≤ 4 := by
    intro i j hij
    by_cases h : β i = β j
    · rw [h, hβnorm j]; norm_num
    · by_cases h' : β i = -β j
      · rw [h', show (-β j) = (-1 : ℤ) • β j by simp, iform_smul_left, hβnorm j]; norm_num
      · have hlt := iform_sq_lt (hβroot i) (hβroot j) h h'
        rw [hβnorm i, hβnorm j] at hlt
        nlinarith
  have heq_of_two : ∀ i j, iform (τ := .E8) (β i) (β j) = 2 → β i = β j := by
    intro i j h
    have hpos : iform (τ := .E8) (β i - β j) (β i - β j) = 0 := by
      rw [iform_sub_left, iform_sub_right, iform_sub_right, hβnorm i, hβnorm j,
        iform_comm (β j) (β i), h]
      ring
    have hzero : β i - β j = 0 := by
      by_contra hne
      have hlt := iform_self_pos hne
      rw [hpos] at hlt
      exact lt_irrefl _ hlt
    exact sub_eq_zero.mp hzero
  have heq_of_neg_two : ∀ i j, iform (τ := .E8) (β i) (β j) = -2 → β i = -β j := by
    intro i j h
    have hpos : iform (τ := .E8) (β i + β j) (β i + β j) = 0 := by
      rw [iform_add_left, iform_add_right, iform_add_right, hβnorm i, hβnorm j,
        iform_comm (β j) (β i), h]
      ring
    have hzero : β i + β j = 0 := by
      by_contra hne
      have hlt := iform_self_pos hne
      rw [hpos] at hlt
      exact lt_irrefl _ hlt
    exact eq_neg_of_add_eq_zero_left hzero
  have hsi_of_eq : ∀ i j, β i = β j → s i = s j := by
    intro i j h
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Fin Tag.E8.rank → ℤ)
    intro v
    rw [hsβ i v, hsβ j v, h]
  have hsi_of_neg : ∀ i j, β i = -β j → s i = s j := by
    intro i j h
    apply weylAction_injective (hA := isFiniteType_cartan .E8)
    rw [hR i, hR j, h]
    exact l6m7_R_neg (β j)
  have hpair3 : ∀ i j, i ≠ j → (CoxeterMatrix.A 8).M i j = 3 →
      iform (τ := .E8) (β i) (β j) = 1 ∨ iform (τ := .E8) (β i) (β j) = -1 := by
    intro i j hij hm
    have hord := horder i j hij
    rw [hm] at hord
    have hne0 : iform (τ := .E8) (β i) (β j) ≠ 0 := by
      intro h0
      have h2 : (s i * s j) ^ 2 = 1 := hsq i j h0
      have hdvd : orderOf (s i * s j) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
      rw [hord] at hdvd
      norm_num at hdvd
    have hne2 : iform (τ := .E8) (β i) (β j) ≠ 2 := by
      intro h2
      have hsi : s i = s j := hsi_of_eq i j (heq_of_two i j h2)
      have h1 : orderOf (s i * s j) = 1 := by rw [hsi, hssq j, orderOf_one]
      omega
    have hne2' : iform (τ := .E8) (β i) (β j) ≠ -2 := by
      intro h2
      have hsi : s i = s j := hsi_of_neg i j (heq_of_neg_two i j h2)
      have h1 : orderOf (s i * s j) = 1 := by rw [hsi, hssq j, orderOf_one]
      omega
    set c := iform (τ := .E8) (β i) (β j) with hc
    have hb : c * c ≤ 4 := by rw [hc]; simpa [pow_two] using hbound i j hij
    have hlo : -2 ≤ c := by nlinarith [hb, sq_nonneg (c + 2)]
    have hhi : c ≤ 2 := by nlinarith [hb, sq_nonneg (c - 2)]
    have hc0 : c ≠ 0 := by rw [hc]; exact hne0
    have hc2 : c ≠ 2 := by rw [hc]; exact hne2
    have hc2' : c ≠ -2 := by rw [hc]; exact hne2'
    interval_cases c <;> omega
  have hpair2 : ∀ i j, i ≠ j → (CoxeterMatrix.A 8).M i j = 2 →
      iform (τ := .E8) (β i) (β j) = 0 := by
    intro i j hij hm
    have hord := horder i j hij
    rw [hm] at hord
    have hthree : ∀ {c : ℤ}, iform (τ := .E8) (β i) (β j) = c → c * c = 1 →
        (s i * s j) ^ 3 = 1 := by
      intro c hc hc2
      apply weylAction_injective (hA := isFiniteType_cartan .E8)
      rw [map_pow, show weylAction (isFiniteType_cartan .E8) (s i * s j) =
            weylAction (isFiniteType_cartan .E8) (s i) *
              weylAction (isFiniteType_cartan .E8) (s j) from map_mul _ _ _,
        map_one, hR i, hR j]
      exact l6m7_R_pow_three_of_sq_one (β i) (β j) (hβnorm i) (hβnorm j) hc hc2
    have hcontra : ∀ {c : ℤ}, iform (τ := .E8) (β i) (β j) = c → c * c = 1 → False := by
      intro c hc hc2
      have h3 : (s i * s j) ^ 3 = 1 := hthree hc hc2
      have h2 : (s i * s j) ^ 2 = 1 := by
        have := pow_orderOf_eq_one (s i * s j)
        rwa [hord] at this
      have hone : s i * s j = 1 := by
        have hx : s i * s j = (s i * s j) ^ 3 * ((s i * s j) ^ 2)⁻¹ := by group
        rw [hx, h3, h2, inv_one, mul_one]
      rw [hone, orderOf_one] at hord
      omega
    have hne1 : iform (τ := .E8) (β i) (β j) ≠ 1 := fun h1 => hcontra h1 (by norm_num)
    have hne1' : iform (τ := .E8) (β i) (β j) ≠ -1 := fun h1 => hcontra h1 (by norm_num)
    have hne2 : iform (τ := .E8) (β i) (β j) ≠ 2 := by
      intro h2
      have hsi : s i = s j := hsi_of_eq i j (heq_of_two i j h2)
      have h1 : orderOf (s i * s j) = 1 := by rw [hsi, hssq j, orderOf_one]
      omega
    have hne2' : iform (τ := .E8) (β i) (β j) ≠ -2 := by
      intro h2
      have hsi : s i = s j := hsi_of_neg i j (heq_of_neg_two i j h2)
      have h1 : orderOf (s i * s j) = 1 := by rw [hsi, hssq j, orderOf_one]
      omega
    set c := iform (τ := .E8) (β i) (β j) with hc
    have hb : c * c ≤ 4 := by rw [hc]; simpa [pow_two] using hbound i j hij
    have hlo : -2 ≤ c := by nlinarith [hb, sq_nonneg (c + 2)]
    have hhi : c ≤ 2 := by nlinarith [hb, sq_nonneg (c - 2)]
    have hc1 : c ≠ 1 := by rw [hc]; exact hne1
    have hc1' : c ≠ -1 := by rw [hc]; exact hne1'
    have hc2 : c ≠ 2 := by rw [hc]; exact hne2
    have hc2' : c ≠ -2 := by rw [hc]; exact hne2'
    interval_cases c <;> omega
  have hedge : ∀ k : Fin 7, iform (τ := .E8) (β (Fin.castSucc k)) (β (Fin.succ k)) *
      iform (τ := .E8) (β (Fin.castSucc k)) (β (Fin.succ k)) = 1 := by
    intro k
    have hadj : (CoxeterMatrix.A 8).M (Fin.castSucc k) (Fin.succ k) = 3 := by
      fin_cases k <;> simp [CoxeterMatrix.A, Matrix.of_apply, Fin.castSucc, Fin.succ]
    have hne : (Fin.castSucc k : Fin 8) ≠ Fin.succ k := by
      intro h
      have := congrArg Fin.val h
      simp [Fin.castSucc, Fin.succ] at this
    rcases hpair3 (Fin.castSucc k) (Fin.succ k) hne hadj with h | h <;> rw [h] <;> norm_num
  let ε : Fin 8 → ℤ := l6m7_eps β
  have hεsq : ∀ i, ε i * ε i = 1 := fun i => l6m7_epsNat_sq β hedge i.val
  have hεedge : ∀ i : Fin 7, ε (Fin.castSucc i) * ε (Fin.succ i) *
      iform (τ := .E8) (β (Fin.castSucc i)) (β (Fin.succ i)) = -1 :=
    fun i => l6m7_eps_edge β hedge i
  have hroot : ∀ i, IsRoot .E8 (ε i • β i) := by
    intro i
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp (hεsq i) with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h, one_smul]; exact hβroot i
    · rw [h, neg_one_smul]; exact IsRoot.neg (hβroot i)
  have hgram : ∀ i j, iform (τ := .E8) (ε i • β i) (ε j • β j) = CartanMatrix.A 8 i j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [iform_smul_left, iform_smul_right, ← mul_assoc, hεsq i, one_mul, hβnorm i]
      exact (l6m7_cartanA_self i).symm
    · rcases l6m7_M_two_or_three i j hij with hm | hm
      · rw [iform_smul_left, iform_smul_right, hpair2 i j hij hm,
          l6m7_cartanA_eq_zero_of_M_two i j hij hm]
        ring
      · rw [l6m7_cartanA_eq_neg_one_of_M_three i j hij hm]
        rcases (l6m7_M_three_iff_adj i j hij).mp hm with hadj | hadj
        · have hi7 : i.val < 7 := by omega
          let kk : Fin 7 := ⟨i.val, hi7⟩
          have hik : (Fin.castSucc kk : Fin 8) = i := Fin.ext rfl
          have hjk : (Fin.succ kk : Fin 8) = j := Fin.ext (by simp [Fin.succ]; omega)
          have hedge' := hεedge kk
          rw [hik, hjk] at hedge'
          rw [iform_smul_left, iform_smul_right]
          rw [show ε i * (ε j * iform (τ := .E8) (β i) (β j)) =
              ε i * ε j * iform (τ := .E8) (β i) (β j) by ring]
          exact hedge'
        · have hj7 : j.val < 7 := by omega
          let kk : Fin 7 := ⟨j.val, hj7⟩
          have hjk : (Fin.castSucc kk : Fin 8) = j := Fin.ext rfl
          have hik : (Fin.succ kk : Fin 8) = i := Fin.ext (by simp [Fin.succ]; omega)
          have hedge' := hεedge kk
          rw [hjk, hik] at hedge'
          rw [iform_smul_left, iform_smul_right, ← iform_comm (β j) (β i)]
          rw [show ε i * (ε j * iform (τ := .E8) (β j) (β i)) =
              ε j * ε i * iform (τ := .E8) (β j) (β i) by ring]
          exact hedge'
  have hsε : ∀ i (v : Fin Tag.E8.rank → ℤ),
      s i • v = v - iform (τ := .E8) v (ε i • β i) • (ε i • β i) := by
    intro i v
    rw [smul_def, hR i]
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp (hεsq i) with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h, one_smul, l6m7_R_apply, l6m7_form_apply]
    · rw [h, neg_one_smul, ← l6m7_R_neg (β i), l6m7_R_apply, l6m7_form_apply]
  refine ⟨fun i => ε i • β i, hroot, hgram, ?_⟩
  intro i
  refine ⟨s i, hsε i, ?_⟩
  exact hrs i

end CFSG.StandardType

end
