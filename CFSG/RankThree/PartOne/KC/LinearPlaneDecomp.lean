module

public import CFSG.RankThree.PartOne.KC.UnitaryPlaneDecomposition
public import CFSG.RankThree.PartOne.KC.LinearPlaneBlocks
public import CFSG.RankThree.PartOne.KC.LinearCommutantFactors

public section

namespace CFSG.RankThree.PartOne.KCLinPlane

open Polynomial Module Matrix CFSG CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCLinComm CFSG.RankThree.PartOne.KCUnitaryPlane

variable {n p : ℕ} {K : Type} [Field K] (E0 : Subgroup (SpecialLinearGroup (Fin n) K))

@[expose] noncomputable def planeRep :
    ↥E0 →* LinearMap.GeneralLinearGroup K (Fin n → K) :=
  (Matrix.GeneralLinearGroup.toLin : GL (Fin n) K ≃*
      LinearMap.GeneralLinearGroup K (Fin n → K)).toMonoidHom.comp
    ((SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K).comp E0.subtype)

theorem act_planeRep (x : ↥E0) :
    act (planeRep E0) x =
      Matrix.toLin' ((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl

theorem planeRep_injective : Function.Injective (planeRep E0) := by
  intro x y hxy
  have h1 : act (planeRep E0) x = act (planeRep E0) y := by
    unfold act
    rw [hxy]
  rw [act_planeRep, act_planeRep] at h1
  exact Subtype.ext (Subtype.ext (Matrix.toLin'.injective h1))

theorem isPlane [IsElementaryAbelian p E0] (hp : p.Prime) (hcard : Nat.card E0 = p ^ 2) :
    IsPlane p E0 where
  prime := hp
  card := hcard
  pow x := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E0)
    (x : SpecialLinearGroup (Fin n) K) x.2)

section Commute

variable [IsMulCommutative E0]

theorem commute_act (x y : ↥E0) : Commute (act (planeRep E0) x) (act (planeRep E0) y) := by
  have hxy : x * y = y * x := (IsMulCommutative.is_comm (M := E0)).comm x y
  show act (planeRep E0) x * act (planeRep E0) y = act (planeRep E0) y * act (planeRep E0) x
  rw [← act_mul, ← act_mul, hxy]

variable [Fintype E0]

theorem commute_act_sumOp (y : ↥E0) (L : Subgroup ↥E0) :
    Commute (act (planeRep E0) y) (sumOp (planeRep E0) L) := by
  classical
  unfold sumOp
  exact Commute.sum_right _ _ _ fun x _ => commute_act E0 y x

theorem commute_act_avgOp (y : ↥E0) (L : Subgroup ↥E0) :
    Commute (act (planeRep E0) y) (avgOp (planeRep E0) L) := by
  unfold avgOp
  exact (commute_act_sumOp E0 y L).smul_right _

theorem commute_act_projLine (y : ↥E0) (L : Subgroup ↥E0) :
    Commute (act (planeRep E0) y) (projLine (planeRep E0) L) := by
  unfold projLine
  exact (commute_act_avgOp E0 y L).sub_right (commute_act_avgOp E0 y ⊤)

end Commute

section Idem

open scoped _root_.Classical

variable [Fintype E0]

abbrev PlaneIdx (E0 : Subgroup (SpecialLinearGroup (Fin n) K)) [Fintype E0] (p : ℕ) : Type :=
  Option {L : Subgroup ↥E0 // L ∈ lines p ↥E0}

@[expose] noncomputable def planeIdem (p : ℕ) : PlaneIdx E0 p → Module.End K (Fin n → K)
  | none => projTop (planeRep E0)
  | some L => projLine (planeRep E0) L.1

variable (hP : IsPlane p E0) (hpK : (p : K) ≠ 0)
include hP hpK

theorem planeIdem_idem (o : PlaneIdx E0 p) :
    planeIdem E0 p o * planeIdem E0 p o = planeIdem E0 p o := by
  cases o with
  | none => exact projTop_mul_self (planeRep E0) hP hpK
  | some L => exact projLine_mul_self (planeRep E0) hP hpK (mem_lines.mp L.2)

theorem planeIdem_orth {o o' : PlaneIdx E0 p} (h : o ≠ o') :
    planeIdem E0 p o * planeIdem E0 p o' = 0 := by
  rcases o with _ | L <;> rcases o' with _ | M
  · exact absurd rfl h
  · exact projTop_mul_projLine (planeRep E0) hP hpK (mem_lines.mp M.2)
  · exact projLine_mul_projTop (planeRep E0) hP hpK (mem_lines.mp L.2)
  · exact projLine_mul_projLine_of_ne (planeRep E0) hP hpK (mem_lines.mp L.2)
      (mem_lines.mp M.2) (fun h' => h (by rw [Subtype.ext h']))

theorem planeIdem_sum : ∑ o, planeIdem E0 p o = 1 := by
  rw [Fintype.sum_option]
  have h1 := sum_projLine_add_projTop (planeRep E0) hP hpK
  rw [← Finset.sum_coe_sort] at h1
  simpa [planeIdem, add_comm] using h1

theorem projLine_apply_of_mem_fixedSpace {L M : Subgroup ↥E0} (hL : Nat.card L = p)
    (hM : Nat.card M = p) (hLM : L ≠ M) {w : Fin n → K}
    (hw : w ∈ fixedSpace (planeRep E0) M) : projLine (planeRep E0) L w = 0 := by
  have hw' : avgOp (planeRep E0) M w = w :=
    avgOp_apply_of_mem_fixedSpace (planeRep E0) (natCard_cast_line hpK hM) hw
  unfold projLine
  rw [LinearMap.sub_apply]
  have h1 : avgOp (planeRep E0) L w = avgOp (planeRep E0) ⊤ w := by
    conv_lhs => rw [← hw']
    exact LinearMap.congr_fun (avgOp_mul_avgOp_of_ne (planeRep E0) hP hpK hL hM hLM) w
  rw [h1, sub_self]

theorem exists_active [Finite K] :
    ∃ L ∈ lines p E0, projLine (planeRep E0) L ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hsum := sum_projLine_add_projTop (planeRep E0) hP hpK
  rw [Finset.sum_eq_zero hcon, zero_add] at hsum
  have hnt : Nontrivial ↥E0 := by
    have hfin : Finite ↥E0 := inferInstance
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [hP.card]
    have := hP.prime.two_le
    nlinarith
  obtain ⟨y, hy⟩ := exists_ne (1 : ↥E0)
  apply hy
  apply planeRep_injective E0
  have h1 := act_mul_avgOp (planeRep E0) (Subgroup.mem_top y)
  have h2 : avgOp (planeRep E0) ⊤ = 1 := hsum
  rw [h2, mul_one] at h1
  refine Units.ext ?_
  rw [map_one]
  exact h1

theorem exists_factor [Finite K] {L M : Subgroup ↥E0} (hL : L ∈ lines p E0) (hM : M ∈ lines p E0)
    (hLM : L ≠ M) (hLne : projLine (planeRep E0) L ≠ 0) {c : ↥E0} (hcM : c ∈ M) (hc1 : c ≠ 1) :
    ∃ h ∈ primaryFactors (act (planeRep E0) c), h ≠ X - C 1 ∧
      projLine (planeRep E0) L * primaryProjection (act (planeRep E0) c) h ≠ 0 := by
  set ρ := planeRep E0 with hρ
  set x := act ρ c with hx
  have hxp : x ^ p = 1 := by
    rw [hx, ← act_pow, hP.pow c, act_one]
  have hsq : Squarefree (minpoly K x) := squarefree_minpoly_of_pow_eq_one hpK hxp
  by_contra hcon
  push Not at hcon
  apply hLne
  have h1 : projLine ρ L = ∑ h ∈ primaryFactors x, projLine ρ L * primaryProjection x h := by
    rw [← Finset.mul_sum, sum_primaryProjection hsq, mul_one]
  rw [h1]
  refine Finset.sum_eq_zero fun h hh => ?_
  by_cases hX : h = X - C 1
  · subst hX
    refine LinearMap.ext fun v => ?_
    have hv : primaryProjection x (X - C 1) v ∈ primaryComponent x (X - C 1) :=
      primaryProjection_mem hsq hh v
    have hfixed : act ρ c (primaryProjection x (X - C 1) v) = primaryProjection x (X - C 1) v := by
      have := mem_primaryComponent.mp hv
      simp only [map_sub, aeval_X, map_one, LinearMap.sub_apply,
        Module.End.one_apply] at this
      exact sub_eq_zero.mp this
    have hfs : primaryProjection x (X - C 1) v ∈ fixedSpace ρ M :=
      fixedSpace_of_apply_eq ρ hP (mem_lines.mp hM) hcM hc1 hfixed
    rw [Module.End.mul_apply, projLine_apply_of_mem_fixedSpace E0 hP hpK (mem_lines.mp hL)
      (mem_lines.mp hM) hLM hfs]
    rfl
  · exact hcon h hh hX

omit hpK in
theorem exists_other_line (L : Subgroup ↥E0) :
    ∃ M ∈ lines p E0, M ≠ L ∧ ∃ c ∈ M, c ≠ 1 := by
  obtain ⟨M, hM, hML⟩ : ∃ M ∈ lines p E0, M ≠ L := by
    have h := hP.card_lines
    exact Finset.exists_mem_ne (by rw [h]; have := hP.prime.two_le; omega) L
  refine ⟨M, hM, hML, ?_⟩
  by_contra hcon
  push Not at hcon
  have hbot : M = ⊥ := (Subgroup.eq_bot_iff_forall M).mpr fun y hy => hcon y hy
  have h1 : Nat.card M = p := mem_lines.mp hM
  rw [hbot, Subgroup.card_bot] at h1
  exact hP.prime.one_lt.ne h1

theorem orderOf_le_finrank_range_projLine [Finite K] [IsMulCommutative E0] {L : Subgroup ↥E0}
    (hL : L ∈ lines p E0) (hLne : projLine (planeRep E0) L ≠ 0) :
    orderOf ((Nat.card K : ℕ) : ZMod p) ≤
      finrank K (LinearMap.range (projLine (planeRep E0) L)) := by
  set ρ := planeRep E0 with hρ
  obtain ⟨M, hM, hML, c, hcM, hc1⟩ := exists_other_line E0 hP L
  obtain ⟨h, hh, hne, hne0⟩ := exists_factor E0 hP hpK hL hM (Ne.symm hML) hLne hcM hc1
  set x := act ρ c with hx
  have hxp : x ^ p = 1 := by
    rw [hx, ← act_pow, hP.pow c, act_one]
  have hsq : Squarefree (minpoly K x) := squarefree_minpoly_of_pow_eq_one hpK hxp
  obtain ⟨v, hv⟩ : ∃ v, (projLine ρ L * primaryProjection x h) v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne0 (LinearMap.ext fun v => hcon v)
  set y := projLine ρ L (primaryProjection x h v) with hy
  have hcomm : Commute (projLine ρ L) x := (commute_act_projLine E0 c L).symm
  have hyU : y ∈ LinearMap.range (projLine ρ L) := LinearMap.mem_range_self _ _
  have hya : y ∈ primaryComponent x h :=
    apply_mem_primaryComponent hcomm (primaryProjection_mem hsq hh v)
  have hU : ∀ u ∈ LinearMap.range (projLine ρ L), x u ∈ LinearMap.range (projLine ρ L) := by
    rintro _ ⟨w, rfl⟩
    refine ⟨x w, ?_⟩
    have := congrArg (fun f : Module.End K (Fin n → K) => f w) hcomm.eq
    simpa using this
  have h1 := natDegree_le_finrank_of_stable hh hU hyU hya hv
  exact (orderOf_le_natDegree_of_mem_primaryFactors hP.prime hxp hh hne).trans h1

end Idem

theorem three_le_orderOf_of_le_three {q : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hq2 : 2 ≤ q)
    (hq3 : q ≤ 3) (hd : 2 ≤ orderOf (q : ZMod p)) : 3 ≤ orderOf (q : ZMod p) := by
  by_contra hlt
  have hd2 : orderOf (q : ZMod p) = 2 := by omega
  have hq : (q : ZMod p) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (q : ZMod p)
    rwa [hd2] at this
  have hdvd : p ∣ q ^ 2 - 1 := by
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    refine (ZMod.natCast_eq_zero_iff _ _).mp ?_
    rw [Nat.cast_sub h1, Nat.cast_pow, hq, Nat.cast_one, sub_self]
  interval_cases q
  · have : p ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · have h8 : p ∣ 2 ^ 3 := by simpa using hdvd
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h8)
    omega

end CFSG.RankThree.PartOne.KCLinPlane
