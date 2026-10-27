module

public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtStabIrred
public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtStabRoots

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime]

private lemma zt3_sum_sq_eq_one {y : Fin 3 → ZMod 3} (h : ∑ i, y i ^ 2 = 1) :
    ∃ (j : Fin 3) (c : ZMod 3), c ≠ 0 ∧ ∀ i, y i = if i = j then c else 0 := by
  have := show ∀ y : Fin 3 → ZMod 3, (∑ i, y i ^ 2 = 1) →
      ∃ (j : Fin 3) (c : ZMod 3), c ≠ 0 ∧ ∀ i, y i = if i = j then c else 0 from by
    decide
  exact this y h

private lemma zt3_quad_sum_three {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {b : Fin 3 → V} {lam : ZMod 3}
    (hnorm : ∀ i, Q (b i) = lam)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (b i) (b j) = 0)
    (y : Fin 3 → ZMod 3) :
    Q (∑ i, y i • b i) = lam * ∑ i, (y i) ^ 2 := by
  rw [Fin.sum_univ_three]
  have h01 : QuadraticMap.polar Q (y 0 • b 0) (y 1 • b 1) = 0 := by
    rw [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
      horth 0 1 (by decide)]
    simp
  have h02 : QuadraticMap.polar Q (y 0 • b 0) (y 2 • b 2) = 0 := by
    rw [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
      horth 0 2 (by decide)]
    simp
  have h12 : QuadraticMap.polar Q (y 1 • b 1) (y 2 • b 2) = 0 := by
    rw [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
      horth 1 2 (by decide)]
    simp
  have h012 : QuadraticMap.polar Q (y 0 • b 0 + y 1 • b 1) (y 2 • b 2) = 0 := by
    rw [QuadraticMap.polar_add_left, h02, h12, add_zero]
  calc
    Q (y 0 • b 0 + y 1 • b 1 + y 2 • b 2)
        = Q (y 0 • b 0 + y 1 • b 1) + Q (y 2 • b 2) +
            QuadraticMap.polar Q (y 0 • b 0 + y 1 • b 1) (y 2 • b 2) := by
          rw [QuadraticMap.map_add Q]
    _ = Q (y 0 • b 0) + Q (y 1 • b 1) + Q (y 2 • b 2) := by
          rw [QuadraticMap.map_add Q, h01, h012]
          abel
    _ = (y 0 * y 0) • Q (b 0) + (y 1 * y 1) • Q (b 1) + (y 2 * y 2) • Q (b 2) := by
          rw [QuadraticMap.map_smul Q, QuadraticMap.map_smul Q, QuadraticMap.map_smul Q]
    _ = lam * (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) := by
          rw [hnorm 0, hnorm 1, hnorm 2]
          simp only [smul_eq_mul, pow_two]
          ring
    _ = lam * ∑ i, y i ^ 2 := by
          rw [Fin.sum_univ_three]

private abbrev zt3_w {V : Type} [AddCommGroup V] (v : Fin 3 → V) : Fin 3 → V :=
  ![v 0 + v 1, v 0 - v 1, v 2]

private lemma zt3_w_norm {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {v : Fin 3 → V}
    (h0 : Q (v 0) = 1) (h1 : Q (v 1) = 1) (h2 : Q (v 2) = 2)
    (h01 : QuadraticMap.polar Q (v 0) (v 1) = 0) :
    Q (zt3_w v 0) = 2 ∧ Q (zt3_w v 1) = 2 ∧ Q (zt3_w v 2) = 2 := by
  refine ⟨?_, ?_, h2⟩
  · show Q (v 0 + v 1) = 2
    rw [QuadraticMap.map_add Q, h0, h1, h01]
    decide
  · show Q (v 0 - v 1) = 2
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg Q, h0, h1,
      QuadraticMap.polar_neg_right, h01, neg_zero]
    decide

private lemma zt3_w_orth {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {v : Fin 3 → V}
    (h0 : Q (v 0) = 1) (h1 : Q (v 1) = 1) (h2 : Q (v 2) = 2)
    (h01 : QuadraticMap.polar Q (v 0) (v 1) = 0)
    (h02 : QuadraticMap.polar Q (v 0) (v 2) = 0)
    (h12 : QuadraticMap.polar Q (v 1) (v 2) = 0) :
    (∀ i j : Fin 3, i ≠ j → QuadraticMap.polar Q (zt3_w v i) (zt3_w v j) = 0) ∧
      ∀ i : Fin 3, (QuadraticMap.polarBilin Q) (zt3_w v i) (zt3_w v i) ≠ 0 := by
  obtain ⟨hw0, hw1, hw2⟩ := zt3_w_norm h0 h1 h2 h01
  have h01' : QuadraticMap.polar Q (zt3_w v 0) (zt3_w v 1) = 0 := by
    show QuadraticMap.polar Q (v 0 + v 1) (v 0 - v 1) = 0
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_sub_right,
      QuadraticMap.polar_sub_right, QuadraticMap.polar_self, QuadraticMap.polar_self,
      h0, h1, h01, QuadraticMap.polar_comm Q (v 1) (v 0), h01]
    decide
  have h02' : QuadraticMap.polar Q (zt3_w v 0) (zt3_w v 2) = 0 := by
    show QuadraticMap.polar Q (v 0 + v 1) (v 2) = 0
    rw [QuadraticMap.polar_add_left, h02, h12]
    simp
  have h12' : QuadraticMap.polar Q (zt3_w v 1) (zt3_w v 2) = 0 := by
    show QuadraticMap.polar Q (v 0 - v 1) (v 2) = 0
    rw [QuadraticMap.polar_sub_left, h02, h12]
    simp
  have horth : ∀ i j : Fin 3, i ≠ j → QuadraticMap.polar Q (zt3_w v i) (zt3_w v j) = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | exact h01'
        | exact h02'
        | exact h12'
        | rwa [QuadraticMap.polar_comm]
  refine ⟨horth, ?_⟩
  intro i
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self]
  have h : Q (zt3_w v i) = 2 := by
    fin_cases i <;> assumption
  rw [h]
  decide

private lemma zt3_w_linearIndependent {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {v : Fin 3 → V}
    (horth : ∀ i j : Fin 3, i ≠ j →
      QuadraticMap.polar Q (zt3_w v i) (zt3_w v j) = 0)
    (hself : ∀ i : Fin 3,
      (QuadraticMap.polarBilin Q) (zt3_w v i) (zt3_w v i) ≠ 0) :
    LinearIndependent (ZMod 3) (zt3_w v) :=
  LinearMap.BilinForm.linearIndependent_of_iIsOrtho (B := QuadraticMap.polarBilin Q)
    (fun i j hij => by
      change (QuadraticMap.polarBilin Q) (zt3_w v i) (zt3_w v j) = 0
      rw [QuadraticMap.polarBilin_apply_apply]
      exact horth i j hij) hself

private lemma zt3_exists_const_norm_basis {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Module.Finite (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 3) :
    ∃ (b : Module.Basis (Fin 3) (ZMod 3) V) (lam : ZMod 3), lam ≠ 0 ∧
      (∀ i, Q (b i) = lam) ∧
      ∀ i j, i ≠ j → QuadraticMap.polar Q (b i) (b j) = 0 := by
  have hodd : Odd (Nat.card (ZMod 3)) := by
    rw [Nat.card_zmod]
    decide
  obtain ⟨v, hvorth, hvnorm, hvlast⟩ :=
    CFSG.RankThree.Classical.exists_orthogonal_basis_quad_eq (K := ZMod 3) (V := V)
      (d := 3) hodd hdim (by norm_num) Q hQ (a := 1) one_ne_zero
  have h2 : Q (v 2) ≠ 0 := by simpa using hvlast
  have hδ : Q (v 2) = 1 ∨ Q (v 2) = 2 := by
    have := show ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = 2 from by decide
    exact this _ h2
  have h0 : Q (v 0) = 1 := hvnorm 0 (by norm_num)
  have h1 : Q (v 1) = 1 := hvnorm 1 (by norm_num)
  have h01 : QuadraticMap.polar Q (v 0) (v 1) = 0 := hvorth 0 1 (by decide)
  have h02 : QuadraticMap.polar Q (v 0) (v 2) = 0 := hvorth 0 2 (by decide)
  have h12 : QuadraticMap.polar Q (v 1) (v 2) = 0 := hvorth 1 2 (by decide)
  rcases hδ with hδ | hδ
  · refine ⟨v, 1, one_ne_zero, ?_, hvorth⟩
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact hδ
  · obtain ⟨hw0, hw1, hw2⟩ := zt3_w_norm h0 h1 hδ h01
    obtain ⟨horth, hself⟩ := zt3_w_orth h0 h1 hδ h01 h02 h12
    have hli := zt3_w_linearIndependent horth hself
    let b : Module.Basis (Fin 3) (ZMod 3) V :=
      basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
    have hb : ∀ i, b i = zt3_w v i := fun i => by
      rw [coe_basisOfLinearIndependentOfCardEqFinrank]
    refine ⟨b, 2, by decide, ?_, ?_⟩
    · intro i
      rw [hb i]
      fin_cases i <;> assumption
    · intro i j hij
      rw [hb i, hb j]
      exact horth i j hij

private lemma zt3_exists_line_of_norm_eq {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {b : Module.Basis (Fin 3) (ZMod 3) V} {lam : ZMod 3}
    (hlam : lam ≠ 0) (hnorm : ∀ i, Q (b i) = lam)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (b i) (b j) = 0)
    {w : V} (hw : Q w = lam) :
    ∃ j : Fin 3, w = b j ∨ w = -b j := by
  let y := b.equivFun w
  have hsum : Q w = lam * ∑ i, (y i) ^ 2 := by
    conv_lhs => rw [← b.sum_equivFun w]
    exact zt3_quad_sum_three hnorm horth y
  have h1 : ∑ i, (y i) ^ 2 = 1 := by
    rw [hsum] at hw
    exact mul_left_cancel₀ hlam (by simpa using hw)
  obtain ⟨j, c, hc, hy⟩ := zt3_sum_sq_eq_one h1
  have hcw : w = c • b j := by
    rw [← b.sum_equivFun w]
    change (∑ i, y i • b i) = c • b j
    rw [Finset.sum_eq_single j]
    · rw [hy j, if_pos rfl]
    · intro i _ hij
      rw [hy i, if_neg hij, zero_smul]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rcases (show ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = 2 from by decide) c hc with rfl | rfl
  · exact ⟨j, Or.inl (by simpa using hcw)⟩
  · refine ⟨j, Or.inr ?_⟩
    rw [hcw, show (2 : ZMod 3) = -1 by decide, neg_one_smul]

theorem tfOrthThreeThree :
    p = 3 → ∀ (U : Type) [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
      (X : Subgroup (U ≃ₗ[ZMod p] U)), SplitSupport X 3 → IsOrthType p (movedGroup X) →
      Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X) := by
  rintro rfl U _ _ _ X hs horth
  classical
  set V := HardMathSupport.Kantor79.commutatorSpace X with hV
  set A := movedGroup X with hA
  obtain ⟨Q, hQ, hAQ⟩ := horth
  have hdim : Module.finrank (ZMod 3) V = 3 := hs.2.1
  obtain ⟨b, lam, hlam, hbnorm, hborth⟩ :=
    zt3_exists_const_norm_basis (V := V) Q hQ hdim
  have hiso : ∀ g ∈ A, IsIsom 3 Q g := by
    rcases hAQ with hO | ⟨c, hc, hAeq⟩
    · intro g hg
      exact (hO g).mp hg
    · intro g hg
      exact isIsom_of_mem_closure_classRefl (by simpa [hAeq] using hg)
  refine ⟨3, fun i => Submodule.span (ZMod 3) {b i}, by norm_num, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [Ne, Submodule.span_singleton_eq_bot]
    exact b.linearIndependent.ne_zero i
  · exact b.linearIndependent.iSupIndep_span_singleton
  · rw [← Submodule.span_range_eq_iSup, b.span_eq]
  · intro g hg i
    have hgi : IsIsom 3 Q g := hiso g hg
    have hnorm : Q (g (b i)) = lam := by
      rw [hgi (b i), hbnorm i]
    obtain ⟨j, hj⟩ := zt3_exists_line_of_norm_eq hlam hbnorm hborth hnorm
    refine ⟨j, ?_⟩
    rw [Submodule.map_span, Set.image_singleton]
    change Submodule.span (ZMod 3) {g (b i)} = Submodule.span (ZMod 3) {b j}
    rcases hj with h | h
    · rw [h]
    · rw [h]
      simpa using Submodule.span_singleton_smul_eq
        (isUnit_neg_one : IsUnit (-1 : ZMod 3)) (b j)

variable {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem tfOrthStabilizer_full_of_class [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (ho : IsOrthOn p Q X) (hp3 : p = 3)
    (hd : ∃ x ∈ X, ∃ y ∈ X, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) :
    X = Subgroup.closure {t | IsRefl p t ∧ IsIsom p Q t ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X} := by
  rcases ho with hfull | ⟨c, hc, hclass⟩
  · exact hfull
  · exfalso
    obtain ⟨x, hxX, y, hyX, hxr, hyr, hxy⟩ := hd
    have hxcl : x ∈ Subgroup.closure (ClassRefl p Q c) := by
      rw [hclass] at hxX
      exact Subgroup.closure_mono (fun t ht => ht.1) hxX
    have hycl : y ∈ Subgroup.closure (ClassRefl p Q c) := by
      rw [hclass] at hyX
      exact Subgroup.closure_mono (fun t ht => ht.1) hyX
    have hle := orderOf_mul_le_three_of_classRefl_three hp3 hQ hc hxcl hycl hxr hyr
    omega

private theorem tfOrthStabilizer_finrank (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {X : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ} (hs : SplitSupport X m)
    (hm : 3 ≤ m) (hm3 : p = 3 → 4 ≤ m) (ho : IsOrthOn p Q X) (hh : h ∈ X)
    (hh' : IsRefl p h) :
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (reflSubgroupIn p X (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)))) + 1 = m := by
  obtain ⟨a, hQa, ha⟩ := DimThree.exists_root_of_isRefl_isIsom hp hQ hh' (ho.isIsom hh)
  have haV : a ∈ HardMathSupport.Kantor79.commutatorSpace X :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hh
      (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg
        (ZMod.prime_ne_zero p 2 hp) ha)
  have haK : a ∉ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := by
    intro hmem
    have hfix : (h : U →ₗ[ZMod p] U) a = a := by
      simpa [LinearMap.mem_ker, sub_eq_zero] using hmem
    have ha0 : a = 0 := eq_zero_of_eq_neg (ZMod.prime_ne_zero p 2 hp) (hfix.symm.trans ha)
    exact hQa (by rw [ha0]; exact map_zero Q)
  have hdim := IsRefl.finrank_inf_ker_sub_one_add_one hp hh'
    (A := HardMathSupport.Kantor79.commutatorSpace X) haV haK
  rw [hs.2.1] at hdim
  rw [show reflSubgroupIn p X (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) =
    reflStab p X h from rfl]
  rw [commutatorSpace_reflStab hp hQ hs hm hm3 ho hh hh']
  exact hdim

theorem tfOrthStabilizer (hp : p ≠ 2) {m : ℕ} :
    3 ≤ m → ∀ (U : Type) [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U],
      Module.finrank (ZMod p) U = m + 1 → ∀ X : Subgroup (U ≃ₗ[ZMod p] U), ReflGen p X →
      SplitSupport X m → IsOrthType p (movedGroup X) →
      ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X) →
      (∃ x ∈ X, ∃ y ∈ X, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) →
      ∀ h ∈ X, IsRefl p h →
        (Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
            (reflSubgroupIn p X (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)))) + 1 = m ∧
          IrredOnSection (reflSubgroupIn p X (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))) ⊥
            (HardMathSupport.Kantor79.commutatorSpace
              (reflSubgroupIn p X (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)))) ∧
          (p = 3 → ∃ x ∈ reflSubgroupIn p X (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)),
            ∃ y ∈ reflSubgroupIn p X (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)),
              IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))) ∨
        (m = 3 ∧ p = 5 ∧ ∃ (r : Fin 3 → U ≃ₗ[ZMod p] U) (e : Fin 3 → U) (s : U ≃ₗ[ZMod p] U),
          r 0 = h ∧ IsCyclicRootTriple p X r e s) := by
  rintro hm U _ _ _ hn X _ hs horth hprim hd h hh hh'
  have hm3 : p = 3 → 4 ≤ m := by
    intro hp3
    by_contra hlt
    have hm3' : m = 3 := by omega
    exact hprim (tfOrthThreeThree (p := p) hp3 U X (hm3' ▸ hs) horth)
  obtain ⟨e, he, he0⟩ := hs.exists_mem_centralizerSpace_ne_zero (l := m) (by omega)
  have hs' : SplitSupport X (Module.finrank (ZMod p) U - 1) := by
    rw [hn, Nat.add_sub_cancel]
    exact hs
  obtain ⟨Q, hQ, ho, _⟩ :=
    exists_isOrthOn_of_isOrthType_movedGroup hp hs' horth he he0 one_ne_zero
  have hfull : p = 3 → X = Subgroup.closure {t | IsRefl p t ∧ IsIsom p Q t ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace X} :=
    fun hp3 => tfOrthStabilizer_full_of_class hQ ho hp3 hd
  rcases irredOnSection_reflStab_or hp hQ hs hm hm3 ho hfull hh hh' with hirr | hexc
  · refine Or.inl ⟨?_, ?_, ?_⟩
    · exact tfOrthStabilizer_finrank hp hQ hs hm hm3 ho hh hh'
    · exact hirr
    · intro hp3
      exact exists_three_lt_orderOf_reflStab hp3 hQ hs (hm3 hp3) (hfull hp3) hh hh'
  · obtain ⟨hm3', hp5, ⟨c, hc, hXc⟩, x, hx, y, hy, hxr, hyr, hxy, hne⟩ := hexc
    exact Or.inr ⟨hm3', hp5, exists_isCyclicRootTriple_of_commute hp5 hQ (hm3' ▸ hs) hc hXc
      hh hh' hx hy hxr hyr hxy hne⟩

end CFSG.StandardType.ZS

end
