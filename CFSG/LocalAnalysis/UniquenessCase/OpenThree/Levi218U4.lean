module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218XE3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218U4
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypFrame
import CFSG.CGT.PushingUpLit.CGT6K1.InnerEven
import CFSG.GH74.Generic.BProg.B3.S1IdentSl2
import CFSG.GH74.Uniqueness.SU.SU1Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup Matrix
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.Quasithin.H13.U4Par (Ix ie1 ie2 if1 if2 ix_cases levMat levMat_apply levHom
  coe_levHom slMat hypSU_ext coe_mul_hypSU)

section Model

variable {n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 n K)

private theorem diagonal_commute_levMat {v : Ix → K} (hv : v ie2 = v if2)
    (A : Matrix (Fin 2) (Fin 2) K) : diagonal v * levMat A = levMat A * diagonal v := by
  ext i j
  rw [diagonal_mul, mul_diagonal]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [levMat_apply, hv, mul_comm]

private theorem levHom_injective : Function.Injective (levHom h) := by
  intro A B hAB
  have hm := congrArg (fun g : hypSU h 2 0 => ((g : GL Ix K) : Matrix Ix Ix K)) hAB
  simp only [coe_levHom] at hm
  ext i j
  have hij : slMat h A i j = slMat h B i j := by
    fin_cases i <;> fin_cases j
    · simpa [levMat_apply] using congrFun (congrFun hm ie2) ie2
    · simpa [levMat_apply] using congrFun (congrFun hm ie2) if2
    · simpa [levMat_apply] using congrFun (congrFun hm if2) ie2
    · simpa [levMat_apply] using congrFun (congrFun hm if2) if2
  exact hij

private theorem pow_eq_one_iff_of_torus {g : hypSU h 2 0} {a : Fin 2 → Kˣ}
    (hg : ((g : GL Ix K) : Matrix Ix Ix K) = diagonal (torusEntries h a isEmptyElim)) (m : ℕ) :
    g ^ m = 1 ↔ ∀ i, a i ^ m = 1 := by
  have hmat := uc22s218_u4_mat_pow h hg m
  constructor
  · intro hgm i
    have h1 := congrArg (fun z : ↥(hypSU h 2 0) =>
      ((z : GL Ix K) : Matrix Ix Ix K) (.inl i) (.inl i)) hgm
    simp only [hmat, diagonal_apply_eq, Pi.pow_apply, Subgroup.coe_one, Units.val_one,
      Matrix.one_apply_eq, torusEntries] at h1
    exact Units.ext (by simpa using h1)
  · intro ha
    apply CFSG.RankThree.CentralLiftU.hypSU_eq_of_diag h hmat (q' := fun _ => 1)
    · rw [Subgroup.coe_one, Units.val_one, diagonal_one.symm]
    · intro x
      simp [torusEntries, ← Units.val_pow_eq_pow_val, ha x]
    · intro k
      exact k.elim0

private theorem exists_torus_u (u : Kˣ) (hu : h.bar (u : K) = u) :
    ∃ g ∈ hypTorus h 2 0, orderOf g = orderOf u ∧ ∃ v : Ix → K, v ie2 = 1 ∧ v if2 = 1 ∧
      ((g : GL Ix K) : Matrix Ix Ix K) = diagonal v := by
  let a : Fin 2 → Kˣ := ![u, 1]
  have hratio : torusRatio h a (isEmptyElim : Fin 0 → Kˣ) = 1 := by
    have e0 : ∏ k : Fin 0, (((isEmptyElim k : Kˣ)) : K) = 1 := Fin.prod_univ_zero _
    rw [torusRatio, e0, mul_one, Fin.prod_univ_two]
    simp only [a, Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_one, map_one, div_one, hu]
    rw [mul_one]
    exact div_self u.ne_zero
  obtain ⟨g, hg, hgm⟩ := torusMat_mem_hypSU h a (d := isEmptyElim) (fun k => isEmptyElim k) hratio
  refine ⟨g, hg, ?_, torusEntries h a isEmptyElim, by simp [torusEntries, a, ie2],
    by simp [torusEntries, a, if2], hgm⟩
  rw [orderOf_eq_orderOf_iff]
  intro m
  rw [pow_eq_one_iff_of_torus h hgm m]
  constructor
  · intro hm
    exact hm 0
  · intro hm i
    fin_cases i
    · exact hm
    · simp [a]

private theorem exists_torus_b (b : Kˣ) (hb : h.bar (b : K) = (b : K)⁻¹) :
    ∃ g ∈ hypTorus h 2 0, orderOf g = orderOf b ∧ ∃ v : Ix → K, v ie2 = v if2 ∧ v ie1 = (b : K)⁻¹ ∧
      ((g : GL Ix K) : Matrix Ix Ix K) = diagonal v := by
  let a : Fin 2 → Kˣ := ![b⁻¹, b]
  have hb' : h.bar ((b⁻¹ : Kˣ) : K) = b := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hb, inv_inv]
  have hratio : torusRatio h a (isEmptyElim : Fin 0 → Kˣ) = 1 := by
    have e0 : ∏ k : Fin 0, (((isEmptyElim k : Kˣ)) : K) = 1 := Fin.prod_univ_zero _
    rw [torusRatio, e0, mul_one, Fin.prod_univ_two]
    simp only [a, Matrix.cons_val_zero, Matrix.cons_val_one, hb', hb]
    have hb0 : (b : K) ≠ 0 := b.ne_zero
    rw [Units.val_inv_eq_inv_val]
    field_simp
  obtain ⟨g, hg, hgm⟩ := torusMat_mem_hypSU h a (d := isEmptyElim) (fun k => isEmptyElim k) hratio
  refine ⟨g, hg, ?_, torusEntries h a isEmptyElim, ?_, by simp [torusEntries, a, ie1], hgm⟩
  · rw [orderOf_eq_orderOf_iff]
    intro m
    rw [pow_eq_one_iff_of_torus h hgm m]
    constructor
    · intro hm
      exact hm 1
    · intro hm i
      fin_cases i
      · simp [a, inv_pow, hm]
      · exact hm
  · simp [torusEntries, a, ie2, if2, hb]

private theorem levi218_U4_model [Finite ↥(hypSU h 2 0)] (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    (hpq1 : p ∣ 2 ^ n + 1) : Levi218 n (2 ^ (2 * n) - 1) (hypUnitriangular h 2 0) p := by
  classical
  have := h.finite
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨hypTorus h 2 0, MonoidHom.range (CFSG.Quasithin.H13.Sec53F.Unit.fieldAutHom h 2 0),
    uc22s218_u4_fieldBorelData_model h, fun {s r} hs hsn hr hrs => ?_⟩
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := uc22p218c_ne_two_of_dvd hs.pos hrs
  have hrn : r ∣ 2 ^ n - 1 := hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)
  have hq2 : 2 ^ (2 * n) - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have e : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [e]
    zify [h1, Nat.one_le_pow 2 (2 ^ n) (by omega)]
    ring
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r (by
    rw [Nat.card_units, h.card, hq2]
    exact Dvd.dvd.mul_right hrn _)
  have hu1 : u ^ (2 ^ n - 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hu]
    exact hrn
  have hubar : h.bar (u : K) = u := by
    rw [UnitaryFieldData.bar_apply]
    have : u ^ 2 ^ n = u := by
      rw [← Nat.sub_add_cancel (Nat.one_le_two_pow (n := n)), pow_succ, hu1, one_mul]
    simpa using congrArg Units.val this
  obtain ⟨x, hxH, hxo, v, hv2, hvf2, hxm⟩ := exists_torus_u h u hubar
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by
    rw [Nat.card_units, h.card, hq2]
    exact Dvd.dvd.mul_left hpq1 _)
  have hb1 : b ^ (2 ^ n + 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hb]
    exact hpq1
  have hbbar : h.bar (b : K) = (b : K)⁻¹ := by
    rw [UnitaryFieldData.bar_apply]
    have : b ^ 2 ^ n = b⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ]
      exact hb1
    rw [← Units.val_pow_eq_pow_val, this, Units.val_inv_eq_inv_val]
  obtain ⟨t, htH, hto, w, hw, hw1, htm⟩ := exists_torus_b h b hbbar
  have hSC : (levHom h).range ≤ centralizer {x} := by
    rintro _ ⟨A, rfl⟩
    rw [mem_centralizer_singleton_iff]
    apply hypSU_ext h
    rw [coe_mul_hypSU, coe_mul_hypSU, coe_levHom, hxm]
    exact (diagonal_commute_levMat (by rw [hv2, hvf2]) _).symm
  have htS : ∀ A, t * levHom h A = levHom h A * t := fun A => by
    apply hypSU_ext h
    rw [coe_mul_hypSU, coe_mul_hypSU, coe_levHom, htm]
    exact diagonal_commute_levMat hw _
  have htx : x * t = t * x := by
    apply hypSU_ext h
    rw [coe_mul_hypSU, coe_mul_hypSU, hxm, htm, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hFfin : Finite h.fixedField := inferInstance
  obtain ⟨A₀, hA₀⟩ := exists_prime_orderOf_dvd_card'
      (G := Matrix.SpecialLinearGroup (Fin 2) h.fixedField) p (by
    rw [CFSG.GH74.Generic.BProg.B3.S1IdentSl2.card_sl2, h.card_fixedField]
    refine dvd_mul_of_dvd_right (hpq1.trans ⟨2 ^ n - 1, ?_⟩) _
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    zify [h1, Nat.one_le_pow 2 (2 ^ n) (by omega)]
    ring)
  have hzo : orderOf (levHom h A₀) = p := by
    rw [orderOf_injective _ (levHom_injective h), hA₀]
  have hz1 : levHom h A₀ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hzo
    exact hp.one_lt.ne hzo
  have htz : t ∉ zpowers (levHom h A₀) := by
    intro ht
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 ht
    have h2 : levHom h (A₀ ^ k) = t := by rw [map_zpow]; exact hk
    have h1 := congrArg (fun g : hypSU h 2 0 => ((g : GL Ix K) : Matrix Ix Ix K) ie1 ie1) h2
    simp only [coe_levHom, htm, diagonal_apply_eq] at h1
    rw [hw1, levMat_apply] at h1
    simp [ie1, ie2, if1, if2] at h1
    have hb1' : (b : K) = 1 := by
      have := congrArg (·⁻¹) h1
      simpa using this.symm
    have : b = 1 := Units.ext hb1'
    rw [this, orderOf_one] at hb
    exact hp.one_lt.ne hb
  obtain ⟨hQe, hQc⟩ := CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_card_sup_zpowers hp
    (by rw [← hzo]; exact pow_orderOf_eq_one _) (by rw [← hb, ← hto]; exact pow_orderOf_eq_one _)
    hz1 htz (htS A₀).symm
  refine ⟨x, hxH, by rw [hxo, hu], (levHom h).range, n, hSC, by omega, Or.inl ?_,
    Or.inr ⟨⟨zpowers (levHom h A₀) ⊔ zpowers t, ?_, hQe, hQc⟩, fun A hAe hAc => ?_⟩⟩
  ·
    have := Fintype.ofFinite h.fixedField
    exact CFSG.CGT.PushingUpLit.CGT6K1.lieModel_PSL_two_of_mulEquiv_SL_two (by omega)
      (by rw [← Nat.card_eq_fintype_card, h.card_fixedField])
      (MonoidHom.ofInjective (levHom_injective h)).symm
  ·
    refine sup_le (zpowers_le.2 (hSC ⟨A₀, rfl⟩)) (zpowers_le.2 ?_)
    rw [mem_centralizer_singleton_iff]
    exact htx.symm
  ·
    have hζ : IsPrimitiveRoot (u : K) r := by
      have := IsPrimitiveRoot.orderOf u
      rw [hu] at this
      exact IsPrimitiveRoot.coe_units_iff.2 this
    obtain ⟨g, hg⟩ := CFSG.StandardType.exists_conj_hypEntries h hr hr2 hrn hζ (by norm_num) A hAe
      (by rw [hAc])
    have hwC : g⁻¹ * t * g ∈ centralizer (A : Set (hypSU h 2 0)) := by
      rw [mem_centralizer_iff]
      intro y hy
      obtain ⟨e, he⟩ := hg y hy
      have hcomm : g * y * g⁻¹ * t = t * (g * y * g⁻¹) := by
        apply hypSU_ext h
        rw [coe_mul_hypSU h (g * y * g⁻¹) t, coe_mul_hypSU h t (g * y * g⁻¹), he, htm,
          diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1
        funext i
        exact mul_comm _ _
      calc y * (g⁻¹ * t * g) = g⁻¹ * ((g * y * g⁻¹) * t) * g := by group
        _ = g⁻¹ * (t * (g * y * g⁻¹)) * g := by rw [hcomm]
        _ = g⁻¹ * t * g * y := by group
    have hwo : orderOf (g⁻¹ * t * g) = p := by
      have h1 : orderOf (MulAut.conj g⁻¹ t) = p := by rw [MulEquiv.orderOf_eq, hto, hb]
      rw [MulAut.conj_apply, inv_inv] at h1
      exact h1
    rw [← hwo, ← Subgroup.orderOf_mk _ hwC]
    exact orderOf_dvd_natCard _

end Model

theorem levi218_U4 {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsU4 Y n) (hn : ¬ IsPowTwo n)
    {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ 2 ^ n - 1) (hrk : ¬ p ∣ 2 ^ n + 1 → 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y)) :
    Levi218 n (2 ^ (2 * n) - 1) U p := by
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : 1 ≤ n := (CFSG.Blueprint.LieModel.admissible hY).2.1
  have hn3 : 3 ≤ n := by
    by_contra h3
    interval_cases n
    · exact hn ⟨0, rfl⟩
    · exact hn ⟨1, rfl⟩
  have hpq1 : p ∣ 2 ^ n + 1 := by
    by_contra h1
    have h2 := hrk h1
    rw [uc22s218_u4_pRank_eq_div hY hp hp2 h1] at h2
    have ho1 := uc22s218_u4_orderOf_ne_one (q := 2 ^ n) hp h1
    have ho2 : orderOf (-((2 ^ n : ℕ) : ZMod p)) ≠ 2 := by
      intro ho
      have hsq : (-((2 ^ n : ℕ) : ZMod p)) ^ orderOf (-((2 ^ n : ℕ) : ZMod p)) = 1 :=
        pow_orderOf_eq_one _
      rw [ho, sq, neg_mul_neg] at hsq
      rcases mul_self_eq_one_iff.1 hsq with h3 | h3
      · apply hpq
        have h4 : ((2 ^ n - 1 : ℕ) : ZMod p) = 0 := by
          rw [Nat.cast_sub Nat.one_le_two_pow, h3, Nat.cast_one, sub_self]
        exact (ZMod.natCast_eq_zero_iff _ _).1 h4
      · apply h1
        have h4 : ((2 ^ n + 1 : ℕ) : ZMod p) = 0 := by
          rw [Nat.cast_add, h3, Nat.cast_one, neg_add_cancel]
        exact (ZMod.natCast_eq_zero_iff _ _).1 h4
    have h4 : 4 / orderOf (-((2 ^ n : ℕ) : ZMod p)) ≤ 1 := by
      rcases Nat.lt_or_ge (orderOf (-((2 ^ n : ℕ) : ZMod p))) 3 with h5 | h5
      · interval_cases h6 : orderOf (-((2 ^ n : ℕ) : ZMod p)) <;> simp_all
      · exact (Nat.div_le_div_left h5 (by norm_num)).trans (by norm_num)
    omega
  obtain ⟨K, _, h, ⟨e⟩⟩ := CFSG.Quasithin.H13.U4Par.exists_hypSU_equiv_of_lieModel hY
  have : Finite ↥(hypSU h 2 0) := Finite.of_equiv Y e.symm.toEquiv
  have h1 := (levi218_U4_model h hn3 hp hpq1).map hp e
  exact h1.of_sylow hp hU

end CFSG.LocalAnalysis.UniquenessCase.UC22
