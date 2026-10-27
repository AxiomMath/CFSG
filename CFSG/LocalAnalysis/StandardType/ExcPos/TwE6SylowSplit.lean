module

public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs
public import CFSG.RankThree.Classical2.TwistedE6RationalOrder

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
  CFSG.StandardType.GGFinModel CFSG.Open


@[reducible] private noncomputable def lk0xtta_R (f : ℕ) :
    Subgroup (ModGL (langTag .twistedE6) GGL) := ggFixGp .twistedE6 f

@[reducible] private noncomputable def lk0xtta_T (f : ℕ) :
    Subgroup (ModGL (langTag .twistedE6) GGL) :=
  graphFixedTorus TwistTag.E6 GGL (ggFrobT f)

private def lk0xtta_S (q k : ℕ) : ℕ := Finset.sum (Finset.range k) fun i => q ^ i

private def lk0xtta_M (q : ℕ) : ℕ :=
  q ^ 36 * lk0xtta_S q 12 * lk0xtta_S q 8 * lk0xtta_S q 6 * (q ^ 9 + 1) * (q ^ 5 + 1)

private theorem lk0xtta_S_succ (q n : ℕ) :
    lk0xtta_S q (n + 1) = lk0xtta_S q n + q ^ n := by
  simp [lk0xtta_S, Finset.sum_range_succ]

private theorem lk0xtta_geom_add_one (q k : ℕ) (hq : 1 ≤ q) :
    (q - 1) * lk0xtta_S q k + 1 = q ^ k := by
  induction k with
  | zero => simp [lk0xtta_S]
  | succ n ih =>
    rw [lk0xtta_S_succ, mul_add, pow_succ]
    calc (q - 1) * lk0xtta_S q n + (q - 1) * q ^ n + 1
        = ((q - 1) * lk0xtta_S q n + 1) + (q - 1) * q ^ n := by ring
      _ = q ^ n + (q - 1) * q ^ n := by rw [ih]
      _ = (1 + (q - 1)) * q ^ n := by ring
      _ = q * q ^ n := by rw [show 1 + (q - 1) = q by omega]
      _ = q ^ n * q := by ring

private theorem lk0xtta_geom_mul (q k : ℕ) (hq : 1 ≤ q) :
    (q - 1) * lk0xtta_S q k = q ^ k - 1 := by
  have h := lk0xtta_geom_add_one q k hq
  omega

private theorem lk0xtta_p_not_dvd_2304 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (2304 : ZMod p) ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro h
  have hd : p ∣ 2304 := (ZMod.natCast_eq_zero_iff 2304 p).mp h
  have h23 : p ∣ 2 ∨ p ∣ 3 := by
    have hnum : (2304 : ℕ) = 2 ^ 8 * 3 ^ 2 := by norm_num
    rw [hnum] at hd
    rcases hp.dvd_mul.mp hd with h2 | h3
    · exact Or.inl (hp.dvd_of_dvd_pow h2)
    · exact Or.inr (hp.dvd_of_dvd_pow h3)
  rcases h23 with h2 | h3
  · have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
    omega
  · have : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
    omega

private theorem lk0xtta_not_dvd_index_arith {q p index : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hq2 : 2 ≤ q) (hpq : p ∣ q - 1)
    (hidx : (q ^ 2 - 1) ^ 2 * (q - 1) ^ 2 * index =
      q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
        (q ^ 5 + 1) * (q ^ 2 - 1)) :
    ¬ p ∣ index := by
  have hq1 : 1 ≤ q := by omega
  have hS2 : lk0xtta_S q 2 = q + 1 := by
    simp only [lk0xtta_S, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
      zero_add]
    ring
  have h2 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have h := lk0xtta_geom_mul q 2 hq1
    rw [hS2] at h
    exact h.symm
  have hT : (q ^ 2 - 1) ^ 2 * (q - 1) ^ 2 = (q - 1) ^ 4 * (q + 1) ^ 2 := by
    rw [h2]; ring
  have hR : q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
        (q ^ 5 + 1) * (q ^ 2 - 1)
      = (q - 1) ^ 4 * ((q + 1) * lk0xtta_M q) := by
    rw [← lk0xtta_geom_mul q 12 hq1, ← lk0xtta_geom_mul q 8 hq1,
      ← lk0xtta_geom_mul q 6 hq1, h2]
    simp only [lk0xtta_M]
    ring
  have hidx' := hidx
  rw [hT, hR] at hidx'
  rw [mul_assoc] at hidx'
  have hcancel1 : (q + 1) ^ 2 * index = (q + 1) * lk0xtta_M q :=
    Nat.eq_of_mul_eq_mul_left (pow_pos (by omega : 0 < q - 1) 4) hidx'
  have hfinal : (q + 1) * index = lk0xtta_M q := by
    have h := hcancel1
    rw [pow_two, mul_assoc] at h
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q + 1) h
  have hqmod : (q : ZMod p) = 1 := by
    have hd : ((q - 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (q - 1) p).mpr hpq
    have hqeq : q = (q - 1) + 1 := (Nat.sub_add_cancel hq1).symm
    rw [hqeq, Nat.cast_add, Nat.cast_one, hd, zero_add]
  have hS : ∀ k, ((lk0xtta_S q k : ℕ) : ZMod p) = (k : ZMod p) := by
    intro k
    simp only [lk0xtta_S, Nat.cast_sum, Nat.cast_pow]
    have hterm : ∀ i ∈ Finset.range k, ((q : ZMod p)) ^ i = 1 := by
      intro i _
      rw [hqmod, one_pow]
    rw [Finset.sum_congr rfl hterm]
    simp
  have hMval : ((lk0xtta_M q : ℕ) : ZMod p) = 2304 := by
    simp only [lk0xtta_M, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, hqmod,
      hS 12, hS 8, hS 6]
    norm_num
  intro hdvd
  have hzero : ((index : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff index p).mpr hdvd
  have hcast := congrArg (fun n : ℕ => (n : ZMod p)) hfinal
  have hMzero : ((lk0xtta_M q : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, hqmod, hzero, mul_zero] at hcast
    exact hcast.symm
  rw [hMval] at hMzero
  exact lk0xtta_p_not_dvd_2304 hp hp5 hMzero

private theorem lk0xtta_exists_conj_le_of_not_dvd_index {M : Type*} [Group M] [Finite M]
    {p : ℕ} (hp : p.Prime) {A S : Subgroup M} (hAp : IsPGroup p A) (hnot : ¬ p ∣ S.index) :
    ∃ x : M, ∀ a ∈ A, x⁻¹ * a * x ∈ S := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let Ω := M ⧸ S
  let _ : MulAction A Ω :=
    { smul := fun a q => (a : M) • q
      one_smul := fun q => one_smul M q
      mul_smul := fun a b q => mul_smul (a : M) (b : M) q }
  have hcard : Nat.card Ω = S.index := (Subgroup.index_eq_card S).symm
  have hnot' : ¬ p ∣ Nat.card Ω := by rw [hcard]; exact hnot
  obtain ⟨q, hq⟩ := hAp.nonempty_fixed_point_of_prime_not_dvd_card Ω hnot'
  set x : M := q.out with hxdef
  have hfix : ∀ a : A, (a : M) • q = q := fun a => MulAction.mem_fixedPoints.mp hq a
  refine ⟨x, fun a ha => ?_⟩
  have h1 : QuotientGroup.mk (s := S) ((a : M) * x) = QuotientGroup.mk (s := S) x := by
    have hL : QuotientGroup.mk (s := S) ((a : M) * x) = (a : M) • q := by
      rw [hxdef]
      simpa using MulAction.Quotient.mk_smul_out (b := (a : M)) (q := q)
    have hR : QuotientGroup.mk (s := S) x = q := by rw [hxdef]; simp
    rw [hL, hR, hfix ⟨a, ha⟩]
  have h2 : ((a : M) * x)⁻¹ * x ∈ S := QuotientGroup.leftRel_apply.mp (Quotient.exact' h1)
  have h3 : (((a : M) * x)⁻¹ * x : M) = x⁻¹ * a⁻¹ * x := by simp [mul_assoc]
  rw [h3] at h2
  have hinv := S.inv_mem h2
  simpa [mul_assoc] using hinv

theorem twE6_pSubgroup_split {f : ℕ} (hf : 1 ≤ f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ f - 1) {E : Subgroup (ModGL (langTag .twistedE6) GGL)}
    (hE : E ≤ ggFixGp .twistedE6 f) (hEp : IsPGroup p ↥E) :
    ∃ g ∈ ggFixGp .twistedE6 f, ∀ x ∈ E, g⁻¹ * x * g ∈ torusGroup (langTag .twistedE6) GGL := by
  classical
  let K := GaloisField 2 (2 * f)
  letI : Algebra K GGL := (ggRatEmb (2 * f)).toAlgebra
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  haveI : CharP K 2 := inferInstance
  haveI : CharP GGL 2 := inferInstance
  haveI : IsScalarTower (ZMod 2) K GGL :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  haveI : IsAlgClosure K GGL :=
    { isAlgClosed := inferInstance
      isAlgebraic := Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := K) }
  have hK : Nat.card K = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega : 2 * f ≠ 0)]
    rw [← pow_mul, Nat.mul_comm]
  let σ : K →+* K := iterateFrobenius K 2 f
  have hσ : ∀ c, σ c = c ^ 2 ^ f := fun c => iterateFrobenius_def 2 f c
  obtain ⟨hfin, -, -, -, hTcard, hRcard, -⟩ :=
    CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order (ℓ := 2) (f := f) Nat.prime_two hf K hK σ hσ
      GGL (ggFrobT f) (ggFrobT_apply f)
  haveI : Finite ↥(lk0xtta_R f) := by
    show Finite ↥(ggFixGp .twistedE6 f)
    rw [show ggFixGp .twistedE6 f = twistedFixedGroup TwistTag.E6 GGL (ggFrobT f) from rfl]
    exact hfin
  have hTR : (lk0xtta_T f) ≤ (lk0xtta_R f) := by
    rw [show (lk0xtta_T f) = graphFixedTorus TwistTag.E6 GGL (ggFrobT f) from rfl, graphFixedTorus]
    exact inf_le_right
  have hTG : (lk0xtta_T f) ≤ torusGroup (langTag .twistedE6) GGL := by
    rw [show (lk0xtta_T f) = graphFixedTorus TwistTag.E6 GGL (ggFrobT f) from rfl, graphFixedTorus]
    exact inf_le_left
  have hcardT : Nat.card ↥(lk0xtta_T f) = ((2 ^ f) ^ 2 - 1) ^ 2 * (2 ^ f - 1) ^ 2 := by
    show Nat.card ↥(graphFixedTorus TwistTag.E6 GGL (ggFrobT f)) = _
    exact hTcard
  have hcardR : Nat.card ↥(lk0xtta_R f) =
      (2 ^ f) ^ 36 * ((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 9 + 1) * ((2 ^ f) ^ 8 - 1) *
        ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 5 + 1) * ((2 ^ f) ^ 2 - 1) := by
    show Nat.card ↥(twistedFixedGroup TwistTag.E6 GGL (ggFrobT f)) = _
    exact hRcard
  have hindex : Nat.card ↥(lk0xtta_T f) * ((lk0xtta_T f).subgroupOf (lk0xtta_R f)).index = Nat.card ↥(lk0xtta_R f) := by
    have h := Subgroup.card_mul_index (H := (lk0xtta_T f).subgroupOf (lk0xtta_R f))
    have hcard : Nat.card ↥((lk0xtta_T f).subgroupOf (lk0xtta_R f)) = Nat.card ↥(lk0xtta_T f) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTR).toEquiv
    rwa [hcard] at h
  have harith : ((2 ^ f) ^ 2 - 1) ^ 2 * (2 ^ f - 1) ^ 2 * ((lk0xtta_T f).subgroupOf (lk0xtta_R f)).index =
      (2 ^ f) ^ 36 * ((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 9 + 1) * ((2 ^ f) ^ 8 - 1) *
        ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 5 + 1) * ((2 ^ f) ^ 2 - 1) := by
    rw [← hcardT, ← hcardR]
    exact hindex
  have hq2 : 2 ≤ 2 ^ f := by
    have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hf
    simpa using h
  have hnot : ¬ p ∣ ((lk0xtta_T f).subgroupOf (lk0xtta_R f)).index :=
    lk0xtta_not_dvd_index_arith hp hp5 hq2 hpq harith
  have hEp' : IsPGroup p ↥(E.subgroupOf (lk0xtta_R f)) :=
    IsPGroup.of_injective hEp (Subgroup.subgroupOfEquivOfLe hE).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hE).injective
  obtain ⟨x, hxconj⟩ :=
    lk0xtta_exists_conj_le_of_not_dvd_index (p := p) hp (A := E.subgroupOf (lk0xtta_R f))
      (S := (lk0xtta_T f).subgroupOf (lk0xtta_R f)) hEp' hnot
  refine ⟨(x : ModGL (langTag .twistedE6) GGL), x.2, ?_⟩
  intro y hy
  have hmem : (⟨y, hE hy⟩ : ↥(lk0xtta_R f)) ∈ E.subgroupOf (lk0xtta_R f) := by
    rw [Subgroup.mem_subgroupOf]
    exact hy
  have hconj := hxconj ⟨y, hE hy⟩ hmem
  exact hTG (Subgroup.mem_subgroupOf.mp hconj)

end CFSG.StandardType.LieKnownR2.ExcPos
