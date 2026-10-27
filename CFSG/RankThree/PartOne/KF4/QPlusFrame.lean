module

public import CFSG.RankThree.PartOne.KF4.F4Sylow
public import CFSG.RankThree.PartOne.KE.A1Weyl
public import CFSG.RankThree.PartOne.KE.CTCasesE6Arith
public import CFSG.RankThree.PartOne.KF4.QPlusWeyl

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec)
open CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE.CTE6
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley.SteinbergBT.TrialityPlane
open scoped Matrix


section Arith

theorem f4QPlus_zmod_facts {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (y : ZMod p) (hy : y + 1 = 0) :
    y ≠ 0 ∧ y - 1 ≠ 0 ∧ y ^ 4 + y ^ 2 + 1 ≠ 0 ∧ y ^ 6 + y ^ 4 + y ^ 2 + 1 ≠ 0 ∧
      y ^ 10 + y ^ 8 + y ^ 6 + y ^ 4 + y ^ 2 + 1 ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    by_contra h
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by norm_num)
  have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (by norm_num) (by omega)
  have h3 : ((3 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (by norm_num) (by omega)
  have h4 : ((4 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (by norm_num) (by omega)
  have h6 : ((6 : ℕ) : ZMod p) ≠ 0 := fun h => by
    have h' := (ZMod.natCast_eq_zero_iff 6 p).1 h
    have h'' : p ∣ 2 * 3 := by simpa using h'
    rcases (Nat.Prime.dvd_mul hp).1 h'' with h1 | h1
    · have := Nat.le_of_dvd (by norm_num) h1
      omega
    · have := Nat.le_of_dvd (by norm_num) h1
      omega
  have h2' : (2 : ZMod p) ≠ 0 := by simpa using h2
  have h3' : (3 : ZMod p) ≠ 0 := by simpa using h3
  have h4' : (4 : ZMod p) ≠ 0 := by simpa using h4
  have h6' : (6 : ZMod p) ≠ 0 := by simpa using h6
  have hy0 : y ≠ 0 := fun h => by
    rw [h, zero_add] at hy
    exact one_ne_zero hy
  have hy2 : y ^ 2 = 1 := by linear_combination (y - 1) * hy
  have hy4 : y ^ 4 = 1 := by rw [show y ^ 4 = (y ^ 2) ^ 2 by ring, hy2, one_pow]
  have hy6 : y ^ 6 = 1 := by rw [show y ^ 6 = (y ^ 2) ^ 3 by ring, hy2, one_pow]
  have hy8 : y ^ 8 = 1 := by rw [show y ^ 8 = (y ^ 2) ^ 4 by ring, hy2, one_pow]
  have hy10 : y ^ 10 = 1 := by rw [show y ^ 10 = (y ^ 2) ^ 5 by ring, hy2, one_pow]
  refine ⟨hy0, ?_, ?_, ?_, ?_⟩
  · intro h
    apply h2'
    linear_combination hy - h
  · intro h
    apply h3'
    linear_combination h - hy4 - hy2
  · intro h
    apply h4'
    linear_combination h - hy6 - hy4 - hy2
  · intro h
    apply h6'
    linear_combination h - hy10 - hy8 - hy6 - hy4 - hy2

theorem f4QPlus_ordProj (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hΦ : ((Nat.card K : ℕ) : ZMod p) + 1 = 0) :
    ordProj[p] (Nat.card (adjointGroup .F4 K)) = ordProj[p] ((Nat.card K + 1) ^ 4) := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  set q : ℕ := Nat.card K with hqdef
  set n₀ : ℕ := q + 1 with hn₀def
  have hn₀ne : n₀ ≠ 0 := by omega
  have hn₀ : (n₀ : ℤ) = (q : ℤ) + 1 := by rw [hn₀def]; push_cast; ring
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hy0, hy1, hy4, hy6, hy10⟩ := f4QPlus_zmod_facts hp hp3 ((q : ℕ) : ZMod p) hΦ
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hnd : ∀ y : ℤ, (y : ZMod p) ≠ 0 → ¬ (p : ℤ) ∣ y := fun y hy hd =>
    hy ((ZMod.intCast_zmod_eq_zero_iff_dvd y p).2 hd)
  have hq1 : 1 ≤ q := by omega
  have hcast : ∀ d : ℕ, ((q ^ d - 1 : ℕ) : ℤ) = (q : ℤ) ^ d - 1 := fun d => by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hq1), Nat.cast_pow, Nat.cast_one]
  have hcard : Nat.card (adjointGroup .F4 K) =
      q ^ 24 * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1) := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4]
    rfl
  have hN : ∀ d : ℕ, 0 < d → q ^ d - 1 ≠ 0 := by
    intro d hd
    have : 1 < q ^ d := Nat.one_lt_pow hd.ne' (by omega)
    omega
  have hpq : ¬ p ∣ q ^ 24 := fun h => by
    have h1 : p ∣ q := hp.dvd_of_dvd_pow h
    exact hy0 ((ZMod.natCast_eq_zero_iff q p).2 h1)
  have hnd1 : ¬ (p : ℤ) ∣ ((q : ℤ) - 1) := hnd _ (by push_cast; exact hy1)
  have hR2 : ¬ (p : ℤ) ∣ ((q : ℤ) - 1) := hnd1
  have hR6 : ¬ (p : ℤ) ∣ ((q : ℤ) - 1) * ((q : ℤ) ^ 4 + (q : ℤ) ^ 2 + 1) :=
    hpz.not_dvd_mul hnd1 (hnd _ (by push_cast; exact hy4))
  have hR8 : ¬ (p : ℤ) ∣ ((q : ℤ) - 1) * ((q : ℤ) ^ 6 + (q : ℤ) ^ 4 + (q : ℤ) ^ 2 + 1) :=
    hpz.not_dvd_mul hnd1 (hnd _ (by push_cast; exact hy6))
  have hR12 : ¬ (p : ℤ) ∣ ((q : ℤ) - 1) * ((q : ℤ) ^ 10 + (q : ℤ) ^ 8 + (q : ℤ) ^ 6 +
      (q : ℤ) ^ 4 + (q : ℤ) ^ 2 + 1) :=
    hpz.not_dvd_mul hnd1 (hnd _ (by push_cast; exact hy10))
  have e2 : ordProj[p] (q ^ 2 - 1) = ordProj[p] n₀ :=
    ordProj_eq_of_int_factor hn₀ne (hN 2 (by norm_num)) (R := (q : ℤ) - 1)
      (by rw [hcast, hn₀]; ring) hR2
  have e6 : ordProj[p] (q ^ 6 - 1) = ordProj[p] n₀ :=
    ordProj_eq_of_int_factor hn₀ne (hN 6 (by norm_num))
      (R := ((q : ℤ) - 1) * ((q : ℤ) ^ 4 + (q : ℤ) ^ 2 + 1))
      (by rw [hcast, hn₀]; ring) hR6
  have e8 : ordProj[p] (q ^ 8 - 1) = ordProj[p] n₀ :=
    ordProj_eq_of_int_factor hn₀ne (hN 8 (by norm_num))
      (R := ((q : ℤ) - 1) * ((q : ℤ) ^ 6 + (q : ℤ) ^ 4 + (q : ℤ) ^ 2 + 1))
      (by rw [hcast, hn₀]; ring) hR8
  have e12 : ordProj[p] (q ^ 12 - 1) = ordProj[p] n₀ :=
    ordProj_eq_of_int_factor hn₀ne (hN 12 (by norm_num))
      (R := ((q : ℤ) - 1) * ((q : ℤ) ^ 10 + (q : ℤ) ^ 8 + (q : ℤ) ^ 6 + (q : ℤ) ^ 4 +
        (q : ℤ) ^ 2 + 1))
      (by rw [hcast, hn₀]; ring) hR12
  have h24 : q ^ 24 ≠ 0 := by positivity
  have h12 := hN 12 (by norm_num)
  have h8 := hN 8 (by norm_num)
  have h6 := hN 6 (by norm_num)
  have h2 := hN 2 (by norm_num)
  rw [hcard, Nat.ordProj_mul p (mul_ne_zero (mul_ne_zero (mul_ne_zero h24 h12) h8) h6) h2,
    Nat.ordProj_mul p (mul_ne_zero (mul_ne_zero h24 h12) h8) h6,
    Nat.ordProj_mul p (mul_ne_zero h24 h12) h8, Nat.ordProj_mul p h24 h12,
    ordProj_eq_one_of_not_dvd hpq, e2, e6, e8, e12,
    show (q + 1) ^ 4 = n₀ * n₀ * n₀ * n₀ by rw [hn₀def]; ring,
    Nat.ordProj_mul p (mul_ne_zero (mul_ne_zero hn₀ne hn₀ne) hn₀ne) hn₀ne,
    Nat.ordProj_mul p (mul_ne_zero hn₀ne hn₀ne) hn₀ne, Nat.ordProj_mul p hn₀ne hn₀ne]
  ring

end Arith

section Torus

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]

theorem qp_card_rootsOfUnity_of_odd {m : ℕ} (hm : Odd m) :
    Nat.card (rootsOfUnity m L) = m := by
  have hm0 : (m : L) ≠ 0 := fun h => by
    have := (CharP.cast_eq_zero_iff L 2 m).1 h
    exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 this)
  have : NeZero m := ⟨hm.pos.ne'⟩
  have : NeZero (m : L) := ⟨hm0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L m
  exact hζ.card_rootsOfUnity

omit
  [CharP L 2] [IsAlgClosed L] in
theorem qp_mem_fixedCharTuples_iff {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (a : Fin Tag.F4.rank → Lˣ) :
    a ∈ fixedCharTuples (-1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) Fr ↔
      ∀ i, a i ^ (q + 1) = 1 := by
  have hmap : ∀ y : Lˣ, Units.map Fr.toMonoidHom y = y ^ q := fun y => by
    apply Units.ext
    simp [hFr]
  rw [mem_fixedCharTuples_iff]
  constructor
  · intro h i
    have := h (Pi.single i 1)
    rw [Matrix.neg_mulVec, Matrix.one_mulVec, rootChar_neg_vec, CTTorus.rootChar_single, hmap]
      at this
    rw [pow_succ]
    rw [← this, inv_mul_cancel]
  · intro h u
    rw [Matrix.neg_mulVec, Matrix.one_mulVec, rootChar_neg_vec, hmap]
    have h1 : rootChar a u ^ (q + 1) = 1 := by
      rw [rootChar, ← Finset.prod_pow]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, h i,
        _root_.one_zpow]
    rw [pow_succ] at h1
    exact inv_eq_of_mul_eq_one_left h1

theorem qp_card_fixedCharTuples {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (hq : Even q) :
    Nat.card (fixedCharTuples (-1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) Fr) =
      (q + 1) ^ 4 := by
  have hodd : Odd (q + 1) := hq.add_one
  let e : fixedCharTuples (-1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) Fr ≃
      (Fin Tag.F4.rank → rootsOfUnity (q + 1) L) :=
    { toFun := fun a i => ⟨a.1 i, (mem_rootsOfUnity (q + 1) (a.1 i)).2
        ((qp_mem_fixedCharTuples_iff hFr a.1).1 a.2 i)⟩
      invFun := fun z => ⟨fun i => (z i : Lˣ), (qp_mem_fixedCharTuples_iff hFr _).2 fun i =>
        (mem_rootsOfUnity (q + 1) _).1 (z i).2⟩
      left_inv := fun a => rfl
      right_inv := fun z => rfl }
  rw [Nat.card_congr e, Nat.card_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  simp only [qp_card_rootsOfUnity_of_odd (L := L) hodd]
  rfl

end Torus

section Frame

theorem f4_qplus_frame (K : Type) [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hΦ : ((Nat.card K : ℕ) : ZMod p) + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2] :
    ∃ g0 : ModGL .F4 L, g0 ∈ adjointGroup .F4 L ∧
      Units.map (entrywiseHom (iterateFrobenius L 2 f)) g0 = g0 * qpRep L ∧
      (∀ P : Subgroup (ModGL .F4 L), Finite P → P ≤ adjointGroup .F4 L →
        (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L 2 f)) x = x) → ⁅P, P⁆ = P →
          P ≤ (adjEmb .F4 K L).range) ∧
      twistedTorusOf (qpRep L) (Units.map (entrywiseHom (iterateFrobenius L 2 f))) =
        (fixedCharTuples (-1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ)
          (iterateFrobenius L 2 f)).map (rootDiagUnitHom .F4 L) ∧
      ∀ Q : Subgroup (adjointGroup .F4 K), IsPGroup p Q →
        ∃ c : adjointGroup .F4 K, ∀ q ∈ Q, g0⁻¹ * adjEmb .F4 K L (c * q * c⁻¹) * g0 ∈
          twistedTorusOf (qpRep L) (Units.map (entrywiseHom (iterateFrobenius L 2 f))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L 2 f with hFrdef
  set Φ : ModGL .F4 L →* ModGL .F4 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr' : ∀ c, Fr c = c ^ (2 ^ f) := fun c => iterateFrobenius_def 2 f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hnm : qpRep L ∈ monomialSubgroup .F4 L := qpRep_mem_monomial
  have hnC : qpRep L ∈ adjointGroup .F4 L := qpRep_mem_adjointGroup
  have hinj0 : Function.Injective (rootDiagUnitHom .F4 L) := rootDiagUnit_injective
  have hnW : ∀ u, weylQuotientHom .F4 L ⟨qpRep L, hnm⟩ • u =
      (-1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) *ᵥ u := fun u => by
    rw [weylQuotientHom_qpRep_smul, Matrix.neg_mulVec, Matrix.one_mulVec]
  have hT : twistedTorusOf (qpRep L) Φ = (fixedCharTuples
      (-1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) Fr).map (rootDiagUnitHom .F4 L) := by
    have h := twistedFixedTuples_eq_fixedCharTuples hnW Fr
    rw [← h]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl Fr
  have hZcard : Nat.card (twistedTorusOf (qpRep L) Φ) = (Nat.card K + 1) ^ 4 := by
    rw [hT, Subgroup.card_map_of_injective hinj0]
    refine qp_card_fixedCharTuples hFr ?_
    rw [hK]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩)
  have hN : (Nat.card K + 1) ^ 4 ≠ 0 := by positivity
  have hord : p ^ (Nat.card (adjointGroup .F4 K)).factorization p =
      p ^ ((Nat.card K + 1) ^ 4).factorization p := f4QPlus_ordProj K hp hp3 hΦ
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := sigma_untwisted_sylow_F4 K hf hK L hp hp3 (qpRep L)
    hnC (twistedTorusOf (qpRep L) Φ) le_rfl hN hZcard hord
  refine ⟨g0, hg0C, hg0, hperf, hT, fun Q hQ => ?_⟩
  obtain ⟨c, hc⟩ := hconj Q hQ
  exact ⟨c, fun q hq => (mem_subtorusImage_iff _ _ _ _).1 (hc q hq)⟩

end Frame

end CFSG.RankThree.PartOne.KF4
