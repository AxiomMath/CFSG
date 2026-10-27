module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherKit
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.HardMathSupport.RichardWeiss.Proving.WCLocalBridge

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open Matrix
open scoped MatrixGroups

theorem gf2_eq_zero_or_one (r : GaloisField 2 1) : r = 0 ∨ r = 1 :=
  CFSG.HardMathSupport.RichardWeiss.Proving.galoisField_two_one_eq_zero_or_one r

theorem gf2_one_add_one : (1 : GaloisField 2 1) + 1 = 0 := by
  rw [one_add_one_eq_two]
  exact CharP.cast_eq_zero (GaloisField 2 1) 2

theorem gf2_vec_add_self {n : ℕ} (v : Fin n → GaloisField 2 1) : v + v = 0 := by
  ext k
  rw [Pi.add_apply, Pi.zero_apply, ← one_mul (v k), ← add_mul, gf2_one_add_one, zero_mul]

theorem center_SL_gf2 {n : ℕ} (hn : 1 ≤ n) : Subgroup.center SL(n, GaloisField 2 1) = ⊥ :=
  Sec4.center_specialLinearGroup_eq_bot fun r hr => by
    rcases gf2_eq_zero_or_one r with rfl | rfl
    · rw [zero_pow (by omega)] at hr
      exact absurd hr zero_ne_one
    · rfl

noncomputable def slEquivProjSL {n : ℕ} (hn : 1 ≤ n) :
    SL(n, GaloisField 2 1) ≃* projSL n (GaloisField 2 1) :=
  ((QuotientGroup.quotientMulEquivOfEq (show
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars n (GaloisField 2 1) = ⊥ by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center,
      center_SL_gf2 hn])).trans QuotientGroup.quotientBot).symm.trans
    (Sec4.projSLEquivProjectiveSL n _).symm

theorem card_SL_gf2 {n : ℕ} (hn : 1 ≤ n) :
    Nat.card SL(n, GaloisField 2 1) =
      2 ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (2 ^ j - 1) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq hn,
    GaloisField.card 2 1 one_ne_zero, pow_one]

theorem center_projSL_gf2 {n : ℕ} (hn : 1 ≤ n) :
    Subgroup.center (projSL n (GaloisField 2 1)) = ⊥ :=
  Sec4.center_eq_bot_of_mulEquiv (slEquivProjSL hn).symm (center_SL_gf2 hn)

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (higher_linear_outer_order_divides_field_gcd_bound) in
theorem not_three_dvd_card_outer_projSL_gf2 {n : ℕ} (hn : 3 ≤ n) :
    ¬ 3 ∣ Nat.card (Outer (projSL n (GaloisField 2 1))) := by
  intro h3
  have hd := higher_linear_outer_order_divides_field_gcd_bound
    (k := GaloisField 2 1) Nat.prime_two le_rfl hn (GaloisField.card 2 1 one_ne_zero)
  rw [Nat.card_congr (equivalence (Sec4.projSLEquivProjectiveSL n (GaloisField 2 1))).toEquiv]
    at h3
  rw [show Nat.gcd n (2 ^ 1 - 1) = 1 by norm_num] at hd
  have := Nat.le_of_dvd (by norm_num) (h3.trans hd)
  omega


section Transvection

variable {n : ℕ}

theorem SL_ext_smul {A B : SL(n, GaloisField 2 1)}
    (h : ∀ k, A • (Pi.single k 1 : Fin n → GaloisField 2 1) = B • Pi.single k 1) : A = B :=
  Subtype.ext (Matrix.ext_of_mulVec_single fun k => h k)

theorem transvection_smul_single_of_ne {i j k : Fin n} (hij : i ≠ j) (hk : k ≠ j)
    (c : GaloisField 2 1) :
    SpecialLinearGroup.transvection hij c • (Pi.single k 1 : Fin n → GaloisField 2 1) =
      Pi.single k 1 := by
  change (SpecialLinearGroup.transvection hij c : Matrix (Fin n) (Fin n) (GaloisField 2 1)) *ᵥ
    (Pi.single k 1 : Fin n → GaloisField 2 1) = Pi.single k 1
  rw [SpecialLinearGroup.transvection_coe, add_mulVec, one_mulVec, single_mulVec_eq,
    Pi.single_eq_of_ne hk.symm, mul_zero, zero_smul, add_zero]

theorem transvection_smul_single_snd' {i j : Fin n} (hij : i ≠ j) :
    SpecialLinearGroup.transvection hij (1 : GaloisField 2 1) •
      (Pi.single j 1 : Fin n → GaloisField 2 1) = Pi.single j 1 + Pi.single i 1 := by
  rw [SpecialLinearGroup.transvection_smul_single_snd, one_smul]

noncomputable def blk {a b : Fin n} (hab : a ≠ b) : SL(n, GaloisField 2 1) :=
  SpecialLinearGroup.transvection hab 1 * SpecialLinearGroup.transvection hab.symm 1

theorem blk_smul_fst {a b : Fin n} (hab : a ≠ b) :
    blk hab • (Pi.single a 1 : Fin n → GaloisField 2 1) = Pi.single b 1 := by
  rw [blk, mul_smul, transvection_smul_single_snd' hab.symm, smul_add,
    SpecialLinearGroup.transvection_smul_single_fst, transvection_smul_single_snd' hab,
    add_left_comm, gf2_vec_add_self, add_zero]

theorem blk_smul_snd {a b : Fin n} (hab : a ≠ b) :
    blk hab • (Pi.single b 1 : Fin n → GaloisField 2 1) = Pi.single a 1 + Pi.single b 1 := by
  rw [blk, mul_smul, SpecialLinearGroup.transvection_smul_single_fst,
    transvection_smul_single_snd' hab, add_comm]

theorem blk_smul_of_ne {a b k : Fin n} (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b) :
    blk hab • (Pi.single k 1 : Fin n → GaloisField 2 1) = Pi.single k 1 := by
  rw [blk, mul_smul, transvection_smul_single_of_ne hab.symm hka,
    transvection_smul_single_of_ne hab hkb]

theorem blk_pow_three {a b : Fin n} (hab : a ≠ b) : blk hab ^ 3 = 1 := by
  apply SL_ext_smul
  intro k
  rw [one_smul, pow_three, mul_smul, mul_smul]
  by_cases hka : k = a
  · subst hka
    rw [blk_smul_fst, blk_smul_snd, smul_add, blk_smul_fst, blk_smul_snd, add_left_comm,
      gf2_vec_add_self, add_zero]
  by_cases hkb : k = b
  · subst hkb
    rw [blk_smul_snd, smul_add, blk_smul_fst, blk_smul_snd, add_left_comm, gf2_vec_add_self,
      add_zero, blk_smul_fst]
  · rw [blk_smul_of_ne hab hka hkb, blk_smul_of_ne hab hka hkb, blk_smul_of_ne hab hka hkb]

theorem blk_ne_one {a b : Fin n} (hab : a ≠ b) : blk hab ≠ 1 := by
  intro h
  have h1 := blk_smul_fst hab
  rw [h, one_smul] at h1
  have h2 := congrFun h1 a
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hab] at h2
  exact one_ne_zero h2

theorem commute_transvection_of_ne {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) (hil : i ≠ l)
    (hjk : j ≠ k) (c d : GaloisField 2 1) :
    Commute (SpecialLinearGroup.transvection hij c) (SpecialLinearGroup.transvection hkl d) :=
  SpecialLinearGroup.commute_transvection hij hkl hjk hil.symm c d

theorem commute_blk_transvection {a b i j : Fin n} (hab : a ≠ b) (hij : i ≠ j) (hia : i ≠ a)
    (hib : i ≠ b) (hja : j ≠ a) (hjb : j ≠ b) (c : GaloisField 2 1) :
    Commute (blk hab) (SpecialLinearGroup.transvection hij c) :=
  Commute.mul_left (commute_transvection_of_ne hab hij hja.symm hib.symm 1 c)
    (commute_transvection_of_ne hab.symm hij hjb.symm hia.symm 1 c)

theorem commute_blk_blk {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) : Commute (blk hab) (blk hcd) :=
  Commute.mul_right (commute_blk_transvection hab hcd hac.symm hbc.symm had.symm hbd.symm 1)
    (commute_blk_transvection hab hcd.symm had.symm hbd.symm hac.symm hbc.symm 1)

theorem eq_top_of_hub {H : Subgroup SL(n, GaloisField 2 1)} (h : Fin n)
    (hin : ∀ (i : Fin n) (hi : i ≠ h), SpecialLinearGroup.transvection hi 1 ∈ H)
    (hout : ∀ (i : Fin n) (hi : h ≠ i), SpecialLinearGroup.transvection hi 1 ∈ H) : H = ⊤ := by
  have hall : ∀ (i j : Fin n) (hij : i ≠ j), SpecialLinearGroup.transvection hij 1 ∈ H := by
    intro i j hij
    by_cases hi : i = h
    · subst hi
      exact hout j hij
    by_cases hj : j = h
    · subst hj
      exact hin i hij
    have hc := SpecialLinearGroup.commutatorElement_transvection hi (Ne.symm hj) hij
      (1 : GaloisField 2 1) 1
    rw [mul_one] at hc
    rw [← hc, commutatorElement_def]
    have h1 := hin i hi
    have h2 := hout j (Ne.symm hj)
    exact H.mul_mem (H.mul_mem (H.mul_mem h1 h2) (H.inv_mem h1)) (H.inv_mem h2)
  rw [eq_top_iff, ← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
    Subgroup.closure_le]
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  rw [TransvectionStruct.toSpecialLinearGroup_mk]
  rcases gf2_eq_zero_or_one c with rfl | rfl
  · rw [SpecialLinearGroup.transvection_coeff_zero]
    exact H.one_mem
  · exact hall i j hij

theorem blk_smul_fst_ne {a b : Fin n} (hab : a ≠ b) :
    blk hab • (Pi.single a 1 : Fin n → GaloisField 2 1) ≠ Pi.single a 1 := by
  rw [blk_smul_fst]
  intro h
  have h1 := congrFun h b
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hab.symm] at h1
  exact one_ne_zero h1

theorem eq_zero_of_blk_pow_smul {a b : Fin n} (hab : a ≠ b) {m : ℕ} (hm : m < 3)
    (h : blk hab ^ m • (Pi.single a 1 : Fin n → GaloisField 2 1) = Pi.single a 1) : m = 0 := by
  interval_cases m
  · rfl
  · rw [pow_one] at h
    exact absurd h (blk_smul_fst_ne hab)
  · rw [pow_two, mul_smul, blk_smul_fst, blk_smul_snd] at h
    have h1 := congrFun h b
    rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab.symm, zero_add] at h1
    exact absurd h1 one_ne_zero

theorem pow_smul_eq_of_smul_eq {g : SL(n, GaloisField 2 1)} {v : Fin n → GaloisField 2 1}
    (h : g • v = v) (m : ℕ) : g ^ m • v = v :=
  MulAction.mem_stabilizer_iff.mp
    (Subgroup.pow_mem _ (MulAction.mem_stabilizer_iff.mpr h) m)

theorem notMem_zpowers_of_smul {p q : SL(n, GaloisField 2 1)} {v : Fin n → GaloisField 2 1}
    (hp : p • v = v) (hq : q • v ≠ v) : q ∉ Subgroup.zpowers p := fun h =>
  hq (MulAction.mem_stabilizer_iff.mp
    ((Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hp) :
      Subgroup.zpowers p ≤ MulAction.stabilizer SL(n, GaloisField 2 1) v) h))

theorem transvection_mem_hyperCent {P : Subgroup SL(n, GaloisField 2 1)} (hP9 : Nat.card P = 9)
    {a b : Fin n} (hab : a ≠ b) (hmem : blk hab ∈ P) {i j : Fin n} (hij : i ≠ j) (hia : i ≠ a)
    (hib : i ≠ b) (hja : j ≠ a) (hjb : j ≠ b) :
    SpecialLinearGroup.transvection hij 1 ∈ hyperCent P :=
  mem_hyperCent_of_commute hP9 hmem (blk_pow_three hab) (blk_ne_one hab)
    (commute_blk_transvection hab hij hia hib hja hjb 1).eq

end Transvection

section Perm

variable {n : ℕ}

theorem gf2_neg_one : (-1 : GaloisField 2 1) = 1 :=
  neg_eq_of_add_eq_zero_left gf2_one_add_one

noncomputable def permSL (σ : Equiv.Perm (Fin n)) : SL(n, GaloisField 2 1) :=
  ⟨σ⁻¹.permMatrix (GaloisField 2 1), by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ⁻¹) with h | h <;> rw [h]
    · simp
    · simp [gf2_neg_one]⟩

theorem permSL_smul_single (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    permSL σ • (Pi.single k 1 : Fin n → GaloisField 2 1) = Pi.single (σ k) 1 := by
  change σ⁻¹.permMatrix (GaloisField 2 1) *ᵥ (Pi.single k 1 : Fin n → GaloisField 2 1) =
    Pi.single (σ k) 1
  rw [Matrix.permMatrix_mulVec]
  ext i
  simp only [Function.comp_apply, Pi.single_apply, Equiv.Perm.inv_eq_iff_eq]

theorem permSL_mul (σ τ : Equiv.Perm (Fin n)) : permSL (σ * τ) = permSL σ * permSL τ := by
  apply SL_ext_smul
  intro k
  rw [mul_smul, permSL_smul_single, permSL_smul_single, permSL_smul_single,
    Equiv.Perm.mul_apply]

theorem permSL_one : permSL (1 : Equiv.Perm (Fin n)) = 1 := by
  apply SL_ext_smul
  intro k
  rw [permSL_smul_single, one_smul, Equiv.Perm.one_apply]

theorem permSL_pow (σ : Equiv.Perm (Fin n)) (m : ℕ) : permSL (σ ^ m) = permSL σ ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, permSL_one]
  | succ m ih => rw [pow_succ, pow_succ, permSL_mul, ih]

theorem permSL_mul_transvection (σ : Equiv.Perm (Fin n)) {i j : Fin n} (hij : i ≠ j)
    (c : GaloisField 2 1) :
    permSL σ * SpecialLinearGroup.transvection hij c =
      SpecialLinearGroup.transvection (σ.injective.ne hij) c * permSL σ := by
  apply SL_ext_smul
  intro k
  rw [mul_smul, mul_smul, permSL_smul_single]
  by_cases hk : k = j
  · subst hk
    rw [SpecialLinearGroup.transvection_smul_single_snd,
      SpecialLinearGroup.transvection_smul_single_snd, smul_add, smul_comm, permSL_smul_single,
      permSL_smul_single]
  · rw [transvection_smul_single_of_ne hij hk,
      transvection_smul_single_of_ne _ (σ.injective.ne hk), permSL_smul_single]

theorem permSL_mul_blk (σ : Equiv.Perm (Fin n)) {a b : Fin n} (hab : a ≠ b) :
    permSL σ * blk hab = blk (σ.injective.ne hab) * permSL σ := by
  have h1 := permSL_mul_transvection σ hab 1
  have h2 := permSL_mul_transvection σ hab.symm 1
  calc permSL σ * blk hab = permSL σ * SpecialLinearGroup.transvection hab 1 *
        SpecialLinearGroup.transvection hab.symm 1 := by rw [blk, mul_assoc]
    _ = SpecialLinearGroup.transvection (σ.injective.ne hab) 1 *
        (permSL σ * SpecialLinearGroup.transvection hab.symm 1) := by rw [h1, mul_assoc]
    _ = blk (σ.injective.ne hab) * permSL σ := by rw [h2, ← mul_assoc, blk]

theorem permSL_conj_blk (σ : Equiv.Perm (Fin n)) {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (hc : σ a = c) (hd : σ b = d) : permSL σ * blk hab * (permSL σ)⁻¹ = blk hcd := by
  subst hc hd
  rw [permSL_mul_blk, mul_inv_cancel_right]

end Perm

theorem statedScalars_subgroupOf_eq_bot {n : ℕ} (H : Subgroup (GL (Fin n) (GaloisField 2 1))) :
    (CFSG.Assembly.LowTwoRank.StatedScalars (Fin n) (GaloisField 2 1)).subgroupOf H = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨g, hg⟩ hgZ
  rw [Subgroup.mem_subgroupOf, CFSG.Assembly.LowTwoRank.StatedScalars, MonoidHom.mem_range]
    at hgZ
  obtain ⟨u, hu⟩ := hgZ
  have hu1 : u = 1 := by
    have : Subsingleton (GaloisField 2 1)ˣ := by
      rw [← Finite.card_le_one_iff_subsingleton, Nat.card_units,
        GaloisField.card 2 1 one_ne_zero]
      norm_num
    exact Subsingleton.elim u 1
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hu, hu1, map_one]
  rfl

theorem center_layer_eq_bot_of_projSL_gf2
    {G : Type} [Group G] [Finite G]
    {A M Q : Subgroup G} (h : Ctx434Core G A M Q) {n : ℕ} (hn : 2 ≤ n)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* projSL n (GaloisField 2 1)) :
    Subgroup.center (layer G) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect (layer G) := h.isQuasisimple.1
  have hodd : Odd (Nat.card (Subgroup.center (layer G))) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_center_layer
    rw [hk]
    exact Odd.pow (by decide)
  let ψ : CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSL n (GaloisField 2 1)) ≃* projSL n (GaloisField 2 1) :=
    (Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
      (MulEquiv.subgroupCongr (PartOne.projImage_statedSL_eq_projSL n _))
  obtain ⟨φ, -, -, hD⟩ :=
    CFSG.SectionRank.EvenCover.even_linear_perfect_odd_cover_map hn hodd (e.trans ψ.symm)
  rw [← hD, statedScalars_subgroupOf_eq_bot, Subgroup.map_bot]

section Transport

variable {S X : Type*} [Group S] [Group X]

theorem mem_hyperCent_map (ψ : S ≃* X) {P : Subgroup S} {x : S} (hx : x ∈ hyperCent P) :
    ψ x ∈ hyperCent (P.map ψ.toMonoidHom) := by
  obtain ⟨R, hRP, hR3, hRx⟩ := hx
  refine ⟨R.map ψ.toMonoidHom, Subgroup.map_mono hRP, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective ψ.injective, Subgroup.card_map_of_injective ψ.injective,
      hR3]
  · rintro _ ⟨r, hr, rfl⟩
    change ψ r * ψ x = ψ x * ψ r
    rw [← map_mul, ← map_mul, hRx r hr]

theorem closure_hyperCent_map (ψ : S ≃* X) {P : Subgroup S}
    (hP : Subgroup.closure (hyperCent P) = ⊤) :
    Subgroup.closure (hyperCent (P.map ψ.toMonoidHom)) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hy : ψ.symm y ∈ Subgroup.closure (hyperCent P) := by
    rw [hP]
    exact Subgroup.mem_top _
  have h1 := Subgroup.mem_map_of_mem ψ.toMonoidHom hy
  rw [MonoidHom.map_closure] at h1
  have h2 : ψ.toMonoidHom (ψ.symm y) = y := ψ.apply_symm_apply y
  rw [h2] at h1
  refine Subgroup.closure_mono ?_ h1
  rintro _ ⟨x, hx, rfl⟩
  exact mem_hyperCent_map ψ hx

theorem gen_of_mulEquiv (ψ : S ≃* X) {k : ℕ}
    (h : ∀ P : Subgroup S, CFSG.Assembly.IsElemAbelian 3 P → Nat.card P = k →
      Subgroup.closure (hyperCent P) = ⊤) :
    ∀ P : Subgroup X, CFSG.Assembly.IsElemAbelian 3 P → Nat.card P = k →
      Subgroup.closure (hyperCent P) = ⊤ := by
  intro P hP hPk
  have hmap : (P.map ψ.symm.toMonoidHom).map ψ.toMonoidHom = P := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id P
    ext x
    simp
  rw [← hmap]
  exact closure_hyperCent_map ψ (h _
    (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ P hP)
    (by rw [Subgroup.card_map_of_injective ψ.symm.injective, hPk]))

end Transport

section Elem

variable {H : Type*} [Group H]

theorem isElemAbelian_zpowers_sup [Finite H] {p q : H} (hp : p ^ 3 = 1) (hp1 : p ≠ 1)
    (hq : q ^ 3 = 1) (hqp : q ∉ Subgroup.zpowers p) (hpq : p * q = q * p) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers p ⊔ Subgroup.zpowers q) ∧
      Nat.card (Subgroup.zpowers p ⊔ Subgroup.zpowers q : Subgroup H) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzp : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers p) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hp,
      _root_.one_zpow]
  have hcomm : ∀ a ∈ Subgroup.zpowers p, a * q = q * a := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left hpq k).eq
  obtain ⟨hab, hcard⟩ := Sec5.isElemAbelian_sup_zpowers hzp hqp hq hcomm
  refine ⟨hab, ?_⟩
  rw [hcard, Nat.card_zpowers, orderOf_eq_prime hp hp1]

theorem mem_hyperCent_of_commute_sup {P : Subgroup H} (hP27 : Nat.card P = 27) {p q x : H}
    (hR : Subgroup.zpowers p ⊔ Subgroup.zpowers q ≤ P)
    (hR9 : Nat.card (Subgroup.zpowers p ⊔ Subgroup.zpowers q : Subgroup H) = 9)
    (hpx : p * x = x * p) (hqx : q * x = x * q) : x ∈ hyperCent P := by
  refine ⟨Subgroup.zpowers p ⊔ Subgroup.zpowers q, hR, by rw [hR9, hP27], fun r hr => ?_⟩
  have hle : Subgroup.zpowers p ⊔ Subgroup.zpowers q ≤ Subgroup.centralizer {x} :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hpx))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hqx))
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hr)

end Elem

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther
