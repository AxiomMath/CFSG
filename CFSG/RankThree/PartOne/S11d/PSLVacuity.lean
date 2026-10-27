module

public import CFSG.RankThree.PartOne.S11d.PSLRankTwoTorus
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
public import CFSG.RankThree.PartOne.TCX.RankInterface
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.RankThree.PartOne.TCX.Interface

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Blueprint CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix
open CFSG.Assembly.LowTwoRank (StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized)

section Arith

theorem dvd_pow_sub_one_iff_of_eq_pow {p q Q : ℕ} (hp : p.Prime) (hq : 0 < q) (hQ : Q = q ^ p)
    (j : ℕ) : p ∣ Q ^ j - 1 ↔ p ∣ q ^ j - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : Q ≡ q [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff, hQ]
    push_cast
    exact ZMod.pow_card _
  have h2 : Q ^ j ≡ q ^ j [MOD p] := h1.pow j
  have hQj : 1 ≤ Q ^ j := Nat.one_le_pow _ _ (by rw [hQ]; exact pow_pos hq _)
  have hqj : 1 ≤ q ^ j := Nat.one_le_pow _ _ hq
  rw [← (Nat.modEq_iff_dvd' hQj), ← (Nat.modEq_iff_dvd' hqj)]
  exact ⟨fun h => h.trans h2, fun h => h.trans h2.symm⟩

theorem dvd_pow_pred_sub_one {p q : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q) : p ∣ q ^ (p - 1) - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hq : (q : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  have h1 : ((q : ZMod p)) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hq
  have hq1 : 1 ≤ q ^ (p - 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (by
    rintro rfl
    exact hpq (dvd_zero p)))
  rw [← (Nat.modEq_iff_dvd' hq1)]
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  exact h1.symm

end Arith

section Fixed

variable {T : Type} [Group T]

theorem center_eq_bot_of_nonLocalized {E : Subgroup T} (hNL : NonLocalized E) :
    Subgroup.center ↥E = ⊥ := by
  by_contra hne
  let Z : Subgroup T := (Subgroup.center ↥E).map E.subtype
  have hZne : Z ≠ ⊥ := fun h =>
    hne ((Subgroup.map_eq_bot_iff_of_injective _ E.subtype_injective).mp h)
  have hsolv : Group.IsSolvable ↥Z := by
    refine Group.isSolvable_of_comm ?_
    rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    show (a : T) * b = b * a
    have := (Subgroup.mem_center_iff.mp ha) b
    exact congrArg Subtype.val this.symm
  refine hNL Z hZne hsolv (le_normalizer_of_conj_mem E Z ?_)
  rintro x hx _ ⟨c, hc, rfl⟩
  have := (Subgroup.mem_center_iff.mp hc) ⟨x, hx⟩
  refine ⟨c, hc, ?_⟩
  show (c : T) = x * c * x⁻¹
  have h2 : (⟨x, hx⟩ : E) * c = c * ⟨x, hx⟩ := this
  have h3 : (x : T) * c = c * x := congrArg Subtype.val h2
  rw [h3, mul_inv_cancel_right]

theorem exists_fixRes_equiv_projectiveSL [Finite T] {n f₀ : ℕ} {α : MulAut T}
    (hNL : NonLocalized (fixRes α)) (hX : FixModel .PSL n f₀ α) :
    2 ≤ n ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ f₀ ∧
      Nonempty (↥(fixRes α) ≃* projectiveSL n k) := by
  have hZ : Subgroup.center ↥(fixRes α) = ⊥ := center_eq_bot_of_nonLocalized hNL
  rcases hX with h | ⟨ht, -⟩
  · have hM : LieModel ↥(fixRes α) .PSL n 2 f₀ :=
      lieModel_of_mulEquiv (centerQuotientEquivSelf hZ) h
    obtain ⟨hadm, k, _, _, hk, ⟨e0⟩⟩ := (lieModel_classical_iff (by decide)).mp hM
    let e : ↥(fixRes α) ≃* projectiveSL n k :=
      (e0.trans (projectiveSpecialLinearGroupEquivStatedProj n k).symm).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL n k)
    exact ⟨hadm.2.2.1, k, inferInstance, inferInstance, hk, ⟨e⟩⟩
  · exact absurd ht (by decide)

theorem false_of_rank_two_in_fixSub {p : ℕ} {α : MulAut T} (hαp : α ^ p = 1)
    (hαinn : α ∉ innerAut T) (hLR : LocalRankAut p T α) {X : Type} [Group X] (ψ : X →* T)
    (hψ : Function.Injective ψ) (hfix : ∀ x, α (ψ x) = ψ x) {R U : Subgroup X}
    (hRe : CFSG.IsElementaryAbelian p R) (hRc : Nat.card R = p ^ 2) (hU1 : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) (hN : R ≤ Subgroup.normalizer (U : Set X)) : False := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rankTwoCfg_map ψ R U (fun x _ y _ h => hψ h)
    (fun x _ h => hψ (by simpa using h)) hRe hRc hU1 hU2 hN
  refine hLR hαp hαinn (R.map ψ) h1 h2 ?_ (U.map ψ) h3 h4 ?_ h5
  · rintro _ ⟨x, -, rfl⟩
    exact hfix x
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, (hfix x).symm⟩

end Fixed

theorem psl_false (hF : TagFixedFacts .PSL) {T : Type} [Group T] [Finite T] {p n f₀ : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hrank : LocalRankLeTwo p T) (h2 : 2 ≤ CFSG.pRank p T)
    (hf₀ : 1 ≤ f₀) (hM : LieModel T .PSL n 2 (p * f₀)) (α : MulAut T) (hαp : α ^ p = 1)
    (hαinn : α ∉ innerAut T) (hLR : LocalRankAut p T α) (hFix : FixModel .PSL n f₀ α) :
    False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hFF : FixedFacts p α := hF T p hp hp5 hrank n f₀ hf₀ hM α hαp hαinn hLR hFix α hαp hαinn
    hLR ⟨1, fun h => by
      have := Int.eq_one_of_dvd_one (by positivity) h
      omega, by
      rw [zpow_one, mul_inv_cancel]
      exact (innerAut T).one_mem⟩
  have hC : StatedClassicalModel T .PSL n 2 (p * f₀) := (lieModel_classical_iff (by decide)).mp hM
  have hn2 : 2 ≤ n := hC.1.2.2.1
  by_cases hn2' : n = 2
  · subst hn2'
    have h1 := CFSG.QuasithinUnique.Id2519.pRank_le_one_psl_two_even hC hp hp2
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top] at h1
    omega
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  let e : T ≃* projectiveSL n K :=
    (e0.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
  have : Fintype K := Fintype.ofFinite K
  have hcharK : CharP K 2 := charP_of_card_eq_prime_pow (f := p * f₀) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have hrkT : 2 ≤ CFSG.pRank p (projectiveSL n K) := by
    rw [← pRank_eq_of_mulEquiv_of_one_lt hp.one_lt e]
    exact h2
  obtain ⟨-, k₀, _, _, hk₀, ⟨eE⟩⟩ := exists_fixRes_equiv_projectiveSL hFF.nonLocalized hFix
  have : Fintype k₀ := Fintype.ofFinite k₀
  have hchark : CharP k₀ 2 := charP_of_card_eq_prime_pow (f := f₀) (by
    rw [← Nat.card_eq_fintype_card, hk₀])
  have hQq : Nat.card K = Nat.card k₀ ^ p := by
    rw [hK, hk₀, ← pow_mul, mul_comm]
  have hq0 : 0 < Nat.card k₀ := Nat.card_pos
  have hconf : ∃ R U : Subgroup (projectiveSL n k₀), CFSG.IsElementaryAbelian p R ∧
      Nat.card R = p ^ 2 ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      R ≤ Subgroup.normalizer (U : Set (projectiveSL n k₀)) := by
    by_cases hpk : p ∣ Nat.card k₀ˣ
    · exact exists_rank_two_unip_psl_torus hn3 hp (by omega) hpk
    · have hpk1 : ¬ p ∣ Nat.card k₀ - 1 := by
        rwa [Nat.card_units] at hpk
      have hpKK : ¬ p ∣ Nat.card Kˣ := by
        rw [Nat.card_units]
        intro h
        apply hpk1
        have := (dvd_pow_sub_one_iff_of_eq_pow hp hq0 hQq 1).mp (by simpa using h)
        simpa using this
      have hex : ∃ j : ℕ, 1 ≤ j ∧ p ∣ Nat.card K ^ j - 1 := by
        refine ⟨p - 1, by omega, ?_⟩
        rw [dvd_pow_sub_one_iff_of_eq_pow hp hq0 hQq]
        exact dvd_pow_pred_sub_one hp (not_dvd_card_of_charTwo hp hp2)
      have he := Nat.find_spec hex
      have hmin : ∀ j : ℕ, 1 ≤ j → p ∣ Nat.card K ^ j - 1 → Nat.find hex ≤ j :=
        fun j hj hd => Nat.find_min' hex ⟨hj, hd⟩
      have h2e : 2 * Nat.find hex ≤ n :=
        two_mul_le_of_pRank_projectiveSL hp hp2 hpKK hmin hrkT
      have hdq : p ∣ Nat.card k₀ ^ Nat.find hex - 1 :=
        (dvd_pow_sub_one_iff_of_eq_pow hp hq0 hQq _).mp he.2
      exact exists_rank_two_unip_psl hp hpk he.1 hdq h2e
  obtain ⟨R, U, hRe, hRc, hU1, hU2, hN⟩ := hconf
  let ψ : projectiveSL n k₀ →* T := (fixRes α).subtype.comp eE.symm.toMonoidHom
  have hψ : Function.Injective ψ := (fixRes α).subtype_injective.comp eE.symm.injective
  have hfix : ∀ x, α (ψ x) = ψ x := fun x =>
    mem_fixSub.mp (fixRes_le_fixSub α (eE.symm x).2)
  exact false_of_rank_two_in_fixSub hαp hαinn hLR ψ hψ hfix hRe hRc hU1 hU2 hN

end CFSG.RankThree.PartOne

namespace CFSG.RankThree.PartOne.TCX

open CFSG.RankThree.PartOne.FieldFix

theorem threeCompT_PSL (hF : TagFixedFacts .PSL) : ThreeCompT .PSL := by
  intro T _ _ p hp hp5 hrank h2 n f₀ hf₀ hM α hαp hαinn hLR hFix x _ _ _
  exact (psl_false hF hp hp5 hrank h2 hf₀ hM α hαp hαinn hLR hFix).elim

theorem fixedRankT_PSL (hF : TagFixedFacts .PSL) : FixedRankT .PSL := by
  intro T _ _ p hp hp5 hrank h2 n f₀ hf₀ hM α hαp hαinn hLR hFix
  exact (psl_false hF hp hp5 hrank h2 hf₀ hM α hαp hαinn hLR hFix).elim

end CFSG.RankThree.PartOne.TCX
