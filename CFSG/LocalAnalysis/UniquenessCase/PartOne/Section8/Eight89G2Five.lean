module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

private abbrev g2f_short : Fin Tag.G2.rank → ℤ := (![0, 1] : Fin 2 → ℤ)

private abbrev g2f_high : Fin Tag.G2.rank → ℤ := (![2, 3] : Fin 2 → ℤ)

private theorem g2f_simpleRootSL2_injective
    {τ : Tag} {K : Type} [Field K]
    (i : Fin τ.rank) : Function.Injective (simpleRootSL2 τ K i) := by
  by_cases hK : ringChar K = 2
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    obtain ⟨l, hl, hgl⟩ :=
      (exceptional_ordinary_rank_one_central_image τ K i).choose_spec.2.2.2.2.2.1 g hg
    have : CharP K 2 := ringChar.eq_iff.mp hK
    have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
    have hl1 : (l : K) = 1 := by
      have h0 : ((l : K) - 1) ^ 2 = 0 := by linear_combination hl - ((l : K) - 1) * h2
      exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0)
    rw [Subgroup.mem_bot]
    ext a b
    simp [hgl, hl1]
  · exact simpleRootSL2_injective hK i

private theorem g2f_rootSL2_injective
    {τ : Tag} {K : Type} [Field K]
    (β : Fin τ.rank → ℤ) : Function.Injective (rootSL2 τ K β) := fun A B h => by
  rw [rootSL2_apply, rootSL2_apply] at h
  exact g2f_simpleRootSL2_injective _ (by simpa using h)

private theorem g2f_sq_eq_one_of_mem_center {K : Type} [Field K] {t : SL2 K}
    (ht : t ∈ Subgroup.center (SL2 K)) : t ^ 2 = 1 := by
  obtain ⟨r, hr, hrt⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 ht
  rw [Fintype.card_fin] at hr
  ext a b
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrt, ← map_pow, hr, map_one,
    Matrix.SpecialLinearGroup.coe_one]

private theorem g2f_card_SL2 {K : Type} [Field K] [Finite K] :
    Nat.card (SL2 K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h1 := Matrix.card_SL_mul_card_units (n := Fin 2) (R := K)
  rw [Matrix.card_GL_field, Nat.card_units, Fin.prod_univ_two, ← Nat.card_eq_fintype_card] at h1
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h1
  have hq : 1 < Nat.card K := Finite.one_lt_card
  apply Nat.eq_of_mul_eq_mul_right (show 0 < Nat.card K - 1 by omega)
  rw [h1]
  have h : Nat.card K ^ 2 - Nat.card K = Nat.card K * (Nat.card K - 1) := by
    rw [Nat.mul_sub_one, sq]
  rw [h]
  ring

private theorem g2f_five_dvd {q : ℕ} (hq : 1 ≤ q) (h : 5 ∣ CFSG.Open.ordG2 q) :
    5 ∣ q * (q ^ 2 - 1) := by
  have hz : ((CFSG.Open.ordG2 q : ℕ) : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  unfold CFSG.Open.ordG2 at hz
  push_cast [Nat.cast_sub h6, Nat.cast_sub h2] at hz
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast [Nat.cast_sub h2]
  have key : ∀ x : ZMod 5, x ^ 6 * (x ^ 6 - 1) * (x ^ 2 - 1) = 0 → x * (x ^ 2 - 1) = 0 := by
    decide
  exact key _ hz

private theorem g2f_core
    {Y : Type} [Group Y] [Finite Y]
    {K : Type} [Field K] (e : Y ≃* adjointGroup .G2 K) {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {s : SL2 K} (hs : orderOf s = p) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y) := by
  have hα : IsRoot .G2 g2f_short := by
    rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .G2)]
    decide
  have hγ : IsRoot .G2 g2f_high := by
    rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .G2)]
    decide
  have hpl : ¬ IsRoot .G2 (g2f_short + g2f_high) := by
    rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .G2)]
    decide
  have hmi : ¬ IsRoot .G2 (g2f_short - g2f_high) := by
    rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .G2)]
    decide
  have h0 : iform g2f_short g2f_high = 0 := by decide
  have hcomm := exceptional_Lang_strongly_orthogonal_root_rank_one_commutation .G2 K hα hγ h0
    hpl hmi
  have hinjα := g2f_rootSL2_injective (K := K) g2f_short
  have hinjγ := g2f_rootSL2_injective (K := K) g2f_high
  have hmemα := (exceptional_Lang_root_rank_one_data .G2 K g2f_short).2.2.2.2.1
  have hmemγ := (exceptional_Lang_root_rank_one_data .G2 K g2f_high).2.2.2.2.1
  set a : ModGL .G2 K := rootSL2 .G2 K g2f_short s
  set b : ModGL .G2 K := rootSL2 .G2 K g2f_high s
  have hao : orderOf a = p := (orderOf_injective _ hinjα s).trans hs
  have hbo : orderOf b = p := (orderOf_injective _ hinjγ s).trans hs
  have hab : a * b = b * a := hcomm a ⟨s, rfl⟩ b ⟨s, rfl⟩
  have hba : ∀ n : ℤ, a ^ n ≠ b := by
    intro n hn
    have hta : rootSL2 .G2 K g2f_short (s ^ n) = b := by rw [map_zpow]; exact hn
    have htc : s ^ n ∈ Subgroup.center (SL2 K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply hinjα
      rw [map_mul, map_mul, hta]
      exact hcomm _ ⟨g, rfl⟩ b ⟨s, rfl⟩
    have hb2 : b ^ 2 = 1 := by
      rw [← hta, ← map_pow, g2f_sq_eq_one_of_mem_center htc, map_one]
    have hdvd := orderOf_dvd_of_pow_eq_one hb2
    rw [hbo] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 hdvd)
  let x : Y := e.symm ⟨a, hmemα s⟩
  let y : Y := e.symm ⟨b, hmemγ s⟩
  have hxo : orderOf x = p := by
    rw [show x = e.symm ⟨a, hmemα s⟩ from rfl, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hao]
  have hyo : orderOf y = p := by
    rw [show y = e.symm ⟨b, hmemγ s⟩ from rfl, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hbo]
  have hxy : Commute x y := by
    refine Commute.map ?_ e.symm.toMonoidHom
    exact Subtype.ext hab
  refine CFSG.GroupTheory.two_le_pRank_of_commute (Subgroup.mem_top x) (Subgroup.mem_top y)
    hxo hyo hxy ?_
  intro hy
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hy
  apply hba n
  have h := congrArg (fun z => ((e z : adjointGroup .G2 K) : ModGL .G2 K)) hn
  simpa [x, y] using h

theorem g2FiveRankCore_holds :
    G2FiveRankCore := by
  intro Y _ _ r f _ hY h5
  have hU : UntwistedChevalleyModel Y .G2 (r ^ f) :=
    (hY.chevalleyExceptionalModel (by decide)).2
  have hcard := CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2 hU
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hU
  let e' : Y ≃* adjointGroup .G2 K := e.trans ((QuotientGroup.quotientMulEquivOfEq
    center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [hcard, ← hK] at h5
  have hSL : 5 ∣ Nat.card (SL2 K) := by
    rw [g2f_card_SL2]
    exact g2f_five_dvd Nat.card_pos h5
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 5 hSL
  exact g2f_core e' (by norm_num) hs

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
