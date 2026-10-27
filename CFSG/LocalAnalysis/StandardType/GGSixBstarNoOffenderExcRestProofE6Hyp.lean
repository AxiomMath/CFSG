module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofE6Plane

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace NoOffRest

open TableBExc.E6Three TableBExc.Three

local instance noOffRestNeZeroRankE6H : NeZero Tag.E6.rank := ⟨by decide⟩

local instance noOffRestFactThreeH : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

section Transfer

theorem fixAllCard_hyp_le_of_words {ι : Type} (A : Subgroup (Model piE7 piE7_pow_three))
    (ω : ι → List (Fin Tag.E6.rank))
    (h : ∀ t, ∃ y ∈ A, modelHomE6 y = (coxeterSystem .E6).wordProd (ω t)) :
    fixAllCard hypPerm modelHomE6 A ≤
      Nat.card {x : Fin Tag.E6.rank → ZMod 3 // ∀ t, adWord .E6 3 (ω t) x = x} := by
  refine Nat.card_le_card_of_injective (fun x => ⟨x.1.1, fun t => ?_⟩) fun x x' hxx => ?_
  · obtain ⟨y, hy, hFy⟩ := h t
    have h1 := congrArg Subtype.val (x.2 y hy)
    rw [coe_hypPerm_apply, hFy, ← adWord_eq_adAct] at h1
    exact h1
  · have h := congrArg Subtype.val hxx
    exact Subtype.ext (Subtype.ext h)

theorem fixCard_hyp_le (y : Model piE7 piE7_pow_three) :
    fixCard hypPerm modelHomE6 y ≤ fixCard (adPerm .E6 3) modelHomE6 y :=
  Nat.card_le_card_of_injective (fun x => ⟨x.1.1, by
    have h1 := congrArg Subtype.val x.2
    rw [coe_hypPerm_apply] at h1
    exact h1⟩) fun x x' hxx => by
    have h := congrArg Subtype.val hxx
    exact Subtype.ext (Subtype.ext h)

theorem modelHomE6_single (i : Fin 3) :
    modelHomE6 (SemidirectProduct.inl (.ofAdd (Pi.single i 1))) =
      (coxeterSystem .E6).wordProd (wordE6G i) := by
  rw [modelHomE6, modelHom_inl, modelN_single, ZMod.val_one, pow_one]
  rfl

theorem adWord_eq_of_adAct_eq {w : WeylGroup .E6} {ω : List (Fin Tag.E6.rank)}
    (hw : w = (coxeterSystem .E6).wordProd ω) {u : Fin Tag.E6.rank → ZMod 3}
    (h : adAct .E6 3 w u = u) : adWord .E6 3 ω u = u := by
  rw [adWord_eq_adAct, ← hw]
  exact h

theorem fixCard_hyp_single (i : Fin 3) :
    fixCard hypPerm modelHomE6 (SemidirectProduct.inl (.ofAdd (Pi.single i 1))) ≤ 3 ^ 3 := by
  refine le_trans (le_of_eq (Nat.card_congr ?_)) (card_fix_hyp_wordE6G i)
  exact
    { toFun := fun x => ⟨x.1.1,
        adWord_eq_of_adAct_eq (modelHomE6_single i) (congrArg Subtype.val x.2), x.1.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.2⟩, Subtype.ext (by
        show adAct .E6 3 (modelHomE6 (SemidirectProduct.inl (.ofAdd (Pi.single i 1)))) x.1 = x.1
        rw [modelHomE6_single, ← adWord_eq_adAct]
        exact x.2.1)⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }

theorem fixCard_hyp_inl_le (v : Multiplicative (Fin 3 → ZMod 3)) (hv : v ≠ 1) :
    fixCard hypPerm modelHomE6 (SemidirectProduct.inl v) ≤ 3 ^ 3 := by
  classical
  by_cases h2 : 2 ≤ (supp v).card
  · exact (fixCard_hyp_le _).trans (fix_supp_E6 v h2)
  obtain ⟨i, hi⟩ : ∃ i, v.toAdd i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (Multiplicative.toAdd.injective (funext hcon))
  have hsupp : supp v = {i} :=
    (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr (mem_supp.mpr hi))
      (by rw [Finset.card_singleton]; omega)).symm
  set a := v.toAdd i with ha
  have hv' : v = .ofAdd (Pi.single i a) := eq_single_of_supp hsupp
  have h12 : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = 2 := by decide
  rcases h12 a hi with h1 | h1
  · rw [hv', h1]
    exact fixCard_hyp_single i
  · have e : SemidirectProduct.inl (.ofAdd (Pi.single i a)) =
        (SemidirectProduct.inl (.ofAdd (Pi.single i 1)) : Model piE7 piE7_pow_three) ^ 2 := by
      rw [← map_pow]
      congr 1
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_ofAdd, toAdd_ofAdd, nsmul_single, h1]
      rfl
    rw [hv', e, fixCard_sq hypPerm modelHomE6 (by rw [← map_pow]; exact
      (by rw [← map_one SemidirectProduct.inl]; congr 1; exact
        CFSG.RankThree.CentralCover.pow_eq_one_of_zmod _))]
    exact fixCard_hyp_single i

end Transfer

section Key

theorem card_mul_fixAllCard_hyp_lt_caseI {A : Subgroup (Model piE7 piE7_pow_three)}
    (hA3 : ∀ y ∈ A, y ^ 3 = 1) (hAc : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y)
    {y : Model piE7 piE7_pow_three} (hyA : y ∈ A) (hy1 : y.right ≠ 1) :
    Nat.card A * fixAllCard hypPerm modelHomE6 A < 3 ^ 5 := by
  classical
  have := finite_model (π := piE7) (hπ := piE7_pow_three)
  obtain ⟨y₁, hy₁A, hy₁⟩ := exists_right_eq_ofAdd_one hyA hy1
  have he : y₁ = ⟨y₁.left, .ofAdd 1⟩ := SemidirectProduct.ext rfl hy₁
  have hv3 : y₁.left * shiftAut piE7 y₁.left * (shiftAut piE7 ^ 2) y₁.left = 1 := by
    rw [← left_cube (hπ := piE7_pow_three), ← he, hA3 y₁ hy₁A, SemidirectProduct.one_left]
  have hw : (Multiplicative.ofAdd ![0, -(y₁.left.toAdd 1), y₁.left.toAdd 0] :
      Multiplicative (Fin 3 → ZMod 3)) * y₁.left *
        (shiftAut piE7 (.ofAdd ![0, -(y₁.left.toAdd 1), y₁.left.toAdd 0]))⁻¹ = 1 := by
    rw [eq_ofAdd_vec3 y₁.left] at hv3
    have h := conj_vec3_E7 _ _ _ hv3
    rw [← eq_ofAdd_vec3 y₁.left] at h
    exact h
  set z₀ : Model piE7 piE7_pow_three :=
    SemidirectProduct.inl (.ofAdd ![0, -(y₁.left.toAdd 1), y₁.left.toAdd 0]) with hz₀
  set A' := A.map (MulAut.conj z₀).toMonoidHom with hA'
  have hcA' : (⟨1, .ofAdd 1⟩ : Model piE7 piE7_pow_three) ∈ A' := ⟨y₁, hy₁A, by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hz₀]
    conv_lhs => rw [he]
    rw [inl_conj_eq, hw]⟩
  have hcard : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj z₀).injective
  have hfix : fixAllCard hypPerm modelHomE6 A' = fixAllCard hypPerm modelHomE6 A :=
    fixAllCard_map_conj hypPerm modelHomE6 A z₀
  have hA'c : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hAc a ha b hb]
  have hle9 : Nat.card A' ≤ 3 * 3 := card_le_of_right_eq hA'c hcA' rfl card_fixShift_E7
  rw [← hcard, ← hfix]
  by_cases hsmall : Nat.card A' ≤ 3
  · have hf : fixAllCard hypPerm modelHomE6 A' ≤ 3 ^ 3 := by
      refine (fixAllCard_le hypPerm modelHomE6 hcA').trans ((fixCard_hyp_le _).trans ?_)
      rw [fixCard_adPerm_eq _ _ _ modelHomE6_c]
      exact card_fix_adWordE6C
    calc Nat.card A' * fixAllCard hypPerm modelHomE6 A' ≤ 3 * 3 ^ 3 := Nat.mul_le_mul hsmall hf
      _ < 3 ^ 5 := by norm_num
  · obtain ⟨z, hzA', hzr, hz1⟩ : ∃ z ∈ A', z.right = 1 ∧ z ≠ 1 := by
      by_contra hcon
      push Not at hcon
      apply hsmall
      have hinj : Function.Injective (fun a : A' => (a : Model piE7 piE7_pow_three).right) := by
        intro a b hab
        have hab' : (a : Model piE7 piE7_pow_three).right = (b : Model piE7 piE7_pow_three).right :=
          hab
        have h1 :
            ((a : Model piE7 piE7_pow_three) * (b : Model piE7 piE7_pow_three)⁻¹).right = 1 := by
          rw [SemidirectProduct.mul_right, SemidirectProduct.inv_right, hab']
          exact mul_inv_cancel _
        have h2 := hcon _ (A'.mul_mem a.2 (A'.inv_mem b.2)) h1
        exact Subtype.ext (mul_inv_eq_one.mp h2)
      calc Nat.card A' ≤ Nat.card (Multiplicative (ZMod 3)) := Nat.card_le_card_of_injective _ hinj
        _ = 3 := by rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    have hzl : z = SemidirectProduct.inl z.left := eq_inl_of_right_eq_one hzr
    have hsh : shiftAut piE7 z.left = z.left := by
      apply shiftAut_eq_of_comm (v := 1)
      have e1 : z = ⟨z.left, 1⟩ := SemidirectProduct.ext rfl hzr
      rw [← e1]
      exact hA'c z hzA' _ hcA'
    have hzl1 : z.left ≠ 1 := fun h => hz1 (by rw [hzl, h, map_one])
    rw [eq_ofAdd_vec3 z.left] at hsh hzl1
    have hf : fixAllCard hypPerm modelHomE6 A' ≤ 3 ^ 2 := by
      rcases eq_of_shiftAut_eq _ _ _ hsh hzl1 with h | h
      · refine (fixAllCard_hyp_le_of_words A' ![wordE6C, nfWordE6 1 1 1] fun t => ?_).trans
          card_fixAll_adWordE6CZ1
        fin_cases t
        · exact ⟨_, hcA', modelHomE6_c⟩
        · refine ⟨z, hzA', ?_⟩
          rw [hzl, eq_ofAdd_vec3 z.left, h, modelHomE6_inl]
          rfl
      · refine (fixAllCard_hyp_le_of_words A' ![wordE6C, nfWordE6 2 2 2] fun t => ?_).trans
          card_fixAll_adWordE6CZ2
        fin_cases t
        · exact ⟨_, hcA', modelHomE6_c⟩
        · refine ⟨z, hzA', ?_⟩
          rw [hzl, eq_ofAdd_vec3 z.left, h, modelHomE6_inl]
          rfl
    calc Nat.card A' * fixAllCard hypPerm modelHomE6 A' ≤ (3 * 3) * 3 ^ 2 :=
          Nat.mul_le_mul hle9 hf
      _ < 3 ^ 5 := by norm_num

theorem card_mul_fixAllCard_hyp_lt_caseII {A : Subgroup (Model piE7 piE7_pow_three)}
    (hA3 : ∀ y ∈ A, y ^ 3 = 1) (hA : A ≠ ⊥) (hI : ∀ y ∈ A, y.right = 1) :
    Nat.card A * fixAllCard hypPerm modelHomE6 A < 3 ^ 5 := by
  classical
  have := finite_model (π := piE7) (hπ := piE7_pow_three)
  set Ninl := (SemidirectProduct.inl :
    Multiplicative (Fin 3 → ZMod 3) →* Model piE7 piE7_pow_three).range with hNinl
  have hAN : A ≤ Ninl := fun y hy => ⟨y.left, (eq_inl_of_right_eq_one (hI y hy)).symm⟩
  have hNcard : Nat.card Ninl = 3 ^ 3 := card_range_inl
  obtain ⟨⟨y, hyA⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hyl : y = SemidirectProduct.inl y.left := eq_inl_of_right_eq_one (hI y hyA)
  have hyl1 : y.left ≠ 1 := fun h => hy1' (by rw [hyl, h, map_one])
  by_cases hsmall : Nat.card A ≤ 3
  · have hf : fixAllCard hypPerm modelHomE6 A ≤ 3 ^ 3 := by
      refine (fixAllCard_le hypPerm modelHomE6 hyA).trans ?_
      rw [hyl]
      exact fixCard_hyp_inl_le _ hyl1
    calc Nat.card A * fixAllCard hypPerm modelHomE6 A ≤ 3 * 3 ^ 3 := Nat.mul_le_mul hsmall hf
      _ < 3 ^ 5 := by norm_num
  have hdvd : Nat.card A ∣ 3 ^ 3 := hNcard ▸ Subgroup.card_dvd_of_le hAN
  obtain ⟨k, hk, hkA⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  by_cases hk3 : k = 3
  · subst hk3
    have hAeq : A = Ninl := Subgroup.eq_of_le_of_card_ge hAN (by rw [hkA, hNcard])
    have hf : fixAllCard hypPerm modelHomE6 A ≤ 3 ^ 1 := by
      refine (fixAllCard_hyp_le_of_words A ![wordE6G0, wordE6G1, wordE6G2] fun t => ?_).trans
        card_fixAll_adWordE6N
      refine ⟨SemidirectProduct.inl (.ofAdd (Pi.single t 1)), by rw [hAeq]; exact ⟨_, rfl⟩, ?_⟩
      rw [modelHomE6_single]
      rfl
    calc Nat.card A * fixAllCard hypPerm modelHomE6 A ≤ 3 ^ 3 * 3 ^ 1 :=
          Nat.mul_le_mul hkA.le hf
      _ < 3 ^ 5 := by norm_num
  have hA9 : Nat.card A ≤ 3 ^ 2 := hkA ▸ Nat.pow_le_pow_right (by norm_num) (by omega)
  have hzp : Nat.card (Subgroup.zpowers y) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) (hA3 y hyA)
  obtain ⟨y', hy'A, hy'⟩ : ∃ y' ∈ A, y' ∉ Subgroup.zpowers y := by
    by_contra hcon
    push Not at hcon
    exact hsmall ((Subgroup.card_le_of_le hcon).trans hzp)
  have hy'l : y' = SemidirectProduct.inl y'.left := eq_inl_of_right_eq_one (hI y' hy'A)
  have hu : (Multiplicative.ofAdd ![y.left.toAdd 0, y.left.toAdd 1, y.left.toAdd 2] :
      Multiplicative (Fin 3 → ZMod 3)) ≠ 1 := by
    rw [← eq_ofAdd_vec3]
    exact hyl1
  have hu' : ∀ e : Fin 3,
      (Multiplicative.ofAdd ![y'.left.toAdd 0, y'.left.toAdd 1, y'.left.toAdd 2] :
        Multiplicative (Fin 3 → ZMod 3)) ≠
      (Multiplicative.ofAdd ![y.left.toAdd 0, y.left.toAdd 1, y.left.toAdd 2]) ^ (e : ℕ) := by
    intro e he
    rw [← eq_ofAdd_vec3, ← eq_ofAdd_vec3] at he
    apply hy'
    refine ⟨((e : ℕ) : ℤ), ?_⟩
    show y ^ ((e : ℕ) : ℤ) = y'
    rw [zpow_natCast, hy'l, he, map_pow, ← hyl]
  obtain ⟨j, ⟨n, m, hnm⟩, ⟨n', m', hnm'⟩⟩ := exists_planeGen _ _ _ _ _ _ hu hu'
  rw [← eq_ofAdd_vec3, ← eq_ofAdd_vec3] at hnm hnm'
  have hmem : ∀ (g : Fin 3 → ZMod 3) (a b : Fin 3),
      Multiplicative.ofAdd g = y.left ^ (a : ℕ) * y'.left ^ (b : ℕ) →
        SemidirectProduct.inl (Multiplicative.ofAdd g) ∈ A := by
    intro g a b hg
    rw [hg, map_mul, map_pow, map_pow, ← hyl, ← hy'l]
    exact A.mul_mem (A.pow_mem hyA _) (A.pow_mem hy'A _)
  have hf : fixAllCard hypPerm modelHomE6 A ≤ 3 ^ 2 := by
    refine (fixAllCard_hyp_le_of_words A (planeWord j) fun t => ?_).trans (card_fix_planeWord j)
    fin_cases t
    · exact ⟨_, hmem _ n m hnm, by rw [modelHomE6_inl]; rfl⟩
    · exact ⟨_, hmem _ n' m' hnm', by rw [modelHomE6_inl]; rfl⟩
  calc Nat.card A * fixAllCard hypPerm modelHomE6 A ≤ 3 ^ 2 * 3 ^ 2 := Nat.mul_le_mul hA9 hf
    _ < 3 ^ 5 := by norm_num

theorem card_mul_fixAllCard_hyp_lt {A : Subgroup (Model piE7 piE7_pow_three)}
    (hA3 : ∀ y ∈ A, y ^ 3 = 1) (hAc : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y) (hA : A ≠ ⊥) :
    Nat.card A * fixAllCard hypPerm modelHomE6 A < 3 ^ 5 := by
  by_cases hI : ∃ y ∈ A, y.right ≠ 1
  · obtain ⟨y, hyA, hy1⟩ := hI
    exact card_mul_fixAllCard_hyp_lt_caseI hA3 hAc hyA hy1
  · push Not at hI
    exact card_mul_fixAllCard_hyp_lt_caseII hA3 hA hI

end Key

section Weyl

theorem noOffender_hypE6_sylow (A : Subgroup (WeylGroup .E6)) (hAS : A ≤ modelHomE6.range)
    (hA : IsElemAbelian 3 A) (hA1 : A ≠ ⊥) :
    Nat.card A * Nat.card {x : hypE6 // ∀ a ∈ A, hypPerm a x = x} < 3 ^ 5 :=
  card_mul_card_fix_lt_of_model hypPerm modelHomE6 modelHomE6_injective
    (fun _ h3 hc h1 => card_mul_fixAllCard_hyp_lt h3 hc h1) hAS hA hA1


theorem actNoOffender_hypPerm_E6 : ActNoOffender hypPerm 3 := by
  refine actNoOffender_of_sylow Nat.prime_three (S := modelHomE6.range) ?_
    fun A hAS hA hA1 => ?_
  · rw [NoOffExc.index_eq_of_card card_range_modelHomE6 NoOffExc.card_weyl_E6
      (show 81 * 640 = 51840 by norm_num) (by norm_num)]
    norm_num
  · rw [card_hypE6]
    exact noOffender_hypE6_sylow A hAS hA hA1

theorem adAct_pow_three_eq {p : ℕ} {τ : Tag} {w : WeylGroup τ} {x : Fin τ.rank → ZMod p}
    (hwy : adAct τ p w (adAct τ p w x - x) = adAct τ p w x - x) (h3 : (3 : ZMod p) = 0) :
    adAct τ p (w ^ 3) x = x := by
  set y := adAct τ p w x - x with hydef
  have hy : adAct τ p w x = x + y := by rw [hydef, add_sub_cancel]
  have e2 : adAct τ p w (adAct τ p w x) = x + y + y := by rw [hy, adAct_add, hy, hwy]
  have e3 : adAct τ p w (adAct τ p w (adAct τ p w x)) = x + y + y + y := by
    rw [e2, adAct_add, adAct_add, hy, hwy]
  rw [pow_three, adAct_mul, adAct_mul, e3]
  funext i
  simp only [Pi.add_apply]
  linear_combination y i * h3

theorem hypPerm_injective : Function.Injective hypPerm := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have hfix : ∀ x ∈ hypE6, adAct .E6 3 w x = x := fun x hx =>
    congrArg Subtype.val (Equiv.ext_iff.mp hw ⟨x, hx⟩)
  have hw3 : w ^ 3 = 1 := by
    refine eq_one_of_adAct (p := 3) (by norm_num) fun x => ?_
    have hy : adAct .E6 3 w x - x ∈ hypE6 :=
      mem_hypE6.mpr ((kDotP_sub _ _).trans (by rw [kDot_adAct]; exact sub_self _))
    exact adAct_pow_three_eq (hfix _ hy) (by decide)
  by_contra hw1
  have hord : orderOf w = 3 := orderOf_eq_prime hw3 hw1
  have hA : IsElemAbelian 3 (Subgroup.zpowers w) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨k, hk⟩ := a.2
      obtain ⟨l, hl⟩ := b.2
      show (a : WeylGroup .E6) * b = b * a
      rw [← hk, ← hl]
      exact zpow_mul_comm w k l
    · obtain ⟨k, rfl⟩ := ha
      calc (w ^ k) ^ 3 = (w ^ 3) ^ k := by
            rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast w 3, ← zpow_mul, mul_comm]
        _ = 1 := by rw [hw3, one_zpow]
  have hA1 : Subgroup.zpowers w ≠ ⊥ := fun h => hw1 (Subgroup.zpowers_eq_bot.mp h)
  have h := actNoOffender_hypPerm_E6 _ hA hA1
  have hall : Nat.card {x : hypE6 // ∀ a ∈ Subgroup.zpowers w, hypPerm a x = x} =
      Nat.card hypE6 := by
    refine Nat.card_congr (Equiv.subtypeUnivEquiv fun x => ?_)
    rintro _ ⟨k, rfl⟩
    rw [map_zpow, hw, one_zpow]
    rfl
  rw [hall, Nat.card_zpowers, hord] at h
  omega

end Weyl


end NoOffRest

end CFSG.StandardType
