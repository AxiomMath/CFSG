module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofE6Ad
public import CFSG.LocalAnalysis.StandardType.GGTableBE6ThreeEndCount
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.ComponentClassification.ThompsonAB

public section

namespace CFSG.StandardType.E6NonToralThree

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc.Three TableBExc.E6Three

open CFSG.ComponentClassification.ThompsonAB

private noncomputable def adActMulAut (w : WeylGroup .E6) :
    MulAut (Multiplicative (Fin Tag.E6.rank → ZMod 3)) where
  toFun x := Multiplicative.ofAdd (adAct .E6 3 w x.toAdd)
  invFun x := Multiplicative.ofAdd (adAct .E6 3 w⁻¹ x.toAdd)
  left_inv x := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd]
    rw [← adAct_mul, inv_mul_cancel, adAct_one]
  right_inv x := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd]
    rw [← adAct_mul, mul_inv_cancel, adAct_one]
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd, toAdd_mul, Pi.add_apply]
    exact NoOffRest.adAct_add w x.toAdd y.toAdd

private theorem adActMulAut_apply (w : WeylGroup .E6)
    (x : Multiplicative (Fin Tag.E6.rank → ZMod 3)) :
    adActMulAut w x = Multiplicative.ofAdd (adAct .E6 3 w x.toAdd) := rfl

private noncomputable def adActHom :
    WeylGroup .E6 →* MulAut (Multiplicative (Fin Tag.E6.rank → ZMod 3)) where
  toFun := adActMulAut
  map_one' := by
    ext x
    apply Multiplicative.toAdd.injective
    simp [adActMulAut_apply, adAct_one]
  map_mul' w w' := by
    ext x
    apply Multiplicative.toAdd.injective
    simp [adActMulAut_apply, adAct_mul]

private def centralFix (A : Subgroup (WeylGroup .E6)) : Subgroup (WeylGroup .E6) where
  carrier := {w | (∀ a ∈ A, w * a = a * w) ∧
    ∀ x, (∀ a ∈ A, adAct .E6 3 a x = x) → adAct .E6 3 w x = x}
  one_mem' := by
    refine ⟨by intro a ha; group, ?_⟩
    intro x _
    exact adAct_one x
  mul_mem' := by
    rintro w w' ⟨hw1, hw2⟩ ⟨hw'1, hw'2⟩
    refine ⟨?_, ?_⟩
    · intro a ha
      calc (w * w') * a = w * (w' * a) := by group
        _ = w * (a * w') := by rw [hw'1 a ha]
        _ = (w * a) * w' := by group
        _ = (a * w) * w' := by rw [hw1 a ha]
        _ = a * (w * w') := by group
    · intro x hx
      rw [adAct_mul, hw'2 x hx]
      exact hw2 x hx
  inv_mem' := by
    rintro w ⟨hw1, hw2⟩
    refine ⟨?_, ?_⟩
    · intro a ha
      calc w⁻¹ * a = w⁻¹ * (a * w) * w⁻¹ := by group
        _ = w⁻¹ * (w * a) * w⁻¹ := by rw [hw1 a ha]
        _ = a * w⁻¹ := by group
    · intro x hx
      have hxw : adAct .E6 3 w x = x := hw2 x hx
      have h2 : adAct .E6 3 w⁻¹ (adAct .E6 3 w x) = x := by
        rw [← adAct_mul, inv_mul_cancel, adAct_one]
      rwa [hxw] at h2

private theorem eq_one_of_mem_centralFix_of_coprime (A : Subgroup (WeylGroup .E6))
    (hA : IsElemAbelian 3 A) {w : WeylGroup .E6} (hw : w ∈ centralFix A)
    (hcop : Nat.Coprime (orderOf w) 3) : w = 1 := by
  have hVp : IsPGroup 3 (Multiplicative (Fin Tag.E6.rank → ZMod 3)) := by
    apply IsPGroup.of_card (n := 6)
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin,
      show Tag.E6.rank = 6 by decide]
  have hAp : IsPGroup 3 A := TableB.isPGroup_of_isElemAbelian hA
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let action : A →* MulAut (Multiplicative (Fin Tag.E6.rank → ZMod 3)) :=
    adActHom.comp A.subtype
  have hcomm : ∀ element : A, Commute (adActMulAut w) (action element) := by
    intro element
    have h1 : w * (element : WeylGroup .E6) = (element : WeylGroup .E6) * w :=
      hw.1 element element.2
    have h2 := congrArg adActHom h1
    change adActHom w * action element = action element * adActHom w
    simpa [action, MonoidHom.comp_apply, map_mul] using h2
  have hfixed : ∀ member : Multiplicative (Fin Tag.E6.rank → ZMod 3),
      (∀ element : A, action element member = member) → adActMulAut w member = member := by
    intro member hmem
    obtain ⟨x, rfl⟩ := Multiplicative.ofAdd.surjective member
    apply Multiplicative.ofAdd.injective
    simp only [adActMulAut_apply, toAdd_ofAdd]
    apply hw.2 x
    intro a ha
    have h := congrArg Multiplicative.toAdd (hmem ⟨a, ha⟩)
    change Multiplicative.toAdd (adActMulAut a (Multiplicative.ofAdd x)) = x at h
    simpa [adActMulAut_apply] using h
  have hpower : (adActMulAut w) ^ (orderOf w) = 1 := by
    have h := congrArg adActHom (pow_orderOf_eq_one w)
    rw [map_pow, map_one] at h
    change (adActMulAut w) ^ orderOf w = 1
    exact h
  have haut : adActMulAut w = 1 :=
    coprime_eq_one 3 hVp hAp action (adActMulAut w) hcomm hfixed (orderOf w) hpower hcop
  refine NoOffRest.eq_one_of_adAct (p := 3) (by norm_num) ?_
  intro x
  have h := congrArg (fun f : MulAut (Multiplicative (Fin Tag.E6.rank → ZMod 3)) =>
    f (Multiplicative.ofAdd x)) haut
  simpa [adActMulAut_apply] using h

private theorem orderOf_eq_pow_three_of_mem_centralFix (A : Subgroup (WeylGroup .E6))
    (hA : IsElemAbelian 3 A) {w : WeylGroup .E6} (hw : w ∈ centralFix A) :
    ∃ k, orderOf w = 3 ^ k := by
  have hne : orderOf w ≠ 0 := (orderOf_pos w).ne'
  have huniq : ∀ {d : ℕ}, Nat.Prime d → d ∣ orderOf w → d = 3 := by
    intro d hd hdvd
    by_contra hd3
    let y := w ^ (orderOf w / d)
    have hyo : orderOf y = d := orderOf_pow_orderOf_div hne hdvd
    have hyX : y ∈ centralFix A := Subgroup.pow_mem (centralFix A) hw _
    have hcop : Nat.Coprime (orderOf y) 3 := by
      rw [hyo]
      exact (Nat.coprime_primes hd Nat.prime_three).mpr hd3
    have h1 : y = 1 := eq_one_of_mem_centralFix_of_coprime A hA hyX hcop
    rw [h1] at hyo
    rw [orderOf_one] at hyo
    exact hd.one_lt.ne' hyo.symm
  exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hne fun hd hdvd => huniq hd hdvd⟩

private theorem exists_pow_three_mem_of_ne (A : Subgroup (WeylGroup .E6))
    (hpow : ∀ x ∈ centralFix A, ∃ k, orderOf x = 3 ^ k)
    {x : WeylGroup .E6} (hx : x ∈ centralFix A) (hxA : x ∉ A) :
    ∃ y ∈ centralFix A, y ∉ A ∧ y ^ 3 ∈ A := by
  classical
  obtain ⟨k, hk⟩ := hpow x hx
  have hxne : x ≠ 1 := fun h => hxA (h ▸ A.one_mem)
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, pow_zero] at hk
      exact absurd hk (by rw [orderOf_eq_one_iff]; exact hxne)
    · exact h
  let p : ℕ → Prop := fun j => 0 < j ∧ x ^ 3 ^ j ∈ A
  have hex : ∃ j, p j :=
    ⟨k, hkpos, by rw [← hk, pow_orderOf_eq_one]; exact A.one_mem⟩
  let j := Nat.find hex
  have hj : p j := Nat.find_spec hex
  have hjpos : 0 < j := hj.1
  refine ⟨x ^ 3 ^ (j - 1), Subgroup.pow_mem (centralFix A) hx _, ?_, ?_⟩
  · intro hyA
    rcases Nat.eq_or_lt_of_le hjpos with h1 | h1
    · rw [← h1] at hyA
      exact hxA (by simpa using hyA)
    · exact Nat.find_min hex (by omega) ⟨by omega, hyA⟩
  · rw [← pow_mul]
    have h3 : 3 ^ (j - 1) * 3 = 3 ^ j := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h3]
    exact hj.2

private theorem isPGroup_sup_zpowers (A : Subgroup (WeylGroup .E6)) (hA : IsElemAbelian 3 A)
    {y : WeylGroup .E6} (hycomm : ∀ a ∈ A, y * a = a * y) (hy3 : y ^ 3 ∈ A) :
    IsPGroup 3 ↥(A ⊔ Subgroup.zpowers y) := by
  have hy9 : y ^ 9 = 1 := by
    have h : (y ^ 3) ^ 3 = 1 := hA.2 (y ^ 3) hy3
    rw [← pow_mul] at h
    rwa [show (3 : ℕ) * 3 = 9 by norm_num] at h
  have hzy : IsPGroup 3 (Subgroup.zpowers y) := by
    apply IsPGroup.of_card_dvd_pow (n := 2)
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hy9
  have hcent : A ≤ Subgroup.centralizer ({y} : Set (WeylGroup .E6)) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hycomm a ha).symm
  have hnorm : A ≤ Subgroup.normalizer (Subgroup.zpowers y : Set (WeylGroup .E6)) := by
    calc A ≤ Subgroup.centralizer ({y} : Set (WeylGroup .E6)) := hcent
      _ ≤ Subgroup.normalizer ({y} : Set (WeylGroup .E6)) :=
        Subgroup.centralizer_le_normalizer {y}
      _ ≤ Subgroup.normalizer (Subgroup.closure {y}) :=
        Subgroup.normalizer_le_normalizer_closure {y}
      _ = Subgroup.normalizer (Subgroup.zpowers y : Set (WeylGroup .E6)) := by
        rw [Subgroup.zpowers_eq_closure]
  exact IsPGroup.to_sup_of_normal_right' (TableB.isPGroup_of_isElemAbelian hA) hzy hnorm

private theorem isMulCommutative_sup_zpowers (A : Subgroup (WeylGroup .E6))
    (hA : IsElemAbelian 3 A) {y : WeylGroup .E6} (hycomm : ∀ a ∈ A, y * a = a * y) :
    IsMulCommutative ↥(A ⊔ Subgroup.zpowers y) := by
  have hB : A ⊔ Subgroup.zpowers y =
      Subgroup.closure ((A : Set (WeylGroup .E6)) ∪ {y}) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.zpowers_eq_closure]
  rw [hB]
  refine Subgroup.isMulCommutative_closure ?_
  intro u hu v hv _
  rw [Set.mem_union, Set.mem_singleton_iff] at hu hv
  rcases hu with hu | hu
  · rcases hv with hv | hv
    · exact TableB.IsElemAbelian.comm hA hu hv
    · rw [hv]
      exact (hycomm u hu).symm
  · rcases hv with hv | hv
    · rw [hu]
      exact hycomm v hv
    · rw [hu, hv]

private theorem adAct_eq_of_mem_closure {s : Set (WeylGroup .E6)}
    {x : Fin Tag.E6.rank → ZMod 3} (h : ∀ g ∈ s, adAct .E6 3 g x = x)
    {g : WeylGroup .E6} (hg : g ∈ Subgroup.closure s) : adAct .E6 3 g x = x := by
  induction hg using Subgroup.closure_induction with
  | mem y hy => exact h y hy
  | one => exact adAct_one x
  | mul y z _ _ ihy ihz => rw [adAct_mul, ihz, ihy]
  | inv y _ ihy =>
      have h2 : adAct .E6 3 y⁻¹ (adAct .E6 3 y x) = x := by
        rw [← adAct_mul, inv_mul_cancel, adAct_one]
      rwa [ihy] at h2

private theorem card_fix_sup_zpowers (A : Subgroup (WeylGroup .E6)) {y : WeylGroup .E6}
    (hyfix : ∀ x : Fin Tag.E6.rank → ZMod 3,
      (∀ a ∈ A, adAct .E6 3 a x = x) → adAct .E6 3 y x = x) :
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
      ∀ b ∈ A ⊔ Subgroup.zpowers y, adAct .E6 3 b x = x} =
      Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
        ∀ a ∈ A, adAct .E6 3 a x = x} := by
  have hB : A ⊔ Subgroup.zpowers y =
      Subgroup.closure ((A : Set (WeylGroup .E6)) ∪ {y}) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.zpowers_eq_closure]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  constructor
  · intro hb a ha
    exact hb a (Subgroup.mem_sup_left ha)
  · intro ha b hb
    rw [hB] at hb
    refine adAct_eq_of_mem_closure (s := (A : Set (WeylGroup .E6)) ∪ {y}) ?_ hb
    rintro g (hga | hga)
    · exact ha g hga
    · rw [Set.mem_singleton_iff] at hga
      subst hga
      exact hyfix x ha

private theorem card_le_card_sup_zpowers (A : Subgroup (WeylGroup .E6)) {y : WeylGroup .E6}
    (hy3 : y ^ 3 ∈ A) (hyA : y ∉ A)
    (hcommB : IsMulCommutative ↥(A ⊔ Subgroup.zpowers y)) :
    3 * Nat.card A ≤ Nat.card ↥(A ⊔ Subgroup.zpowers y) := by
  classical
  let B := A ⊔ Subgroup.zpowers y
  have hAB : A ≤ B := le_sup_left
  let AB : Subgroup B := A.subgroupOf B
  haveI : IsMulCommutative ↥B := hcommB
  haveI : AB.Normal := Subgroup.normal_of_comm AB
  let yB : B := ⟨y, Subgroup.mem_sup_right (Subgroup.mem_zpowers y)⟩
  let q : B →* B ⧸ AB := QuotientGroup.mk' AB
  have hqy_ne : q yB ≠ 1 := by
    intro h
    have hyAB : yB ∈ AB := (QuotientGroup.eq_one_iff yB).mp h
    exact hyA (Subgroup.mem_subgroupOf.mp hyAB)
  have hqy3 : (q yB) ^ 3 = 1 := by
    rw [← map_pow]
    have hyB3 : yB ^ 3 = ⟨y ^ 3, Subgroup.mem_sup_left hy3⟩ := Subtype.ext rfl
    rw [hyB3]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hy3)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hqy_order : orderOf (q yB) = 3 := orderOf_eq_prime hqy3 hqy_ne
  have hdvd : 3 ∣ Nat.card (B ⧸ AB) := by
    rw [← hqy_order]
    exact orderOf_dvd_natCard (q yB)
  have hge : 3 ≤ Nat.card (B ⧸ AB) := Nat.le_of_dvd Nat.card_pos hdvd
  have hidx : AB.index = Nat.card (B ⧸ AB) := Subgroup.index_eq_card AB
  have hcardB : Nat.card AB * AB.index = Nat.card B := Subgroup.card_mul_index AB
  have hcardAB : Nat.card AB = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
  calc 3 * Nat.card A = Nat.card A * 3 := by ring
    _ ≤ Nat.card AB * AB.index := by
      rw [hcardAB, hidx]
      exact Nat.mul_le_mul_left (Nat.card A) hge
    _ = Nat.card B := hcardB

private theorem phi_one : (phi piE7 piE7_pow_three) (Multiplicative.ofAdd (1 : ZMod 3)) =
    shiftAut piE7 := by
  simpa using phi_ofAdd_natCast (π := piE7) (hπ := piE7_pow_three) 1

private theorem phi_two : (phi piE7 piE7_pow_three) (Multiplicative.ofAdd (2 : ZMod 3)) =
    shiftAut piE7 ^ 2 := by
  simpa using phi_ofAdd_natCast (π := piE7) (hπ := piE7_pow_three) 2

private theorem model_pow_three_of_one (v : Multiplicative (Fin 3 → ZMod 3)) :
    (⟨v, 1⟩ : Model piE7 piE7_pow_three) ^ 3 = 1 := by
  rw [pow_three]
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, map_one, one_mul,
      map_mul, MulAut.one_apply, SemidirectProduct.one_left]
    apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_mul, toAdd_one, Pi.add_apply, Pi.zero_apply]
    fin_cases i <;> (ring_nf; rw [show (3 : ZMod 3) = 0 by decide, mul_zero])
  · simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right]

private theorem model_pow_three_of_one_mul (v : Multiplicative (Fin 3 → ZMod 3)) :
    (⟨v, Multiplicative.ofAdd (1 : ZMod 3)⟩ : Model piE7 piE7_pow_three) ^ 3 =
      (⟨Multiplicative.ofAdd (fun _ => v.toAdd 0 + v.toAdd 1 + v.toAdd 2), 1⟩ :
        Model piE7 piE7_pow_three) := by
  rw [pow_three]
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, map_mul, phi_one,
      phi_two]
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;>
      simp [toAdd_shiftAut, piE7] <;> ring_nf
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, map_mul, phi_one,
      phi_two, ← ofAdd_add]
    decide

private theorem modelHomE6_of_right_one (u : Multiplicative (Fin 3 → ZMod 3)) :
    modelHomE6 (⟨u, Multiplicative.ofAdd (1 : ZMod 3)⟩ : Model piE7 piE7_pow_three) =
      (coxeterSystem .E6).wordProd
        (nfWordE6 (u.toAdd 0).val (u.toAdd 1).val (u.toAdd 2).val ++ wordE6C) := by
  rw [show (⟨u, Multiplicative.ofAdd (1 : ZMod 3)⟩ : Model piE7 piE7_pow_three) =
      SemidirectProduct.inl u * SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 3))
        from (SemidirectProduct.inl_left_mul_inr_right _).symm,
    map_mul, modelHomE6_inl, show modelHomE6
        (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 3))) =
      (coxeterSystem .E6).wordProd wordE6C from modelHomE6_c,
    ← CoxeterSystem.wordProd_append]

private theorem card_fix_word_order_nine_aux :
    ∀ u : Multiplicative (Fin 3 → ZMod 3),
      u.toAdd 0 + u.toAdd 1 + u.toAdd 2 ≠ 0 →
      Fintype.card {x : Fin Tag.E6.rank → ZMod 3 //
        adWord .E6 3 (nfWordE6 (u.toAdd 0).val (u.toAdd 1).val (u.toAdd 2).val ++ wordE6C)
          x = x} ≤ 9 := by
  decide +kernel

private theorem card_fix_order_nine_m1 (v : Fin 3 → ZMod 3)
    (hv : v 0 + v 1 + v 2 ≠ 0) :
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
      adAct .E6 3 (modelHomE6 (⟨Multiplicative.ofAdd v, Multiplicative.ofAdd (1 : ZMod 3)⟩ :
        Model piE7 piE7_pow_three)) x = x} ≤ 9 := by
  have hv' : (Multiplicative.ofAdd v).toAdd 0 + (Multiplicative.ofAdd v).toAdd 1 +
      (Multiplicative.ofAdd v).toAdd 2 ≠ 0 := by simpa using hv
  rw [modelHomE6_of_right_one, Nat.card_eq_fintype_card]
  simpa only [adWord_eq_adAct] using
    card_fix_word_order_nine_aux (Multiplicative.ofAdd v) hv'

private theorem right_ne_one_of_orderOf_eq_nine (t : Model piE7 piE7_pow_three)
    (ht : orderOf t = 9) : t.right ≠ 1 := by
  intro h
  have h3 : t ^ 3 = 1 := by
    have e : t = (⟨t.left, 1⟩ : Model piE7 piE7_pow_three) := SemidirectProduct.ext rfl h
    rw [e]
    exact model_pow_three_of_one t.left
  have hdvd : orderOf t ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rw [ht] at hdvd
  norm_num at hdvd

private theorem sum_ne_zero_of_orderOf_eq_nine (u : Multiplicative (Fin 3 → ZMod 3))
    (h : orderOf (⟨u, Multiplicative.ofAdd (1 : ZMod 3)⟩ : Model piE7 piE7_pow_three) = 9) :
    u.toAdd 0 + u.toAdd 1 + u.toAdd 2 ≠ 0 := by
  intro h0
  have h3 : (⟨u, Multiplicative.ofAdd (1 : ZMod 3)⟩ : Model piE7 piE7_pow_three) ^ 3 = 1 := by
    rw [model_pow_three_of_one_mul, h0]
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      simp
    · rfl
  have hdvd : orderOf (⟨u, Multiplicative.ofAdd (1 : ZMod 3)⟩ : Model piE7 piE7_pow_three) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one h3
  rw [h] at hdvd
  norm_num at hdvd

private theorem adAct_inv_fixed_iff (t : Model piE7 piE7_pow_three)
    (x : Fin Tag.E6.rank → ZMod 3) :
    adAct .E6 3 (modelHomE6 t⁻¹) x = x ↔ adAct .E6 3 (modelHomE6 t) x = x := by
  constructor
  · intro h
    have h1 := congrArg (fun y => adAct .E6 3 (modelHomE6 t) y) h
    rw [← adAct_mul, ← map_mul, mul_inv_cancel, map_one, adAct_one] at h1
    exact h1.symm
  · intro h
    have h1 := congrArg (fun y => adAct .E6 3 (modelHomE6 t⁻¹) y) h
    rw [← adAct_mul, ← map_mul, inv_mul_cancel, map_one, adAct_one] at h1
    exact h1.symm

private theorem card_fix_order_nine_model (t : Model piE7 piE7_pow_three)
    (ht : orderOf t = 9) :
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 // adAct .E6 3 (modelHomE6 t) x = x} ≤ 9 := by
  classical
  obtain ⟨m, hm⟩ := Multiplicative.ofAdd.surjective t.right
  have hm0 : m ≠ 0 := by
    intro h0
    exact right_ne_one_of_orderOf_eq_nine t ht (by rw [← hm, h0]; rfl)
  have hm12 : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = 2 := by
    intro x
    have hx : x = 0 ∨ x = 1 ∨ x = 2 := by
      revert x
      decide
    rcases hx with rfl | rfl | rfl
    · intro h
      exact absurd rfl h
    · intro _
      exact Or.inl rfl
    · intro _
      exact Or.inr rfl
  rcases hm12 m hm0 with rfl | rfl
  · have ht' : t = (⟨t.left, Multiplicative.ofAdd (1 : ZMod 3)⟩ :
        Model piE7 piE7_pow_three) := SemidirectProduct.ext rfl hm.symm
    rw [ht']
    exact card_fix_order_nine_m1 t.left
      (sum_ne_zero_of_orderOf_eq_nine t.left (by rw [← ht']; exact ht))
  · let u := (t⁻¹).left
    have hright : (t⁻¹).right = Multiplicative.ofAdd (1 : ZMod 3) := by
      rw [SemidirectProduct.inv_right, ← hm]
      decide
    have htin : t⁻¹ = (⟨u, Multiplicative.ofAdd (1 : ZMod 3)⟩ :
        Model piE7 piE7_pow_three) := SemidirectProduct.ext rfl hright
    have hord : orderOf (⟨u, Multiplicative.ofAdd (1 : ZMod 3)⟩ :
        Model piE7 piE7_pow_three) = 9 := by
      rw [← htin, orderOf_inv, ht]
    have hfix : Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
        adAct .E6 3 (modelHomE6 t) x = x} =
        Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
          adAct .E6 3 (modelHomE6 (⟨u, Multiplicative.ofAdd (1 : ZMod 3)⟩ :
            Model piE7 piE7_pow_three)) x = x} := by
      rw [← htin]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun x => (adAct_inv_fixed_iff t x).symm)
    rw [hfix]
    exact card_fix_order_nine_m1 u (sum_ne_zero_of_orderOf_eq_nine u hord)

private theorem mem_of_eq_bot_of_centralFix (A : Subgroup (WeylGroup .E6)) {w : WeylGroup .E6}
    (hwx : ∀ x : Fin Tag.E6.rank → ZMod 3,
      (∀ a ∈ A, adAct .E6 3 a x = x) → adAct .E6 3 w x = x) (hA1 : A = ⊥) : w ∈ A := by
  have hwx_all : ∀ x : Fin Tag.E6.rank → ZMod 3, adAct .E6 3 w x = x := by
    intro x
    apply hwx x
    intro a ha
    rw [hA1] at ha
    rw [Subgroup.mem_bot.mp ha, adAct_one]
  have hw1 : w = 1 := NoOffRest.eq_one_of_adAct (p := 3) (by norm_num) hwx_all
  rw [hA1, hw1]
  exact Subgroup.mem_bot.mpr rfl

private theorem three_le_card_of_le_range (A : Subgroup (WeylGroup .E6))
    (hAS : A ≤ modelHomE6.range) (hA1 : A ≠ ⊥) : 3 ≤ Nat.card A := by
  have hAdvd : Nat.card A ∣ 3 ^ 4 := by
    have h := Subgroup.card_dvd_of_le hAS
    rwa [card_range_modelHomE6, show (81 : ℕ) = 3 ^ 4 by norm_num] at h
  rcases (Nat.dvd_prime_pow Nat.prime_three).mp hAdvd with ⟨k, hk, hkA⟩
  rw [hkA]
  rcases Nat.eq_zero_or_pos k with h | h
  · rw [h, pow_zero] at hkA
    exact absurd hkA.symm ((Subgroup.one_lt_card_iff_ne_bot A).mpr hA1).ne
  · calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h

private theorem exists_abelian_sup_zpowers (A : Subgroup (WeylGroup .E6))
    (hA : IsElemAbelian 3 A) (hcard : 3 ^ 4 ≤ Nat.card A *
      Nat.card {x : Fin Tag.E6.rank → ZMod 3 // ∀ a ∈ A, adAct .E6 3 a x = x})
    (hA_ge3 : 3 ≤ Nat.card A) {y : WeylGroup .E6}
    (hyX : y ∈ centralFix A) (hyA : y ∉ A) (hy3A : y ^ 3 ∈ A) :
    ∃ B : Subgroup (WeylGroup .E6), B = A ⊔ Subgroup.zpowers y ∧ A ≤ B ∧
      IsPGroup 3 ↥B ∧ IsMulCommutative ↥B ∧ 3 < Nat.card ↥B ∧
      3 ^ 5 ≤ Nat.card ↥B * Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
        ∀ b ∈ B, adAct .E6 3 b x = x} := by
  have hycomm : ∀ a ∈ A, y * a = a * y := fun a ha => hyX.1 a ha
  let B : Subgroup (WeylGroup .E6) := A ⊔ Subgroup.zpowers y
  have hB3 : IsPGroup 3 ↥B := isPGroup_sup_zpowers A hA hycomm hy3A
  have hBcomm : IsMulCommutative ↥B := isMulCommutative_sup_zpowers A hA hycomm
  have hBcard : 3 * Nat.card A ≤ Nat.card ↥B := card_le_card_sup_zpowers A hy3A hyA hBcomm
  have hBfix : Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
      ∀ b ∈ B, adAct .E6 3 b x = x} =
      Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
        ∀ a ∈ A, adAct .E6 3 a x = x} :=
    card_fix_sup_zpowers A (fun x hx => hyX.2 x hx)
  have hBprod : 3 ^ 5 ≤ Nat.card ↥B *
      Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
        ∀ b ∈ B, adAct .E6 3 b x = x} := by
    rw [hBfix]
    calc 3 ^ 5 = 3 * 3 ^ 4 := by norm_num
      _ ≤ 3 * (Nat.card A *
          Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
            ∀ a ∈ A, adAct .E6 3 a x = x}) := Nat.mul_le_mul_left 3 hcard
      _ = (3 * Nat.card A) *
          Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
            ∀ a ∈ A, adAct .E6 3 a x = x} := by ring
      _ ≤ Nat.card ↥B *
          Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
            ∀ a ∈ A, adAct .E6 3 a x = x} := Nat.mul_le_mul_right _ hBcard
  have hB_gt3 : 3 < Nat.card ↥B := by
    calc 3 < 3 * Nat.card A := by
          have h9 : 9 ≤ 3 * Nat.card A := Nat.mul_le_mul_left 3 hA_ge3
          omega
      _ ≤ Nat.card ↥B := hBcard
  exact ⟨B, rfl, le_sup_left, hB3, hBcomm, hB_gt3, hBprod⟩

private theorem elemAbelian_or_order_nine (A : Subgroup (WeylGroup .E6))
    (hA : IsElemAbelian 3 A) {y : WeylGroup .E6}
    (hycomm : ∀ a ∈ A, y * a = a * y) (hy3A : y ^ 3 ∈ A) :
    IsElemAbelian 3 (A ⊔ Subgroup.zpowers y) ∨
      ∃ z ∈ A ⊔ Subgroup.zpowers y, orderOf z = 9 := by
  by_cases hB : IsElemAbelian 3 (A ⊔ Subgroup.zpowers y)
  · exact Or.inl hB
  · right
    have hy3eq : y ^ 3 ≠ 1 := by
      intro h
      apply hB
      have hzyp : IsElemAbelian 3 (Subgroup.zpowers y) := CFSG.Open.isElemAbelian_zpowers h
      refine TableB.isElemAbelian_sup hA hzyp ?_
      intro a ha c hc
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
      rw [← hk]
      exact (Commute.zpow_right (hycomm a ha).symm k).eq
    have hy9 : y ^ 9 = 1 := by
      have h : (y ^ 3) ^ 3 = 1 := hA.2 (y ^ 3) hy3A
      rw [← pow_mul] at h
      rwa [show (3 : ℕ) * 3 = 9 by norm_num] at h
    have hy_order9 : orderOf y = 9 :=
      orderOf_eq_prime_pow (p := 3) (n := 1) hy3eq (by
        rw [show 3 ^ (1 + 1) = 9 by norm_num]
        exact hy9)
    exact ⟨y, Subgroup.mem_sup_right (Subgroup.mem_zpowers y), hy_order9⟩

private theorem commute_map_conj (B : Subgroup (WeylGroup .E6))
    (hBcomm : IsMulCommutative ↥B) (g : WeylGroup .E6) :
    ∀ u ∈ B.map (MulAut.conj g).toMonoidHom,
      ∀ v ∈ B.map (MulAut.conj g).toMonoidHom, u * v = v * u := by
  rintro u ⟨a, ha, rfl⟩ v ⟨b, hb, rfl⟩
  haveI : IsMulCommutative ↥B := hBcomm
  have hab : a * b = b * a :=
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥B) (⟨b, hb⟩ : ↥B))
  calc (MulAut.conj g).toMonoidHom a * (MulAut.conj g).toMonoidHom b
      = g * (a * b) * g⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    _ = g * (b * a) * g⁻¹ := by rw [hab]
    _ = (MulAut.conj g).toMonoidHom b * (MulAut.conj g).toMonoidHom a := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group

private theorem exists_conj_le_range
    (B : Subgroup (WeylGroup .E6)) (hB3 : IsPGroup 3 ↥B) :
    ∃ (g : WeylGroup .E6) (B' : Subgroup (WeylGroup .E6)),
      B' = B.map (MulAut.conj g).toMonoidHom ∧ B' ≤ modelHomE6.range ∧
      Nat.card ↥B' = Nat.card ↥B ∧
      Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
        ∀ b ∈ B', adAct .E6 3 b x = x} =
      Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
        ∀ b ∈ B, adAct .E6 3 b x = x} := by
  have hidx : ¬ 3 ∣ modelHomE6.range.index := by
    rw [NoOffExc.index_eq_of_card card_range_modelHomE6 NoOffExc.card_weyl_E6
      (show 81 * 640 = 51840 by norm_num) (by norm_num)]
    norm_num
  obtain ⟨g, hgB⟩ := TableBF4.exists_conj_le_of_not_dvd_index Nat.prime_three hidx hB3
  refine ⟨g, B.map (MulAut.conj g).toMonoidHom, rfl, hgB, ?_, ?_⟩
  · exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  · exact NoOffRest.card_fix_map_conj (adPerm .E6 3) B g

private theorem card_mul_fix_lt_of_elemAbelian (B' : Subgroup (WeylGroup .E6))
    (hB'S : B' ≤ modelHomE6.range) (hB'el : IsElemAbelian 3 B')
    (hB'gt3 : 3 < Nat.card ↥B') :
    Nat.card ↥B' * Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
      ∀ b ∈ B', adAct .E6 3 b x = x} < 3 ^ 5 := by
  have hB'ne : B' ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot B').mp (by omega)
  rcases E6ThreeEnd.refined_E6 B' hB'S hB'el hB'ne with hlt | ⟨i, hi⟩
  · exact hlt
  · have hg1 : gE6 i ≠ 1 := by
      intro h
      exact (testE6_move i).1 (by rw [h]; rfl)
    have hB'card3 : Nat.card ↥B' = 3 := by
      rw [hi, Nat.card_zpowers]
      exact orderOf_eq_prime (gE6_pow_three i) hg1
    omega

private theorem card_le_nine_of_order_nine_card (B' : Subgroup (WeylGroup .E6))
    (hB'S : B' ≤ modelHomE6.range)
    (hB'comm : ∀ u ∈ B', ∀ v ∈ B', u * v = v * u)
    {s : WeylGroup .E6} (hsB' : s ∈ B') (hs9 : orderOf s = 9) :
    Nat.card ↥B' ≤ 9 := by
  obtain ⟨t, ht⟩ := hB'S hsB'
  let B'' : Subgroup (Model piE7 piE7_pow_three) := B'.comap modelHomE6
  have htB'' : t ∈ B'' := Subgroup.mem_comap.mpr (by rwa [ht])
  have ht9 : orderOf t = 9 := by
    have h := orderOf_injective modelHomE6 modelHomE6_injective t
    rw [← h, ht, hs9]
  have hB''card : Nat.card ↥B'' = Nat.card ↥B' := by
    have hmap := Subgroup.card_map_of_injective (f := modelHomE6) (K := B'')
      modelHomE6_injective
    rw [Subgroup.map_comap_eq_self hB'S] at hmap
    exact hmap.symm
  have hB''comm : ∀ u ∈ B'', ∀ v ∈ B'', u * v = v * u := by
    intro u hu v hv
    apply modelHomE6_injective
    rw [map_mul, map_mul]
    exact hB'comm _ (Subgroup.mem_comap.mp hu) _ (Subgroup.mem_comap.mp hv)
  have ht_right_ne : t.right ≠ 1 := right_ne_one_of_orderOf_eq_nine t ht9
  obtain ⟨t₁, ht₁B'', ht₁right⟩ := TableBExc.Three.exists_right_eq_ofAdd_one
    (A := B'') htB'' ht_right_ne
  have hK : Nat.card {w : Multiplicative (Fin 3 → ZMod 3) // shiftAut piE7 w = w} ≤ 3 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hB''card_le : Nat.card ↥B'' ≤ 3 * 3 :=
    TableBExc.Three.card_le_of_right_eq (π := piE7) (hπ := piE7_pow_three)
      hB''comm ht₁B'' ht₁right (K₁ := 3) hK
  calc Nat.card ↥B' = Nat.card ↥B'' := hB''card.symm
    _ ≤ 3 * 3 := hB''card_le
    _ = 9 := by norm_num

private theorem card_fix_le_nine_of_order_nine (B' : Subgroup (WeylGroup .E6))
    (hB'S : B' ≤ modelHomE6.range) {s : WeylGroup .E6}
    (hsB' : s ∈ B') (hs9 : orderOf s = 9) :
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
      ∀ b ∈ B', adAct .E6 3 b x = x} ≤ 9 := by
  obtain ⟨t, ht⟩ := hB'S hsB'
  have ht9 : orderOf t = 9 := by
    have h := orderOf_injective modelHomE6 modelHomE6_injective t
    rw [← h, ht, hs9]
  calc Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
        ∀ b ∈ B', adAct .E6 3 b x = x}
      ≤ Nat.card {x : Fin Tag.E6.rank → ZMod 3 // adAct .E6 3 s x = x} :=
        Nat.card_le_card_of_injective
          (fun x : {x : Fin Tag.E6.rank → ZMod 3 //
              ∀ b ∈ B', adAct .E6 3 b x = x} =>
            (⟨x.1, x.2 s hsB'⟩ :
              {x : Fin Tag.E6.rank → ZMod 3 // adAct .E6 3 s x = x}))
          (fun x y hxy => Subtype.ext (congrArg
            (fun z : {x : Fin Tag.E6.rank → ZMod 3 //
                adAct .E6 3 s x = x} => z.1) hxy))
    _ = Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
          adAct .E6 3 (modelHomE6 t) x = x} := by rw [ht]
    _ ≤ 9 := card_fix_order_nine_model t ht9

private theorem card_le_nine_of_order_nine (B' : Subgroup (WeylGroup .E6))
    (hB'S : B' ≤ modelHomE6.range)
    (hB'comm : ∀ u ∈ B', ∀ v ∈ B', u * v = v * u)
    {s : WeylGroup .E6} (hsB' : s ∈ B') (hs9 : orderOf s = 9) :
    Nat.card ↥B' ≤ 9 ∧ Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
      ∀ b ∈ B', adAct .E6 3 b x = x} ≤ 9 :=
  ⟨card_le_nine_of_order_nine_card B' hB'S hB'comm hsB' hs9,
   card_fix_le_nine_of_order_nine B' hB'S hsB' hs9⟩

theorem mem_of_commute_of_fix
    (A : Subgroup (WeylGroup .E6)) (hAS : A ≤ modelHomE6.range) (hA : IsElemAbelian 3 A)
    (hcard : 3 ^ 4 ≤ Nat.card A *
      Nat.card {x : Fin Tag.E6.rank → ZMod 3 // ∀ a ∈ A, adAct .E6 3 a x = x})
    {w : WeylGroup .E6} (hwA : ∀ a ∈ A, w * a = a * w)
    (hwx : ∀ x : Fin Tag.E6.rank → ZMod 3, (∀ a ∈ A, adAct .E6 3 a x = x) →
      adAct .E6 3 w x = x) :
    w ∈ A := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hA1 : A = ⊥
  · exact mem_of_eq_bot_of_centralFix A hwx hA1
  · have hA_ge3 : 3 ≤ Nat.card A := three_le_card_of_le_range A hAS hA1
    have hwX : w ∈ centralFix A := ⟨hwA, hwx⟩
    by_contra hw_not
    obtain ⟨y, hyX, hyA, hy3A⟩ := exists_pow_three_mem_of_ne A
      (fun x hx => orderOf_eq_pow_three_of_mem_centralFix A hA hx) hwX hw_not
    obtain ⟨B, hBdef, _, hB3, hBcomm, hB_gt3, hBprod⟩ :=
      exists_abelian_sup_zpowers A hA hcard hA_ge3 hyX hyA hy3A
    have hBdich := elemAbelian_or_order_nine A hA (fun a ha => hyX.1 a ha) hy3A
    rw [← hBdef] at hBdich
    obtain ⟨g, B', hB'def, hB'S, hB'card, hB'fix⟩ := exists_conj_le_range B hB3
    have hB'gt3 : 3 < Nat.card ↥B' := by
      rw [hB'card]
      exact hB_gt3
    have hB'prod : 3 ^ 5 ≤ Nat.card ↥B' *
        Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
          ∀ b ∈ B', adAct .E6 3 b x = x} := by
      rw [hB'card, hB'fix]
      exact hBprod
    have hB'comm : ∀ u ∈ B', ∀ v ∈ B', u * v = v * u := by
      rw [hB'def]
      exact commute_map_conj B hBcomm g
    rcases hBdich with hBel | ⟨z, hzB, hz9⟩
    · have hB'el : IsElemAbelian 3 B' := by
        rw [hB'def]
        exact TableB.isElemAbelian_map hBel ((MulAut.conj g).toMonoidHom)
      have hlt := card_mul_fix_lt_of_elemAbelian B' hB'S hB'el hB'gt3
      omega
    · let s : WeylGroup .E6 := (MulAut.conj g).toMonoidHom z
      have hsB' : s ∈ B' := by
        rw [hB'def]
        exact ⟨z, hzB, rfl⟩
      have hs9 : orderOf s = 9 := by
        have h := MulEquiv.orderOf_eq (MulAut.conj g) z
        exact h.trans hz9
      obtain ⟨hcard_le, hfix_le⟩ :=
        card_le_nine_of_order_nine B' hB'S hB'comm hsB' hs9
      have hprod_le : Nat.card ↥B' *
          Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
            ∀ b ∈ B', adAct .E6 3 b x = x} ≤ 9 * 9 :=
        Nat.mul_le_mul hcard_le hfix_le
      have : 3 ^ 5 ≤ 9 * 9 := le_trans hB'prod hprod_le
      norm_num at this

end CFSG.StandardType.E6NonToralThree
