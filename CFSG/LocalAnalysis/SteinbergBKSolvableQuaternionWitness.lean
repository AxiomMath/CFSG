module

public import CFSG.RankThree.PGroups.SolvableFittingSelfCentralizing
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedAltSevenQuaternion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalizerComplement
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOneAutomorphisms

public section

namespace CFSG.LocalAnalysis.SteinbergBK

open Subgroup
open scoped MatrixGroups


@[expose] def slTwoThreeX : SL(2, ZMod 3) :=
  ⟨!![0, 1; -1, 0], by rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def slTwoThreeY : SL(2, ZMod 3) :=
  ⟨!![1, 1; 1, -1], by rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def slTwoThreeA : SL(2, ZMod 3) :=
  ⟨!![0, 1; -1, -1], by rw [Matrix.det_fin_two_of]; decide⟩

theorem slTwoThree_relations :
    slTwoThreeX ^ 4 = 1 ∧ slTwoThreeY ^ 2 = slTwoThreeX ^ 2 ∧
      slTwoThreeY * slTwoThreeX * slTwoThreeY⁻¹ = slTwoThreeX⁻¹ ∧
      slTwoThreeX ^ 2 = -1 ∧ slTwoThreeA ^ 3 = 1 ∧
      slTwoThreeA * slTwoThreeX * slTwoThreeA⁻¹ = slTwoThreeY ∧
      slTwoThreeA * slTwoThreeY * slTwoThreeA⁻¹ = slTwoThreeX * slTwoThreeY := by
  decide +kernel

@[expose] def slTwoThreeNormalForm (f : Fin 2 × Fin 2 × Fin 2 × Fin 3) : SL(2, ZMod 3) :=
  (-1) ^ (f.1 : ℕ) * slTwoThreeX ^ (f.2.1 : ℕ) * slTwoThreeY ^ (f.2.2.1 : ℕ) *
    slTwoThreeA ^ (f.2.2.2 : ℕ)

theorem slTwoThreeNormalForm_bijective : Function.Bijective slTwoThreeNormalForm := by
  refine ⟨?_, ?_⟩
  · intro f g h
    revert f g
    decide +kernel
  · decide +kernel

section QuaternionLift

variable {H : Type*} [Group H]

theorem pow_val_add_of_pow_four_eq_one {x : H} (hx : x ^ 4 = 1) (i j : ZMod (2 * 2)) :
    x ^ (i + j).val = x ^ i.val * x ^ j.val := by
  have h4 : x ^ (2 * 2) = 1 := hx
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (i.val + j.val) (2 * 2), pow_add, pow_mul]
  rw [h4, one_pow, mul_one]

theorem pow_val_sub_of_pow_four_eq_one {x : H} (hx : x ^ 4 = 1) (i j : ZMod (2 * 2)) :
    x ^ (j - i).val = x ^ j.val * (x ^ i.val)⁻¹ := by
  have h := pow_val_add_of_pow_four_eq_one hx (j - i) i
  rw [sub_add_cancel] at h
  rw [h, mul_inv_cancel_right]

theorem pow_mul_eq_mul_inv_pow_of_conj {x y : H} (hyx : y * x * y⁻¹ = x⁻¹) (k : ℕ) :
    x ^ k * y = y * (x ^ k)⁻¹ := by
  have h1 : y⁻¹ * x * y = x⁻¹ := by
    have h2 : y * x = x⁻¹ * y := by rw [← hyx, inv_mul_cancel_right]
    calc y⁻¹ * x * y = y⁻¹ * (x * y) := mul_assoc _ _ _
      _ = (y⁻¹ * x⁻¹ * y)⁻¹ := by group
      _ = x⁻¹ := by
        rw [mul_assoc, ← h2, ← mul_assoc, inv_mul_cancel, one_mul]
  have h3 : y⁻¹ * x ^ k * y = (x ^ k)⁻¹ := by
    have := conj_pow (a := y⁻¹) (b := x) (i := k)
    rw [inv_inv] at this
    rw [← this, h1, inv_pow]
  calc x ^ k * y = y * (y⁻¹ * x ^ k * y) := by group
    _ = y * (x ^ k)⁻¹ := by rw [h3]

@[expose] def quaternionEightLift (x y : H) (hx : x ^ 4 = 1) (hy : y ^ 2 = x ^ 2)
    (hyx : y * x * y⁻¹ = x⁻¹) : QuaternionGroup 2 →* H where
  toFun g := match g with
    | QuaternionGroup.a i => x ^ i.val
    | QuaternionGroup.xa i => y * x ^ i.val
  map_one' := by
    rw [QuaternionGroup.one_def]
    change x ^ (0 : ZMod (2 * 2)).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' g h := by
    have hc : ∀ i j : ZMod (2 * 2), (x ^ i.val)⁻¹ * x ^ j.val = x ^ j.val * (x ^ i.val)⁻¹ :=
      fun i j => ((Commute.pow_pow_self x i.val j.val).inv_left).eq
    cases g with
    | a i =>
      cases h with
      | a j =>
        change x ^ (i + j).val = x ^ i.val * x ^ j.val
        exact pow_val_add_of_pow_four_eq_one hx i j
      | xa j =>
        change y * x ^ (j - i).val = x ^ i.val * (y * x ^ j.val)
        rw [pow_val_sub_of_pow_four_eq_one hx i j, ← mul_assoc (x ^ i.val) y,
          pow_mul_eq_mul_inv_pow_of_conj hyx, mul_assoc y, hc]
    | xa i =>
      cases h with
      | a j =>
        change y * x ^ (i + j).val = y * x ^ i.val * x ^ j.val
        rw [pow_val_add_of_pow_four_eq_one hx i j, mul_assoc]
      | xa j =>
        change x ^ (((2 : ℕ) : ZMod (2 * 2)) + j - i).val = y * x ^ i.val * (y * x ^ j.val)
        have e1 : x ^ (((2 : ℕ) : ZMod (2 * 2)) + j - i).val =
            x ^ 2 * x ^ j.val * (x ^ i.val)⁻¹ := by
          rw [pow_val_sub_of_pow_four_eq_one hx i, pow_val_add_of_pow_four_eq_one hx,
            ZMod.val_natCast]
        have e2 : y * x ^ i.val * (y * x ^ j.val) = x ^ 2 * ((x ^ i.val)⁻¹ * x ^ j.val) := by
          rw [mul_assoc y, ← mul_assoc (x ^ i.val) y, pow_mul_eq_mul_inv_pow_of_conj hyx,
            ← mul_assoc y, ← mul_assoc y, ← pow_two y, hy, mul_assoc]
        rw [e1, e2, hc, mul_assoc]

theorem quaternionEightLift_a (x y : H) (hx : x ^ 4 = 1) (hy : y ^ 2 = x ^ 2)
    (hyx : y * x * y⁻¹ = x⁻¹) (i : ZMod (2 * 2)) :
    quaternionEightLift x y hx hy hyx (QuaternionGroup.a i) = x ^ i.val :=
  rfl

theorem quaternionEightLift_xa (x y : H) (hx : x ^ 4 = 1) (hy : y ^ 2 = x ^ 2)
    (hyx : y * x * y⁻¹ = x⁻¹) (i : ZMod (2 * 2)) :
    quaternionEightLift x y hx hy hyx (QuaternionGroup.xa i) = y * x ^ i.val :=
  rfl

end QuaternionLift

section Quaternion

open QuaternionGroup

theorem isPGroup_mulAut_quaternionGroup {k : ℕ} (hk : 2 ≤ k) :
    IsPGroup 2 (MulAut (QuaternionGroup (2 ^ k))) := by
  have hne : NeZero (2 ^ k) := ⟨by positivity⟩
  have hT : IsPGroup 2 (QuaternionGroup (2 ^ k)) :=
    CFSG.ProperTwoGeneratedCore.quaternion_power_two_isPGroup k
  set u : QuaternionGroup (2 ^ k) := a 1 with hu
  have hin : ∀ i : ZMod (2 * 2 ^ k), (a i : QuaternionGroup (2 ^ k)) ∈ zpowers u := by
    intro i
    refine ⟨(i.val : ℤ), ?_⟩
    change u ^ (i.val : ℤ) = a i
    rw [zpow_natCast, hu, a_one_pow, ZMod.natCast_zmod_val]
  have hout : ∀ g : QuaternionGroup (2 ^ k), g ∉ zpowers u → ∃ i, g = xa i := by
    intro g hg
    cases g with
    | a i => exact absurd (hin i) hg
    | xa i => exact ⟨i, rfl⟩
  have hcoset : ∀ x y : QuaternionGroup (2 ^ k), x ∉ zpowers u → y ∉ zpowers u →
      y * x⁻¹ ∈ zpowers u := by
    intro x y hx hy
    obtain ⟨i, rfl⟩ := hout x hx
    obtain ⟨j, rfl⟩ := hout y hy
    have hinv : (xa i : QuaternionGroup (2 ^ k))⁻¹ = xa (((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) + i) := by
      rw [inv_eq_iff_mul_eq_one, xa_mul_xa, QuaternionGroup.one_def]
      congr 1
      have h2 : (((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) + ((2 ^ k : ℕ) : ZMod (2 * 2 ^ k))) = 0 := by
        have h3 := ZMod.natCast_self (2 * 2 ^ k)
        push_cast at h3 ⊢
        linear_combination h3
      linear_combination h2
    rw [hinv, xa_mul_xa]
    exact hin _
  have hpres : ∀ φ : MulAut (QuaternionGroup (2 ^ k)), φ u ∈ zpowers u := by
    intro φ
    by_contra hφ
    obtain ⟨i, hi⟩ := hout _ hφ
    have h := congrArg orderOf hi
    rw [MulEquiv.orderOf_eq, hu, orderOf_a_one, orderOf_xa] at h
    have h4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  intro φ
  have hmaps : ∀ w ∈ zpowers u, φ w ∈ zpowers u := by
    intro w hw
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hw
    rw [map_zpow]
    exact zpow_mem (hpres φ) m
  let f : zpowers u →* zpowers u :=
    (φ.toMonoidHom.domRestrict (zpowers u)).codRestrict (zpowers u) (fun w => hmaps w w.2)
  have hf : Function.Injective f := fun x y hxy =>
    Subtype.ext (φ.injective (congrArg Subtype.val hxy))
  let φZ : MulAut (zpowers u) := MulEquiv.ofBijective f ⟨hf, Finite.injective_iff_surjective.mp hf⟩
  have hφZ : ∀ j : ℕ, ∀ w : zpowers u, (((φZ ^ j) w : zpowers u) : QuaternionGroup (2 ^ k)) =
      (φ ^ j) (w : QuaternionGroup (2 ^ k)) := by
    intro j
    induction j with
    | zero => intro w; rfl
    | succ j ih =>
      intro w
      rw [pow_succ φZ j, MulAut.mul_apply, ih, pow_succ φ j, MulAut.mul_apply]
      rfl
  obtain ⟨c, hc⟩ := CFSG.TwoRankLowerBound.Helpers.cyclic_two_group_automorphisms_isPGroup
    (zpowers u) (hT.to_subgroup (zpowers u)) φZ
  set ψ := φ ^ 2 ^ c with hψ
  have hψZ : ∀ w ∈ zpowers u, ψ w = w := by
    intro w hw
    have h := hφZ (2 ^ c) ⟨w, hw⟩
    rw [hc] at h
    exact h.symm
  have hψpowZ : ∀ j : ℕ, ∀ w ∈ zpowers u, (ψ ^ j) w = w := by
    intro j
    induction j with
    | zero => intro w _; rfl
    | succ j ih => intro w hw; rw [pow_succ' ψ j, MulAut.mul_apply, ih w hw, hψZ w hw]
  obtain ⟨d, hd⟩ := IsPGroup.iff_orderOf.mp hT u
  have hx : (xa 0 : QuaternionGroup (2 ^ k)) ∉ zpowers u := by
    intro h
    classical
    rw [mem_zpowers_iff_mem_range_orderOf] at h
    obtain ⟨n, -, hn⟩ := Finset.mem_image.mp h
    rw [hu, a_one_pow] at hn
    cases hn
  set x : QuaternionGroup (2 ^ k) := xa 0 with hxdef
  have hψx : ψ x ∉ zpowers u := fun h => hx (by
    have h1 := ψ.injective (hψZ _ h)
    rwa [h1] at h)
  have hbZ : ψ x * x⁻¹ ∈ zpowers u := hcoset x (ψ x) hx hψx
  have hψpow : ∀ j : ℕ, (ψ ^ j) x = (ψ x * x⁻¹) ^ j * x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ' ψ j, MulAut.mul_apply, ih, map_mul, map_pow, hψZ _ hbZ, pow_succ,
        mul_assoc _ (ψ x * x⁻¹) x, inv_mul_cancel_right]
  have hbN : (ψ x * x⁻¹) ^ 2 ^ d = 1 := by
    rw [← hd]
    exact orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_of_mem_zpowers hbZ)
  refine ⟨c + d, ?_⟩
  rw [pow_add, pow_mul, ← hψ]
  refine MulEquiv.ext fun y => ?_
  by_cases hy : y ∈ zpowers u
  · exact hψpowZ _ y hy
  · have hyx : y * x⁻¹ ∈ zpowers u := hcoset x y hx hy
    have hy' : y = (y * x⁻¹) * x := by group
    rw [hy', map_mul, hψpowZ _ _ hyx, hψpow, hbN, one_mul]
    rfl

end Quaternion

section Conjugation

variable {R : Type*} [Group R]

theorem map_conj_map_conj (A : Subgroup R) (g h : R) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      A.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem map_conj_one (A : Subgroup R) : A.map (MulAut.conj (1 : R)).toMonoidHom = A := by
  ext x
  simp

@[expose] def conjPermOfInvariant (𝒜 : Set (Subgroup R))
    (h𝒜 : ∀ g : R, ∀ A ∈ 𝒜, A.map (MulAut.conj g).toMonoidHom ∈ 𝒜) : R →* Equiv.Perm 𝒜 where
  toFun g :=
    { toFun := fun A => ⟨A.1.map (MulAut.conj g).toMonoidHom, h𝒜 g A.1 A.2⟩
      invFun := fun A => ⟨A.1.map (MulAut.conj g⁻¹).toMonoidHom, h𝒜 g⁻¹ A.1 A.2⟩
      left_inv := fun A => Subtype.ext (by
        change (A.1.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A.1
        rw [map_conj_map_conj, inv_mul_cancel, map_conj_one])
      right_inv := fun A => Subtype.ext (by
        change (A.1.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = A.1
        rw [map_conj_map_conj, mul_inv_cancel, map_conj_one]) }
  map_one' := Equiv.ext fun A => Subtype.ext (map_conj_one A.1)
  map_mul' g h := Equiv.ext fun A => Subtype.ext (by
    change A.1.map (MulAut.conj (g * h)).toMonoidHom =
      (A.1.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom
    rw [map_conj_map_conj])

theorem conjPermOfInvariant_apply (𝒜 : Set (Subgroup R))
    (h𝒜 : ∀ g : R, ∀ A ∈ 𝒜, A.map (MulAut.conj g).toMonoidHom ∈ 𝒜) (g : R) (A : 𝒜) :
    ((conjPermOfInvariant 𝒜 h𝒜 g A : 𝒜) : Subgroup R) = A.1.map (MulAut.conj g).toMonoidHom :=
  rfl

@[expose] def threeCoreInverseImage (P : Subgroup R) [P.Normal] : Subgroup R :=
  (CFSG.pCore 3 (R ⧸ P)).comap (QuotientGroup.mk' P)

theorem threeCoreInverseImage_characteristic (P : Subgroup R) [P.Characteristic] :
    (threeCoreInverseImage P).Characteristic := by
  rw [characteristic_iff_comap_eq]
  intro φ
  have hφP : P.map (φ : R →* R) = P := characteristic_iff_map_eq.mp inferInstance φ
  let φbar : (R ⧸ P) ≃* (R ⧸ P) := QuotientGroup.congr P P φ hφP
  have hcomp : (QuotientGroup.mk' P).comp φ.toMonoidHom =
      φbar.toMonoidHom.comp (QuotientGroup.mk' P) := by
    ext x
    rfl
  unfold threeCoreInverseImage
  rw [Subgroup.comap_comap, hcomp, ← Subgroup.comap_comap,
    characteristic_iff_comap_eq.mp inferInstance φbar]

theorem map_normal_of_characteristic {J : Subgroup R} [J.Characteristic] {H : Type*} [Group H]
    (ι : R →* H) (hι : Function.Injective ι) (hn : ι.range.Normal) : (J.map ι).Normal := by
  let e : R ≃* ι.range := MonoidHom.ofInjective hι
  let K : Subgroup ι.range := J.map e.toMonoidHom
  have hK : K.Characteristic := by
    rw [characteristic_iff_map_eq]
    intro ψ
    have h1 : J.map (e.trans (ψ.trans e.symm)).toMonoidHom = J :=
      characteristic_iff_map_eq.mp inferInstance _
    calc K.map ψ.toMonoidHom =
          (J.map (e.trans (ψ.trans e.symm)).toMonoidHom).map e.toMonoidHom := by
          simp only [K, Subgroup.map_map]
          congr 1
          ext x
          simp
      _ = K := by rw [h1]
  have hmap : K.map ι.range.subtype = J.map ι := by
    simp only [K, Subgroup.map_map]
    congr 1
  rw [← hmap]
  exact ConjAct.normal_of_characteristic_of_normal

end Conjugation

@[expose] noncomputable def finiteAlternatingGroup (α : Type*) [Finite α] :
    Subgroup (Equiv.Perm α) :=
  @alternatingGroup α (Fintype.ofFinite α) (Classical.decEq α)

theorem eq_finiteAlternatingGroup_of_card_eq_three {α : Type*} [Finite α]
    (hα : Nat.card α = 3) {H : Subgroup (Equiv.Perm α)} (hH : Nat.card H = 3) :
    H = finiteAlternatingGroup α := by
  classical
  let : Fintype α := Fintype.ofFinite α
  have hnt : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hle : H ≤ finiteAlternatingGroup α := by
    intro σ hσ
    have h3 : σ ^ 3 = 1 := by
      have := pow_card_eq_one (G := H) (x := ⟨σ, hσ⟩)
      rw [Fintype.card_eq_nat_card, hH] at this
      exact congrArg Subtype.val this
    show σ ∈ @alternatingGroup α (Fintype.ofFinite α) (Classical.decEq α)
    rw [Equiv.Perm.mem_alternatingGroup]
    have hs : Equiv.Perm.sign σ ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · exact h
    · rw [h] at hs
      exact absurd hs (by decide)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hH]
  have : Nat.card (finiteAlternatingGroup α) = (Nat.card α).factorial / 2 := by
    show Nat.card (@alternatingGroup α (Fintype.ofFinite α) (Classical.decEq α)) = _
    exact nat_card_alternatingGroup
  rw [this, hα]
  decide

theorem isPGroup_of_centralizer_le_of_isPGroup_mulAut {R : Type*} [Group R] {N : Subgroup R}
    [N.Normal] (hN : IsPGroup 2 N) (hC : centralizer (N : Set R) ≤ N)
    (hA : IsPGroup 2 (MulAut N)) : IsPGroup 2 R := by
  intro g
  obtain ⟨a, ha⟩ := hA (MulAut.conjNormal g)
  have hmem : g ^ 2 ^ a ∈ centralizer (N : Set R) := by
    rw [mem_centralizer_iff]
    intro n hn
    have h := congrArg (fun σ : MulAut N => ((σ ⟨n, hn⟩ : N) : R)) ha
    simp only [← map_pow, MulAut.conjNormal_apply, MulAut.one_apply] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  obtain ⟨b, hb⟩ := hN ⟨g ^ 2 ^ a, hC hmem⟩
  refine ⟨a + b, ?_⟩
  rw [pow_add, pow_mul]
  exact congrArg Subtype.val hb

theorem quaternionGroup_not_commute {m : ℕ} (hm : 2 ≤ m) :
    (QuaternionGroup.a 1 : QuaternionGroup m) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
  rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a, ne_eq, QuaternionGroup.xa.injEq,
    zero_sub, zero_add, neg_eq_iff_add_eq_zero, ← two_mul]
  intro h
  have h2 : ((2 : ℕ) : ZMod (2 * m)) = 0 := by exact_mod_cast (mul_one (2 : ZMod (2 * m))) ▸ h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem solvable_quaternion_two_core {R : Type*} [Group R] [Finite R] [Group.IsSolvable R]
    (hO : CFSG.pPrimeCore 2 R = ⊥) (S : Sylow 2 R) {r : ℕ} (hr : 3 ≤ r)
    (eS : (S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2))) :
    CFSG.fittingSubgroup R = CFSG.pCore 2 R ∧
    centralizer (CFSG.pCore 2 R : Set R) ≤ CFSG.pCore 2 R ∧
    ∃ t : R, t ∈ CFSG.pCore 2 R ∧ orderOf t = 2 ∧ (∀ u : R, orderOf u = 2 → u = t) ∧
      (∃ k : ℕ, 1 ≤ k ∧ Nonempty (CFSG.pCore 2 R ≃* QuaternionGroup (2 ^ k))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.pCore 2 R with hPdef
  have hF : CFSG.fittingSubgroup R = P := CFSG.Fitting_eq_pcore R 2 hO
  have hCP : centralizer (P : Set R) ≤ P := by
    have := CFSG.RankThree.PGroups.solvable_fitting_self_centralizing R
    rwa [hF] at this
  have hPp : IsPGroup 2 P := CFSG.pCore_isPGroup
  have hm : 2 ≤ 2 ^ (r - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hne : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  have hSnc : ¬ ∀ u v : (S : Subgroup R), u * v = v * u := by
    intro h
    apply quaternionGroup_not_commute hm
    have := h (eS.symm (QuaternionGroup.a 1)) (eS.symm (QuaternionGroup.xa 0))
    simpa [← map_mul] using congrArg eS this
  have hPne : P ≠ ⊥ := by
    intro hP
    apply hSnc
    intro u v
    have htop : (⊤ : Subgroup R) ≤ ⊥ := by
      calc (⊤ : Subgroup R) = centralizer (P : Set R) := by
            rw [hP, Subgroup.coe_bot]
            exact (Subgroup.centralizer_eq_top_iff_subset.mpr
              (Set.singleton_subset_iff.mpr (one_mem _))).symm
        _ ≤ P := hCP
        _ = ⊥ := hP
    have h1 : (u : R) = 1 := (Subgroup.mem_bot).mp (htop (mem_top _))
    have h2 : (v : R) = 1 := (Subgroup.mem_bot).mp (htop (mem_top _))
    have hu1 : u = 1 := Subtype.ext (by rw [h1]; rfl)
    have hv1 : v = 1 := Subtype.ext (by rw [h2]; rfl)
    rw [hu1, hv1]
  have hTuniq : ∀ T : Sylow 2 R, ∀ u v : R, u ∈ (T : Subgroup R) → v ∈ (T : Subgroup R) →
      orderOf u = 2 → orderOf v = 2 → u = v := by
    intro T u v hu hv hou hov
    let f : (T : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)) := (Sylow.equiv T S).trans eS
    have h1 := (CFSG.Semidihedral.QuaternionAutomorphismLifting.unique_involution (2 ^ (r - 2))
      (by positivity) (f ⟨u, hu⟩)).mp (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hou)
    have h2 := (CFSG.Semidihedral.QuaternionAutomorphismLifting.unique_involution (2 ^ (r - 2))
      (by positivity) (f ⟨v, hv⟩)).mp (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hov)
    exact congrArg Subtype.val (f.injective (h1.trans h2.symm))
  have hinT : ∀ u : R, orderOf u = 2 → ∃ T : Sylow 2 R, u ∈ (T : Subgroup R) ∧
      P ≤ (T : Subgroup R) := by
    intro u hu
    have hzp : IsPGroup 2 (zpowers u) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
    obtain ⟨T, hT⟩ := hzp.exists_le_sylow
    refine ⟨T, hT (mem_zpowers u), ?_⟩
    have hsup : IsPGroup 2 (P ⊔ (T : Subgroup R) : Subgroup R) :=
      hPp.to_sup_of_normal_left T.isPGroup'
    have := T.is_maximal' hsup le_sup_right
    rw [← this]
    exact le_sup_left
  obtain ⟨n, hn⟩ := hPp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hPne (Subgroup.eq_bot_of_card_eq P (by rw [hn, pow_zero]))
  obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' (G := P) 2
    (by rw [hn]; exact dvd_pow_self 2 hn0)
  have ht : orderOf (t₀ : R) = 2 := by rw [Subgroup.orderOf_coe]; exact ht₀
  have huniq : ∀ u : R, orderOf u = 2 → u = t₀ := by
    intro u hu
    obtain ⟨T, huT, hPT⟩ := hinT u hu
    exact hTuniq T u t₀ huT (hPT t₀.2) hu ht
  have hrank : CFSG.pRank 2 P ≤ 1 :=
    CFSG.ComponentClassification.UnbalancedAltSeven.pRank_le_one_of_unique (z := t₀) ht₀
      (fun y hy => Subtype.ext (huniq y (by rw [Subgroup.orderOf_coe]; exact hy)))
  refine ⟨hF, hCP, t₀, t₀.2, ht, huniq, ?_⟩
  rcases (CFSG.LocalAnalysis.ComponentInitial.pgroup_rank_one_classification Nat.prime_two
    hPp).mp hrank with hcyc | ⟨-, n', hn', ⟨eP⟩⟩
  · exfalso
    have hA := CFSG.TwoRankLowerBound.Helpers.cyclic_two_group_automorphisms_isPGroup P hPp
    have hR := isPGroup_of_centralizer_le_of_isPGroup_mulAut hPp hCP hA
    have hPtop : (⊤ : Subgroup R) ≤ P := le_sSup ⟨inferInstance, hR.to_subgroup ⊤⟩
    have hSc : IsCyclic (S : Subgroup R) :=
      isCyclic_of_injective (Subgroup.inclusion (le_top.trans hPtop))
        (Subgroup.inclusion_injective _)
    apply hSnc
    intro u v
    exact (IsMulCommutative.is_comm (M := (S : Subgroup R))).comm u v
  · exact ⟨n' - 2, by omega, ⟨eP⟩⟩

theorem solvable_quaternion_centers {R : Type*} [Group R] {P : Subgroup R} {t : R}
    (htP : t ∈ P) (ht : orderOf t = 2) (huniq : ∀ u : R, orderOf u = 2 → u = t)
    (hCP : centralizer (P : Set R) ≤ P) {k : ℕ} (hk : 1 ≤ k) (e : P ≃* QuaternionGroup (2 ^ k)) :
    centralizer (P : Set R) = zpowers t ∧ (center P).map P.subtype = zpowers t ∧
      center R = zpowers t ∧ ∃ x y : P, x * y ≠ y * x := by
  have hm : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hne : NeZero (2 ^ k) := ⟨by positivity⟩
  have htc : ∀ g : R, g * t = t * g := by
    intro g
    have h := MulEquiv.orderOf_eq (MulAut.conj g) t
    rw [MulAut.conj_apply, ht] at h
    have h2 := huniq _ h
    exact (mul_inv_eq_iff_eq_mul.mp h2)
  have hcenterP : ∀ g : P, g ∈ center P → (g : R) = 1 ∨ (g : R) = t := by
    intro g hg
    have heg : e g ∈ center (QuaternionGroup (2 ^ k)) := by
      rw [mem_center_iff]
      intro h
      have := mem_center_iff.mp hg (e.symm h)
      have := congrArg e this
      simpa [map_mul] using this
    rcases ((CFSG.GroupTheory.quaternion_centralizers hm).2.2.1 (e g)).mp heg with h | h
    · left
      have : g = 1 := e.injective (by rw [h, map_one, QuaternionGroup.a_zero])
      rw [this]
      rfl
    · right
      apply huniq
      have h2 : orderOf (e g) = 2 :=
        (CFSG.Semidihedral.QuaternionAutomorphismLifting.unique_involution (2 ^ k)
          (by positivity) (e g)).mpr h
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe] at h2
      exact h2
  have htZ : (⟨t, htP⟩ : P) ∈ center P := by
    rw [mem_center_iff]
    intro h
    exact Subtype.ext (htc h)
  have hZ : (center P).map P.subtype = zpowers t := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      rcases hcenterP g hg with h | h
      · change (g : R) ∈ zpowers t
        rw [h]
        exact one_mem _
      · change (g : R) ∈ zpowers t
        rw [h]
        exact mem_zpowers t
    · exact zpowers_le.mpr ⟨⟨t, htP⟩, htZ, rfl⟩
  have hC : centralizer (P : Set R) = zpowers t := by
    apply le_antisymm
    · intro g hg
      have hgP : g ∈ P := hCP hg
      rw [← hZ]
      refine ⟨⟨g, hgP⟩, ?_, rfl⟩
      change (⟨g, hgP⟩ : P) ∈ center P
      rw [mem_center_iff]
      intro h
      exact Subtype.ext (mem_centralizer_iff.mp hg h h.2)
    · exact zpowers_le.mpr (mem_centralizer_iff.mpr fun h _ => (htc h))
  refine ⟨hC, hZ, ?_, ?_⟩
  · apply le_antisymm
    · intro g hg
      rw [← hC]
      exact mem_centralizer_iff.mpr fun h _ => (mem_center_iff.mp hg h)
    · exact zpowers_le.mpr (mem_center_iff.mpr fun g => htc g)
  · refine ⟨e.symm (QuaternionGroup.a 1), e.symm (QuaternionGroup.xa 0), fun h => ?_⟩
    apply quaternionGroup_not_commute hm
    have := congrArg e h
    simpa [map_mul] using this

section QuaternionEight

open QuaternionGroup

theorem quaternionEight_pow_four : ∀ g : QuaternionGroup 2, g ^ 4 = 1 := by decide

theorem quaternionEight_conj_inv : ∀ g h : QuaternionGroup 2, g ^ 2 ≠ 1 → h ^ 2 ≠ 1 → h ≠ g →
    h ≠ g⁻¹ → h * g * h⁻¹ = g⁻¹ := by
  decide

theorem quaternionEight_third_axis : ∀ g h k : QuaternionGroup 2, g ^ 2 ≠ 1 → h ^ 2 ≠ 1 →
    k ^ 2 ≠ 1 → h ≠ g → h ≠ g⁻¹ → k ≠ g → k ≠ g⁻¹ → k ≠ h → k ≠ h⁻¹ →
      k = g * h ∨ k = (g * h)⁻¹ := by
  decide

theorem quaternionEight_generators :
    (a 1 : QuaternionGroup 2) ^ 2 ≠ 1 ∧ (xa 0 : QuaternionGroup 2) ^ 2 ≠ 1 ∧
      (a 1 * xa 0 : QuaternionGroup 2) ^ 2 ≠ 1 ∧ (xa 0 : QuaternionGroup 2) ≠ a 1 ∧
      (xa 0 : QuaternionGroup 2) ≠ (a 1)⁻¹ ∧ (a 1 * xa 0 : QuaternionGroup 2) ≠ a 1 ∧
      (a 1 * xa 0 : QuaternionGroup 2) ≠ (a 1)⁻¹ ∧ (a 1 * xa 0 : QuaternionGroup 2) ≠ xa 0 ∧
      (a 1 * xa 0 : QuaternionGroup 2) ≠ (xa 0)⁻¹ := by
  decide

variable {R : Type*} [Group R] {P : Subgroup R}

theorem sq_ne_one_iff_of_mulEquiv {Q : Type*} [Group Q] (e : P ≃* Q) (g : P) :
    e g ^ 2 ≠ 1 ↔ g ^ 2 ≠ 1 := by
  rw [← map_pow, ne_eq, ne_eq, MulEquiv.map_eq_one_iff]

theorem pow_four_of_mulEquiv_quaternionEight (e : P ≃* QuaternionGroup 2) {g : R}
    (hg : g ∈ P) : g ^ 4 = 1 := by
  have h := quaternionEight_pow_four (e ⟨g, hg⟩)
  rw [← map_pow, MulEquiv.map_eq_one_iff] at h
  exact congrArg Subtype.val h

theorem conj_inv_of_mulEquiv_quaternionEight (e : P ≃* QuaternionGroup 2) {g h : R}
    (hg : g ∈ P) (hh : h ∈ P) (hg2 : g ^ 2 ≠ 1) (hh2 : h ^ 2 ≠ 1) (h1 : h ≠ g) (h2 : h ≠ g⁻¹) :
    h * g * h⁻¹ = g⁻¹ := by
  have hg2' : (⟨g, hg⟩ : P) ^ 2 ≠ 1 := fun hc => hg2 (by simpa using congrArg Subtype.val hc)
  have hh2' : (⟨h, hh⟩ : P) ^ 2 ≠ 1 := fun hc => hh2 (by simpa using congrArg Subtype.val hc)
  have h1' : (⟨h, hh⟩ : P) ≠ ⟨g, hg⟩ := fun hc => h1 (congrArg Subtype.val hc)
  have h2' : (⟨h, hh⟩ : P) ≠ (⟨g, hg⟩ : P)⁻¹ := fun hc => h2 (congrArg Subtype.val hc)
  have := quaternionEight_conj_inv (e ⟨g, hg⟩) (e ⟨h, hh⟩)
    ((sq_ne_one_iff_of_mulEquiv e _).mpr hg2') ((sq_ne_one_iff_of_mulEquiv e _).mpr hh2')
    (e.injective.ne h1') (by rw [← map_inv]; exact e.injective.ne h2')
  rw [← map_inv, ← map_mul, ← map_mul, ← map_inv] at this
  exact congrArg Subtype.val (e.injective this)

theorem third_axis_of_mulEquiv_quaternionEight (e : P ≃* QuaternionGroup 2) {g h k : R}
    (hg : g ∈ P) (hh : h ∈ P) (hk : k ∈ P) (hg2 : g ^ 2 ≠ 1) (hh2 : h ^ 2 ≠ 1)
    (hk2 : k ^ 2 ≠ 1) (h1 : h ≠ g) (h2 : h ≠ g⁻¹) (h3 : k ≠ g) (h4 : k ≠ g⁻¹) (h5 : k ≠ h)
    (h6 : k ≠ h⁻¹) : k = g * h ∨ k = (g * h)⁻¹ := by
  have sq : ∀ {z : R} (hz : z ∈ P), z ^ 2 ≠ 1 → e ⟨z, hz⟩ ^ 2 ≠ 1 := fun hz hz2 =>
    (sq_ne_one_iff_of_mulEquiv e _).mpr fun hc => hz2 (by simpa using congrArg Subtype.val hc)
  have ne : ∀ {z w : R} (hz : z ∈ P) (hw : w ∈ P), z ≠ w → e ⟨z, hz⟩ ≠ e ⟨w, hw⟩ :=
    fun hz hw hzw => e.injective.ne fun hc => hzw (congrArg Subtype.val hc)
  have ne' : ∀ {z w : R} (hz : z ∈ P) (hw : w ∈ P), z ≠ w⁻¹ → e ⟨z, hz⟩ ≠ (e ⟨w, hw⟩)⁻¹ :=
    fun hz hw hzw => by
      rw [← map_inv]
      exact e.injective.ne fun hc => hzw (congrArg Subtype.val hc)
  rcases quaternionEight_third_axis (e ⟨g, hg⟩) (e ⟨h, hh⟩) (e ⟨k, hk⟩) (sq hg hg2) (sq hh hh2)
    (sq hk hk2) (ne hh hg h1) (ne' hh hg h2) (ne hk hg h3) (ne' hk hg h4) (ne hk hh h5)
    (ne' hk hh h6) with hc | hc
  · left
    rw [← map_mul] at hc
    exact congrArg Subtype.val (e.injective hc)
  · right
    rw [← map_mul, ← map_inv] at hc
    exact congrArg Subtype.val (e.injective hc)

end QuaternionEight

section Axes

variable {R : Type*} [Group R]

@[expose] def cyclicOrderFourSubgroups (P : Subgroup R) : Set (Subgroup R) :=
  {A | A ≤ P ∧ IsCyclic A ∧ Nat.card A = 4}

theorem map_conj_mem_cyclicOrderFourSubgroups {P : Subgroup R} [P.Normal] (g : R)
    {A : Subgroup R} (hA : A ∈ cyclicOrderFourSubgroups P) :
    A.map (MulAut.conj g).toMonoidHom ∈ cyclicOrderFourSubgroups P := by
  obtain ⟨hAP, hcyc, hcard⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (inferInstance : P.Normal).conj_mem y (hAP hy) g
  · exact isCyclic_of_surjective
      (A.equivMapOfInjective _ (MulAut.conj g).injective).toMonoidHom
      (A.equivMapOfInjective _ (MulAut.conj g).injective).surjective
  · rw [card_map_of_injective (MulAut.conj g).injective]
    exact hcard

theorem orderOf_eq_four_of_sq_ne_one {g : R} (hg4 : g ^ 4 = 1) (hg2 : g ^ 2 ≠ 1) :
    orderOf g = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using hg2) (by simpa using hg4)

theorem eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_four [Finite R] {g h : R}
    (hg : orderOf g = 4) (hh : h ∈ zpowers g) (hh2 : h ^ 2 ≠ 1) : h = g ∨ h = g⁻¹ := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hg] at hh
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hh
  have hg4 : g ^ 4 = 1 := hg ▸ pow_orderOf_eq_one g
  rw [Finset.mem_range] at hn
  interval_cases n
  · exact absurd (by simp) hh2
  · left
    exact pow_one g
  · exact absurd (by rw [← pow_mul]; exact hg4) hh2
  · right
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hg4

theorem card_cyclicOrderFourSubgroups [Finite R] {P : Subgroup R}
    (e : P ≃* QuaternionGroup 2) : Nat.card (cyclicOrderFourSubgroups P) = 3 := by
  have hsq : ∀ q : QuaternionGroup 2, ((e.symm q : P) : R) ^ 2 = ((e.symm (q ^ 2) : P) : R) :=
    fun q => by rw [map_pow]; rfl
  have hone : ∀ q : QuaternionGroup 2, ((e.symm q : P) : R) = 1 ↔ q = 1 := fun q => by
    rw [OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff]
  have hcoe : ∀ q q' : QuaternionGroup 2, ((e.symm q : P) : R) = (e.symm q' : P) ↔ q = q' :=
    fun q q' => by rw [SetLike.coe_eq_coe, e.symm.injective.eq_iff]
  have hinv : ∀ q : QuaternionGroup 2, ((e.symm q : P) : R)⁻¹ = ((e.symm q⁻¹ : P) : R) :=
    fun q => by rw [map_inv]; rfl
  have hmul : ∀ q q' : QuaternionGroup 2,
      ((e.symm q : P) : R) * (e.symm q' : P) = ((e.symm (q * q') : P) : R) :=
    fun q q' => by rw [map_mul]; rfl
  set x : R := ((e.symm (QuaternionGroup.a 1) : P) : R) with hx
  set y : R := ((e.symm (QuaternionGroup.xa 0) : P) : R) with hy
  obtain ⟨gx, gy, gxy, g1, g2, g3, g4, g5, g6⟩ := quaternionEight_generators
  have hxP : x ∈ P := (e.symm _).2
  have hyP : y ∈ P := (e.symm _).2
  have hxyP : x * y ∈ P := P.mul_mem hxP hyP
  have hx2 : x ^ 2 ≠ 1 := by rw [hx, hsq, ne_eq, hone]; exact gx
  have hy2 : y ^ 2 ≠ 1 := by rw [hy, hsq, ne_eq, hone]; exact gy
  have hxy2 : (x * y) ^ 2 ≠ 1 := by rw [hx, hy, hmul, hsq, ne_eq, hone]; exact gxy
  have hyx : y ≠ x := by rw [hx, hy, ne_eq, hcoe]; exact g1
  have hyx' : y ≠ x⁻¹ := by rw [hx, hy, hinv, ne_eq, hcoe]; exact g2
  have hxyx : x * y ≠ x := by rw [hx, hy, hmul, ne_eq, hcoe]; exact g3
  have hxyx' : x * y ≠ x⁻¹ := by rw [hx, hy, hmul, hinv, ne_eq, hcoe]; exact g4
  have hxyy : x * y ≠ y := by rw [hx, hy, hmul, ne_eq, hcoe]; exact g5
  have hxyy' : x * y ≠ y⁻¹ := by rw [hx, hy, hmul, hinv, ne_eq, hcoe]; exact g6
  have hP4 : ∀ g ∈ P, g ^ 4 = 1 := fun g hg => pow_four_of_mulEquiv_quaternionEight e hg
  have hord : ∀ g ∈ P, g ^ 2 ≠ 1 → orderOf g = 4 := fun g hg hg2 =>
    orderOf_eq_four_of_sq_ne_one (hP4 g hg) hg2
  have hmem : ∀ g ∈ P, g ^ 2 ≠ 1 → zpowers g ∈ cyclicOrderFourSubgroups P :=
    fun g hg hg2 => ⟨zpowers_le.mpr hg, inferInstance, by rw [Nat.card_zpowers, hord g hg hg2]⟩
  have hne : ∀ g h : R, orderOf g = 4 → h ^ 2 ≠ 1 → h ≠ g → h ≠ g⁻¹ → zpowers g ≠ zpowers h := by
    intro g h hg hh2 h1 h2 heq
    rcases eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_four hg (heq ▸ mem_zpowers h) hh2
      with h3 | h3
    · exact h1 h3
    · exact h2 h3
  have hset : cyclicOrderFourSubgroups P = {zpowers x, zpowers y, zpowers (x * y)} := by
    ext A
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hAP, hcyc, hcard⟩
      obtain ⟨g₀, hg₀⟩ := hcyc.exists_generator
      have hA : A = zpowers (g₀ : R) := by
        ext z
        constructor
        · intro hz
          obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (hg₀ ⟨z, hz⟩)
          exact mem_zpowers_iff.mpr ⟨n, by rw [← Subgroup.coe_zpow, hn]⟩
        · intro hz
          obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hz
          exact zpow_mem g₀.2 n
      have hg₀4 : orderOf (g₀ : R) = 4 := by
        rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg₀, hcard]
      have hg₀2 : (g₀ : R) ^ 2 ≠ 1 := by
        intro h
        have := orderOf_le_of_pow_eq_one (by norm_num) h
        omega
      have hg₀P : (g₀ : R) ∈ P := hAP g₀.2
      by_cases h1 : (g₀ : R) = x
      · left; rw [hA, h1]
      by_cases h2 : (g₀ : R) = x⁻¹
      · left; rw [hA, h2, zpowers_inv]
      by_cases h3 : (g₀ : R) = y
      · right; left; rw [hA, h3]
      by_cases h4 : (g₀ : R) = y⁻¹
      · right; left; rw [hA, h4, zpowers_inv]
      right; right
      rcases third_axis_of_mulEquiv_quaternionEight e hxP hyP hg₀P hx2 hy2 hg₀2 hyx hyx' h1 h2
        h3 h4 with h5 | h5
      · rw [hA, h5]
      · rw [hA, h5, zpowers_inv]
    · rintro (rfl | rfl | rfl)
      · exact hmem x hxP hx2
      · exact hmem y hyP hy2
      · exact hmem (x * y) hxyP hxy2
  rw [Nat.card_coe_set_eq, hset, Set.ncard_eq_three]
  exact ⟨zpowers x, zpowers y, zpowers (x * y), hne x y (hord x hxP hx2) hy2 hyx hyx',
    hne x (x * y) (hord x hxP hx2) hxy2 hxyx hxyx', hne y (x * y) (hord y hyP hy2) hxy2 hxyy hxyy',
    rfl⟩

end Axes

section AxesAction

variable {R : Type*} [Group R]

theorem isPGroup_two_of_prime_orderOf_eq_one {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    (h : ∀ σ ∈ K, ∀ q : ℕ, q.Prime → q ≠ 2 → orderOf σ = q → σ = 1) : IsPGroup 2 K := by
  apply IsPGroup.of_card
  apply Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := K)).ne'
  intro q hq hdvd
  by_contra hne
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' q hdvd
  have h1 := h σ σ.2 q hq hne (by rw [Subgroup.orderOf_coe]; exact hσ)
  have h2 : σ = 1 := Subtype.ext h1
  rw [h2, orderOf_one] at hσ
  exact hq.one_lt.ne hσ

@[expose] def axisAction (P : Subgroup R) [P.Normal] :
    R →* Equiv.Perm (cyclicOrderFourSubgroups P) :=
  conjPermOfInvariant (cyclicOrderFourSubgroups P)
    (fun g _ hA => map_conj_mem_cyclicOrderFourSubgroups g hA)

theorem axisAction_apply (P : Subgroup R) [P.Normal] (g : R) (A : cyclicOrderFourSubgroups P) :
    ((axisAction P g A : cyclicOrderFourSubgroups P) : Subgroup R) =
      (A : Subgroup R).map (MulAut.conj g).toMonoidHom :=
  rfl

theorem axisAction_ker [Finite R] {P : Subgroup R} [P.Normal] (hPc : P = CFSG.pCore 2 R)
    (e : P ≃* QuaternionGroup 2) {t : R} (huniq : ∀ u : R, orderOf u = 2 → u = t)
    (hC : centralizer (P : Set R) = zpowers t) (ht : orderOf t = 2) :
    (axisAction P).ker = P := by
  have hP8 : Nat.card P = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hP4 : ∀ g ∈ P, g ^ 4 = 1 := fun g hg => pow_four_of_mulEquiv_quaternionEight e hg
  have hord : ∀ g ∈ P, g ^ 2 ≠ 1 → orderOf g = 4 := fun g hg hg2 =>
    orderOf_eq_four_of_sq_ne_one (hP4 g hg) hg2
  have hmem : ∀ g ∈ P, g ^ 2 ≠ 1 → zpowers g ∈ cyclicOrderFourSubgroups P :=
    fun g hg hg2 => ⟨zpowers_le.mpr hg, inferInstance, by rw [Nat.card_zpowers, hord g hg hg2]⟩
  have htc : ∀ g : R, g * t = t * g := by
    intro g
    have h := MulEquiv.orderOf_eq (MulAut.conj g) t
    rw [MulAut.conj_apply, ht] at h
    exact mul_inv_eq_iff_eq_mul.mp (huniq _ h)
  apply le_antisymm
  · have hK : IsPGroup 2 (axisAction P).ker := by
      refine isPGroup_two_of_prime_orderOf_eq_one fun k hk q hq hq2 hkq => ?_
      have hqodd : Odd q := hq.odd_of_ne_two hq2
      have hkq1 : k ^ q = 1 := hkq ▸ pow_orderOf_eq_one k
      have hkP : k ∈ centralizer (P : Set R) := by
        rw [mem_centralizer_iff]
        intro g hg
        by_cases hg2 : g ^ 2 = 1
        · by_cases hg1 : g = 1
          · rw [hg1, one_mul, mul_one]
          · rw [huniq g (orderOf_eq_prime hg2 hg1)]
            exact (htc k).symm
        · have hA := hmem g hg hg2
          have hfix : (zpowers g).map (MulAut.conj k).toMonoidHom = zpowers g := by
            have h := congrArg
              (fun σ : Equiv.Perm (cyclicOrderFourSubgroups P) =>
                ((σ ⟨zpowers g, hA⟩ : cyclicOrderFourSubgroups P) : Subgroup R))
              (MonoidHom.mem_ker.mp hk)
            exact h
          have hkg : k * g * k⁻¹ ∈ zpowers g := by
            rw [← hfix]
            exact ⟨g, mem_zpowers g, rfl⟩
          have hkg2 : (k * g * k⁻¹) ^ 2 ≠ 1 := by
            rw [conj_pow]
            intro h
            apply hg2
            have h' : k * g ^ 2 = k := by
              calc k * g ^ 2 = k * g ^ 2 * k⁻¹ * k := by group
                _ = k := by rw [h, one_mul]
            simpa using h'
          rcases eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_four (hord g hg hg2) hkg hkg2 with
            h | h
          · exact (mul_inv_eq_iff_eq_mul.mp h).symm
          · exfalso
            have hk2 : k ^ 2 * g = g * k ^ 2 := by
              have h1 : k * g = g⁻¹ * k := mul_inv_eq_iff_eq_mul.mp h
              have h2 : k * g⁻¹ = g * k := by
                have h3 : k * g⁻¹ * k⁻¹ = g := by
                  have := congrArg (·⁻¹) h
                  simpa [mul_assoc] using this
                calc k * g⁻¹ = k * g⁻¹ * k⁻¹ * k := by group
                  _ = g * k := by rw [h3]
              calc k ^ 2 * g = k * (k * g) := by rw [pow_two, mul_assoc]
                _ = k * (g⁻¹ * k) := by rw [h1]
                _ = (k * g⁻¹) * k := by rw [mul_assoc]
                _ = g * k ^ 2 := by rw [h2, mul_assoc, ← pow_two]
            obtain ⟨i, hi⟩ := hqodd
            have hci : Commute ((k ^ 2) ^ i) g := (show Commute (k ^ 2) g from hk2).pow_left i
            have hkey : k ^ q * g * (k ^ q)⁻¹ = g⁻¹ := by
              rw [hi, pow_succ, pow_mul]
              calc (k ^ 2) ^ i * k * g * ((k ^ 2) ^ i * k)⁻¹
                  = (k ^ 2) ^ i * (k * g * k⁻¹) * ((k ^ 2) ^ i)⁻¹ := by group
                _ = (k ^ 2) ^ i * g⁻¹ * ((k ^ 2) ^ i)⁻¹ := by rw [h]
                _ = g⁻¹ := by
                  rw [((hci.inv_right).eq), mul_assoc, mul_inv_cancel, mul_one]
            rw [hkq1, one_mul, inv_one, mul_one] at hkey
            apply hg2
            calc g ^ 2 = g * g := pow_two g
              _ = g * g⁻¹ := by rw [← hkey]
              _ = 1 := mul_inv_cancel g
      rw [hC] at hkP
      have hdvd : orderOf k ∣ 2 := ht ▸ orderOf_dvd_of_mem_zpowers hkP
      rw [hkq] at hdvd
      exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdvd) hq2
    have hle : (axisAction P).ker ≤ CFSG.pCore 2 R := le_sSup ⟨inferInstance, hK⟩
    exact hle.trans hPc.symm.le
  · intro p hp
    rw [MonoidHom.mem_ker]
    refine Equiv.ext fun A => Subtype.ext ?_
    change (A : Subgroup R).map (MulAut.conj p).toMonoidHom = A
    obtain ⟨hAP, -, hcard⟩ := A.2
    have hidx : ((A : Subgroup R).subgroupOf P).index = 2 := by
      have h1 := Subgroup.card_mul_index ((A : Subgroup R).subgroupOf P)
      rw [Nat.card_congr (subgroupOfEquivOfLe hAP).toEquiv, hcard, hP8] at h1
      omega
    have hn := Subgroup.normal_of_index_eq_two hidx
    have hle : (A : Subgroup R).map (MulAut.conj p).toMonoidHom ≤ A := by
      rintro _ ⟨a, ha, rfl⟩
      have := hn.conj_mem ⟨a, hAP ha⟩ (mem_subgroupOf.mpr ha) ⟨p, hp⟩
      exact mem_subgroupOf.mp this
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_map_of_injective (MulAut.conj p).injective]

theorem axisAction_range [Finite R] {P : Subgroup R} [P.Normal] (hPc : P = CFSG.pCore 2 R)
    (e : P ≃* QuaternionGroup 2) {t : R} (huniq : ∀ u : R, orderOf u = 2 → u = t)
    (hC : centralizer (P : Set R) = zpowers t) (ht : orderOf t = 2) (hnot : ¬ IsPGroup 2 R) :
    Nat.card R = 8 * Nat.card (axisAction P).range ∧
      (Nat.card (axisAction P).range = 3 ∨ Nat.card (axisAction P).range = 6) ∧
      ((axisAction P).range = finiteAlternatingGroup (cyclicOrderFourSubgroups P) ∨
        (axisAction P).range = ⊤) := by
  have hP8 : Nat.card P = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hker := axisAction_ker hPc e huniq hC ht
  have hcard : Nat.card R = 8 * Nat.card (axisAction P).range := by
    rw [← Subgroup.index_ker, hker, ← hP8, Subgroup.card_mul_index]
  have h3 := card_cyclicOrderFourSubgroups e
  have hperm : Nat.card (Equiv.Perm (cyclicOrderFourSubgroups P)) = 6 := by
    rw [Nat.card_perm, h3]
    rfl
  have hdvd : Nat.card (axisAction P).range ∣ 6 :=
    hperm ▸ Subgroup.card_subgroup_dvd_card _
  have h36 : Nat.card (axisAction P).range = 3 ∨ Nat.card (axisAction P).range = 6 := by
    have hcases : ∀ n : ℕ, n ∣ 6 → n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6 := by
      intro n hn
      have := Nat.le_of_dvd (by norm_num) hn
      interval_cases n <;> simp_all
    rcases hcases _ hdvd with h | h | h | h
    · exact absurd (IsPGroup.of_card (n := 3) (by rw [hcard, h]; norm_num)) hnot
    · exact absurd (IsPGroup.of_card (n := 4) (by rw [hcard, h]; norm_num)) hnot
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨hcard, h36, ?_⟩
  rcases h36 with h | h
  · exact Or.inl (eq_finiteAlternatingGroup_of_card_eq_three
      (by rw [Nat.card_coe_set_eq] at h3 ⊢; exact h3) h)
  · exact Or.inr (Subgroup.eq_top_of_card_eq _ (by rw [h, hperm]))

end AxesAction

section ThreeCore

variable {R : Type*} [Group R]

theorem threeCoreInverseImage_facts [Finite R] {P : Subgroup R} [P.Normal]
    (hP8 : Nat.card P = 8) (hQ : Nat.card (R ⧸ P) = 3 ∨ Nat.card (R ⧸ P) = 6) :
    Nat.card (threeCoreInverseImage P) = 24 ∧ (threeCoreInverseImage P).index ≤ 2 ∧
      P ≤ threeCoreInverseImage P ∧
      ∃ T : Sylow 2 (threeCoreInverseImage P),
        (T : Subgroup (threeCoreInverseImage P)).map (threeCoreInverseImage P).subtype = P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pCore 3 (R ⧸ P) with hO
  have h3dvd : 3 ^ 1 ∣ Nat.card (R ⧸ P) := by
    rcases hQ with h | h <;> rw [h] <;> norm_num
  obtain ⟨T₃, hT₃⟩ := Sylow.exists_subgroup_card_pow_prime 3 h3dvd
  have hT₃n : T₃.Normal := by
    have h1 := Subgroup.card_mul_index T₃
    rw [hT₃] at h1
    rcases hQ with h | h
    · have hidx : T₃.index = 1 := by rw [h] at h1; omega
      rw [Subgroup.index_eq_one] at hidx
      rw [hidx]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two (by rw [h] at h1; omega)
  have hT₃O : T₃ ≤ O := le_sSup ⟨hT₃n, IsPGroup.of_card hT₃⟩
  have hOcard : Nat.card O = 3 := by
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 3) (G := R ⧸ P)).exists_card_eq
    have hdvd : Nat.card O ∣ Nat.card (R ⧸ P) := Subgroup.card_subgroup_dvd_card O
    have hge : 3 ≤ Nat.card O := by
      calc 3 = 3 ^ 1 := by norm_num
        _ = Nat.card T₃ := hT₃.symm
        _ ≤ Nat.card O := Subgroup.card_le_of_le hT₃O
    rw [hj] at hdvd hge ⊢
    have hj1 : j ≤ 1 := by
      by_contra hj1
      have h9 : 3 ^ 2 ∣ 3 ^ j := pow_dvd_pow 3 (by omega)
      have := h9.trans hdvd
      rcases hQ with h | h <;> rw [h] at this <;> norm_num at this
    interval_cases j
    · norm_num at hge
    · rfl
  have hOidx : O.index * 3 = Nat.card (R ⧸ P) := by
    rw [← hOcard, mul_comm, Subgroup.card_mul_index]
  have hJidx : (threeCoreInverseImage P).index = O.index :=
    Subgroup.index_comap_of_surjective O (QuotientGroup.mk'_surjective P)
  have hR : Nat.card R = Nat.card (R ⧸ P) * 8 := by
    rw [← hP8, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have hJcard : Nat.card (threeCoreInverseImage P) = 24 := by
    have h1 := Subgroup.card_mul_index (threeCoreInverseImage P)
    rw [hJidx, hR, ← hOidx] at h1
    have hpos : 0 < O.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have h2 : Nat.card (threeCoreInverseImage P) * O.index = 24 * O.index := by
      rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  have hPJ : P ≤ threeCoreInverseImage P := by
    intro p hp
    change QuotientGroup.mk' P p ∈ O
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff p).mpr hp]
    exact one_mem _
  refine ⟨hJcard, ?_, hPJ, ?_⟩
  · rw [hJidx]
    rcases hQ with h | h <;> omega
  · have hP' : IsPGroup 2 (P.subgroupOf (threeCoreInverseImage P)) := IsPGroup.of_card (n := 3)
      (by rw [Nat.card_congr (subgroupOfEquivOfLe hPJ).toEquiv, hP8]; norm_num)
    have hidx : (P.subgroupOf (threeCoreInverseImage P)).index = 3 := by
      have h1 := Subgroup.card_mul_index (P.subgroupOf (threeCoreInverseImage P))
      rw [Nat.card_congr (subgroupOfEquivOfLe hPJ).toEquiv, hP8, hJcard] at h1
      omega
    refine ⟨hP'.toSylow (by rw [hidx]; norm_num), ?_⟩
    rw [IsPGroup.toSylow_coe, map_subgroupOf_eq_of_le hPJ]

end ThreeCore

section OddCore

variable {R : Type*} [Group R]

theorem pPrimeCore_two_eq_bot_of_centralizer [Finite R] {P J : Subgroup R} [P.Normal]
    (hPJ : P ≤ J) (hP2 : IsPGroup 2 P) {t : R} (ht : orderOf t = 2)
    (hC : centralizer (P : Set R) = zpowers t) : CFSG.pPrimeCore 2 J = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine sSup_eq_bot.mpr fun K ⟨hKn, hKc⟩ => ?_
  have hKodd : Odd (Nat.card K) := Nat.coprime_two_left.mp hKc
  have hcoprime : ∀ n ∈ K, ∀ j : ℕ, orderOf (n : R) ∣ 2 ^ j → n = 1 := by
    intro n hn j hj
    have h1 : orderOf n ∣ Nat.card K := by
      have := orderOf_dvd_natCard (⟨n, hn⟩ : K)
      rwa [Subgroup.orderOf_mk] at this
    have h2 : orderOf n ∣ 2 ^ j := by rwa [← Subgroup.orderOf_coe]
    have h3 : Nat.Coprime (2 ^ j) (Nat.card K) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hKodd)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 h3) h1)
  refine (Subgroup.eq_bot_iff_forall K).mpr fun n hn => ?_
  have hnC : (n : R) ∈ centralizer (P : Set R) := by
    rw [mem_centralizer_iff]
    intro p hp
    set p' : J := ⟨p, hPJ hp⟩
    set c : J := n * p' * n⁻¹ * p'⁻¹ with hc
    have hcK : c ∈ K := by
      have : p' * n⁻¹ * p'⁻¹ ∈ K := hKn.conj_mem _ (K.inv_mem hn) p'
      have h : c = n * (p' * n⁻¹ * p'⁻¹) := by rw [hc]; group
      rw [h]
      exact K.mul_mem hn this
    have hcP : (c : R) ∈ P := by
      have h1 : (n : R) * p * (n : R)⁻¹ ∈ P := (inferInstance : P.Normal).conj_mem p hp n
      have h : (c : R) = ((n : R) * p * (n : R)⁻¹) * p⁻¹ := by rw [hc]; rfl
      rw [h]
      exact P.mul_mem h1 (P.inv_mem hp)
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hP2 ⟨c, hcP⟩
    have hc1 := hcoprime c hcK j (by rw [← Subgroup.orderOf_mk (c : R) hcP, hj])
    have h : (n : R) * p * (n : R)⁻¹ * p⁻¹ = 1 := by
      have := congrArg Subtype.val hc1
      exact this
    have h' : (n : R) * p = p * n := by
      calc (n : R) * p = (n : R) * p * (n : R)⁻¹ * p⁻¹ * (p * n) := by group
        _ = p * n := by rw [h, one_mul]
    exact h'.symm
  rw [hC] at hnC
  exact hcoprime n hn 1 (by rw [pow_one, ← ht]; exact orderOf_dvd_of_mem_zpowers hnC)

end OddCore

section Triple

variable {R : Type*} [Group R]

theorem exists_quaternion_triple [Finite R] {P J : Subgroup R} [P.Normal]
    (e : P ≃* QuaternionGroup 2) {t : R} (ht : orderOf t = 2)
    (huniq : ∀ u : R, orderOf u = 2 → u = t) (hC : centralizer (P : Set R) = zpowers t)
    (hJ3 : 3 ∣ Nat.card J) :
    ∃ a x y : R, a ∈ J ∧ x ∈ P ∧ y ∈ P ∧ orderOf a = 3 ∧ x ^ 2 = t ∧ y ^ 2 = t ∧
      y * x * y⁻¹ = x⁻¹ ∧ a * x * a⁻¹ = y ∧ a * y * a⁻¹ = x * y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a₀, ha₀⟩ := exists_prime_orderOf_dvd_card' (G := J) 3 hJ3
  obtain ⟨a, haJ, ha3⟩ : ∃ a : R, a ∈ J ∧ orderOf a = 3 :=
    ⟨a₀, a₀.2, by rw [Subgroup.orderOf_coe]; exact ha₀⟩
  have ha3' : a ^ 3 = 1 := ha3 ▸ pow_orderOf_eq_one a
  have hP4 : ∀ g ∈ P, g ^ 4 = 1 := fun g hg => pow_four_of_mulEquiv_quaternionEight e hg
  have htc : ∀ g : R, g * t = t * g := by
    intro g
    have h := MulEquiv.orderOf_eq (MulAut.conj g) t
    rw [MulAut.conj_apply, ht] at h
    exact mul_inv_eq_iff_eq_mul.mp (huniq _ h)
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ← pow_two, ht2]
  have hsqt : ∀ g ∈ P, g ^ 2 ≠ 1 → g ^ 2 = t := by
    intro g hg hg2
    apply huniq
    apply orderOf_eq_prime _ hg2
    rw [← pow_mul]
    exact hP4 g hg
  obtain ⟨α, hα⟩ : ∃ α : R → R, ∀ g, α g = a * g * a⁻¹ := ⟨_, fun _ => rfl⟩
  have hαP : ∀ g ∈ P, α g ∈ P := fun g hg => by
    rw [hα]; exact (inferInstance : P.Normal).conj_mem g hg a
  have hαsq : ∀ g : R, g ^ 2 ≠ 1 → (α g) ^ 2 ≠ 1 := by
    intro g hg2 h
    apply hg2
    rw [hα, conj_pow] at h
    have h2 : g ^ 2 = a⁻¹ * (a * g ^ 2 * a⁻¹) * a := by group
    rw [h2, h, mul_one, inv_mul_cancel]
  have hαinj : ∀ g h : R, α g = α h → g = h := by
    intro g h hgh
    rw [hα, hα] at hgh
    have : a⁻¹ * (a * g * a⁻¹) * a = a⁻¹ * (a * h * a⁻¹) * a := by rw [hgh]
    simpa [mul_assoc] using this
  have hαinv : ∀ g : R, α g⁻¹ = (α g)⁻¹ := fun g => by rw [hα, hα]; group
  have hα3 : ∀ g : R, α (α (α g)) = g := by
    intro g
    rw [hα, hα, hα]
    calc a * (a * (a * g * a⁻¹) * a⁻¹) * a⁻¹ = a ^ 3 * g * (a ^ 3)⁻¹ := by
          rw [pow_three]; group
      _ = g := by rw [ha3', one_mul, inv_one, mul_one]
  obtain ⟨x, hxP, hx2, hxy1, hxy2⟩ : ∃ x ∈ P, x ^ 2 ≠ 1 ∧ α x ≠ x ∧ α x ≠ x⁻¹ := by
    by_contra hcon
    push Not at hcon
    have haC : a ∈ centralizer (P : Set R) := by
      rw [mem_centralizer_iff]
      intro g hg
      by_cases hg2 : g ^ 2 = 1
      · by_cases hg1 : g = 1
        · rw [hg1, one_mul, mul_one]
        · rw [huniq g (orderOf_eq_prime hg2 hg1)]
          exact (htc a).symm
      · have hαg : α g = g := by
          by_contra hne
          have h1 : α g = g⁻¹ := hcon g hg hg2 hne
          have h2 : α (α (α g)) = g⁻¹ := by
            rw [h1, hαinv g, h1, inv_inv, h1]
          rw [hα3] at h2
          apply hg2
          calc g ^ 2 = g * g := pow_two g
            _ = g * g⁻¹ := by rw [← h2]
            _ = 1 := mul_inv_cancel g
        rw [hα] at hαg
        exact (mul_inv_eq_iff_eq_mul.mp hαg).symm
    rw [hC] at haC
    have hdvd : orderOf a ∣ 2 := ht ▸ orderOf_dvd_of_mem_zpowers haC
    rw [ha3] at hdvd
    norm_num at hdvd
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, y₀ = α x := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = α y₀ := ⟨_, rfl⟩
  rw [← hy₀] at hxy1 hxy2
  have hy₀P : y₀ ∈ P := hy₀ ▸ hαP x hxP
  have hzP : z ∈ P := hz ▸ hαP y₀ hy₀P
  have hy₀2 : y₀ ^ 2 ≠ 1 := hy₀ ▸ hαsq x hx2
  have hz2 : z ^ 2 ≠ 1 := hz ▸ hαsq y₀ hy₀2
  have hzy : z ≠ y₀ := fun h => hxy1 (hαinj _ _ (by rw [← hy₀, ← hz, h]))
  have hzy' : z ≠ y₀⁻¹ := fun h => hxy2 (hαinj _ _ (by rw [← hz, h, hy₀, hαinv]))
  have hzx : z ≠ x := fun h => hxy1 (by
    have h1 : α (α (α x)) = α x := by rw [← hy₀, ← hz, h, ← hy₀]
    rw [hα3, ← hy₀] at h1
    exact h1.symm)
  have hzx' : z ≠ x⁻¹ := fun h => hxy2 (by
    have h1 : α (α (α x)) = α x⁻¹ := by rw [← hy₀, ← hz, h]
    rw [hα3, hαinv, ← hy₀] at h1
    rw [h1, inv_inv])
  have hanti : ∀ g h : R, g ∈ P → h ∈ P → g ^ 2 ≠ 1 → h ^ 2 ≠ 1 → h ≠ g → h ≠ g⁻¹ →
      h * g * h⁻¹ = g⁻¹ := fun g h hg hh hg2 hh2 h1 h2 =>
    conj_inv_of_mulEquiv_quaternionEight e hg hh hg2 hh2 h1 h2
  have hax : a * x * a⁻¹ = y₀ := by rw [hy₀, hα]
  have hay : a * y₀ * a⁻¹ = z := by rw [hz, hα]
  rcases third_axis_of_mulEquiv_quaternionEight e hxP hy₀P hzP hx2 hy₀2 hz2 hxy1 hxy2 hzx hzx'
    hzy hzy' with h | h
  · exact ⟨a, x, y₀, haJ, hxP, hy₀P, ha3, hsqt x hxP hx2, hsqt y₀ hy₀P hy₀2,
      hanti x y₀ hxP hy₀P hx2 hy₀2 hxy1 hxy2, hax, hay.trans h⟩
  · have hxinv2 : x⁻¹ ^ 2 ≠ 1 := by
      rw [inv_pow]; exact fun h => hx2 (inv_eq_one.mp h)
    have hyinv2 : y₀⁻¹ ^ 2 ≠ 1 := by
      rw [inv_pow]; exact fun h => hy₀2 (inv_eq_one.mp h)
    have hxt : x⁻¹ = x * t := by
      rw [← hsqt x hxP hx2, inv_eq_iff_mul_eq_one, ← pow_succ', ← pow_succ']
      exact hP4 x hxP
    have hyt : y₀⁻¹ = y₀ * t := by
      rw [← hsqt y₀ hy₀P hy₀2, inv_eq_iff_mul_eq_one, ← pow_succ', ← pow_succ']
      exact hP4 y₀ hy₀P
    refine ⟨a, x⁻¹, y₀⁻¹, haJ, P.inv_mem hxP, P.inv_mem hy₀P, ha3, ?_, ?_, ?_, ?_, ?_⟩
    · rw [inv_pow, hsqt x hxP hx2, htinv]
    · rw [inv_pow, hsqt y₀ hy₀P hy₀2, htinv]
    · exact hanti x⁻¹ y₀⁻¹ (P.inv_mem hxP) (P.inv_mem hy₀P) hxinv2 hyinv2
        (fun h' => hxy1 (inv_injective h'))
        (fun h' => hxy2 (by rw [inv_inv] at h'; rw [← h', inv_inv]))
    · rw [← hax]; group
    · have h1 : a * y₀⁻¹ * a⁻¹ = z⁻¹ := by rw [← hay]; group
      rw [h1, h, inv_inv, hxt, hyt]
      calc x * y₀ = x * y₀ * (t * t) := by rw [← pow_two, ht2, mul_one]
        _ = x * (y₀ * t) * t := by group
        _ = x * (t * y₀) * t := by rw [htc y₀]
        _ = x * t * (y₀ * t) := by group

end Triple

section Psi

open QuaternionGroup

variable {R : Type*} [Group R]

theorem quaternionEight_closure_eq_top :
    closure ({a 1, xa 0} : Set (QuaternionGroup 2)) = ⊤ := by
  rw [eq_top_iff]
  rintro g -
  have h1 : (a 1 : QuaternionGroup 2) ∈ closure ({a 1, xa 0} : Set (QuaternionGroup 2)) :=
    subset_closure (by simp)
  have h2 : (xa 0 : QuaternionGroup 2) ∈ closure ({a 1, xa 0} : Set (QuaternionGroup 2)) :=
    subset_closure (by simp)
  cases g with
  | a i =>
    have : (a i : QuaternionGroup 2) = a 1 ^ i.val := by rw [a_one_pow, ZMod.natCast_zmod_val]
    rw [this]
    exact pow_mem h1 _
  | xa i =>
    have : (xa i : QuaternionGroup 2) = xa 0 * a 1 ^ i.val := by
      rw [a_one_pow, ZMod.natCast_zmod_val, xa_mul_a, zero_add]
    rw [this]
    exact mul_mem h2 (pow_mem h1 _)

theorem exists_mulEquiv_slTwoThree [Finite R] {P J : Subgroup R} [P.Normal] (hPJ : P ≤ J)
    (hP8 : Nat.card P = 8) (hJ24 : Nat.card J = 24) {t a x y : R} (haJ : a ∈ J) (hxP : x ∈ P)
    (hyP : y ∈ P) (ha3 : orderOf a = 3) (hx2 : x ^ 2 = t) (hy2 : y ^ 2 = t)
    (hyx : y * x * y⁻¹ = x⁻¹) (hax : a * x * a⁻¹ = y) (hay : a * y * a⁻¹ = x * y)
    (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) :
    ∃ ψ : J ≃* SL(2, ZMod 3),
      (∀ j : J, (j : R) = t → ψ j = -1) ∧
      (∀ (j : J) (f : Fin 2 × Fin 2 × Fin 2 × Fin 3),
        (j : R) = t ^ (f.1 : ℕ) * x ^ (f.2.1 : ℕ) * y ^ (f.2.2.1 : ℕ) * a ^ (f.2.2.2 : ℕ) →
        ψ j = slTwoThreeNormalForm f) ∧
      (P.subgroupOf J).map ψ.toMonoidHom = Subgroup.closure {slTwoThreeX, slTwoThreeY} := by
  classical
  have : Fact (1 < 2 * 2) := ⟨by norm_num⟩
  obtain ⟨hX4, hY2, hYX, hX2, hA3, hAX, hAY⟩ := slTwoThree_relations
  set xP : P := ⟨x, hxP⟩ with hxPdef
  set yP : P := ⟨y, hyP⟩ with hyPdef
  have hx4 : xP ^ 4 = 1 := Subtype.ext (by
    change x ^ 4 = 1
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hx2, ht2])
  have hy2' : yP ^ 2 = xP ^ 2 := Subtype.ext (by
    change y ^ 2 = x ^ 2
    rw [hx2, hy2])
  have hyx' : yP * xP * yP⁻¹ = xP⁻¹ := Subtype.ext hyx
  let ℓ : QuaternionGroup 2 →* P := quaternionEightLift xP yP hx4 hy2' hyx'
  have hxP2 : xP ^ 2 ≠ 1 := fun h => ht1 (by rw [← hx2]; exact congrArg Subtype.val h)
  have hℓinj : Function.Injective ℓ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [Subgroup.mem_bot]
    cases g with
    | a i =>
      change xP ^ i.val = 1 at hg
      have hord : orderOf xP = 4 := orderOf_eq_four_of_sq_ne_one hx4 hxP2
      have hdvd := orderOf_dvd_of_pow_eq_one hg
      rw [hord] at hdvd
      have hlt : i.val < 4 := ZMod.val_lt i
      have hi : i.val = 0 := by omega
      rw [(ZMod.val_eq_zero i).mp hi, QuaternionGroup.a_zero]
    | xa i =>
      exfalso
      change yP * xP ^ i.val = 1 at hg
      have hy : yP = (xP ^ i.val)⁻¹ := eq_inv_of_mul_eq_one_left hg
      have hc : yP * xP * yP⁻¹ = xP := by
        rw [hy, inv_inv, mul_assoc, (Commute.self_pow xP i.val).eq, inv_mul_cancel_left]
      rw [hyx'] at hc
      apply hxP2
      rw [pow_two]
      nth_rewrite 1 [← hc]
      exact inv_mul_cancel xP
  have hcardQ : Nat.card (QuaternionGroup 2) = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hℓbij : Function.Bijective ℓ := hℓinj.bijective_of_nat_card_le (by rw [hP8, hcardQ])
  let eP : QuaternionGroup 2 ≃* P := MulEquiv.ofBijective ℓ hℓbij
  have heP_a : eP (QuaternionGroup.a 1) = xP := by
    change xP ^ (1 : ZMod (2 * 2)).val = xP
    rw [ZMod.val_one, pow_one]
  have heP_xa : eP (QuaternionGroup.xa 0) = yP := by
    change yP * xP ^ (0 : ZMod (2 * 2)).val = yP
    rw [ZMod.val_zero, pow_zero, mul_one]
  let q₀ : QuaternionGroup 2 →* SL(2, ZMod 3) :=
    quaternionEightLift slTwoThreeX slTwoThreeY hX4 hY2 hYX
  have hq₀a : q₀ (QuaternionGroup.a 1) = slTwoThreeX := by
    change slTwoThreeX ^ (1 : ZMod (2 * 2)).val = slTwoThreeX
    rw [ZMod.val_one, pow_one]
  have hq₀xa : q₀ (QuaternionGroup.xa 0) = slTwoThreeY := by
    change slTwoThreeY * slTwoThreeX ^ (0 : ZMod (2 * 2)).val = slTwoThreeY
    rw [ZMod.val_zero, pow_zero, mul_one]
  let fP : P →* SL(2, ZMod 3) := q₀.comp eP.symm.toMonoidHom
  have hfPx : fP xP = slTwoThreeX := by
    change q₀ (eP.symm xP) = slTwoThreeX
    rw [← heP_a, MulEquiv.symm_apply_apply, hq₀a]
  have hfPy : fP yP = slTwoThreeY := by
    change q₀ (eP.symm yP) = slTwoThreeY
    rw [← heP_xa, MulEquiv.symm_apply_apply, hq₀xa]
  have hPext : ∀ f₁ f₂ : P →* SL(2, ZMod 3), f₁ xP = f₂ xP → f₁ yP = f₂ yP → f₁ = f₂ := by
    intro f₁ f₂ h1 h2
    have h3 : f₁.comp eP.toMonoidHom = f₂.comp eP.toMonoidHom :=
      MonoidHom.eq_of_eqOn_dense quaternionEight_closure_eq_top (by
        rintro g (rfl | rfl)
        · change f₁ (eP (QuaternionGroup.a 1)) = f₂ (eP (QuaternionGroup.a 1))
          rw [heP_a, h1]
        · change f₁ (eP (QuaternionGroup.xa 0)) = f₂ (eP (QuaternionGroup.xa 0))
          rw [heP_xa, h2])
    refine MonoidHom.ext fun p => ?_
    have h4 := DFunLike.congr_fun h3 (eP.symm p)
    simpa using h4
  set PJ : Subgroup J := P.subgroupOf J with hPJdef
  let ιP : PJ ≃* P := subgroupOfEquivOfLe hPJ
  set aJ : J := ⟨a, haJ⟩ with haJdef
  set AJ : Subgroup J := zpowers aJ with hAJdef
  have hPJcard : Nat.card PJ = 8 := by rw [Nat.card_congr ιP.toEquiv, hP8]
  have haJ3 : orderOf aJ = 3 := by rw [← Subgroup.orderOf_coe]; exact ha3
  have hAJcard : Nat.card AJ = 3 := by rw [Nat.card_zpowers, haJ3]
  have hcompl : PJ.IsComplement' AJ :=
    isComplement'_of_coprime (by rw [hPJcard, hAJcard, hJ24]) (by rw [hPJcard, hAJcard]; norm_num)
  let E := SemidirectProduct.mulEquivSubgroup hcompl
  let fPJ : PJ →* SL(2, ZMod 3) := fP.comp ιP.toMonoidHom
  let gA : AJ := ⟨aJ, mem_zpowers aJ⟩
  have hgen : ∀ k : AJ, k ∈ zpowers gA := by
    rintro ⟨k, hk⟩
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hk
    exact ⟨n, Subtype.ext (by simp [gA])⟩
  have hgA3 : orderOf gA = 3 := by rw [Subgroup.orderOf_mk, haJ3]
  have hA3' : orderOf slTwoThreeA ∣ orderOf gA := by
    rw [hgA3]; exact orderOf_dvd_of_pow_eq_one hA3
  let fA : AJ →* SL(2, ZMod 3) := monoidHomOfForallMemZpowers hgen hA3'
  have hfA : fA gA = slTwoThreeA := monoidHomOfForallMemZpowers_apply_gen hgen hA3'
  let φ : AJ →* MulAut PJ := PJ.normalizerMonoidHom.comp (inclusion (PJ.normalizer_eq_top ▸ le_top))
  have hφ : ∀ (k : AJ) (p : PJ), ((φ k p : PJ) : J) = (k : J) * p * (k : J)⁻¹ := fun k p =>
    normalizerMonoidHom_apply_apply_coe _ _ _
  have hφR : ∀ (k : AJ) (p : PJ), (((φ k p : PJ) : J) : R) = ((k : J) : R) * ((p : J) : R) *
      ((k : J) : R)⁻¹ := fun k p => by rw [hφ]; rfl
  have hbase : ∀ p : PJ, fPJ (φ gA p) = slTwoThreeA * fPJ p * slTwoThreeA⁻¹ := by
    have h1 : fPJ.comp ((φ gA).toMonoidHom.comp ιP.symm.toMonoidHom) =
        (MulAut.conj slTwoThreeA).toMonoidHom.comp fP := by
      apply hPext
      · have hx' : φ gA (ιP.symm xP) = ιP.symm yP := Subtype.ext (Subtype.ext (by
          rw [hφR]
          exact hax))
        change fPJ (φ gA (ιP.symm xP)) = slTwoThreeA * fP xP * slTwoThreeA⁻¹
        rw [hx', hfPx, hAX]
        change fP (ιP (ιP.symm yP)) = slTwoThreeY
        rw [MulEquiv.apply_symm_apply, hfPy]
      · have hy' : φ gA (ιP.symm yP) = ιP.symm (xP * yP) := Subtype.ext (Subtype.ext (by
          rw [hφR]
          exact hay))
        change fPJ (φ gA (ιP.symm yP)) = slTwoThreeA * fP yP * slTwoThreeA⁻¹
        rw [hy', hfPy, hAY]
        change fP (ιP (ιP.symm (xP * yP))) = slTwoThreeX * slTwoThreeY
        rw [MulEquiv.apply_symm_apply, map_mul, hfPx, hfPy]
    intro p
    have h2 := DFunLike.congr_fun h1 (ιP p)
    simpa [fPJ] using h2
  have hpow : ∀ (n : ℕ) (p : PJ), fPJ (φ (gA ^ n) p) = fA (gA ^ n) * fPJ p * (fA (gA ^ n))⁻¹ := by
    intro n
    induction n with
    | zero => intro p; simp
    | succ n ih =>
      intro p
      rw [pow_succ', map_mul, MulAut.mul_apply, hbase, ih, map_mul, hfA]
      group
  have hcompat : ∀ k : AJ,
      fPJ.comp (φ k).toMonoidHom = (MulAut.conj (fA k)).toMonoidHom.comp fPJ := by
    intro k
    obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.mpr (hgen k))
    refine MonoidHom.ext fun p => ?_
    rw [← hn]
    exact hpow n p
  let Ψ₀ : PJ ⋊[φ] AJ →* SL(2, ZMod 3) := SemidirectProduct.lift fPJ fA hcompat
  let ψhom : J →* SL(2, ZMod 3) := Ψ₀.comp E.symm.toMonoidHom
  have hψP : ∀ p : PJ, ψhom (p : J) = fPJ p := by
    intro p
    have : E.symm (p : J) = SemidirectProduct.inl p := by
      rw [MulEquiv.symm_apply_eq, SemidirectProduct.mulEquivSubgroup_apply]
      simp
    change Ψ₀ (E.symm (p : J)) = fPJ p
    rw [this]
    exact SemidirectProduct.lift_inl _ _ _ _
  have hψA : ∀ k : AJ, ψhom (k : J) = fA k := by
    intro k
    have : E.symm (k : J) = SemidirectProduct.inr k := by
      rw [MulEquiv.symm_apply_eq, SemidirectProduct.mulEquivSubgroup_apply]
      simp
    change Ψ₀ (E.symm (k : J)) = fA k
    rw [this]
    exact SemidirectProduct.lift_inr _ _ _ _
  set xJ : J := ⟨x, hPJ hxP⟩ with hxJ
  set yJ : J := ⟨y, hPJ hyP⟩ with hyJ
  set tJ : J := xJ ^ 2 with htJ
  have hψx : ψhom xJ = slTwoThreeX := by
    have := hψP (ιP.symm xP)
    rw [show ((ιP.symm xP : PJ) : J) = xJ from rfl] at this
    rw [this]
    change fP (ιP (ιP.symm xP)) = _
    rw [MulEquiv.apply_symm_apply, hfPx]
  have hψy : ψhom yJ = slTwoThreeY := by
    have := hψP (ιP.symm yP)
    rw [show ((ιP.symm yP : PJ) : J) = yJ from rfl] at this
    rw [this]
    change fP (ιP (ιP.symm yP)) = _
    rw [MulEquiv.apply_symm_apply, hfPy]
  have hψa : ψhom aJ = slTwoThreeA := by
    have := hψA gA
    rwa [hfA] at this
  have hψt : ψhom tJ = -1 := by rw [htJ, map_pow, hψx, hX2]
  have htJR : (tJ : R) = t := by rw [htJ, Subgroup.coe_pow, ← hx2]
  have hnf : ∀ f : Fin 2 × Fin 2 × Fin 2 × Fin 3,
      ψhom (tJ ^ (f.1 : ℕ) * xJ ^ (f.2.1 : ℕ) * yJ ^ (f.2.2.1 : ℕ) * aJ ^ (f.2.2.2 : ℕ)) =
        slTwoThreeNormalForm f := by
    intro f
    simp only [map_mul, map_pow, hψt, hψx, hψy, hψa, slTwoThreeNormalForm]
  have hsurj : Function.Surjective ψhom := by
    intro s
    obtain ⟨f, hf⟩ := slTwoThreeNormalForm_bijective.2 s
    exact ⟨_, (hnf f).trans hf⟩
  have hcardSL : Nat.card SL(2, ZMod 3) = 24 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hbij : Function.Bijective ψhom :=
    hsurj.bijective_of_nat_card_le (by rw [hJ24, hcardSL])
  refine ⟨MulEquiv.ofBijective ψhom hbij, ?_, ?_, ?_⟩
  · intro j hj
    have : j = tJ := Subtype.ext (hj.trans htJR.symm)
    rw [MulEquiv.ofBijective_apply, this, hψt]
  · intro j f hj
    have : j = tJ ^ (f.1 : ℕ) * xJ ^ (f.2.1 : ℕ) * yJ ^ (f.2.2.1 : ℕ) * aJ ^ (f.2.2.2 : ℕ) := by
      apply Subtype.ext
      rw [hj]
      simp only [Subgroup.coe_mul, Subgroup.coe_pow, htJR]
      rfl
    rw [MulEquiv.ofBijective_apply, this, hnf]
  · have hrange : q₀.range = Subgroup.closure {slTwoThreeX, slTwoThreeY} := by
      rw [MonoidHom.range_eq_map, ← quaternionEight_closure_eq_top, MonoidHom.map_closure,
        Set.image_pair, hq₀a, hq₀xa]
    apply le_antisymm
    · rintro _ ⟨p, hp, rfl⟩
      rw [← hrange]
      change ψhom p ∈ q₀.range
      have h1 : ψhom p = fPJ ⟨p, hp⟩ := hψP ⟨p, hp⟩
      rw [h1]
      exact ⟨_, rfl⟩
    · rw [Subgroup.closure_le]
      rintro s (rfl | rfl)
      · exact ⟨xJ, (mem_subgroupOf.mpr hxP), hψx⟩
      · exact ⟨yJ, (mem_subgroupOf.mpr hyP), hψy⟩

end Psi

theorem coe_slTwoThreeNormalForm (ε u v : Fin 2) (e : Fin 3) :
    ((slTwoThreeNormalForm (ε, u, v, e) : SL(2, ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      (-1) ^ (ε : ℕ) * !![0, 1; -1, 0] ^ (u : ℕ) * !![1, 1; 1, -1] ^ (v : ℕ) *
        !![0, 1; -1, -1] ^ (e : ℕ) := by
  simp only [slTwoThreeNormalForm, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one]
  rfl

theorem solvable_quaternion_witness_characteristic_field_three_subgroup
    {R : Type*} [Group R] [Finite R] [Group.IsSolvable R] (hO : CFSG.pPrimeCore 2 R = ⊥)
    (S : Sylow 2 R) {r : ℕ} (hr : 3 ≤ r)
    (eS : (S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2))) :
    let P := CFSG.pCore 2 R
    let J := threeCoreInverseImage P
    (∃ k : ℕ, 1 ≤ k ∧ Nonempty (P ≃* QuaternionGroup (2 ^ k))) ∧
    (∃ u v : P, u * v ≠ v * u) ∧
    ∃ t : R, orderOf t = 2 ∧ (∀ u : R, orderOf u = 2 → u = t) ∧
      CFSG.fittingSubgroup R = P ∧ centralizer (P : Set R) = zpowers t ∧
      (center P).map P.subtype = zpowers t ∧ center R = zpowers t ∧
      ((IsPGroup 2 R ∧ P = ⊤ ∧ (S : Subgroup R) = ⊤ ∧
          ∃ e : R ≃* QuaternionGroup (2 ^ (r - 2)),
            ∀ (g : R) (hg : g ∈ (S : Subgroup R)), e g = eS ⟨g, hg⟩) ∨
        (¬ IsPGroup 2 R ∧ Nat.card P = 8 ∧ Nat.card (cyclicOrderFourSubgroups P) = 3 ∧
          (axisAction P).ker = P ∧
          ((axisAction P).range = finiteAlternatingGroup (cyclicOrderFourSubgroups P) ∨
            (axisAction P).range = ⊤) ∧
          (Nat.card R = 24 ∨ Nat.card R = 48) ∧
          J.Characteristic ∧ Nat.card J = 24 ∧ J.index ≤ 2 ∧
          (∃ T : Sylow 2 J, (T : Subgroup J).map J.subtype = P) ∧ CFSG.pPrimeCore 2 J = ⊥ ∧
          (∃ a x y : R, a ∈ J ∧ x ∈ P ∧ y ∈ P ∧ orderOf a = 3 ∧ x ^ 2 = t ∧ y ^ 2 = t ∧
            y * x * y⁻¹ = x⁻¹ ∧ a * x * a⁻¹ = y ∧ a * y * a⁻¹ = x * y ∧
            (∀ j ∈ J, ∃! f : Fin 2 × Fin 2 × Fin 2 × Fin 3,
              t ^ (f.1 : ℕ) * x ^ (f.2.1 : ℕ) * y ^ (f.2.2.1 : ℕ) * a ^ (f.2.2.2 : ℕ) = j) ∧
            ∃ ψ : J ≃* SL(2, ZMod 3),
              (∀ j : J, (j : R) = t → ((ψ j : SL(2, ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
                -1) ∧
              (∀ (j : J) (ε u v : Fin 2) (e : Fin 3),
                (j : R) = t ^ (ε : ℕ) * x ^ (u : ℕ) * y ^ (v : ℕ) * a ^ (e : ℕ) →
                ((ψ j : SL(2, ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
                  (-1) ^ (ε : ℕ) * !![0, 1; -1, 0] ^ (u : ℕ) * !![1, 1; 1, -1] ^ (v : ℕ) *
                    !![0, 1; -1, -1] ^ (e : ℕ)) ∧
              (P.subgroupOf J).map ψ.toMonoidHom = Subgroup.closure {slTwoThreeX, slTwoThreeY} ∧
              Nat.card (Subgroup.closure ({slTwoThreeX, slTwoThreeY} : Set SL(2, ZMod 3))) = 8 ∧
              Nonempty (Subgroup.closure ({slTwoThreeX, slTwoThreeY} : Set SL(2, ZMod 3)) ≃*
                QuaternionGroup 2)) ∧
          ∀ (H : Type*) [Group H] (ι : R →* H), Function.Injective ι → ι.range.Normal →
            (J.map ι).Normal ∧ ι t ∈ J.map ι)) := by
  intro P J
  obtain ⟨hF, hCP, t, htP, ht, huniq, k, hk, ⟨eP⟩⟩ := solvable_quaternion_two_core hO S hr eS
  obtain ⟨hC, hZ, hZR, hnab⟩ := solvable_quaternion_centers htP ht huniq hCP hk eP
  refine ⟨⟨k, hk, ⟨eP⟩⟩, hnab, t, ht, huniq, hF, hC, hZ, hZR, ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hR2 : IsPGroup 2 R
  · left
    have hPtop : P = ⊤ := top_le_iff.mp (le_sSup ⟨inferInstance, hR2.to_subgroup ⊤⟩)
    have hStop : (S : Subgroup R) = ⊤ := (S.is_maximal' (hR2.to_subgroup ⊤) le_top).symm
    exact ⟨hR2, hPtop, hStop,
      Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr hStop.symm).trans eS),
      fun g hg => rfl⟩
  · right
    have hk1 : k = 1 := by
      by_contra hk1
      have hA : IsPGroup 2 (MulAut P) :=
        (isPGroup_mulAut_quaternionGroup (by omega : 2 ≤ k)).of_equiv (MulAut.congr eP).symm
      exact hR2 (isPGroup_of_centralizer_le_of_isPGroup_mulAut CFSG.pCore_isPGroup hCP hA)
    subst hk1
    have e8 : P ≃* QuaternionGroup 2 := eP
    have hP8 : Nat.card P = 8 := by
      rw [Nat.card_congr e8.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have ht1 : t ≠ 1 := by
      intro h
      rw [h, orderOf_one] at ht
      exact absurd ht (by norm_num)
    have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
    obtain ⟨hcardR, h36, hrange⟩ := axisAction_range rfl e8 huniq hC ht hR2
    have hker := axisAction_ker rfl e8 huniq hC ht
    have hQ : Nat.card (R ⧸ P) = 3 ∨ Nat.card (R ⧸ P) = 6 := by
      have h1 : Nat.card (R ⧸ P) = Nat.card (axisAction P).range := by
        rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange (axisAction P)).toEquiv, hker]
      rwa [h1]
    obtain ⟨hJ24, hJidx, hPJ, hSyl⟩ := threeCoreInverseImage_facts hP8 hQ
    have hJodd := pPrimeCore_two_eq_bot_of_centralizer hPJ CFSG.pCore_isPGroup ht hC
    obtain ⟨a, x, y, haJ, hxP, hyP, ha3, hx2, hy2, hyx, hax, hay⟩ :=
      exists_quaternion_triple (J := J) e8 ht huniq hC (by rw [hJ24]; norm_num)
    obtain ⟨ψ, hψt, hψnf, hψP⟩ := exists_mulEquiv_slTwoThree hPJ hP8 hJ24 haJ hxP hyP ha3 hx2
      hy2 hyx hax hay ht1 ht2
    have hmemJ : ∀ f : Fin 2 × Fin 2 × Fin 2 × Fin 3,
        t ^ (f.1 : ℕ) * x ^ (f.2.1 : ℕ) * y ^ (f.2.2.1 : ℕ) * a ^ (f.2.2.2 : ℕ) ∈ J := fun f =>
      J.mul_mem (J.mul_mem (J.mul_mem (J.pow_mem (hPJ htP) _) (J.pow_mem (hPJ hxP) _))
        (J.pow_mem (hPJ hyP) _)) (J.pow_mem haJ _)
    have hPJcard : Nat.card (P.subgroupOf J) = 8 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hPJ).toEquiv, hP8]
    refine ⟨hR2, hP8, card_cyclicOrderFourSubgroups e8, hker, hrange, ?_,
      threeCoreInverseImage_characteristic P, hJ24, hJidx, hSyl, hJodd,
      ⟨a, x, y, haJ, hxP, hyP, ha3, hx2, hy2, hyx, hax, hay, ?_, ψ, ?_, ?_, hψP, ?_, ?_⟩, ?_⟩
    · rcases h36 with h | h
      · left; rw [hcardR, h]
      · right; rw [hcardR, h]
    · intro j hj
      obtain ⟨f, hf⟩ := slTwoThreeNormalForm_bijective.2 (ψ ⟨j, hj⟩)
      have hNf : ∀ g : Fin 2 × Fin 2 × Fin 2 × Fin 3,
          ψ ⟨_, hmemJ g⟩ = slTwoThreeNormalForm g := fun g => hψnf ⟨_, hmemJ g⟩ g rfl
      have hfj : t ^ (f.1 : ℕ) * x ^ (f.2.1 : ℕ) * y ^ (f.2.2.1 : ℕ) * a ^ (f.2.2.2 : ℕ) = j :=
        congrArg Subtype.val (ψ.injective ((hNf f).trans hf))
      refine ⟨f, hfj, fun f' hf' => ?_⟩
      have hf'' : t ^ (f'.1 : ℕ) * x ^ (f'.2.1 : ℕ) * y ^ (f'.2.2.1 : ℕ) *
          a ^ (f'.2.2.2 : ℕ) = j := hf'
      apply slTwoThreeNormalForm_bijective.1
      rw [← hNf f', ← hNf f]
      congr 1
      apply Subtype.ext
      exact hf''.trans hfj.symm
    · intro j hj
      rw [hψt j hj, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
      rfl
    · intro j ε u v e hj
      rw [hψnf j (ε, u, v, e) hj, coe_slTwoThreeNormalForm]
    · rw [← hψP, card_map_of_injective ψ.injective, hPJcard]
    · rw [← hψP]
      exact ⟨((P.subgroupOf J).equivMapOfInjective ψ.toMonoidHom ψ.injective).symm.trans
        ((subgroupOfEquivOfLe hPJ).trans e8)⟩
    · intro H _ ι hι hn
      have := threeCoreInverseImage_characteristic P
      exact ⟨map_normal_of_characteristic ι hι hn, ⟨t, hPJ htP, rfl⟩⟩

end CFSG.LocalAnalysis.SteinbergBK
