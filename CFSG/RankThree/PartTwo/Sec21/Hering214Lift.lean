module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofLie
public import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofSmall
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open Item211Res2Proof
open scoped commutatorElement

namespace Hering214

section Odd

variable {H : Type*} [Group H]

theorem eq_one_of_sq_eq_one_of_odd {θ : Subgroup H} (hθo : Odd (Nat.card θ)) {z : H} (hz : z ∈ θ)
    (h2 : z ^ 2 = 1) : z = 1 := by
  have h1 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have h3 : orderOf z ∣ Nat.card θ := Subgroup.orderOf_dvd_natCard θ hz
  have hcop : Nat.Coprime 2 (Nat.card θ) := Nat.coprime_two_left.mpr hθo
  have hdvd : orderOf z ∣ Nat.gcd 2 (Nat.card θ) := Nat.dvd_gcd h1 h3
  rw [hcop] at hdvd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)

theorem eq_one_of_pow_four_eq_one_of_odd {θ : Subgroup H} (hθo : Odd (Nat.card θ)) {z : H}
    (hz : z ∈ θ) (h4 : z ^ 4 = 1) : z = 1 := by
  have hz2 : z ^ 2 ∈ θ := θ.pow_mem hz 2
  have h22 : (z ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact h4
  exact eq_one_of_sq_eq_one_of_odd hθo hz (eq_one_of_sq_eq_one_of_odd hθo hz2 h22)

theorem pow_natCard_eq_one {θ : Subgroup H} [Finite θ] {y : H} (hy : y ∈ θ) :
    y ^ Nat.card θ = 1 := by
  have := orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard θ hy)
  exact this

theorem commute_of_sq_mem {θ : Subgroup H} (hθo : Odd (Nat.card θ))
    (hθc : θ ≤ Subgroup.center H) {x y : H} (hx : x ^ 2 ∈ θ) (hz : x * y * x⁻¹ * y⁻¹ ∈ θ) :
    x * y = y * x := by
  set z := x * y * x⁻¹ * y⁻¹ with hzdef
  have hzc : ∀ a : H, a * z = z * a := fun a => Subgroup.mem_center_iff.mp (hθc hz) a
  have hxc : ∀ a : H, a * x ^ 2 = x ^ 2 * a := fun a => Subgroup.mem_center_iff.mp (hθc hx) a
  have hxy : x * y = z * (y * x) := by
    simp only [hzdef]
    group
  have h1 : x ^ 2 * y = z ^ 2 * (y * x ^ 2) := by
    calc x ^ 2 * y = x * (x * y) := by rw [sq, mul_assoc]
      _ = x * (z * (y * x)) := by rw [hxy]
      _ = z * (x * (y * x)) := by rw [← mul_assoc, hzc x, mul_assoc]
      _ = z * ((x * y) * x) := by rw [mul_assoc x y x]
      _ = z * ((z * (y * x)) * x) := by rw [hxy]
      _ = z ^ 2 * (y * x ^ 2) := by simp only [sq, mul_assoc]
  have h2 : z ^ 2 * (y * x ^ 2) = y * x ^ 2 := by
    rw [← h1]
    exact (hxc y).symm
  have h3 : z ^ 2 = 1 := by
    have := h2
    exact (mul_eq_right.mp this)
  have h4 : z = 1 := eq_one_of_sq_eq_one_of_odd hθo hz h3
  rw [h4, one_mul] at hxy
  exact hxy

end Odd

section Lift

variable {H Q : Type*} [Group H] [Group Q]

theorem exists_lift_four {q : H →* Q} (hq : Function.Surjective q)
    (hKc : q.ker ≤ Subgroup.center H) (hKo : Odd (Nat.card q.ker)) [Finite H] {W : Subgroup Q}
    (hW : IsElemAbelian 2 W) (hW4 : Nat.card W = 4) :
    ∃ S : Subgroup H, (∀ x, x ∈ S ↔ q x ∈ W ∧ x ^ 4 = 1) ∧ IsElemAbelian 2 S ∧
      Nat.card S = 4 ∧ ∀ w ∈ W, ∃ x ∈ S, q x = w := by
  have hsq : ∀ x : H, q x ∈ W → x ^ 2 ∈ q.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, map_pow]
    exact hW.2 _ hx
  have hcomm : ∀ x y : H, q x ∈ W → q y ∈ W → x * y = y * x := by
    intro x y hx hy
    have hxy : q x * q y = q y * q x := congrArg Subtype.val (hW.1.is_comm.comm ⟨q x, hx⟩ ⟨q y, hy⟩)
    have hz : x * y * x⁻¹ * y⁻¹ ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hxy]
      group
    exact commute_of_sq_mem hKo hKc (hsq x hx) hz
  have hinj4 : ∀ x : H, x ^ 4 = 1 → q x = 1 → x = 1 := fun x h4 h1 =>
    eq_one_of_pow_four_eq_one_of_odd hKo ((MonoidHom.mem_ker).mpr h1) h4
  let S : Subgroup H :=
    { carrier := {x | q x ∈ W ∧ x ^ 4 = 1}
      mul_mem' := by
        rintro x y ⟨hx, hx4⟩ ⟨hy, hy4⟩
        refine ⟨by rw [map_mul]; exact W.mul_mem hx hy, ?_⟩
        have hc : Commute x y := hcomm x y hx hy
        rw [hc.mul_pow, hx4, hy4, one_mul]
      one_mem' := ⟨by rw [map_one]; exact W.one_mem, one_pow 4⟩
      inv_mem' := by
        rintro x ⟨hx, hx4⟩
        exact ⟨by rw [map_inv]; exact W.inv_mem hx, by rw [inv_pow, hx4, inv_one]⟩ }
  have hmem : ∀ x, x ∈ S ↔ q x ∈ W ∧ x ^ 4 = 1 := fun x => Iff.rfl
  have hSsq : ∀ x ∈ S, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨hxW, hx4⟩ := hx
    have h22 : (x ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hx4
    exact eq_one_of_sq_eq_one_of_odd hKo (hsq x hxW) h22
  have hSsurj : ∀ w ∈ W, ∃ x ∈ S, q x = w := by
    intro w hw
    obtain ⟨y, rfl⟩ := hq w
    set m := Nat.card q.ker with hm
    have hy2 : y ^ 2 ∈ q.ker := hsq y hw
    have hym : (y ^ 2) ^ m = 1 := pow_natCard_eq_one hy2
    refine ⟨y ^ m, ⟨?_, ?_⟩, ?_⟩
    · rw [map_pow]
      obtain ⟨k, hk⟩ := hKo
      rw [hk, pow_succ, pow_mul]
      have : (q y) ^ 2 = 1 := hW.2 _ hw
      rw [this, one_pow, one_mul]
      exact hw
    · calc (y ^ m) ^ 4 = ((y ^ 2) ^ m) ^ 2 := by
            simp only [← pow_mul]
            congr 1
            ring
        _ = 1 := by rw [hym, one_pow]
    · rw [map_pow]
      obtain ⟨k, hk⟩ := hKo
      rw [hk, pow_succ, pow_mul]
      have : (q y) ^ 2 = 1 := hW.2 _ hw
      rw [this, one_pow, one_mul]
  have hScomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy => hcomm x y hx.1 hy.1
  refine ⟨S, hmem, ⟨⟨⟨fun a b => Subtype.ext (hScomm _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩, ?_, hSsurj⟩
  · rw [hSsq x hx]
  ·
    have hbij : Function.Bijective (fun x : S => (⟨q x, x.2.1⟩ : W)) := by
      constructor
      · intro a b hab
        have h1 : q a = q b := congrArg Subtype.val hab
        have h2 : q ((a : H) * (b : H)⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
        have h3 : ((a : H) * (b : H)⁻¹) ^ 4 = 1 := by
          have hab' : (a : H) * (b : H)⁻¹ = (b : H)⁻¹ * (a : H) := by
            have := hScomm _ a.2 _ (S.inv_mem b.2)
            exact this
          rw [Commute.mul_pow (a := (a : H)) (b := (b : H)⁻¹) hab' 4, inv_pow, a.2.2, b.2.2]
          simp
        have h4 := hinj4 _ h3 h2
        exact Subtype.ext (mul_inv_eq_one.mp h4)
      · intro w
        obtain ⟨x, hx, hxw⟩ := hSsurj w w.2
        exact ⟨⟨x, hx⟩, Subtype.ext hxw⟩
    rw [Nat.card_eq_of_bijective _ hbij, hW4]

end Lift

variable {G : Type} [Group G] [Finite G]

theorem exists_fourGroupsMinus_of_bar {E L : Subgroup G}
    (hEL : E ≤ Subgroup.normalizer (L : Set G))
    (hE3 : ∀ e ∈ E, e ^ 3 = 1)
    (hθc : aschbacherSolvableCore 3 L ≤ Subgroup.center L)
    (hθo : Odd (Nat.card (aschbacherSolvableCore 3 L)))
    {W : Subgroup (lBar L)} (hW : IsElemAbelian 2 W) (hW4 : Nat.card W = 4)
    (hinv : ∀ σ ∈ barImage L E, ∀ w ∈ W, σ w ∈ W)
    (hnt : ∃ σ ∈ barImage L E, ∃ w ∈ W, σ w ≠ w) :
    ∃ U' ∈ fourGroupsMinus E, U' ≤ L := by
  classical
  let q : ↥L →* lBar L := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : q.ker = aschbacherSolvableCore 3 ↥L := QuotientGroup.ker_mk' _
  obtain ⟨S, hSmem, hSel, hS4, hSsurj⟩ :=
    exists_lift_four (q := q) hq (by rw [hker]; exact hθc) (by rw [hker]; exact hθo) hW hW4
  have hbarmem : ∀ e (he : e ∈ E), barAct L ⟨e, hEL he⟩ ∈ barImage L E := fun e he =>
    mem_barImage_iff.mpr ⟨e, hEL he, he, rfl⟩
  have hcl : ∀ e (he : e ∈ E) (x : ↥L), x ∈ S → L.normalizerMonoidHom ⟨e, hEL he⟩ x ∈ S := by
    intro e he x hx
    rw [hSmem] at hx ⊢
    refine ⟨?_, ?_⟩
    · have h1 : q (L.normalizerMonoidHom ⟨e, hEL he⟩ x) = barAct L ⟨e, hEL he⟩ (q x) := rfl
      rw [h1]
      exact hinv _ (hbarmem e he) _ hx.1
    · rw [← map_pow, hx.2, map_one]
  set U' : Subgroup G := S.map L.subtype with hU'
  have hEinv : ∀ e ∈ E, ∀ u ∈ U', e * u * e⁻¹ ∈ U' := by
    rintro e he _ ⟨x, hx, rfl⟩
    exact ⟨_, hcl e he x hx, rfl⟩
  have hnorm : E ≤ Subgroup.normalizer (U' : Set G) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨fun hu => hEinv e he u hu, fun hu => ?_⟩
    have := hEinv e⁻¹ (E.inv_mem he) _ hu
    simpa [mul_assoc] using this
  have hU'ab : IsElemAbelian 2 U' := CFSG.Open.IsElemAbelian.map hSel L.subtype
  have hU'4 : Nat.card U' = 4 := by
    rw [hU', Subgroup.card_map_of_injective L.subtype_injective, hS4]
  have hU'4g : U' ∈ fourGroups E := mem_fourGroups_iff.mpr ⟨hnorm, hU'ab, hU'4⟩
  rcases mem_fourGroupsPlus_or_mem_fourGroupsMinus hE3 hU'4g with hP | hM
  · exfalso
    obtain ⟨σ, hσ, w, hw, hne⟩ := hnt
    obtain ⟨e, heN, heE, rfl⟩ := mem_barImage_iff.mp hσ
    obtain ⟨x, hx, rfl⟩ := hSsurj w hw
    apply hne
    have hEc := (mem_fourGroupsPlus_iff.mp hP).2 heE
    have hxu : ((x : ↥L) : G) ∈ U' := ⟨x, hx, rfl⟩
    have hc : (x : G) * e = e * x := Subgroup.mem_centralizer_iff.mp hEc _ hxu
    have h1 : L.normalizerMonoidHom ⟨e, heN⟩ x = x := by
      apply Subtype.ext
      change e * (x : G) * e⁻¹ = x
      rw [← hc]
      group
    exact congrArg q h1
  · exact ⟨U', hM, Subgroup.map_subtype_le S⟩

end Hering214

end CFSG.RankThree.PartTwo.Sec21
