module

public import CFSG.OddTranspositions.PartThree.EightEight.Star
public import CFSG.Timmesfeld.Bridge.Asc72Minimal

import CFSG.OddTranspositions.BlockGraph
import CFSG.OddTranspositions.PartThree.EightEight.Eighteen
import CFSG.OddTranspositions.PartThree.EightEight.FibreCentre
import CFSG.OddTranspositions.PartThree.EightEight.Kernel
import CFSG.OddTranspositions.PartThree.EightEight.Seventeen
import CFSG.OddTranspositions.PartThree.EightEight.ThirdCentralizer
import CFSG.OddTranspositions.PartThree.EightEight.Transport
import CFSG.OddTranspositions.PartThree.EightFive.Transitive
import CFSG.OddTranspositions.PartThree.HalphaCentralizer
import CFSG.OddTranspositions.PartThree.Nine.ThreeBlocks
import CFSG.OddTranspositions.SixSevenLocalStep
import CFSG.Timmesfeld.Bridge.Asc72ConjOrbit

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem mul_mul_pow_notMem_of_notMem (hC : HypothesisC D) (hZ : Subgroup.center G = ⊥)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {β : Set G} (hβ : β ∈ blockClass hC.alpha)
    (hx : x ∈ β) (hy : y ∈ β) (hw : w ∉ β) : x * y * (x * y * w) ^ n ∉ β := by
  classical
  let z : G := (x * y * w) ^ n
  let e : G := x * y * z
  change e ∉ β
  intro he
  obtain ⟨-, hz1, hzx, -, hzw, -⟩ :=
    IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord
  have hze : x * y * e = z := mul_mul_mul_mul_cancel_of_isTriangle hC.setup.oddT ht z
  have hzH : ∀ h ∈ Halpha D β, Commute z h := by
    intro h hh
    have hcent : ∀ a ∈ β, a * h = h * a :=
      fun a ha => Subgroup.mem_centralizer_iff.mp (Halpha_le_centralizer D β hh) a ha
    have hxh : Commute x h := (commute_iff_eq x h).mpr (hcent x hx)
    have hyh : Commute y h := (commute_iff_eq y h).mpr (hcent y hy)
    have heh : Commute e h := (commute_iff_eq e h).mpr (hcent e he)
    have hzh : Commute (x * y * e) h := (hxh.mul_left hyh).mul_left heh
    rwa [hze] at hzh
  have hsub := commute_subset_perp_of_commute_Halpha hC hZ hβ hx hz1 hzx hzH
  have hwin : w ∈ β ∪ DalphaStar D β := hsub ⟨ht.2.2.1, hzw.symm⟩
  rcases hwin with hwβ | hwS
  · exact hw hwβ
  · obtain ⟨γ, hγ, hwγ⟩ := hwS
    exact ht.2.2.2.2.2.1 ((mem_Dalpha_iff.mp hγ).2.2.2 x hx w hwγ)

private theorem exists_mem_Halpha_conj_eq_of_mem_DalphaStar (hC : HypothesisC D) {β : Set G}
    (hβ : β ∈ blockClass hC.alpha) {p q : G} (hp : p ∈ DalphaStar D β)
    (hq : q ∈ DalphaStar D β) :
    ∃ h ∈ Halpha D β, h * p * h⁻¹ = q := by
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hβ
  let hC' : HypothesisC D := hC.conj g
  have hα : hC'.alpha = β := (HypothesisC.conj_alpha hC g).trans hg.symm
  have hp' : p ∈ DalphaStar D hC'.alpha := hα.symm ▸ hp
  have hq' : q ∈ DalphaStar D hC'.alpha := hα.symm ▸ hq
  obtain ⟨h, hh, hhp⟩ := hC'.Halpha_transitive p hp' q hq'
  exact ⟨h, hα ▸ hh, hhp⟩

private theorem eq_of_forall_commute_of_mem_DalphaStar (hC : HypothesisC D) {β : Set G}
    (hβ : β ∈ blockClass hC.alpha) {p : G} (hp : p ∈ DalphaStar D β)
    (hcomm : ∀ q ∈ DalphaStar D β, Commute p q) {q : G} (hq : q ∈ DalphaStar D β) :
    q = p := by
  obtain ⟨h, hh, hhp⟩ := exists_mem_Halpha_conj_eq_of_mem_DalphaStar hC hβ hp hq
  have hle : Halpha D β ≤ Subgroup.centralizer ({p} : Set G) := by
    rw [Halpha, Subgroup.closure_le]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx).eq.symm
  have hph : h * p = p * h := Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
  rw [← hhp, hph]
  group

private theorem conj_mem_of_mem_Dalpha (hC : HypothesisC D) {β ε : Set G}
    (hβ : β ∈ blockClass hC.alpha) (hε : ε ∈ Dalpha D β) {x y e k : G}
    (hx : x ∈ β) (hy : y ∈ β) (heε : e ∈ ε) (hkx : k * x * k⁻¹ = e) :
    k * y * k⁻¹ ∈ ε := by
  have hεα : ε ∈ blockClass hC.alpha :=
    mem_blockClass_of_mem_blockClass (mem_blockClass_comm.mpr hβ) hε.1
  have hkB : (fun y => k * y * k⁻¹) '' β = ε :=
    eq_of_mem_of_mem_blockClass hC.isBlock_alpha (conj_image_mem_blockClass hβ k) hεα
      ⟨e, ⟨x, hx, hkx⟩, heε⟩
  have hy' : k * y * k⁻¹ ∈ (fun y => k * y * k⁻¹) '' β := ⟨y, hy, rfl⟩
  rwa [hkB] at hy'

omit [Finite G] in
private theorem conj_e_mem_and_commute (hC : HypothesisC D) {x w y : G}
    (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n)
    {k : G} (hkK : k ∈ localGroup D ((x * y * w) ^ n))
    (hkx : k * x * k⁻¹ = x * y * (x * y * w) ^ n) :
    k * (x * y * (x * y * w) ^ n) * k⁻¹ ∈ D ∧
      Commute (k * (x * y * (x * y * w) ^ n) * k⁻¹) x ∧
      Commute (k * (x * y * (x * y * w) ^ n) * k⁻¹) y := by
  let z : G := (x * y * w) ^ n
  let e : G := x * y * z
  let e' : G := k * e * k⁻¹
  have hkx' : k * x * k⁻¹ = e := hkx
  obtain ⟨-, -, hzx, -, -, heD⟩ := IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord
  have hex : Commute e x := commute_mul_mul_pow_left hC.setup.oddT hC.setup.normal ht hn hord
  have heK : e ∈ conjOrbit (localGroup D z) x := mul_mul_pow_mem_conjOrbit hC.setup ht hn hord
  have he'K : e' ∈ conjOrbit (localGroup D z) x := conj_mem_conjOrbit hkK heK
  have he'cent : e' ∈ centSet D z :=
    conjOrbit_subset_centSet hC.setup.normal ⟨ht.1, hzx.symm⟩ he'K
  have he'e : Commute e' e := by
    have h := hex.conj k
    rw [hkx'] at h
    exact h
  have h27 := commute_iff_commute_of_mem_centSet hC.setup ht hn hord he'cent
  have he'x : Commute e' x := h27.2.mpr he'e
  have he'y : Commute e' y := h27.1.mp he'x
  exact ⟨he'cent.1, he'x, he'y⟩

omit [Finite G] in
private theorem conj_mul_eq_of_mem_conjOrbit (hC : HypothesisC D) {x w y : G}
    (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n)
    {k : G} (hkK : k ∈ localGroup D ((x * y * w) ^ n))
    (hkx : k * x * k⁻¹ = x * y * (x * y * w) ^ n) :
    (k * y * k⁻¹) * (k * (x * y * (x * y * w) ^ n) * k⁻¹) = x * y ∧
      k * y * k⁻¹ = (x * y) * (k * (x * y * (x * y * w) ^ n) * k⁻¹) := by
  let z : G := (x * y * w) ^ n
  let e : G := x * y * z
  let y' : G := k * y * k⁻¹
  let e' : G := k * e * k⁻¹
  obtain ⟨hzz, -, -, -, -, heD⟩ := IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord
  have hkx' : e = k * x * k⁻¹ := hkx.symm
  have hze : x * y * e = z := mul_mul_mul_mul_cancel_of_isTriangle hC.setup.oddT ht z
  have hkz : Commute k z := commute_of_mem_localGroup hkK
  have hz_eq : z = e * y' * e' := by
    have h1 : e * y' * e' = k * (x * y * e) * k⁻¹ := by
      calc e * y' * e' = (k * x * k⁻¹) * y' * e' := by rw [hkx']
        _ = (k * x * k⁻¹) * (k * y * k⁻¹) * e' := by rw [show y' = k * y * k⁻¹ from rfl]
        _ = (k * x * k⁻¹) * (k * y * k⁻¹) * (k * e * k⁻¹) := by
              rw [show e' = k * e * k⁻¹ from rfl]
        _ = k * (x * y * e) * k⁻¹ := by group
    calc z = k * z * k⁻¹ := by rw [hkz.eq]; group
      _ = k * (x * y * e) * k⁻¹ := by rw [hze]
      _ = e * y' * e' := h1.symm
  have hzz' : z * z = 1 := hzz
  have hez : e * z = x * y := by
    show x * y * z * z = x * y
    calc x * y * z * z = x * y * (z * z) := by group
      _ = x * y := by rw [hzz', mul_one]
  have he'1 : e' * e' = 1 := by
    have he'D : e' ∈ D := hC.setup.conj_mem k heD
    exact hC.setup.oddT.mul_self_eq_one he'D
  have h2 : y' * e' = x * y := by
    have h1 : e * z = y' * e' := by
      rw [hz_eq]
      calc e * (e * y' * e') = (e * e) * y' * e' := by group
        _ = y' * e' := by
            rw [show e * e = 1 from hC.setup.oddT.mul_self_eq_one heD, one_mul]
    rw [← h1, hez]
  have hy'_eq : y' = (x * y) * e' := by
    calc y' = (y' * e') * e' := by rw [mul_assoc, he'1, mul_one]
      _ = (x * y) * e' := by rw [h2]
  exact ⟨h2, hy'_eq⟩

private theorem false_of_conj_data_mem (hC : HypothesisC D) {β : Set G}
    (hβ : β ∈ blockClass hC.alpha) {x y e y' e' : G}
    (hx : x ∈ β) (hy : y ∈ β) (heS : e ∈ DalphaStar D β)
    (hy'S : y' ∈ DalphaStar D β) (he'β : e' ∈ β) (hey' : e ≠ y')
    (hy'_eq : y' = x * y * e') : False := by
  have hy'comm : ∀ h ∈ DalphaStar D β, Commute y' h := by
    intro h hh
    rw [hy'_eq]
    exact ((commute_of_mem_of_mem_DalphaStar hx hh).mul_left
      (commute_of_mem_of_mem_DalphaStar hy hh)).mul_left
      (commute_of_mem_of_mem_DalphaStar he'β hh)
  exact hey' (eq_of_forall_commute_of_mem_DalphaStar hC hβ hy'S hy'comm heS)

private theorem false_of_conj_data_DalphaStar (hC : HypothesisC D) {x w y : G}
    (ht : IsTriangle D x w y) {β : Set G} (hβ : β ∈ blockClass hC.alpha)
    (hx : x ∈ β) (hy : y ∈ β) {e' y' f : G} (he'D : e' ∈ D) (hy'D : y' ∈ D)
    (he'xy : Commute e' (x * y)) (h2 : y' * e' = x * y)
    (hy'_eq : y' = (x * y) * e') (hyf : ¬ Commute y' f)
    (hfS : f ∈ DalphaStar D β) : False := by
  have hfD : f ∈ D :=
    DalphaStar_subset (isBlock_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hβ) hfS
  have htord : orderOf (x * y) = 2 :=
    hC.setup.oddT.orderOf_mul_eq_two ht.1 ht.2.1 ht.2.2.2.1 ht.2.2.2.2.1
  have hy't : Commute y' (x * y) := by
    rw [hy'_eq]
    exact ((Commute.refl (x * y)).mul_right he'xy.symm).symm
  have hft : Commute f (x * y) := (commute_mul_of_mem_DalphaStar hx hy hfS).symm
  have hyft : Commute (y' * f) (x * y) := hy't.mul_left hft
  have hy'2 : y' * y' = 1 := hC.setup.oddT.mul_self_eq_one hy'D
  have he'eq : e' = y' * (x * y) := by
    rw [← h2]
    rw [← mul_assoc, hy'2, one_mul]
  have he'f : e' * f = (y' * f) * (x * y) := by
    rw [he'eq, mul_assoc, ← hft.eq, ← mul_assoc]
  have hmodd : Odd (orderOf (y' * f)) := by
    rcases hC.setup.oddT.2 y' hy'D f hfD with hdvd | hodd
    · exact absurd ((commute_iff_mul_sq_eq_one (hC.setup.oddT.mul_self_eq_one hy'D)
        (hC.setup.oddT.mul_self_eq_one hfD)).mpr (orderOf_dvd_iff_pow_eq_one.mp hdvd)) hyf
    · exact hodd
  have hcop : (orderOf (y' * f)).Coprime (orderOf (x * y)) := by
    rw [htord]
    exact hmodd.coprime_two_right
  have hord_ef : orderOf (e' * f) = orderOf (y' * f) * 2 := by
    rw [he'f, hyft.orderOf_mul_eq_mul_orderOf_of_coprime hcop, htord]
  have hcases := hC.setup.oddT.2 e' he'D f hfD
  rw [hord_ef] at hcases
  rcases hcases with hdvd | hodd2
  · have hle : orderOf (y' * f) * 2 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < orderOf (y' * f) := orderOf_pos _
    have hm1 : orderOf (y' * f) = 1 := by omega
    have h1 : y' * f = 1 := orderOf_eq_one_iff.mp hm1
    have hyf' : y' = f := by
      rw [← hC.setup.oddT.inv_eq hfD]
      exact mul_eq_one_iff_eq_inv.mp h1
    rw [hyf'] at hyf
    exact hyf (Commute.refl f)
  · obtain ⟨r, hr⟩ := hodd2
    omega

theorem mul_mul_pow_mem_of_mem (hC : HypothesisC D)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {β : Set G} (hβ : β ∈ blockClass hC.alpha)
    (hx : x ∈ β) (hy : y ∈ β) : x * y * (x * y * w) ^ n ∈ β := by
  classical
  let z : G := (x * y * w) ^ n
  let e : G := x * y * z
  change e ∈ β
  by_contra heβ
  obtain ⟨-, -, -, -, -, heD⟩ := IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord
  have hex : Commute e x := commute_mul_mul_pow_left hC.setup.oddT hC.setup.normal ht hn hord
  have heS : e ∈ DalphaStar D β := by
    rcases Nine.mem_block_or_DalphaStar_of_commute hC hβ hx heD hex.symm with h | h
    · exact absurd h heβ
    · exact h
  obtain ⟨ε, hε, heε⟩ := heS
  have heS' : e ∈ DalphaStar D β := ⟨ε, hε, heε⟩
  obtain ⟨k, hkK, hkx⟩ := mul_mul_pow_mem_conjOrbit hC.setup ht hn hord
  have hkx' : k * x * k⁻¹ = x * y * (x * y * w) ^ n := hkx.symm
  have hy'ε : k * y * k⁻¹ ∈ ε :=
    conj_mem_of_mem_Dalpha hC hβ hε hx hy heε hkx'
  obtain ⟨he'D, he'x, he'y⟩ := conj_e_mem_and_commute hC ht hn hord hkK hkx'
  obtain ⟨h2, hy'_eq⟩ := conj_mul_eq_of_mem_conjOrbit hC ht hn hord hkK hkx'
  have hey' : e ≠ k * y * k⁻¹ := by
    intro h
    apply ht.2.2.2.1
    have h' : x * y * (x * y * w) ^ n = k * y * k⁻¹ := h
    exact mul_left_cancel (mul_right_cancel (hkx'.trans h'))
  have hy'D : k * y * k⁻¹ ∈ D := hC.setup.conj_mem k ht.2.1
  have hy'S : k * y * k⁻¹ ∈ DalphaStar D β := ⟨ε, hε, hy'ε⟩
  have he'case : k * (x * y * (x * y * w) ^ n) * k⁻¹ ∈ β ∨
      k * (x * y * (x * y * w) ^ n) * k⁻¹ ∈ DalphaStar D β :=
    Nine.mem_block_or_DalphaStar_of_commute hC hβ hx he'D he'x.symm
  rcases he'case with he'β | he'S
  · exact false_of_conj_data_mem hC hβ hx hy heS' hy'S he'β hey' hy'_eq
  · have hnotall : ¬ ∀ q, q ∈ DalphaStar D β → Commute (k * y * k⁻¹) q := by
      intro hall
      exact hey' (eq_of_forall_commute_of_mem_DalphaStar hC hβ hy'S hall heS')
    rw [not_forall] at hnotall
    obtain ⟨f, hf⟩ := hnotall
    rw [not_imp] at hf
    obtain ⟨hfS, hyf⟩ := hf
    exact false_of_conj_data_DalphaStar hC ht hβ hx hy he'D hy'D
      (he'x.mul_right he'y) h2 hy'_eq hyf hfS

theorem mem_of_isThirdKind_of_mem (hC : HypothesisC D) (hZ : Subgroup.center G = ⊥)
    {x w y : G} (ht : IsTriangle D x w y) (h3 : IsThirdKind x w y) {β : Set G}
    (hβ : β ∈ blockClass hC.alpha) (hx : x ∈ β) (hy : y ∈ β) : w ∈ β := by
  obtain ⟨n, hn, -, hord⟩ := h3
  by_contra hw
  exact (mul_mul_pow_notMem_of_notMem hC hZ ht hn hord hβ hx hy hw)
    (mul_mul_pow_mem_of_mem hC ht hn hord hβ hx hy)

theorem not_commute_of_mem_of_mem (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {ρ : Set G} (hρ : ρ ∈ blockClass hC.alpha) {a b : G} (ha : a ∈ ρ) (hb : b ∈ ρ)
    (hab : a ≠ b) : ¬ Commute a b := by
  intro hcomm
  have hZ : Subgroup.center G = ⊥ := Asc72.eq_bot_of_le_center hrad le_rfl
  obtain ⟨β, hβ⟩ := exists_mem_Dalpha hC
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp (mem_blockClass_of_mem_blockClass hρ hβ.1)
  let a' : G := g * a * g⁻¹
  let b' : G := g * b * g⁻¹
  have ha' : a' ∈ β := by rw [hg]; exact ⟨a, ha, rfl⟩
  have hb' : b' ∈ β := by rw [hg]; exact ⟨b, hb, rfl⟩
  have ha'b' : a' ≠ b' := by
    intro h
    apply hab
    calc a = g⁻¹ * a' * g := by simp only [a']; group
      _ = g⁻¹ * b' * g := by rw [h]
      _ = b := by simp only [b']; group
  have hcomm' : Commute a' b' := by
    have h := hcomm.conj g
    simpa only [a', b'] using h
  obtain ⟨γ, hγ, hγperp, htri3⟩ :=
    exists_isThirdKind_of_commute_of_mem h86 h87 hC hrad hO4 hF hne hβ ha' hb' ha'b' hcomm'
  obtain ⟨c, hc⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hγ.1
  obtain ⟨htri, hthird⟩ := htri3 c hc
  have hcβ : c ∈ β :=
    mem_of_isThirdKind_of_mem hC hZ htri hthird hβ.1 ha' hb'
  have hγβ : γ = β :=
    eq_of_mem_of_mem_blockClass hC.isBlock_alpha hγ.1 hβ.1 ⟨c, hc, hcβ⟩
  rw [hγβ] at hγperp
  exact hγperp (mem_perp_iff.mpr (Or.inr rfl))

theorem setOf_commute_mem_conjOrbit_eq (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) :
    {r | r ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x ∧ Commute r x} =
      {x, y, x * y * (x * y * w) ^ n} := by
  classical
  let z : G := (x * y * w) ^ n
  let e : G := x * y * z
  change {r | r ∈ conjOrbit (localGroup D z) x ∧ Commute r x} = {x, y, e}
  obtain ⟨-, -, hzx, -, -, heD⟩ :=
    IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord
  have hze : x * y * e = z := mul_mul_mul_mul_cancel_of_isTriangle hC.setup.oddT ht z
  have hex : Commute e x :=
    commute_mul_mul_pow_left hC.setup.oddT hC.setup.normal ht hn hord
  have hey : Commute e y :=
    commute_mul_mul_pow_right hC.setup.oddT hC.setup.normal ht hn hord
  ext r
  constructor
  · rintro ⟨hrO, hrx⟩
    have hrcent : r ∈ centSet D z :=
      conjOrbit_subset_centSet hC.setup.normal ⟨ht.1, hzx.symm⟩ hrO
    have h27 := commute_iff_commute_of_mem_centSet hC.setup ht hn hord hrcent
    have hry : Commute r y := h27.1.mp hrx
    have hre : Commute r e := h27.2.mp hrx
    obtain ⟨ρ, hρ, hrρ⟩ :=
      exists_mem_blockClass_of_mem hC.setup.isClass hC.isBlock_alpha hrcent.1
    have hyO : y ∈ conjOrbit (localGroup D (x * y * e)) x := by
      rw [hze]
      exact (mem_conjOrbit_of_third_kind hC.setup ht hn hord).1
    have heO : e ∈ conjOrbit (localGroup D (x * y * e)) x := by
      rw [hze]
      exact mul_mul_pow_mem_conjOrbit hC.setup ht hn hord
    have hrO' : r ∈ conjOrbit (localGroup D (x * y * e)) x := by
      rw [hze]
      exact hrO
    have h23 := mem_or_mem_or_mem_of_mem_conjOrbit hC hne ht.1 ht.2.1 heD
      ht.2.2.2.2.1 hex.symm hey.symm hyO heO hrO' hrx hry hρ hrρ
    rcases h23 with hxρ | hyρ | heρ
    · have hrx_eq : r = x := by
        by_contra hrx_ne
        exact (not_commute_of_mem_of_mem h86 h87 hC hrad hO4 hF hne hρ hrρ hxρ hrx_ne) hrx
      rw [hrx_eq]
      simp
    · have hry_eq : r = y := by
        by_contra hry_ne
        exact (not_commute_of_mem_of_mem h86 h87 hC hrad hO4 hF hne hρ hrρ hyρ hry_ne) hry
      rw [hry_eq]
      simp
    · have hre_eq : r = e := by
        by_contra hre_ne
        exact (not_commute_of_mem_of_mem h86 h87 hC hrad hO4 hF hne hρ hrρ heρ hre_ne) hre
      rw [hre_eq]
      simp
  · intro hr
    have hr' : r = x ∨ r = y ∨ r = e := by
      simpa using hr
    rcases hr' with hrx | hry | hre
    · rw [hrx]
      exact ⟨self_mem_conjOrbit (localGroup D z) x, Commute.refl x⟩
    · rw [hry]
      exact ⟨(mem_conjOrbit_of_third_kind hC.setup ht hn hord).1, ht.2.2.2.2.1.symm⟩
    · rw [hre]
      exact ⟨mul_mul_pow_mem_conjOrbit hC.setup ht hn hord, hex⟩

end CFSG.OddTranspositions.PartThree.EightEight

end
