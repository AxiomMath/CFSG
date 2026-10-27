module

public import CFSG.RankThree.PartOne.S11c.SporadicPlaneHSMcL
public import CFSG.RankThree.PartOne.S11c.OuterInner
public import CFSG.RankThree.PartOne.S11c.HeisenbergSylow
public import CFSG.RankThree.PartOne.SPOR.Outer
public import CFSG.Sporadic.HNSchreier.Algebra

public section

namespace CFSG.RankThree.PartOne.HNRed

open Subgroup CFSG
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.RankThree.PartOne (PlaneOn PlaneCentralizes)

section Hom

variable {G : Type*} [Group G]

@[expose] def fiveHom2 (x y : G) (hx : x ^ 5 = 1) (hy : y ^ 5 = 1) (hxy : Commute x y) :
    Multiplicative (ZMod 5 × ZMod 5) →* G where
  toFun a := x ^ (Multiplicative.toAdd a).1.val * y ^ (Multiplicative.toAdd a).2.val
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ZMod.val_add]
    rw [← pow_eq_pow_mod _ hx, ← pow_eq_pow_mod _ hy, pow_add, pow_add]
    calc x ^ (Multiplicative.toAdd a).1.val * x ^ (Multiplicative.toAdd b).1.val *
          (y ^ (Multiplicative.toAdd a).2.val * y ^ (Multiplicative.toAdd b).2.val) =
        x ^ (Multiplicative.toAdd a).1.val * (x ^ (Multiplicative.toAdd b).1.val *
          y ^ (Multiplicative.toAdd a).2.val) * y ^ (Multiplicative.toAdd b).2.val := by
          simp only [mul_assoc]
      _ = x ^ (Multiplicative.toAdd a).1.val * (y ^ (Multiplicative.toAdd a).2.val *
          x ^ (Multiplicative.toAdd b).1.val) * y ^ (Multiplicative.toAdd b).2.val := by
          rw [(hxy.pow_pow (Multiplicative.toAdd b).1.val (Multiplicative.toAdd a).2.val).eq]
      _ = _ := by simp only [mul_assoc]

theorem fiveHom2_apply (x y : G) (hx : x ^ 5 = 1) (hy : y ^ 5 = 1) (hxy : Commute x y)
    (a : Multiplicative (ZMod 5 × ZMod 5)) :
    fiveHom2 x y hx hy hxy a =
      x ^ (Multiplicative.toAdd a).1.val * y ^ (Multiplicative.toAdd a).2.val := rfl

theorem fiveHom2_pow_five (x y : G) (hx : x ^ 5 = 1) (hy : y ^ 5 = 1) (hxy : Commute x y)
    (a : Multiplicative (ZMod 5 × ZMod 5)) : fiveHom2 x y hx hy hxy a ^ 5 = 1 := by
  rw [← map_pow]
  have h3 : ∀ u : ZMod 5, 5 * u = 0 := fun u => by
    have : (5 : ZMod 5) = 0 := by decide
    rw [this, zero_mul]
  have : a ^ 5 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    ext
    · simpa using h3 (Multiplicative.toAdd a).1
    · simpa using h3 (Multiplicative.toAdd a).2
  rw [this, map_one]

theorem fiveHom2_injective (x y : G) (hx : x ^ 5 = 1) (hy : y ^ 5 = 1) (hxy : Commute x y)
    (hind : ∀ i j : ℕ, x ^ i * y ^ j = 1 → 5 ∣ i ∧ 5 ∣ j) :
    Function.Injective (fiveHom2 x y hx hy hxy) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  obtain ⟨⟨u, w⟩, rfl⟩ : ∃ p : ZMod 5 × ZMod 5, a = Multiplicative.ofAdd p :=
    ⟨a.toAdd, rfl⟩
  have h := hind u.val w.val ha
  have hu : u = 0 := by
    rw [← ZMod.natCast_zmod_val u, (ZMod.natCast_eq_zero_iff u.val 5).2 h.1]
  have hw : w = 0 := by
    rw [← ZMod.natCast_zmod_val w, (ZMod.natCast_eq_zero_iff w.val 5).2 h.2]
  rw [hu, hw]
  rfl

end Hom

section HS

theorem hs_simple_nonab :
    IsSimpleGroup (Carrier .HS) ∧ ∃ a b : Carrier .HS, a * b ≠ b * a := by
  have hs : IsSimpleGroup (Carrier .HS) := CFSG.Sporadic.HS.isSimpleGroup_HS
  refine ⟨hs, ?_⟩
  by_contra hcomm
  have hcomm' : ∀ a b : Carrier .HS, a * b = b * a := fun a b =>
    by_contra fun h => hcomm ⟨a, b, h⟩
  let _ : CommGroup (Carrier .HS) := { (inferInstance : Group (Carrier .HS)) with
    mul_comm := hcomm' }
  have hp := IsSimpleGroup.prime_card (α := Carrier .HS)
  have hcard : Nat.card (Carrier .HS) = 44352000 := CFSG.Sporadic.HS.card_HS
  rw [hcard] at hp
  norm_num at hp

end HS

section Plane

theorem mulAut_mul_conj_mul_inv {G : Type*} [Group G] (φ : MulAut G) (g : G) :
    φ * MulAut.conj g * φ⁻¹ = MulAut.conj (φ g) := by
  ext x
  simp [MulAut.conj_apply, MulAut.mul_apply]

theorem inv_conj_mem_of_pow_five {G : Type*} [Group G] {N : Subgroup G} {y : G} (hy : y ^ 5 = 1)
    (h1 : ∀ n ∈ N, y * n * y⁻¹ ∈ N) : ∀ n ∈ N, y⁻¹ * n * y ∈ N := by
  intro n hn
  have hk : ∀ k : ℕ, y ^ k * n * (y ^ k)⁻¹ ∈ N := by
    intro k
    induction k with
    | zero => simpa using hn
    | succ k ih =>
      have h := h1 _ ih
      have e : y * (y ^ k * n * (y ^ k)⁻¹) * y⁻¹ = y ^ (k + 1) * n * (y ^ (k + 1))⁻¹ := by group
      rwa [e] at h
  have h4 := hk 4
  have hinv : y ^ 4 = y⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hy
  rw [hinv, inv_inv] at h4
  exact h4

theorem hs_pair_centralizes
    (a b : MulAut (Carrier .HS)) (hab : a * b = b * a) (ha : a ^ 5 = 1) (hb : b ^ 5 = 1)
    (hind : ∀ i j : ℕ, a ^ i * b ^ j = 1 → 5 ∣ i ∧ 5 ∣ j)
    (S : Subgroup (MulAut (Carrier .HS))) (hS : IsPGroup 2 S)
    (hSa : ∀ s ∈ S, a * s * a⁻¹ ∈ S) (hSb : ∀ s ∈ S, b * s * b⁻¹ ∈ S) :
    ∀ s ∈ S, a * s = s * a := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨hsimp, hnab⟩ := hs_simple_nonab
  have hfin : Finite (Carrier .HS) :=
    Nat.finite_of_card_ne_zero (by
      rw [show Nat.card (Carrier .HS) = 44352000 from CFSG.Sporadic.HS.card_HS]
      norm_num)
  have hcenter : Subgroup.center (Carrier .HS) = ⊥ :=
    CFSG.RankThree.PartOne.center_eq_bot_of_simple hnab
  have hinj := CFSG.RankThree.PartOne.conj_injective_of_center_eq_bot hcenter
  have hOut : ¬ 5 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (Carrier .HS)) := by
    have h2 := CFSG.RankThree.PartOne.SPOR.card_outer_HS_le_two
    intro hd
    have := Nat.le_of_dvd Nat.card_pos hd
    omega
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.exists_inner_of_pow_eq_one_of_not_dvd_card_outer
    Nat.prime_five hOut a ha
  have hcomm : Commute a b := hab
  have hψ : Function.Injective (fiveHom2 a b ha hb hcomm) :=
    fiveHom2_injective a b ha hb hcomm hind
  let E : Subgroup (MulAut (Carrier .HS)) := (fiveHom2 a b ha hb hcomm).range
  have : Fact (1 < 5) := ⟨by norm_num⟩
  have haE : a ∈ E := ⟨Multiplicative.ofAdd ((1 : ZMod 5), (0 : ZMod 5)), by
    rw [fiveHom2_apply]
    simp [ZMod.val_one]⟩
  have haN : a ∈ Subgroup.normalizer (S : Set (MulAut (Carrier .HS))) :=
    mem_normalizer_of_conj_mem hSa (inv_conj_mem_of_pow_five ha hSa)
  have hbN : b ∈ Subgroup.normalizer (S : Set (MulAut (Carrier .HS))) :=
    mem_normalizer_of_conj_mem hSb (inv_conj_mem_of_pow_five hb hSb)
  have hEN : ∀ e ∈ E, ∀ s ∈ S, e * s * e⁻¹ ∈ S := by
    intro e he s hs
    obtain ⟨x, rfl⟩ := he
    have hxN : fiveHom2 a b ha hb hcomm x ∈
        Subgroup.normalizer (S : Set (MulAut (Carrier .HS))) := by
      rw [fiveHom2_apply]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ haN _) (Subgroup.pow_mem _ hbN _)
    exact (Subgroup.mem_normalizer_iff.1 hxN s).1 hs
  have hEel : IsElementaryAbelian 5 E := by
    refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩, exponent_dvd_p := ?_ }
    · obtain ⟨x, hx⟩ := x
      obtain ⟨y, hy⟩ := y
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨v, rfl⟩ := hy
      apply Subtype.ext
      show fiveHom2 a b ha hb hcomm u * fiveHom2 a b ha hb hcomm v =
        fiveHom2 a b ha hb hcomm v * fiveHom2 a b ha hb hcomm u
      rw [← map_mul, ← map_mul, mul_comm u v]
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => ?_
      obtain ⟨x, hx⟩ := x
      obtain ⟨u, rfl⟩ := hx
      exact Subtype.ext (fiveHom2_pow_five a b ha hb hcomm u)
  have hEcard : Nat.card E = 5 ^ 2 := by
    have h1 : Nat.card E = Nat.card (Multiplicative (ZMod 5 × ZMod 5)) :=
      (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm
    rw [h1, Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_prod, ZMod.card]
    norm_num
  let U : Subgroup (Carrier .HS) := S.comap (MulAut.conj : Carrier .HS →* MulAut (Carrier .HS))
  have hU2 : IsPGroup 2 U := by
    intro x
    obtain ⟨k, hk⟩ := hS ⟨MulAut.conj (x : Carrier .HS), x.2⟩
    refine ⟨k, Subtype.ext (hinj ?_)⟩
    have h1 : (MulAut.conj (x : Carrier .HS)) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    show MulAut.conj ((x : Carrier .HS) ^ 2 ^ k) = MulAut.conj 1
    rw [map_pow, map_one]
    exact h1
  have hnorm : ∀ e ∈ E, ∀ u ∈ U, e u ∈ U := by
    intro e he u hu
    have h1 := hEN e he _ hu
    rw [mulAut_mul_conj_mul_inv] at h1
    exact h1
  have hplane : PlaneOn 5 E U := ⟨Nat.prime_five, by norm_num, hEel, hEcard, hU2, hnorm⟩
  have hcent : PlaneCentralizes E U :=
    sporadicPlanesCentralize_HS (Carrier .HS) hsimp hnab ⟨MulEquiv.refl _⟩ 5 E U hplane
  intro s hs
  set c : MulAut (Carrier .HS) := a * s * a⁻¹ * s⁻¹ with hc
  have hcS : c ∈ S := S.mul_mem (hSa s hs) (S.inv_mem hs)
  have hcx : c = MulAut.conj (g * s g⁻¹) := by
    have h1 := mulAut_mul_conj_mul_inv s g⁻¹
    rw [map_inv] at h1
    rw [map_mul, ← h1, hc, ← hg]
    group
  have hxU : g * s g⁻¹ ∈ U := by
    show MulAut.conj (g * s g⁻¹) ∈ S
    rw [← hcx]
    exact hcS
  have hax : a (g * s g⁻¹) = g * s g⁻¹ := hcent a haE _ hxU
  have hac : a * c * a⁻¹ = c := by
    rw [hcx, mulAut_mul_conj_mul_inv, hax]
  have hacomm : a * c = c * a := mul_inv_eq_iff_eq_mul.1 hac
  have hcs : a * s * a⁻¹ = c * s := by rw [hc]; group
  have hit : ∀ k : ℕ, a ^ k * s * (a ^ k)⁻¹ = c ^ k * s := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e1 : a ^ (k + 1) * s * (a ^ (k + 1))⁻¹ = a * (a ^ k * s * (a ^ k)⁻¹) * a⁻¹ := by
        group
      have hpow : a * c ^ k = c ^ k * a := (Commute.pow_right hacomm k).eq
      rw [e1, ih]
      calc a * (c ^ k * s) * a⁻¹ = (a * c ^ k) * s * a⁻¹ := by group
        _ = (c ^ k * a) * s * a⁻¹ := by rw [hpow]
        _ = c ^ k * (a * s * a⁻¹) := by group
        _ = c ^ k * (c * s) := by rw [hcs]
        _ = c ^ (k + 1) * s := by rw [pow_succ]; group
  have h5 := hit 5
  rw [ha, inv_one, one_mul, mul_one] at h5
  have hc5 : c ^ 5 = 1 := by
    have : c ^ 5 * s = 1 * s := by rw [one_mul]; exact h5.symm
    exact mul_right_cancel this
  obtain ⟨m, hm⟩ := hS ⟨c, hcS⟩
  have hm' : c ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hcop : Nat.Coprime (2 ^ m) 5 := Nat.Coprime.pow_left m (by norm_num)
  have hord : orderOf c = 1 := by
    have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm') (orderOf_dvd_of_pow_eq_one hc5)
    rw [hcop.gcd_eq_one] at h1
    exact Nat.dvd_one.1 h1
  have hc1 : c = 1 := orderOf_eq_one_iff.1 hord
  have h6 : a * s * a⁻¹ * s⁻¹ = 1 := by rw [← hc]; exact hc1
  have h7 : a * s * a⁻¹ = s := mul_inv_eq_one.1 h6
  exact mul_inv_eq_iff_eq_mul.1 h7

end Plane

end CFSG.RankThree.PartOne.HNRed
