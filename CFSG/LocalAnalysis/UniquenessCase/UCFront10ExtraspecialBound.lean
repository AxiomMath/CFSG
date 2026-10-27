module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.GH74.GLS.LU.Local.Core
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open Subgroup

namespace ExtraspecialBound

variable {X : Type} [Group X] {p : ℕ} {A : Subgroup X}

theorem card_fixed_sq_le_of_commutator_inverts [Finite X] (hp : p.Prime) (hp2 : p ≠ 2)
    (hA : IsElementaryAbelian p A) (hA1 : A ≠ ⊥) {x y z : X} (hxA : x ∈ normalizer (A : Set X))
    (hyA : y ∈ normalizer (A : Set X)) (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1)
    (hxy : x * y * x⁻¹ * y⁻¹ = z) (hinv : ∀ a ∈ A, z * a * z⁻¹ = a⁻¹) :
    A ⊓ centralizer {x} ≠ ⊥ ∧ Nat.card ↥(A ⊓ centralizer {x}) ^ 2 ≤ Nat.card A := by
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.toIsMulCommutative.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
  have hxx : x * x = 1 := by rw [← sq]; exact hx2
  have hyy : y * y = 1 := by rw [← sq]; exact hy2
  have hconj : ∀ g ∈ normalizer (A : Set X), ∀ a ∈ A, g * a * g⁻¹ ∈ A :=
    fun g hg a ha => (mem_normalizer_iff.mp hg a).mp ha
  have hxyz : x * y = z * y * x := by rw [← hxy]; group
  have hxy_conj : ∀ b : X, x * (y * b * y⁻¹) * x⁻¹ = z * (y * (x * b * x⁻¹) * y⁻¹) * z⁻¹ := by
    intro b
    calc x * (y * b * y⁻¹) * x⁻¹ = (x * y) * b * (x * y)⁻¹ := by group
      _ = (z * y * x) * b * (z * y * x)⁻¹ := by rw [hxyz]
      _ = z * (y * (x * b * x⁻¹) * y⁻¹) * z⁻¹ := by group
  have hyy_conj : ∀ b : X, y * (y * b * y⁻¹) * y⁻¹ = b := by
    intro b
    calc y * (y * b * y⁻¹) * y⁻¹ = (y * y) * b * (y * y)⁻¹ := by group
      _ = b := by rw [hyy]; group
  have hcx : ∀ a : X, a ∈ centralizer {x} ↔ x * a * x⁻¹ = a := by
    intro a
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro h
      rw [← h]
      group
    · intro h
      calc a * x = (x * a * x⁻¹) * x := by rw [h]
        _ = x * a := by group
  have hto : ∀ a ∈ A ⊓ centralizer {x},
      y * a * y⁻¹ ∈ A ∧ x * (y * a * y⁻¹) * x⁻¹ = (y * a * y⁻¹)⁻¹ := by
    intro a hmem
    obtain ⟨ha, hc⟩ := mem_inf.mp hmem
    have hb := hconj y hyA a ha
    exact ⟨hb, by rw [hxy_conj, (hcx a).mp hc, hinv _ hb]⟩
  have hof : ∀ b ∈ A, x * b * x⁻¹ = b⁻¹ → y * b * y⁻¹ ∈ A ⊓ centralizer {x} := by
    intro b hb hbx
    have ha := hconj y hyA b hb
    refine mem_inf.mpr ⟨ha, (hcx _).mpr ?_⟩
    rw [hxy_conj, hbx]
    calc z * (y * b⁻¹ * y⁻¹) * z⁻¹ = (z * (y * b * y⁻¹) * z⁻¹)⁻¹ := by group
      _ = y * b * y⁻¹ := by rw [hinv _ ha, inv_inv]
  let e : ↥(A ⊓ centralizer {x}) ≃ {b : X // b ∈ A ∧ x * b * x⁻¹ = b⁻¹} :=
    { toFun := fun a => ⟨y * a * y⁻¹, hto a a.2⟩
      invFun := fun b => ⟨y * b * y⁻¹, hof b b.2.1 b.2.2⟩
      left_inv := fun a => Subtype.ext (hyy_conj a)
      right_inv := fun b => Subtype.ext (hyy_conj b) }
  have hfix : ∀ w ∈ A, x * w * x⁻¹ = w → x * w * x⁻¹ = w⁻¹ → w = 1 := by
    intro w hw h1 h2
    have hww : w = w⁻¹ := h1.symm.trans h2
    have hw2 : w ^ 2 = 1 := by
      calc w ^ 2 = w * w⁻¹ := by rw [sq]; nth_rewrite 2 [hww]; rfl
        _ = 1 := mul_inv_cancel w
    have hwp : w ^ p = 1 := by
      have := hA
      exact elemPow_eq_one_of_isElementaryAbelian w hw
    exact (pow_eq_one_iff_of_coprime ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)).mp
      ⟨hwp, hw2⟩
  have hmA : ∀ u : ↥(A ⊓ centralizer {x}), (u : X) ∈ A := fun u => (mem_inf.mp u.2).1
  have hmC : ∀ u : ↥(A ⊓ centralizer {x}), (u : X) ∈ centralizer {x} :=
    fun u => (mem_inf.mp u.2).2
  let f : ↥(A ⊓ centralizer {x}) × {b : X // b ∈ A ∧ x * b * x⁻¹ = b⁻¹} → ↥A :=
    fun uv => ⟨uv.1 * uv.2.1, A.mul_mem (hmA uv.1) uv.2.2.1⟩
  have hf : Function.Injective f := by
    rintro ⟨u, v⟩ ⟨u', v'⟩ h
    have h' : (u : X) * v.1 = u' * v'.1 := congrArg Subtype.val h
    have hw : (u' : X)⁻¹ * u = v'.1 * v.1⁻¹ := by
      calc (u' : X)⁻¹ * u = (u' : X)⁻¹ * (u * v.1) * v.1⁻¹ := by group
        _ = (u' : X)⁻¹ * (u' * v'.1) * v.1⁻¹ := by rw [h']
        _ = v'.1 * v.1⁻¹ := by group
    have hwA : (u' : X)⁻¹ * u ∈ A := A.mul_mem (A.inv_mem (hmA u')) (hmA u)
    have h1 : x * ((u' : X)⁻¹ * u) * x⁻¹ = (u' : X)⁻¹ * u :=
      (hcx _).mp (mul_mem (inv_mem (hmC u')) (hmC u))
    have h2 : x * ((u' : X)⁻¹ * u) * x⁻¹ = ((u' : X)⁻¹ * u)⁻¹ := by
      rw [hw]
      calc x * (v'.1 * v.1⁻¹) * x⁻¹ = (x * v'.1 * x⁻¹) * (x * v.1 * x⁻¹)⁻¹ := by group
        _ = v'.1⁻¹ * (v.1⁻¹)⁻¹ := by rw [v'.2.2, v.2.2]
        _ = (v'.1 * v.1⁻¹)⁻¹ := by
          rw [inv_inv, hcomm _ (A.inv_mem v'.2.1) _ v.2.1]
          group
    have hu : (u : X) = u' := by
      calc (u : X) = u' * ((u' : X)⁻¹ * u) := by group
        _ = u' := by rw [hfix _ hwA h1 h2, mul_one]
    have hv : v.1 = v'.1 := by
      rw [hu] at h'
      exact mul_left_cancel h'
    exact Prod.ext (Subtype.ext hu) (Subtype.ext hv)
  have hcard : Nat.card ↥(A ⊓ centralizer {x}) *
      Nat.card {b : X // b ∈ A ∧ x * b * x⁻¹ = b⁻¹} ≤ Nat.card A := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_injective f hf
  have heq : Nat.card ↥(A ⊓ centralizer {x}) = Nat.card {b : X // b ∈ A ∧ x * b * x⁻¹ = b⁻¹} :=
    Nat.card_congr e
  refine ⟨?_, ?_⟩
  · intro hP
    apply hA1
    rw [eq_bot_iff]
    intro a ha
    rw [mem_bot]
    have hxa : x * a * x⁻¹ ∈ A := hconj x hxA a ha
    have hb : a * (x * a * x⁻¹) ∈ A ⊓ centralizer {x} := by
      refine mem_inf.mpr ⟨A.mul_mem ha hxa, (hcx _).mpr ?_⟩
      calc x * (a * (x * a * x⁻¹)) * x⁻¹ = (x * a * x⁻¹) * ((x * x) * a * (x * x)⁻¹) := by
            group
        _ = (x * a * x⁻¹) * a := by rw [hxx]; group
        _ = a * (x * a * x⁻¹) := hcomm _ hxa _ ha
    rw [hP, mem_bot] at hb
    have hy := hof a ha (eq_inv_of_mul_eq_one_right hb)
    rw [hP, mem_bot] at hy
    calc a = y⁻¹ * (y * a * y⁻¹) * y := by group
      _ = 1 := by rw [hy]; group
  · calc Nat.card ↥(A ⊓ centralizer {x}) ^ 2
        = Nat.card ↥(A ⊓ centralizer {x}) * Nat.card ↥(A ⊓ centralizer {x}) := sq _
      _ = Nat.card ↥(A ⊓ centralizer {x}) * Nat.card {b : X // b ∈ A ∧ x * b * x⁻¹ = b⁻¹} := by
          rw [← heq]
      _ ≤ Nat.card A := hcard

end ExtraspecialBound

open ExtraspecialBound

variable {X : Type} [Group X] [Finite X]

theorem pow_two_pow_le_card_of_config {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup X}
    (hA : IsElementaryAbelian p A) (hA1 : A ≠ ⊥) {z : X} (hz2 : z ^ 2 = 1)
    (hfree : A ⊓ centralizer {z} = ⊥) (x y : Fin n → X)
    (hxA : ∀ i, x i ∈ normalizer (A : Set X)) (hyA : ∀ i, y i ∈ normalizer (A : Set X))
    (hx2 : ∀ i, x i ^ 2 = 1) (hy2 : ∀ i, y i ^ 2 = 1)
    (hxy : ∀ i, x i * y i * (x i)⁻¹ * (y i)⁻¹ = z)
    (hcx : ∀ i j, i ≠ j → Commute (x i) (x j))
    (hcxy : ∀ i j, i ≠ j → Commute (x i) (y j)) :
    p ^ (2 ^ n) ≤ Nat.card A := by
  induction n generalizing A with
  | zero =>
    have : Fact p.Prime := ⟨hp⟩
    rcases bot_or_exists_ne_one A with h | ⟨a, ha, ha1⟩
    · exact absurd h hA1
    have hpa : a ^ p = 1 := by
      have := hA
      exact elemPow_eq_one_of_isElementaryAbelian a ha
    have hdvd : p ∣ Nat.card A := by
      rw [← orderOf_eq_prime hpa ha1]
      exact Subgroup.orderOf_dvd_natCard A ha
    rw [pow_zero, pow_one]
    exact Nat.le_of_dvd Nat.card_pos hdvd
  | succ n ih =>
    have hzN : z ∈ normalizer (A : Set X) := by
      rw [← hxy (Fin.last n)]
      exact mul_mem (mul_mem (mul_mem (hxA _) (hyA _)) (inv_mem (hxA _))) (inv_mem (hyA _))
    have hzz : z * z = 1 := by rw [← sq]; exact hz2
    have hfix : ∀ a ∈ A, z * a * z⁻¹ = a → a = 1 := by
      intro a ha h
      have hc : a ∈ A ⊓ centralizer {z} := by
        refine mem_inf.mpr ⟨ha, mem_centralizer_singleton_iff.mpr ?_⟩
        calc a * z = (z * a * z⁻¹) * z := by rw [h]
          _ = z * a := by group
      rwa [hfree, mem_bot] at hc
    have hinv := CFSG.GH74.GLS.LU.Local.inverts_of_fixed_eq_bot hzz
      (fun a ha b hb =>
        congrArg Subtype.val (hA.toIsMulCommutative.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩))
      (fun a ha => (mem_normalizer_iff.mp hzN a).mp ha) hfix
    obtain ⟨hP1, hPc⟩ := card_fixed_sq_le_of_commutator_inverts hp hp2 hA hA1 (hxA (Fin.last n))
      (hyA (Fin.last n)) (hx2 _) (hy2 _) (hxy _) hinv
    have hnorm : ∀ g, g ∈ normalizer (A : Set X) → Commute g (x (Fin.last n)) →
        g ∈ normalizer ((A ⊓ centralizer {x (Fin.last n)} : Subgroup X) : Set X) :=
      fun g hg hgx => inf_normalizer_le_normalizer_inf
        (mem_inf.mpr ⟨hg, le_normalizer (mem_centralizer_singleton_iff.mpr hgx.eq)⟩)
    have hne : ∀ i : Fin n, i.castSucc ≠ Fin.last n := fun i => (Fin.castSucc_lt_last i).ne
    have hne' : ∀ i j : Fin n, i ≠ j → i.castSucc ≠ j.castSucc :=
      fun i j hij h => hij (Fin.castSucc_injective n h)
    have key := ih (A := A ⊓ centralizer {x (Fin.last n)})
      (hA := hA.of_le inf_le_left) (hA1 := hP1)
      (hfree := eq_bot_iff.mpr fun a ha => by
        rw [← hfree]
        exact mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp ha).1).1, (mem_inf.mp ha).2⟩)
      (x := fun i => x i.castSucc) (y := fun i => y i.castSucc)
      (hxA := fun i => hnorm _ (hxA _) (hcx _ _ (hne i)))
      (hyA := fun i => hnorm _ (hyA _) (hcxy _ _ (hne i).symm).symm)
      (hx2 := fun i => hx2 _) (hy2 := fun i => hy2 _) (hxy := fun i => hxy _)
      (hcx := fun i j hij => hcx _ _ (hne' i j hij))
      (hcxy := fun i j hij => hcxy _ _ (hne' i j hij))
    calc p ^ 2 ^ (n + 1) = (p ^ 2 ^ n) ^ 2 := by rw [← pow_mul, ← pow_succ]
      _ ≤ Nat.card ↥(A ⊓ centralizer {x (Fin.last n)}) ^ 2 := Nat.pow_le_pow_left key 2
      _ ≤ Nat.card A := hPc

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
