module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem subtype_preimage_card {α β : Type*} [Finite α] [Finite β]
    (f : α → β) (q : β → Prop) (k : ℕ)
    (hfib : ∀ y, q y → Nat.card {x : α // f x = y} = k) :
    Nat.card {x : α // q (f x)} = k * Nat.card {y : β // q y} := by
  have h1 : Nat.card (Σ y : {y : β // q y}, {x : α // f x = y}) =
      Nat.card {x : α // q (f x)} :=
    Nat.card_congr (Equiv.sigmaSubtypeFiberEquivSubtype f (p := fun x => q (f x))
      (q := q) (fun x => Iff.rfl))
  rw [← h1]
  haveI : Fintype {y : β // q y} := Fintype.ofFinite _
  rw [Nat.card_sigma]
  have h2 : ∀ y : {y : β // q y}, Nat.card {x : α // f x = y.1} = k :=
    fun y => hfib y.1 y.2
  rw [Finset.sum_congr rfl fun y _ => h2 y, Finset.sum_const, Finset.card_univ]
  rw [Nat.nsmul_eq_mul, ← Nat.card_eq_fintype_card, mul_comm]

theorem coe_mul_self_eq_one_iff {G H : Type*} [Group G] [Group H] {Q : Subgroup G}
    (e : ↥Q ≃* H) (q : ↥Q) : e q * e q = 1 ↔ (q : G) * q = 1 := by
  rw [← map_mul, MulEquiv.map_eq_one_iff, Subtype.ext_iff]
  rfl

variable {Q D N : Subgroup G}

def q8d8MulHom (hcomm : ∀ q ∈ Q, ∀ d ∈ D, q * d = d * q) (hsup : Q ⊔ D = N) :
    ↥Q × ↥D →* ↥N where
  toFun p := ⟨(p.1 : G) * (p.2 : G), hsup ▸ Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' p p' := Subtype.ext (by
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    calc (p.1 : G) * p'.1 * ((p.2 : G) * p'.2)
        = (p.1 : G) * ((p'.1 : G) * (p.2 : G)) * p'.2 := by group
      _ = (p.1 : G) * ((p.2 : G) * (p'.1 : G)) * p'.2 :=
        by rw [hcomm (p'.1 : G) p'.1.2 (p.2 : G) p.2.2]
      _ = (p.1 : G) * p.2 * ((p'.1 : G) * p'.2) := by group)

lemma q8d8MulHom_surjective (hcomm : ∀ q ∈ Q, ∀ d ∈ D, q * d = d * q)
    (hsup : Q ⊔ D = N) : Function.Surjective (q8d8MulHom hcomm hsup) := by
  intro n
  have hNle : N ≤ Q ⊔ D := by rw [← hsup]
  obtain ⟨q, hq, d, hd, hqd⟩ :=
    CFSG.GH74.Uniqueness.SU.SU5.mem_sup_of_commute hcomm (hNle n.2)
  exact ⟨(⟨q, hq⟩, ⟨d, hd⟩), Subtype.ext hqd⟩

lemma q8d8MulHom_ker_card (hcomm : ∀ q ∈ Q, ∀ d ∈ D, q * d = d * q)
    (hsup : Q ⊔ D = N) (eQ : ↥Q ≃* QuaternionGroup 2) (eD : ↥D ≃* DihedralGroup 4)
    (hNcard : Nat.card ↥N = 32) : Nat.card (q8d8MulHom hcomm hsup).ker = 2 := by
  have h1 := Subgroup.card_ker_mul_card_of_surjective
    (q8d8MulHom_surjective hcomm hsup)
  have hdom : Nat.card (↥Q × ↥D) = 64 := by
    rw [Nat.card_prod, Nat.card_congr eQ.toEquiv, Nat.card_congr eD.toEquiv,
      CFSG.GH74.Uniqueness.SU.SU5.card_q8, CFSG.GH74.Uniqueness.SU.SU5.card_d8]
  rw [hdom, hNcard] at h1
  omega

def q8d8FiberEquivKer (hcomm : ∀ q ∈ Q, ∀ d ∈ D, q * d = d * q)
    (hsup : Q ⊔ D = N) (a : ↥Q × ↥D) :
    {x : ↥Q × ↥D // q8d8MulHom hcomm hsup x = q8d8MulHom hcomm hsup a} ≃
      (q8d8MulHom hcomm hsup).ker where
  toFun x := ⟨a⁻¹ * x.1, by
    rw [MonoidHom.mem_ker, map_mul, map_inv, x.2, inv_mul_cancel]⟩
  invFun k := ⟨a * k.1, by rw [map_mul, MonoidHom.mem_ker.mp k.2, mul_one]⟩
  left_inv x := Subtype.ext (by group)
  right_inv k := Subtype.ext (by group)

lemma q8d8_mul_sq_eq_one_iff (hcomm : ∀ q ∈ Q, ∀ d ∈ D, q * d = d * q)
    (hsup : Q ⊔ D = N) {ζ : G}
    (hζsq : ∀ n ∈ N, n * n = 1 ∨ n * n = ζ) (hζne : ζ ≠ 1) (hζsq1 : ζ * ζ = 1)
    (q : ↥Q) (d : ↥D) :
    ((q : G) * d) * ((q : G) * d) = 1 ↔ ((q : G) * q = 1 ↔ (d : G) * d = 1) := by
  have hqd : ((q : G) * d) * ((q : G) * d) = ((q : G) * q) * ((d : G) * d) := by
    calc ((q : G) * d) * ((q : G) * d) = (q : G) * (d * (q : G)) * d := by group
      _ = (q : G) * ((q : G) * d) * d := by rw [← hcomm (q : G) q.2 (d : G) d.2]
      _ = ((q : G) * q) * ((d : G) * d) := by group
  have hq := hζsq (q : G) (hsup ▸ Subgroup.mem_sup_left q.2)
  have hd := hζsq (d : G) (hsup ▸ Subgroup.mem_sup_right d.2)
  rw [hqd]
  constructor
  · intro h
    rcases hq with hq1 | hq1 <;> rcases hd with hd1 | hd1
    · exact ⟨fun _ => hd1, fun _ => hq1⟩
    · rw [hq1, hd1, one_mul] at h
      exact absurd h hζne
    · rw [hq1, hd1, mul_one] at h
      exact absurd h hζne
    · exact ⟨fun h' => absurd h' (by rw [hq1]; exact hζne),
        fun h' => absurd h' (by rw [hd1]; exact hζne)⟩
  · intro h
    rcases hq with hq1 | hq1 <;> rcases hd with hd1 | hd1
    · rw [hq1, hd1, one_mul]
    · exact absurd (h.1 hq1) (by rw [hd1]; exact hζne)
    · exact absurd (h.2 hd1) (by rw [hq1]; exact hζne)
    · rw [hq1, hd1, hζsq1]

theorem q8d8Counts : Q8D8Counts := by
  intro G _ _ N h
  obtain ⟨hNcard, ζ, hζN, hζne, _hζcen, hζsq⟩ := h.facts
  obtain ⟨Q, D, ⟨eQ⟩, ⟨eD⟩, hcomm, hsup, _hcard⟩ := h
  have hζsq1 : ζ * ζ = 1 := by
    rcases hζsq ζ hζN with h | h
    · exact h
    · exact absurd (mul_left_cancel (h.trans (mul_one ζ).symm)) hζne
  let φ : ↥Q × ↥D →* ↥N := q8d8MulHom hcomm hsup
  have hsurj : Function.Surjective φ := q8d8MulHom_surjective hcomm hsup
  have hker : Nat.card φ.ker = 2 := q8d8MulHom_ker_card hcomm hsup eQ eD hNcard
  have hfib : ∀ y : ↥N, y * y = 1 → Nat.card {x : ↥Q × ↥D // φ x = y} = 2 := by
    intro y _
    obtain ⟨a, ha⟩ := hsurj y
    rw [show y = φ a from ha.symm]
    exact (Nat.card_congr (q8d8FiberEquivKer hcomm hsup a)).trans hker
  have hS : Nat.card {x : ↥Q × ↥D // (φ x) * (φ x) = 1} =
      2 * Nat.card {n : ↥N // n * n = 1} :=
    subtype_preimage_card φ (fun n : ↥N => n * n = 1) 2 hfib
  have hcount : Nat.card {p : QuaternionGroup 2 × DihedralGroup 4 //
      (p.1 * p.1 = 1) ↔ (p.2 * p.2 = 1)} = 24 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have h24 : Nat.card {x : ↥Q × ↥D // (φ x) * (φ x) = 1} = 24 := by
    rw [← hcount]
    refine Nat.card_congr (Equiv.subtypeEquiv (eQ.toEquiv.prodCongr eD.toEquiv) ?_)
    intro p
    have hφ : (φ p) * (φ p) = 1 ↔
        ((p.1 : G) * p.2) * ((p.1 : G) * p.2) = 1 := by
      rw [Subtype.ext_iff]
      rfl
    rw [hφ, q8d8_mul_sq_eq_one_iff hcomm hsup hζsq hζne hζsq1 p.1 p.2]
    change ((p.1 : G) * p.1 = 1 ↔ (p.2 : G) * p.2 = 1) ↔
      (eQ p.1 * eQ p.1 = 1 ↔ eD p.2 * eD p.2 = 1)
    rw [coe_mul_self_eq_one_iff eQ p.1, coe_mul_self_eq_one_iff eD p.2]
  have h2 : 2 * Nat.card {n : ↥N // n * n = 1} = 24 := by rw [← hS, h24]
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
