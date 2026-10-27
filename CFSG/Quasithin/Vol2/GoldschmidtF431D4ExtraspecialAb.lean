module

public import CFSG.Quasithin.Vol2.GoldschmidtF431q2NFAux

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.Quasithin.H13.F431.G2Two

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_comm_subtype (X : Subgroup G) (c : G) :
    Nat.card {x : ↥X // c * (x : G) = x * c} =
      Nat.card (X ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨(x : G), x.1.2, mem_centralizer_singleton.2 x.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, mem_centralizer_singleton.1 y.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

omit [Finite G] in
theorem card_commuting_set (X S : Subgroup G) :
    Nat.card {x : ↥X // ∀ s ∈ S, (x : G) * s = s * x} =
      Nat.card (X ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨(x : G), x.1.2, Subgroup.mem_centralizer_iff.2
        fun s hs => (x.2 s hs).symm⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, fun s hs =>
        (Subgroup.mem_centralizer_iff.1 y.2.2 s hs).symm⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

theorem card_comm_dichotomy {X : Subgroup G} {c z : G}
    (h : ∀ x ∈ X, x * c * x⁻¹ * c⁻¹ = 1 ∨ x * c * x⁻¹ * c⁻¹ = z) :
    ((∀ x ∈ X, c * x = x * c) ∧ Nat.card {x : ↥X // c * (x : G) = x * c} = Nat.card X) ∨
      ((¬ ∀ x ∈ X, c * x = x * c) ∧ 2 * Nat.card {x : ↥X // c * (x : G) = x * c} = Nat.card X) := by
  classical
  have hle2 : Nat.card X ≤ 2 * Nat.card (X ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) := by
    refine card_le_two_mul_inf_centralizer (c := c) (w := z) fun x hx => ?_
    rcases h x hx with h1 | h1
    · left
      refine mem_centralizer_singleton.2 ?_
      have h2 : x * c * x⁻¹ = c := mul_inv_eq_one.1 h1
      calc c * x = (x * c * x⁻¹) * x := by rw [h2]
        _ = x * c := by group
    · right
      calc x * c * x⁻¹ = (x * c * x⁻¹ * c⁻¹) * c := by group
        _ = z * c := by rw [h1]
  rw [card_comm_subtype]
  obtain ⟨S, hSdef⟩ : ∃ S : Subgroup G, S = X ⊓ Subgroup.centralizer ({c} : Set G) := ⟨_, rfl⟩
  rw [← hSdef] at hle2 ⊢
  have hSX : S ≤ X := by rw [hSdef]; exact inf_le_left
  have hXS : ∀ x ∈ X, c * x = x * c → x ∈ S := fun x hx hc => by
    rw [hSdef]; exact ⟨hx, mem_centralizer_singleton.2 hc⟩
  have hSc : ∀ x ∈ S, c * x = x * c := fun x hx => by
    rw [hSdef] at hx; exact mem_centralizer_singleton.1 hx.2
  by_cases hall : ∀ x ∈ X, c * x = x * c
  · left
    refine ⟨hall, ?_⟩
    have : S = X := le_antisymm hSX fun x hx => hXS x hx (hall x hx)
    rw [this]
  · right
    refine ⟨hall, le_antisymm ?_ ?_⟩
    · obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hSX
      have hpos : 0 < Nat.card X := Nat.card_pos
      have hk1 : k ≠ 1 := by
        rintro rfl
        apply hall
        have hSX' : S = X := Subgroup.eq_of_le_of_card_ge hSX (by omega)
        intro x hx
        exact hSc x (by rw [hSX']; exact hx)
      have hk0 : k ≠ 0 := by
        rintro rfl
        omega
      have hk2 : 2 ≤ k := by omega
      calc 2 * Nat.card S ≤ k * Nat.card S := Nat.mul_le_mul_right _ hk2
        _ = Nat.card X := by rw [hk]; ring
    · exact hle2

omit [Finite G] in
theorem sum_two_mul {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P] (t : ι → ℕ)
    (M : ℕ) (h : ∀ i, 2 * t i = M * (if P i then 2 else 1)) :
    2 * ∑ i, t i = M * (Fintype.card ι + Fintype.card {i // P i}) := by
  rw [Finset.mul_sum]
  have h1 : ∑ i, 2 * t i = ∑ i, M * (1 + if P i then 1 else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h i]
    split_ifs <;> ring
  rw [h1, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one, ← Finset.card_filter, Fintype.card_subtype]

theorem card_pairs_left (Q A : Subgroup G) [Fintype ↥Q] :
    Nat.card {p : ↥Q × ↥A // (p.1 : G) * p.2 = p.2 * p.1} =
      ∑ x : ↥Q, Nat.card {a : ↥A // (x : G) * a = a * x} := by
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    (fun (x : ↥Q) (a : ↥A) => (x : G) * a = a * x)), Nat.card_sigma]

theorem card_pairs_right (Q A : Subgroup G) [Fintype ↥A] :
    Nat.card {p : ↥Q × ↥A // (p.1 : G) * p.2 = p.2 * p.1} =
      ∑ a : ↥A, Nat.card {x : ↥Q // (a : G) * x = x * a} := by
  have e1 : {p : ↥Q × ↥A // (p.1 : G) * p.2 = p.2 * p.1} ≃
      {p : ↥A × ↥Q // (p.1 : G) * p.2 = p.2 * p.1} :=
    (Equiv.prodComm ↥Q ↥A).subtypeEquiv fun p => eq_comm
  rw [Nat.card_congr e1, Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    (fun (a : ↥A) (x : ↥Q) => (a : G) * x = x * a)), Nat.card_sigma]

theorem two_mul_card_pairs_left {Q A : Subgroup G} {z : G}
    (hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z) (hAQ : A ≤ Q) :
    2 * Nat.card {p : ↥Q × ↥A // (p.1 : G) * p.2 = p.2 * p.1} =
      Nat.card A * (Nat.card Q + Nat.card (Q ⊓ Subgroup.centralizer (A : Set G) : Subgroup G)) := by
  classical
  have : Fintype ↥Q := Fintype.ofFinite _
  rw [card_pairs_left]
  have h := sum_two_mul (fun x : ↥Q => ∀ a ∈ A, (x : G) * a = a * x)
    (fun x : ↥Q => Nat.card {a : ↥A // (x : G) * a = a * x}) (Nat.card A) fun x => by
    rcases card_comm_dichotomy (X := A) (c := (x : G)) (z := z)
      (fun a ha => hQcomm a (hAQ ha) x x.2) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [eq_true h1, ↓reduceIte]
      rw [h2]
      ring
    · simp only [eq_false h1, ↓reduceIte]
      omega
  rw [h, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_commuting_set]

theorem two_mul_card_pairs_right {Q A : Subgroup G} {z : G}
    (hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z) (hAQ : A ≤ Q) :
    2 * Nat.card {p : ↥Q × ↥A // (p.1 : G) * p.2 = p.2 * p.1} =
      Nat.card Q * (Nat.card A + Nat.card (A ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G)) := by
  classical
  have : Fintype ↥A := Fintype.ofFinite _
  rw [card_pairs_right]
  have h := sum_two_mul (fun a : ↥A => ∀ x ∈ Q, (a : G) * x = x * a)
    (fun a : ↥A => Nat.card {x : ↥Q // (a : G) * x = x * a}) (Nat.card Q) fun a => by
    rcases card_comm_dichotomy (X := Q) (c := (a : G)) (z := z)
      (fun x hx => hQcomm x hx a (hAQ a.2)) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [eq_true h1, ↓reduceIte]
      rw [h2]
      ring
    · simp only [eq_false h1, ↓reduceIte]
      omega
  rw [h, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_commuting_set]

theorem card_sq_le_two_mul_of_abelian {z : G} {Q A : Subgroup G}
    (hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z)
    (hQZ : ∀ w ∈ Q, (∀ q ∈ Q, q * w = w * q) → w = 1 ∨ w = z) (hAQ : A ≤ Q)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : Nat.card A * Nat.card A ≤ 2 * Nat.card Q := by
  have h1 := two_mul_card_pairs_left hQcomm hAQ
  have h2 := two_mul_card_pairs_right hQcomm hAQ
  rw [h1] at h2
  have hAC : Nat.card A ≤ Nat.card (Q ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by
    refine Subgroup.card_le_of_le fun a ha =>
      ⟨hAQ ha, Subgroup.mem_centralizer_iff.2 fun b hb => ?_⟩
    exact hA b hb a ha
  have hZ : Nat.card (A ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) ≤ 2 :=
    card_le_two_of_forall (z := z) fun w hw =>
      hQZ w (hAQ hw.1) fun q hq => Subgroup.mem_centralizer_iff.1 hw.2 q hq
  have h3 : Nat.card A * Nat.card (Q ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) =
      Nat.card Q * Nat.card (A ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) := by
    nlinarith [h2]
  calc Nat.card A * Nat.card A
      ≤ Nat.card A * Nat.card (Q ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) :=
        Nat.mul_le_mul_left _ hAC
    _ = Nat.card Q * Nat.card (A ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) := h3
    _ ≤ Nat.card Q * 2 := Nat.mul_le_mul_left _ hZ
    _ = 2 * Nat.card Q := by ring

theorem card_abelian_le_32 {z : G} {Q A : Subgroup G} (hQcard : Nat.card Q = 512)
    (hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z)
    (hQZ : ∀ w ∈ Q, (∀ q ∈ Q, q * w = w * q) → w = 1 ∨ w = z) (hAQ : A ≤ Q)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : Nat.card A ≤ 32 := by
  have h := card_sq_le_two_mul_of_abelian hQcomm hQZ hAQ hA
  rw [hQcard] at h
  by_contra hgt
  push Not at hgt
  nlinarith

end CFSG.Quasithin.D4Hex
