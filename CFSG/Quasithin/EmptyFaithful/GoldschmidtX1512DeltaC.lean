module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512DeltaB

public section

namespace CFSG.Quasithin.X1512

namespace Delta

private def a5 : Equiv.Perm (Fin 5) := Equiv.swap 0 1
private def b5 : Equiv.Perm (Fin 5) := Equiv.swap 2 3
private def c5 : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 1 3

private def D8list : List (Equiv.Perm (Fin 5)) :=
  [1, a5, b5, a5 * b5, c5, a5 * c5, b5 * c5, a5 * b5 * c5]

private def E5 : List (Equiv.Perm (Fin 5)) := [a5, b5, a5 * b5, c5, a5 * b5 * c5]

private theorem D8_mul : ∀ a ∈ D8list, ∀ b ∈ D8list, a * b ∈ D8list := by decide +kernel

private theorem D8_inv : ∀ a ∈ D8list, a⁻¹ ∈ D8list := by decide +kernel

private def D8std : Subgroup (Equiv.Perm (Fin 5)) where
  carrier := {σ | σ ∈ D8list}
  one_mem' := by decide +kernel
  mul_mem' := fun {a b} ha hb => D8_mul a ha b hb
  inv_mem' := fun {a} ha => D8_inv a ha

private theorem card_D8std : Nat.card D8std = 8 := by
  show Nat.card {σ : Equiv.Perm (Fin 5) // σ ∈ D8list} = 8
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem E5_spec : ∀ x ∈ D8list, x * x = 1 → x = 1 ∨ x ∈ E5 := by decide +kernel

private def D3list : List (Equiv.Perm (Fin 3)) := [1, Equiv.swap 0 1]

private def E3 : List (Equiv.Perm (Fin 3)) := [Equiv.swap 0 1]

private theorem D3_mul : ∀ a ∈ D3list, ∀ b ∈ D3list, a * b ∈ D3list := by decide +kernel

private theorem D3_inv : ∀ a ∈ D3list, a⁻¹ ∈ D3list := by decide +kernel

private def D3std : Subgroup (Equiv.Perm (Fin 3)) where
  carrier := {σ | σ ∈ D3list}
  one_mem' := by decide +kernel
  mul_mem' := fun {a b} ha hb => D3_mul a ha b hb
  inv_mem' := fun {a} ha => D3_inv a ha

private theorem card_D3std : Nat.card D3std = 2 := by
  show Nat.card {σ : Equiv.Perm (Fin 3) // σ ∈ D3list} = 2
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem E3_spec : ∀ x ∈ D3list, x * x = 1 → x = 1 ∨ x ∈ E3 := by decide +kernel

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
private theorem cert_three : ∀ l ∈ subs E3, (∀ a ∈ l, ∀ b ∈ l, a * b = b * a) →
    (∀ a ∈ l, ∀ b ∈ l, a * b = 1 ∨ a * b ∈ l) →
    (1 :: l).toFinset.card * fixCount 3 (1 :: l).toFinset ≤ 2 ^ (3 - 1) ∧
    ((1 :: l).toFinset.card * fixCount 3 (1 :: l).toFinset = 2 ^ (3 - 1) → l ≠ [] →
      ∃ ξ ∈ [Equiv.swap 0 1 * Equiv.swap 1 2], ξ ^ 3 = 1 ∧ ξ ≠ 1 ∧
        (∀ g ∈ 1 :: l, g * ξ * g⁻¹ = ξ ∨ g * ξ * g⁻¹ = ξ⁻¹) ∧
        (∃ g ∈ 1 :: l, g * ξ * g⁻¹ = ξ⁻¹) ∧ True) := by
  decide +kernel

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
private theorem cert_five : ∀ l ∈ subs E5, (∀ a ∈ l, ∀ b ∈ l, a * b = b * a) →
    (∀ a ∈ l, ∀ b ∈ l, a * b = 1 ∨ a * b ∈ l) →
    (1 :: l).toFinset.card * fixCount 5 (1 :: l).toFinset ≤ 2 ^ (5 - 1) ∧
    ((1 :: l).toFinset.card * fixCount 5 (1 :: l).toFinset = 2 ^ (5 - 1) → l ≠ [] →
      ∃ ξ ∈ [Equiv.swap 0 1 * Equiv.swap 1 4, Equiv.swap 2 3 * Equiv.swap 3 4],
        ξ ^ 3 = 1 ∧ ξ ≠ 1 ∧ (∀ g ∈ 1 :: l, g * ξ * g⁻¹ = ξ ∨ g * ξ * g⁻¹ = ξ⁻¹) ∧
        (∃ g ∈ 1 :: l, g * ξ * g⁻¹ = ξ⁻¹) ∧
        ∃ t ∈ D8list, (ξ * t) ^ 5 = 1 ∧ ξ * t ≠ 1) := by
  decide +kernel

private theorem eq_top_of_dvd {G : Type*} [Group G] [Finite G] (K : Subgroup G) {m : ℕ}
    (hm : Nat.card G = m) (h : m ∣ Nat.card K) : K = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  have h1 := Subgroup.card_subgroup_dvd_card K
  rw [hm] at h1 ⊢
  exact Nat.dvd_antisymm h1 h

private theorem closure_five {ξ t : Equiv.Perm (Fin 5)} (h3 : ξ ^ 3 = 1) (h1 : ξ ≠ 1)
    (ht : t ∈ D8std) (h5 : (ξ * t) ^ 5 = 1) (h5' : ξ * t ≠ 1) :
    Subgroup.closure ({ξ} ∪ (D8std : Set (Equiv.Perm (Fin 5)))) = ⊤ := by
  set K := Subgroup.closure ({ξ} ∪ (D8std : Set (Equiv.Perm (Fin 5)))) with hK
  have hξ : ξ ∈ K := Subgroup.subset_closure (Or.inl rfl)
  have hD : D8std ≤ K := fun x hx => Subgroup.subset_closure (Or.inr hx)
  have d8 : 8 ∣ Nat.card K := card_D8std ▸ Subgroup.card_dvd_of_le hD
  have d3 : 3 ∣ Nat.card K := by
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    simpa [orderOf_eq_prime h3 h1] using Subgroup.orderOf_dvd_natCard K hξ
  have d5 : 5 ∣ Nat.card K := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    simpa [orderOf_eq_prime h5 h5'] using Subgroup.orderOf_dvd_natCard K (K.mul_mem hξ (hD ht))
  refine eq_top_of_dvd K (m := 120) ?_ (by omega)
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

private theorem closure_three {ξ : Equiv.Perm (Fin 3)} (h3 : ξ ^ 3 = 1) (h1 : ξ ≠ 1) :
    Subgroup.closure ({ξ} ∪ (D3std : Set (Equiv.Perm (Fin 3)))) = ⊤ := by
  set K := Subgroup.closure ({ξ} ∪ (D3std : Set (Equiv.Perm (Fin 3)))) with hK
  have hξ : ξ ∈ K := Subgroup.subset_closure (Or.inl rfl)
  have hD : D3std ≤ K := fun x hx => Subgroup.subset_closure (Or.inr hx)
  have d2 : 2 ∣ Nat.card K := card_D3std ▸ Subgroup.card_dvd_of_le hD
  have d3 : 3 ∣ Nat.card K := by
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    simpa [orderOf_eq_prime h3 h1] using Subgroup.orderOf_dvd_natCard K hξ
  refine eq_top_of_dvd K (m := 6) ?_ (by omega)
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

private theorem fin_five_std {B : Subgroup (Equiv.Perm (Fin 5))} (hBD : B ≤ D8std)
    (hBe : CFSG.Open.IsElemAbelian 2 B) : FinConcl 5 D8std B := by
  obtain ⟨hle, heq⟩ := fin_of_cert (E := E5)
    (Gen := fun ξ => ∃ t ∈ D8list, (ξ * t) ^ 5 = 1 ∧ ξ * t ≠ 1) (fun x hx => E5_spec x hx)
    cert_five hBD hBe
  refine ⟨hle, fun h hB => ?_⟩
  obtain ⟨ξ, h3, h1, hc, hi, t, ht, h5, h5'⟩ := heq h hB
  exact ⟨ξ, h3, h1, hc, hi, closure_five h3 h1 ht h5 h5'⟩

private theorem fin_three_std {B : Subgroup (Equiv.Perm (Fin 3))} (hBD : B ≤ D3std)
    (hBe : CFSG.Open.IsElemAbelian 2 B) : FinConcl 3 D3std B := by
  obtain ⟨hle, heq⟩ := fin_of_cert (E := E3) (Gen := fun _ => True) (fun x hx => E3_spec x hx)
    cert_three hBD hBe
  refine ⟨hle, fun h hB => ?_⟩
  obtain ⟨ξ, h3, h1, hc, hi, -⟩ := heq h hB
  exact ⟨ξ, h3, h1, hc, hi, closure_three h3 h1⟩

private theorem exists_conj_std {G : Type*} [Group G] [Finite G] {D0 D : Subgroup G} {k m : ℕ}
    (hG : Nat.card G = 2 ^ k * m) (hm : ¬ 2 ∣ m)
    (h0 : Nat.card D0 = 2 ^ k) (hD : Nat.card D = 2 ^ k) :
    ∃ g : G, D = D0.map (MulAut.conj g).toMonoidHom := by
  have idx : ∀ {E : Subgroup G}, Nat.card E = 2 ^ k → ¬ 2 ∣ E.index := by
    intro E hE
    have h1 := Subgroup.card_mul_index E
    rw [hE, hG] at h1
    rw [Nat.eq_of_mul_eq_mul_left (by positivity) h1]
    exact hm
  let P : Sylow 2 G := (IsPGroup.of_card h0).toSylow (idx h0)
  let Q : Sylow 2 G := (IsPGroup.of_card hD).toSylow (idx hD)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  exact ⟨g, (congrArg (fun R : Sylow 2 G => (R : Subgroup G)) hg).symm⟩

end Delta

theorem fin_main {n : ℕ} (h : n = 3 ∨ n = 5) {D B : Subgroup (Equiv.Perm (Fin n))}
    (hD : Nat.card D = if n = 3 then 2 else 8) (hBD : B ≤ D)
    (hBe : CFSG.Open.IsElemAbelian 2 B) :
    Nat.card B * Nat.card (fixΔ n B) ≤ 2 ^ (n - 1) ∧
    (Nat.card B * Nat.card (fixΔ n B) = 2 ^ (n - 1) → B ≠ ⊥ →
      ∃ ξ : Equiv.Perm (Fin n), ξ ^ 3 = 1 ∧ ξ ≠ 1 ∧
        (∀ g ∈ B, g * ξ * g⁻¹ = ξ ∨ g * ξ * g⁻¹ = ξ⁻¹) ∧ (∃ g ∈ B, g * ξ * g⁻¹ = ξ⁻¹) ∧
        Subgroup.closure ({ξ} ∪ (D : Set (Equiv.Perm (Fin n)))) = ⊤) := by
  rcases h with rfl | rfl
  · obtain ⟨g, hg⟩ := Delta.exists_conj_std (k := 1) (m := 3) (D0 := Delta.D3std) (D := D)
      (by rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl) (by norm_num)
      (by rw [Delta.card_D3std]; rfl) (by simpa using hD)
    exact Delta.finConcl_of_conj (fun hB he => Delta.fin_three_std hB he) g hg hBD hBe
  · obtain ⟨g, hg⟩ := Delta.exists_conj_std (k := 3) (m := 15) (D0 := Delta.D8std) (D := D)
      (by rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl) (by norm_num)
      (by rw [Delta.card_D8std]; rfl) (by simpa using hD)
    exact Delta.finConcl_of_conj (fun hB he => Delta.fin_five_std hB he) g hg hBD hBe

end CFSG.Quasithin.X1512
