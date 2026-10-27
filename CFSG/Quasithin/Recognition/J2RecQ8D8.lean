module

public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

namespace CFSG.Quasithin

open QuaternionGroup DihedralGroup

private theorem quaternion_central :
    ∀ q : QuaternionGroup 2, (∀ r : QuaternionGroup 2, q * r = r * q) →
      q = 1 ∨ q = QuaternionGroup.a 2 := by decide

private theorem dihedral_central :
    ∀ d : DihedralGroup 4, (∀ e : DihedralGroup 4, d * e = e * d) →
      d = 1 ∨ d = DihedralGroup.r 2 := by decide

private theorem quaternion_card : Nat.card (QuaternionGroup 2) = 8 := by
  rw [Nat.card_eq_fintype_card]; decide

private theorem dihedral_card : Nat.card (DihedralGroup 4) = 8 := by
  rw [Nat.card_eq_fintype_card]; decide

theorem IsQ8D8.exists_hom {P : Type*} [Group P] [Finite P] (h : IsQ8D8 P) :
    ∃ φ : QuaternionGroup 2 × DihedralGroup 4 →* P, Function.Surjective φ ∧
      φ (QuaternionGroup.a 2, 1) = φ (1, DihedralGroup.r 2) ∧ φ (QuaternionGroup.a 2, 1) ≠ 1 ∧
      ∀ c ∈ Subgroup.center P, c = 1 ∨ c = φ (QuaternionGroup.a 2, 1) := by
  obtain ⟨hcard, A, B, ⟨hAB, hgen⟩, ⟨eA⟩, ⟨eB⟩⟩ := h
  set fA : QuaternionGroup 2 →* P := A.subtype.comp eA.symm.toMonoidHom with hfA
  set fB : DihedralGroup 4 →* P := B.subtype.comp eB.symm.toMonoidHom with hfB
  have hfAinj : Function.Injective fA := fun x y hxy =>
    eA.symm.injective (Subtype.ext hxy)
  have hfBinj : Function.Injective fB := fun x y hxy =>
    eB.symm.injective (Subtype.ext hxy)
  have hcomm : ∀ (a : QuaternionGroup 2) (b : DihedralGroup 4), Commute (fA a) (fB b) := by
    intro a b
    exact (Subgroup.mem_centralizer_iff.mp (hAB (eA.symm a).2) _ (eB.symm b).2).symm
  set φ : QuaternionGroup 2 × DihedralGroup 4 →* P := fA.noncommCoprod fB hcomm with hφ
  have hφapp : ∀ a b, φ (a, b) = fA a * fB b := fun a b => by
    rw [hφ, MonoidHom.noncommCoprod_apply]
  have hfAmem : ∀ q, fA q ∈ A := fun q => (eA.symm q).2
  have hfBmem : ∀ q, fB q ∈ B := fun q => (eB.symm q).2
  have hfArange : ∀ x ∈ A, ∃ q, fA q = x := fun x hx => ⟨eA ⟨x, hx⟩, by simp [hfA]⟩
  have hfBrange : ∀ x ∈ B, ∃ q, fB q = x := fun x hx => ⟨eB ⟨x, hx⟩, by simp [hfB]⟩
  have hsurj : Function.Surjective φ := by
    intro p
    have hp : p ∈ A ⊔ B := by rw [hgen]; exact Subgroup.mem_top p
    have hAN : A ≤ Subgroup.normalizer (B : Set P) :=
      hAB.trans (Subgroup.centralizer_le_normalizer _)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A B hAN] at hp
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hp
    obtain ⟨a, rfl⟩ := hfArange x hx
    obtain ⟨b, rfl⟩ := hfBrange y hy
    exact ⟨(a, b), hφapp a b⟩
  have hnotinj : ¬ Function.Injective φ := by
    intro hinj
    have := Nat.card_le_card_of_injective φ hinj
    rw [Nat.card_prod, quaternion_card, dihedral_card, hcard] at this
    omega
  rw [injective_iff_map_eq_one] at hnotinj
  push Not at hnotinj
  obtain ⟨⟨a, b⟩, hab1, hab⟩ := hnotinj
  rw [hφapp] at hab1
  have hg : fA a = (fB b)⁻¹ := eq_inv_of_mul_eq_one_left hab1
  have hanot : a ≠ 1 := by
    rintro rfl
    rw [map_one, one_mul] at hab1
    exact hab (Prod.ext rfl (hfBinj (hab1.trans (map_one fB).symm)))
  have hbnot : b ≠ 1 := by
    rintro rfl
    rw [map_one, mul_one] at hab1
    exact hab (Prod.ext (hfAinj (hab1.trans (map_one fA).symm)) rfl)
  have haC : a = QuaternionGroup.a 2 := by
    refine (quaternion_central a fun r => ?_).resolve_left hanot
    apply hfAinj
    rw [map_mul, map_mul, hg]
    exact (hcomm r b).inv_right.symm.eq
  have hbC : b = DihedralGroup.r 2 := by
    refine (dihedral_central b fun e => ?_).resolve_left hbnot
    apply hfBinj
    have hb : fB b = (fA a)⁻¹ := by rw [hg, inv_inv]
    rw [map_mul, map_mul, hb]
    exact (hcomm a e).inv_left.eq
  have hsqB : fB (DihedralGroup.r 2) * fB (DihedralGroup.r 2) = 1 := by
    rw [← map_mul]
    have : DihedralGroup.r 2 * DihedralGroup.r 2 = (1 : DihedralGroup 4) := by decide
    rw [this, map_one]
  have hsqA : fA (QuaternionGroup.a 2) * fA (QuaternionGroup.a 2) = 1 := by
    rw [← map_mul]
    have : QuaternionGroup.a 2 * QuaternionGroup.a 2 = (1 : QuaternionGroup 2) := by decide
    rw [this, map_one]
  have hζ : fA (QuaternionGroup.a 2) = fB (DihedralGroup.r 2) := by
    have h1 : fA (QuaternionGroup.a 2) = (fB (DihedralGroup.r 2))⁻¹ := by
      have := hg
      rw [haC, hbC] at this
      exact this
    rw [h1]
    exact inv_eq_of_mul_eq_one_right hsqB
  have hζ1 : fA (QuaternionGroup.a 2) ≠ 1 := fun h1 =>
    (by decide : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1)
      (hfAinj (h1.trans (map_one fA).symm))
  refine ⟨φ, hsurj, ?_, ?_, ?_⟩
  · simp only [hφapp, map_one, mul_one, one_mul]
    exact hζ
  · simpa only [hφapp, map_one, mul_one] using hζ1
  · intro c hc
    obtain ⟨⟨a', b'⟩, rfl⟩ := hsurj c
    simp only [hφapp] at hc ⊢
    have hc' := Subgroup.mem_center_iff.mp hc
    have ha' : a' = 1 ∨ a' = QuaternionGroup.a 2 := by
      refine quaternion_central a' fun r => ?_
      apply hfAinj
      rw [map_mul, map_mul]
      have h1 := hc' (fA r)
      have hRY : fA r * fB b' = fB b' * fA r := (hcomm r b').eq
      have h3 : (fA r * fA a') * fB b' = (fA a' * fA r) * fB b' := by
        calc (fA r * fA a') * fB b' = fA r * (fA a' * fB b') := by rw [mul_assoc]
          _ = fA a' * fB b' * fA r := h1
          _ = fA a' * (fB b' * fA r) := by rw [mul_assoc]
          _ = fA a' * (fA r * fB b') := by rw [hRY]
          _ = (fA a' * fA r) * fB b' := by rw [mul_assoc]
      exact (mul_right_cancel h3).symm
    have hb' : b' = 1 ∨ b' = DihedralGroup.r 2 := by
      refine dihedral_central b' fun e => ?_
      apply hfBinj
      rw [map_mul, map_mul]
      have h1 := hc' (fB e)
      have hAE : fA a' * fB e = fB e * fA a' := (hcomm a' e).eq
      have h3 : fA a' * (fB e * fB b') = fA a' * (fB b' * fB e) := by
        calc fA a' * (fB e * fB b') = (fA a' * fB e) * fB b' := by rw [mul_assoc]
          _ = (fB e * fA a') * fB b' := by rw [hAE]
          _ = fB e * (fA a' * fB b') := by rw [mul_assoc]
          _ = fA a' * fB b' * fB e := h1
          _ = fA a' * (fB b' * fB e) := by rw [mul_assoc]
      exact (mul_left_cancel h3).symm
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · left
      simp only [map_one, mul_one]
    · right
      simp only [map_one, one_mul, mul_one]
      exact hζ.symm
    · right
      rfl
    · left
      rw [← hζ]
      exact hsqA

private def lines5 : Fin 5 → QuaternionGroup 2 × DihedralGroup 4 :=
  ![(QuaternionGroup.a 0, DihedralGroup.sr 0), (QuaternionGroup.a 0, DihedralGroup.sr 1),
    (QuaternionGroup.xa 0, DihedralGroup.r 1), (QuaternionGroup.a 1, DihedralGroup.r 1),
    (QuaternionGroup.xa 1, DihedralGroup.r 3)]

private theorem lines5_sq : ∀ i : Fin 5, lines5 i * lines5 i = 1 ∨
    lines5 i * lines5 i = (QuaternionGroup.a 2, DihedralGroup.r 2) := by decide

private theorem lines5_comm : ∀ i j : Fin 5, i ≠ j →
    (lines5 i * lines5 j) * (lines5 i * lines5 j) = (QuaternionGroup.a 2, 1) ∨
      (lines5 i * lines5 j) * (lines5 i * lines5 j) = (1, DihedralGroup.r 2) := by decide

private theorem lines5_prod : lines5 0 * lines5 1 * lines5 2 * lines5 3 * lines5 4 = 1 ∨
    lines5 0 * lines5 1 * lines5 2 * lines5 3 * lines5 4 =
      (QuaternionGroup.a 2, DihedralGroup.r 2) := by decide

theorem IsQ8D8.exists_fiveLines {P : Type*} [Group P] [Finite P] (h : IsQ8D8 P) {z : P}
    (hz : z ∈ Subgroup.center P) (hz1 : z ≠ 1) :
    ∃ x : Fin 5 → P, (∀ i, x i * x i = 1) ∧ (∀ i, x i * z = z * x i) ∧
      (∀ i j, i ≠ j → (x i * x j) ^ 2 = z) ∧ x 0 * x 1 * x 2 * x 3 * x 4 = 1 := by
  obtain ⟨φ, -, hφeq, -, hcenter⟩ := h.exists_hom
  have hzζ : z = φ (QuaternionGroup.a 2, 1) := (hcenter z hz).resolve_left hz1
  have hsq : φ (QuaternionGroup.a 2, 1) * φ (QuaternionGroup.a 2, 1) = 1 := by
    rw [← map_mul]
    have : ((QuaternionGroup.a 2, 1) : QuaternionGroup 2 × DihedralGroup 4) *
        (QuaternionGroup.a 2, 1) = 1 := by decide
    rw [this, map_one]
  have hε : φ (QuaternionGroup.a 2, DihedralGroup.r 2) = 1 := by
    have : ((QuaternionGroup.a 2, DihedralGroup.r 2) : QuaternionGroup 2 × DihedralGroup 4) =
        (QuaternionGroup.a 2, 1) * (1, DihedralGroup.r 2) := by simp
    rw [this, map_mul, ← hφeq]
    exact hsq
  refine ⟨fun i => φ (lines5 i), fun i => ?_, fun i => ?_, fun i j hij => ?_, ?_⟩
  · rw [← map_mul]
    rcases lines5_sq i with h1 | h1 <;> rw [h1]
    · exact map_one φ
    · exact hε
  · exact Subgroup.mem_center_iff.mp hz _
  · rw [pow_two, ← map_mul, ← map_mul, hzζ]
    rcases lines5_comm i j hij with h1 | h1 <;> rw [h1]
    exact hφeq.symm
  · rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
    rcases lines5_prod with h1 | h1 <;> rw [h1]
    · exact map_one φ
    · exact hε

end CFSG.Quasithin
