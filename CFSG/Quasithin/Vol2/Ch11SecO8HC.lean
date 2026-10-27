module

public import CFSG.Quasithin.Vol2.Ch11SecO8HB
public import CFSG.Quasithin.Vol2.Ch11SecSCartanL2
public import CFSG.Quasithin.Vol2.Ch11SecSCartanT5

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

namespace O8H

variable {G : Type} [Group G]

theorem card_sup_dvd [Finite G] {A B : Subgroup G} (h : A ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card ↥(A ⊔ B) ∣ Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_mul_card B (A ⊔ B)
  rw [inf_eq_left.mpr le_sup_right, relIndex_sup_eq h] at h1
  rw [← h1]
  exact Nat.mul_dvd_mul_right (Subgroup.relIndex_dvd_card B A) _

variable [Finite G] {T L I V₁ V₂ X : Subgroup G} {n : ℕ}

theorem card_cartan_dvd (hC : SecS.CartanFacts) (hN : SecA.NatFacts) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂)
    (hX : IsCartanX T L X) : Nat.card X ∣ (2 ^ n - 1) ^ 2 := by
  have d := SecS.transportData hN h1102 h hV₁ hV₂ hX
  have hab := (SecA.isElemAbelian_fsuV h).1
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (SecA.isElemAbelian_fsuV h).2 w w.2)
  have hP := SecA.isSylowTwoOf_P h
  have hU₁ := SecA.isFlagW_of_isVi h hV₁
  have hU₂ := SecA.isFlagW_of_isVi h hV₂
  have hD := SecS.isHall_autOn_cartan h1102 h hX
  have hn : 2 ≤ n := h.one_lt
  have hconc : SecS.CartanConcl (autOn L (fsuV T I)) (V₁.subgroupOf (fsuV T I))
      (V₂.subgroupOf (fsuV T I)) (autOn X (fsuV T I)) (2 ^ n) := by
    obtain ⟨_, -, -, -, hk⟩ := h1102 G T L I n h
    rcases hk with ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨K, _, _, hK, -, π, hπ, -⟩ |
        ⟨K, _, _, hK, -, hnat⟩
    · exact hC.sl3 K n hn hK _ hsq _ _ π hπ _ hP _ _ hU₁ hU₂ _ hD
    · exact (hC.sp4 K n hn hK _ hsq _ _ π hπ _ hP _ _ hU₁ hU₂ _ hD).1
    · obtain ⟨K', _, _, hK', π, hπ⟩ := hnat
      exact (hC.g2 K' n hn hK' _ hsq _ _ π hπ _ hP _ _ hU₁ hU₂ _ hD).1
  obtain ⟨ha, -, -, h1, h2, -, -⟩ := hconc
  have hx1 : SecA.xOne X (LOf L V₁) ≤ X := inf_le_left
  have hle : X ≤ SecA.xOne X (LOf L V₁) ⊔ (X ⊓ LOf L V₁) :=
    d.le_sup hx1 inf_le_left (by rw [d.f₁, d.e₁]; exact ha)
  have hcard₁ : Nat.card ↥(X ⊓ LOf L V₁) = 2 ^ n - 1 := by
    rw [← d.card inf_le_left, d.e₁, h1]
  have hcardX₁ : Nat.card ↥(SecA.xOne X (LOf L V₁)) = 2 ^ n - 1 := by
    rw [← d.card hx1, d.f₁, h2]
  have hXN : X ≤ Subgroup.normalizer (LOf L V₁ : Set G) :=
    SecS.cartan_le_normalizer_lOf hN h1102 h (Or.inl rfl) hV₁ hX
  have hnorm : SecA.xOne X (LOf L V₁) ≤ Subgroup.normalizer ((X ⊓ LOf L V₁ : Subgroup G) : Set G) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (hx1 hx), hXN (hx1 hx)⟩
  have heq : X = SecA.xOne X (LOf L V₁) ⊔ (X ⊓ LOf L V₁) :=
    le_antisymm hle (sup_le hx1 inf_le_left)
  rw [heq, sq]
  have := card_sup_dvd hnorm
  rwa [hcardX₁, hcard₁] at this

theorem coprime_cartan (hC : SecS.CartanFacts) (hN : SecA.NatFacts) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂)
    (hX : IsCartanX T L X) {m : ℕ} (hm : Nat.Coprime m (2 ^ n - 1)) :
    Nat.Coprime (Nat.card X) m :=
  Nat.Coprime.coprime_dvd_left (card_cartan_dvd hC hN h1102 h hV₁ hV₂ hX)
    (Nat.Coprime.pow_left 2 hm.symm)

end O8H

end CFSG.Quasithin.Vol2.Ch11.SecD
