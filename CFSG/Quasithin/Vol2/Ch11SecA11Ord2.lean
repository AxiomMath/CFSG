module

public import CFSG.Quasithin.Background.A3Structure312Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Blueprint

theorem eleven_dvd_card_M22 : 11 ∣ Nat.card ↥NativeSporadic.M22 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨g, hg, hg11, hg1⟩ : ∃ g ∈ NativeSporadic.M22, g ^ 11 = 1 ∧ g ≠ 1 := by
    refine ⟨_, Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))), ?_, ?_⟩
    · decide +kernel
    · decide +kernel
  have ho : orderOf (⟨g, hg⟩ : ↥NativeSporadic.M22) = 11 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hg11 hg1
  rw [← ho]
  exact orderOf_dvd_natCard _

theorem card_M22_dvd : Nat.card ↥NativeSporadic.M22 ∣ Nat.factorial 22 := by
  have := Subgroup.card_subgroup_dvd_card NativeSporadic.M22
  rwa [Nat.card_perm, Nat.card_fin] at this

theorem twentythree_dvd_card_M24 : 23 ∣ Nat.card ↥NativeSporadic.M24 := by
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  obtain ⟨g, hg, hg23, hg1⟩ : ∃ g ∈ NativeSporadic.M24, g ^ 23 = 1 ∧ g ≠ 1 := by
    refine ⟨_, Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))), ?_, ?_⟩
    · decide +kernel
    · decide +kernel
  have ho : orderOf (⟨g, hg⟩ : ↥NativeSporadic.M24) = 23 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hg23 hg1
  rw [← ho]
  exact orderOf_dvd_natCard _

theorem card_M24_dvd : Nat.card ↥NativeSporadic.M24 ∣ Nat.factorial 24 := by
  have := Subgroup.card_subgroup_dvd_card NativeSporadic.M24
  rwa [Nat.card_perm, Nat.card_fin] at this

variable {X : Type} [Group X]

theorem card_of_isExt [Finite X] {PV PY : ∀ (V : Type) [Group V], Prop} (h : IsExt X PV PY)
    (hPV : ∀ (V : Type) [Group V] [Finite V], PV V → ∃ k, Nat.card V = 2 ^ k) :
    ∃ (V : Subgroup X) (_ : V.Normal), PY (X ⧸ V) ∧ ∃ k, Nat.card X = 2 ^ k * Nat.card (X ⧸ V) := by
  obtain ⟨V, hV, hPV', hPY⟩ := h
  obtain ⟨k, hk⟩ := hPV _ hPV'
  refine ⟨V, hV, hPY, k, ?_⟩
  rw [V.card_eq_card_quotient_mul_card_subgroup, hk, mul_comm]

theorem card_isE2 {k : ℕ} (h : IsE2 k X) : Nat.card X = 2 ^ k := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Fin k → ZMod 2) = 2 ^ k
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem card_isExtraspecial2 {m : ℕ} (h : IsExtraspecial2 m X) : Nat.card X = 2 ^ (1 + 2 * m) :=
  h.2

theorem card_isZ4Cubed (h : IsZ4Cubed X) : Nat.card X = 2 ^ 6 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Fin 3 → ZMod 4) = 2 ^ 6
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

theorem card_isZ4StarExtra2 [Finite X] (h : IsZ4StarExtra2 X) : ∃ k, Nat.card X = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Z, E, hZ, -, hE, hZc, hZE, -⟩ := h
  have hZn : Z.Normal := ⟨fun z hz g => by
    rw [Subgroup.mem_center_iff.mp (hZc hz) g, mul_inv_cancel_right]
    exact hz⟩
  have hp : IsPGroup 2 ↥(Z ⊔ E) :=
    IsPGroup.to_sup_of_normal_left (IsPGroup.of_card (n := 2) (by rw [hZ]; norm_num))
      (IsPGroup.of_card hE.2)
  rw [hZE] at hp
  exact IsPGroup.iff_card.mp (hp.of_equiv Subgroup.topEquiv)

end CFSG.Quasithin.Vol2.Ch11.SecA
