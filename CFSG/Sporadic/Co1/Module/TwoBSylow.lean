module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Sporadic.Co1.Module.TwoB

variable {G : Type*} [Group G]

theorem index_inf_odd [Finite G] {C H S : Subgroup G} (hHC : H ≤ C)
    (hidx : Nat.card C ≤ 2 * Nat.card H) (hSC : S ≤ C) {k m : ℕ} (hm : Odd m)
    (hC : Nat.card C = 2 ^ k * m) (hS : Nat.card S = 2 ^ k) :
    ¬ 2 ∣ ((H ⊓ S).subgroupOf H).index := by
  have hHpos : 0 < Nat.card H := Nat.card_pos
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hHC
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h] at hc
      omega
    · exact h
  have hc2 : c ≤ 2 := by
    by_contra h
    have : Nat.card H * 3 ≤ Nat.card H * c := Nat.mul_le_mul_left _ (by omega)
    omega
  have hQH : H ⊓ S ≤ H := inf_le_left
  have hQcard : Nat.card ((H ⊓ S).subgroupOf H) = Nat.card (H ⊓ S : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
  have hidxeq : Nat.card (H ⊓ S : Subgroup G) * ((H ⊓ S).subgroupOf H).index = Nat.card H := by
    rw [← hQcard]
    exact Subgroup.card_mul_index _
  have hrel : H.relIndex S * Nat.card (H ⊓ S : Subgroup G) = Nat.card S :=
    Subgroup.relIndex_mul_card H S
  have hrelC : H.relIndex C * Nat.card (H ⊓ C : Subgroup G) = Nat.card C :=
    Subgroup.relIndex_mul_card H C
  rw [inf_eq_left.2 hHC] at hrelC
  have hrelC' : H.relIndex C = c := by
    have : H.relIndex C * Nat.card H = c * Nat.card H := by rw [hrelC, hc, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right hHpos this
  have hrle : H.relIndex S ≤ c := by
    have := Subgroup.relIndex_le_of_le_right (H := H) hSC (by rw [hrelC']; omega)
    rwa [hrelC'] at this
  have hQpos : 0 < Nat.card (H ⊓ S : Subgroup G) := Nat.card_pos
  have hSpos : 0 < Nat.card S := Nat.card_pos
  have hrpos : 0 < H.relIndex S := by
    rcases Nat.eq_zero_or_pos (H.relIndex S) with h | h
    · rw [h] at hrel
      omega
    · exact h
  have key : c * ((H ⊓ S).subgroupOf H).index = H.relIndex S * m := by
    have h1 : Nat.card (H ⊓ S : Subgroup G) * (c * ((H ⊓ S).subgroupOf H).index) =
        Nat.card (H ⊓ S : Subgroup G) * (H.relIndex S * m) := by
      calc Nat.card (H ⊓ S : Subgroup G) * (c * ((H ⊓ S).subgroupOf H).index)
          = c * (Nat.card (H ⊓ S : Subgroup G) * ((H ⊓ S).subgroupOf H).index) := by ring
        _ = c * Nat.card H := by rw [hidxeq]
        _ = Nat.card C := by rw [hc, mul_comm]
        _ = 2 ^ k * m := hC
        _ = Nat.card S * m := by rw [hS]
        _ = (H.relIndex S * Nat.card (H ⊓ S : Subgroup G)) * m := by rw [hrel]
        _ = Nat.card (H ⊓ S : Subgroup G) * (H.relIndex S * m) := by ring
    exact Nat.eq_of_mul_eq_mul_left hQpos h1
  obtain ⟨m', hm'⟩ := hm
  intro h2
  obtain ⟨i, hi⟩ := h2
  rw [hi] at key
  have : c = 1 ∨ c = 2 := by omega
  rcases this with rfl | rfl
  · have hr : H.relIndex S = 1 := by omega
    rw [hr] at key
    omega
  · rcases (show H.relIndex S = 1 ∨ H.relIndex S = 2 by omega) with hr | hr
    · rw [hr] at key
      omega
    · rw [hr] at key
      omega

theorem le_of_normal_two_subgroup [Finite G] {C H N S : Subgroup G} (hHC : H ≤ C)
    (hidx : Nat.card C ≤ 2 * Nat.card H) (hSC : S ≤ C) {k m : ℕ} (hm : Odd m)
    (hC : Nat.card C = 2 ^ k * m) (hS : Nat.card S = 2 ^ k) (hNH : N ≤ H)
    (hNnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hNp : IsPGroup 2 N) : N ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSp : IsPGroup 2 S := IsPGroup.of_card hS
  have hQp : IsPGroup 2 ((H ⊓ S).subgroupOf H) := (hSp.to_inf_right (H := H)).comap_subtype
  let P : Sylow 2 H := hQp.toSylow (index_inf_odd hHC hidx hSC hm hC hS)
  have hNn : (N.subgroupOf H).Normal :=
    ⟨fun n hn h => by
      have h1 : (h : G) * (n : G) * (h : G)⁻¹ ∈ N := hNnorm h h.2 n hn
      exact h1⟩
  have hNp' : IsPGroup 2 (N.subgroupOf H) := hNp.comap_subtype
  intro n hn
  have h1 : (⟨n, hNH hn⟩ : H) ∈ N.subgroupOf H := hn
  have h2 : (⟨n, hNH hn⟩ : H) ∈ P := hNp'.le_sylow_of_normal P h1
  exact (Subgroup.mem_inf.1 h2).2

theorem card_le_of_normal_two_subgroup [Finite G] {C H N S T : Subgroup G} (hHC : H ≤ C)
    (hidx : Nat.card C ≤ 2 * Nat.card H) (hSC : S ≤ C) (hTC : T ≤ C) {k m : ℕ} (hm : Odd m)
    (hC : Nat.card C = 2 ^ k * m) (hS : Nat.card S = 2 ^ k) (hT : Nat.card T = 2 ^ k)
    (hNH : N ≤ H) (hNnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hNp : IsPGroup 2 N) :
    Nat.card N ≤ Nat.card ↥(S ⊓ T) :=
  Subgroup.card_le_of_le (le_inf (le_of_normal_two_subgroup hHC hidx hSC hm hC hS hNH hNnorm hNp)
    (le_of_normal_two_subgroup hHC hidx hTC hm hC hT hNH hNnorm hNp))

theorem map_conj_le_centralizer {s : G} {S : Subgroup G}
    (hS : S ≤ Subgroup.centralizer ({s} : Set G)) (x : G) :
    S.map (MulAut.conj x).toMonoidHom ≤ Subgroup.centralizer ({x * s * x⁻¹} : Set G) := by
  rintro _ ⟨y, hy, rfl⟩
  have hy' := Subgroup.mem_centralizer_singleton_iff.1 (hS hy)
  rw [Subgroup.mem_centralizer_singleton_iff]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc x * y * x⁻¹ * (x * s * x⁻¹) = x * (y * s) * x⁻¹ := by group
    _ = x * (s * y) * x⁻¹ := by rw [hy']
    _ = x * s * x⁻¹ * (x * y * x⁻¹) := by group

theorem card_map_conj (S : Subgroup G) (x : G) :
    Nat.card ↥(S.map (MulAut.conj x).toMonoidHom) = Nat.card ↥S :=
  Subgroup.card_map_of_injective (MulAut.conj x).injective

theorem map_conj_inf (S T : Subgroup G) (x : G) :
    (S ⊓ T).map (MulAut.conj x).toMonoidHom =
      S.map (MulAut.conj x).toMonoidHom ⊓ T.map (MulAut.conj x).toMonoidHom :=
  Subgroup.map_inf_eq _ _ _ (MulAut.conj x).injective

theorem conj_mem_of_mem {K : Subgroup G} {g y : G} (hg : g ∈ K) (hy : y ∈ K) :
    (MulAut.conj g).toMonoidHom y ∈ K := by
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact K.mul_mem (K.mul_mem hg hy) (K.inv_mem hg)

end CFSG.Sporadic.Co1.Module.TwoB
