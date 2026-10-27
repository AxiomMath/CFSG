module

public import CFSG.RankThree.PartOne.KF.SU5Final

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly

theorem three_lt_evenRank_of_frame {H : Type} [Group H] [Finite H] {L : Subgroup H} {Γ : Type}
    [Group Γ] (ψ : Γ ≃* L) {A : Subgroup Γ} (hA : IsElementaryAbelian 5 A)
    (hAcard : Nat.card A = 5 ^ 3) {r : Γ} (hr : orderOf r = 2) (hrA : ∀ a ∈ A, a * r = r * a)
    {y : H} (hy5 : y ^ 5 = 1) (hyL : y ∉ L)
    (hyA : ∀ a ∈ A, y * ((ψ a : L) : H) = ((ψ a : L) : H) * y)
    (hyr : y * ((ψ r : L) : H) = ((ψ r : L) : H) * y) : 3 < evenRank H := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set φ : Γ →* H := L.subtype.comp ψ.toMonoidHom with hφ
  have hφinj : Function.Injective φ := L.subtype_injective.comp ψ.injective
  set AL : Subgroup H := A.map φ with hAL
  set K : Subgroup H := Subgroup.zpowers (φ r) with hK
  have hALel : IsElementaryAbelian 5 AL := IsElementaryAbelian.map φ
  have hALcard : Nat.card AL = 5 ^ 3 := by
    rw [hAL, Subgroup.card_map_of_injective hφinj]
    exact hAcard
  have hALL : AL ≤ L := by
    rintro _ ⟨a, -, rfl⟩
    exact (ψ a).2
  have hφr : φ r ∈ L := (ψ r).2
  have hKL : K ≤ L := (Subgroup.zpowers_le).mpr hφr
  have hord : orderOf (φ r) = 2 := by
    rw [orderOf_injective φ hφinj r]
    exact hr
  have hKcard : Nat.card K = 2 := by
    rw [hK, Nat.card_zpowers, hord]
  have hKA : K ⊓ AL = ⊥ := by
    have h1 : Nat.card ↥(K ⊓ AL) ∣ 2 := hKcard ▸ Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(K ⊓ AL) ∣ 5 ^ 3 := hALcard ▸ Subgroup.card_dvd_of_le inf_le_right
    have h3 : Nat.card ↥(K ⊓ AL) = 1 := by
      have := Nat.dvd_gcd h1 h2
      have h4 : Nat.gcd 2 (5 ^ 3) = 1 := by norm_num
      rw [h4] at this
      exact Nat.dvd_one.mp this
    exact Subgroup.card_eq_one.mp h3
  have hKc : K ≤ Subgroup.centralizer (AL : Set H) := by
    rw [hK, Subgroup.zpowers_le]
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have := congrArg φ (hrA a ha)
    rw [map_mul, map_mul] at this
    exact this
  have hec : y ∈ Subgroup.centralizer (AL : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    exact (hyA a ha).symm
  have heK : y ∈ Subgroup.normalizer (K : Set H) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [hK, Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact ((Commute.zpow_right (show Commute y (φ r) from hyr) k)).symm.eq
  have hK2 : 2 ∣ Nat.card K := hKcard ▸ dvd_rfl
  exact KFSU5.three_lt_evenRank_of_outer_element hALel hALcard hALL hKL hKA hKc hec heK hy5 hyL
    hK2

end CFSG.RankThree.PartOne
