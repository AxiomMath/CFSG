module

public import CFSG.RankThree.GF2n.Tim79aCitedInvol
public import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

@[expose] def H (z : G) : Subgroup G := Subgroup.centralizer ({z} : Set G)

@[expose] def J (z : G) : Subgroup G := inSubgroup (pCore 2) (H z)

private theorem J_eq_inSubgroup (z : G) :
    J z = inSubgroup (pCore 2) (Subgroup.centralizer ({z} : Set G)) := rfl

theorem H_eq_centralizer : H z = Subgroup.centralizer ({z} : Set G) := rfl

theorem J_le_H : J z ≤ H z := Subgroup.map_subtype_le _

theorem z_mem_H : z ∈ H z := by
  rw [H_eq_centralizer]
  exact Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem z_mem_J (h : Tim79a.ParrottHyp z) : z ∈ J z := by
  obtain ⟨h1, h2, hcomm, h4, hquot⟩ := h
  have hz : z ∈ ⁅J z, J z⁆ := by
    rw [J_eq_inSubgroup, hcomm]
    exact Subgroup.mem_zpowers z
  exact Subgroup.commutator_le_self (J z) hz

theorem z_centralizes_H (h : Tim79a.ParrottHyp z) :
    z ∈ Subgroup.centralizer (H z : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  exact Subgroup.mem_centralizer_singleton_iff.mp (by simpa [H] using hg)

theorem z_centralizes_J (h : Tim79a.ParrottHyp z) :
    z ∈ Subgroup.centralizer (J z : Set G) :=
  Subgroup.centralizer_le (J_le_H (z := z)) (z_centralizes_H h)

theorem card_J (h : Tim79a.ParrottHyp z) : Nat.card (J z) = 2 ^ 10 := by
  obtain ⟨h1, ⟨T, F, hTcard, hF, hFcard, hdisj, hcomm, hsup⟩, hJcomm, h4, hquot⟩ := h
  have hTcomm : IsMulCommutative T := isMulCommutative_of_card_two T hTcard
  have hTT : ∀ a ∈ T, ∀ a' ∈ T, Commute a a' := by
    intro a ha a' ha'
    exact commute_of_mem_of_isMulCommutative hTcomm ha ha'
  have hcard := CFSG.card_sup_eq_mul_of_commute T F hcomm hdisj
  rw [hsup, hTcard, hFcard] at hcard
  rw [J_eq_inSubgroup, hcard]
  norm_num

theorem isPGroup_J (h : Tim79a.ParrottHyp z) : IsPGroup 2 (J z) :=
  IsPGroup.of_card (n := 10) (card_J h)

theorem card_centerIn_J (h : Tim79a.ParrottHyp z) : Nat.card (centerIn (J z)) = 4 := by
  obtain ⟨h1, ⟨T, F, hTcard, hF, hFcard, hdisj, hcomm, hsup⟩, hJcomm, h4, hquot⟩ := h
  have hTcomm : IsMulCommutative T := isMulCommutative_of_card_two T hTcard
  have hTT : ∀ a ∈ T, ∀ a' ∈ T, Commute a a' := by
    intro a ha a' ha'
    exact commute_of_mem_of_isMulCommutative hTcomm ha ha'
  have hcenter_eq :
      centerIn (J z) = T ⊔ (Subgroup.center F).map F.subtype := by
    rw [J_eq_inSubgroup, ← hsup]
    exact CFSG.centerIn_sup_eq_sup_center hTT hcomm hdisj
  have hcardC : Nat.card ((Subgroup.center F).map F.subtype) = 2 := by
    rw [← hF.2.1]
    exact hF.2.2
  have hC_le_F : (Subgroup.center F).map F.subtype ≤ F := Subgroup.map_subtype_le _
  have hTCdisj : T ⊓ (Subgroup.center F).map F.subtype = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [← hdisj]
    exact ⟨hx.1, hC_le_F hx.2⟩
  have hcommTC : ∀ t ∈ T, ∀ c ∈ (Subgroup.center F).map F.subtype, Commute t c :=
    fun t ht c hc => hcomm t ht c (hC_le_F hc)
  have hcard := CFSG.card_sup_eq_mul_of_commute T ((Subgroup.center F).map F.subtype) hcommTC hTCdisj
  rw [hcenter_eq, hcard, hTcard, hcardC]

theorem exists_z1 (h : Tim79a.ParrottHyp z) :
    ∃ z1 : G, centerIn (J z) = Subgroup.zpowers z ⊔ Subgroup.zpowers z1 ∧
      z1 ∉ Subgroup.zpowers z ∧ orderOf z1 = 2 := by
  obtain ⟨h1, ⟨T, F, hTcard, hF, hFcard, hdisj, hcomm, hsup⟩, hJcomm, h4, hquot⟩ := h
  have hTcomm : IsMulCommutative T := isMulCommutative_of_card_two T hTcard
  have hTT : ∀ a ∈ T, ∀ a' ∈ T, Commute a a' := by
    intro a ha a' ha'
    exact commute_of_mem_of_isMulCommutative hTcomm ha ha'
  let C : Subgroup G := (Subgroup.center F).map F.subtype
  have hcenter_eq : centerIn (J z) = T ⊔ C := by
    rw [J_eq_inSubgroup, ← hsup]
    exact CFSG.centerIn_sup_eq_sup_center hTT hcomm hdisj
  have hcardC : Nat.card C = 2 := by
    change Nat.card ((Subgroup.center F).map F.subtype) = 2
    rw [← hF.2.1]
    exact hF.2.2
  have hJ'leC : ⁅J z, J z⁆ ≤ C := by
    rw [J_eq_inSubgroup, ← hsup]
    change ⁅T ⊔ F, T ⊔ F⁆ ≤ (Subgroup.center F).map F.subtype
    rw [← hF.2.1]
    exact CFSG.commutator_sup_le_commutator_right hTT hcomm
  have hzC : z ∈ C := by
    have hz : z ∈ ⁅J z, J z⁆ := by
      rw [J_eq_inSubgroup, hJcomm]
      exact Subgroup.mem_zpowers z
    exact hJ'leC hz
  have hC_eq : C = Subgroup.zpowers z := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (K := C)
    · exact Subgroup.zpowers_le_of_mem hzC
    · rw [hcardC, Nat.card_zpowers, h1]
  have hTnt : Nontrivial T := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    rw [hTcard]
    norm_num
  obtain ⟨z1, hz1T, hz1ne⟩ := Subgroup.exists_ne_one_of_nontrivial T
  have hz1dvd : orderOf z1 ∣ 2 := by
    simpa [hTcard] using Subgroup.orderOf_dvd_natCard T hz1T
  have hz1ord : orderOf z1 = 2 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hz1dvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1ne
    · exact h
  have hT_eq : T = Subgroup.zpowers z1 := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (K := T)
    · exact Subgroup.zpowers_le_of_mem hz1T
    · rw [hTcard, Nat.card_zpowers, hz1ord]
  have hTCdisj : T ⊓ C = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [← hdisj]
    exact ⟨hx.1, Subgroup.map_subtype_le _ hx.2⟩
  have hz1_not_z : z1 ∉ Subgroup.zpowers z := by
    intro hz1z
    have hz1C : z1 ∈ C := by
      rw [hC_eq]
      exact hz1z
    have hz1bot : z1 ∈ T ⊓ C := ⟨hz1T, hz1C⟩
    rw [hTCdisj] at hz1bot
    exact hz1ne (Subgroup.mem_bot.mp hz1bot)
  refine ⟨z1, ?_, hz1_not_z, hz1ord⟩
  calc
    centerIn (J z) = T ⊔ C := hcenter_eq
    _ = Subgroup.zpowers z1 ⊔ Subgroup.zpowers z := by rw [hT_eq, hC_eq]
    _ = Subgroup.zpowers z ⊔ Subgroup.zpowers z1 := by rw [sup_comm]

theorem centralizer_J_eq_centerIn (h : Tim79a.ParrottHyp z) :
    H z ⊓ Subgroup.centralizer (J z : Set G) = centerIn (J z) := by
  obtain ⟨h1, h2, hcomm, h4, hquot⟩ := h
  apply le_antisymm
  · intro x hx
    exact ⟨h4 hx, hx.2⟩
  · intro x hx
    exact ⟨J_le_H hx.1, hx.2⟩

end CFSG.RankThree.GF2n.Parrott
