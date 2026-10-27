module

public import CFSG.RankThree.GF2n.Parrott.ExtraspecialJ

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem central_in_J_of_decomposition {T F : Subgroup G}
    (hT : Nat.card T = 2) (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f)
    (hsup : T ⊔ F = J z) :
    ∀ t ∈ T, ∀ x ∈ J z, Commute t x := by
  have hTcomm : IsMulCommutative T := CFSG.isMulCommutative_of_card_two T hT
  have hTT : ∀ t ∈ T, ∀ t' ∈ T, Commute t t' :=
    fun t ht t' ht' => CFSG.commute_of_mem_of_isMulCommutative hTcomm ht ht'
  intro t ht x hx
  have hx' : x ∈ T ⊔ F := by
    rwa [← hsup] at hx
  obtain ⟨t', ht', f, hf, rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp hx'
  exact (hTT t ht t' ht').mul_right (hcomm t ht f hf)

theorem isExtraspecial2_of_complement (h : Tim79a.ParrottHyp z)
    {T K : Subgroup G} (hT : Nat.card T = 2)
    (hsup : T ⊔ K = J z) (hinf : T ⊓ K = ⊥)
    (hcent : ∀ t ∈ T, ∀ x ∈ J z, Commute t x)
    (hKcard : Nat.card K = 2 ^ 9) :
    IsExtraspecial2 K := by
  classical
  have hTcomm : IsMulCommutative T := CFSG.isMulCommutative_of_card_two T hT
  have hTT : ∀ t ∈ T, ∀ t' ∈ T, Commute t t' :=
    fun t ht t' ht' => CFSG.commute_of_mem_of_isMulCommutative hTcomm ht ht'
  have hKJ : K ≤ J z := by
    rw [← hsup]
    exact le_sup_right
  have hcommTK : ∀ t ∈ T, ∀ k ∈ K, Commute t k :=
    fun t ht k hk => hcent t ht k (hKJ hk)
  have hcenterJ : centerIn (J z) = T ⊔ (Subgroup.center K).map K.subtype := by
    rw [← hsup]
    exact CFSG.centerIn_sup_eq_sup_center hTT hcommTK hinf
  have hTCdisj : T ⊓ (Subgroup.center K).map K.subtype = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [← hinf]
    exact ⟨hx.1, Subgroup.map_subtype_le _ hx.2⟩
  have hcommTC : ∀ t ∈ T, ∀ c ∈ (Subgroup.center K).map K.subtype, Commute t c := by
    intro t ht c hc
    obtain ⟨c', hc', rfl⟩ := Subgroup.mem_map.mp hc
    exact hcommTK t ht c' c'.2
  have hcardC : Nat.card ((Subgroup.center K).map K.subtype) = 2 := by
    have hcard := CFSG.card_sup_eq_mul_of_commute T
      ((Subgroup.center K).map K.subtype) hcommTC hTCdisj
    rw [← hcenterJ, card_centerIn_J h, hT] at hcard
    have hcard' : 2 * Nat.card ((Subgroup.center K).map K.subtype) = 2 * 2 := by
      omega
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) hcard'
  have hcardCenterK : Nat.card (centerIn K) = 2 := by
    rw [CFSG.centerIn_eq_map_center K]
    exact hcardC
  obtain ⟨T₀, F, hT₀, hF, _hFcard, _hdisj₀, hcomm₀, hsup₀⟩ := exists_decomposition h
  have hT₀comm : IsMulCommutative T₀ := CFSG.isMulCommutative_of_card_two T₀ hT₀
  have hT₀T₀ : ∀ t ∈ T₀, ∀ t' ∈ T₀, Commute t t' :=
    fun t ht t' ht' => CFSG.commute_of_mem_of_isMulCommutative hT₀comm ht ht'
  have hF_le_J : F ≤ J z := by
    rw [← hsup₀]
    exact le_sup_right
  have hcommJ : ⁅J z, J z⁆ = (Subgroup.center F).map F.subtype := by
    apply le_antisymm
    · rw [← hsup₀]
      calc
        ⁅T₀ ⊔ F, T₀ ⊔ F⁆ ≤ ⁅F, F⁆ :=
          CFSG.commutator_sup_le_commutator_right hT₀T₀ hcomm₀
        _ = (Subgroup.center F).map F.subtype := hF.2.1
    · rw [← hF.2.1]
      exact Subgroup.commutator_mono hF_le_J hF_le_J
  have hcardCommJ : Nat.card (⁅J z, J z⁆ : Subgroup G) = 2 := by
    rw [hcommJ, ← hF.2.1]
    exact hF.2.2
  have hcommJK : ⁅J z, J z⁆ = ⁅K, K⁆ := by
    apply le_antisymm
    · rw [← hsup]
      exact CFSG.commutator_sup_le_commutator_right hTT hcommTK
    · rw [← hsup]
      exact Subgroup.commutator_mono le_sup_right le_sup_right
  have hcardCommK : Nat.card (⁅K, K⁆ : Subgroup G) = 2 := by
    rw [← hcommJK]
    exact hcardCommJ
  have hcommJ_le_centerJ : ⁅J z, J z⁆ ≤ centerIn (J z) := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact commutator_mem_centerIn_J h hx hy
  have hcommK_le_centerJ : ⁅K, K⁆ ≤ centerIn (J z) :=
    hcommJK ▸ hcommJ_le_centerJ
  have hinf_center : K ⊓ centerIn (J z) ≤ centerIn K := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    intro y hy
    exact hx.2.2 y (hKJ hy)
  have hcommK_le_centerK : ⁅K, K⁆ ≤ centerIn K :=
    (le_inf (Subgroup.commutator_le_self K) hcommK_le_centerJ).trans hinf_center
  have hcommK_eq_centerK : ⁅K, K⁆ = centerIn K := by
    apply Subgroup.eq_of_le_of_card_ge hcommK_le_centerK
    rw [hcardCenterK, hcardCommK]
  refine ⟨IsPGroup.of_card (n := 9) hKcard, ?_, hcardCommK⟩
  rw [hcommK_eq_centerK, CFSG.centerIn_eq_map_center K]

end CFSG.RankThree.GF2n.Parrott
