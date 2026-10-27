module

public import CFSG.Quasithin.Vol2.Ch11SecSX1b
public import CFSG.Quasithin.Vol2.Ch11SecSK0d
public import CFSG.Quasithin.Vol2.Ch11SecSPGL

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G} {P₁ P₂ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)}

theorem xOne_not_le_sectionCentralizer (hPGL : FactPGL34Levi) (hN : NatFacts)
    (h1102 : Stmt11_0_2) (h : StarHyp G T L I V₁ V₂ X K) (hc : CartanL L V₁ V₂ X)
    (hP : ParData T K (LOf L V₁) P₁ P₂) :
    ¬ xOne X (LOf L V₁) ≤ sectionCentralizer (k0Of K P₂) (pCoreOf 2 (k0Of K P₂)) := by
  intro hle
  set Y := K ⊔ xOne X (LOf L V₁) with hY
  have hKY : K ≤ Y := le_sup_left
  have hXY : xOne X (LOf L V₁) ≤ Y := le_sup_right
  have hL₁Y : LOf L V₁ ≤ Y := h.L₁_le_K.trans hKY
  have hK₀Y : k0Of K P₂ ≤ Y := (k0Of_le K P₂).trans hKY
  have hSY := h.isSylowTwoOf_inf_sup hN h1102 hc
  have hOY : pCoreOf 2 Y ≤ T ⊓ K := pCoreOf_two_le_of_isSylowTwoOf hSY
  have hQs := isSolvable_pCoreOf_two Y
  have hQ₁ : pCoreOf 2 Y ≤ Subgroup.normalizer (LOf L V₁ : Set G) :=
    hOY.trans (inf_le_left.trans h.T_le_normalizer_L₁)
  have hQ₀ : pCoreOf 2 Y ≤ Subgroup.normalizer (k0Of K P₂ : Set G) :=
    hOY.trans (inf_le_left.trans (h.T_le_normalizer_k0Of hP))
  have hL₁ne : LOf L V₁ ≠ ⊥ := fun hb => hP.c₁.1 (by
    rw [← hP.l₁, hb]; unfold modO2Image; simp)
  obtain ⟨F, _, _, hF, he⟩ := h.pgl
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨x, hx⟩, hx3⟩ := exists_prime_orderOf_dvd_card' (G := ↥(xOne X (LOf L V₁))) 3
    (by rw [hc.cardX₁])
  rw [Subgroup.orderOf_mk] at hx3
  set x' : ↥Y ⧸ CFSG.pCore 2 ↥Y := QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨x, hXY hx⟩ with hx'
  have hKR : modO2Image Y K ≤ ⁅(⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)), ⊤⁆ := by
    rw [← modO2Image_perfect hKY h.perfect]
    exact Subgroup.commutator_mono le_top le_top
  have hne' : ∀ B : Subgroup G, B ≤ K → ⁅B, B⁆ = B →
      pCoreOf 2 Y ≤ Subgroup.normalizer (B : Set G) → B ≠ K →
        modO2Image Y B ≠ ⁅(⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)), ⊤⁆ := by
    intro B hBK hBp hQB hBne heq
    apply hBne
    refine le_antisymm hBK ?_
    have h1 := le_sup_of_modO2Image_le hKY (hBK.trans hKY) (heq ▸ hKR)
    calc K = perfectCore K := (perfectCore_eq_self_of_perfect h.perfect).symm
      _ ≤ perfectCore (B ⊔ pCoreOf 2 Y) := perfectCore_mono h1
      _ = B := perfectCore_sup_eq hBp hQs hQB
  have hx1 : x' ∈ sectionCentralizer (modO2Image Y (LOf L V₁))
      (pCoreOf 2 (modO2Image Y (LOf L V₁))) := mk_mem_sectionCentralizer hL₁Y (hXY hx) hx.2
  have hx0 : x' ∈ sectionCentralizer (modO2Image Y (k0Of K P₂))
      (pCoreOf 2 (modO2Image Y (k0Of K P₂))) := mk_mem_sectionCentralizer hK₀Y (hXY hx) (hle hx)
  refine hPGL _ ⟨F, inferInstance, inferInstance, hF, he⟩ _ _ _ (isSylowTwoOf_modO2Image hSY)
    ?_ (modO2Image_ne_bot hL₁Y h.perfect_L₁ hL₁ne)
    (modO2Image_ne_bot hK₀Y (k0Of_perfect K P₂) hP.k0Of_ne_bot)
    (modO2Image_perfect hL₁Y h.perfect_L₁) (modO2Image_perfect hK₀Y (k0Of_perfect K P₂))
    (hne' _ h.L₁_le_K h.perfect_L₁ hQ₁ h.L₁_ne_K)
    (hne' _ (k0Of_le K P₂) (k0Of_perfect K P₂) hQ₀ (k0Of_ne_K hP))
    (modO2Image_le_normalizer (inf_le_left.trans h.T_le_normalizer_L₁))
    (modO2Image_le_normalizer (inf_le_left.trans (h.T_le_normalizer_k0Of hP))) x'
    (mk_mem_normalizer_modO2Image (hXY hx) (h.cartan_le_normalizer_inf hN h1102 hP hx.1))
    ?_ hx1 hx0
  · intro heq
    have h1 := sup_eq_of_modO2Image_eq hL₁Y hK₀Y heq
    apply k0Of_ne_L₁ hP
    rw [← perfectCore_sup_eq (k0Of_perfect K P₂) hQs hQ₀, ← h1,
      perfectCore_sup_eq h.perfect_L₁ hQs hQ₁]
  · have hd : orderOf x' ∣ 3 := by
      have := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) ⟨x, hXY hx⟩
      rwa [Subgroup.orderOf_mk, hx3] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
    · exfalso
      rw [orderOf_eq_one_iff, hx', QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have hxO : x ∈ pCoreOf 2 Y := by
        rw [pCoreOf_two_eq_map]
        exact ⟨_, h1, rfl⟩
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) ⟨x, hxO⟩
      have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have := orderOf_dvd_of_pow_eq_one hk'
      rw [hx3] at this
      have h32 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_three this)
      omega
    · exact h1

end StarHyp

end CFSG.Quasithin.Vol2.Ch11.SecS
