module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S29Defs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S29ModTab
public import CFSG.Quasithin.EmptyFaithful.SzF53MZa

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher.S29

variable {G : Type} [Group G] [Finite G]

theorem modFacts_of_modelSec {M : Model 5} (hM : M = orth ∨ M = nat) {X S Z : Subgroup G}
    (hS : IsSylowTwoOf S X) (hq : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 5)))
    (h : IsModelSec M X ⊥ Z) : ModFacts X S Z := by
  have hW : Nat.card M.W = 16 := by
    rcases hM with rfl | rfl
    · exact card_orth
    · exact card_nat
  have hQ := h.cSecIn_eq_pCoreOf hq
  have hZcard : Nat.card Z = 16 := by rw [IsModelSec.card_bot h, hW]
  obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := h
  obtain ⟨Ψ, β', hΨs, hkΨ, hsd', hPS, hsgn⟩ := hsd.exists_normalized hθs hθk hS
  have hSX : S ≤ X := hS.1
  have hQX : pCoreOf 2 X ≤ X := LieType.BorelTits.pCoreOf_le 2 X
  have hkΨQ : Ψ.ker = (pCoreOf 2 X).subgroupOf X := by rw [hkΨ, hQ]
  have hbar : ∀ B : Subgroup G, B ≤ S → (B.subgroupOf X).map Ψ ≤ S5Syl := fun B hB => by
    rw [← hPS]
    exact Subgroup.map_mono fun y hy => Subgroup.mem_subgroupOf.mpr
      (hB (Subgroup.mem_subgroupOf.mp hy))
  have hcardB : ∀ B : Subgroup G, B ≤ X →
      Nat.card ((B.subgroupOf X).map Ψ) = (pCoreOf 2 X ⊓ B).relIndex B := fun B hB => by
    rw [← Subgroup.relIndex_ker, hkΨQ, Subgroup.relIndex_subgroupOf hB,
      Subgroup.inf_relIndex_right]
  have hfixIdx : ∀ B : Subgroup G, B ≤ X →
      (Z ⊓ Subgroup.centralizer (B : Set G)).relIndex Z =
        (fixW M ((B.subgroupOf X).map Ψ)).index := fun B hB => by
    have hfix : fixSecIn B ⊥ Z = Z ⊓ Subgroup.centralizer (B : Set G) := by
      ext x
      rw [X1512.mem_fixSecIn bot_le, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
      constructor
      · rintro ⟨hxZ, hx⟩
        refine ⟨hxZ, fun a ha => ?_⟩
        have := hx a ha
        rw [Subgroup.mem_bot] at this
        exact comm_eq_one_iff.mp this
      · rintro ⟨hxZ, hx⟩
        refine ⟨hxZ, fun a ha => ?_⟩
        rw [Subgroup.mem_bot]
        exact comm_eq_one_iff.mpr (hx a ha)
    rw [← hfix]
    exact hsd'.relIndex_fixSecIn bot_le hB
  have hcommCard : ∀ B : Subgroup G, B ≤ X →
      Nat.card ↥⁅Z, B⁆ = Nat.card (commW M ((B.subgroupOf X).map Ψ) ⊤) := fun B hB => by
    have hD2 := hsd'.card_commSec (bot_le : ⊥ ≤ Z) hB
    have hcomm_eq : commSec B ⊥ Z = ⁅Z, B⁆ := by unfold commSec; exact sup_bot_eq _
    rwa [hcomm_eq, Subgroup.relIndex_bot_left] at hD2
  refine ⟨hZcard, ?_, ?_, ?_⟩
  ·
    intro B hBS hBe
    have hBX : B ≤ X := hBS.trans hSX
    have hsq : ∀ x ∈ (B.subgroupOf X).map Ψ, x * x = 1 := by
      rintro _ ⟨b, hb, rfl⟩
      have hb2 : (b : G) ^ 2 = 1 := hBe.2 _ (Subgroup.mem_subgroupOf.mp hb)
      rw [← map_mul]
      have : b * b = 1 := Subtype.ext (by simpa [pow_two] using hb2)
      rw [this, map_one]
    obtain ⟨h4, h16, h4c⟩ := exp_two_profile M hM (hbar B hBS) hsq
    rw [hcardB B hBX] at h4 h16 h4c
    refine ⟨h4, ?_, fun h4' => ?_⟩
    · rw [hfixIdx B hBX]
      have hmi := Subgroup.card_mul_index (fixW M ((B.subgroupOf X).map Ψ))
      rw [hW] at hmi
      have hpos : 0 < Nat.card (fixW M ((B.subgroupOf X).map Ψ)) := Nat.card_pos
      rw [← hcardB B hBX] at h16 ⊢
      refine Nat.le_of_mul_le_mul_right (c := Nat.card (fixW M ((B.subgroupOf X).map Ψ))) ?_ hpos
      calc _ ≤ 16 := h16
        _ = _ := by rw [← hmi, mul_comm]
    · rw [hcommCard B hBX]
      exact h4c h4'
  ·
    intro B hBS hSn h2
    have hBX : B ≤ X := hBS.trans hSX
    have hQB : pCoreOf 2 X ⊔ B ≤ X := sup_le hQX hBX
    have hmapQB : (((pCoreOf 2 X) ⊔ B).subgroupOf X).map Ψ = (B.subgroupOf X).map Ψ := by
      rw [Subgroup.subgroupOf_sup hQX hBX, Subgroup.map_sup, ← hkΨQ,
        (Subgroup.map_eq_bot_iff _).mpr le_rfl, bot_sup_eq]
    have hcard : Nat.card ((B.subgroupOf X).map Ψ) = 2 := by
      rw [← hmapQB, ← Subgroup.relIndex_ker, hkΨQ, Subgroup.relIndex_subgroupOf hQB, h2]
    have hnorm : ∀ τ ∈ S5Syl, ∀ b ∈ (B.subgroupOf X).map Ψ,
        τ * b * τ⁻¹ ∈ (B.subgroupOf X).map Ψ := by
      intro τ hτ b hb
      rw [← hPS] at hτ
      obtain ⟨s, hs, rfl⟩ := hτ
      obtain ⟨y, hy, rfl⟩ := hb
      have hsy : (s : G) * (y : G) * (s : G)⁻¹ ∈ pCoreOf 2 X ⊔ B :=
        ((Subgroup.mem_normalizer_iff.mp (hSn (Subgroup.mem_subgroupOf.mp hs))) (y : G)).mp
          (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hy))
      rw [← hmapQB]
      refine ⟨s * y * s⁻¹, Subgroup.mem_subgroupOf.mpr hsy, ?_⟩
      rw [map_mul, map_mul, map_inv]
    have hBbar : (B.subgroupOf X).map Ψ =
        Subgroup.zpowers (Equiv.swap (0 : Fin 5) 2 * Equiv.swap 1 3) :=
      eq_zpowers_of_normal_card_two hcard (hbar B hBS) hnorm
    have hprof4 : Nat.card (fixW M (Subgroup.zpowers (Equiv.swap (0 : Fin 5) 2 *
        Equiv.swap 1 3))) = 4 := by
      rcases hM with rfl | rfl
      · exact congrArg (fun p => p.2.1) profile_orth.2.1
      · exact congrArg (fun p => p.2.1) profile_nat.2.1
    rw [hfixIdx B hBX, hBbar]
    have hmi := Subgroup.card_mul_index
      (fixW M (Subgroup.zpowers (Equiv.swap (0 : Fin 5) 2 * Equiv.swap 1 3)))
    rw [hprof4, hW] at hmi
    omega
  ·
    intro U hUZ hSnU hU8 s hsS hscomm
    have hsX : s ∈ X := hSX hsS
    have hinvU : ∀ k ∈ S, ∀ u ∈ U, k * u * k⁻¹ ∈ U := fun k hk u hu =>
      ((Subgroup.mem_normalizer_iff.mp (hSnU hk)) u).mp hu
    obtain ⟨Y, hY, hYm⟩ := (hsd'.invariant_iff_sub hSX bot_le hUZ).mp hinvU
    have hYinv : IsInvSub M S5Syl Y := by rw [← hPS]; exact hY
    have hYcard : Nat.card Y = 2 ^ 3 := by
      have h1 : Nat.card (Y.map β') = Nat.card Y := Subgroup.card_map_of_injective hsd'.inj
      rw [← h1, hYm, ← Subgroup.relIndex_ker, QuotientGroup.ker_mk',
        Subgroup.relIndex_subgroupOf hUZ, Subgroup.relIndex_bot_left, hU8]
      norm_num
    have hVinv : IsInvSub M S5Syl (commW M S5Syl ⊤) :=
      isInvSub_commW M (fun _ _ _ _ => trivial)
    have hVcard : Nat.card (commW M S5Syl ⊤) = 2 ^ 3 := by
      rw [show Nat.card (commW M S5Syl ⊤) = 8 from
        congrArg (fun p => p.1) (profile_sylow M hM card_S5Syl)]
      norm_num
    have hYV : Y = commW M S5Syl ⊤ :=
      (lemma26 M hM 3 (by norm_num)).unique ⟨hYinv, hYcard⟩ ⟨hVinv, hVcard⟩
    have hact := (hsd'.act_trivial_iff hUZ hYm hsX).mp fun x hx => by
      rw [Subgroup.mem_bot]
      exact comm_eq_one_iff.mpr (hscomm x hx)
    rw [hYV] at hact
    have hmem : Ψ ⟨s, hsX⟩ ∈ S5Syl := by
      rw [← hPS]
      exact ⟨⟨s, hsX⟩, Subgroup.mem_subgroupOf.mpr hsS, rfl⟩
    have h1 : Ψ ⟨s, hsX⟩ = 1 := eq_one_of_fixes_commW_sylow M hM hmem hact
    have : (⟨s, hsX⟩ : ↥X) ∈ Ψ.ker := h1
    rw [hkΨQ] at this
    exact Subgroup.mem_subgroupOf.mp this

theorem modFacts_of {X S Z : Subgroup G} (hS : IsSylowTwoOf S X)
    (hq : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 5)))
    (hZ : IsOrthSec X ⊥ Z ∨ IsNatSec X ⊥ Z) : ModFacts X S Z := by
  rcases hZ with h | h
  · exact modFacts_of_modelSec (Or.inl rfl) hS hq h
  · exact modFacts_of_modelSec (Or.inr rfl) hS hq h

end F53.Stellmacher.S29

end CFSG.Quasithin
