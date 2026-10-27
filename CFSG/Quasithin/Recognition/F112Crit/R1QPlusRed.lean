module

public import CFSG.Quasithin.Recognition.F112Crit.ListedNoMcL

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.MS93 (oddGen)

open CosetGeom (nbrs γ₀ γ₁)

@[expose] def R1QCenter : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), F112Hyp L1 L2 S → VS3 L1 → S ≤ L1 →
    VBig L2 → (¬ ∃ n : ℕ, IsL2Quot n (oTwoQuot ↥L2)) → centerOf (L2 ⊔ S ⊔ borelOf L1 S) ≠ ⊥

@[expose] def S3OddB (P : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), F112Hyp L1 L2 S →
    Setting L1 L2 S (omegaOneCenterOf (L2 ⊔ S ⊔ borelOf L1 S)) → VS3 L1 → VBig L2 →
    (¬ ∃ n : ℕ, IsL2Quot n (oTwoQuot ↥L2)) →
    Odd (critB (L1 ⊔ L2 ⊔ S) (P₂ L1 L2 S) (P₁ L1 L2 S)
      (omegaOneCenterOf (L2 ⊔ S ⊔ borelOf L1 S))) →
    P (critB (L1 ⊔ L2 ⊔ S) (P₂ L1 L2 S) (P₁ L1 L2 S)
      (omegaOneCenterOf (L2 ⊔ S ⊔ borelOf L1 S))) → False

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

private theorem omegaOneOf_ne_bot_of_isPGroup' {Y : Subgroup G} (hY : IsPGroup 2 Y)
    (hne : Y ≠ ⊥) : omegaOneOf Y ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hY.exists_card_eq
  have h2 : 2 ∣ Nat.card Y := by
    rcases n with _ | n
    · exact absurd (Subgroup.eq_bot_of_card_eq Y (by simpa using hn)) hne
    · rw [hn, pow_succ]
      exact dvd_mul_left 2 _
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hy2 : y ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y
  have hy2' : (y : G) ^ 2 = 1 := by simpa using congrArg Subtype.val hy2
  intro hbot
  have hmem : (y : G) ∈ omegaOneOf Y := Subgroup.subset_closure ⟨y.2, hy2'⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have hy1 : y = 1 := Subtype.ext hmem
  rw [hy1, orderOf_one] at hy
  exact absurd hy (by norm_num)

theorem setting_of_s3 (hH : F112Hyp L1 L2 S) (hS3 : VS3 L1)
    (hc : centerOf (L2 ⊔ S ⊔ borelOf L1 S) ≠ ⊥) (hS : S ≤ L1) :
    Setting L1 L2 S (omegaOneCenterOf (L2 ⊔ S ⊔ borelOf L1 S)) := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hH.1
  have hP : P₂ L1 L2 S = L2 ⊔ S ⊔ borelOf L1 S := P₂_swap_eq L2 L1 S
  have hSyl : IsSylowTwoOf S (L2 ⊔ S ⊔ borelOf L1 S) := by
    rw [← hP]
    exact F112W.isSylowTwoOf_parabolic' hR
  have hZS : centerOf (L2 ⊔ S ⊔ borelOf L1 S) ≤ S :=
    (centerOf_le_pCoreOf_of_charTwo hH.1.h2.charTwo).trans
      (pCoreOf_two_le_of_isSylowTwoOf hSyl)
  have hcard := card_oTwoQuot_of_vS3 hS3
  exact
    { hyp := hR
      S_le := hS
      ne_bot := omegaOneOf_ne_bot_of_isPGroup' (hH.1.h2.pgroup.to_le hZS) hc
      isElemAbelian := ⟨⟨⟨fun x y => Subtype.ext (A4.mul_comm_of_mem_omegaOneCenterOf x.2 y.2)⟩⟩,
        fun _ hx => A4.sq_eq_one_of_mem_omegaOneCenterOf hx⟩
      le_S := (A4.omegaOneCenterOf_le_centerOf _).trans hZS
      centralizes := hP ▸ le_centralizer_omegaOneCenterOf _
      prime := by rw [relIndex_borelOf_eq_three hR hcard]; norm_num
      cyclic := isCyclic_of_vS3 hS3 }

theorem f112R1QPlus_of_parts (hC : R1QCenter)
    (h3 : S3OddB (· = 3)) (h5 : S3OddB (5 ≤ ·)) : CFSG.Quasithin.H13.F112R1QPlus := by
  intro G _ _ L1 L2 S hH hS3 hS hBig
  by_contra hL2
  have hL : IsRankOneListed (oTwoQuot ↥L2) := hH.1.h2.listed
  have hns : ¬ Group.IsSolvable (oTwoQuot ↥L2) := fun h =>
    VBig.not_isSolvable hL hBig (isSolvable_vertex_of_oTwoQuot h)
  obtain ⟨n, i, hn, hK, htype⟩ := exists_isBenderQuot_of_listed hL hns
  have h65 : 65 ≤ (2 ^ n) ^ i + 1 := htype.resolve_left fun h => hL2 ⟨n, h.2⟩
  have hs := setting_of_s3 hH hS3 (hC G L1 L2 S hH hS3 hS hBig hL2) hS
  have hcr := hs.toCritAmalgam
  have hcard := card_oTwoQuot_of_vS3 hS3
  have hX := hs.isLocalRegGrp (oddGen_inf_borelOf_le hs.hyp (Or.inl hcard))
  rw [relIndex_borelOf_eq_three hs.hyp hcard] at hX
  have hloc := hX.isLocalReg hcr
  have hb3 := hs.three_le_critB (isQuasisimple_of_listed hL hns)
    (listedNoMcL _ hL hns fun h => hL2 ⟨2, h⟩)
  rcases Nat.even_or_odd (critB (L1 ⊔ L2 ⊔ S) (P₂ L1 L2 S) (P₁ L1 L2 S)
      (omegaOneCenterOf (L2 ⊔ S ⊔ borelOf L1 S))) with hb | hb
  ·
    have hb4 : 4 ≤ critB (L1 ⊔ L2 ⊔ S) (P₂ L1 L2 S) (P₁ L1 L2 S)
        (omegaOneCenterOf (L2 ⊔ S ⊔ borelOf L1 S)) := by
      obtain ⟨k, hk⟩ := hb
      omega
    have h17 := theorem723 hcr hloc (Or.inl rfl) (hs.benderLocal hK) hb hb4
    rw [hs.card_nbrs_γ₀ hK] at h17
    omega
  ·
    rcases Nat.lt_or_ge (critB (L1 ⊔ L2 ⊔ S) (P₂ L1 L2 S) (P₁ L1 L2 S)
        (omegaOneCenterOf (L2 ⊔ S ⊔ borelOf L1 S))) 4 with hlt | hge
    · exact h3 G L1 L2 S hH hs hS3 hBig hL2 hb (by omega)
    · refine h5 G L1 L2 S hH hs hS3 hBig hL2 hb ?_
      obtain ⟨k, hk⟩ := hb
      show 5 ≤ _
      omega

end CFSG.Quasithin.F112Crit

end
