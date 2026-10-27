module

public import CFSG.Quasithin.EmptyFaithful.SzSurvLocStmt
public import CFSG.Quasithin.Background.Harris.R1.D4Facts
public import CFSG.Quasithin.Background.Harris.R1.D4L2B
public import CFSG.Quasithin.Background.Harris.R1.R1bAmalgam
public import CFSG.Quasithin.Background.Harris.R1.Q8L2Q
public import CFSG.Quasithin.Background.Harris.R1.S8

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.D4Hex
  CFSG.LargeExtraspecial.S63 CFSG.Quasithin.Background.Harris.R1.D4Vert

@[expose] def NormGensL28Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K1 L2 S Zs : Subgroup G), R1SettingLegacyBare K1 L2 S Zs →
    (∀ u ∈ S, u * u = 1 → (∀ s ∈ S, u * s = s * u) → u ∈ Zs) →
    IsL2Quot 3 (OTwoQuot K1) → ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥ →
    pCoreOf 2 K1 = vBeta K1 L2 S Zs → S ≤ K1 →
    ∃ z x a b : G, z ∈ Zs ∧ z ≠ 1 ∧ x ∈ conjClosure Zs L2 ∧ x ∉ Zs ∧ a ∈ K1 ∧ b ∈ K1 ∧
      (∀ r ∈ hRels, evalWord ![z, x, a, b] r = 1) ∧
      Subgroup.closure ({z, x, a, b} : Set G) = K1

section Transport

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem mem_pCore_iff_of_l2B
    (hset : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) (hSK : S ≤ K1) (e : ↥K1 ≃* ↥d4H)
    (heS : ∀ k : ↥K1, (k : G) ∈ S ↔ ((e k : D) ∈ d4U))
    (heV : ∀ k : ↥K1, (k : G) ∈ conjClosure Zs L2 ↔ ((e k : D) ∈ d4V))
    (heB : ∀ k : ↥K1, (k : G) ∈ bigB K1 L2 S ↔ (e k : D) ∈ d4B)
    (ψ : ↥(L2 ⊔ bigB K1 L2 S) ≃* ↥d4N)
    (hψ : ∀ (b : G) (hb : b ∈ bigB K1 L2 S),
      (ψ ⟨b, Subgroup.mem_sup_right hb⟩ : D) = (e ⟨b, bigB_le_K1 hset hR hSK hb⟩ : D))
    (y : ↥(L2 ⊔ bigB K1 L2 S)) :
    (y : G) ∈ pCoreOf 2 (L2 ⊔ S) ↔ (ψ y : D) ∈ Q2 := by
  classical
  have hBK : bigB K1 L2 S ≤ K1 := bigB_le_K1 hset hR hSK
  have hQS : pCoreOf 2 (L2 ⊔ S) ≤ S := SzR1.MNU.pCore_le_S_of_setting hset hR
  have hQeq : pCoreOf 2 (L2 ⊔ S) = S ⊓ Subgroup.centralizer (conjClosure Zs L2 : Set G) :=
    SzR1.MNU.pCore_eq_of_setting hset hR
  have hVK : conjClosure Zs L2 ≤ K1 :=
    (SzR1.MNU.V_le_pCore_of_setting hset hR).trans (hQS.trans hSK)
  have heV' : ∀ k ∈ K1, k ∈ conjClosure Zs L2 ↔ ebar e k ∈ d4V := fun k hk => by
    rw [ebar_of_mem e hk]; exact heV ⟨k, hk⟩
  have hVH : d4V ≤ d4H := d4V_le_d4H
  have hQt : ∀ k : ↥K1, (k : G) ∈ pCoreOf 2 (L2 ⊔ S) ↔ (e k : D) ∈ Q2 := by
    intro k
    have hC := mem_centralizer_ebar_iff e hVH heV' hVK k.2
    rw [ebar_of_mem e k.2] at hC
    rw [hQeq, ← centralizer_d4V_inf_d4U, Subgroup.mem_inf, Subgroup.mem_inf, heS k]
    exact and_congr Iff.rfl hC
  constructor
  · intro hy
    have hb : (y : G) ∈ bigB K1 L2 S := (le_sup_right : S ≤ bigB K1 L2 S) (hQS hy)
    have h1 : (ψ y : D) = (e ⟨y, hBK hb⟩ : D) := hψ (y : G) hb
    rw [h1]
    exact (hQt ⟨y, hBK hb⟩).mp hy
  · intro hy
    have hyB : (ψ y : D) ∈ d4B := d4U_le_d4B (Q2_le_d4U hy)
    set k : ↥K1 := e.symm ⟨ψ y, hyB.1⟩ with hk
    have hek : (e k : D) = ψ y := by rw [hk, MulEquiv.apply_symm_apply]
    have hkB : (k : G) ∈ bigB K1 L2 S := (heB k).mpr (by rw [hek]; exact hyB)
    have hψk : ψ ⟨k, Subgroup.mem_sup_right hkB⟩ = ψ y :=
      Subtype.ext ((hψ (k : G) hkB).trans hek)
    have hyk : (y : G) = k := congrArg Subtype.val (ψ.injective hψk).symm
    rw [hyk]
    exact (hQt k).mpr (hek ▸ hy)

theorem orderOf_s0D :
    orderOf s0D = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ fun h => s0D_not_mem_H (h ▸ d4H.one_mem)
  have h := evalWord_gD _ (nRels_mem 22 (by norm_num))
  rw [nRels22] at h
  simpa [evalWord, gD, pow_succ, mul_assoc] using h

end Transport

section Assembly


theorem f112R1bLoc_of_gens (hgens : NormGensL28Stmt) : F112R1bLocStatement := by
  intro G _ _ K1 L2 S Zs hset hZS hL
  classical
  have hR : Hyp111R K1 L2 S := F112J2.hyp111R_of_setting rankOneListedFacts hset
  have hna : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥ :=
    r1b_vBeta_nonabelian rankOneListedFacts hset hL
  have hZS' := hZS hna
  have hQK : pCoreOf 2 K1 = vBeta K1 L2 S Zs := qbetaLoc8_holds G K1 L2 S Zs hset hZS' hL hna
  have hSK : S ≤ K1 := s8_holds G K1 L2 S Zs hset hZS hL
  have hcen := centerBender_holds G K1 L2 S Zs hset ⟨3, by norm_num, Or.inl hL⟩ hna
  have hsp : IsSpecialPow 2 2 4 ↥(pCoreOf 2 K1) := by
    rw [hQK]; exact vBeta_special_of_L28 G K1 L2 S Zs hset hL hna
  have hK : Nat.card K1 = 258048 := S1421QA27.card_K1_of_survivor4 hL hsp
  obtain ⟨z, x, a, b, hz, hz1, hxV, hxZ, haK, hbK, hrel, hcl⟩ :=
    hgens G K1 L2 S Zs hset hZS' hL hna hQK hSK
  obtain ⟨e, heS, heV, heB⟩ :=
    exists_v1_iso d4HFacts hset hR hSK hQK hcen hK hz hz1 hxV hxZ haK hbK hrel hcl
  obtain ⟨ψ, hψ⟩ := exists_l2B_iso d4NFacts hset hR hSK e heS heV
  have hKB : K1 ⊔ bigB K1 L2 S = K1 := sup_eq_left.mpr (bigB_le_K1 hset hR hSK)
  have hL2 : IsL2Quot 1 (OTwoQuot L2) := isL2Quot_one_iff_perm3.mpr hset.s3
  have hQN : Q2 ≤ d4N := (Q2_le_d4U.trans d4U_le_d4B).trans inf_le_right
  have hQ : ∀ y : ↥(L2 ⊔ bigB K1 L2 S),
      (y : G) ∈ pCoreOf 2 (L2 ⊔ S) ↔ ψ y ∈ Q2.subgroupOf d4N := fun y => by
    rw [Subgroup.mem_subgroupOf]
    exact mem_pCore_iff_of_l2B hset hR hSK e heS heV heB ψ hψ y
  have hs0 : orderOf (⟨s0D, s0D_mem_N⟩ : ↥d4N) = 3 := by
    rw [← Subgroup.orderOf_coe]; exact orderOf_s0D
  have hQcard : Nat.card ↥(Q2.subgroupOf d4N) = 2 ^ 11 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv, card_Q2]
    norm_num
  have hmodel : ∀ Y : Subgroup ↥d4N, Y.Normal → (⟨s0D, s0D_mem_N⟩ : ↥d4N) ∈ Y →
      Q2.subgroupOf d4N ≤ Y := by
    intro Y hY hsY q hq
    have hconj : ∀ n ∈ d4N, ∀ x ∈ Y.map d4N.subtype, n * x * n⁻¹ ∈ Y.map d4N.subtype := by
      intro n hn x hx
      obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
      have hc := hY.conj_mem y hy ⟨n, hn⟩
      refine Subgroup.mem_map.mpr ⟨_, hc, ?_⟩
      rw [← hxy, map_mul, map_mul, map_inv]
      rfl
    have hle := Q2_le_of_normal (Y.map d4N.subtype) (Subgroup.map_subtype_le Y) hconj
      (Subgroup.mem_map_of_mem d4N.subtype hsY)
    obtain ⟨y, hy, hyq⟩ := Subgroup.mem_map.mp (hle (Subgroup.mem_subgroupOf.mp hq))
    rwa [show q = y from Subtype.ext hyq.symm]
  obtain ⟨-, -, hO⟩ := pCore_L2_eq hset hL hna hQK hSK ψ (Q2.subgroupOf d4N) ⟨s0D, s0D_mem_N⟩
    hQ hs0 hQcard hmodel
  exact survivor4_of_isos hR hKB e heB ψ (fun b hb _ => hψ b hb) hL hsp hL2 hO

end Assembly

end CFSG.Quasithin.Background.Harris.R1
