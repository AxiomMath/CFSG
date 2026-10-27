module

public import CFSG.Quasithin.H13.U3S1348S
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOrigRank
public import CFSG.Quasithin.H13.U3S1348G
public import CFSG.Quasithin.H13.U3S1348Q

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem pCoreOf_le_pCoreOf_of_le_of_le {H Y : Subgroup G} (hOY : pCoreOf 2 H ≤ Y)
    (hYH : Y ≤ H) : pCoreOf 2 H ≤ pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _ hOY ?_
    (pCoreOf_isPGroup 2 H)
  exact (normal_subgroupOf_iff_le_normalizer hOY).2 (hYH.trans (le_normalizer_pCoreOf 2 H))

theorem s134_isHStar_IT {H I M : Subgroup G} (hTsyl : IsSylowTwoOf T H) (hIH : I ≤ H)
    (hO2H : pCoreOf 2 H ≠ ⊥) (hTM : T ≤ M) (hIM : ¬ I ≤ M) (h3 : T.relIndex (I ⊔ T) = 3) :
    IsHStar T M (I ⊔ T) := by
  have hOT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hTsyl
  have hO : pCoreOf 2 (I ⊔ T) ≠ ⊥ := fun h => hO2H (le_bot_iff.1 (h ▸
    pCoreOf_le_pCoreOf_of_le_of_le (hOT.trans le_sup_right) (sup_le hIH hTsyl.1)))
  refine ⟨⟨le_sup_right, hO⟩, fun h => hIM (le_sup_left.trans h), fun Y hY hYIT hYM => ?_⟩
  rcases eq_or_eq_of_relIndex_three h3 hY.1 hYIT with h | h
  · exact absurd (h ▸ hTM) hYM
  · exact h

theorem s134_eq_IT_of_isHStar {H I L₁ M : Subgroup G} (hTsyl : IsSylowTwoOf T H)
    (hHq : quasithinO2QuotientIso H (Perm (Fin 3) × Perm (Fin 3))) (hTM : T ≤ M)
    (hITH : I ⊔ T ≤ H) (hL1TH : L₁ ⊔ T ≤ H) (hL1TM : L₁ ⊔ T ≤ M) (hHM : ¬ H ≤ M)
    (hIT : IsHStar T M (I ⊔ T)) (h9 : T.relIndex H = 9) (h3 : T.relIndex (I ⊔ T) = 3)
    (h3' : T.relIndex (L₁ ⊔ T) = 3) {X : Subgroup G} (hX : IsHStar T M X) (hXH : X ≤ H) :
    X = I ⊔ T := by
  have hGzSL : quasithinO2QuotientIso H A6.SL22.K := by
    obtain ⟨φ, hφ, hker⟩ := hHq
    let e : A6.SL22.K ≃* Perm (Fin 3) × Perm (Fin 3) :=
      MulEquiv.prodCongr CFSG.QuasithinUnique.Setup.Lift.sl2F2EquivPerm3
        CFSG.QuasithinUnique.Setup.Lift.sl2F2EquivPerm3
    refine ⟨e.symm.toMonoidHom.comp φ, e.symm.surjective.comp hφ, ?_⟩
    rw [← hker]
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact ⟨fun h => by simpa using congrArg e h, fun h => by rw [h, map_one]⟩
  obtain ⟨P₀, X₁, X₂, hP, hP', hc, hX₁, hX₂, hX₁₂, hX₂₁⟩ := A6.modelData_SL22.exists_data
  obtain ⟨A₁, A₂, -, -, -, -, hA₁₂, hA₂₁, -, -, hcls⟩ :=
    A6.overgroups_transport hGzSL hTsyl hP hP' hc hX₁ hX₂ hX₁₂ hX₂₁
  have hneT : ∀ {Y : Subgroup G}, T ≤ Y → T.relIndex Y = 3 → Y ≠ T := fun _ h => by
    rintro rfl
    rw [relIndex_self] at h
    omega
  have hneH : ∀ {Y : Subgroup G}, T.relIndex Y = 3 → Y ≠ H := fun h hY => by
    rw [hY] at h
    omega
  have hXT : X ≠ T := fun h => hX.2.1 (h ▸ hTM)
  have hXH' : X ≠ H := by
    rintro rfl
    have := hX.2.2 (I ⊔ T) hIT.1 hITH hIT.2.1
    exact hneH h3 this
  rcases hcls X hX.1.1 hXH with h | hX1 | hX2 | h
  · exact absurd h hXT
  · rcases hcls (I ⊔ T) le_sup_right hITH with h | h | h | h
    · exact absurd h (hneT le_sup_right h3)
    · exact hX1.trans h.symm
    · rcases hcls (L₁ ⊔ T) le_sup_right hL1TH with h' | h' | h' | h'
      · exact absurd h' (hneT le_sup_right h3')
      · exact absurd (by rw [hX1, ← h']; exact hL1TM) hX.2.1
      · exact absurd (by rw [h, ← h']; exact hL1TM) hIT.2.1
      · exact absurd (by rw [← h']; exact hL1TM) hHM
    · exact absurd h (hneH h3)
  · rcases hcls (I ⊔ T) le_sup_right hITH with h | h | h | h
    · exact absurd h (hneT le_sup_right h3)
    · rcases hcls (L₁ ⊔ T) le_sup_right hL1TH with h' | h' | h' | h'
      · exact absurd h' (hneT le_sup_right h3')
      · exact absurd (by rw [h, ← h']; exact hL1TM) hIT.2.1
      · exact absurd (by rw [hX2, ← h']; exact hL1TM) hX.2.1
      · exact absurd (by rw [← h']; exact hL1TM) hHM
    · exact hX2.trans h.symm
    · exact absurd h (hneH h3)
  · exact absurd h hXH'

theorem stmt13_4_8_of (hC137 : C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h44 : Stmt13_4_4)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56) (h1228 : Stmt12_2_8)
    (h139 : A6.Stmt13_3_9) : Stmt13_4_8 := by
  intro G _ _ T L V S z hz hzL hCz H VH hHz hsolv hred hZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := conjClosure (thompsonJ (r1Of T L V)) H with hIdef
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set M := normalizer (L : Set G) with hM
  have hJ := claim1348_of hC137 h1332 h331 h1222 h44 G T L V S z hz hzL hCz H VH hHz hsolv hred
    hZ
  have hzV : S.zV ∈ quasithinOmegaOneCenter T ⊓ centralizer (L : Set G) ⊓ (VH ⊔ zpowers z) := by
    refine ⟨⟨mem_quasithinOmegaOneCenter_iff.2 ⟨S.V_le_T S.zV_mem_V, ?_, S.zV_sq⟩,
      (S.mem_ZV_iff.2 (Or.inr rfl)).2⟩, mem_sup_left (hZ (S.mem_ZV_iff.2 (Or.inr rfl)))⟩
    refine mem_centralizer_iff.2 fun t ht => ?_
    have h1 := S.conj_zV ⟨t, S.frame.T_le ht⟩
    calc t * S.zV = (t * S.zV * t⁻¹) * t := by group
      _ = S.zV * t := by rw [h1]
  have hX : quasithinOmegaOneCenter T ⊓ centralizer (L : Set G) ⊓ (VH ⊔ zpowers z) ≠ ⊥ :=
    fun h => S.zV_ne_one ((mem_bot).1 (h ▸ hzV))
  obtain ⟨-, h442, -⟩ := h44 G T L V S z hz hzL H VH hHz hred hX
  have hcR := s134_r1Of_inf_centralizer S hHz hred h442
  obtain ⟨𝓗, 𝓘, B, hne, hcard⟩ := s134_blocks h56 S hHz hsolv hred hzL hcR hJ
  obtain ⟨hTsyl, hL1TH, hHzC, hO2H, hHM⟩ := s134_inHz_facts S hHz
  have hTH : T ≤ H := hTsyl.1
  have hHN : H ≤ normalizer (VH : Set G) := hred.2.1
  have hJR : thompsonJ (r1Of T L V) ≤ r1Of T L V := iSup₂_le fun _ hA => hA.1
  have hJT : thompsonJ (r1Of T L V) ≤ T := hJR.trans (r1Of_le_T T L V)
  have hIH : I ≤ H := conjClosure_le fun h hh j hj =>
    mul_mem (mul_mem hh (hTH (hJT hj))) (inv_mem hh)
  have hHI : H ≤ normalizer (I : Set G) := le_normalizer_conjClosure _ _
  have hIN : I ≤ normalizer (VH : Set G) := hIH.trans hHN
  obtain ⟨h5, -, -, -⟩ := h1332 G T L S.h13 L S.h13.faithful
  rcases a6_or_hatA6_of_isA6On S.frame.L_le (s134_pCoreOf_L_le S) h5 (s134_isA6On S) with
    he | hhat
  swap
  · exfalso
    rcases h442 with ⟨-, hC, -, -⟩ | ⟨Lp, -, hLphat, hLpeq, hHLp, -, hR₁⟩
    · exact s134_false_of_hat_C h1332 hC58 h317 h56 S hhat hHz hsolv hred hcR hJ hC B hne hcard
    · rw [hLphat hhat] at hLpeq hHLp hR₁
      exact s134_false_of_hat_sylow h1332 hC58 h317 h56 S hhat hHz hsolv hred hcR hJ hLpeq hHLp
        hR₁ B hne hcard
  have P := s134Plus_L1 S he
  have hs1 : 𝓘.card = 1 ∧ I ⊓ centralizer (VH : Set G) ≤ pCoreOf 2 H := by
    rcases h442 with ⟨-, hC, -, -⟩ | ⟨Lp, hLpA6, -, hLpeq, hHLp, -, hR₁⟩
    · exact ⟨s134_card_blocks_eq_one_of_C S P hHz hsolv hred hcR hJ hC B hne hcard,
        fun x hx => hC ▸ mem_inf.2 ⟨hIH hx.1, hx.2⟩⟩
    · rw [hLpA6 he] at hLpeq hHLp hR₁
      exact ⟨s134_card_blocks_eq_one_of_sylow S P hHz hsolv hred hcR hJ hLpeq hHLp hR₁ B hne
        hcard, s134_I_inf_C_of_sylow S P hHz hsolv hred hcR hJ hLpeq hHLp hR₁ B hne hcard⟩
  obtain ⟨K, hK𝓘, hIK, hHK⟩ := s134_single_block B hs1.1
  have hK : K ∈ 𝓗 := B.sub hK𝓘
  have hIq : quasithinO2QuotientIso I (Perm (Fin 3)) :=
    s134_quot_I_of hred hTsyl (r1Of_le_T T L V) hJ (B.hb.card_eq K hK) hIK hs1.2
  have hIcard : Nat.card ↥⁅VH, I⁆ = 4 := by
    rw [s134_comm_eq_U hred.2.2.1 hIN hIK]
    exact s134_card_U hred.2.2.1 B.hb hK
  have hCM := s134_centralizer_U_le h1332 hC58 h317 h56 S hz hzL hHz hred B.hb hK hIK hIH hHK
  have hdec : ∀ h ∈ H, ∃ i ∈ I, i⁻¹ * h ∈ H ⊓ M := by
    intro h hh
    obtain ⟨i, hi, hiC⟩ := s134_exists_I_mul hred.2.2.1 B.hb hK hIK hHN hHK hh
    have hiH : i⁻¹ * h ∈ H := mul_mem (inv_mem (hIH hi)) hh
    exact ⟨i, hi, mem_inf.2 ⟨hiH, hCM (mem_inf.2 ⟨hiH, hiC⟩)⟩⟩
  have hsylI : IsSylowTwoOf (T ⊓ I) I := A4.isSylowTwoOf_inf_normal hTsyl hIH hHI
  have hI3 : (T ⊓ I).relIndex I = 3 := relIndex_eq_three_of_quot hIq hsylI
  have hIM : ¬ I ≤ M :=
    s134_I_not_le_M h1332 h1228 S he hz hzL hHz hsolv hred hcR hJ B hne hcard
  have hHM3 : (H ⊓ M).relIndex H = 3 := s134_relIndex_HM hIH hHI hI3 S.T_le_NL hIM hdec
  have h23 := s134_two_three h139 S he hz hzL hHz hHM3
  have hHMeq : H ⊓ M = L₁ ⊔ T := s134_HM_eq h1222 h1332 h1228 S he hz hzL hHz h23
  have hTH9 : T.relIndex H = 9 := s134_relIndex_TH S he hHM3 hHMeq
  have hHeq : H = L₁ ⊔ I ⊔ T := by
    refine le_antisymm (fun h hh => ?_)
      (sup_le (sup_le (le_sup_left.trans hL1TH) hIH) hTH)
    obtain ⟨i, hi, hiM⟩ := hdec h hh
    rw [hHMeq] at hiM
    have e : h = i * (i⁻¹ * h) := by group
    rw [e]
    exact mul_mem (mem_sup_left (mem_sup_right hi))
      ((sup_le (le_sup_left.trans le_sup_left) le_sup_right : L₁ ⊔ T ≤ L₁ ⊔ I ⊔ T) hiM)
  obtain ⟨τ, hτJ, hτK, hτ1, -⟩ := s134_exists_tau S P hHz hsolv hred hcR hJ B hcard hK𝓘
  obtain ⟨hCq, hCO⟩ := s134_quot_C S he hHz hred hcR hJ B.hb hK hIK hHK hτJ hτK hτ1 hTH9
  set C := H ⊓ centralizer (C124.toG hred.2.2.1
    (commSub (⊤ : Subgroup (IntMod VH hred.2.2.1)) K) : Set G) with hC
  have hCH : C ≤ H := inf_le_left
  have hHU := s134_le_normalizer_U hred.2.2.1 hHN hHK
  have hHC : H ≤ normalizer (C : Set G) := fun h hh =>
    mem_normalizer_inf_of (le_normalizer hh) (mem_normalizer_centralizer_of_mem (hHU hh))
  have hHq : quasithinO2QuotientIso H (Perm (Fin 3) × Perm (Fin 3)) := by
    refine quasithinO2QuotientIso_prod hIH hCH hHI hHC (fun h hh => ?_) ?_ hIq hCq ?_ hCO
    · obtain ⟨i, hi, hiC⟩ := s134_exists_I_mul hred.2.2.1 B.hb hK hIK hHN hHK hh
      exact ⟨i, hi, i⁻¹ * h, mem_inf.2 ⟨mul_mem (inv_mem (hIH hi)) hh, hiC⟩, by group⟩
    · intro x hx
      exact hs1.2 (mem_inf.2 ⟨hx.1,
        s134_I_inf_CU_le hred.2.2.1 B.hb hK hIK hIN (mem_inf.2 ⟨hx.1, hx.2.2⟩)⟩)
    · exact le_antisymm (le_inf (pCoreOf_le 2 I) (pCoreOf_le_pCoreOf hIH hHI))
        (inf_pCoreOf_le_pCoreOf_of_le hIH)
  have hTI : T ≤ normalizer (I : Set G) := hTH.trans hHI
  have hsylIT : IsSylowTwoOf T (I ⊔ T) := A5.isSylowTwoOf_of_le S.h13.sylow le_sup_right
  have hIT3 : T.relIndex (I ⊔ T) = 3 := (quot_S3_sup hTI hsylIT hIq).2
  have hstar : IsHStar T M (I ⊔ T) := s134_isHStar_IT hTsyl hIH hO2H S.T_le_NL hIM hIT3
  have hL1T3 : T.relIndex (L₁ ⊔ T) = 3 := by
    rw [relIndex_sup_eq (s134_T_le_normalizer_L1 S), s134_relIndex_L1T S he]
  have hL1TM : L₁ ⊔ T ≤ M := hHMeq ▸ inf_le_right
  refine ⟨(quasithinO2QuotientIso_iff L _).2 he, hIq, hIcard, hHeq, hHq, hstar,
    fun X hXs hXH => ?_⟩
  exact s134_eq_IT_of_isHStar hTsyl hHq S.T_le_NL (sup_le hIH hTH) hL1TH hL1TM hHM hstar hTH9
    hIT3 hL1T3 hXs hXH

end CFSG.Quasithin.H13.U3
