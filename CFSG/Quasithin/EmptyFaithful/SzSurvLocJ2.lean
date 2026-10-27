module

public import CFSG.Quasithin.EmptyFaithful.SzSurvLocDefs
public import CFSG.Quasithin.EmptyFaithful.S1421QA17Surv10
public import CFSG.Quasithin.EmptyFaithful.S1421QA17Surv11
public import CFSG.Quasithin.EmptyFaithful.S1421QA17Count
public import CFSG.Quasithin.EmptyFaithful.S1421QA17AutData
public import CFSG.Quasithin.EmptyFaithful.S1421L2
public import CFSG.Quasithin.EmptyFaithful.S1421QA17Trans

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SzSurvLoc

open S1421QA17

section Setting

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem survivor10Loc_core (st : Setting1427 T M H K1)
    (hs : Survivor10Loc K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1))
    (htl : oTwoUpper H = K1 ∧ T = S1421.sOf T K1 ∧ pCoreOf 2 (mcOf T) = pCoreOf 2 K1) :
    ∃ z : G, z * z = 1 ∧ z ≠ 1 ∧ CharTwo (Subgroup.centralizer ({z} : Set G)) ∧
      IsQ8D8 ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) ∧
      Nonempty (OTwoQuot (Subgroup.centralizer ({z} : Set G)) ≃* alternatingGroup (Fin 5)) ∧
      ∃ g : G, g * z * g⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧
        g * z * g⁻¹ ≠ z := by
  obtain ⟨hL4, hQ8, hSK⟩ := hs
  obtain ⟨-, hTS, hQ⟩ := htl
  have hyp := st.hyp
  obtain ⟨z, hzZ, hz1, hzz, hall⟩ := exists_central_involution hyp
  have hC := centralizer_eq_mcOf hzZ hall
  have hQ8' : IsQ8D8 ↥(pCoreOf 2 (mcOf T)) := by rw [hQ]; exact hQ8
  have hK1c : Nat.card K1 = 1920 := by
    rw [card_eq_card_oTwoQuot_mul K1, hL4.card (by norm_num), hQ8.1]
    norm_num
  have hTK : T ≤ K1 := hTS.le.trans hSK
  have hT128 : Nat.card T ≤ 128 := by
    have hdvd : Nat.card T ∣ 1920 := hK1c ▸ Subgroup.card_dvd_of_le hTK
    obtain ⟨n, hn⟩ := hyp.sylow.1.exists_card_eq
    rw [hn] at hdvd ⊢
    by_contra hlt
    have hn8 : 8 ≤ n := by
      by_contra hn8
      have : 2 ^ n ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact hlt this
    have : 2 ^ 8 ∣ 1920 := (pow_dvd_pow 2 hn8).trans hdvd
    norm_num at this
  have hMc : K1 = mcOf T := eq_mcOf_of_card hyp (K1_le_mcOf st) hQ8' hK1c hT128
  have hHM : H = mcOf T :=
    le_antisymm (le_mcOf_of_isHStar hyp st.hStar)
      (hMc ▸ st.notation_.le_K.trans (oTwoUpper_le H))
  refine ⟨z, hzz, hz1, ?_, ?_, ?_, ?_⟩
  · rw [hC]
    exact charTwo_mcOf hyp
  · rw [hC]
    exact hQ8'
  · rw [hC, ← hMc]
    exact nonempty_mulEquiv_alt5_of_isL2Quot_two hL4
  · obtain ⟨y, hyY, hyN⟩ := IsConcreteLE.not_le_iff_exists.mp
      (S1421.not_y_le_normalizer_Z hyp st.facts)
    have hyM : y ∈ M := yOfL22_le T M hyY
    have hmem : y * z * y⁻¹ ∈ VZ T M := mem_conjClosure hyM hzZ
    refine ⟨y, ?_, ?_⟩
    · have := vz_le_pCoreOf st hmem
      rwa [hC, ← hHM]
    · intro hyz
      apply hyN
      rw [normalizer_omegaOneCenter_eq_mcOf hyp, ← hC]
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc y * z = (y * z * y⁻¹) * y := by group
        _ = z * y := by rw [hyz]

theorem false_of_survivor11Loc (hR : AutJ2OuterInvolution) (st : Setting1427 T M H K1)
    (hs : Survivor11Loc K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1))
    (htl : oTwoUpper H = K1 ∧ T = S1421.sOf T K1 ∧ pCoreOf 2 (mcOf T) = pCoreOf 2 K1) :
    False := by
  obtain ⟨hS5, hQ8, Y, iY, hY, TY0, M₁, φ, hSylY0, hTY0⟩ := hs
  obtain ⟨-, hTS, hQ⟩ := htl
  have hyp := st.hyp
  have := hyp.simple
  rw [← hTS] at hS5
  have hQ8' : IsQ8D8 ↥(pCoreOf 2 (mcOf T)) := by rw [hQ]; exact hQ8
  have hQK : pCoreOf 2 (mcOf T) ≤ K1 := hQ ▸ pCoreOf_le 2 K1
  obtain ⟨hXeq, θ, hker, hrange, hMc3840⟩ :=
    mcOf_eq_sup_of_s5 hyp (K1_le_mcOf st) hQ8' hQK hS5
  have hK1c : K1 ∈ cComp (K1 ⊔ S1421.sOf T K1) := st.notation_.cComp_mem
  have hns : ¬ K1 ≤ pCoreOf 2 (mcOf T) := by
    intro hle
    apply not_isSolvable_of_mem_cComp hK1c
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hK12 : IsPGroup 2 K1 := (pCoreOf_isPGroup 2 (mcOf T)).to_le hle
    have := hK12.isNilpotent
    infer_instance
  have hTN : T ≤ Subgroup.normalizer (K1 : Set G) := hTS ▸ inf_le_right
  have hn : mcOf T ≤ Subgroup.normalizer (K1 : Set G) :=
    hXeq ▸ sup_le Subgroup.le_normalizer hTN
  have hK1card : Nat.card K1 = 1920 :=
    card_eq_of_perfect_normal_s5 θ hker hrange hQ8'.1 (K1_le_mcOf st) hQK hn
      (perfect_of_mem_cComp hK1c) hns
  have hsylMc : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_T_mcOf hyp
  have hT256 : Nat.card T = 256 := by
    rw [hsylMc.card_eq]
    exact (twoPart_eq_of_card (n := 8) (m := 15) (by norm_num) (by rw [hMc3840]; norm_num)).trans
      (by norm_num)
  have hK1T : Nat.card ↥(T ⊓ K1) = 128 := by
    rw [st.notation_.sylow.card_eq]
    exact (twoPart_eq_of_card (n := 7) (m := 15) (by norm_num) (by rw [hK1card]; norm_num)).trans
      (by norm_num)
  have hcard : Nat.card T = 2 * Nat.card ↥(T ⊓ K1) := by rw [hT256, hK1T]
  have : Finite Y := by
    obtain ⟨e⟩ := hY
    exact Finite.of_equiv _ e.symm.toEquiv
  have hTP : T ≤ K1 ⊔ bigB K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1) :=
    hTS.le.trans ((le_sup_right : S1421.sOf T K1 ≤ borelOf K1 (S1421.sOf T K1) ⊔
      borelOf (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1) ⊔ S1421.sOf T K1).trans
      le_sup_right)
  have hMcP : mcOf T ≤ K1 ⊔ bigB K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1) :=
    hXeq ▸ sup_le le_sup_left hTP
  set ψ : ↥(mcOf T) →* Y := (M₁.subtype.comp φ.toMonoidHom).comp (Subgroup.inclusion hMcP)
    with hψdef
  have hψ : Function.Injective ψ :=
    (Subtype.val_injective.comp φ.injective).comp (Subgroup.inclusion_injective hMcP)
  have hTM : T ≤ mcOf T := T_le_mcOf hyp
  have hYS : IsSylowTwoOf ((T.subgroupOf (mcOf T)).map ψ) ⊤ := by
    have hP2 : IsPGroup 2 ((T.subgroupOf (mcOf T)).map ψ) :=
      (hyp.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm).map ψ
    have hcT := card_map_subgroupOf hψ hTM
    have hle1 : Nat.card ((T.subgroupOf (mcOf T)).map ψ) ≤ twoPart (⊤ : Subgroup Y) :=
      card_le_twoPart le_top hP2
    have hsylP : IsSylowTwoOf T (K1 ⊔ bigB K1 (S1421.l2Of T H (yOfL22 T M))
        (S1421.sOf T K1)) := isSylowTwoOf_of_isSylowTwo hyp.sylow hTP
    have h1 : Nat.card TY0 ≤ twoPart M₁ := card_le_twoPart hTY0 hSylY0.isPGroup
    have h2 : twoPart M₁ = twoPart (K1 ⊔ bigB K1 (S1421.l2Of T H (yOfL22 T M))
        (S1421.sOf T K1)) := by
      unfold twoPart
      rw [Nat.card_congr φ.toEquiv.symm]
    have h3 : Nat.card TY0 = twoPart (⊤ : Subgroup Y) := hSylY0.card_eq
    have h4 : Nat.card T = twoPart (K1 ⊔ bigB K1 (S1421.l2Of T H (yOfL22 T M))
        (S1421.sOf T K1)) := hsylP.card_eq
    exact isSylowTwoOf_of_card_eq le_top hP2 (by omega)
  obtain ⟨z, hzZ, hz1, hzz, hall⟩ := exists_central_involution hyp
  have hzT : z ∈ T := (quasithinOmegaOneCenter_le_center T hzZ).1
  have hzc : ∀ t ∈ T, t * z = z * t := fun t ht =>
    Subgroup.mem_centralizer_iff.mp (quasithinOmegaOneCenter_le_center T hzZ).2 t ht
  exact false_of_residual hR hyp.nonabelian hY hψ hTM (K1_le_mcOf st)
    (isSylowTwoOf_of_isSylowTwo hyp.sylow le_top) hzT hz1 hzz hzc
    (centralizer_eq_mcOf hzZ hall) (perfect_of_mem_cComp hK1c) hcard hYS

end Setting

end SzSurvLoc

theorem lemma14217J2Loc_of_residual (hR : AutJ2OuterInvolution) : Lemma14217J2Loc := by
  intro G _ _ T M H K1 st _ hsurv htl
  rcases hsurv with h10 | h11
  · obtain ⟨z, hzz, hz1, hC, hQ, hA, hw⟩ := SzSurvLoc.survivor10Loc_core st h10 htl
    have hTH2 : IsTypeH2 G z := ⟨by rw [pow_two]; exact hzz, hz1, hC, hQ, hA, hw⟩
    exact ⟨z, hTH2.sq, hz1, hC, hQ, hA, hw, S1421QA17.involutionClassCount_le_two hTH2⟩
  · exact (SzSurvLoc.false_of_survivor11Loc hR st h11 htl).elim

theorem lemma14217J2Loc_holds :
    Lemma14217J2Loc :=
  lemma14217J2Loc_of_residual S1421QA17.autJ2OuterInvolution_holds

end CFSG.Quasithin
