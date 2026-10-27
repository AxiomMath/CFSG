module

public import CFSG.Quasithin.H13.A5S1327i

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits

theorem A4_cube_or : ∀ σ : Equiv.Perm (Fin 5), σ 4 = 4 → σ.sign = 1 →
    σ ^ 3 = 1 ∨ ((σ * c3p⁻¹) ^ 3 = 1 ∧ (σ * c3p⁻¹) 4 = 4 ∧ (σ * c3p⁻¹).sign = 1) := by
  decide +kernel

theorem isUniqueMaxOver_of_card_three {G : Type*} [Group G] [Finite G] {W T : Subgroup G}
    (hTW : T ≤ W) (hcard : Nat.card ↥W = 3 * Nat.card ↥T) : IsUniqueMaxOver W T T := by
  have hT0 : 0 < Nat.card ↥T := Nat.card_pos
  have hdich : ∀ K : Subgroup G, T ≤ K → K ≤ W → K = T ∨ K = W := by
    intro K hTK hKW
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hTK
    have h1 := Subgroup.card_dvd_of_le hKW
    rw [hm, hcard, mul_comm 3] at h1
    have h2 : m ∣ 3 := Nat.dvd_of_mul_dvd_mul_left hT0 h1
    rcases (Nat.dvd_prime Nat.prime_three).1 h2 with rfl | rfl
    · left
      exact (Subgroup.eq_of_le_of_card_ge hTK (by rw [hm, mul_one])).symm
    · right
      exact Subgroup.eq_of_le_of_card_ge hKW (by rw [hm, hcard, mul_comm])
  have hTlt : T < W := by
    refine lt_of_le_of_ne hTW fun h => ?_
    have h1 : Nat.card ↥T = Nat.card ↥W := by rw [h]
    omega
  ext N
  simp only [maxOver, IsMaxSubgroupIn, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hNlt, -⟩, hTN⟩
    rcases hdich N hTN hNlt.le with h | h
    · exact h
    · exact absurd h hNlt.ne
  · rintro rfl
    refine ⟨⟨hTlt, fun K hTK hKW => ?_⟩, le_rfl⟩
    rcases hdich K hTK.le hKW with h | h
    · exact absurd h hTK.ne'
    · exact h

theorem lieModel_of_alternating_five {X : Type} [Group X]
    (e : X ≃* alternatingGroup (Fin 5)) : LieModel X .PSL 2 2 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl (by rw [hK]; norm_num))
  exact Or.inl ⟨by decide, ⟨Nat.prime_two, by norm_num, by decide⟩, GaloisField 2 2,
    inferInstance, inferInstance, hK, ⟨e.trans e5.symm⟩⟩

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem mem_pCoreOf_of_mem_pPrimeCore {H : Subgroup G}
    (htriple : F6.IsGoldschmidtTripleIn (S.H0 H) (S.L1 ⊔ T) H) {x : ↥(S.H0 H)}
    (hx : x ∈ CFSG.pPrimeCore 3 ↥(S.H0 H)) {b : ℕ} (hxb : x ^ 2 ^ b = 1) :
    (x : G) ∈ pCoreOf 2 (S.H0 H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsylO := htriple.isSylowTwoOf_pCore_pPrimeCore
  set O' := CFSG.Open.pCore 2 ↥(S.H0 H) with hO'
  have hO'n : O'.Normal := inferInstance
  have hx2 : IsPGroup 2 ↥(Subgroup.zpowers x) := by
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hxb)
    refine IsPGroup.of_card (n := c) ?_
    rw [Nat.card_zpowers, hc]
  have hP : IsPGroup 2 ↥(Subgroup.zpowers x ⊔ O') :=
    IsPGroup.to_sup_of_normal_right hx2 hsylO.2.1
  have hmax := (A4.isSylowTwoOf_iff_maximal.mp hsylO).2.2 (Subgroup.zpowers x ⊔ O')
    (sup_le ((Subgroup.zpowers_le).mpr hx) hsylO.1) hP le_sup_right
  exact ⟨x, hmax (Subgroup.mem_sup_left (Subgroup.mem_zpowers x)), rfl⟩

theorem exists_d_mem_M (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h5172 : Stmt5_1_7_two) (h311 : Theorem311Stmt) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    (hO2 : pCoreOf 2 (S.H0 H) ≠ ⊥) (h3 : ¬ ThreeTop (S.H0 H))
    {K Zc : Subgroup (↥(S.H0 H) ⧸ CFSG.pPrimeCore 3 ↥(S.H0 H))} (hc : S.Case3 H K Zc)
    {F : ↥(S.H0 H) →* Equiv.Perm (Fin 3)}
    (hF1 : ∀ g : ↥(S.H0 H), F g = 1 ↔ (g : G) ∈ Subgroup.centralizer (S.UH H : Set G))
    (hFs : Function.Surjective F) {L' : Subgroup ↥(S.H0 H)}
    (hL'K : L'.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H))) = K)
    (hL'U : L'.map (S.H0 H).subtype ≤ Subgroup.centralizer (S.UH H : Set G)) :
    ∃ d : ↥(S.H0 H), F d ≠ 1 ∧ F d ^ 3 = 1 ∧ (d : G) ∈ Subgroup.normalizer (L : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M := Subgroup.normalizer (L : Set G) with hM
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)) with hπ
  have hTH : T ≤ H := hH.1.1
  have hTI : T ≤ S.H0 H := hTH.trans le_sup_right
  have htriple := S.triple_of h331 h1222 h5172 hH hHZ hsolv hS3 h3
  have hN3s : Group.IsSolvable ↥(CFSG.pPrimeCore 3 ↥(S.H0 H)) := htriple.isSolvable_pPrimeCore
  have hZn := S.normal_Zc hTH hc
  have hsylI : IsSylowTwoOf T (S.H0 H) := isSylowTwoOf_of_le S.h13.sylow hTI
  have hTt : IsSylowTwoOf (T.subgroupOf (S.H0 H)) ⊤ := by
    refine ⟨le_top, A4.isPGroup_subgroupOf_of_le hTI S.isPGroup_T, ?_⟩
    show ¬ 2 ∣ (T.subgroupOf (S.H0 H)).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hsylI.2.2
  have hTb2 : IsPGroup 2 ↥((T.subgroupOf (S.H0 H)).map π) := hTt.2.1.map π
  obtain ⟨W', hTW', hW'card, hW'Y, hW's⟩ :=
    exists_W hN3s CFSG.pPrimeCore_coprime_card hTt hZn hc.card_Zc
  have hodd : ∀ w ∈ W', Odd (orderOf w) → π w ∈ Zc := fun w hw hwo =>
    mem_of_odd_of_mem_sup_normal hZn hTb2 (hW'Y hw) (Odd.of_dvd_nat hwo (orderOf_map_dvd π w))
  have h3W' : 3 ∣ Nat.card ↥W' := by rw [hW'card]; exact Dvd.intro _ rfl
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3W'
  set d : ↥(S.H0 H) := (x : ↥(S.H0 H)) with hd
  have hdo : orderOf d = 3 := by rw [hd, Subgroup.orderOf_coe, hx]
  have hd3 : d ^ 3 = 1 := by rw [← hdo]; exact pow_orderOf_eq_one d
  have hπd : π d ∈ Zc := hodd d x.2 (by rw [hdo]; decide)
  have hπd1 : π d ≠ 1 := by
    intro h
    have hdN : d ∈ CFSG.pPrimeCore 3 ↥(S.H0 H) := (QuotientGroup.eq_one_iff d).mp h
    have h1 : orderOf (⟨d, hdN⟩ : ↥(CFSG.pPrimeCore 3 ↥(S.H0 H))) ∣
        Nat.card ↥(CFSG.pPrimeCore 3 ↥(S.H0 H)) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hdo] at h1
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card h1
  have hFd1 : F d ≠ 1 := S.F0_ne_one_of_map_mem_Zc hH hHZ hc hF1 hFs hL'K hL'U hπd hπd1
  have hFd3 : F d ^ 3 = 1 := by rw [← map_pow, hd3, map_one]
  refine ⟨d, hFd1, hFd3, ?_⟩
  obtain ⟨t₀, ht₀, hFt₀⟩ := S.exists_T_F0_ne_one h331 h1222 hH hHZ hsolv hS3 hF1
  have hdZ := S.not_mem_centralizer_Z_of_F0 hHZ hF1 ht₀ hFt₀ hFd1 hFd3
  by_contra hdM
  set W := W'.map (S.H0 H).subtype with hW
  have hWI : W ≤ S.H0 H := Subgroup.map_subtype_le W'
  have hTW : T ≤ W := fun t ht => ⟨⟨t, hTI ht⟩, hTW' (show _ ∈ T.subgroupOf (S.H0 H) from ht), rfl⟩
  have hWcard : Nat.card ↥W = 3 * Nat.card ↥T := by
    rw [Subgroup.card_map_of_injective (S.H0 H).subtype_injective, hW'card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTI).toEquiv]
  have hdW : (d : G) ∈ W := ⟨d, x.2, rfl⟩
  have hWs : Group.IsSolvable ↥W := by
    have e := (W'.equivMapOfInjective (S.H0 H).subtype (S.H0 H).subtype_injective).symm
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  obtain ⟨⟨j, hjJ, hjN, hj⟩, -⟩ :=
    S.lemma_13_2_4_two_b (S.thompsonJ_not_le_centralizer h5172 hH hHZ)
  have hjT : j ∈ T := thompsonJ_le_self T hjJ
  have hOR : pCoreOf 2 (S.H0 H) ≤ S.R1 := S.pCoreOf_H0_le_R1 hTH hjT hjN hj
  have hOT : pCoreOf 2 (S.H0 H) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsylI
  have hO2W : ∀ k ∈ oTwoUpper W, (∃ b : ℕ, k ^ 2 ^ b = 1) →
      k ∈ pCoreOf 2 (S.H0 H) := by
    have hle : oTwoUpper W ≤ (Zc.comap π).map (S.H0 H).subtype := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro w ⟨hwW, hwo⟩
      obtain ⟨w', hw', rfl⟩ := hwW
      refine ⟨w', hodd w' hw' ?_, rfl⟩
      rwa [show orderOf ((S.H0 H).subtype w') = orderOf w' from Subgroup.orderOf_coe w'] at hwo
    rintro k hk ⟨b, hb⟩
    obtain ⟨k', hk', rfl⟩ := hle hk
    have hk'b : k' ^ 2 ^ b = 1 := Subtype.ext (by simpa using hb)
    have hπk : π k' = 1 := by
      have h1 : π k' ^ 2 ^ b = 1 := by rw [← map_pow, hk'b, map_one]
      have h2 : π k' ^ 3 = 1 := by
        have h4 := pow_card_eq_one' (G := ↥Zc) (x := ⟨π k', hk'⟩)
        rw [hc.card_Zc] at h4
        simpa using congrArg Subtype.val h4
      exact eq_one_of_pow_coprime h1 h2 (Nat.Coprime.pow_left b (by norm_num))
    exact S.mem_pCoreOf_of_mem_pPrimeCore htriple ((QuotientGroup.eq_one_iff k').mp hπk) hk'b
  set X := oTwoUpper W ⊔ S.R1 with hXdef
  have hR1T : S.R1 ≤ T := S.R1_le_T
  have hR12 : IsPGroup 2 ↥S.R1 := S.isPGroup_T.to_le hR1T
  have hR1N : S.R1 ≤ Subgroup.normalizer (oTwoUpper W : Set G) :=
    (hR1T.trans hTW).trans (le_normalizer_oTwoUpper W)
  have hsylX : IsSylowTwoOf S.R1 X :=
    isSylowTwoOf_sup_of_two_elements hR12 hR1N fun k hk hk2 => hOR (hO2W k hk hk2)
  have hXW : X ≤ W := sup_le (oTwoUpper_le W) (hR1T.trans hTW)
  have hXI : X ≤ S.H0 H := hXW.trans hWI
  have hdodd : Odd (orderOf (d : G)) := by
    rw [Subgroup.orderOf_coe, hdo]
    decide
  have hdO : (d : G) ∈ oTwoUpper W := mem_oTwoUpper_of_odd hdW hdodd
  have hdX : (d : G) ∈ X := Subgroup.mem_sup_left hdO
  have hXM : ¬ X ≤ M := fun h => hdM (h hdX)
  have hR10 : 0 < Nat.card ↥S.R1 := Nat.card_pos
  obtain ⟨k', hk'⟩ := Subgroup.card_dvd_of_le hsylX.1
  have hk'odd : ¬ 2 ∣ k' := by
    intro h2
    apply hsylX.2.2
    have h1 := (S.R1.subgroupOf X).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsylX.1).toEquiv, hk'] at h1
    have h1' := Nat.eq_of_mul_eq_mul_left hR10 h1
    rw [h1']
    exact h2
  have hk'3 : k' ∣ 3 := by
    have h1 := Subgroup.card_dvd_of_le hXW
    rw [hk', hWcard] at h1
    obtain ⟨a, ha⟩ := S.isPGroup_T.exists_card_eq
    rw [ha] at h1
    have h2 : k' ∣ 3 * 2 ^ a := (Dvd.intro_left _ rfl).trans h1
    have hco : Nat.Coprime k' (2 ^ a) :=
      Nat.Coprime.pow_right a (Nat.coprime_comm.mp (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr
        (Nat.two_dvd_ne_zero.mp hk'odd))))
    exact hco.dvd_of_dvd_mul_right h2
  have hmin : ∀ Y : Subgroup G, S.R1 ≤ Y → Y < X → Y ≤ M := by
    intro Y hR1Y hYX
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hR1Y
    have h1 := Subgroup.card_dvd_of_le hYX.le
    rw [hm, hk'] at h1
    have hmk : m ∣ k' := Nat.dvd_of_mul_dvd_mul_left hR10 h1
    have hm3 : m ∣ 3 := hmk.trans hk'3
    rcases (Nat.dvd_prime Nat.prime_three).1 hm3 with rfl | rfl
    · have : Y = S.R1 := (Subgroup.eq_of_le_of_card_ge hR1Y (by rw [hm, mul_one])).symm
      rw [this]
      exact hR1T.trans S.T_le_NL
    · exfalso
      have hk'3' : k' = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).1 hk'3 with h | h
        · rw [h] at hmk
          exact absurd (Nat.le_of_dvd one_pos hmk) (by norm_num)
        · exact h
      exact hYX.ne (Subgroup.eq_of_le_of_card_ge hYX.le (by rw [hm, hk', hk'3']))
  have hInI : InH T (S.H0 H) := ⟨hTI, hO2⟩
  have hFX : CharTwo X := by
    have hOX : pCoreOf 2 (S.H0 H) ≤ pCoreOf 2 X :=
      le_pCoreOf_of_le_normalizer (hOR.trans le_sup_right)
        (hXI.trans (le_normalizer_pCoreOf 2 (S.H0 H))) (pCoreOf_isPGroup 2 (S.H0 H))
    rintro x ⟨hxX, hxC⟩
    exact hOX (S.charTwo_of_inH hInI ⟨hXI hxX, Subgroup.centralizer_le hOX hxC⟩)
  have hXZ : ¬ X ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := fun h => hdZ (h hdX)
  have hsolvX : Group.IsSolvable ↥X :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hXW)
  have hSQTI : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (S.H0 H) ≤ 2 := by
    obtain ⟨-, hq⟩ := isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian hInI
    intro q hq' hq2
    have : Fact q.Prime := ⟨hq'⟩
    have h1 := hq q hq' hq2
    rwa [← pRank_top_subtype]
  have hSQTX : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q X ≤ 2 := fun q hq hq2 =>
    (CFSG.SectionRank.pRank_mono hq.one_lt hXI).trans (hSQTI q hq hq2)
  have hPX : oTwoUpper W ⊓ T ≤ oTwoUpper X := by
    refine inf_le_left.trans ((Subgroup.closure_le _).mpr fun w hw => ?_)
    exact mem_oTwoUpper_of_odd (Subgroup.mem_sup_left (Subgroup.subset_closure hw)) hw.2
  have hPR : oTwoUpper W ⊓ T ≤ S.R1 := by
    rintro k ⟨hk, hkT⟩
    obtain ⟨b, hb⟩ := S.isPGroup_T ⟨k, hkT⟩
    exact hOR (hO2W k hk ⟨b, by simpa using congrArg Subtype.val hb⟩)
  have hH' : InH T W := by
    refine ⟨hTW, fun h => hO2 (eq_bot_iff.mpr ?_)⟩
    rw [← h]
    exact le_pCoreOf_of_le_normalizer (hOT.trans hTW)
      (hWI.trans (le_normalizer_pCoreOf 2 (S.H0 H))) (pCoreOf_isPGroup 2 (S.H0 H))
  have h2 : ∀ k ∈ oTwoUpper W, (∃ b : ℕ, k ^ 2 ^ b = 1) → k ∈ oTwoUpper W ⊓ T :=
    fun k hk hk2 => ⟨hk, hOT (hO2W k hk hk2)⟩
  have hWM := S.le_M_of_minParabolic h311 hsylX hXM hmin hFX hXZ hsolvX hSQTX hPX hPR hH'
    ⟨T, isUniqueMaxOver_of_card_three hTW hWcard⟩ h2
  exact hdM (hWM hdW)

theorem pCoreOf_L_le_centralizer_UH {H : Subgroup G} (hTH : T ≤ H)
    {F : ↥(S.H0 H) →* Equiv.Perm (Fin 3)}
    (hF1 : ∀ g : ↥(S.H0 H), F g = 1 ↔ (g : G) ∈ Subgroup.centralizer (S.UH H : Set G))
    {d : ↥(S.H0 H)} (hFd1 : F d ≠ 1) (hFd3 : F d ^ 3 = 1)
    (hdM : (d : G) ∈ Subgroup.normalizer (L : Set G)) :
    pCoreOf 2 L ≤ T ⊓ Subgroup.centralizer (S.UH H : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTI : T ≤ S.H0 H := hTH.trans le_sup_right
  have hOLT : pCoreOf 2 L ≤ T := by
    refine le_trans ?_ S.pCoreOf_LT_le_T
    refine le_pCoreOf_of_le_normalizer ((pCoreOf_le 2 L).trans le_sup_left) ?_
      (pCoreOf_isPGroup 2 L)
    exact sup_le (le_normalizer_pCoreOf 2 L)
      (S.T_le_NL.trans (normalizer_le_normalizer_pCoreOf 2 L))
  intro u hu
  have huT : u ∈ T := hOLT hu
  refine ⟨huT, ?_⟩
  set u' : ↥(S.H0 H) := ⟨u, hTI huT⟩ with hu'
  have hc : ((u' * d * u'⁻¹ * d⁻¹ : ↥(S.H0 H)) : G) ∈ pCoreOf 2 L := by
    have h1 : (d : G) * u⁻¹ * (d : G)⁻¹ ∈ pCoreOf 2 L :=
      (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_pCoreOf 2 L hdM) _).mp
        ((pCoreOf 2 L).inv_mem hu)
    have e : ((u' * d * u'⁻¹ * d⁻¹ : ↥(S.H0 H)) : G) = u * ((d : G) * u⁻¹ * (d : G)⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hu']
      group
    rw [e]
    exact (pCoreOf 2 L).mul_mem hu h1
  obtain ⟨b, hb⟩ := pCoreOf_isPGroup 2 L ⟨_, hc⟩
  have hcb : (u' * d * u'⁻¹ * d⁻¹) ^ 2 ^ b = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hb)
  have hFc2 : (F u' * F d * (F u')⁻¹ * (F d)⁻¹) ^ 2 ^ b = 1 := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_pow, hcb, map_one]
  have hFc3 : (F u' * F d * (F u')⁻¹ * (F d)⁻¹) ^ 3 = 1 := by
    refine perm3_cube_mul _ _ ?_ ?_
    · rw [conj_pow, hFd3]
      group
    · rw [inv_pow, hFd3, inv_one]
  have hFc : F u' * F d * (F u')⁻¹ * (F d)⁻¹ = 1 :=
    eq_one_of_pow_coprime hFc2 hFc3 (Nat.Coprime.pow_left b (by norm_num))
  have hcomm : F u' * F d = F d * F u' := by
    have := congrArg (· * (F d * F u')) hFc
    simp only [one_mul] at this
    rw [← this]
    group
  have hFu2 : F u' ^ 2 = 1 := by
    obtain ⟨b', hb'⟩ := S.isPGroup_T ⟨u, huT⟩
    refine perm3_sq_of_two_pow (k := b') ?_
    rw [← map_pow]
    have : u' ^ 2 ^ b' = 1 := Subtype.ext (by simpa using congrArg Subtype.val hb')
    rw [this, map_one]
  exact (hF1 u').1 (perm3_comm _ _ hcomm hFu2 hFd3 hFd1)

theorem T_inf_L_le_pCoreOf (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    (hL1 : S.L1 ≤ Subgroup.centralizer (S.UH H : Set G))
    (hOL : pCoreOf 2 L ≤ T ⊓ Subgroup.centralizer (S.UH H : Set G)) :
    T ⊓ L ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hH.1.1
  rintro t ⟨htT, htL⟩
  refine S.centralizer_UH_le_pCoreOf h331 h1222 hH hHZ hsolv hS3 ⟨hTH htT, ?_⟩
  set t' : ↥(Subgroup.normalizer (V : Set G)) := ⟨t, S.frame.T_le htT⟩ with ht'
  have h4 : S.frame.ρ t' 4 = 4 := S.rho_four_of_mem_L1T (Subgroup.mem_sup_right htT)
  have hsg : (S.frame.ρ t').sign = 1 := (S.frame.image_L _).1 ⟨t', htL, rfl⟩
  obtain ⟨g, hgL1, hg⟩ : ∃ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ S.L1 ∧
      S.frame.ρ g = S.frame.ρ t' := by
    rcases A4_cube_or _ h4 hsg with h | ⟨h3, h4', hs'⟩
    · exact S.exists_L1_of_three hsg h4 h
    · obtain ⟨g₁, hg₁L, hg₁⟩ := S.exists_L1_of_three hs' h4' h3
      obtain ⟨g₂, hg₂L, hg₂⟩ := S.exists_L1_c3p
      refine ⟨g₁ * g₂, S.L1.mul_mem hg₁L hg₂L, ?_⟩
      rw [map_mul, hg₁, hg₂, inv_mul_cancel_right]
  have hc1 : S.frame.ρ (g⁻¹ * t') = 1 := by rw [map_mul, map_inv, hg, inv_mul_cancel]
  have hcV : ((g⁻¹ * t' : ↥(Subgroup.normalizer (V : Set G))) : G) ∈
      Subgroup.centralizer (V : Set G) := S.frame.mem_centralizer_of_rho _ hc1
  have hgL : (g : G) ∈ L := S.L1_le_L hgL1
  have hcL : ((g⁻¹ * t' : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ L := by
    show (g : G)⁻¹ * t ∈ L
    exact L.mul_mem (L.inv_mem hgL) htL
  have hcO : ((g⁻¹ * t' : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ pCoreOf 2 L := by
    have hLQ : L ⊓ pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 L := by
      refine le_pCoreOf_of_le_normalizer inf_le_left ?_
        ((pCoreOf_isPGroup 2 (L ⊔ T)).to_le inf_le_right)
      intro l hl
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hl, le_normalizer_pCoreOf 2 (L ⊔ T) (Subgroup.mem_sup_left hl)⟩
    refine hLQ ⟨hcL, ?_⟩
    rw [← S.cLT]
    exact ⟨Subgroup.mem_sup_left hcL, hcV⟩
  have e : t = (g : G) * ((g⁻¹ * t' : ↥(Subgroup.normalizer (V : Set G))) : G) := by
    simp [ht']
  rw [e]
  exact Subgroup.mul_mem _ (hL1 hgL1) (hOL hcO).2

theorem false_of_T_inf_L_le (h432 : Stmt4_3_2) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H) (hTL : T ⊓ L ≤ pCoreOf 2 H) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hH.1.1
  have hlie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 2 := by
    obtain ⟨φ, hφ, hker⟩ := S.a5
    have hker' : φ.ker = CFSG.pCore 2 ↥L := by
      rw [hker]
    exact lieModel_of_alternating_five ((QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ))
  have hOT : pCoreOf 2 H ≤ T :=
    pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le S.h13.sylow hTH)
  have hinf : pCoreOf 2 H ⊓ L = T ⊓ L :=
    le_antisymm (inf_le_inf_right L hOT) (le_inf hTL inf_le_right)
  have hsyl : IsSylowTwoOf (pCoreOf 2 H ⊓ L) L := hinf ▸ S.sylow_inf_L
  have hN := (h432 G T (Subgroup.normalizer (L : Set G)) L S.h13.simple S.h13.nonabelian
    S.h13.qtke S.h13.sylow S.uniqueM.1.1 S.T_le_NL S.maximal S.h13.faithful
    Subgroup.le_normalizer le_rfl ⟨2, le_rfl, hlie⟩).2 (pCoreOf 2 H) hOT hsyl
  exact hH.2.1 ((le_normalizer_pCoreOf 2 H).trans hN)

theorem false_of_case3 (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h5172 : Stmt5_1_7_two) (h311 : Theorem311Stmt) (h432 : Stmt4_3_2) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    (hO2 : pCoreOf 2 (S.H0 H) ≠ ⊥) (h3 : ¬ ThreeTop (S.H0 H))
    {K Zc : Subgroup (↥(S.H0 H) ⧸ CFSG.pPrimeCore 3 ↥(S.H0 H))} (hc : S.Case3 H K Zc) :
    False := by
  have hTH : T ≤ H := hH.1.1
  have htriple := S.triple_of h331 h1222 h5172 hH hHZ hsolv hS3 h3
  have hN3s := htriple.isSolvable_pPrimeCore
  obtain ⟨L', hL', hL'K, hL'n, hZL'⟩ := S.exists_L0 hH hO2 hN3s hc
  obtain ⟨r, hr, z₀, hz₀, hrz⟩ := S.exists_R1_not_comm h331 h311 hH hHZ hsolv hS3 hc
  have hL1L0 : S.L1 ≤ L'.map (S.H0 H).subtype :=
    S.L1_le_of_map hN3s hL' fun l hl => hL'K ▸ S.map_L1_le_K hTH hc hr hz₀ hrz hl
  have hL0U := S.le_centralizer_UH_of_normal hL'n hZL'
  have hL1U := hL1L0.trans hL0U
  obtain ⟨F, hF1, hFs⟩ := S.exists_F0 hH hS3 hL1U
  obtain ⟨d, hFd1, hFd3, hdM⟩ :=
    S.exists_d_mem_M h331 h1222 h5172 h311 hH hHZ hsolv hS3 hO2 h3 hc hF1 hFs hL'K hL0U
  have hOL := S.pCoreOf_L_le_centralizer_UH hTH hF1 hFd1 hFd3 hdM
  exact S.false_of_T_inf_L_le h432 hH (S.T_inf_L_le_pCoreOf h331 h1222 hH hHZ hsolv hS3 hL1U hOL)

end Setting

theorem final1327CaseThree_of (h331 : Stmt3_3_1)
    (h1222 : Stmt12_2_2) (h5172 : Stmt5_1_7_two) (h311 : Theorem311Stmt) (h432 : Stmt4_3_2)
    (hL2 : FactL2Three) : Final1327CaseThree := by
  intro G _ _ T L V S H hH hHZ hsolv hS3 hO2 h3 hcase
  obtain ⟨K, Zc, hc⟩ := S.case3_of hL2 (Or.inl hcase)
  exact S.false_of_case3 h331 h1222 h5172 h311 h432 hH hHZ hsolv hS3 hO2 h3 hc

theorem final1327_of_facts (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h5172 : Stmt5_1_7_two) (h311 : Theorem311Stmt) (h432 : Stmt4_3_2)
    (hF618 : F6.TheoremF618Cat) (hBig : FactF618Big) (hL2 : FactL2Three) : Final1327 :=
  final1327_of h331 h1222 h5172 h311 hF618 hBig
    (final1327CaseThree_of h331 h1222 h5172 h311 h432 hL2)

theorem stmt13_2_7_of_caseS2_ofNoN
    (h331 : Stmt3_3_1) (h311 : Theorem311Stmt) (h432 : Stmt4_3_2) (h523 : Stmt5_2_3)
    (h1222 : Stmt12_2_2) (h5172 : Stmt5_1_7_two) (hE22 : E2.E22StatementNoN) (hRes : Res1328a)
    (hF618 : F6.TheoremF618Cat) (hBig : FactF618Big) (hL2 : FactL2Three) (hS2 : CaseS2_1327) :
    Stmt13_2_7 :=
  stmt13_2_7_of_rest_ofNoN h331 h311 h523 h1222 h5172 hE22 hRes hS2
    (final1327_of_facts h331 h1222 h5172 h311 h432 hF618 hBig hL2)

end CFSG.Quasithin.H13.A5
