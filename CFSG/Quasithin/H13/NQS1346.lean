module

public import CFSG.Quasithin.H13.NQS1345
public import CFSG.Quasithin.H13.A6S1322
public import CFSG.Quasithin.H13.NQS134Defs2
public import CFSG.Quasithin.H13.U3S1344A

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem oTwoRes_oTwoRes_eq (X : Subgroup G) : oTwoRes (oTwoRes X) = oTwoRes X := by
  rw [oTwoRes_eq_oTwoUpper, oTwoRes_eq_oTwoUpper, A4.oTwoUpper_oTwoUpper]

theorem isCyclic_of_pRank_three_le_one {X C : Subgroup G} (hX : IsPGroup 3 X) (hXC : X ≤ C)
    (hr : CFSG.pRank 3 ↥C ≤ 1) : IsCyclic ↥X := by
  by_contra hnc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, pRank_top_subtype] at hr
  have : Fact (IsPGroup 3 ↥X) := ⟨hX⟩
  obtain ⟨S, -, hS, hSe⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hnc
  have hSe' := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 S).1 hSe
  have h2 := CFSG.SectionRank.le_pRank (p := 3) (by norm_num)
    (show S.map X.subtype ≤ C from (map_subtype_le S).trans hXC)
    (CFSG.SectionRank.isElemAbelian_map hSe' _)
    (show Nat.card ↥(S.map X.subtype) = 3 ^ 2 by
      rw [card_map_of_injective X.subtype_injective, hS])
  omega

omit [Finite G] in
theorem pCoreOf_centralizer_ne_bot {z : G} (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) :
    pCoreOf 2 (centralizer ({z} : Set G)) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  have hzmem : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have hp : IsPGroup 2 (zpowers z) := by
    have hc : Nat.card (zpowers z) = 2 ^ 1 := by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime hz2 hz1
    exact IsPGroup.of_card hc
  have hN : centralizer ({z} : Set G) ≤ normalizer ((zpowers z : Subgroup G) : Set G) := by
    intro y hy
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    exact ((Commute.zpow_left (mem_centralizer_singleton_iff.mp hy).symm k).symm).eq.symm
  have hle : zpowers z ≤ pCoreOf 2 (centralizer ({z} : Set G)) :=
    le_pCoreOf_of_le_normalizer 2 (zpowers_le.mpr hzmem) hN hp
  rw [hbot, le_bot_iff, zpowers_eq_bot] at hle
  exact hz1 hle

theorem comm_J_of (hC58 : TheoremC58) (h317 : AS317Sylow) (h1332 : Stmt13_3_2)
    (S : A6.Setting134 G T L V) {K : Subgroup G} (hKf : quasithinIsFaithfulLocal T K)
    {z : G} (hzZ : z ∈ quasithinOmegaOneCenter T)
    (hGzK : centralizer ({z} : Set G) ≤ normalizer (K : Set G))
    (hLK : ¬ L ≤ normalizer (K : Set G)) : ⁅K, thompsonJ T⁆ = K := by
  obtain ⟨-, ⟨hTK, -, hNKmax, huniq⟩, ⟨⟨VK, hVK⟩, hall⟩, -⟩ := h1332 G T L S.h13 K hKf
  obtain ⟨-, -, hfsu, -⟩ := hall VK hVK
  have hKc : K ∈ cComp (K ⊔ T) := hKf.1.2.1
  have hTKsyl : IsSylowTwoOf T (K ⊔ T) := ⟨le_sup_right, hKf.1.1, hKf.1.2.2.1⟩
  have hred := twoReduced_R2 (K ⊔ T)
  have hKR : ¬ K ≤ centralizer (reducedAggregate (K ⊔ T) : Set G) := by
    intro hle
    have hVc : K ≤ centralizer (VK : Set G) :=
      hle.trans (centralizer_le (SetLike.coe_subset_coe.mpr hVK.1))
    have h1 : ⁅VK, K⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hVc)
    exact hVK.2.1 (hVK.2.2.2.1.symm.trans h1)
  have hqo : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) :=
    A3.isQuasisimple_iff_open.1 (CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (A3.pCore_eq_openCore 2 ↥K)) hfsu.quasisimple)
  have hcen := (Ch3Sec3.centralizer_reduced_of_cComp hKc hqo hTKsyl hred hKR).2.1
  have hLTK : ¬ L ⊔ T ≤ normalizer (K : Set G) := fun h => hLK (le_sup_left.trans h)
  obtain ⟨H₀, hH₀, -⟩ := A5.exists_isHStar_le' (⟨le_sup_right, S.h13.faithful.1.2.2.2⟩ :
    InH T (L ⊔ T)) hLTK
  have h318 : Hyp318 T (normalizer (K : Set G)) K (reducedAggregate (K ⊔ T)) :=
    { inM := ⟨hNKmax, hTK⟩
      nonempty := ⟨H₀, hH₀⟩
      perfect := eq_oTwoUpper_of_perfect (perfect_of_mem_cComp hKc)
      le_M := le_normalizer
      normal := le_rfl
      unique := ⟨⟨hNKmax, sup_le le_normalizer hTK⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩
      reduced := hred
      centralizer := hcen.symm }
  rcases theorem318_three hC58 h317 S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow h318
    with ⟨hJ, -⟩ | ⟨-, hZ, -⟩
  · refine U3.comm_thompsonJ_eq_of_not_le hTKsyl hKc hfsu.quasisimple hTK fun hle => hJ ?_
    rw [← h318.centralizer]
    exact hle
  · exfalso
    apply hH₀.2.1
    refine le_trans (fun h hh => ?_) hGzK
    rw [mem_centralizer_singleton_iff]
    have hzc := (mem_inf.1 (hZ H₀ hH₀ hzZ)).2
    exact mem_centralizer_iff.mp hzc h hh

theorem four_of (h1222 : Stmt12_2_2) (h1338 : A6.Stmt13_3_8) (h1337 : A6.Stmt13_3_7)
    (S : A6.Setting134 G T L V) {K : Subgroup G} (hKf : quasithinIsFaithfulLocal T K)
    {z : G} (hzV : z ∈ V) (hGzK : centralizer ({z} : Set G) ≤ normalizer (K : Set G))
    (hLK : ¬ L ≤ normalizer (K : Set G)) :
    normalizer (L : Set G) = L ⊔ T ∨
      (A6.IsHatA6 L ∧ ∃ X : Subgroup G, IsCyclic ↥X ∧
        IsSylowIn 3 X (normalizer (L : Set G) ⊓ centralizer (V : Set G)) ∧
        normalizer (L : Set G) = (L ⊔ X) ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M := normalizer (L : Set G) with hMdef
  set P := M ⊓ centralizer (V : Set G) with hPdef
  have hMV : M ≤ normalizer (V : Set G) := S.normalizer_L_le h1222
  have hLTM : L ⊔ T ≤ M := sup_le le_normalizer S.T_le_NL
  have hPM : P ≤ M := inf_le_left
  have hMP : M ≤ normalizer (P : Set G) := fun m hm =>
    inf_normalizer_le_normalizer_inf ⟨le_normalizer hm, U3.mem_normalizer_centralizer_of (hMV hm)⟩
  have hMLTP : M ≤ (L ⊔ T) ⊔ P := by
    intro m hm
    obtain ⟨h, hh, hact⟩ := S.exists_act_eq ⟨m, hMV hm⟩
    have hhm : h⁻¹ * m ∈ P := by
      refine mem_inf.mpr ⟨mul_mem (inv_mem (hLTM hh)) hm, mem_centralizer_iff.mpr fun v hv => ?_⟩
      have h1 : m * v * m⁻¹ = h * v * h⁻¹ := hact v hv
      calc v * (h⁻¹ * m) = h⁻¹ * (h * v * h⁻¹) * m := by group
        _ = h⁻¹ * (m * v * m⁻¹) * m := by rw [h1]
        _ = h⁻¹ * m * v := by group
    have e : m = h * (h⁻¹ * m) := by group
    rw [e]
    exact mul_mem (le_sup_left (b := P) hh) (le_sup_right (a := L ⊔ T) hhm)
  set Y := oTwoRes P with hYdef
  have hYP : Y ≤ P := oTwoRes_le P
  have hMY : M ≤ normalizer (Y : Set G) := A5.le_normalizer_oTwoRes_of_le_normalizer hMP
  have hYK : Y ≤ normalizer (K : Set G) :=
    (hYP.trans inf_le_right).trans ((centralizer_le (by simpa using hzV)).trans hGzK)
  have hVM : V ≤ pCoreOf 2 M :=
    le_pCoreOf_of_le_normalizer 2 (S.V_le_T.trans S.T_le_NL) hMV S.isPGroup_V
  have hInHM : InH T M := ⟨S.T_le_NL, fun h => S.irr.2.1 (le_bot_iff.mp (h ▸ hVM))⟩
  have hMK : ¬ M ≤ normalizer (K : Set G) := fun h => hLK (le_normalizer.trans h)
  have h23 : A6.IsTwoThreeGroup Y :=
    (h1338 G T L K M Y S.h13 hKf hInHM hMK (oTwoRes_oTwoRes_eq P) (hYP.trans hPM) hMY hYK).2
  have hTsylM : IsSylowTwoOf T M := A5.isSylowTwoOf_of_le S.h13.sylow S.T_le_NL
  have hTP : IsSylowTwoOf (T ⊓ P) P := A4.isSylowTwoOf_inf_normal hTsylM hPM hMP
  have hPYT : P ≤ Y ⊔ (T ⊓ P) := le_oTwoRes_sup_of_isSylowTwoOf hTP
  have hodd : ∀ x ∈ P, ∀ q : ℕ, q.Prime → q ≠ 2 → orderOf x = q → q = 3 := by
    intro x hx q hq hq2 hxq
    have hxq' : x ^ q = 1 := by rw [← hxq]; exact pow_orderOf_eq_one x
    have hxY : x ∈ Y := subset_closure ⟨hx, q, hq.odd_of_ne_two hq2, hxq'⟩
    have hdvd : q ∣ Nat.card Y := by
      rw [← hxq]
      exact Subgroup.orderOf_dvd_natCard Y hxY
    exact (h23 q hq hdvd).resolve_left hq2
  by_cases h3 : 3 ∣ Nat.card P
  · right
    have h3C : 3 ∣ Nat.card ↥(centralizer (V : Set G)) :=
      h3.trans (card_dvd_of_le inf_le_right)
    obtain ⟨hhat, hr, -⟩ := (h1337 G T L V S.h13 S.irr (U3.s134_isA6On S)).resolve_left
      (not_not_intro h3C)
    obtain ⟨X, hX, -⟩ := exists_isSylowIn_ge 3 (bot_le : (⊥ : Subgroup G) ≤ P) IsPGroup.of_bot
    refine ⟨hhat, X, isCyclic_of_pRank_three_le_one hX.2.1 (hX.1.trans inf_le_right) hr.le,
      hX, le_antisymm ?_ ?_⟩
    ·
      have hPTX : P ≤ (T ⊓ P) ⊔ X := by
        rw [← relIndex_eq_one]
        by_contra hne
        obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
        have hq2 : q ∣ (T ⊓ P).relIndex P := hqd.trans (relIndex_dvd_of_le_left P le_sup_left)
        have hq3 : q ∣ X.relIndex P := hqd.trans (relIndex_dvd_of_le_left P le_sup_right)
        have hqP : q ∣ Nat.card P := hqd.trans (relIndex_dvd_card _ _)
        have : Fact q.Prime := ⟨hq⟩
        obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) q hqP
        by_cases hq2' : q = 2
        · subst hq2'
          exact hTP.2.2 hq2
        · have := hodd x x.2 q hq hq2' (by rw [← Subgroup.orderOf_coe] at hx; exact hx)
          subst this
          exact hX.2.2 hq3
      refine hMLTP.trans (sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
        (hPTX.trans (sup_le (inf_le_left.trans le_sup_right) (le_sup_right.trans le_sup_left))))
    · exact sup_le (sup_le le_normalizer (hX.1.trans hPM)) S.T_le_NL
  · left
    have hY1 : Y = ⊥ := by
      rw [eq_bot_iff, hYdef, oTwoRes, closure_le]
      rintro x ⟨hx, m, hm, hxm⟩
      rw [SetLike.mem_coe, mem_bot]
      by_contra hx1
      have hord : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
      obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hord
      have hoddo : Odd (orderOf x) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hxm)
      have hq2 : q ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.mpr hoddo) (even_iff_two_dvd.mpr hqd)
      have : Fact q.Prime := ⟨hq⟩
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) q
        (hqd.trans (Subgroup.orderOf_dvd_natCard P hx))
      have := hodd y y.2 q hq hq2 (by rw [← Subgroup.orderOf_coe] at hy; exact hy)
      subst this
      exact h3 (hqd.trans (Subgroup.orderOf_dvd_natCard P hx))
    rw [hY1, bot_sup_eq] at hPYT
    exact le_antisymm (hMLTP.trans (sup_le le_rfl (hPYT.trans (inf_le_left.trans le_sup_right))))
      hLTM

theorem stmt13_4_6_of (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h13316 : Stmt13_3_16)
    (h1334 : A6.Stmt13_3_4) (h1337 : A6.Stmt13_3_7) (h1338 : A6.Stmt13_3_8)
    (hC58 : TheoremC58) (h317 : AS317Sylow) : Stmt13_4_6 := by
  intro G _ _ T L V S z H hzV1 hzL hHz hnsolv
  have hH : InH T H := ⟨le_sup_right.trans hHz.1.1, hHz.1.2⟩
  obtain ⟨hex, hall⟩ := stmt13_4_5_of h1332 h13316 h1334 h1338 G T L V S H hH hHz.2.2 hnsolv
  have hzV : z ∈ V := hzV1.1
  have hzZ : z ∈ quasithinOmegaOneCenter T := hzV1.2
  have hz1 : z ≠ 1 := fun h => hzL (h ▸ one_mem _)
  have hz2 : z ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.1 hzZ).2.2
  have hInHGz : InH T (centralizer ({z} : Set G)) :=
    ⟨hH.1.trans hHz.2.1, pCoreOf_centralizer_ne_bot hz1 hz2⟩
  have key : ∀ K ∈ cComp H, quasithinIsFaithfulLocal T K ∧
      K ≤ centralizer ({z} : Set G) ∧ centralizer ({z} : Set G) ≤ normalizer (K : Set G) ∧
      ¬ L ≤ normalizer (K : Set G) := by
    intro K hK
    obtain ⟨⟨-, hKf⟩, -, -, -, hLK, -⟩ := hall K hK
    have hKGz : K ≤ centralizer ({z} : Set G) := (le_of_mem_cComp hK).trans hHz.2.1
    exact ⟨hKf, hKGz, le_normalizer_of_faithful h1332 S hInHGz hKGz hKf, hLK⟩
  refine ⟨hex, fun K hK => ?_, ?_⟩
  · obtain ⟨⟨hKmax, hKf⟩, hHK, -, hKM, hLK, hKZ, -⟩ := hall K hK
    obtain ⟨-, hKGz, hGzK, -⟩ := key K hK
    exact ⟨⟨hKmax, hKf⟩, hHK, hKM, hLK, hKZ, hKGz, hGzK,
      comm_J_of hC58 h317 h1332 S hKf hzZ hGzK hLK⟩
  · obtain ⟨K, hK⟩ := hex
    obtain ⟨hKf, -, hGzK, hLK⟩ := key K hK
    exact four_of h1222 h1338 h1337 S hKf hzV hGzK hLK

end CFSG.Quasithin.H13.NQS134
