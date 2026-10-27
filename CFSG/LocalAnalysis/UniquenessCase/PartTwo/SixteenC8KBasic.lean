module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KSet
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Std
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.Quasithin.H13.GoldschmidtC137SQL32

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem c8k_ne_top (hst : StandingGe3 G) {K : Subgroup G}
    (hK : CFSG.QuasithinUnique.CharTwo K) : K ≠ ⊤ := by
  intro htop
  let N : Subgroup G := CFSG.Open.pCoreOf 2 (⊤ : Subgroup G)
  have hK' : (⊤ : Subgroup G) ⊓ Subgroup.centralizer (N : Set G) ≤ N := by
    have hN : N = CFSG.Open.pCoreOf 2 (⊤ : Subgroup G) := rfl
    rw [hN]
    rw [htop] at hK
    exact hK
  have hcent_le : Subgroup.centralizer (N : Set G) ≤ N :=
    (le_inf le_top le_rfl).trans hK'
  have hNnormal : N.Normal := by
    have hN : N = (CFSG.pCore 2 ↥(⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype := rfl
    rw [hN]
    exact (CFSG.pCore_normal (p := 2) (G := ↥(⊤ : Subgroup G))).map
      (⊤ : Subgroup G).subtype (fun g => ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩)
  have hNp : IsPGroup 2 N := by
    have hN : N = (CFSG.pCore 2 ↥(⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype := rfl
    rw [hN]
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥(⊤ : Subgroup G))).map
      (⊤ : Subgroup G).subtype
  haveI : N.Normal := hNnormal
  rcases hst.simple.eq_bot_or_eq_top_of_normal N with hNbot | hNtop
  · have htop_bot : (⊤ : Subgroup G) ≤ ⊥ := by
      have h1 : (⊤ : Subgroup G) ≤ Subgroup.centralizer (N : Set G) := by
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [hNbot] at hy
        have hy1 : y = 1 := Subgroup.mem_bot.1 (show y ∈ (⊥ : Subgroup G) from hy)
        rw [hy1]
        simp
      have h2 : Subgroup.centralizer (N : Set G) ≤ (⊥ : Subgroup G) := by
        rw [← hNbot]
        exact hcent_le
      exact h1.trans h2
    haveI : Subsingleton G := ⟨fun a b => by
      have ha : a = 1 := Subgroup.mem_bot.1 (htop_bot (Subgroup.mem_top a))
      have hb : b = 1 := Subgroup.mem_bot.1 (htop_bot (Subgroup.mem_top b))
      rw [ha, hb]⟩
    obtain ⟨a, b, hab⟩ := hst.nonab
    exact hab (Subsingleton.elim (a * b) (b * a))
  · have htopP : IsPGroup 2 (⊤ : Subgroup G) := by
      rw [← hNtop]
      exact hNp
    have h2G : IsPGroup 2 G := by
      intro g
      obtain ⟨k, hk⟩ := htopP ⟨g, Subgroup.mem_top g⟩
      exact ⟨k, by simpa using Subtype.ext_iff.mp hk⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnil : Group.IsNilpotent G := IsPGroup.isNilpotent h2G
    haveI : Group.IsNilpotent G := hnil
    have hsol : Group.IsSolvable G := inferInstance
    obtain ⟨a, b, hab⟩ := hst.nonab
    exact hab (hst.simple.comm_iff_isSolvable.2 hsol a b)

theorem c8_d_exists {M L V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {v₀ : IntMod V hV}
    (hLift : barSub V₀ V hV (L ⊓ centralizer ({v₀.val} : Set G)) =
      ptCent (Mbar M V₀ V hV) (mkTil V₀ V hV v₀))
    (he64 : IsE64L3 ↥(ptCent (Mbar M V₀ V hV) (mkTil V₀ V hV v₀))) :
    ∃ d ∈ L ⊓ centralizer ({v₀.val} : Set G), orderOf d = 3 := by
  classical
  let P : Subgroup (MulAut (Vtil V₀ V hV)) :=
    ptCent (Mbar M V₀ V hV) (mkTil V₀ V hV v₀)
  have hP : P = ptCent (Mbar M V₀ V hV) (mkTil V₀ V hV v₀) := rfl
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  haveI : Finite P := inferInstance
  have he64' : IsE64L3 ↥P := by
    rw [hP]
    exact he64
  obtain ⟨N, hN, -, hL⟩ := he64'
  haveI : N.Normal := hN
  have hcard168 : Nat.card (P ⧸ N) = 168 :=
    (CFSG.Quasithin.H13.U3.GC137.SQ.simple_card_of_lieModel_psl_three_two hL).2
  have h3dvd : 3 ∣ Nat.card P := by
    have hd : Nat.card (P ⧸ N) ∣ Nat.card P := Subgroup.card_quotient_dvd_card N
    rw [hcard168] at hd
    exact (by norm_num : 3 ∣ 168).trans hd
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 3 h3dvd
  have hybar : (y : MulAut (Vtil V₀ V hV)) ∈
      barSub V₀ V hV (L ⊓ centralizer ({v₀.val} : Set G)) := by
    rw [hLift]
    show (y : MulAut (Vtil V₀ V hV)) ∈ P
    exact y.2
  obtain ⟨g, hgmem, hgact⟩ := (mem_barSub V₀ V hV _ _).1 hybar
  have h3g : 3 ∣ orderOf (g : G) := by
    have h1 : orderOf (actTil V₀ V hV g) = 3 := by
      rw [hgact, Subgroup.orderOf_coe y]
      exact hy
    have h2 : orderOf (actTil V₀ V hV g) ∣ orderOf g := orderOf_map_dvd _ g
    rw [h1] at h2
    rwa [← Subgroup.orderOf_coe g] at h2
  exact ⟨(g : G) ^ (orderOf (g : G) / 3),
    pow_mem hgmem (orderOf (g : G) / 3),
    orderOf_pow_orderOf_div (orderOf_pos (g : G)).ne' h3g⟩

theorem c8k_d_cent {M K : Subgroup G} (hse : IsStronglyPEmbedded 3 M) {d : ↥K}
    (hd : (d : G) ∈ M) (hd3 : orderOf d = 3) :
    centralizer ({d} : Set ↥K) ≤ (K ⊓ M).subgroupOf K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x hx
  rw [Subgroup.mem_centralizer_iff] at hx
  have hd1 : (d : G) ≠ 1 := by
    intro h
    have hd_eq : d = 1 := Subtype.ext h
    rw [hd_eq, orderOf_one] at hd3
    exact absurd hd3 (by norm_num)
  have hd3' : (d : G) ^ 3 = 1 := by
    have h : d ^ 3 = 1 := by
      rw [← hd3]
      exact pow_orderOf_eq_one d
    simpa using congrArg Subtype.val h
  have hxd : (d : G) * (x : G) = (x : G) * (d : G) := by
    have h := hx d (Set.mem_singleton d)
    simpa using congrArg Subtype.val h
  have hxM : (x : G) ∈ M :=
    CFSG.RankThree.PartOne.IsStronglyPEmbedded.centralizer_le hse hd1 hd3' hd
      (Subgroup.mem_centralizer_iff.2 fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact hxd)
  rw [Subgroup.mem_subgroupOf]
  exact ⟨x.2, hxM⟩

theorem c8k_char2 {K : Subgroup G} (hK : CFSG.QuasithinUnique.CharTwo K) :
    centralizer ((CFSG.pCore 2 ↥K : Subgroup ↥K) : Set ↥K) ≤ CFSG.pCore 2 ↥K := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff] at hx
  have hxK : (x : G) ∈ K ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G) := by
    refine ⟨x.2, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
    rw [CFSG.openPCoreOf_eq_map_pCore] at hz
    obtain ⟨q, hqK, hqz⟩ := Subgroup.mem_map.1 hz
    have hcomm := hx q hqK
    rw [← hqz]
    simpa using congrArg Subtype.val hcomm
  have hxQ : (x : G) ∈ CFSG.Open.pCoreOf 2 K := hK hxK
  rw [← CFSG.openPCoreOf_subgroupOf]
  rw [Subgroup.mem_subgroupOf]
  exact hxQ

theorem c8k_rank (D : Data G) (hx : DataExt D) (hσ3 : SigmaThree D) (hsig : D.sig = {3})
    (hm3 : CFSG.Open.pRank 3 D.M = 3) {K : Subgroup G} (hK : CFSG.QuasithinUnique.CharTwo K) :
    ∀ p : ℕ, p.Prime → 3 < p → pRank p (⊤ : Subgroup ↥K) ≤ 2 := by
  intro p hp hp3
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank p (⊤ : Subgroup ↥K)]
  by_cases hQ : CFSG.Open.pCoreOf 2 K = ⊥
  · have hKbot : K = ⊥ := by
      apply le_bot_iff.1
      have hcent : K ≤ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G) := by
        rw [hQ]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hy1 : y = 1 := Subgroup.mem_bot.1 (show y ∈ (⊥ : Subgroup G) from hy)
        rw [hy1]
        simp
      calc K ≤ K ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G) := le_inf le_rfl hcent
        _ ≤ CFSG.Open.pCoreOf 2 K := hK
        _ = ⊥ := hQ
    have hcard : Nat.card ↥K = 1 := by
      rw [hKbot]
      exact Subgroup.card_bot
    have hle := CFSG.SectionRank.pRank_le_card_of_one_lt (G := ↥K) hp.one_lt
      (⊤ : Subgroup ↥K)
    rw [hcard] at hle
    omega
  · let Q : Subgroup G := CFSG.Open.pCoreOf 2 K
    have hQne : Q ≠ ⊥ := by
      have h : Q = CFSG.Open.pCoreOf 2 K := rfl
      rw [h]
      exact hQ
    have hQt : IsPGroup 2 Q := by
      have h : Q = (CFSG.pCore 2 ↥K).map K.subtype := rfl
      rw [h]
      exact (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).map K.subtype
    have hH : CFSG.Open.IsTwoLocal (Subgroup.normalizer (Q : Set G)) :=
      ⟨Q, hQne, hQt, rfl⟩
    have hQnorm : (Q.subgroupOf K).Normal := by
      have h : Q = CFSG.Open.pCoreOf 2 K := rfl
      rw [h, CFSG.openPCoreOf_subgroupOf]
      exact CFSG.pCore_normal
    have hQK : Q ≤ K := by
      have h : Q = CFSG.Open.pCoreOf 2 K := rfl
      rw [h]
      exact CFSG.openPCoreOf_le 2 K
    haveI : (Q.subgroupOf K).Normal := hQnorm
    have hKQ : K ≤ Subgroup.normalizer (Q : Set G) :=
      Subgroup.le_normalizer_of_normal_subgroupOf hQK
    have hle : CFSG.Open.pRank p K ≤ 2 :=
      (CFSG.SectionRank.pRank_mono hp.one_lt hKQ).trans
        (pRank_le_two_of_twoLocal D hx hσ3 hsig hm3 hp hp3 hH)
    rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup K]

theorem c8_cTilde_le (M V₀ V : Subgroup G) : F11.CTilde M V₀ V ≤ M :=
  (iInf₂_le 1 V.one_mem).trans fun _ hm => hm.1

theorem c8k_c0_le (D : Data G) (V₀ V K : Subgroup G) : c8kC0 D V₀ V K ≤ c8kB D K := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact ⟨hx.1, c8_cTilde_le D.M V₀ V hx.2⟩

theorem c8k_s_le (D : Data G) {K T' : Subgroup G} (hT : T' ≤ D.M) : c8kS K T' ≤ c8kB D K := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact ⟨hx.2, hT hx.1⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
