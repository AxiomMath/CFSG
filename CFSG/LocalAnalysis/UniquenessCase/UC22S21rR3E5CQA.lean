module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229N
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XB
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveFixed
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Rank
import CFSG.Assembly.E6FourLabelArith
import CFSG.CGT.PushingUpLit.BHS7.OmegaSL
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22i
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC6S846
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22r3e5c_five_mem_piSet {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch)
    (hn3 : 3 ≤ c.n) (hpow : IsPowTwo c.n) : 5 ∈ piSet c.B0 := by
  obtain ⟨k, hk⟩ := hpow
  have hk2 : 2 ≤ k := by
    rcases k with _ | _ | k
    · rw [hk] at hn3
      norm_num at hn3
    · rw [hk] at hn3
      norm_num at hn3
    · omega
  have h4 : 4 ∣ c.n := by
    rw [hk]
    exact Nat.pow_dvd_pow 2 hk2
  have h5 : 5 ∣ 2 ^ c.n - 1 :=
    (show 5 ∣ 2 ^ 4 - 1 by norm_num).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 h4)
  rw [c.hpi]
  exact ⟨Nat.prime_five, h5⟩

theorem uc22r3e5c_exists_elt_of_order_five {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch)
    (hn3 : 3 ≤ c.n) (hpow : IsPowTwo c.n) : ∃ a ∈ c.B0, orderOf a = 5 :=
  uc22p22i_exists_elt_of_mem_piSet (uc22r3e5c_five_mem_piSet c hn3 hpow)

theorem uc22r3e5c_odd_of_isSz {X : Type} [Group X] {n : ℕ} (h : IsSz X n) : Odd n := by
  obtain ⟨-, -, a, -, -, -, -, rfl, -, -⟩ := CFSG.Blueprint.LieModel.suzukiModel h
  exact ⟨a, rfl⟩

theorem uc22r3e5c_not_five_dvd_two_pow_sub_one {n : ℕ} (hn : Odd n) : ¬ 5 ∣ 2 ^ n - 1 := by
  intro h
  have h4 := CFSG.Assembly.e6Four_five_dvd_two_pow_sub_one.1 h
  obtain ⟨k, rfl⟩ := hn
  omega

theorem uc22r3e5c_eq_one_of_mem_normalizer_sylow
    {X : Type} [Group X] [Finite X] {n : ℕ} (hSz : IsSz X n) (hn : Odd n)
    (Q : Sylow 2 X) {s : X} (hs5 : s ^ 5 = 1)
    (hsN : s ∈ normalizer ((Q : Subgroup X) : Set X)) : s = 1 := by
  by_contra hne
  have hord : orderOf s = 5 := by
    rcases (Nat.dvd_prime Nat.prime_five).1 (orderOf_dvd_of_pow_eq_one hs5) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  have hdvd : 5 ∣ Nat.card (normalizer ((Q : Subgroup X) : Set X)) := by
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard (s := normalizer ((Q : Subgroup X) : Set X)) hsN
  have hcard := CFSG.LieType.SuzukiSubgroups.card_normalizer_sylow_of_isSz
    (CFSG.LocalAnalysis.WeakClosure81.isSz_iff_isSz.mp hSz) Q
  rw [hcard] at hdvd
  have h2 : ¬ 5 ∣ (2 ^ n) ^ 2 := by
    intro h
    rw [← pow_mul] at h
    exact absurd (Nat.prime_five.dvd_of_dvd_pow h) (by norm_num)
  have h1 : ¬ 5 ∣ 2 ^ n - 1 := uc22r3e5c_not_five_dvd_two_pow_sub_one hn
  rcases (Nat.Prime.dvd_mul Nat.prime_five).1 hdvd with h | h
  · exact h2 h
  · exact h1 h


theorem uc22r3e5c_mem_normalizer_T_inf {D : Data G} {L : Subgroup G} {a : G}
    (haT : a ∈ normalizer ((D.T ⊓ conjClosure D.M L : Subgroup G) : Set G))
    (haL : a ∈ normalizer (L : Set G)) :
    a ∈ normalizer ((D.T ⊓ L : Subgroup G) : Set G) := by
  have hLmem : L ∈ conjSetOf D.M L :=
    ⟨1, D.M.one_mem, by ext z; simp [MulAut.conj_apply]⟩
  have hXL : L ≤ conjClosure D.M L :=
    le_iSup₂_of_le (f := fun K (_ : K ∈ conjSetOf D.M L) => K) L hLmem le_rfl
  have hTXL : (D.T ⊓ conjClosure D.M L) ⊓ L = D.T ⊓ L := by
    rw [inf_assoc, inf_eq_right.mpr hXL]
  rw [← hTXL]
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨haT, haL⟩

theorem uc22r3e5c_center_bar2_eq_bot {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    {n : ℕ} (hSz : IsSz (Bar2 L) n) : Subgroup.center (Bar2 L) = ⊥ := by
  obtain ⟨e⟩ := uc22p22l_barImage_equiv hL
  have h := Subgroup.map_center_eq e
  rw [u4x_center_eq_bot hL (Or.inr hSz)] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h

theorem uc22r3e5c_rhoL_pow_five {L : Subgroup G} {a : G} (haL : a ∈ normalizer (L : Set G))
    (ha5 : orderOf a = 5) : rhoL L ⟨a, haL⟩ ^ 5 = 1 := by
  rw [← map_pow]
  have h1 : (⟨a, haL⟩ : ↥(normalizer (L : Set G))) ^ 5 = 1 := by
    refine Subtype.ext ?_
    show a ^ 5 = 1
    rw [← ha5]
    exact pow_orderOf_eq_one a
  rw [h1, map_one]

theorem uc22r3e5c_pow_five_of_conj_eq {L : Subgroup G} {s : Bar2 L} {ρ : MulAut (Bar2 L)}
    (hZ : Subgroup.center (Bar2 L) = ⊥) (hs : MulAut.conj s = ρ) (hρ : ρ ^ 5 = 1) :
    s ^ 5 = 1 :=
  CFSG.mulAutConj_injective_of_center_eq_bot hZ (by
    calc MulAut.conj (s ^ 5) = MulAut.conj s ^ 5 := by rw [map_pow]
      _ = ρ ^ 5 := by rw [hs]
      _ = 1 := hρ
      _ = MulAut.conj (1 : Bar2 L) := (map_one _).symm)

theorem uc22r3e5c_exists_sylow_barImage {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M) :
    ∃ Q : Sylow 2 (Bar2 L), (Q : Subgroup (Bar2 L)) = barImage L (D.T ⊓ L) := by
  have hT2 : CFSG.QuasithinUnique.IsSylowTwoOf D.T D.M :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr D.sylowM
  have hSylL : CFSG.QuasithinUnique.IsSylowTwoOf (D.T ⊓ L) L :=
    CFSG.CGT.PushingUpLit.BHS7.isSylowTwoOf_inf_of_isSubnormal hL.1 hT2
  let QL : Sylow 2 ↥L := CFSG.Quasithin.A4.toSylow hSylL
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let Q : Sylow 2 (Bar2 L) := Sylow.mapSurjective hπ QL
  refine ⟨Q, ?_⟩
  rw [Sylow.coe_mapSurjective]
  show (QL : Subgroup ↥L).map π = barImage L (D.T ⊓ L)
  rw [CFSG.Quasithin.A4.toSylow_coe]
  rfl

theorem uc22r3e5c_centralizesBar_of_rhoL_eq_one {L : Subgroup G} {a : G}
    (haL : a ∈ normalizer (L : Set G)) (h : rhoL L ⟨a, haL⟩ = 1) : CentralizesBar a L := by
  refine uc22p21d_centralizesBar_iff.mpr fun l hl => ?_
  exact (rhoL_fix_iff L ⟨a, haL⟩ ⟨l, hl⟩).mp (by rw [h]; rfl)

theorem uc22r3e5c_centralizesBar_of_isSz
    {D : Data G} {Ch : Choice2011 G} (h5 : S21_5 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M)
    {n : ℕ} (hSz : IsSz (Bar2 L) n) (h5n : ¬ 5 ∣ n)
    {a : G} (haB : a ∈ c.B0) (ha5 : orderOf a = 5)
    (haT : a ∈ normalizer ((D.T ⊓ conjClosure D.M L : Subgroup G) : Set G)) :
    CentralizesBar a L := by
  have hodd : Odd n := uc22r3e5c_odd_of_isSz hSz
  let c' : Ctx21 D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  have haL : a ∈ normalizer (L : Set G) := h5 h1930 c' L hL haB
  have haTL : a ∈ normalizer ((D.T ⊓ L : Subgroup G) : Set G) :=
    uc22r3e5c_mem_normalizer_T_inf haT haL
  have hpow : rhoL L ⟨a, haL⟩ ^ 5 = 1 := uc22r3e5c_rhoL_pow_five haL ha5
  obtain ⟨s, hs⟩ := uc22p2214_inner_of_prime_Sz hSz (r := 5) (by norm_num) h5n hpow
  have hs5 : s ^ 5 = 1 :=
    uc22r3e5c_pow_five_of_conj_eq (uc22r3e5c_center_bar2_eq_bot hL hSz) hs hpow
  have hmap : (barImage L (D.T ⊓ L)).map (rhoL L ⟨a, haL⟩).toMonoidHom =
      barImage L (D.T ⊓ L) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.rhoL_maps_barImage inf_le_right haTL haL
  have hsN : s ∈ normalizer ((barImage L (D.T ⊓ L) : Subgroup (Bar2 L)) : Set (Bar2 L)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa [← hs] using hmap
  obtain ⟨Q, hQcoe⟩ := uc22r3e5c_exists_sylow_barImage hL
  have hsNQ : s ∈ normalizer ((Q : Subgroup (Bar2 L)) : Set (Bar2 L)) := by
    rw [hQcoe]
    exact hsN
  have hs1 : s = 1 := uc22r3e5c_eq_one_of_mem_normalizer_sylow hSz hodd Q hs5 hsNQ
  have hrho : rhoL L ⟨a, haL⟩ = 1 := by rw [← hs, hs1, map_one]
  exact uc22r3e5c_centralizesBar_of_rhoL_eq_one haL hrho

theorem uc22r3e5c_centralizes_x
    {D : Data G} {Ch : Choice2011 G} (h5 : S21_5 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M)
    {n : ℕ} (hSz : IsSz (Bar2 L) n) (h5n : ¬ 5 ∣ n)
    {a : G} (haB : a ∈ c.B0) (ha5 : orderOf a = 5)
    (haT : a ∈ normalizer ((D.T ⊓ conjClosure D.M L : Subgroup G) : Set G)) :
    CentralizesBar a (conjClosure D.M L) := by
  classical
  have hmem : ∀ K' ∈ conjSetOf D.M L, a ∈ normalizer (K' : Set G) := fun K' hK' =>
    h5 h1930 { c with B := c.B0, hB := c.hB0, hle := le_rfl } K'
      (uc22p2214_calC_of_mem_conjSetOf hL hK') haB
  have haX : a ∈ normalizer ((conjClosure D.M L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 : ∀ K ∈ conjSetOf D.M L, K.map (MulAut.conj a).toMonoidHom = K := fun K hK =>
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hmem K hK)
    rw [conjClosure, Subgroup.map_iSup]
    simp only [Subgroup.map_iSup]
    exact iSup_congr fun K => iSup_congr fun hK => h1 K hK
  obtain ⟨hXM, hMX, -⟩ := uc22p22u_conjClosure_isProd (X := D.M) (K := L) le_rfl
    Subgroup.le_normalizer hL
  refine uc22p2214_centralizesBar_conjClosure (M := D.M) (K := L) haX fun K' hK' k hk => ?_
  have hK'cal : K' ∈ calC D.M := uc22p2214_calC_of_mem_conjSetOf hL hK'
  obtain ⟨eK⟩ := u4x_bar2_equiv hK'
  have hSzK : IsSz (Bar2 K') n := CFSG.Blueprint.LieModel.of_mulEquiv eK hSz
  have hXeq : conjClosure D.M K' = conjClosure D.M L := by
    rw [conjClosure, conjClosure, uc22p2214_conjSetOf_eq hK']
  have haT' : a ∈ normalizer ((D.T ⊓ conjClosure D.M K' : Subgroup G) : Set G) := by
    rw [hXeq]; exact haT
  have hCK : CentralizesBar a K' :=
    uc22r3e5c_centralizesBar_of_isSz h5 h1930 c hK'cal hSzK h5n haB ha5 haT'
  have hsub : CFSG.Open.IsSubnormal K' D.M := hK'cal.1
  have h1 : CFSG.Open.pCoreOf 2 K' ≤ CFSG.Open.pCoreOf 2 D.M :=
    CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hsub
  have h2 : CFSG.Open.pCoreOf 2 K' ≤ conjClosure D.M L :=
    (Subgroup.map_subtype_le _).trans
      (le_iSup₂ (f := fun Y (_ : Y ∈ conjSetOf D.M L) => Y) K' hK')
  exact uc22p2214_pCoreOf_inf_le hXM ⟨h1 (hCK.2 k hk), h2 (hCK.2 k hk)⟩

theorem uc22r3e5c_one_le_pRank_of_dvd_card {p : ℕ} (hp : p.Prime)
    {H : Subgroup G} (hdvd : p ∣ Nat.card H) : 1 ≤ CFSG.Open.pRank (G := G) p H := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) p hdvd
  have hcard : Nat.card ↥(Subgroup.zpowers g) = p := by
    rw [Nat.card_zpowers, hg]
  have hel : IsElemAbelian p (Subgroup.zpowers g) :=
    CFSG.GroupTheory.isElemAbelian_of_card_prime hcard
  refine CFSG.SectionRank.le_pRank hp.one_lt (H := H)
    (E := (Subgroup.zpowers g).map H.subtype) (Subgroup.map_subtype_le _) ?_ (k := 1) ?_
  · exact hel.map H.subtype
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hcard, pow_one]

theorem uc22r3e5c_dvd_card_bar2 {D : Data G} {Ch : Choice2011 G} (h15 : S21_15C D Ch)
    (h1930 : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ} (hSz : IsSz (Bar2 L) n) {p : ℕ}
    (hp : p ∈ D.sig) : p ∣ Nat.card (Bar2 L) := by
  have hcong := P2214S.sz_cong_of_s21_15C h15 h1930 c hL hc2 hSz hp
  have hdiv : (p : ℤ) ∣ (2 : ℤ) ^ (2 * n) + 1 := by
    have h := Int.modEq_iff_dvd.mp hcong
    rw [show (2 : ℤ) ^ (2 * n) + 1 = -(-1 - (2 : ℤ) ^ (2 * n)) by ring]
    exact dvd_neg.mpr h
  have hdivN : p ∣ 2 ^ (2 * n) + 1 := by
    have h := hdiv
    push_cast at h
    exact_mod_cast h
  have hcard := CFSG.Quasithin.card_of_isSz
    (CFSG.LocalAnalysis.WeakClosure81.isSz_iff_isSz.mp hSz)
  have hq : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by
    rw [← pow_mul, show n * 2 = 2 * n by omega]
  rw [hcard]
  refine hdivN.trans ?_
  rw [hq]
  exact (dvd_mul_right _ _).trans (dvd_mul_right _ _)

theorem uc22r3e5c_two_le_pRank_barImage_x {D : Data G} {Ch : Choice2011 G}
    (h15 : S21_15C D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ}
    (hSz : IsSz (Bar2 L) n) {p : ℕ} (hp : p ∈ D.sig) :
    2 ≤ CFSG.Open.pRank p (barImage D.M (conjClosure D.M L)) := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  obtain ⟨K, hne, hset, hK⟩ := uc22s21ru4e_exists_second_member hc2 hL
  have hmemK : K ∈ conjSetOf D.M L := by rw [hset]; simp
  have hSzK : IsSz (Bar2 K) n := by
    obtain ⟨eK⟩ := u4x_bar2_equiv hmemK
    exact CFSG.Blueprint.LieModel.of_mulEquiv eK hSz
  have hdvdL := uc22r3e5c_dvd_card_bar2 h15 h1930 c hL hc2 hSz hp
  have hcK : (conjSetOf D.M K).ncard = 2 := by
    rw [uc22p2214_conjSetOf_eq hmemK]; exact hc2
  have hdvdK := uc22r3e5c_dvd_card_bar2 h15 h1930 c hK hcK hSzK hp
  have hcardL : Nat.card ↥(barImage D.M L) = Nat.card (Bar2 L) := by
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv (L := D.M) (K := L) hL
    exact (Nat.card_congr e.toEquiv).symm
  have hcardK : Nat.card ↥(barImage D.M K) = Nat.card (Bar2 K) := by
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv (L := D.M) (K := K) hK
    exact (Nat.card_congr e.toEquiv).symm
  have h1 : 1 ≤ CFSG.Open.pRank p (barImage D.M L) :=
    uc22r3e5c_one_le_pRank_of_dvd_card hpp (by rwa [hcardL])
  have h2 : 1 ≤ CFSG.Open.pRank p (barImage D.M K) :=
    uc22r3e5c_one_le_pRank_of_dvd_card hpp (by rwa [hcardK])
  obtain ⟨hcomm, hinf, -, -, hXc, -, -⟩ := u4x_bar_structure hL hK hne hset (Or.inr hSz)
  have hsum := CFSG.Quasithin.pRank_add_le_pRank_sup (p := p) hpp hcomm hinf
  rw [hXc]
  omega


theorem uc22r3e5c_exists_mul_of_mem_sup {X A : Subgroup G}
    (hsup : (X ⊓ centralizer (A : Set G)) ⊔ CFSG.Open.pCoreOf 2 X = X) {x : G} (hx : x ∈ X) :
    ∃ c ∈ X ⊓ centralizer (A : Set G), ∃ o ∈ CFSG.Open.pCoreOf 2 X, c * o = x := by
  have hOXeq : (CFSG.Open.pCoreOf 2 X).subgroupOf X = CFSG.pCore 2 ↥X := by
    ext o
    rw [Subgroup.mem_subgroupOf, CFSG.mem_openPCoreOf_iff]
  have htop : (X ⊓ centralizer (A : Set G)).subgroupOf X ⊔ CFSG.pCore 2 ↥X = ⊤ := by
    rw [← hOXeq]
    change (X ⊓ centralizer (A : Set G)).subgroupOf X ⊔
      ((CFSG.pCore 2 X).map X.subtype).subgroupOf X = ⊤
    rw [← Subgroup.subgroupOf_sup inf_le_left (Subgroup.map_subtype_le _)]
    rw [show (X ⊓ centralizer (A : Set G)) ⊔ (CFSG.pCore 2 X).map X.subtype = X from hsup,
      Subgroup.subgroupOf_self]
  have hmem : (⟨x, hx⟩ : ↥X) ∈
      (X ⊓ centralizer (A : Set G)).subgroupOf X ⊔ CFSG.pCore 2 ↥X := by
    rw [htop]; trivial
  obtain ⟨c, hc, o, ho, hco⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := (X ⊓ centralizer (A : Set G)).subgroupOf X)
      (t := CFSG.pCore 2 ↥X)).mp hmem
  exact ⟨(c : G), Subgroup.mem_subgroupOf.mp hc, (o : G),
    (CFSG.mem_openPCoreOf_iff o).mpr ho, congrArg Subtype.val hco⟩

theorem uc22r3e5c_barImage_inf_centralizer {M X A : Subgroup G} (hXM : X ≤ M)
    (hsup : (X ⊓ centralizer (A : Set G)) ⊔ CFSG.Open.pCoreOf 2 X = X)
    (hOX : CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 M) :
    barImage M (X ⊓ centralizer (A : Set G)) = barImage M X := by
  refine le_antisymm ?_ ?_
  · intro q hq
    obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.mp hq
    exact uc22p21c_mem_barImage.mpr ⟨m, (Subgroup.mem_inf.mp hm).1, rfl⟩
  · intro q hq
    obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.mp hq
    obtain ⟨c, hc, o, ho, hco⟩ := uc22r3e5c_exists_mul_of_mem_sup hsup hm
    have h1 : uc22p21cPi M ⟨o, hXM (Subgroup.map_subtype_le _ ho)⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ((CFSG.mem_openPCoreOf_iff _).mp (hOX ho))
    refine uc22p21c_mem_barImage.mpr
      ⟨⟨c, hXM (Subgroup.mem_inf.mp hc).1⟩, hc, ?_⟩
    have hm' : m = ⟨c, hXM (Subgroup.mem_inf.mp hc).1⟩ *
        ⟨o, hXM (Subgroup.map_subtype_le _ ho)⟩ := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul] using hco.symm
    rw [hm', map_mul, h1, mul_one]

theorem uc22r3e5c_barImage_le_map_top {M C : Subgroup G} (hCM : C ≤ M) :
    barImage M C ≤ (⊤ : Subgroup ↥C).map
      ((uc22p21cPi M).comp (Subgroup.inclusion hCM)) := by
  intro q hq
  obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.mp hq
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_top (⟨(m : G), hm⟩ : ↥C))

theorem uc22r3e5c_two_le_pRank_centralizer
    {D : Data G} {Ch : Choice2011 G} (h5 : S21_5 D Ch) (h15 : S21_15C D Ch)
    (h1930 : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ} (hSz : IsSz (Bar2 L) n)
    (h5n : ¬ 5 ∣ n) {a : G} (haB : a ∈ c.B0) (ha5 : orderOf a = 5)
    (haT : a ∈ normalizer ((D.T ⊓ conjClosure D.M L : Subgroup G) : Set G)) {p : ℕ}
    (hp : p ∈ D.sig) :
    2 ≤ CFSG.Open.pRank p (conjClosure D.M L ⊓ centralizer (Subgroup.zpowers a : Set G)) := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  haveI : Fact p.Prime := ⟨hpp⟩
  have hCX : CentralizesBar a (conjClosure D.M L) :=
    uc22r3e5c_centralizes_x h5 h1930 c hL hSz h5n haB ha5 haT
  have hcent : ∀ x ∈ Subgroup.zpowers a, CentralizesBar x (conjClosure D.M L) := fun x hx =>
    uc22p21d_centralizesBar_of_mem_zpowers hCX hx
  have hcard5 : Nat.card ↥(Subgroup.zpowers a) = 5 := by
    rw [Nat.card_zpowers, ha5]
  have hsup : (conjClosure D.M L ⊓ centralizer (Subgroup.zpowers a : Set G)) ⊔
      CFSG.Open.pCoreOf 2 (conjClosure D.M L) = conjClosure D.M L :=
    uc22p21d_sup_pCore_eq (L := conjClosure D.M L) (A := Subgroup.zpowers a) (r := 5)
      Nat.prime_five (by norm_num) hcard5 hcent
  obtain ⟨hXM, hMX, -⟩ := uc22p22u_conjClosure_isProd (X := D.M) (K := L) le_rfl
    Subgroup.le_normalizer hL
  have hsub : CFSG.Open.IsSubnormal (conjClosure D.M L) D.M :=
    CFSG.Quasithin.A3.subnormal_of_normal hXM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hXM).2 hMX)
  have hOX : CFSG.Open.pCoreOf 2 (conjClosure D.M L) ≤ CFSG.Open.pCoreOf 2 D.M :=
    CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hsub
  have hbar := uc22r3e5c_barImage_inf_centralizer hXM hsup hOX
  have h2 : 2 ≤ CFSG.Open.pRank p (barImage D.M (conjClosure D.M L ⊓
      centralizer (Subgroup.zpowers a : Set G))) := by
    rw [hbar]
    exact uc22r3e5c_two_le_pRank_barImage_x h15 h1930 c hL hc2 hSz hp
  have hC : conjClosure D.M L ⊓ centralizer (Subgroup.zpowers a : Set G) ≤ D.M :=
    inf_le_left.trans hXM
  have hle := uc22r3e5c_barImage_le_map_top hC
  have hres := CFSG.LocalAnalysis.WeakClosure81.two_le_pRank_of_le_map
    ((uc22p21cPi D.M).comp (Subgroup.inclusion hC)) hpp hp2 hle h2
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup
    (conjClosure D.M L ⊓ centralizer (Subgroup.zpowers a : Set G))] at hres
  exact hres

end CFSG.LocalAnalysis.UniquenessCase.UC22
