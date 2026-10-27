module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19D
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem24Three

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement

variable {G : Type} [Group G]

abbrev ch6U (T L V : Subgroup G) : Subgroup G :=
  conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))

abbrev ch6R (T L V : Subgroup G) (l : G) : Subgroup G :=
  pCoreOf 2 (ch6U T L V ⊔ conjSubgroup (ch6U T L V) l)

abbrev ch6CH (T L V : Subgroup G) : Subgroup G :=
  centralizerMod (ch6ZS T L V) (Subgroup.normalizer (ch6ZS T L V : Set G)) (ch6U T L V)

variable [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp6116

theorem ch6CH_eq (h432 : Stmt4_3_2) (h6111 : Stmt6_1_11) (h6119 : Stmt6_1_19)
    (h : Hyp6116 G T M L V n) :
    ch6CH T L V = pCoreOf 2 (Subgroup.centralizer (ch6ZS T L V : Set G)) := by
  have h17 := (stmt6_1_17 h432 G T M L V n h _ h.isInHS_sup).2.2.1
  rw [inf_eq_right.mpr le_sup_left, h.conjClosure_sup_T_eq] at h17
  have hCHI := h.centralizerMod_normalizer_le h432 h6111 h6119
  have hIH : Subgroup.centralizer (ch6ZS T L V : Set G) ≤
      Subgroup.normalizer (ch6ZS T L V : Set G) := Subgroup.centralizer_le_normalizer _
  rw [h17]
  exact le_antisymm (fun x hx => ⟨hCHI hx, hx.2.1, hx.2.2⟩) (centralizerMod_mono_left _ hIH)

theorem R_le_I (h432 : Stmt4_3_2) (h6111 : Stmt6_1_11) (h6119 : Stmt6_1_19)
    (h : Hyp6116 G T M L V n) {l : G} (hl : l ∈ L)
    (hlN : l ∉ Subgroup.normalizer (ch6ZS T L V : Set G)) :
    ch6R T L V l ≤ Subgroup.centralizer (ch6ZS T L V : Set G) := by
  have h21 := stmt6_1_21 h432 h6111 h6119 G T M L V n h l hl hlN
  dsimp only at h21
  obtain ⟨-, ⟨hRAB, -⟩, -, -, -⟩ := h21
  obtain ⟨hUO, -⟩ := h.lemma_6_1_20_one h432
  rw [ch6R, hRAB]
  refine sup_le (inf_le_left.trans (hUO.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _))) ?_
  exact inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left))

theorem MV_le_normalizer_R (h432 : Stmt4_3_2) (h6111 : Stmt6_1_11) (h6119 : Stmt6_1_19)
    (h : Hyp6116 G T M L V n) {l : G} (hl : l ∈ L)
    (hlN : l ∉ Subgroup.normalizer (ch6ZS T L V : Set G)) :
    ch6MV M V ≤ Subgroup.normalizer (ch6R T L V l : Set G) ∧
      ch6R T L V l ≤ pCoreOf 2 (ch6MV M V) := by
  have h21 := stmt6_1_21 h432 h6111 h6119 G T M L V n h l hl hlN
  dsimp only at h21
  exact h21.2.2.2.2

theorem R_le_S (h432 : Stmt4_3_2) (h6111 : Stmt6_1_11) (h6119 : Stmt6_1_19)
    (h : Hyp6116 G T M L V n) {l : G} (hl : l ∈ L)
    (hlN : l ∉ Subgroup.normalizer (ch6ZS T L V : Set G)) :
    ch6R T L V l ≤ ch6S T L V := by
  have hTMV : IsSylowTwoOf T (ch6MV M V) :=
    A4.isSylowTwoOf_mono ⟨le_top, h.sylow.1, by
        rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
        exact h.sylow.2⟩
      (le_inf h.T_le h.toHyp611.T_le_normalizer) le_top
  refine le_inf ?_ (h.R_le_I h432 h6111 h6119 hl hlN)
  exact (h.MV_le_normalizer_R h432 h6111 h6119 hl hlN).2.trans
    (F7.isSylowTwoOf_pCoreOf_le hTMV)

omit [Finite G] in
theorem _root_.CFSG.Quasithin.H13.mem_normalizer_sup_ch6 {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h1 : x * y * x⁻¹ ∈ (A ⊔ B).map (MulAut.conj x).toMonoidHom := ⟨y, hy, rfl⟩
    rwa [Subgroup.map_sup, map_conj_eq_of_mem_normalizer_ch6 hA,
      map_conj_eq_of_mem_normalizer_ch6 hB] at h1
  · intro hy
    have h1 : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ ∈ (A ⊔ B).map (MulAut.conj x⁻¹).toMonoidHom :=
      ⟨_, hy, rfl⟩
    rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer_ch6 (Subgroup.inv_mem _ hA),
      map_conj_eq_of_mem_normalizer_ch6 (Subgroup.inv_mem _ hB)] at h1
    simpa [mul_assoc] using h1

omit [Finite G] in
theorem DL_le_L {DL : Subgroup G} (hDL : Lin2.IsHallTwoPrimeOf DL (borelL T L)) : DL ≤ L :=
  hDL.1.trans inf_le_left

theorem DL_le_normalizer_ZS (h : Hyp6116 G T M L V n) {DL : Subgroup G}
    (hDL : Lin2.IsHallTwoPrimeOf DL (borelL T L)) :
    DL ≤ Subgroup.normalizer (ch6ZS T L V : Set G) :=
  hDL.1.trans h.toHyp611Nat.borelL_le_normalizer_ZS

theorem DL_le_MV (h : Hyp6116 G T M L V n) {DL : Subgroup G}
    (hDL : Lin2.IsHallTwoPrimeOf DL (borelL T L)) : DL ≤ ch6MV M V :=
  le_inf ((DL_le_L hDL).trans h.L_le) ((DL_le_L hDL).trans h.toHyp611.L_le_normalizer)

theorem DL_inf_I (h : Hyp6116 G T M L V n) {DL : Subgroup G}
    (hDL : Lin2.IsHallTwoPrimeOf DL (borelL T L)) :
    DL ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) = ⊥ :=
  h.toHyp611Nat.inf_centralizer_ZS_eq_bot (DL_le_L hDL) hDL.2.1

theorem card_DL (h : Hyp6116 G T M L V n) {DL : Subgroup G}
    (hDL : Lin2.IsHallTwoPrimeOf DL (borelL T L)) : IsCyclic ↥DL ∧ Nat.card DL = 2 ^ n - 1 :=
  h.toHyp5_0_1.isCyclic_card_of_isHall l2TorusFact hDL

theorem DL_ne_bot (h : Hyp6116 G T M L V n) {DL : Subgroup G}
    (hDL : Lin2.IsHallTwoPrimeOf DL (borelL T L)) : DL ≠ ⊥ := by
  intro h0
  have hc := (h.card_DL hDL).2
  rw [h0, Subgroup.card_bot] at hc
  have h2 := h.toHyp5_0_1.two_le
  have : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
  omega

theorem DL_le_normalizer_S (h432 : Stmt4_3_2) (h : Hyp6116 G T M L V n) {DL : Subgroup G}
    (hDL : Lin2.IsHallTwoPrimeOf DL (borelL T L)) :
    DL ≤ Subgroup.normalizer (ch6S T L V : Set G) := by
  intro d hd
  rw [(stmt6_1_9 h432 G T M L V n h.toHyp611Nat).1.1]
  refine mem_normalizer_sup_ch6 (hDL.1 hd).2 ?_
  exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
    (Subgroup.mem_sup_left (DL_le_L hDL hd))

end Hyp6116

omit [Finite G] in
theorem mem_normalizer_of_map_conj_eq_ch625 {X : Subgroup G} {x : G}
    (h : X.map (MulAut.conj x).toMonoidHom = X) : x ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : x * y * x⁻¹ ∈ X.map (MulAut.conj x).toMonoidHom := ⟨y, hy, rfl⟩
    rwa [h] at this
  · intro hy
    rw [← h] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have e : x * z * x⁻¹ = x * y * x⁻¹ := hzy
    have : z = y := mul_left_cancel (mul_right_cancel e)
    rw [← this]
    exact hz

theorem pCoreOf_le_normalizer_of_mem_cComp {X K : Subgroup G} (hK : K ∈ cComp X) :
    pCoreOf 2 X ≤ Subgroup.normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCoreOf 2 X with hP
  have hPX : P ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hPn : (P.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPX).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
  have hPs : Group.IsSolvable ↥P := by
    have := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).isNilpotent
    infer_instance
  have hbij := cComp_quotient_bijOn_of_le hPX hPn hPs
  intro x hx
  have hxX : x ∈ X := hPX hx
  have hKx : K.map (MulAut.conj x).toMonoidHom ∈ cComp X := by
    have := quasithinIsCComponent_map (MulAut.conj x) hK
    rwa [map_conj_eq_of_mem_normalizer_ch6 (Subgroup.le_normalizer hxX)] at this
  apply mem_normalizer_of_map_conj_eq_ch625
  refine hbij.injOn hKx hK ?_
  have hKX : K ≤ X := le_of_mem_cComp hK
  have hmk : (QuotientGroup.mk' (P.subgroupOf X) : ↥X →* _) ⟨x, hxX⟩ = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hx
  ext q
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, ⟨k, hk, hky⟩, rfl⟩
    refine ⟨⟨k, hKX hk⟩, hk, ?_⟩
    have hy : y = ⟨x, hxX⟩ * ⟨k, hKX hk⟩ * ⟨x, hxX⟩⁻¹ := Subtype.ext (by
      rw [← hky]
      rfl)
    rw [hy, map_mul, map_mul, map_inv, hmk, one_mul, inv_one, mul_one]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨x, hxX⟩ * y * ⟨x, hxX⟩⁻¹, ⟨y, hy, rfl⟩, ?_⟩
    rw [map_mul, map_mul, map_inv, hmk, one_mul, inv_one, mul_one]

theorem map_conj_eq_of_odd_of_ncard_two {X : Set (Subgroup G)} (hX : X.ncard = 2)
    {K : Subgroup G} (hKX : K ∈ X) {g : G}
    (hg : ∀ Y ∈ X, Y.map (MulAut.conj g).toMonoidHom ∈ X) (hodd : Odd (orderOf g)) :
    K.map (MulAut.conj g).toMonoidHom = K := by
  set f : Subgroup G → Subgroup G := fun Y => Y.map (MulAut.conj g).toMonoidHom with hf
  have hinj : Function.Injective f := fun A B hAB =>
    Subgroup.map_injective (MulAut.conj g).injective hAB
  have hpow : ∀ j : ℕ, f^[j] K = K.map (MulAut.conj (g ^ j)).toMonoidHom := by
    intro j
    induction j with
    | zero =>
      ext x
      simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih, hf]
      dsimp only
      rw [Subgroup.map_map, pow_succ', map_mul]
      rfl
  by_contra hne
  have hfK : f K ∈ X := hg K hKX
  have hffK : f (f K) ∈ X := hg _ hfK
  have hX2 : ∀ Y ∈ X, Y = K ∨ Y = f K := by
    intro Y hY
    by_contra hY'
    push Not at hY'
    have h3 : ({K, f K, Y} : Set (Subgroup G)) ⊆ X := by
      intro Z hZ
      rcases hZ with rfl | rfl | rfl
      · exact hKX
      · exact hfK
      · exact hY
    have h4 := Set.ncard_le_ncard h3 (Set.toFinite X)
    rw [Set.ncard_insert_of_notMem (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun h0 => hne h0.symm, fun h0 => hY'.1 h0.symm⟩),
      Set.ncard_pair (fun h0 => hY'.2 h0.symm)] at h4
    omega
  have hff : f (f K) = K := by
    rcases hX2 _ hffK with h1 | h1
    · exact h1
    · exact absurd (hinj h1) hne
  have heven : ∀ j : ℕ, f^[2 * j] K = K := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [show 2 * (j + 1) = 2 + 2 * j by ring, Function.iterate_add_apply, ih]
      exact hff
  obtain ⟨j, hj⟩ := hodd
  have h1 : f^[orderOf g] K = K := by
    rw [hpow, pow_orderOf_eq_one, map_one]
    exact Subgroup.map_id K
  rw [hj, add_comm, Function.iterate_add_apply, heven, Function.iterate_one] at h1
  exact hne h1

omit [Finite G] in
theorem map_conj_mul_ch625 (K : Subgroup G) (a b : G) :
    K.map (MulAut.conj (a * b)).toMonoidHom =
      (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map, map_mul]
  rfl

namespace Hyp6116

theorem pCoreOf_H_ne_bot (h : Hyp6116 G T M L V n) :
    pCoreOf 2 (Subgroup.normalizer (ch6ZS T L V : Set G)) ≠ ⊥ := by
  intro h0
  apply h.toHyp611Nat.ZS_ne_bot
  rw [eq_bot_iff, ← h0]
  have hZel : IsElemAbelian 2 (ch6ZS T L V) :=
    B2F.isElemAbelian_mono inf_le_left h.toHyp611.isElemAbelian
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
    (B2F.isPGroup_of_isElemAbelian hZel)

omit [Finite G] in
theorem _root_.CFSG.Quasithin.H13.mem_cComp_normalizer_ZS {K : Subgroup G}
    (hK : K ∈ cComp (Subgroup.centralizer (ch6ZS T L V : Set G))) :
    K ∈ cComp (Subgroup.normalizer (ch6ZS T L V : Set G)) := by
  refine cComp_mem_of_subnormal (A3.subnormal_of_normal (Subgroup.centralizer_le_normalizer _)
    ?_) hK
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mpr
    (F7.normalizer_le_normalizer_centralizer _)

theorem le_normalizer_K (h432 : Stmt4_3_2) (h6111 : Stmt6_1_11) (h6119 : Stmt6_1_19)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp6116 G T M L V n) {l : G} (hl : l ∈ L)
    (hlN : l ∉ Subgroup.normalizer (ch6ZS T L V : Set G)) {DL : Subgroup G}
    (hDL : Lin2.IsHallTwoPrimeOf DL (borelL T L)) {K : Subgroup G}
    (hK : K ∈ cComp (Subgroup.centralizer (ch6ZS T L V : Set G))) :
    DL ≤ Subgroup.normalizer (K : Set G) ∧ ch6R T L V l ≤ Subgroup.normalizer (K : Set G) := by
  have : IsSimpleGroup G := h.simple
  have hLoc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  set Hn := Subgroup.normalizer (ch6ZS T L V : Set G) with hHn
  set I := Subgroup.centralizer (ch6ZS T L V : Set G) with hI
  have hKH : K ∈ cComp Hn := mem_cComp_normalizer_ZS hK
  have hDLH : DL ≤ Hn := h.DL_le_normalizer_ZS hDL
  have hRI : ch6R T L V l ≤ I := h.R_le_I h432 h6111 h6119 hl hlN
  have hIH : I ≤ Hn := Subgroup.centralizer_le_normalizer _
  have hOK : pCoreOf 2 I ≤ Subgroup.normalizer (K : Set G) := pCoreOf_le_normalizer_of_mem_cComp hK
  have hCUV : ch6U T L V ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 I :=
    inf_le_left.trans (h.lemma_6_1_20_one h432).1
  have hR24 := (h.lemma_6_1_24_two h432 h6111 h6119 hl hlN).2.2 DL hDL DL le_rfl
    (h.DL_ne_bot hDL)
  rcases Vol2Native.lemma_1_2_1_three hLoc h37 h38 h.pCoreOf_H_ne_bot hKH with hn | ⟨h2, -⟩
  · have hHK : Hn ≤ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hKH)).mp hn
    exact ⟨hDLH.trans hHK, hRI.trans (hIH.trans hHK)⟩
  · set X := conjSubgroupsBy Hn K with hX
    have hperm : ∀ g ∈ Hn, ∀ Y ∈ X, Y.map (MulAut.conj g).toMonoidHom ∈ X := by
      rintro g hg Y ⟨t, ht, rfl⟩
      exact ⟨g * t, Hn.mul_mem hg ht, (map_conj_mul_ch625 K g t).symm⟩
    have hKX : K ∈ X := ⟨1, Hn.one_mem, by ext x; simp⟩
    have hfix : ∀ d ∈ DL, ∀ Y ∈ X, Y.map (MulAut.conj d).toMonoidHom = Y := by
      intro d hd Y hY
      have hodd : Odd (orderOf d) := by
        refine Odd.of_dvd_nat hDL.2.1 ?_
        rw [← Subgroup.orderOf_mk d hd]
        exact orderOf_dvd_natCard _
      exact map_conj_eq_of_odd_of_ncard_two h2 hY (hperm d (hDLH hd)) hodd
    have hDK : DL ≤ Subgroup.normalizer (K : Set G) := fun d hd =>
      mem_normalizer_of_map_conj_eq_ch625 (hfix d hd K hKX)
    refine ⟨hDK, ?_⟩
    have hR24' : ch6R T L V l = ⁅ch6R T L V l, DL⁆ ⊔
        (ch6U T L V ⊓ Subgroup.centralizer (V : Set G)) := hR24
    rw [hR24']
    refine sup_le ?_ (hCUV.trans hOK)
    rw [Subgroup.commutator_le]
    intro r hr d hd
    apply mem_normalizer_of_map_conj_eq_ch625
    have hdK : K.map (MulAut.conj d⁻¹).toMonoidHom = K :=
      map_conj_eq_of_mem_normalizer_ch6 (Subgroup.inv_mem _ (hDK hd))
    have hY : K.map (MulAut.conj r⁻¹).toMonoidHom ∈ X :=
      hperm _ (Subgroup.inv_mem _ (hIH (hRI hr))) K hKX
    have hrK : (K.map (MulAut.conj r⁻¹).toMonoidHom).map (MulAut.conj r).toMonoidHom = K := by
      rw [← map_conj_mul_ch625, mul_inv_cancel]
      ext x
      simp
    rw [commutatorElement_def, map_conj_mul_ch625, map_conj_mul_ch625, map_conj_mul_ch625, hdK,
      hfix d hd _ hY, hrK]

end Hyp6116

end CFSG.Quasithin.H13
