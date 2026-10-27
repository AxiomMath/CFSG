module

public import CFSG.Quasithin.Background.E6TwentyOne
public import CFSG.Quasithin.Background.E6ElevenComp
public import CFSG.Quasithin.Background.E6EightSmall
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.I32Final

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

section Helpers

variable {G : Type} [Group G] [Finite G]

theorem two_dvd_card_of_isQuasisimple {L : Subgroup G} (hL : CFSG.IsQuasisimple ↥L) :
    2 ∣ Nat.card L := by
  by_contra h
  have hodd : Odd (Nat.card L) := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)
  have hsol : Group.IsSolvable ↥L := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hL
  have : Group.IsPerfect ↥L := hL.1
  exact Group.IsPerfect.not_isSolvable ↥L hsol

theorem oddCoreIn_le_of_subnormal'' {K H : Subgroup G} (hKH : K ≤ H)
    (hsub : (K.subgroupOf H).IsSubnormal) : oddCoreIn K ≤ oddCoreIn H := by
  intro y hy
  have hyK : y ∈ K := E3.oddCoreIn_le K hy
  have hyH : y ∈ H := hKH hyK
  let π : Set Nat.Primes := {q | q.val ≠ 2}
  have h1 : (⟨y, hyK⟩ : K) ∈ CFSG.oddCore ↥K := (mem_oddCoreIn_iff K ⟨y, hyK⟩).mp hy
  rw [CFSG.oddCore_eq_piCore] at h1
  let e : ↥(K.subgroupOf H) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKH
  have h2 : e.symm ⟨y, hyK⟩ ∈ CFSG.piCore π ↥(K.subgroupOf H) := by
    have := CFSG.LocalCores.piCore_map_mulEquiv π e.symm
    rw [← this]
    exact ⟨_, h1, rfl⟩
  have hmem : (⟨y, hyH⟩ : H) ∈ (K.subgroupOf H) ⊓ CFSG.piCore π H := by
    rw [← CFSG.LocalCores.prime_set_core_subnormal_intersection π hsub]
    exact ⟨e.symm ⟨y, hyK⟩, h2, rfl⟩
  have hodd' : (⟨y, hyH⟩ : H) ∈ CFSG.oddCore H := by
    rw [CFSG.oddCore_eq_piCore]
    exact hmem.2
  exact (mem_oddCoreIn_iff H ⟨y, hyH⟩).mpr hodd'

theorem isComponentIn_of_isTwoComponentIn {Y H : Subgroup G} (hY : Id2519.IsTwoComponentIn Y H)
    (hO : oddCoreIn H = ⊥) : IsComponentIn Y H := by
  have hYH : Y ≤ H := le_of_mem_cComp hY.1
  have hsub : (Y.subgroupOf H).IsSubnormal :=
    Id2519.subgroupOf_isSubnormal_of_open (subnormal_of_mem_cComp hY.1)
  have hOY : oddCoreIn Y = ⊥ := le_bot_iff.1 (hO ▸ oddCoreIn_le_of_subnormal'' hYH hsub)
  have hOY' : CFSG.oddCore ↥Y = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : G) ∈ oddCoreIn Y := (mem_oddCoreIn_iff Y x).mpr hx
    rw [hOY, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).2 (Subtype.ext hx')
  have e : (↥Y ⧸ CFSG.oddCore ↥Y) ≃* ↥Y :=
    (QuotientGroup.quotientMulEquivOfEq hOY').trans QuotientGroup.quotientBot
  exact Id2519.isComponentIn_of_mem_cComp hY.1 (CFSG.LocalCores.isQuasisimple_of_mulEquiv e hY.2)

omit [Finite G] in
theorem centralizer_eq_inf_of_relIndex_two {U₀ U : Subgroup G} (hU₀U : U₀ ≤ U)
    (hidx : U₀.relIndex U = 2) {u : G} (huU : u ∈ U) (huU₀ : u ∉ U₀) :
    Subgroup.centralizer (U : Set G) =
      Subgroup.centralizer (U₀ : Set G) ⊓ Subgroup.centralizer ({u} : Set G) := by
  apply le_antisymm
  · exact le_inf (Subgroup.centralizer_le hU₀U)
      (Subgroup.centralizer_le (Set.singleton_subset_iff.2 huU))
  · rintro x ⟨hx₀, hxu⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hidx' : (U₀.subgroupOf U).index = 2 := hidx
    have hu' : u * x = x * u := Subgroup.mem_centralizer_iff.1 hxu u (Set.mem_singleton u)
    by_cases hw₀ : w ∈ U₀
    · exact Subgroup.mem_centralizer_iff.1 hx₀ w hw₀
    · have hwu : w * u ∈ U₀ := by
        have key := Subgroup.mul_mem_iff_of_index_two hidx' (a := ⟨w, hw⟩) (b := ⟨u, huU⟩)
        have : (⟨w, hw⟩ * ⟨u, huU⟩ : U) ∈ U₀.subgroupOf U :=
          key.2 (iff_of_false (fun h => hw₀ h) (fun h => huU₀ h))
        exact this
      have h1 := Subgroup.mem_centralizer_iff.1 hx₀ (w * u) hwu
      have hu'' : u⁻¹ * x = x * u⁻¹ := by
        calc u⁻¹ * x = u⁻¹ * (x * u) * u⁻¹ := by group
          _ = u⁻¹ * (u * x) * u⁻¹ := by rw [hu']
          _ = x * u⁻¹ := by group
      calc w * x = (w * u) * (u⁻¹ * x) := by group
        _ = (w * u) * (x * u⁻¹) := by rw [hu'']
        _ = ((w * u) * x) * u⁻¹ := by group
        _ = (x * (w * u)) * u⁻¹ := by rw [h1]
        _ = x * w := by group

end Helpers

section Setting

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

theorem e68_setting (hlist : Lemma115_3_List) (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hO : oddCoreIn (Subgroup.centralizer (U : Set G)) = ⊥)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) :
    ¬ L ≤ M ∧ V ≤ Subgroup.normalizer (L : Set G) ∧
      IsSylowTwoOf ((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L) L ∧
      ∃ z : G, Lemma115Cases L z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.simple
  set H := Subgroup.centralizer (U : Set G) with hHdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hQH : IsSylowTwoOf Q H := e6_5_one h hU
  have hVQ : V ≤ Q := h.le_inf_centralizer
  have hQV : Q ≤ Subgroup.centralizer (V : Set G) := inf_le_right
  have hVH : V ≤ H := hVQ.trans hQH.1
  have hLH : L ≤ H := hL.1
  have hUV : U ≤ V := hU.1
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm h.isElemAbelian ha hb
  have hLM : ¬ L ≤ M := fun hLM => DoubleA3.not_isComponentIn_of_charTwo (e6_6_one h hUV) L
    (BenderBranch.isComponentIn_of_le hL (le_inf hLM hLH) inf_le_right)
  have hSL : IsSylowTwoOf (Q ⊓ L) L := isSylowTwoOf_inf_of_subnormal' hQH hLH hL.2.2
  have hcoreH : CFSG.pPrimeCore 2 ↥H = ⊥ := pPrimeCore_eq_bot_of_oddCoreIn' hO
  have hQ2' : IsPGroup 2 (Q.subgroupOf H) :=
    hQH.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hQH.1).symm
  set P : Sylow 2 ↥H := hQ2'.toSylow hQH.2.2 with hPdef
  have hVN : V ≤ Subgroup.normalizer (L : Set G) := by
    intro v hv
    have hvz : (⟨v, hVH hv⟩ : ↥H) ∈ Subgroup.centralizer ((P : Subgroup ↥H) : Set ↥H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hQV (show (y : G) ∈ Q from hy)) v hv).symm
    have hvzS : (⟨v, hVH hv⟩ : ↥H) ∈ (P : Subgroup ↥H) := show v ∈ Q from hVQ hv
    have hnorm := central_sylow_normalizes_components hcoreH P hvz hvzS hL.2
    have h2 : v ∈ (Subgroup.normalizer ((L.subgroupOf H : Subgroup ↥H) : Set ↥H)).map H.subtype :=
      ⟨_, hnorm, rfl⟩
    rw [map_subtype_normalizer hL.1] at h2
    exact h2.2
  refine ⟨hLM, hVN, hSL, ?_⟩
  obtain ⟨z, hzV, hzT, hz1⟩ : ∃ z ∈ V, z ∈ T ⊓ Subgroup.centralizer (T : Set G) ∧ z ≠ 1 := by
    have hT2 : IsPGroup 2 T := h.sylow.1
    have : Group.IsNilpotent T := hT2.isNilpotent
    have hnormal : (V.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer h.normal
    have hne : V.subgroupOf T ≠ ⊥ := by
      intro h0
      apply h.ne_bot
      rw [← Subgroup.map_subgroupOf_eq_of_le h.le, h0, Subgroup.map_bot]
    obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
    refine ⟨y, hy.1, ⟨y.2, Subgroup.mem_centralizer_iff.2 fun t ht =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)⟩, fun h1 => hy1 ?_⟩
    exact Subtype.ext (Subtype.ext h1)
  have hz2 : z ^ 2 = 1 := h.isElemAbelian.2 z hzV
  have hZ2 : IsPGroup 2 (Subgroup.zpowers z) := by
    rintro ⟨_, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    show (z ^ k) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz2, one_zpow]
  have hCz : Subgroup.centralizer ({z} : Set G) =
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) ⊓
        Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    ext g
    constructor
    · intro hg
      have hgz : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.1 hg
      have hgZ : g ∈ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨k, rfl⟩
        exact ((Commute.zpow_left hgz.symm k).symm).eq.symm
      exact ⟨Subgroup.centralizer_le_normalizer _ hgZ, hgZ⟩
    · rintro ⟨-, hg⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hg z (Subgroup.mem_zpowers z)).symm
  have hTsyl : IsSylowTwoOf T ⊤ :=
    ⟨le_top, h.sylow.1, by rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]; exact h.sylow.2⟩
  have hZT : Subgroup.zpowers z ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ := by
    intro h0
    apply hz1
    have : z ∈ Subgroup.zpowers z ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) :=
      ⟨Subgroup.mem_zpowers z, hzT⟩
    rw [h0] at this
    exact this
  have hNz := CT.charTwo_normalizer_of_inf_center h.qtke.2.1 hTsyl hZ2 hZT
  have hCz2 : CharTwo (Subgroup.centralizer ({z} : Set G)) := by
    rw [hCz]
    exact CT.CharTwo.inf_centralizer hNz Subgroup.le_normalizer hZ2
  have hzQ : z ∈ Q := hVQ hzV
  have hzC : z ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hUz : U ≤ pCoreOf 2 (H ⊓ Subgroup.centralizer ({z} : Set G)) := by
    refine C1.le_pCoreOf_of_normalized (le_inf (fun u hu => ?_) (fun u hu => ?_)) (fun g hg => ?_)
      (h.isPGroup_V.to_le hUV)
    · exact Subgroup.mem_centralizer_iff.2 fun u' hu' => hVc _ (hUV hu') _ (hUV hu)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hVc _ (hUV hu) _ hzV)
    · exact Subgroup.centralizer_le_normalizer _ hg.1
  have h115 : Lemma115Hyp H Q (Subgroup.centralizer ({z} : Set G)) z :=
    { pCore_ne_bot := fun h0 => hU.2.1 (le_bot_iff.1 (h0 ▸ (C1.le_pCoreOf_of_normalized
        (fun u hu => Subgroup.mem_centralizer_iff.2 fun u' hu' => hVc _ (hUV hu') _ (hUV hu))
        (Subgroup.centralizer_le_normalizer _) (h.isPGroup_V.to_le hUV))))
      sylow := hQH
      charTwo := hCz2
      pCore_M_ne_bot := fun h0 => hz1 (by
        have hle : Subgroup.zpowers z ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) :=
          C1.le_pCoreOf_of_normalized (Subgroup.zpowers_le.2 hzC) (by
            rw [hCz]; exact inf_le_left) hZ2
        have := hle (Subgroup.mem_zpowers z)
        rw [h0] at this
        exact this)
      le := fun q hq => Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 (hQV hq) z hzV).symm
      centralizer_le := fun g hg => Subgroup.centralizer_le hUz hg.2
      centralizer_z_le := le_rfl
      z_ne_one := hz1
      z_mem := hzQ
      z_central := Subgroup.mem_centralizer_iff.2 fun q hq =>
        (Subgroup.mem_centralizer_iff.1 (hQV hq) z hzV).symm
      z_sq := hz2 }
  obtain ⟨-, -, -, hcases⟩ := Lemma115_3_List.component_cases hlist h.simple h.nonabelian
    (qtkeCore_of_cat h.nonabelian h.qtke) h115 hL
  exact ⟨z, hcases⟩

end Setting

section Hyperplane

variable {G : Type} [Group G] [Finite G] {T M V U U₀ L : Subgroup G}

theorem isComponentIn_of_le_hyperplane (hlist : Lemma115_3_List) (h618 : E618Stmt)
    (h621 : E621Stmt) (hCent : E68CentComp) (hV : IsElemAbelian 2 V) (h : HypE61 T M V)
    (h15 : HypE615 hV M) (hm : 2 < E3.mParam (autI hV M)) (hUV : U ≤ V)
    (hU1 : E3.mQuot V U = 1) (hUM : ¬ Subgroup.centralizer (U : Set G) ≤ M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) (hU₀U : U₀ ≤ U) (hU₀1 : U₀ ≠ ⊥)
    (hU₀2 : E3.mQuot U U₀ ≤ 1) : IsComponentIn L (Subgroup.centralizer (U₀ : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.simple
  by_cases hUeq : U₀ = U
  · subst hUeq
    exact hL
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  have hU2 : IsPGroup 2 U := hV2.to_le hUV
  have hq1 : E3.mQuot U U₀ = 1 := by
    have h0 : E3.mQuot U U₀ ≠ 0 := fun h0 => hUeq ((E3.mQuot_eq_zero_iff hU2 hU₀U).1 h0)
    omega
  obtain ⟨u, huU, huU₀⟩ : ∃ u ∈ U, u ∉ U₀ := by
    by_contra hall
    push Not at hall
    exact hUeq (le_antisymm hU₀U hall)
  have hidx : U₀.relIndex U = 2 := by rw [E3.relIndex_eq_two_pow hU2, hq1, pow_one]
  have hCU := centralizer_eq_inf_of_relIndex_two hU₀U hidx huU huU₀
  set H₀ := Subgroup.centralizer (U₀ : Set G) with hH₀def
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hU₀V : U₀ ≤ V := hU₀U.trans hUV
  have hq2 : E3.mQuot V U₀ = 2 := by
    rw [E3.mQuot_add hU₀U hUV, hU1, hq1]
  have hH₀M : ¬ H₀ ≤ M := fun hle => hUM ((Subgroup.centralizer_le hU₀U).trans hle)
  have hU₀Γ : U₀ ∈ gammaE64 V M := mem_gammaE64_of_mQuot_lt hV h hU₀V hU₀1 hH₀M (by omega)
  have hO₀ : oddCoreIn H₀ = ⊥ := h621 G T M V U₀ hV h h15 hU₀V hU₀1
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm h.isElemAbelian ha hb
  have huV : u ∈ V := hUV huU
  have huH₀ : u ∈ H₀ := Subgroup.mem_centralizer_iff.2 fun w hw => hVc _ (hU₀V hw) _ huV
  have hu1 : u ≠ 1 := fun h1 => huU₀ (h1 ▸ U₀.one_mem)
  have hu2 : u ^ 2 = 1 := h.isElemAbelian.2 u huV
  have hq : QTKECore G := qtkeCore_of_cat h.nonabelian h.qtke
  have hpc : pCoreOf 2 H₀ ≠ ⊥ := by
    intro h0
    apply hU₀1
    refine le_bot_iff.1 (h0 ▸ C1.le_pCoreOf_of_normalized ?_ (Subgroup.centralizer_le_normalizer _)
      (hV2.to_le hU₀V))
    exact fun w hw => Subgroup.mem_centralizer_iff.2 fun w' hw' => hVc _ (hU₀V hw') _ (hU₀V hw)
  have hK : CFSG.SectionRank.IsKGroupCat ↥H₀ := (hq.1 H₀ hpc).2
  have hLq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hL2 : Id2519.IsTwoComponentIn L (H₀ ⊓ Subgroup.centralizer ({u} : Set G)) := by
    rw [← hCU]
    exact Id2519.isTwoComponentIn_of_isComponentIn hL (two_dvd_card_of_isQuasisimple hLq)
  have hQH₀ : IsSylowTwoOf Q H₀ := e6_5_one h hU₀Γ
  have hVQ : V ≤ Q := h.le_inf_centralizer
  have hQV : Q ≤ Subgroup.centralizer (V : Set G) := inf_le_right
  have hcore : CFSG.pPrimeCore 2 ↥H₀ = ⊥ := pPrimeCore_eq_bot_of_oddCoreIn' hO₀
  have hQ2' : IsPGroup 2 (Q.subgroupOf H₀) :=
    hQH₀.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hQH₀.1).symm
  set P : Sylow 2 ↥H₀ := hQ2'.toSylow hQH₀.2.2 with hPdef
  have hnormJ : ∀ J : Subgroup G, IsComponentIn J H₀ → u ∈ Subgroup.normalizer (J : Set G) := by
    intro J hJ
    have hvz : (⟨u, huH₀⟩ : ↥H₀) ∈ Subgroup.centralizer ((P : Subgroup ↥H₀) : Set ↥H₀) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hQV (show (y : G) ∈ Q from hy)) u huV).symm
    have hvzS : (⟨u, huH₀⟩ : ↥H₀) ∈ (P : Subgroup ↥H₀) := show u ∈ Q from hVQ huV
    have hnorm := central_sylow_normalizes_components hcore P hvz hvzS hJ.2
    have h2 : u ∈
        (Subgroup.normalizer ((J.subgroupOf H₀ : Subgroup ↥H₀) : Set ↥H₀)).map H₀.subtype :=
      ⟨_, hnorm, rfl⟩
    rw [map_subtype_normalizer hJ.1] at h2
    exact h2.2
  rcases I32.lemmaI32 G H₀ hK u huH₀ hu1 hu2 L hL2 with ⟨hY, -⟩ | ⟨J, hJ, hJne, -, -⟩
  swap
  · exact absurd ((BenderBranch.conjugate_eq_iff_mem_normalizer.2
      (hnormJ J (isComponentIn_of_isTwoComponentIn hJ hO₀))).symm) hJne
  set Y := ⨆ g ∈ Id2519.oddLayer H₀, CFSG.conjugate L g with hYdef
  have hYc : IsComponentIn Y H₀ := isComponentIn_of_isTwoComponentIn hY hO₀
  have hLY : L ≤ Y := by
    refine le_trans (le_of_eq (BenderBranch.conjugate_one L).symm) ?_
    exact le_iSup₂_of_le 1 (Subgroup.one_mem _) le_rfl
  have hLu : L ≤ Subgroup.centralizer ({u} : Set G) := by
    have h1 := hL.1
    rw [hCU] at h1
    exact h1.trans inf_le_right
  have hYuU : Y ⊓ Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer (U : Set G) := by
    rw [hCU]
    exact inf_le_inf_right _ hYc.1
  by_cases huY : u ∈ Subgroup.centralizer (Y : Set G)
  ·
    have hYu : Y ≤ Subgroup.centralizer ({u} : Set G) := fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 huY y hy)
    have hYCU : Y ≤ Subgroup.centralizer (U : Set G) := (le_inf le_rfl hYu).trans hYuU
    have hYc' : IsComponentIn Y (Subgroup.centralizer (U : Set G)) :=
      BenderBranch.isComponentIn_of_le hYc hYCU (Subgroup.centralizer_le hU₀U)
    rcases BenderBranch.eq_or_commute_of_isComponentIn hL hYc' with heq | hcomm
    · rw [heq]
      exact hYc
    · exfalso
      have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hLq.1
      have hbot : L = ⊥ := by
        rw [← hperf, eq_bot_iff, ← hcomm]
        exact Subgroup.commutator_mono le_rfl hLY
      have := CFSG.LocalCores.isQuasisimple_nontrivial hLq
      exact (Subgroup.nontrivial_iff_ne_bot L).mp this hbot
  ·
    exfalso
    obtain ⟨-, hVNY, hSY, z, hcases⟩ := e68_setting hlist h hU₀Γ hO₀ hYc
    set R := Q ⊓ Subgroup.normalizer (Y : Set G) with hRdef
    have hRY : R ⊓ Y = Q ⊓ Y := by
      rw [hRdef, inf_assoc, inf_eq_right.2 (Subgroup.le_normalizer : Y ≤ _)]
    have hE : E68CentHyp Y R u :=
      { quasisimple := BenderBranch.isQuasisimple_of_isComponentIn hYc
        isPGroup := hQH₀.2.1.to_le inf_le_left
        normalizer := inf_le_right
        sylow := by rw [hRY]; exact hSY
        mem := ⟨hVQ huV, hVNY huV⟩
        central := fun r hr => Subgroup.mem_centralizer_iff.1 (hQV hr.1) u huV
        sq := hu2
        not_mem := huY }
    have hLK : IsComponentIn L (Y ⊓ Subgroup.centralizer ({u} : Set G)) :=
      BenderBranch.isComponentIn_of_le hL (le_inf hLY hLu) hYuU
    obtain ⟨⟨φ, -, hZ, -, -⟩, -⟩ := hCent G Y R L z u hcases hE hLK
    exact h618 G T M V U₀ Y hV h h15 hU₀Γ (by omega) hYc ⟨⟨φ⟩, hZ⟩

end Hyperplane

end E6

end CFSG.Quasithin
