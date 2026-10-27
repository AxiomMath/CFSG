module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34QDiag
public import CFSG.Quasithin.Vol2.Ch12Sec2GlueIrr
public import CFSG.Quasithin.Vol2.Ch3Sec2IrrPlus
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QKer
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QKq
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QSec
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QTail

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Setup521

variable {D₃ Z₁ : Subgroup G} (s : Setup521 G T M L V H B D D₃ Z₁ n)
include s

theorem two_lt_qhatInt
    (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) (h510 : Stmt5_1_10)
    (h521 : Stmt5_1_21) (hD : D310L34Fact) (hB : B45L34Fact)
    (hnot : ¬ Concl5_1_14_four T L V B D n)
    (hU : IsElemAbelian 2 (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) H))) :
    (2 : WithTop ℚ) < qhatInt (tildeOf Z₁ H) (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) H))
      hU := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  have hHN := s.H_le_normalizer_Z₁ h5114
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hKN : oTwoUpper H ≤ Subgroup.normalizer (Z₁ : Set G) := hKH.trans hHN
  have hTH : T ≤ H := s.hyp.hyp.hStar.1.1
  have hTN : T ≤ Subgroup.normalizer (Z₁ : Set G) := hTH.trans hHN
  have hTsyl : IsSylowTwoOf T H := hh.isSylowTwoOf hTH
  set U := conjClosure (conjClosure Z₁ D₃) H with hUdef
  set Ut := tildeOf Z₁ U with hUtdef
  set Ht := tildeOf Z₁ H with hHtdef
  set Kt := tildeOf Z₁ (oTwoUpper H) with hKtdef
  set Tt := tildeOf Z₁ T with hTtdef
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure _ H
  have hHtU : Ht ≤ Subgroup.normalizer (Ut : Set _) := tildeOf_le_normalizer_tildeOf hHU
  have hKtHt : Kt ≤ Ht := tildeOf_mono hKH
  have hHtKt : Ht ≤ Subgroup.normalizer (Kt : Set _) :=
    tildeOf_le_normalizer_tildeOf (le_normalizer_oTwoUpper H)
  have hTtHt : Tt ≤ Ht := tildeOf_mono hTH
  have hTtKt : Tt ≤ Subgroup.normalizer (Kt : Set _) := hTtHt.trans hHtKt
  have hKtU : Kt ≤ Subgroup.normalizer (Ut : Set _) := hKtHt.trans hHtU
  have hTtU : Tt ≤ Subgroup.normalizer (Ut : Set _) := hTtHt.trans hHtU
  have hHt : Ht = Kt ⊔ Tt := by
    rw [hKtdef, hTtdef, ← tildeOf_sup hKN hTN, hHtdef]
    congr 1
    exact s.hyp.H_eq_sup
  have hTtsyl : IsSylowTwoOf Tt Ht := isSylowTwoOf_secImg hTsyl hHN s.Z₁_le_T
  have hTt2 : IsPGroup 2 ↥Tt := hTtsyl.2.1
  have hSH : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot hh.qtke hh.simple hh.nonabelian s.hyp.hyp.hStar.1.2
  have hSHt : SQTKGroup ↥Ht := by
    refine InternalSec.sqtkGroup_of_surjective (tildeRes Z₁ H hHN) (tildeRes_surjective hHN)
      ?_ hSH
    rintro ⟨x, hx⟩
    have hx1 : tildeRes Z₁ H hHN x = 1 := hx
    have hxZ : (x : G) ∈ Z₁ := by
      have h1 : tmk Z₁ ⟨x, hHN x.2⟩ = 1 := by
        have := congrArg Subtype.val hx1
        rwa [tildeRes_apply, OneMemClass.coe_one] at this
      exact (secMk_eq_one_iff (A := Subgroup.normalizer (Z₁ : Set G)) (B := Z₁)).mp h1
    have hx2 : (x : G) ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.mp (s.Z₁_le_Z hxZ)).2.2
    exact ⟨1, Subtype.ext (Subtype.ext (by simpa using hx2))⟩
  have hKtnot : ¬ Kt ≤ Subgroup.centralizer (Ut : Set _) := s.not_tildeOf_K_le_centralizer h5114 hF
  have hne : ⁅Ut, Kt⁆ ≠ ⊥ := fun hb => hKtnot
    (Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hb))
  have hO2Kt : ∀ N : Subgroup (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁), N ≤ Kt →
      (N.subgroupOf Kt).Normal → (∀ x ∈ Kt, ∃ k : ℕ, x ^ 2 ^ k ∈ N) → N = Kt := by
    intro N hNK _ h2
    refine le_antisymm hNK ?_
    have hK : oTwoUpper H ≤ (N.comap (tmk Z₁)).map (Subgroup.normalizer (Z₁ : Set G)).subtype := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨hyH, hyo⟩
      have hyK : y ∈ oTwoUpper H := mem_oTwoUpper_of_odd hyH hyo
      refine ⟨⟨y, hHN hyH⟩, ?_, rfl⟩
      obtain ⟨k, hk⟩ := h2 _ (secMk_mem_secImg (A := Subgroup.normalizer (Z₁ : Set G)) (B := Z₁)
        (x := ⟨y, hHN hyH⟩) hyK)
      have hdvd : orderOf (tmk Z₁ ⟨y, hHN hyH⟩) ∣ orderOf y := by
        have := orderOf_map_dvd (tmk Z₁) ⟨y, hHN hyH⟩
        rwa [Subgroup.orderOf_mk] at this
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime
        (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (Odd.of_dvd_nat hyo hdvd)) :
          Nat.Coprime (2 ^ k) (orderOf (tmk Z₁ ⟨y, hHN hyH⟩)))
      show tmk Z₁ ⟨y, hHN hyH⟩ ∈ N
      rw [← hm]
      exact N.pow_mem hk m
    rw [hKtdef]
    unfold tildeOf
    rw [secImg_le_iff]
    intro x hx
    obtain ⟨x', hx', hx'x⟩ := hK hx
    have : x' = x := Subtype.ext hx'x
    rw [← this]
    exact hx'
  have hR2 : ∀ x ∈ Ut, x * x = 1 := fun x hx => by rw [← sq]; exact hU.2 x hx
  have hSne : {I : Subgroup (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁) |
      IsIrrPlusBase Kt Ut I}.Nonempty := exists_irrPlusBase hO2Kt hR2 hKtU hne
  obtain ⟨I₀, hI₀, hmin⟩ := Set.exists_min_image _ (fun I => Nat.card ↥(conjClosure I Tt))
    (Set.toFinite _) hSne
  have hI₀U : I₀ ≤ Ut := hI₀.1
  have hVTU : conjClosure I₀ Tt ≤ Ut :=
    conjClosure_le fun t ht y hy => (Subgroup.mem_normalizer_iff.mp (hTtU ht) y).mp (hI₀U hy)
  have hKtVT : Kt ≤ Subgroup.normalizer (conjClosure I₀ Tt : Set _) :=
    le_normalizer_conjClosure_of_le hTtKt hI₀.2.2.1
  have hTtVT : Tt ≤ Subgroup.normalizer (conjClosure I₀ Tt : Set _) :=
    le_normalizer_conjClosure I₀ Tt
  have hVTab : IsElemAbelian 2 (conjClosure I₀ Tt) := isElemAbelian_mono hU hVTU
  have : IsMulCommutative ↥(conjClosure I₀ Tt) := hVTab.1
  obtain ⟨V₀, hV₀, -⟩ := exists_isIrrPlusIn_sectionIso hVTab.2 hKtVT hTtVT hTtKt hTt2
    ⟨le_conjClosure I₀ Tt, hI₀.2⟩
  have hV₀VT : V₀ ≤ conjClosure I₀ Tt := hV₀.1
  have hcl : conjClosure V₀ Tt ≤ conjClosure I₀ Tt :=
    conjClosure_le fun t ht y hy => (Subgroup.mem_normalizer_iff.mp (hTtVT ht) y).mp (hV₀VT hy)
  have hV₀base : IsIrrPlusBase Kt Ut V₀ :=
    ⟨hV₀VT.trans hVTU, hV₀.2.1, hV₀.2.2.1, hV₀.2.2.2.1, hV₀.2.2.2.2.1, hV₀.2.2.2.2.2.1⟩
  have hceq : conjClosure V₀ Tt = conjClosure I₀ Tt :=
    Subgroup.eq_of_le_of_card_ge hcl (hmin V₀ hV₀base)
  rw [← hceq] at hV₀
  have hWU : conjClosure V₀ Tt ≤ Ut := hceq ▸ hVTU
  have hHtW : Ht ≤ Subgroup.normalizer (conjClosure V₀ Tt : Set _) := by
    rw [hHt, hceq]; exact sup_le hKtVT hTtVT
  have hKtW : ¬ Kt ≤ Subgroup.centralizer (conjClosure V₀ Tt : Set _) := by
    intro hc
    apply hV₀.2.1
    rw [← hV₀.2.2.2.1, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff.mp
      (hc.trans (Subgroup.centralizer_le (le_conjClosure V₀ Tt)))
  have hWab : IsElemAbelian 2 (conjClosure V₀ Tt) := isElemAbelian_mono hU hWU
  have htail := two_lt_qhatInt_of_irrPlusIn hD hB hSHt hTtsyl hKtHt hHtKt hHt hV₀ hWab
    (s.pCoreOf_autOn_eq_bot hWU hHtW hKtW h5114 h521 hnot)
    (s.lieModel_autOn hWU hHtW hKtW h5114 h521 hnot)
    (s.isPGroup_inf_centralizer hWU hHtW hKtW h5114 h521 hnot)
    (isDiagramNontrivial_tildeOf hHN hKH (le_normalizer_oTwoUpper H) hTsyl s.Z₁_le_T
      (s.hyp.isDiagramNontrivial h510))
  by_contra hle
  rw [not_lt] at hle
  let := commGroupOfElemAbelian hU
  have hV : ∀ v : ↥Ut, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hU.2 v v.2)
  have hle' : qhatOf (autOn Ht Ut) ≤ (2 : WithTop ℚ) := hle
  have h2top : (2 : WithTop ℚ) ≠ ⊤ := by simp
  obtain ⟨r, hr'⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top h2top hle')
  have hr : qhatOf (autOn Ht Ut) = (r : WithTop ℚ) := hr'.symm
  have hr2 : r ≤ 2 := by
    rw [hr] at hle'
    have : ((r : ℚ) : WithTop ℚ) ≤ ((2 : ℚ) : WithTop ℚ) := by simpa using hle'
    exact WithTop.coe_le_coe.mp this
  obtain ⟨A, hA⟩ := QhatStar_nonempty hr hr2
  obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  have hX : autOn Ht Ut ≤ stabSub ((conjClosure V₀ Tt).subgroupOf Ut) := by
    intro x hx u
    obtain ⟨g, hgY, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_subgroupOf] at hgY
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, conjAct_coe_apply]
    have h1 := Subgroup.mem_normalizer_iff.mp (hHtW hgY) (u : SecQuot _ _)
    exact ⟨fun h => h1.mpr h, fun h => h1.mp h⟩
  have hfaith : autOn Ht Ut ⊓ centSub ((conjClosure V₀ Tt).subgroupOf Ut) = ⊥ := by
    rw [eq_bot_iff]
    rintro φ ⟨hφX, hφC⟩
    obtain ⟨⟨y, hyN⟩, hyH, rfl⟩ := Subgroup.mem_map.mp hφX
    rw [Subgroup.mem_subgroupOf] at hyH
    obtain ⟨h, hh, rfl⟩ := mem_secImg.mp hyH
    have hc : tmk Z₁ h ∈ Subgroup.centralizer (conjClosure V₀ Tt : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h1 := congrArg Subtype.val (hφC ⟨w, hWU hw⟩ hw)
      rw [conjAct_coe_apply] at h1
      have h2 := congrArg (· * tmk Z₁ h) h1
      simpa [mul_assoc] using h2.symm
    have hhO := s.mem_pCoreOf_of_mem_centralizer h5114 hHtW hKtW hh h.2 hc
    have hcU := s.tildeOf_pCoreOf_le_centralizer h5114 h521 hnot
      (secMk_mem_secImg (A := Subgroup.normalizer (Z₁ : Set G)) (B := Z₁) (x := h) hhO)
    rw [Subgroup.mem_bot]
    ext u
    rw [conjAct_coe_apply, MulAut.one_apply]
    have hcu := Subgroup.mem_centralizer_iff.mp hcU (u : SecQuot _ _) u.2
    rw [← hcu, mul_inv_cancel_right]
  have hcommA : commSub ((conjClosure V₀ Tt).subgroupOf Ut) A ≠ ⊥ := by
    rw [Ne, commSub_eq_bot_iff]
    intro hfix
    apply hA2.2.1
    rw [eq_bot_iff]
    intro a ha
    have : a ∈ autOn Ht Ut ⊓ centSub ((conjClosure V₀ Tt).subgroupOf Ut) :=
      ⟨hA2.1 ha, fun u hu => hfix hu a ha⟩
    rw [hfaith] at this
    exact this
  have h27 := qhatOf_autSub_le_of_mem_QhatStar hV hr hA (hA2.1.trans hX) hcommA
  have htrans := qhatInt_le_qhatOf_autSub hU hWU hHtW
  have hlt : (2 : WithTop ℚ) < (r : WithTop ℚ) := lt_of_lt_of_le htail (htrans.trans h27)
  have hr2' : (r : WithTop ℚ) ≤ (2 : WithTop ℚ) := by
    have : ((r : ℚ) : WithTop ℚ) ≤ ((2 : ℚ) : WithTop ℚ) := WithTop.coe_le_coe.mpr hr2
    simpa using this
  exact absurd hlt (not_lt.mpr hr2')

end Setup521

end CFSG.Quasithin.H13
