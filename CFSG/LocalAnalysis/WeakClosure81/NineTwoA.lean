module

public import CFSG.LocalAnalysis.WeakClosure81.NineOne
public import CFSG.LocalAnalysis.WeakClosure81.NineCalP

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.LieType.BorelTits Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V K S X : Subgroup G} {p : ℕ}

private def nineTwoA_ncl (K Y : Subgroup G) : Subgroup G :=
  ⨆ k : ↥K, CFSG.Quasithin.conjSubgroup Y (k : G)

private theorem nineTwoA_conjSubgroup_le_of_le {A B : Subgroup G} (h : A ≤ B) {k : G}
    (hk : k ∈ B) : CFSG.Quasithin.conjSubgroup A k ≤ B := by
  intro x hx
  rw [CFSG.Quasithin.mem_conjSubgroup_iff] at hx
  exact (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hk) x).mpr (h hx)

private theorem nineTwoA_conj_smul_eq (g : G) (X : Subgroup G) :
    MulAut.conj g • X = CFSG.Quasithin.conjSubgroup X g⁻¹ := by
  rw [show MulAut.conj g • X = CFSG.CGT.Timmesfeld75.conjSubgroup g X from rfl]
  exact t75_conjSubgroup_eq X g

private theorem nineTwoA_ncl_conj_mem {K Y : Subgroup G} (hYK : Y ≤ K) {k₀ : G}
    (hk₀ : k₀ ∈ K) {x : G} (hx : x ∈ nineTwoA_ncl K Y) :
    k₀ * x * k₀⁻¹ ∈ nineTwoA_ncl K Y := by
  rw [nineTwoA_ncl] at hx ⊢
  refine Subgroup.iSup_induction (fun k : ↥K => CFSG.Quasithin.conjSubgroup Y (k : G))
    (C := fun m => k₀ * m * k₀⁻¹ ∈ nineTwoA_ncl K Y) hx (fun k m hm => ?_)
    (by simp) (fun m n hm hn => ?_)
  · have h1 : k₀ * m * k₀⁻¹ ∈ CFSG.Quasithin.conjSubgroup
        (CFSG.Quasithin.conjSubgroup Y (k : G)) k₀⁻¹ := by
      rw [CFSG.Quasithin.mem_conjSubgroup_iff]
      have heq : k₀⁻¹ * (k₀ * m * k₀⁻¹) * (k₀⁻¹)⁻¹ = m := by group
      rw [heq]
      exact hm
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup] at h1
    rw [nineTwoA_ncl]
    exact Subgroup.mem_iSup_of_mem
      (S := fun k : ↥K => CFSG.Quasithin.conjSubgroup Y (k : G))
      ⟨(k : G) * k₀⁻¹, K.mul_mem k.2 (K.inv_mem hk₀)⟩ h1
  · rw [show k₀ * (m * n) * k₀⁻¹ = k₀ * m * k₀⁻¹ * (k₀ * n * k₀⁻¹) by group]
    exact mul_mem hm hn

private theorem nineTwoA_le_ncl (K Y : Subgroup G) : Y ≤ nineTwoA_ncl K Y := by
  rw [nineTwoA_ncl]
  have h : CFSG.Quasithin.conjSubgroup Y (((1 : ↥K) : G)) ≤
      ⨆ k : ↥K, CFSG.Quasithin.conjSubgroup Y (k : G) :=
    le_iSup (fun k : ↥K => CFSG.Quasithin.conjSubgroup Y (k : G)) 1
  simpa [CFSG.Quasithin.conjSubgroup_one] using h

private theorem nineTwoA_ncl_le {K Y : Subgroup G} (hYK : Y ≤ K) : nineTwoA_ncl K Y ≤ K := by
  rw [nineTwoA_ncl]
  exact iSup_le fun k => nineTwoA_conjSubgroup_le_of_le hYK k.2

private theorem nineTwoA_le_normalizer_ncl {K Y : Subgroup G} (hYK : Y ≤ K) :
    K ≤ normalizer (nineTwoA_ncl K Y : Set G) := by
  intro k₀ hk₀
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact nineTwoA_ncl_conj_mem hYK hk₀ hx
  · intro hx
    have h' : k₀⁻¹ * (k₀ * x * k₀⁻¹) * (k₀⁻¹)⁻¹ ∈ nineTwoA_ncl K Y :=
      nineTwoA_ncl_conj_mem hYK (K.inv_mem hk₀) hx
    have heq : k₀⁻¹ * (k₀ * x * k₀⁻¹) * (k₀⁻¹)⁻¹ = x := by group
    rwa [heq] at h'

private theorem nineTwoA_ncl_normal {K Y : Subgroup G} (hYK : Y ≤ K) :
    ((nineTwoA_ncl K Y).subgroupOf K).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (nineTwoA_ncl_le hYK)).mpr
    (nineTwoA_le_normalizer_ncl hYK)

private theorem nineTwoA_X_le_twoResidual (h : TwoPTwo K S X p) : X ≤ twoResidual K := by
  intro x hxX
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨c, hc⟩ := h.sylowP.isPGroup.exists_orderOf_eq_pow ⟨x, hxX⟩
  have hord : orderOf x = p ^ c := (Subgroup.orderOf_mk x hxX).symm.trans hc
  refine F6.mem_twoResidual_of_odd (h.sylowP.le hxX) ?_
  rw [hord]
  exact (h.prime.odd_of_ne_two h.odd).pow

private theorem nineTwoA_isElemAbelian_of_mem_omegaSet {V H E U : Subgroup G}
    (hV : IsElemAbelian 2 V) (hU : U ∈ omegaSet V H E) : IsElemAbelian 2 U := by
  obtain ⟨g, rfl, -, -⟩ := mem_omegaSet.mp hU
  exact isElemAbelian_conjSubgroup' hV g

theorem ne_of_mem_nineOmegaIn (hV : IsElemAbelian 2 V) (h : Nine1Hyp V K S X p) {A : Subgroup G}
    (hA : A ∈ nineOmegaIn V K S) : A ≠ V := by
  intro hAV
  rw [hAV] at hA
  obtain ⟨g, -, -, hAnotR⟩ := mem_omegaSet.mp hA.1
  exact hAnotR (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (hA.2.trans h.sylowTwo.le) h.le (B2F.isPGroup_of_isElemAbelian hV))

theorem nine_two_one (hV : Hyp7 V) (hm : 2 < rk ↥V) (h : Nine2Hyp V K S X p) :
    (∀ B : Subgroup G, IsGConj V B → B ≤ pCoreOf 2 K → B = V) ∧
      ∀ B : Subgroup G, IsGConj V B → B ≤ S → B ∈ nineOmegaIn V K S ∨ B = V := by
  have h3 : NineOneThree V K := by
    rcases nine_one hV hm h.base with h1 | h2 | h3
    · exact absurd h1 h.notW
    · exact absurd h2 h.notC
    · exact h3
  have hfirst : ∀ B : Subgroup G, IsGConj V B → B ≤ pCoreOf 2 K → B = V := by
    intro B hBconj hBR
    by_contra hBne
    obtain ⟨g, hBg⟩ := hBconj
    have hBg_ne : CFSG.Quasithin.conjSubgroup V g ≠ V := by rwa [hBg] at hBne
    have hg : g ∉ normalizer (V : Set G) := fun hg =>
      hBg_ne ((CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer).2 hg)
    have hBcard : Nat.card B = Nat.card V := by rw [hBg, card_conjSubgroup']
    have hBne_bot : B ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card V = 1 := by rw [← hBcard, hbot, Subgroup.card_bot]
      have h2 : 2 < 1 := h1 ▸ hV.2.1
      exact absurd h2 (by norm_num)
    obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne_bot
    have hbB : (b : G) ∈ B := b.2
    have hb1' : (b : G) ≠ 1 := fun hb => hb1 (Subtype.ext hb)
    have hcomm : ⁅twoResidual K, B⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact h3.2 B ⟨g, hBg⟩ hBR
    have htwo : twoResidual K ≤ Subgroup.centralizer (B : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm
    have htwo_b : twoResidual K ≤ Subgroup.centralizer ({(b : G)} : Set G) :=
      htwo.trans (Subgroup.centralizer_le fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        rwa [hx])
    have hbBconj : (b : G) ∈ CFSG.Quasithin.conjSubgroup V g := hBg ▸ hbB
    have hnorm : Subgroup.centralizer ({(b : G)} : Set G) ≤
        normalizer (CFSG.Quasithin.conjSubgroup V g : Set G) :=
      centralizer_le_normalizer_conj hV.2.2 g hbBconj hb1'
    have htwo_norm : twoResidual K ≤
        normalizer (CFSG.Quasithin.conjSubgroup V g : Set G) :=
      htwo_b.trans hnorm
    have hXtwo : X ≤ twoResidual K :=
      nineTwoA_X_le_twoResidual h.base.toTwoPTwoIrred.toTwoPTwo
    have hXle : X ≤ CFSG.Quasithin.conjSubgroup (normalizer (V : Set G)) g := by
      rw [conjSubgroup_normalizer]
      exact hXtwo.trans htwo_norm
    obtain ⟨q, hq, hq2, hXq, hXM, hXG, hXtriv⟩ := h.mem
    have hAleM : CFSG.Quasithin.conjSubgroup V g ≤ normalizer (V : Set G) := by
      rw [← hBg]
      exact hBR.trans ((pCoreOf_le 2 K).trans h.base.le)
    have hbot : X ⊓ CFSG.Quasithin.conjSubgroup (normalizer (V : Set G)) g = ⊥ :=
      hXtriv g hg hAleM
    have hXbot : X ≤ ⊥ := by
      have := le_inf le_rfl hXle
      rwa [hbot] at this
    have hXeq : X = ⊥ := le_bot_iff.mp hXbot
    have hXne : X ≠ ⊥ := by
      intro hXb
      have hlt := h.base.irred.1
      rw [hXb] at hlt
      exact (not_le_of_gt hlt) bot_le
    exact hXne hXeq
  refine ⟨hfirst, ?_⟩
  intro B hBconj hBS
  have hBK : B ≤ K := hBS.trans h.base.sylowTwo.le
  rcases h3.1 B hBconj hBK with hBomega | hBR
  · left
    exact ⟨hBomega.1, hBS⟩
  · right
    exact hfirst B hBconj hBR

theorem exists_mem_nineOmegaIn (hV : Hyp7 V) (hm : 2 < rk ↥V) (h : Nine2Hyp V K S X p) :
    ∃ A : Subgroup G, A ∈ nineOmegaIn V K S := by
  have hnotall : ¬ ∀ B : Subgroup G, IsGConj V B → B ≤ S → B ≤ pCoreOf 2 K := by
    intro hall
    exact h.notW (le_normalizer_wClos_zero_of_forall_le hV.1 h.base.toTwoPTwoIrred.toTwoPTwo
      hall)
  push Not at hnotall
  obtain ⟨B, hBconj, hBS, hBnR⟩ := hnotall
  rcases (nine_two_one hV hm h).2 B hBconj hBS with hBomega | hBVe
  · exact ⟨B, hBomega⟩
  · exfalso
    have hVK : V ≤ K := hBVe ▸ (hBS.trans h.base.sylowTwo.le)
    have hVcore : V ≤ pCoreOf 2 K :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVK h.base.le
        (B2F.isPGroup_of_isElemAbelian hV.1)
    exact hBnR (hBVe ▸ hVcore)

theorem nine_two_transitive (hV : Hyp7 V) (hm : 2 < rk ↥V) (h : TwoPTwoIrred K S X p) :
    ∀ U ∈ omegaIn V K (nineE V K), ∀ U' ∈ omegaIn V K (nineE V K),
      ∃ k ∈ K, U' = conjSubgroup U k := by
  intro U hU U' hU'
  by_contra hno
  push Not at hno
  have hEab : IsMulCommutative (nineE V K) := (isElemAbelian_nineE V K).1
  have hcomm_gen : ∀ k ∈ K, ∀ l ∈ K, ∀ u ∈ CFSG.Quasithin.conjSubgroup U k,
      ∀ v ∈ CFSG.Quasithin.conjSubgroup U' l, u * v = v * u := by
    intro k hk l hl u hu v hv
    have hUk : CFSG.Quasithin.conjSubgroup U k ∈ omegaIn V K (nineE V K) :=
      conjSubgroup_mem_omegaIn hU hk
    have hU'l : CFSG.Quasithin.conjSubgroup U' l ∈ omegaIn V K (nineE V K) :=
      conjSubgroup_mem_omegaIn hU' hl
    obtain ⟨a, b, ha, hb, hN⟩ :=
      nVSub_conj_ne_bot_of_mem_omegaSet hV.2.2 hEab hUk.1 hU'l.1
    have hN' : CFSG.Quasithin.conjSubgroup U k ⊓
        normalizer (CFSG.Quasithin.conjSubgroup U' l : Set G) ≠ ⊥ := by
      rw [ha, hb]
      exact hN
    rcases two_conj_eq_or_comm hV.1 hV.2.2 ⟨a, ha⟩ ⟨b, hb⟩ hN' with
      hcomm | ⟨y, hy, hyeq⟩
    · exact hcomm u hu v hv
    · exfalso
      have hyK : y ∈ K := (sup_le hUk.2 hU'l.2) hy
      have hconj : CFSG.Quasithin.conjSubgroup U' l =
          CFSG.Quasithin.conjSubgroup U (k * y) := by
        rw [hyeq, CFSG.Quasithin.conjSubgroup_conjSubgroup]
      have hU'eq : U' = CFSG.Quasithin.conjSubgroup U (k * y * l⁻¹) := by
        have h1 : CFSG.Quasithin.conjSubgroup (CFSG.Quasithin.conjSubgroup U' l) l⁻¹ = U' := by
          rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel,
            CFSG.Quasithin.conjSubgroup_one]
        calc U' = CFSG.Quasithin.conjSubgroup
              (CFSG.Quasithin.conjSubgroup U' l) l⁻¹ := h1.symm
          _ = CFSG.Quasithin.conjSubgroup
              (CFSG.Quasithin.conjSubgroup U (k * y)) l⁻¹ := by rw [hconj]
          _ = CFSG.Quasithin.conjSubgroup U (k * y * l⁻¹) := by
                rw [CFSG.Quasithin.conjSubgroup_conjSubgroup]
      have hmem : k * y * l⁻¹ ∈ K := K.mul_mem (K.mul_mem hk hyK) (K.inv_mem hl)
      exact hno (k * y * l⁻¹) hmem hU'eq
  have hUK : U ≤ K := hU.2
  have hU'K : U' ≤ K := hU'.2
  have hK₁K : nineTwoA_ncl K U ≤ K := nineTwoA_ncl_le hUK
  have hK₂K : nineTwoA_ncl K U' ≤ K := nineTwoA_ncl_le hU'K
  have hK₁norm : ((nineTwoA_ncl K U).subgroupOf K).Normal := nineTwoA_ncl_normal hUK
  have hK₂norm : ((nineTwoA_ncl K U').subgroupOf K).Normal := nineTwoA_ncl_normal hU'K
  have hUleK₁ : U ≤ nineTwoA_ncl K U := nineTwoA_le_ncl K U
  have hU'leK₂ : U' ≤ nineTwoA_ncl K U' := nineTwoA_le_ncl K U'
  have hcomm12 : nineTwoA_ncl K U ≤ Subgroup.centralizer (nineTwoA_ncl K U' : Set G) := by
    rw [nineTwoA_ncl]
    refine iSup_le fun k => ?_
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [nineTwoA_ncl] at hz
    refine Subgroup.iSup_induction
      (fun l : ↥K => CFSG.Quasithin.conjSubgroup U' (l : G))
      (C := fun z => z * w = w * z) hz
      (fun l z hz => ?_) (by simp) (fun x y hx hy => ?_)
    · exact (hcomm_gen (k : G) k.2 (l : G) l.2 w hw z hz).symm
    · rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  obtain ⟨-, -, -, hUnR⟩ := mem_omegaSet.mp hU.1
  obtain ⟨-, -, -, hU'nR⟩ := mem_omegaSet.mp hU'.1
  have hU2 : IsPGroup 2 U :=
    B2F.isPGroup_of_isElemAbelian (nineTwoA_isElemAbelian_of_mem_omegaSet hV.1 hU.1)
  have hU'2 : IsPGroup 2 U' :=
    B2F.isPGroup_of_isElemAbelian (nineTwoA_isElemAbelian_of_mem_omegaSet hV.1 hU'.1)
  have hnotK₁ : ¬ nineTwoA_ncl K U ≤ nineFrattiniR K X := by
    intro hle
    exact (TwoPTwo.not_le_frattiniR_of_isPGroup h.toTwoPTwo hUK hU2 hUnR)
      (hUleK₁.trans hle)
  have hnotK₂ : ¬ nineTwoA_ncl K U' ≤ nineFrattiniR K X := by
    intro hle
    exact (TwoPTwo.not_le_frattiniR_of_isPGroup h.toTwoPTwo hU'K hU'2 hU'nR)
      (hU'leK₂.trans hle)
  have hres₁ : twoResidual K ≤ nineTwoA_ncl K U :=
    TwoPTwoIrred.twoResidual_le_of_not_le_frattiniR h hK₁K hK₁norm hnotK₁
  have hres₂ : twoResidual K ≤ nineTwoA_ncl K U' :=
    TwoPTwoIrred.twoResidual_le_of_not_le_frattiniR h hK₂K hK₂norm hnotK₂
  have hXtwo : X ≤ twoResidual K := nineTwoA_X_le_twoResidual h.toTwoPTwo
  have hUcentX : ∀ u ∈ U, ∀ x ∈ X, u * x = x * u := by
    intro u hu x hxX
    have huK₁ : u ∈ nineTwoA_ncl K U := hUleK₁ hu
    have hxK₂ : x ∈ nineTwoA_ncl K U' := hres₂ (hXtwo hxX)
    exact (Subgroup.mem_centralizer_iff.mp (hcomm12 huK₁) x hxK₂).symm
  have hUpCore : U ≤ pCoreOf 2 K := by
    intro u hu
    have hcomm : ∀ x ∈ X, ⁅u, x⁆ ∈ pCoreOf 2 K := by
      intro x hxX
      have h1 : ⁅u, x⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (hUcentX u hu x hxX)
      rw [h1]
      exact (pCoreOf 2 K).one_mem
    have husup : u ∈ pCoreOf 2 K ⊔ X :=
      TwoPTwo.mem_sup_of_commutator_mem h.toTwoPTwo (hUK hu) hcomm
    have hu2 : u ^ 2 ^ 1 = 1 := by
      have h := (nineTwoA_isElemAbelian_of_mem_omegaSet hV.1 hU.1).2 u hu
      simpa using h
    exact TwoPTwo.mem_pCoreOf_of_mem_sup h.toTwoPTwo husup hu2
  exact hUnR hUpCore

theorem isPGroup_normalizer_inf (hV : Hyp7 V) (h : Nine2Hyp V K S X p) {A : Subgroup G}
    (hA : A ∈ nineOmegaIn V K S) : IsPGroup 2 ↥(K ⊓ normalizer (A : Set G)) := by
  obtain ⟨g, hAeq, -, -⟩ := mem_omegaSet.mp hA.1
  have hAneV : A ≠ V := ne_of_mem_nineOmegaIn hV.1 h.base hA
  have hg_ne : g ∉ normalizer (V : Set G) := by
    intro hg
    exact hAneV (by rw [hAeq, CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer]; exact hg)
  have hAleM : CFSG.Quasithin.conjSubgroup V g ≤ normalizer (V : Set G) := by
    rw [← hAeq]
    exact hA.2.trans (h.base.sylowTwo.le.trans h.base.le)
  have hnormA : normalizer (A : Set G) =
      CFSG.Quasithin.conjSubgroup (normalizer (V : Set G)) g := by
    rw [hAeq, ← conjSubgroup_normalizer]
  haveI : Fact p.Prime := ⟨h.base.prime⟩
  have hclaim : ∀ z : ↥(K ⊓ normalizer (A : Set G)), Odd (orderOf z) → z = 1 := by
    intro z hzodd
    have hzK : (z : G) ∈ K := z.2.1
    have hzN : (z : G) ∈ normalizer (A : Set G) := z.2.2
    have hzodd' : Odd (orderOf (z : G)) := (Subgroup.orderOf_mk (z : G) z.2) ▸ hzodd
    have hsup : (z : G) ∈ pCoreOf 2 K ⊔ X :=
      TwoPTwo.mem_sup_of_odd_orderOf h.base.toTwoPTwoIrred.toTwoPTwo hzK hzodd'
    let KG := ↥K
    let R0 : Subgroup KG := (pCoreOf 2 K).subgroupOf K
    haveI hR0normal : R0.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 K)).mpr
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
    let π : KG →* KG ⧸ R0 := QuotientGroup.mk' R0
    have hXR : X ≤ normalizer (pCoreOf 2 K : Set G) :=
      h.base.sylowP.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
    have hzmem : (z : G) ∈ (pCoreOf 2 K : Set G) * (X : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left (pCoreOf 2 K) X hXR]
      exact hsup
    obtain ⟨r, hrR, x, hxX, hrx⟩ := hzmem
    have hrK : r ∈ K := pCoreOf_le 2 K hrR
    have hxK : x ∈ K := h.base.sylowP.le hxX
    have hzKG : (⟨(z : G), hzK⟩ : KG) = (⟨r, hrK⟩ : KG) * (⟨x, hxK⟩ : KG) :=
      Subtype.ext hrx.symm
    have hr1 : π ⟨r, hrK⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hrR)
    have hπz : π ⟨(z : G), hzK⟩ = π ⟨x, hxK⟩ := by
      rw [hzKG, map_mul, hr1, one_mul]
    have hxpow : (⟨x, hxK⟩ : KG) ^ Nat.card X = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, Subgroup.orderOf_mk x hxK]
      exact Subgroup.orderOf_dvd_natCard X hxX
    have hπxpow : (π ⟨x, hxK⟩) ^ Nat.card X = 1 := by
      rw [← map_pow, hxpow, map_one]
    have hπzpow : (π ⟨(z : G), hzK⟩) ^ Nat.card X = 1 := by
      rw [hπz]
      exact hπxpow
    have hzR : (z : G) ^ Nat.card X ∈ pCoreOf 2 K := by
      have h1 : π (⟨(z : G), hzK⟩ ^ Nat.card X) = 1 := by
        rw [map_pow, hπzpow]
      have h2 : (⟨(z : G), hzK⟩ : KG) ^ Nat.card X ∈ R0 :=
        (QuotientGroup.eq_one_iff _).mp h1
      simpa using Subgroup.mem_subgroupOf.mp h2
    have hzpow1 : (z : G) ^ Nat.card X = 1 := by
      obtain ⟨n, hn⟩ :=
        CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨(z : G) ^ Nat.card X, hzR⟩
      have h2 : ((z : G) ^ Nat.card X) ^ 2 ^ n = 1 := by
        have hv := congrArg Subtype.val hn
        simpa using hv
      have hdvd2 : orderOf ((z : G) ^ Nat.card X) ∣ 2 ^ n :=
        orderOf_dvd_of_pow_eq_one h2
      have hodd : Odd (orderOf ((z : G) ^ Nat.card X)) :=
        Odd.of_dvd_nat hzodd' (orderOf_pow_dvd (x := (z : G)) (Nat.card X))
      exact orderOf_eq_one_iff.mp
        (((Nat.coprime_two_right.mpr hodd).pow_right n).eq_one_of_dvd hdvd2)
    have hYp : IsPGroup p (Subgroup.zpowers (z : G)) := by
      obtain ⟨c, hc⟩ := h.base.sylowP.isPGroup.exists_card_eq
      refine IsPGroup.of_card_dvd_pow (n := c) ?_
      rw [Nat.card_zpowers]
      exact hc ▸ orderOf_dvd_of_pow_eq_one hzpow1
    have hYK : Subgroup.zpowers (z : G) ≤ K := Subgroup.zpowers_le.mpr hzK
    have hYpK : IsPGroup p ((Subgroup.zpowers (z : G)).subgroupOf K) :=
      hYp.of_equiv (Subgroup.subgroupOfEquivOfLe hYK).symm
    obtain ⟨Q, hQ⟩ := hYpK.exists_le_sylow
    obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (↥K) h.base.sylowP.toSylow Q
    have hyQ : (⟨(z : G), hzK⟩ : ↥K) ∈ Q :=
      hQ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers (z : G)))
    rw [← hk] at hyQ
    change (⟨(z : G), hzK⟩ : ↥K) ∈
      ((k • h.base.sylowP.toSylow : Sylow p ↥K) : Subgroup ↥K) at hyQ
    rw [Sylow.coe_subgroup_smul] at hyQ
    rw [IsSylowIn.coe_toSylow] at hyQ
    rw [Subgroup.conj_smul_subgroupOf h.base.sylowP.le k] at hyQ
    have hyMul : (z : G) ∈ MulAut.conj (k : G) • X :=
      Subgroup.mem_subgroupOf.mp hyQ
    have hyconj : (z : G) ∈ CFSG.Quasithin.conjSubgroup X (k : G)⁻¹ := by
      rwa [nineTwoA_conj_smul_eq] at hyMul
    have hkM : (k : G) ∈ normalizer (V : Set G) := h.base.le k.2
    have hXk_calP : CFSG.Quasithin.conjSubgroup X (k : G)⁻¹ ∈ calP V :=
      calP_conj h.mem ((normalizer (V : Set G)).inv_mem hkM)
    obtain ⟨q, hq, hq2, hXq, hXM, hXG, hXtriv⟩ := hXk_calP
    have hbot : CFSG.Quasithin.conjSubgroup X (k : G)⁻¹ ⊓
        CFSG.Quasithin.conjSubgroup (normalizer (V : Set G)) g = ⊥ :=
      hXtriv g hg_ne hAleM
    have hzN' : (z : G) ∈ CFSG.Quasithin.conjSubgroup (normalizer (V : Set G)) g := by
      rw [← hnormA]
      exact hzN
    have hzbot : (z : G) ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact ⟨hyconj, hzN'⟩
    exact Subtype.ext (Subgroup.mem_bot.mp hzbot)
  rw [isPGroup_iff_pow_pow_eq_one]
  intro y
  obtain ⟨a, m, hm_odd, horder⟩ :=
    Nat.exists_eq_two_pow_mul_odd (n := orderOf y) (orderOf_pos y).ne'
  refine ⟨a, ?_⟩
  have hpow : (y ^ 2 ^ a) ^ m = 1 := by
    rw [← pow_mul, ← horder, pow_orderOf_eq_one]
  have hdiv : orderOf (y ^ 2 ^ a) ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hpow
  have hodd : Odd (orderOf (y ^ 2 ^ a)) := Odd.of_dvd_nat hm_odd hdiv
  exact hclaim (y ^ 2 ^ a) hodd

end CFSG.LocalAnalysis.WeakClosure81
