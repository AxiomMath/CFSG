module

public import CFSG.Quasithin.EmptyFaithful.S152U19
public import CFSG.Quasithin.Vol2.Ch1Residual
public import CFSG.Quasithin.Background.C2Nine
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem opResidual_two_oTwoUpper152 (X : Subgroup G) :
    opResidual 2 (oTwoUpper X) = oTwoUpper X := by
  refine le_antisymm (opResidual_le 2 _) ?_
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  exact mem_opResidual_of_coprime (Subgroup.subset_closure hx) (Nat.coprime_two_right.mpr hx.2)

omit [Finite G] in
theorem isPGroup_of_isElemAbelian152 {E : Subgroup G} (h : IsElemAbelian 2 E) : IsPGroup 2 E :=
  CFSG.Open.IsElemAbelian.isPGroup h

theorem pRank_pCoreOf_le_two152 {T Mc : Subgroup G} (hq : quasithinQTFE14Cat G T Mc)
    {H : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (pCoreOf p H) ≤ 2 := fun p hp hp2 =>
  (CFSG.SectionRank.pRank_mono hp.one_lt (CFSG.LieType.BorelTits.pCoreOf_le p H)).trans
    (pRank_le_two_of_pCoreOf_ne_bot hq.qtke hH hp hp2)

section Main

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I : Subgroup G}

theorem exists_z152 (hD : Inputs152 T Mc M H B₀ I) :
    ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : quasithinOmegaOneCenter T = ⊥ := eq_bot_iff.mpr fun z hz =>
    Subgroup.mem_bot.mpr (hcon z hz)
  have h2 := hD.h17.2.1
  rw [this, Subgroup.card_bot] at h2
  omega

theorem centralizer_z_le_Mc152 (hD : Inputs152 T Mc M H B₀ I) {z : G}
    (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set G) ≤ Mc := by
  have hz2 : z ^ 2 = 1 := sq_eq_one_of_mem_omegaOneCenter T hz
  have hZeq : Subgroup.zpowers z = quasithinOmegaOneCenter T := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz)
    rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1, hD.h17.2.1]
  intro x hx
  rw [hD.h14.mc_eq]
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [← hZeq] at hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hx
  exact ((Commute.zpow_right (show Commute x z from hxz) k).eq).symm

theorem lemma_15_2_20 (hs : Setting152 T Mc M) (hH : IsHStar T M H) (hI : Hyp15215 T Mc M B₀ I)
    (hD : Inputs152 T Mc M H B₀ I)
    (h18 : ∀ I' : Subgroup G, Hyp15215 T Mc M B₀ I' → IsSylowTwoOf (sOf152 T Mc M B₀) I')
    (hU : IsElemAbelian 2 (conjClosure (V154 T Mc M) H)) : Lemma15220Concl T Mc M B₀ I := by
  have hev : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G := hs.qtfe.qtke.2.1
  have hTsyl : IsSylowTwoOf T ⊤ := isSylowTwoOf_of_le151 hs.qtfe.sylow le_top
  have hM : quasithinIsMaxTwoLocal Mc := hs.qtfe.mc_max
  have hT2 : IsPGroup 2 T := hs.qtfe.sylow.1
  have hTM : T ≤ M := T_le_M152 hs
  obtain ⟨Ts, hTs⟩ := hs.qtfe.exists_sylow
  have h115 : ∀ z ∈ quasithinOmegaOneCenter T, z ≠ 1 →
      Lemma115Hyp I (sOf152 T Mc M B₀) Mc z := by
    intro z hz hz1
    have hz2 : z ^ 2 = 1 := sq_eq_one_of_mem_omegaOneCenter T hz
    have hzcT : z ∈ Subgroup.centralizer (T : Set G) := (quasithinOmegaOneCenter_le_center T hz).2
    have hzT : z ∈ T := (quasithinOmegaOneCenter_le_center T hz).1
    have hzS : z ∈ sOf152 T Mc M B₀ := by
      have h1 : z ∈ omegaOneCenterOf (sOf152 T Mc M B₀) := by
        rw [← hD.h14.zS_eq]
        exact hD.h14.le_zS hz
      exact C1GN.omegaOneCenterOf_le_self _ h1
    have hzcS : z ∈ Subgroup.centralizer (sOf152 T Mc M B₀ : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr S_le_T152) hzcT
    have hCM := centralizer_z_le_Mc152 hD hz hz1
    obtain ⟨I₀, hI₀⟩ := exists_inM_of_pCoreOf_ne_bot hI.inH.2
    have hI₀H : Hyp15215 T Mc M B₀ I₀ :=
      ⟨⟨hI.inH.1.trans hI₀.2, pCoreOf_ne_bot_of_isTwoLocal hI₀.1.1⟩,
        fun h => hI.not_le (hI₀.2.trans h)⟩
    have hS₀ : IsSylowTwoOf (sOf152 T Mc M B₀) I₀ := h18 I₀ hI₀H
    obtain ⟨P, hP1, hP2, hPI₀⟩ := hI₀.1.1
    have hBH : P ⊔ Subgroup.centralizer (P : Set G) ≤ I₀ := by
      rw [hPI₀]
      exact sup_le Subgroup.le_normalizer (fun x hx => Subgroup.centralizer_le_normalizer _ hx)
    have hH₀ : Lemma115Hyp I₀ (sOf152 T Mc M B₀) Mc z :=
      lemma116 hev hP2 hP1 hBH hPI₀.le hS₀ hTsyl S_le_T152 hzT hzcT hz1 hz2 hM hCM
    have hSMc : sOf152 T Mc M B₀ ≤ Mc := S_le_T152.trans hs.qtfe.t_le_mc
    have hQT : pCoreOf 2 Mc ≤ T := by
      have := pCoreOf_two_le_sylow Mc Ts (hTs ▸ hs.qtfe.t_le_mc)
      rwa [hTs] at this
    refine ⟨hI.inH.2, h18 I hI,
      charTwo_of_isTwoLocal_of_isSylowTwoOf_le hev hTsyl hM.1 hs.qtfe.t_le_mc,
      pCoreOf_ne_bot_of_isTwoLocal hM.1, hSMc, ?_, hCM, hz1, hzS, hzcS, hz2⟩
    intro x hx
    have hxQ : x ∈ T := hQT hx.1
    have hSI₀ : sOf152 T Mc M B₀ ≤ I₀ ⊓ Mc := le_inf hS₀.1 hSMc
    have hSI : sOf152 T Mc M B₀ ≤ I ⊓ Mc := le_inf (S_le_I152 hD) hSMc
    have hO2 : pCoreOf 2 (I₀ ⊓ Mc) ≤ pCoreOf 2 (I ⊓ Mc) :=
      pCoreOf_le_pCoreOf_of_sylow (inf_le_inf_right Mc hI₀.2) (hT2.to_le S_le_T152) hSI
        (isSylowTwoOf_restrict hS₀ hSI₀ inf_le_left).2.2
    have hxC : x ∈ Subgroup.centralizer (pCoreOf 2 (I₀ ⊓ Mc) : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hO2) hx.2
    have hxI₀ : x ∈ I₀ := hH₀.centralizer_le ⟨hx.1, hxC⟩
    have hxS : x ∈ sOf152 T Mc M B₀ := by
      rw [← inf_eq_of_isSylowTwoOf_of_le hS₀ hT2 S_le_T152]
      exact ⟨hxQ, hxI₀⟩
    exact S_le_I152 hD hxS
  have hOdd : oddCoreIn I = ⊥ := by
    obtain ⟨z, hz, hz1⟩ := exists_z152 hD
    have hz115 := h115 z hz hz1
    have hVT : V154 T Mc M ≤ T :=
      (V154_le_VZ T Mc M).trans (isTwoReducedIn_VZ hs.qtfe hs.mf.1.1).2
    have hVH : V154 T Mc M ≤ H := hVT.trans hH.1.1
    have hUH : conjClosure (V154 T Mc M) H ≤ H :=
      conjClosure_le fun h hh w hw => H.mul_mem (H.mul_mem hh (hVH hw)) (H.inv_mem hh)
    have hHK : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
    have hHU : H ≤ Subgroup.normalizer (conjClosure (V154 T Mc M) H : Set G) :=
      le_normalizer_conjClosure _ H
    have hUKK : ⁅conjClosure (V154 T Mc M) H, oTwoUpper H⁆ ≤ oTwoUpper H := by
      rw [Subgroup.commutator_le]
      intro u hu k hk
      have h1 : u * k * u⁻¹ ∈ oTwoUpper H :=
        (Subgroup.mem_normalizer_iff.mp (hHK (hUH hu)) k).mp hk
      have : ⁅u, k⁆ = (u * k * u⁻¹) * k⁻¹ := by simp only [commutatorElement_def, mul_assoc]
      rw [this]
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hk)
    have hUKU : ⁅conjClosure (V154 T Mc M) H, oTwoUpper H⁆ ≤ conjClosure (V154 T Mc M) H := by
      rw [Subgroup.commutator_le]
      intro u hu k hk
      have h1 : k * u⁻¹ * k⁻¹ ∈ conjClosure (V154 T Mc M) H :=
        (Subgroup.mem_normalizer_iff.mp (hHU (oTwoUpper_le H hk)) u⁻¹).mp (Subgroup.inv_mem _ hu)
      have : ⁅u, k⁆ = u * (k * u⁻¹ * k⁻¹) := by simp only [commutatorElement_def]; group
      rw [this]
      exact Subgroup.mul_mem _ hu h1
    have hKI : oTwoUpper H ≤ I := (K_le_inf152 hD).trans inf_le_right
    have hUKI : ⁅conjClosure (V154 T Mc M) H, oTwoUpper H⁆ ≤ I := hUKK.trans hKI
    have hUKel : IsElemAbelian 2 (⁅conjClosure (V154 T Mc M) H, oTwoUpper H⁆ : Subgroup G) :=
      isElemAbelian_mono151 hUKU hU
    have hUKH : ⁅conjClosure (V154 T Mc M) H, oTwoUpper H⁆ ≤ H := hUKK.trans (oTwoUpper_le H)
    have hHUK : H ≤ Subgroup.normalizer
        (⁅conjClosure (V154 T Mc M) H, oTwoUpper H⁆ : Subgroup G) := fun g hg =>
      A4.mem_normalizer_commutator (hHU hg) (hHK hg)
    have hUKT : ⁅conjClosure (V154 T Mc M) H, oTwoUpper H⁆ ≤ T := by
      have h1 : ⁅conjClosure (V154 T Mc M) H, oTwoUpper H⁆ ≤ pCoreOf 2 H :=
        le_pCoreOf_of_le_normalizer 2 hUKH hHUK (isPGroup_of_isElemAbelian152 hUKel)
      have h2 : pCoreOf 2 H ≤ T := by
        have := pCoreOf_two_le_sylow H Ts (hTs ▸ hH.1.1)
        rwa [hTs] at this
      exact h1.trans h2
    have hUKne : ⁅conjClosure (V154 T Mc M) H, oTwoUpper H⁆ ≠ ⊥ := by
      intro hbot
      have hKV : oTwoUpper H ≤ Subgroup.centralizer (V154 T Mc M : Set G) := by
        intro k hk
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        have hcomm : ⁅v, k⁆ ∈ ⁅conjClosure (V154 T Mc M) H, oTwoUpper H⁆ :=
          Subgroup.commutator_mem_commutator (le_conjClosure _ H hv) hk
        rw [hbot, Subgroup.mem_bot] at hcomm
        have h1 : v * k * v⁻¹ * k⁻¹ = 1 := hcomm
        calc v * k = (v * k * v⁻¹ * k⁻¹) * (k * v) := by group
          _ = k * v := by rw [h1, one_mul]
      have hKH : oTwoUpper H ≤ H ⊓ Subgroup.normalizer (V154 T Mc M : Set G) := fun k hk =>
        ⟨oTwoUpper_le H hk, Subgroup.centralizer_le_normalizer _ (hKV hk)⟩
      have hKT : oTwoUpper H ≤ T := (hD.hN.eq_inf.trans hD.hN.eq_normalizer) ▸ hKH
      apply hH.2.1
      rw [H_eq152 hs hH]
      exact sup_le (hKT.trans hTM) hTM
    have hZUK : quasithinOmegaOneCenter T ≤ ⁅conjClosure (V154 T Mc M) H, oTwoUpper H⁆ :=
      Z_le_of_normal_ne_bot152 hs hD hUKT (hH.1.1.trans hHUK) (fun x hx => hUKel.2 x hx) hUKne
    have hUKcomm : ⁅⁅conjClosure (V154 T Mc M) H, oTwoUpper H⁆, oTwoUpper H⁆ =
        ⁅conjClosure (V154 T Mc M) H, oTwoUpper H⁆ :=
      commutator_commutator_eq_of_opResidual hU ((oTwoUpper_le H).trans hHU)
        (opResidual_two_oTwoUpper152 H)
    have hcent : ⁅conjClosure (V154 T Mc M) H, oTwoUpper H⁆ ≤
        Subgroup.centralizer (fusionOddCoreOf I : Set G) :=
      a126_one hKI (opResidual_two_oTwoUpper152 H) hUKI (isPGroup_of_isElemAbelian152 hUKel)
        hUKcomm (pRank_pCoreOf_le_two152 hs.qtfe hI.inH.2)
        (C2Nine.frattiniIn_eq_bot_of_isElemAbelian hUKel)
    refine eq_bot_iff.mpr fun y hy => ?_
    have hyz : z * y = y * z :=
      (Subgroup.mem_centralizer_iff.mp (hcent (hZUK hz)) y hy).symm
    have hinv := hz115.inverts_oddCoreIn y hy
    have h1 : z⁻¹ * y * z = y := by
      calc z⁻¹ * y * z = z⁻¹ * (y * z) := by group
        _ = z⁻¹ * (z * y) := by rw [← hyz]
        _ = y := by group
    have hyy : y = y⁻¹ := h1.symm.trans hinv
    have hy2 : y ^ 2 = 1 := by
      have : y * y = 1 := mul_eq_one_iff_eq_inv.mpr hyy
      rwa [← sq] at this
    have hodd : Odd (orderOf y) :=
      (odd_card_oddCoreIn I).of_dvd_nat (Subgroup.orderOf_dvd_natCard (oddCoreIn I) hy)
    have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
    have h3 : orderOf y = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h3)
  obtain ⟨z₀, hz₀, hz₀1⟩ := exists_z152 hD
  exact ⟨h115, by rw [inf_comm]; exact (h115 z₀ hz₀ hz₀1).charTwo_inf, hOdd⟩

end Main

theorem stageLemma15220_of (h5 : StageLemma15205) (h159 : StageLemma1519)
    (h11 : StageLemma15211) (h13 : StageLemma15213) (h14 : StageLemma15214)
    (hN : StageNotation15209) (h16 : StageLemma15216) (h17 : StageLemma15217)
    (h18 : StageLemma15218) (h1512 : StageLemma15112) : StageLemma15220 := by
  intro G _ _ T Mc M hs H hH B₀ hB₀ I hI
  exact lemma_15_2_20 hs hH hI
    ⟨h5 G T Mc M hs, h159 G T Mc M hs.qtfe hs.mf hs.ce, h13 G T Mc M hs H hH,
      h14 G T Mc M hs B₀ hB₀, h11 G T Mc M hs H hH, hN G T Mc M hs H hH,
      h16 G T Mc M hs H hH B₀ hB₀ I hI, h17 G T Mc M hs B₀ hB₀ I hI⟩
    (fun I' hI' => (h18 G T Mc M hs H hH B₀ hB₀ I' hI').sylow)
    (h1512 G T Mc M hs.qtfe hs.mf hs.ce H hH).1.elemAbelian

end CFSG.Quasithin
