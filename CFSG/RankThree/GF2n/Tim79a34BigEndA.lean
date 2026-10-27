module

public import CFSG.RankThree.GF2n.Tim79a34BigEpsTwo
public import CFSG.RankThree.GF2n.Tim79a34BigData
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicOddCore

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Blueprint CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.ARS.CaseM CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

section BigEpsA

variable {G : Type} [Group G] {F : Type} [Field F] {n : ℕ}
variable {φ : (Fin n ⊕ Fin n → F) → G} {a : Fin n ⊕ Fin n → F} {M P Q B : Subgroup G}

theorem BigEpsCfg.param_conj_kappa (h : BigEpsCfg φ a M P Q B) {t : G} (ht : t ∈ M) {κ : F}
    (hκ : ∀ x, spForm a x = 0 → ∃ l : F, t * φ x * t⁻¹ = φ (κ • x + l • a))
    {β β'' : Fin n ⊕ Fin n → F} {k : G} (hk : k ∈ Q) (hkk : t * φ β * t⁻¹ = φ β'' * k)
    {p : G} (hp : p ∈ P) {u u₁ : Fin n ⊕ Fin n → F} {c c₁ : F} (hu : spForm a u = 0)
    (hpar : BigEpsParam φ a p u c) (hpar₁ : BigEpsParam φ a (t * p * t⁻¹) u₁ c₁) :
    ∃ m : F, spForm a β'' • u₁ = (κ * spForm a β) • u + m • a := by
  have hp₁ : t * p * t⁻¹ ∈ P := h.normP t ht p hp
  have hL : ⁅t * p * t⁻¹, t * φ β * t⁻¹⁆ = t * ⁅p, φ β⁆ * t⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [h.comm_param hpar β] at hL
  have hzL : spForm a (spForm a β • u + (spForm u β + c * spForm a β) • a) = 0 := by
    rw [spForm_add_right, spForm_smul_right', spForm_smul_right', hu, spForm_self]
    ring
  obtain ⟨l, hl⟩ := hκ _ hzL
  rw [hl] at hL
  obtain ⟨l₂, hl₂⟩ := h.comm_Q k hk (t * p * t⁻¹) hp₁
  have hR : ⁅t * p * t⁻¹, φ β'' * k⁆ =
      ⁅t * p * t⁻¹, φ β''⁆ * (φ β'' * ⁅t * p * t⁻¹, k⁆ * (φ β'')⁻¹) := by
    simp only [commutatorElement_def]
    group
  have hkp : ⁅t * p * t⁻¹, k⁆ = φ (-(l₂ • a)) := by
    rw [← commutatorElement_inv, hl₂, h.neg]
  rw [hkk, hR, h.comm_param hpar₁ β'', hkp] at hL
  have hc : φ β'' * φ (-(l₂ • a)) * (φ β'')⁻¹ = φ (-(l₂ • a)) := by
    rw [h.commute β'', mul_inv_cancel_right]
  rw [hc, ← h.add] at hL
  have h2 := h.inj hL
  exact ⟨κ * (spForm u β + c * spForm a β) + l + l₂ - (spForm u₁ β'' + c₁ * spForm a β''),
    by linear_combination (norm := module) h2⟩

theorem BigEpsCfg.kappa_eq_one_of_fix_A [CharP F 2] (h : BigEpsCfg φ a M P Q B) {t : G}
    (ht : t ∈ M) {κ : F}
    (hκ : ∀ x, spForm a x = 0 → ∃ l : F, t * φ x * t⁻¹ = φ (κ • x + l • a))
    {β : Fin n ⊕ Fin n → F} (hβ : spForm a β ≠ 0) {k : G} (hk : k ∈ Q)
    (hkk : t * φ β * t⁻¹ = φ β * k) (hA : ∀ l : F, t * φ (l • a) * t⁻¹ = φ (l • a)) :
    κ = 1 := by
  obtain ⟨z, -, hz0, hza⟩ := exists_perp_vec_not_smul h.hn h.ha
  obtain ⟨p, hp, hpz⟩ := h.cover β hβ z hz0
  obtain ⟨u, c, hu, hpar⟩ := h.act p hp
  have hu_notin : ∀ l : F, u ≠ l • a := by
    intro l hl
    have h3 := h.inj ((h.comm_param hpar β).symm.trans hpz)
    apply hza (spForm a β * l + (spForm u β + c * spForm a β))
    rw [← h3, hl]
    module
  have hp₁ : t * p * t⁻¹ ∈ P := h.normP t ht p hp
  obtain ⟨u₁, c₁, hu₁, hpar₁⟩ := h.act _ hp₁
  obtain ⟨m, hm⟩ := h.param_conj_kappa ht hκ hk hkk hp hu hpar hpar₁
  obtain ⟨x, hxa, hux⟩ := exists_dual h.ha hu hu_notin
  have hu₁x : spForm u₁ x = κ := by
    have e := congrArg (fun v => spForm v x) hm
    simp only [spForm_add_left, spForm_smul_left', hux, hxa] at e
    have e' : spForm a β * (spForm u₁ x - κ) = 0 := by linear_combination e
    rcases mul_eq_zero.mp e' with h0 | h0
    · exact absurd h0 hβ
    · exact sub_eq_zero.mp h0
  have hu₁a : spForm u₁ a = 0 := by rw [spForm_comm, hu₁, neg_zero]
  have hL : ⁅t * p * t⁻¹, t * φ x * t⁻¹⁆ = t * ⁅p, φ x⁆ * t⁻¹ := by
    simp only [commutatorElement_def]
    group
  have e : spForm a x • u + (spForm u x + c * spForm a x) • a = (1 : F) • a := by
    rw [hxa, hux]
    module
  rw [h.comm_param hpar x, e, hA] at hL
  obtain ⟨l, hl⟩ := hκ x hxa
  rw [hl, h.comm_param hpar₁] at hL
  have h2 := h.inj hL
  have hax : spForm a (κ • x + l • a) = 0 := by
    rw [spForm_add_right, spForm_smul_right', spForm_smul_right', hxa, spForm_self]
    ring
  have hu₁κ : spForm u₁ (κ • x + l • a) = κ * κ := by
    rw [spForm_add_right, spForm_smul_right', spForm_smul_right', hu₁x, hu₁a]
    ring
  rw [hax, hu₁κ] at h2
  have h3 : (κ * κ) • a = (1 : F) • a := by
    rw [← h2]
    module
  have h4 : κ * κ = 1 := smul_left_injective F h.ha h3
  exact charTwo_pow_two_pow_eq_one (k := 1) (by rw [pow_one, pow_two]; exact h4)

end BigEpsA

@[expose] def BigEpsilonFaithfulAStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    ∀ t : ↥M, (t : Mbar M) ∈ Subgroup.centralizer (RbarM M V H : Set (Mbar M)) ⊓
        Subgroup.centralizer (WbarM M V H : Set (Mbar M)) →
      (∀ x ∈ V ⊓ wOf V H, (t : G) * x * (t : G)⁻¹ = x) → (t : Mbar M) ∈ WbarM M V H

theorem bigEpsilonFaithfulAStatement_of_natural (hZ : Sec34CentreTrivialStatement)
    (hN : BigNaturalStatement) (hIW : BigIWStatement) (hγ : BigGammaStatement) :
    BigEpsilonFaithfulAStatement := by
  intro G _ _ M V Q P H hH t hx hfix
  obtain ⟨n, f, ψ, a, B, hf, hcfg, hext, hBW, hPB, hroot⟩ :=
    bigEpsTwo_data hZ hN hIW hγ G M V Q P H hH
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hcentre : Subgroup.center (Xbar V H) = ⊥ :=
    hZ G M V Q P H ⟨hH.setup, hH.tilde, hH.concl⟩ hH.three hH.centre
  have hcP : cPbar V H P ≤ wOf V H := hIW G M V Q P H hH hcentre
  obtain ⟨hPP, -, hCP⟩ := bigPCommutatorStatement_holds hN G M V Q P H hH hcentre hcP
  have hxR := (Subgroup.mem_inf.mp hx).1
  have hxW := (Subgroup.mem_inf.mp hx).2
  have hQM : Q = inSubgroup (pCore 2) M := hc.hQ
  have hWM : wOf V H ≤ M := wOf_le_M_of_minCex hc
  have hxN : (t : Mbar M) ∈ Subgroup.normalizer (RbarM M V H : Set (Mbar M)) :=
    Subgroup.centralizer_le_normalizer _ hxR
  have hconj := bigEpsFConjStatement_of_natural hZ hN hIW hγ G M V Q P H hH t hxN
  have hT3 : ∀ y, spForm a y = 0 → ∃ z, psiElt ψ z = (t : G) * psiElt ψ y * (t : G)⁻¹ := by
    intro y hy
    have hmem : (t : G) * psiElt ψ y * (t : G)⁻¹ ∈ conjSubgroup (t : G) (P ⊓ wOf V H) := by
      rw [mem_conjSubgroup]
      have e : (t : G)⁻¹ * ((t : G) * psiElt ψ y * (t : G)⁻¹) * (t : G) = psiElt ψ y := by group
      rw [e]
      exact ⟨(hcfg.mem_P y).mpr hy, psiElt_mem ψ y⟩
    rw [hconj] at hmem
    exact exists_psiElt ψ hmem.2
  have hroot' : ∀ (c : Fin n ⊕ Fin n → GaloisField 2 f) (μ : GaloisField 2 f),
      spForm a c = 0 → (∀ l : GaloisField 2 f, c ≠ l • a) → μ ≠ 0 →
      ∃ r : G, ⁅(t : G), r⁆ ∈ Q ∧
        ∀ y, r * psiElt ψ y * r⁻¹ = psiElt ψ (y + (μ * spForm c y) • c) := by
    intro c μ hc0 hca hμ
    obtain ⟨r, hr, hrM, -, hract⟩ := hroot c μ hc0 hca hμ
    refine ⟨r, ?_, hract⟩
    have hrbar : ((⟨r, hrM⟩ : ↥M) : Mbar M) ∈ RbarM M V H :=
      Subgroup.mem_map.mpr ⟨⟨r, hrM⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
    have hcm := Subgroup.mem_centralizer_iff.mp hxR _ hrbar
    exact bigEps_comm_mem_Q hQM hcm.symm
  obtain ⟨κ, hκ⟩ := hcfg.exists_kappa t.2 hT3 hroot'
  have hcomm : ∀ f' ∈ P ⊓ wOf V H, ∀ b ∈ B, f' * b = b * f' := fun f' hf' b hb =>
    hc.wOf_isElemAbelian.comm (Subgroup.mem_inf.mp hf').2 (hBW hb)
  obtain ⟨β, hβ1⟩ := exists_spForm_eq_one hcfg.ha
  have hβmem : psiElt ψ β ∈ (P ⊓ wOf V H) ⊔ B := by
    rw [hPB]
    exact psiElt_mem ψ β
  obtain ⟨f', hf', b, hb, hfb⟩ := exists_mul_of_mem_sup hcomm hβmem
  obtain ⟨x, hx'⟩ := exists_psiElt ψ (Subgroup.mem_inf.mp hf').2
  have hxa : spForm a x = 0 :=
    (hcfg.mem_P x).mp (by rw [hx']; exact (Subgroup.mem_inf.mp hf').1)
  obtain ⟨β₀, hβ₀⟩ := hcfg.BW b hb
  have hββ : β = x + β₀ := by
    apply hcfg.inj
    rw [hcfg.add, hx', hβ₀, hfb]
  have hβ₀a : spForm a β₀ ≠ 0 := by
    have : spForm a β₀ = 1 := by
      rw [hββ, spForm_add_right, hxa, zero_add] at hβ1
      exact hβ1
    rw [this]
    exact one_ne_zero
  have hbM : b ∈ M := hWM (hBW hb)
  have hbbar : ((⟨b, hbM⟩ : ↥M) : Mbar M) ∈ WbarM M V H :=
    mem_WbarM_iff.mpr ⟨⟨b, hbM⟩, hBW hb, rfl⟩
  have hk : b⁻¹ * ((t : G) * b * (t : G)⁻¹) ∈ Q := by
    have hcm := Subgroup.mem_centralizer_iff.mp hxW _ hbbar
    have h1 := bigEps_comm_mem_Q hQM hcm.symm
    have e : b⁻¹ * ((t : G) * b * (t : G)⁻¹) = b⁻¹ * ⁅(t : G), b⁆ * (b⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hcfg.normQ _ (M.inv_mem hbM) _ h1
  have hkk : (t : G) * psiElt ψ β₀ * (t : G)⁻¹ =
      psiElt ψ β₀ * (b⁻¹ * ((t : G) * b * (t : G)⁻¹)) := by
    rw [hβ₀]
    group
  have hA : ∀ l : GaloisField 2 f,
      (t : G) * psiElt ψ (l • a) * (t : G)⁻¹ = psiElt ψ (l • a) := fun l =>
    hfix _ (Subgroup.mem_inf.mpr ⟨hext.AV l, psiElt_mem ψ _⟩)
  have hκ1 : κ = 1 := hcfg.kappa_eq_one_of_fix_A t.2 hκ hβ₀a hk hkk hA
  have hF : ∀ y, spForm a y = 0 → ∃ l : GaloisField 2 f,
      (t : G) * psiElt ψ y * (t : G)⁻¹ = psiElt ψ (y + l • a) := by
    intro y hy
    obtain ⟨l, hl⟩ := hκ y hy
    exact ⟨l, by rw [hl, hκ1, one_smul]⟩
  exact bigEpsTwo_in_Wbar hc hcfg hext hBW hPB hroot hPP hCP t hxR hxW hF

section ASLift

open CFSG.ComponentClassification.RankTwoSporadic

variable {G : Type} [Group G] [Finite G]

noncomputable def equivMapMkOfInfEqBot {N : Subgroup G} [N.Normal] {H : Subgroup G}
    (h : H ⊓ N = ⊥) : ↥H ≃* ↥(H.map (QuotientGroup.mk' N)) :=
  MulEquiv.ofBijective ((QuotientGroup.mk' N).subgroupMap H)
    ⟨fun x y hxy => by
      have h1 : (QuotientGroup.mk' N) (x : G) = (QuotientGroup.mk' N) (y : G) :=
        congrArg Subtype.val hxy
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
      have h2 : (x : G)⁻¹ * (y : G) ∈ H ⊓ N := ⟨H.mul_mem (H.inv_mem x.2) y.2, h1⟩
      rw [h, Subgroup.mem_bot] at h2
      exact Subtype.ext (inv_mul_eq_one.mp h2),
     (QuotientGroup.mk' N).subgroupMap_surjective H⟩

theorem eq_of_map_mk_eq {N : Subgroup G} [N.Normal] {H K : Subgroup G} (hKH : K ≤ H)
    (h : H ⊓ N = ⊥) (hmap : H.map (QuotientGroup.mk' N) = K.map (QuotientGroup.mk' N)) :
    H = K := by
  refine le_antisymm (fun x hx => ?_) hKH
  have hx' : (QuotientGroup.mk' N) x ∈ K.map (QuotientGroup.mk' N) :=
    hmap ▸ Subgroup.mem_map_of_mem _ hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
  have h2 : y⁻¹ * x ∈ H ⊓ N := ⟨H.mul_mem (H.inv_mem (hKH hy)) hx, hyx⟩
  rw [h, Subgroup.mem_bot] at h2
  rw [← inv_mul_eq_one.mp h2]
  exact hy

theorem aschbacherSeitz_of_inf_oddCore (hAS : AschbacherSeitzStatement) (A : Subgroup G)
    (m f : ℕ) (hm : 1 ≤ m) (hf : 2 ≤ f) (hAiso : Nonempty (↥A ≃* StatedSp m (GaloisField 2 f)))
    (hstd : standardComponentIsStandard A)
    (hrank : 2 ≤ CFSG.Open.pRank 2 (Subgroup.centralizer (A : Set G)))
    (hL : Subgroup.normalClosure (A : Set G) ⊓ standardComponentOddCore G = ⊥) :
    Subgroup.normalClosure (A : Set G) = A ∨
      (m = 1 ∧ f = 2 ∧
        (Nonempty (↥(Subgroup.normalClosure (A : Set G)) ≃* alternatingGroup (Fin 9)) ∨
          NativeSporadic.IsSporadic ↥(Subgroup.normalClosure (A : Set G)) .M12 ∨
          NativeSporadic.IsSporadic ↥(Subgroup.normalClosure (A : Set G)) .J2)) := by
  set N := standardComponentOddCore G with hNdef
  have hodd : Odd (Nat.card N) := odd_card_standardComponentOddCore
  have hNA : N ≤ Subgroup.centralizer (A : Set G) :=
    standardComponentOddCore_le_centralizer hstd hrank
  have hAp : commutator ↥A = ⊤ := hstd.1.1
  have hAL : A ≤ Subgroup.normalClosure (A : Set G) := Subgroup.le_normalClosure
  have hAN : A ⊓ N = ⊥ := eq_bot_iff.mpr ((inf_le_inf_right N hAL).trans hL.le)
  obtain ⟨e⟩ := hAiso
  have e' : ↥(A.map (QuotientGroup.mk' N)) ≃* StatedSp m (GaloisField 2 f) :=
    (equivMapMkOfInfEqBot hAN).symm.trans e
  have hstd' := standard_map hstd hodd hNA
  have hrank' := two_le_pRank_map hodd hNA hAp hrank
  have hO' : standardComponentOddCore (G ⧸ N) = ⊥ := standardComponentOddCore_quotient_eq_bot
  have hLmap : (Subgroup.normalClosure (A : Set G)).map (QuotientGroup.mk' N) =
      Subgroup.normalClosure ((A.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
    rw [Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective N), Subgroup.coe_map]
  have eL : ↥(Subgroup.normalClosure (A : Set G)) ≃*
      ↥(Subgroup.normalClosure ((A.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) :
        Set (G ⧸ N))) :=
    (equivMapMkOfInfEqBot hL).trans (MulEquiv.subgroupCongr hLmap)
  rcases hAS (G ⧸ N) (A.map (QuotientGroup.mk' N)) m f hm hf ⟨e'⟩ hO' hstd' hrank' with
    hn | ⟨hm1, hf2, h9 | h12 | hJ⟩
  · left
    apply eq_of_map_mk_eq hAL hL
    rw [hLmap, hn]
  · exact Or.inr ⟨hm1, hf2, Or.inl (h9.map fun e9 => eL.trans e9)⟩
  · exact Or.inr ⟨hm1, hf2, Or.inr (Or.inl (h12.map fun e9 => eL.trans e9))⟩
  · exact Or.inr ⟨hm1, hf2, Or.inr (Or.inr (hJ.map fun e9 => eL.trans e9))⟩

end ASLift

section BigLift

open CFSG.ComponentClassification.RankTwoSporadic

variable {G : Type} [Group G]

theorem big_normalClosure_inf_oddCore (hFA : BigEpsilonFaithfulAStatement) [Finite G]
    {M V Q P H : Subgroup G} (hH : BigEndHyp M V Q P H)
    (hstd : standardComponentIsStandard (RbarM M V H))
    (hrank : 2 ≤ CFSG.Open.pRank 2 (Subgroup.centralizer (RbarM M V H : Set (Mbar M))))
    (hWe : IsElemAbelian 2 (WbarM M V H)) (hW4 : 4 ≤ Nat.card (WbarM M V H))
    (hWTI : IsTI (WbarM M V H)) (hAn : ((V ⊓ wOf V H).subgroupOf M).Normal) :
    Subgroup.normalClosure (RbarM M V H : Set (Mbar M)) ⊓ standardComponentOddCore (Mbar M) =
      ⊥ := by
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hQM : Q = inSubgroup (pCore 2) M := hc.hQ
  have hVM : V ≤ M := hc.V_le_P.trans (hc.P_le_Q.trans (hQM ▸ (inSubgroup_pCore_two M).2.1))
  set CAM : Subgroup ↥M := Subgroup.centralizer (((V ⊓ wOf V H).subgroupOf M : Subgroup ↥M) :
    Set ↥M) with hCAM
  haveI : CAM.Normal := inferInstance
  set CA : Subgroup (Mbar M) :=
    CAM.map (QuotientGroup.mk' ((inSubgroup (pCore 2) M).subgroupOf M)) with hCA
  haveI hCAn : CA.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hRCA : RbarM M V H ≤ CA := by
    apply Subgroup.map_mono
    intro r hr
    rw [Subgroup.mem_subgroupOf] at hr
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxV : (x : G) ∈ V := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hr).2 (x : G) hxV)
  have hLCA : Subgroup.normalClosure (RbarM M V H : Set (Mbar M)) ≤ CA :=
    Subgroup.normalClosure_le_normal fun x hx => hRCA hx
  set O := standardComponentOddCore (Mbar M) with hO
  have hOodd : Odd (Nat.card O) := odd_card_standardComponentOddCore
  have hOR : O ≤ Subgroup.centralizer (RbarM M V H : Set (Mbar M)) :=
    standardComponentOddCore_le_centralizer hstd hrank
  have hOW : O ≤ Subgroup.centralizer (WbarM M V H : Set (Mbar M)) :=
    le_centralizer_of_odd_card_of_isTI hWe hW4 hWTI hOodd
  rw [eq_bot_iff]
  rintro z ⟨hzL, hzO⟩
  obtain ⟨t, htC, rfl⟩ := Subgroup.mem_map.mp (hLCA hzL)
  have hfix : ∀ x ∈ V ⊓ wOf V H, (t : G) * x * (t : G)⁻¹ = x := by
    intro x hx
    have hxM : x ∈ M := hVM (Subgroup.mem_inf.mp hx).1
    have h1 := Subgroup.mem_centralizer_iff.mp htC ⟨x, hxM⟩ (Subgroup.mem_subgroupOf.mpr hx)
    have h2 : x * (t : G) = (t : G) * x := congrArg Subtype.val h1
    rw [← h2, mul_inv_cancel_right]
  have hW := hFA G M V Q P H hH t ⟨hOR hzO, hOW hzO⟩ hfix
  exact Subgroup.mem_bot.mpr (eq_one_of_odd_card_of_sq_eq_one hOodd hzO (hWe.2 _ hW))

end BigLift

section BigEndA

variable {G : Type} [Group G]

structure BigBarFactsA : Prop where
  rbarIso : BigRbarIsoStatement
  wbarCard : BigWbarCardStatement
  wbarCentralizes : BigWbarCentralizesStatement
  wbarTI : BigWbarTIStatement
  epsNormalizer : BigEpsilonNormalizerStatement
  epsCentralizer : BigEpsilonCentralizerStatement

theorem bigA_normal (hPD : BigPDerivedStatement) [Finite G] {M V Q P H : Subgroup G}
    (hH : BigEndHyp M V Q P H) : ((V ⊓ wOf V H).subgroupOf M).Normal := by
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  obtain ⟨hPM, -, -, hPn, -, -⟩ := bigPV_base hc
  obtain ⟨hPcomm, hspan⟩ := hPD G M V Q P H hH
  have hcommA : ∀ x ∈ P.subgroupOf M, ∀ y ∈ P.subgroupOf M,
      ⁅x, y⁆ ∈ (V ⊓ wOf V H).subgroupOf M := by
    intro x hx y hy
    have h1 := hPcomm (x : G) (Subgroup.mem_subgroupOf.mp hx) (y : G)
      (Subgroup.mem_subgroupOf.mp hy)
    exact Subgroup.mem_subgroupOf.mpr (by simpa [commutatorElement_def] using h1)
  have hAeq : (V ⊓ wOf V H).subgroupOf M = ⁅P.subgroupOf M, P.subgroupOf M⁆ := by
    apply le_antisymm
    · intro a ha
      have h1 : (a : G) ∈ ⁅P, P⁆ := hspan (Subgroup.mem_subgroupOf.mp ha)
      rw [← map_subtype_commutator_subgroupOf hPM] at h1
      obtain ⟨b, hb', hba⟩ := Subgroup.mem_map.mp h1
      have : b = a := Subtype.ext hba
      exact this ▸ hb'
    · exact Subgroup.commutator_le.mpr hcommA
  rw [hAeq]
  infer_instance

theorem big_as_outcomes (hAS : AschbacherSeitzStatement) (hb : BigBarFactsA)
    (hFA : BigEpsilonFaithfulAStatement) (hPD : BigPDerivedStatement) [Finite G]
    {M V Q P H : Subgroup G} (hH : BigEndHyp M V Q P H) :
    ∃ n f : ℕ, 2 ≤ n ∧ 2 ^ f = qBar V H ∧
      Nonempty (↥(StatedSp n (GaloisField 2 f)) ≃* XbarZ V H) ∧
      (Subgroup.normalClosure (RbarM M V H : Set (Mbar M)) = RbarM M V H ∨
        (n = 2 ∧ f = 2 ∧
          (Nonempty (↥(Subgroup.normalClosure (RbarM M V H : Set (Mbar M))) ≃*
              alternatingGroup (Fin 9)) ∨
            NativeSporadic.IsSporadic
              ↥(Subgroup.normalClosure (RbarM M V H : Set (Mbar M))) .M12 ∨
            NativeSporadic.IsSporadic
              ↥(Subgroup.normalClosure (RbarM M V H : Set (Mbar M))) .J2))) := by
  obtain ⟨f, hf, h2f, n, hn, Φ, hΦ, -⟩ := id hH.three
  have hf2 : 2 ≤ f := two_le_of_pow_eq h2f hH.q_big
  have hiso : Nonempty (↥(StatedSp n (GaloisField 2 f)) ≃* XbarZ V H) :=
    ⟨MulEquiv.ofBijective Φ hΦ⟩
  have hq4 : 4 ≤ 2 ^ f := h2f ▸ hH.q_big
  obtain ⟨e⟩ := hb.rbarIso G M V Q P H hH n f hn h2f hiso
  have hm : 1 ≤ n - 1 := by omega
  haveI : IsSimpleGroup ↥(RbarM M V H) := by
    haveI := isSimpleGroup_statedSp_gf2f hm hf2
    exact e.isSimpleGroup
  have hnc : ¬ IsMulCommutative ↥(RbarM M V H) := by
    intro hc
    apply not_isMulCommutative_statedSp_gf2f hm hf2
    exact ⟨⟨fun a b => e.symm.injective (by
      rw [map_mul, map_mul]
      exact hc.is_comm.comm _ _)⟩⟩
  have heven : Even (Nat.card ↥(RbarM M V H)) := by
    rw [Nat.card_congr e.toEquiv]
    exact even_card_statedSp_gf2f hm (by omega)
  have hB4 : 4 ≤ Nat.card ↥(WbarM M V H) := by
    rw [hb.wbarCard G M V Q P H hH, ← h2f]
    exact hq4
  have hstd : standardComponentIsStandard (RbarM M V H) :=
    standardComponent_of_bar (RbarM M V H) (WbarM M V H) inferInstance hnc heven
      (isElemAbelian_wbar hH) hB4 (hb.wbarCentralizes G M V Q P H hH)
      (hb.wbarTI G M V Q P H hH) (hb.epsNormalizer G M V Q P H hH)
      (hb.epsCentralizer G M V Q P H hH)
  have hrank : 2 ≤ CFSG.Open.pRank 2 (Subgroup.centralizer (RbarM M V H : Set (Mbar M))) :=
    two_le_pRank_centralizer_of_bar (RbarM M V H) (WbarM M V H)
      (isElemAbelian_wbar hH) hB4 (hb.wbarCentralizes G M V Q P H hH)
  have hL := big_normalClosure_inf_oddCore hFA hH hstd hrank (isElemAbelian_wbar hH) hB4
    (hb.wbarTI G M V Q P H hH) (bigA_normal hPD hH)
  refine ⟨n, f, hn, h2f, hiso, ?_⟩
  rcases aschbacherSeitz_of_inf_oddCore hAS (RbarM M V H) (n - 1) f hm hf2 ⟨e⟩ hstd hrank hL with
    hN | ⟨hm1, hf1, hout⟩
  · exact Or.inl hN
  · exact Or.inr ⟨by omega, hf1, hout⟩

theorem big_n_two_f_two_of_as_A (hAS : AschbacherSeitzStatement) (hb : BigBarFactsA)
    (hFA : BigEpsilonFaithfulAStatement) (hPD : BigPDerivedStatement) [Finite G]
    {M V Q P H : Subgroup G} (hH : BigEndHyp M V Q P H) :
    ∃ n f : ℕ, 2 ≤ n ∧ 2 ^ f = qBar V H ∧
      Nonempty (↥(StatedSp n (GaloisField 2 f)) ≃* XbarZ V H) ∧
      (Subgroup.normalClosure (RbarM M V H : Set (Mbar M)) = RbarM M V H ∨
        (n = 2 ∧ f = 2)) := by
  obtain ⟨n, f, hn, h2f, hiso, hcase⟩ := big_as_outcomes hAS hb hFA hPD hH
  exact ⟨n, f, hn, h2f, hiso, hcase.imp id fun h => ⟨h.1, h.2.1⟩⟩

theorem tim79a34BigTildeEndStatement_of_steps_A (hAS : AschbacherSeitzStatement)
    (hHJ : AschbacherHJRepresentationStatement) (hb : BigBarFactsA)
    (hFA : BigEpsilonFaithfulAStatement) (hPD : BigPDerivedStatement)
    (hN : BigNormalStatement) (h12 : BigM12Statement) (hJ : BigHJStatement)
    (h9 : BigA9Statement) : Tim79a34BigTildeEndStatement := by
  intro G _ _ M V Q P H hs hq h3 hcc hT hC hA
  have hH : BigEndHyp M V Q P H := ⟨hs, hq, h3, hcc, hT, hC, hA⟩
  obtain ⟨n, f, -, -, -, hcase⟩ := big_as_outcomes hAS hb hFA hPD hH
  rcases hcase with hn | ⟨-, -, hA9 | hM | hJ'⟩
  · exact hN G M V Q P H hH hn
  · exact h9 G M V Q P H hH hA9
  · exact h12 G M V Q P H hH hM
  · exact hJ hHJ G M V Q P H hH hJ'

end BigEndA

end CFSG.RankThree.GF2n.Tim79a
