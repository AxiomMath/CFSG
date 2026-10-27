module

public import CFSG.Quasithin.EmptyFaithful.S153Odd
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Star
public import CFSG.Quasithin.EmptyFaithful.S153Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

@[expose] def Y153 {G : Type} [Group G] (Mc M : Subgroup G) : Subgroup G :=
  oTwoUpper (conjClosure (pCoreOf 2 (Mc ⊓ M)) M)

theorem Y153_le {G : Type} [Group G] (Mc M : Subgroup G) : Y153 Mc M ≤ M := by
  refine (oTwoUpper_le _).trans (conjClosure_le fun g hg z hz => ?_)
  have hRM : pCoreOf 2 (Mc ⊓ M) ≤ M := (pCoreOf_le 2 _).trans inf_le_right
  exact M.mul_mem (M.mul_mem hg (hRM hz)) (M.inv_mem hg)

theorem le_normalizer_Y153 {G : Type} [Group G] (Mc M : Subgroup G) :
    M ≤ Subgroup.normalizer (Y153 Mc M : Set G) :=
  (le_normalizer_conjClosure _ M).trans (normalizer_le_normalizer_oTwoUpper _)

namespace Hyp153

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem hyp14117 (h : Hyp153 G T Mc M) : Hyp14117 T Mc M Mc (VZ T M) where
  inM := h.inM
  twoReduced := h.twoReduced.1
  ne_bot := fun hbot => by
    have := h.card_VZ
    rw [hbot, Subgroup.card_bot] at this
    omega
  inM₁ := h.qtfe.inM_mc
  ne := h.ne_mc.symm
  cases := Or.inr rfl

theorem odd_card_autOn_oTwoUpper (h : Hyp153 G T Mc M) :
    Odd (Nat.card (autOn (oTwoUpper M) (VZ T M))) := by
  obtain ⟨q, L₁, L₂, t, -, -, -, -, hS, -⟩ := h.exists_ofourStruct
  rw [← A4.oTwoUpper_autOn h.le_normalizer]
  exact hS.odd_card_oTwoUpper

theorem T_le_normalizer_oTwoUpper (h : Hyp153 G T Mc M) :
    T ≤ Subgroup.normalizer (oTwoUpper M : Set G) :=
  h.T_le.trans (le_normalizer_oTwoUpper M)

theorem exists_central_mem_autOn_Rc (h113 : StageLemma14113) (h : Hyp153 G T Mc M) :
    ∃ r ∈ autOn T (VZ T M), r ≠ 1 ∧ r ∈ autOn (pCoreOf 2 (Mc ⊓ M)) (VZ T M) ∧
      ∀ y ∈ autOn M (VZ T M), Odd (orderOf y) → r * y * r⁻¹ = y⁻¹ := by
  obtain ⟨q, L₁, L₂, t, -, -, -, -, hS, -⟩ := h.exists_ofourStruct
  have hsyl := h.isSylowTwoOf_autI
  obtain ⟨r, hrT, hr1, -, -, hrz, hrinv⟩ := hS.exists_central hsyl
  have hRne := lemma_14_1_17_one h113 h.qtfe h.hyp14117
  have hRT : pCoreOf 2 (Mc ⊓ M) ≤ T := h.hyp14117.pCoreOf_le_sylow h.qtfe
  have hRM : pCoreOf 2 (Mc ⊓ M) ≤ M := (pCoreOf_le 2 _).trans inf_le_right
  have hTMV : T ≤ Subgroup.normalizer (VZ T M : Set G) := h.T_le.trans h.le_normalizer
  have hRle : autOn (pCoreOf 2 (Mc ⊓ M)) (VZ T M) ≤ autOn T (VZ T M) := A4.autOn_mono hRT
  have hTn : T ≤ Subgroup.normalizer (pCoreOf 2 (Mc ⊓ M) : Set G) :=
    h.hyp14117.le_inf.trans (le_normalizer_pCoreOf 2 (Mc ⊓ M))
  have hnorm : autOn T (VZ T M) ≤
      Subgroup.normalizer (autOn (pCoreOf 2 (Mc ⊓ M)) (VZ T M) : Set (MulAut (VZ T M))) :=
    autOn_le_normalizer_autOn hTMV (hRM.trans h.le_normalizer) hTn
  obtain ⟨z, hzR, hz1, hzc⟩ := exists_ne_one_mem_center_of_normalized hsyl.2.1 hRle hRne hnorm
  have hzr : z = r := (hrz z (hRle hzR) hzc).resolve_left hz1
  exact ⟨r, hrT, hr1, hzr ▸ hzR, hrinv⟩

theorem conjClosure_Rc_eq (h : Hyp153 G T Mc M) :
    conjClosure (pCoreOf 2 (Mc ⊓ M)) M =
      conjClosure (pCoreOf 2 (Mc ⊓ M)) (oTwoUpper M ⊔ T) := by
  have hV := h.elemAbelian
  have hMN := h.le_normalizer
  obtain ⟨q, L₁, L₂, t, -, -, -, -, hS, -⟩ := h.exists_ofourStruct
  have hsyl := h.isSylowTwoOf_autI
  have hYM : oTwoUpper M ⊔ T ≤ M := sup_le (oTwoUpper_le M) h.T_le
  apply le_antisymm
  · refine conjClosure_le fun m hm z hz => ?_
    have hbar : autI hV (oTwoUpper M ⊔ T) = autI hV M := by
      rw [autI_sup hV ((oTwoUpper_le M).trans hMN) (h.T_le.trans hMN)]
      have e : autI hV (oTwoUpper M) = oTwoUpper (autI hV M) :=
        (A4.oTwoUpper_autOn hMN).symm
      rw [e]
      exact hS.sup_oTwoUpper_eq hsyl
    have hmN : m ∈ Subgroup.normalizer (VZ T M : Set G) := hMN hm
    have hmbar : convI hV ⟨m, hmN⟩ ∈ autI hV (oTwoUpper M ⊔ T) :=
      hbar ▸ convI_mem_autI hV hm hmN
    obtain ⟨g, hgY, hg⟩ := (mem_autI hV).1 hmbar
    have hc1 : convI hV (g⁻¹ * ⟨m, hmN⟩) = 1 := by rw [map_mul, map_inv, hg, inv_mul_cancel]
    have hcC : (g : G)⁻¹ * m ∈ Subgroup.centralizer (VZ T M : Set G) :=
      (convI_eq_one_iff hV _).1 hc1
    have hcM : (g : G)⁻¹ * m ∈ M := M.mul_mem (M.inv_mem (hYM hgY)) hm
    have hcn := h.hyp14117.centralizer_le_normalizer h.qtfe ⟨hcM, hcC⟩
    have hz' : (g : G)⁻¹ * m * z * ((g : G)⁻¹ * m)⁻¹ ∈ pCoreOf 2 (Mc ⊓ M) :=
      (Subgroup.mem_normalizer_iff.mp hcn z).mp hz
    have e : m * z * m⁻¹ = (g : G) * ((g : G)⁻¹ * m * z * ((g : G)⁻¹ * m)⁻¹) * (g : G)⁻¹ := by
      group
    rw [e]
    exact mem_conjClosure hgY hz'
  · exact conjClosure_mono le_rfl hYM

theorem autOn_Y153 (h113 : StageLemma14113) (h : Hyp153 G T Mc M) :
    autOn (Y153 Mc M) (VZ T M) = oTwoUpper (autOn M (VZ T M)) := by
  unfold Y153
  rw [conjClosure_Rc_eq h]
  have h2 := lemma_14_1_17_two h.qtfe h.hyp14117 (oTwoUpper_le M) h.T_le_normalizer_oTwoUpper
    h.odd_card_autOn_oTwoUpper
  rw [h2, ← A4.oTwoUpper_autOn h.le_normalizer]
  obtain ⟨r, -, -, hrR, hinv⟩ := h.exists_central_mem_autOn_Rc h113
  have hRM : pCoreOf 2 (Mc ⊓ M) ≤ M := (pCoreOf_le 2 _).trans inf_le_right
  exact commutator_oTwoUpper_eq_of_inv (A4.autOn_mono hRM) hrR hinv

theorem lemma_15_3_7_inf (h : Hyp153 G T Mc M) :
    Mc ⊓ M = (M ⊓ Subgroup.centralizer (VZ T M : Set G)) ⊔ T := by
  have hV := h.elemAbelian
  have hMN := h.le_normalizer
  apply le_antisymm
  · have hTX : T ≤ Mc ⊓ M := h.hyp14117.le_inf
    have hXM : Mc ⊓ M ≤ M := inf_le_right
    rcases h.dichotomy hTX hXM with h1 | h1
    · intro x hx
      have hxM : x ∈ M := hXM hx
      have hxN := hMN hxM
      have hxbar : convI hV ⟨x, hxN⟩ ∈ autI hV T := h1 ▸ convI_mem_autI hV hx hxN
      obtain ⟨g, hgT, hg⟩ := (mem_autI hV).1 hxbar
      have hk : convI hV (⟨x, hxN⟩ * g⁻¹) = 1 := by rw [map_mul, map_inv, hg, mul_inv_cancel]
      have hk0 : x * (g : G)⁻¹ ∈ Subgroup.centralizer (VZ T M : Set G) :=
        (convI_eq_one_iff hV _).1 hk
      have hkM : x * (g : G)⁻¹ ∈ M := M.mul_mem hxM (M.inv_mem (h.T_le hgT))
      have e : x = (x * (g : G)⁻¹) * g := by group
      rw [e]
      exact Subgroup.mul_mem_sup ⟨hkM, hk0⟩ hgT
    · exfalso
      have hU := h.isUniqueM_of_autI_eq_M hTX hXM h1
      exact h.ne_mc (hU.2 Mc ⟨h.qtfe.mc_max, inf_le_left⟩).symm
  · exact sup_le ((h.hyp14117.centralizer_le h.qtfe).trans (le_of_eq (inf_comm _ _)))
      h.hyp14117.le_inf

theorem autOn_Y153_sup_T (h113 : StageLemma14113) (h : Hyp153 G T Mc M) :
    autOn (Y153 Mc M ⊔ T) (VZ T M) = autOn M (VZ T M) := by
  obtain ⟨q, L₁, L₂, t, -, -, -, -, hS, -⟩ := h.exists_ofourStruct
  have hV := h.elemAbelian
  have hMN := h.le_normalizer
  show autI hV (Y153 Mc M ⊔ T) = autI hV M
  rw [autI_sup hV ((Y153_le Mc M).trans hMN) (h.T_le.trans hMN)]
  have e : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := h.autOn_Y153 h113
  rw [e]
  exact hS.sup_oTwoUpper_eq h.isSylowTwoOf_autI

theorem lemma_15_3_7_unique (h113 : StageLemma14113) (h : Hyp153 G T Mc M) :
    IsUniqueM (Y153 Mc M ⊔ T) M :=
  h.isUniqueM_of_autI_eq_M le_sup_right (sup_le (Y153_le Mc M) h.T_le)
    (h.autOn_Y153_sup_T h113)

theorem Y153_ne_bot (h113 : StageLemma14113) (h : Hyp153 G T Mc M) : Y153 Mc M ≠ ⊥ := by
  obtain ⟨q, L₁, L₂, t, -, -, -, -, hS, -⟩ := h.exists_ofourStruct
  intro hbot
  have e : autOn (Y153 Mc M) (VZ T M) = oTwoUpper (autOn M (VZ T M)) := h.autOn_Y153 h113
  rw [hbot] at e
  have h0 : autOn (⊥ : Subgroup G) (VZ T M) = ⊥ := autI_bot h.elemAbelian
  rw [h0] at e
  exact hS.oTwoUpper_ne_bot e.symm

theorem pCoreOf_Y153_ne_bot (h113 : StageLemma14113) (h : Hyp153 G T Mc M) :
    pCoreOf 2 (Y153 Mc M) ≠ ⊥ := by
  intro hbot
  obtain ⟨S, hS⟩ := h.qtfe.exists_sylow
  have hSM : (S : Subgroup G) ≤ M := hS ▸ h.T_le
  have hF : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
    h.qtfe.qtke.2.1 M h.inM.1.1 ⟨S, hSM⟩
  have hYM := Y153_le Mc M
  have hYn := le_normalizer_Y153 Mc M
  have h1 : Y153 Mc M ⊓ pCoreOf 2 M ≤ pCoreOf 2 (Y153 Mc M) :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hg, le_normalizer_pCoreOf 2 M (hYM hg)⟩)
      ((pCoreOf_isPGroup 2 M).to_le inf_le_right)
  rw [hbot] at h1
  apply Y153_ne_bot h113 h
  rw [eq_bot_iff]
  intro y hy
  have hyM : y ∈ M := hYM hy
  have hcomm : ∀ o ∈ pCoreOf 2 M, y * o * y⁻¹ * o⁻¹ = 1 := by
    intro o ho
    have hoM : o ∈ M := pCoreOf_le 2 M ho
    have hA : y * o * y⁻¹ * o⁻¹ ∈ Y153 Mc M := by
      have e : y * o * y⁻¹ * o⁻¹ = y * (o * y⁻¹ * o⁻¹) := by group
      rw [e]
      refine Subgroup.mul_mem _ hy ?_
      exact (Subgroup.mem_normalizer_iff.mp (hYn hoM) y⁻¹).mp (Subgroup.inv_mem _ hy)
    have hB : y * o * y⁻¹ * o⁻¹ ∈ pCoreOf 2 M := by
      refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ ho)
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M hyM) o).mp ho
    have := h1 ⟨hA, hB⟩
    simpa using this
  have hyF : y ∈ M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
    refine ⟨hyM, Subgroup.mem_centralizer_iff.2 fun o ho => ?_⟩
    have := hcomm o ho
    calc o * y = (y * o * y⁻¹ * o⁻¹) * (o * y) := by rw [this, one_mul]
      _ = y * o := by group
  have hyO : y ∈ pCoreOf 2 M := hF hyF
  have := h1 ⟨hy, hyO⟩
  simpa using this

theorem lemma_15_3_7_normalizer (h113 : StageLemma14113) (h : Hyp153 G T Mc M) :
    M = Subgroup.normalizer (Y153 Mc M : Set G) := by
  apply le_antisymm (le_normalizer_Y153 Mc M)
  intro g hg
  have hgO : g ∈ Subgroup.normalizer (pCoreOf 2 (Y153 Mc M) : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 _ hg
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (Y153 Mc M) : Set G)) :=
    ⟨pCoreOf 2 (Y153 Mc M), h.pCoreOf_Y153_ne_bot h113, pCoreOf_isPGroup 2 _, rfl⟩
  have hle : M ≤ Subgroup.normalizer (pCoreOf 2 (Y153 Mc M) : Set G) :=
    (le_normalizer_Y153 Mc M).trans (normalizer_le_normalizer_pCoreOf 2 _)
  have heq := h.inM.1.2 _ hloc hle
  rw [← heq]
  exact hgO


theorem commutator_Y153_le (h : Hyp153 G T Mc M) {y c : G} (hy : y ∈ Y153 Mc M)
    (hc : c ∈ M ⊓ Subgroup.centralizer (VZ T M : Set G)) :
    y * c * y⁻¹ * c⁻¹ ∈ pCoreOf 2 M := by
  have h3 := (lemma_14_1_17_three h.qtfe h.hyp14117 (oTwoUpper_le M) (T := T)).1
  rw [Subgroup.commutator_comm] at h3
  have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
  have hyM : y ∈ M := Y153_le Mc M hy
  have hy' : y ∈ oTwoUpper (conjClosure (pCoreOf 2 (Mc ⊓ M)) (oTwoUpper M ⊔ T)) := by
    unfold Y153 at hy
    rwa [conjClosure_Rc_eq h] at hy
  have hu : (QuotientGroup.mk ⟨y, hyM⟩ : OTwoQuot M) ∈ imageOTwoQuot M
      (oTwoUpper (conjClosure (pCoreOf 2 (Mc ⊓ M)) (oTwoUpper M ⊔ T))) :=
    mem_imageOTwoQuot_iff.mpr ⟨y, hyM, hy', rfl⟩
  have hv : (QuotientGroup.mk ⟨c, hc.1⟩ : OTwoQuot M) ∈ imageOTwoQuot M
      (M ⊓ Subgroup.centralizer (VZ T M : Set G)) :=
    mem_imageOTwoQuot_iff.mpr ⟨c, hc.1, hc, rfl⟩
  have hcomm := Subgroup.mem_centralizer_iff.mp
    (hle (Subgroup.mem_sup_left hu)) _ hv
  exact (mk_commute_iff ⟨y, hyM⟩ ⟨c, hc.1⟩).1 hcomm.symm

theorem lemma_15_3_7_pCore (h113 : StageLemma14113) (h : Hyp153 G T Mc M) :
    pCoreOf 2 (Y153 Mc M ⊔ T) = T ⊓ Subgroup.centralizer (VZ T M : Set G) := by
  obtain ⟨q, L₁, L₂, t, -, -, -, -, hS, -⟩ := h.exists_ofourStruct
  have hV := h.elemAbelian
  have hMN := h.le_normalizer
  have hsyl := h.isSylowTwoOf_autI
  obtain ⟨S, hS0⟩ := h.qtfe.exists_sylow
  have hYT : Y153 Mc M ⊔ T ≤ M := sup_le (Y153_le Mc M) h.T_le
  have hO2T : pCoreOf 2 M ≤ T := by
    have := pCoreOf_two_le_sylow M S (hS0 ▸ h.T_le)
    rwa [hS0] at this
  apply le_antisymm
  · set K := pCoreOf 2 (Y153 Mc M ⊔ T) with hK
    have hKYT : K ≤ Y153 Mc M ⊔ T := pCoreOf_le 2 _
    have hKT : K ≤ T := by
      have := pCoreOf_two_le_sylow (Y153 Mc M ⊔ T) S (hS0 ▸ le_sup_right)
      rwa [hS0] at this
    refine le_inf hKT ?_
    have hKM : K ≤ M := hKYT.trans hYT
    have hKN : K ≤ Subgroup.normalizer (VZ T M : Set G) := hKM.trans hMN
    have hKn : Y153 Mc M ⊔ T ≤ Subgroup.normalizer (K : Set G) := le_normalizer_pCoreOf 2 _
    have hnorm : autOn (Y153 Mc M ⊔ T) (VZ T M) ≤
        Subgroup.normalizer (autOn K (VZ T M) : Set (MulAut (VZ T M))) :=
      autOn_le_normalizer_autOn (hYT.trans hMN) hKN hKn
    rw [h.autOn_Y153_sup_T h113] at hnorm
    have hbot : autI hV K = ⊥ :=
      hS.eq_bot_of_normal_isPGroup hsyl (autI_mono hV hKM) hnorm
        (B2F.isPGroup_autI hV (pCoreOf_isPGroup 2 _) hKN)
    exact (autI_eq_bot_iff hV hKN).1 hbot
  · set C : Subgroup G := T ⊓ Subgroup.centralizer (VZ T M : Set G) with hC
    have hCT : C ≤ T := inf_le_left
    have hTn : T ≤ Subgroup.normalizer (C : Set G) :=
      fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hg, B2F.le_normalizer_centralizer hMN (h.T_le hg)⟩
    have hYn : Y153 Mc M ≤ Subgroup.normalizer (C : Set G) := by
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      have key : ∀ y ∈ Y153 Mc M, ∀ c ∈ C, y * c * y⁻¹ ∈ C := by
        intro y hy c hc
        have hcM : c ∈ M ⊓ Subgroup.centralizer (VZ T M : Set G) := ⟨h.T_le hc.1, hc.2⟩
        have h1 := commutator_Y153_le h hy hcM
        have h2 : y * c * y⁻¹ * c⁻¹ ∈ C :=
          ⟨hO2T h1, h.hyp14117.pCoreOf_le_centralizer h1⟩
        have e : y * c * y⁻¹ = (y * c * y⁻¹ * c⁻¹) * c := by group
        rw [e]
        exact C.mul_mem h2 hc
      intro c
      refine ⟨key y hy c, fun hc => ?_⟩
      have := key y⁻¹ (Subgroup.inv_mem _ hy) _ hc
      simpa [mul_assoc] using this
    refine le_pCoreOf_of_le_normalizer 2 (hCT.trans le_sup_right) (sup_le hYn hTn)
      ((h.qtfe.sylow.1).to_le hCT)


end Hyp153

end CFSG.Quasithin
