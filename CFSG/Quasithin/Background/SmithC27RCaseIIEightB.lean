module

public import CFSG.Quasithin.Background.SmithC27RCaseIIEightBRho
public import CFSG.Quasithin.Background.C124BlockA
public import CFSG.Quasithin.Background.C124BlkTransfer

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H R M K V : Subgroup G}

namespace CaseIICtx

variable (C : CaseIICtx R K V 8) (hs : StarHyp R K V)

include hs in
theorem blockU_eq_commutator_B8 (hC129 : ASC129Statement G) (h : Hyp27 H R M K)
    (hR : C.bar R = Subgroup.zpowers (swap 0 1)) : blockU K = ⁅V, K⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ρ, hρK, hρφ, hkey⟩ := C.exists_rho_B8 hs hC129 h hR
  refine le_antisymm ?_ (commutator_V_K_le_blockU h hs)
  set N : Subgroup G := Subgroup.closure {x | ∃ g ∈ K, x = g * ρ * g⁻¹} with hNdef
  have hNK : N ≤ K := by
    rw [Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    exact K.mul_mem (K.mul_mem hg hρK) (K.inv_mem hg)
  have hKN : K ≤ Subgroup.normalizer (N : Set G) := by
    intro k hk
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hle : (Subgroup.closure {x | ∃ g ∈ K, x = g * ρ * g⁻¹}).map (MulAut.conj k).toMonoidHom ≤
        N := by
      rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
      rintro _ ⟨g, hg, rfl⟩
      refine Subgroup.subset_closure ⟨k * g, K.mul_mem hk hg, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    exact hle ⟨x, hx, rfl⟩
  have hNeq : N = K := by
    rcases normal_le_oTwoZIn_or_eq h.perfect hs.quasi hNK hKN with hN | hN
    · exfalso
      rw [oTwoZIn_eq_of_center_eq_bot (C.center_eq_bot_B8 hs)] at hN
      have hρN : ρ ∈ N := Subgroup.subset_closure ⟨1, K.one_mem, by group⟩
      have hρC := hs.pCore_K_le_centralizer (hN hρN)
      have h1 := (C.phiB8_eq_one_iff hs.le_normalizer_V ⟨ρ, Subgroup.mem_sup_left hρK⟩).2 hρC
      rw [hρφ] at h1
      exact c3B8_ne_one h1
    · exact hN
  have hW : K ≤ Subgroup.normalizer ((⁅V, K⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator' hs.K_le_normalizer_V fun x hx => Subgroup.le_normalizer hx
  have hconj : ∀ g ∈ K, ∀ w ∈ (⁅V, K⁆ : Subgroup G), g * w * g⁻¹ ∈ (⁅V, K⁆ : Subgroup G) :=
    fun g hg w hw => (Subgroup.mem_normalizer_iff.1 (hW hg) w).1 hw
  have hOK : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have key : ∀ k ∈ N, ∀ p ∈ pCoreOf 2 K, ⁅p, k⁆ ∈ (⁅V, K⁆ : Subgroup G) := by
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      intro p hp
      have hp' : g⁻¹ * p * g ∈ pCoreOf 2 K := by
        have := (Subgroup.mem_normalizer_iff.1 (hOK (K.inv_mem hg)) p).1 hp
        simpa using this
      obtain ⟨v, hv, hpv⟩ := hkey _ (hs.pCore_K_le_pCore hp')
      have hvρ : ⁅v, ρ⁆ ∈ (⁅V, K⁆ : Subgroup G) := Subgroup.commutator_mem_commutator hv hρK
      have he : ⁅p, g * ρ * g⁻¹⁆ = g * ⁅v, ρ⁆ * g⁻¹ := by
        rw [commutatorElement_def, commutatorElement_def, ← hpv]
        group
      rw [he]
      exact hconj g hg _ hvρ
    | one =>
      intro p _
      rw [commutatorElement_one_right]
      exact Subgroup.one_mem _
    | mul x y hx hy ihx ihy =>
      intro p hp
      have he : ⁅p, x * y⁆ = ⁅p, x⁆ * (x * ⁅p, y⁆ * x⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [he]
      exact Subgroup.mul_mem _ (ihx p hp) (hconj x (hNK hx) _ (ihy p hp))
    | inv x hx ihx =>
      intro p hp
      have he : ⁅p, x⁻¹⁆ = x⁻¹ * ⁅p, x⁆⁻¹ * x⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [he]
      exact hconj _ (K.inv_mem (hNK hx)) _ (Subgroup.inv_mem _ (ihx p hp))
  show ⁅pCoreOf 2 K, K⁆ ≤ ⁅V, K⁆
  rw [Subgroup.commutator_le]
  intro p hp k hk
  rw [← hNeq] at hk
  exact key k hk p hp

include hs in
theorem isShort2_B8 (hC129 : ASC129Statement G) (h : Hyp27 H R M K)
    (hR : C.bar R = Subgroup.zpowers (swap 0 1)) : IsShort2 K := by
  have hU := C.blockU_eq_commutator_B8 hs hC129 h hR
  have hKV := hs.K_le_normalizer_V
  have hlt : blockZ K < blockU K := by
    refine lt_of_le_of_ne inf_le_left fun hZU => ?_
    obtain ⟨u, hu⟩ := C.β_surj (C124.YZ.pairQ 0 1)
    have hu1 : C.β u ≠ 1 := by
      rw [hu]
      exact B5FinS8.pclass_ne_one 0 1 (by decide)
    have huU : (u : IntMod V C.hV).val ∈ blockU K := by
      rw [hU]
      exact val_mem_commutator_of_mem_commV C.hV u.2
    rw [← hZU] at huU
    exact hu1 ((C.β_ker u).2 ((mem_fixV_autI_iff C.hV hKV).2 huU.2))
  refine ⟨C124.noTwoQuot_of_perfect h.perfect, h.charTwo, ⟨?_, ?_⟩, Or.inl hs.quasi, hlt, ?_⟩
  · rw [hU]
    refine le_inf (commutator_V_K_le_pCore hs) fun x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact (Subgroup.mem_centralizer_iff.1 (hs.pCore_K_le_centralizer hp) x
      (commutator_V_K_le_V hs hx)).symm
  · intro x hx
    rw [hU] at hx
    exact hs.elemAbelian.2 x (commutator_V_K_le_V hs hx)
  · intro W hZW hWU hKW
    let Wc : Subgroup ↥(commV (autI C.hV K)) :=
      W.comap ((C124.blkVal C.hV).comp (commV (autI C.hV K)).subtype)
    have hW' : ∀ σ ∈ alternatingGroup (Fin 8), ∀ d ∈ Wc.map C.β,
        C124.YZ.dAct 8 σ d ∈ Wc.map C.β := by
      rintro σ hσ _ ⟨u, hu, rfl⟩
      have hgK : ((C.ι.symm σ : ↥(autOn (K ⊔ R) V)) : MulAut ↥V) ∈ autOn K V := by
        rw [C.mem_K, MulEquiv.apply_symm_apply]
        exact hσ
      obtain ⟨k, hkK, hkg⟩ := mem_autOn_iff'.1 hgK
      have hmem : (((C.ι.symm σ : ↥(autOn (K ⊔ R) V)) : MulAut ↥V) : MulAut (IntMod V C.hV))
          (u : IntMod V C.hV) ∈ commV (autI C.hV K) :=
        C124.YZ.apply_mem_commV (C124.YZ.autI_normalizes C.hV hs.le_normalizer
          (C.ι.symm σ).2) u.2
      refine ⟨⟨_, hmem⟩, ?_, ?_⟩
      · have hval : ((((C.ι.symm σ : ↥(autOn (K ⊔ R) V)) : MulAut ↥V) : MulAut (IntMod V C.hV))
            (u : IntMod V C.hV)).val = k * (u : IntMod V C.hV).val * (k : G)⁻¹ := by
          rw [← hkg]
          exact convI_apply_val C.hV k (u : IntMod V C.hV)
        show ((((C.ι.symm σ : ↥(autOn (K ⊔ R) V)) : MulAut ↥V) : MulAut (IntMod V C.hV))
            (u : IntMod V C.hV)).val ∈ W
        rw [hval]
        exact (Subgroup.mem_normalizer_iff.1 (hKW hkK) _).1 hu
      · rw [C.β_equiv _ u hmem, MulEquiv.apply_symm_apply]
    rcases dm8_eq_bot_or_top (Wc.map C.β) hW' with hbot | htop
    · left
      refine le_antisymm (fun w hw => ?_) hZW
      have hwU : w ∈ ⁅V, K⁆ := hU ▸ hWU hw
      obtain ⟨u, huc, huw⟩ := exists_mem_commV_of_mem_commutator C.hV hKV hwU
      have hβ : C.β ⟨u, huc⟩ ∈ Wc.map C.β :=
        ⟨⟨u, huc⟩, show u.val ∈ W by rw [huw]; exact hw, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hβ
      have hfix := (C.β_ker _).1 hβ
      exact ⟨hWU hw, by rw [← huw]; exact (mem_fixV_autI_iff C.hV hKV).1 hfix⟩
    · right
      refine le_antisymm hWU fun x hx => ?_
      have hxU : x ∈ ⁅V, K⁆ := hU ▸ hx
      obtain ⟨u, huc, hux⟩ := exists_mem_commV_of_mem_commutator C.hV hKV hxU
      have hβ : C.β ⟨u, huc⟩ ∈ Wc.map C.β := htop ▸ Subgroup.mem_top _
      obtain ⟨u', hu'W, hu'β⟩ := hβ
      have hk : C.β (u'⁻¹ * ⟨u, huc⟩) = 1 := by
        rw [map_mul, map_inv, hu'β, inv_mul_cancel]
      have hfix := (C.β_ker _).1 hk
      have hcalc : ((u'⁻¹ * ⟨u, huc⟩ : ↥(commV (autI C.hV K))) : IntMod V C.hV).val =
          ((u' : IntMod V C.hV).val)⁻¹ * x := by
        rw [← hux]
        rfl
      have hz : ((u' : IntMod V C.hV).val)⁻¹ * x ∈ blockZ K := by
        rw [← hcalc]
        refine ⟨?_, (mem_fixV_autI_iff C.hV hKV).1 hfix⟩
        rw [hU]
        exact val_mem_commutator_of_mem_commV C.hV (u'⁻¹ * ⟨u, huc⟩).2
      have hx' : x = (u' : IntMod V C.hV).val * (((u' : IntMod V C.hV).val)⁻¹ * x) := by group
      rw [hx']
      exact W.mul_mem hu'W (hZW hz)

include hs in
theorem isAltBlockTypeWith_B8 (hC129 : ASC129Statement G) (h : Hyp27 H R M K)
    (hR : C.bar R = Subgroup.zpowers (swap 0 1)) :
    IsAltBlockTypeWith K 8 (C.alphaB8 hs) := by
  have hU := C.blockU_eq_commutator_B8 hs hC129 h hR
  have hKV := hs.K_le_normalizer_V
  let e : ↥(blockU K) ≃* ↥(commV (autI C.hV K)) :=
    (MulEquiv.subgroupCongr hU).trans (C124.commEquiv C.hV hKV).symm
  have he : ∀ x : ↥(blockU K), ((e x : ↥(commV (autI C.hV K))) : IntMod V C.hV).val = x :=
    fun x => C124.commEquiv_symm_val C.hV hKV _
  let β' : ↥(blockU K) →* Multiplicative (AltHeart 8) :=
    (C124.altQuotEquiv 8 (by norm_num)).toMonoidHom.comp (C.β.comp e.toMonoidHom)
  refine ⟨C.alphaB8_surjective hs, C.ker_alphaB8 hs, β', ?_, ?_, ?_⟩
  · exact (C124.altQuotEquiv 8 (by norm_num)).surjective.comp (C.β_surj.comp e.surjective)
  · have hinj : ∀ d : C124.YZ.DM 8, C124.altQuotEquiv 8 (by norm_num) d = 1 ↔ d = 1 :=
      fun d => map_eq_one_iff _ (C124.altQuotEquiv 8 (by norm_num)).injective
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show C124.altQuotEquiv 8 (by norm_num) (C.β (e x)) = 1 ↔ (x : G) ∈ blockZ K
    refine (hinj _).trans ?_
    rw [C.β_ker, mem_fixV_autI_iff C.hV hKV, he]
    exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
  · intro ℓ u v huv x hx
    set g : ↥(autOn (K ⊔ R) V) := starB8 hs.le_normalizer_V ⟨ℓ, Subgroup.mem_sup_left ℓ.2⟩
      with hgdef
    have hιg : C.ι g = (C.alphaB8 hs ℓ : Perm (Fin 8)) := rfl
    have hmem : ((g : MulAut ↥V) : MulAut (IntMod V C.hV)) (e u : IntMod V C.hV) ∈
        commV (autI C.hV K) :=
      C124.YZ.apply_mem_commV (C124.YZ.autI_normalizes C.hV hs.le_normalizer g.2) (e u).2
    have hev : e v = ⟨_, hmem⟩ := by
      apply Subtype.ext
      apply IntMod.val_injective
      rw [he]
      have hc : (((g : MulAut ↥V) : MulAut (IntMod V C.hV)) (e u : IntMod V C.hV)).val =
          (ℓ : G) * ((e u : ↥(commV (autI C.hV K))) : IntMod V C.hV).val * (ℓ : G)⁻¹ :=
        convI_apply_val C.hV ⟨ℓ, hKV ℓ.2⟩ _
      show (v : G) = (((g : MulAut ↥V) : MulAut (IntMod V C.hV)) (e u : IntMod V C.hV)).val
      rw [hc, he, huv, Subgroup.coe_inv]
    have h1 : C.β (e v) = C124.YZ.dAct 8 (C.alphaB8 hs ℓ) (C.β (e u)) := by
      rw [hev, C.β_equiv g (e u) hmem, hιg]
    show (QuotientAddGroup.mk (permWeight 8 (C.alphaB8 hs ℓ : Perm (Fin 8)) x) : AltHeart 8) =
      Multiplicative.toAdd (C124.altQuotEquiv 8 (by norm_num) (C.β (e v)))
    rw [h1]
    exact altQuotEquiv_dAct_B8 _ _ x hx

end CaseIICtx

theorem three_of_caseII_eight_swap01 (hC129 : ASC129Statement G) (h : Hyp27 H R M K)
    (C : CaseIICtx R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) 8)
    (hR : C.bar R = Subgroup.zpowers (Equiv.swap 0 1)) :
    C27Three H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) := by
  have hs := h.starHyp
  obtain ⟨t, htR, htV, hφt, -, hRt, hord⟩ := C.exists_t_B8 hs hR
  have hcompat : ∀ (k : G) (hk : k ∈ K) (hk' : t * k * t⁻¹ ∈ K),
      ((C.alphaB8 hs ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin 8)) : Perm (Fin 8)) =
        swap 0 1 * (C.alphaB8 hs ⟨k, hk⟩ : Perm (Fin 8)) * (swap 0 1)⁻¹ := by
    intro k hk hk'
    rw [CaseIICtx.coe_alphaB8, CaseIICtx.coe_alphaB8]
    have he : (⟨t * k * t⁻¹, Subgroup.mem_sup_left hk'⟩ : ↥(K ⊔ R)) =
        ⟨t, Subgroup.mem_sup_right htR⟩ * ⟨k, Subgroup.mem_sup_left hk⟩ *
          (⟨t, Subgroup.mem_sup_right htR⟩ : ↥(K ⊔ R))⁻¹ := Subtype.ext rfl
    rw [he, map_mul, map_mul, map_inv, hφt]
  exact Or.inr (Or.inl ⟨⟨8, C.alphaB8 hs, by norm_num, le_rfl, C.isShort2_B8 hs hC129 h hR,
    C.isAltBlockTypeWith_B8 hs hC129 h hR, t, htR, htV, hRt, hord, swap 0 1,
    ⟨0, 1, by decide, rfl⟩, hcompat⟩, C.autOn_MK_eq_B8 h hs hR⟩)

theorem three_of_caseII_eight_swap (hC129 : ASC129Statement G) (h : Hyp27 H R M K)
    (C : CaseIICtx R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) 8) {a b : Fin 8} (hab : a ≠ b)
    (hR : C.bar R = Subgroup.zpowers (Equiv.swap a b)) :
    C27Three H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) := by
  obtain ⟨π, hπa, hπb⟩ := exists_perm_eq_zero_one_B8 hab
  refine three_of_caseII_eight_swap01 hC129 h (C.conjB8 π) ?_
  rw [CaseIICtx.bar_conjB8, hR, MonoidHom.map_zpowers]
  congr 1
  show π * swap a b * π⁻¹ = swap 0 1
  rw [← swap_apply_apply, hπa, hπb]

end CFSG.Quasithin.SmithC27
