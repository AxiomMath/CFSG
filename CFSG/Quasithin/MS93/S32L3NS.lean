module

public import CFSG.Quasithin.Background.B15P4Res
public import CFSG.Quasithin.MS93.ML3Split
public import CFSG.Quasithin.MS93.M15L3
public import CFSG.Quasithin.MS93.S32Main
public import CFSG.Quasithin.MS93.S32Types

public section

namespace CFSG.Quasithin.MS93.S32

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.JonesParshall
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem map_commV_eq {V : Type*} [CommGroup V] {K : Subgroup (MulAut V)} {σ : MulAut V}
    (hσ : σ ∈ Subgroup.normalizer (K : Set (MulAut V))) :
    (commV K).map σ.toMonoidHom = commV K := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact B15P4.map_commV_mem hσ v hv
  · intro v hv
    refine ⟨σ⁻¹ v, B15P4.map_commV_mem (Subgroup.inv_mem _ hσ) v hv, ?_⟩
    show σ (σ⁻¹ v) = v
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]

theorem autI_T_ne_bot (h : PUHyp M T L) : autI h.isElemAbelian_Xq T ≠ ⊥ := by
  intro hb
  have hT : T ≤ Subgroup.centralizer (Xq M : Set G) :=
    (autI_eq_bot_iff _ (h.le.trans (le_normalizer_Xq M))).1 hb
  have hΩ : omegaOneCenterOf T = Xq M := by
    rw [h.omegaOneCenterOf_eq]
    refine inf_eq_left.2 fun x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact (Subgroup.mem_centralizer_iff.mp (hT ht) x hx).symm
  exact h.noChar _ (PU.omegaOneCenterOf_le T) (PU.omegaOneCenterOf_ne_bot h.isPGroup h.ne_bot)
    (CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf T) (hΩ ▸ le_normalizer_Xq M)

theorem s32PartL3NonSplit_of (h51 : AsB51) (hSQ : SQTKQuot)
    (hT : TypeFacts) : S32PartL3NonSplit := by
  intro G _ _ M T L h F _ _ n hF hreal hC hXL hns
  set hX := h.isElemAbelian_Xq with hXdef
  have hs := isSecW_Xq h
  have hLX : L ≤ Subgroup.normalizer (Xq M : Set G) := hs.L_le_normalizer h
  have hMX : M ≤ Subgroup.normalizer (Xq M : Set G) := le_normalizer_Xq M
  have hUZ := Uq_inf_Zq_eq_bot h hC
  have hCX : fixV (autI hX L) ⊓ commV (autI hX L) = ⊥ := by
    rw [← C124.toG_inj hX, C124.toG, Subgroup.map_inf _ _ _ (C124.valHom_injective hX),
      ← C124.toG, ← C124.toG, toG_commV_Xq h, toG_fixV_Xq h, hXL, inf_comm, hUZ, toG_bot]
  obtain ⟨-, ⟨-, hP2⟩, -, -, -, -⟩ := b51_Xq h h51 hSQ
  have hdir : ¬ IsIntDirect (commV (autI hX L)) (fixV (autI hX L)) ⊤ := by
    intro hd
    obtain ⟨hsup, -⟩ := (isIntDirect_Xq_iff h).mp hd
    rw [hXL] at hsup
    exact hns hsup
  obtain ⟨-, hlist⟩ := hP2 hdir
  obtain ⟨π₀, hπ₀⟩ := id hreal
  obtain ⟨hn, hUc⟩ := card_lstar_of_sl3 (isSecW_Uq h) h hF hπ₀
  have hbin : BinaryNaturalSL (autI hX L) (commV (autI hX L)) ⊥ 3 1 := by
    rw [← hCX]
    rcases hlist with ⟨m, F', iF', fF', hF', π', hπ'⟩ | ⟨m, F', iF', fF', hF', π', hπ'⟩ |
      ⟨m, F', iF', fF', hF', π', hπ'⟩ | ⟨π', hπ'⟩ | ⟨π', hπ'⟩ | ⟨F', iF', fF', hF', π', hπ'⟩ |
      hsl
    · exact (false_of_sl2 hs h hT hF' hπ').elim
    · obtain ⟨hm, hc⟩ := card_lstar_of_sp4 hs h hF' hπ'
      exact (CFSG.Timmesfeld.Orders.ordA_ne_ordBC_two (by norm_num) hn (by omega)
        (hUc.symm.trans hc)).elim
    · obtain ⟨hm, hc⟩ := card_lstar_of_g2 hs h hT hF' hπ'
      exact (ordA_two_ne_ordG2 hn hm (hUc.symm.trans hc)).elim
    · exact (ordA_two_ne_360 hn (hUc.symm.trans (card_lstar_of_alt6 hs h hπ'))).elim
    · exact (false_of_alt8 hs h hT hπ').elim
    · exact (ordA_two_ne_6048 hn (hUc.symm.trans (card_lstar_of_g2d hs h hT hF' hπ'))).elim
    · exact hsl
  have hn1 : n = 1 := by
    obtain ⟨F', iF', fF', hF', π', hπ'⟩ := id hbin
    exact eq_one_of_ordA_two hn (hUc.symm.trans (card_lstar_of_sl3 hs h hF' hπ').2)
  obtain ⟨D⟩ := FFC.exists_natQuot3 hbin
  have hKinv : ∀ g ∈ autI hX L, ∀ w ∈ commV (autI hX L), g w ∈ commV (autI hX L) :=
    fun g hg w hw => B15P4.map_commV_mem (Subgroup.le_normalizer hg) w hw
  have hKc : ∀ g ∈ autI hX L, ∀ v, g v * v⁻¹ ∈ commV (autI hX L) :=
    fun g hg v => Subgroup.subset_closure ⟨g, hg, v, rfl⟩
  have hcent := hs.cent h
  have htwo := hs.two h
  have hZK : Subgroup.center ↥(autI hX L) = ⊥ := by
    obtain ⟨F', iF', fF', hF', π', hπ'⟩ := id hbin
    exact B5.Ln.center_eq_bot_of_equiv (hF'.trans (pow_one 2))
      (FFC.equivOfRealizes (FFModel.nat_faithful _) hπ').symm
  have hXM : autI hX M = autI hX L := by
    refine le_antisymm (fun σ hσ => ?_) (hs.autI_L_le h)
    have hσN := hs.autI_le_normalizer h hσ
    obtain ⟨l₀, hl₀, hc⟩ := A6Twist.inner_of_stable_nat3 hbin hσN (map_commV_eq hσN)
      (Subgroup.map_bot _)
    set c := σ * l₀⁻¹ with hcdef
    have hcX : c ∈ autI hX M := (autI hX M).mul_mem hσ ((autI hX M).inv_mem (hs.autI_L_le h hl₀))
    obtain ⟨e, he⟩ := htwo σ hσ
    have hce : c ^ 2 ^ e = σ ^ 2 ^ e * (l₀ ^ 2 ^ e)⁻¹ := by
      have hcl : Commute c l₀ := hc l₀ hl₀
      have hσc : σ = c * l₀ := by rw [hcdef, inv_mul_cancel_right]
      rw [hσc, hcl.mul_pow, mul_inv_cancel_right]
    have hceK : c ^ 2 ^ e ∈ autI hX L := by
      rw [hce]
      exact (autI hX L).mul_mem he ((autI hX L).inv_mem ((autI hX L).pow_mem hl₀ _))
    have hce1 : c ^ 2 ^ e = 1 := by
      have hz : (⟨c ^ 2 ^ e, hceK⟩ : ↥(autI hX L)) ∈ Subgroup.center ↥(autI hX L) := by
        rw [Subgroup.mem_center_iff]
        intro k
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        exact (Commute.pow_left (hc k k.2) (2 ^ e)).eq.symm
      rw [hZK, Subgroup.mem_bot] at hz
      exact congrArg Subtype.val hz
    have hc1 : c = 1 := hcent c hcX (fun k hk => hc k hk) e hce1
    have : σ = l₀ := by rw [hcdef, mul_inv_eq_one] at hc1; exact hc1
    rw [this]
    exact hl₀
  have hTK : autI hX T ≤ autI hX L := hXM ▸ autI_mono hX h.le
  have hT2 : IsPGroup 2 ↥(autI hX T) :=
    IsPGroup.of_surjective h.isPGroup (toAutI hX (h.le.trans hMX))
      (toAutI_surjective hX (h.le.trans hMX))
  obtain ⟨t, htT, ht1, ht2⟩ : ∃ t ∈ autI hX T, t ≠ 1 ∧ t ^ 2 = 1 := by
    obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (autI_T_ne_bot h)
    obtain ⟨m, hm1, hm2⟩ := exists_pow_invol hT2 x.2 (fun h1 => hx1 (Subtype.ext h1))
    exact ⟨_, (autI hX T).pow_mem x.2 m, hm1, hm2⟩
  have hfixt : fixV (Subgroup.zpowers t) ≤ commV (autI hX L) ⊔ fixV (autI hX L) := by
    intro v hv
    have hA : Subgroup.zpowers t ≤ autI hX L := (Subgroup.zpowers_le).2 (hTK htT)
    refine FFC.mem_sup_fixV_of_B1A hKinv hKc v (D.hR (fun z hz _ _ => by
        rw [Subgroup.mem_bot] at hz; rw [hz, map_one]) hA
      ((Subgroup.zpowers_ne_bot).2 ht1) (fun a ha => ?_) hKinv _
      (FFC.cocy_mem_Z1A hKinv hKc v) ⟨0, fun a ha => ?_⟩)
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]
    · apply Additive.toMul.injective
      apply Subtype.ext
      rw [FFC.muW_sub_apply]
      show (a : MulAut _) v * v⁻¹ = (a : MulAut _) 1 * (1 : _)⁻¹
      rw [hv _ ha, map_one, mul_inv_cancel, mul_inv_cancel]
  have hTN : T ≤ Subgroup.normalizer (Xq M : Set G) := h.le.trans hMX
  have hCT : omegaOneCenterOf T ≤ Uq M T L ⊔ Zq M L := by
    rw [h.omegaOneCenterOf_eq]
    have h1 : fixV (autI hX T) ≤ commV (autI hX L) ⊔ fixV (autI hX L) :=
      (fixV_anti ((Subgroup.zpowers_le).2 htT)).trans hfixt
    have h2 := (C124.toG_le_iff hX).2 h1
    rw [toG_fixV hX hTN, C124.toG, Subgroup.map_sup, ← C124.toG, ← C124.toG, toG_commV_Xq h,
      toG_fixV_Xq h, hXL] at h2
    exact h2
  have hZT : Zq M L ≤ omegaOneCenterOf T := by
    rw [h.omegaOneCenterOf_eq, ← toG_fixV_Xq h, ← toG_fixV hX hTN]
    exact (C124.toG_le_iff hX).2 (fixV_anti hTK)
  have hZ0 : Z0q M T = Zq M L ⊔ Uq M T L := by
    rw [h.Z0q_eq_sup]
    refine le_antisymm (sup_le (hCT.trans_eq (sup_comm _ _)) le_sup_right) ?_
    exact sup_le (hZT.trans le_sup_left) le_sup_right
  refine ⟨hZ0, by rw [inf_comm]; exact hUZ, ?_, ?_⟩
  ·
    have hsupX : C124.toG hX (commV (autI hX L) ⊔ fixV (autI hX L)) = Z0q M T := by
      rw [C124.toG, Subgroup.map_sup, ← C124.toG, ← C124.toG, toG_commV_Xq h, toG_fixV_Xq h,
        hXL, hZ0, sup_comm]
    have hind : (commV (autI hX L) ⊔ fixV (autI hX L)).index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      have hne : commV (autI hX L) ⊔ fixV (autI hX L) ≠ ⊤ := by
        intro htop
        apply hns
        have := congrArg (C124.toG hX) htop
        rw [C124.toG, Subgroup.map_sup, ← C124.toG, ← C124.toG, toG_commV_Xq h, toG_fixV_Xq h,
          hXL, toG_top] at this
        exact this
      obtain ⟨a, -, ha⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hne)
      refine ⟨a, fun b => ?_⟩
      rcases FFC.sup_fixV_natural3 hKinv hKc D b (b * a) with hb | hba | hd
      · refine Or.inr ⟨hb, fun hba => ha ?_⟩
        have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) hba
        rwa [inv_mul_cancel_left] at this
      · exact Or.inl ⟨hba, fun hb => ha (by
          have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) hba
          rwa [inv_mul_cancel_left] at this)⟩
      · exfalso
        apply ha
        have e : b * (b * a)⁻¹ = a⁻¹ := by
          rw [mul_inv_rev, mul_comm a⁻¹ b⁻¹, mul_inv_cancel_left]
        rw [e] at hd
        simpa using Subgroup.inv_mem _ hd
    have hrel : (C124.toG hX (commV (autI hX L) ⊔ fixV (autI hX L))).relIndex
        (C124.toG hX ⊤) = 2 := by
      rw [C124.toG, C124.toG,
        Subgroup.relIndex_map_map_of_injective _ _ (C124.valHom_injective hX),
        Subgroup.relIndex_top_right]
      exact hind
    rwa [hsupX, toG_top] at hrel
  ·
    subst hn1
    obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod ⟨F, inferInstance, inferInstance, hF, hreal⟩
    obtain ⟨α, hα, hsum⟩ :=
      isSumNat_one_of_realizesVia h.isElemAbelian_Uq ((isSecW_Uq h).L_le_normalizer h) hπ
    rw [toG_bot] at hsum
    exact ⟨α, hα, hsum⟩

end CFSG.Quasithin.MS93.S32
