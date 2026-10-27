module

public import CFSG.Quasithin.MS93.S4A42W
public import CFSG.Quasithin.MS93.S4A42

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped Matrix commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)

section Step

include h hfull

theorem usup_eq_commutator_uloc {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) :
    Usup (puAmalgam h.le) α β = ⁅Uloc h.le L α, Qv _ β⁆ := by
  rw [Usup, zv_of_isMVtx _ hα]
  exact commutator_zm_eq_uloc h hfull hα (qv_le_stab_of_adj _ hαβ.symm)

theorem usup_le_usup_sup_dloc (hC : CentHyp (puAmalgam h.le))
    (hb : 2 < critDist (puAmalgam h.le)) {α β δ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) (hβδ : (puAmalgam h.le).treeGraph.Adj β δ)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {ψ : ↥(stab (puAmalgam h.le) α) →* ↥(StatedSL 3 F)} (hsurj : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc h.le L α) ⊥ ψ false 1)
    (hU : Usup (puAmalgam h.le) δ β ≤ Bloc h.le L α)
    (hcard : Nat.card ↥(Usup (puAmalgam h.le) α β) = Nat.card F ^ 2) :
    Usup (puAmalgam h.le) δ β ≤ Usup (puAmalgam h.le) α β ⊔ Dloc h.le L α := by
  have h20 := h.hyp20
  have hβ : ¬ IsMVtx (puAmalgam h.le) β := by
    rw [← isMVtx_iff_of_adj _ hαβ]
    exact hα
  have hδ : IsMVtx (puAmalgam h.le) δ := by
    by_contra hδ
    exact hβ ((isMVtx_iff_of_adj _ hβδ).mpr hδ)
  have hQβα : Qv (puAmalgam h.le) β ≤ stab _ α := qv_le_stab_of_adj _ hαβ.symm
  have hQδβ : Qv (puAmalgam h.le) δ ≤ Qv _ β := qv_le_qv _ h20 hδ hβδ.symm
  have hQαβ : Qv (puAmalgam h.le) α ≤ Qv _ β := qv_le_qv _ h20 hα hαβ
  have hWZ : Usup (puAmalgam h.le) δ β ≤ ZM _ δ := by
    rw [Usup, zv_of_isMVtx _ hδ]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((qv_le_stab_of_adj _ hβδ).trans (stab_le_normalizer_zm _ δ))
  by_cases hQ : Qv (puAmalgam h.le) δ = Qv _ α
  · have hZ : ZM (puAmalgam h.le) δ = ZM _ α := by
      rw [← xm_eq_zm h hfull hδ, ← xm_eq_zm h hfull hα, XM, XM, hQ]
    rw [Usup, Usup, zv_of_isMVtx _ hδ, zv_of_isMVtx _ hα, hZ]
    exact le_sup_left
  have hYU : ¬ Qv (puAmalgam h.le) δ ≤
      Subgroup.centralizer (Uloc h.le L α : Set (puAmalgam h.le).Universal) := by
    intro hc
    apply hQ
    refine qv_eq_of_le h hα hδ ?_
    rw [← hC α β hα hαβ]
    refine le_inf hQδβ ?_
    rw [zm_eq_uloc_sup_zloc h hfull hα, Subgroup.le_centralizer_iff]
    refine sup_le (Subgroup.le_centralizer_iff.mp hc) ?_
    exact (zloc_le_centralizer_stab h hfull hα).trans
      (Subgroup.centralizer_le (hQδβ.trans hQβα))
  have hUD : Usup (puAmalgam h.le) δ β ≤ Uloc h.le L α ⊔ Dloc h.le L α := by
    intro w hw
    have hwB := hU hw
    have hwV := ((mem_bloc_iff h hb hα).mp hwB)
    refine mem_uloc_sup_dloc h hfull hα hsurj hψ (vv_le_qv h hb hα hwV.1) (fun l hl => ?_)
      (hQδβ.trans hQβα) (fun y hy => ?_) ?_ ((isPGroup_qv _ h20 hβ).to_le hQδβ) hYU
    · rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ (hwV.2 l hl)
    · exact (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hδ (hWZ hw)) y hy)
    · exact hQαβ.trans ((qv_le_stab_of_adj _ hβδ).trans (stab_le_normalizer_qv _ δ))
  have hT2 : IsPGroup 2 ↥(natImage ψ (Qv (puAmalgam h.le) β)) := by
    have hT : IsPGroup 2 ↥((Qv (puAmalgam h.le) β).subgroupOf (stab (puAmalgam h.le) α)) :=
      (isPGroup_qv _ h20 hβ).of_equiv (Subgroup.subgroupOfEquivOfLe hQβα).symm
    exact hT.map _
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hrank : Module.finrank F (commN (natImage ψ (Qv (puAmalgam h.le) β))) = 2 := by
    have h1 := card_commutator_eq hψ hQβα
    rw [← usup_eq_commutator_uloc h hfull hα hαβ, hcard] at h1
    have h2 : Nat.card ↥(commN (natImage ψ (Qv (puAmalgam h.le) β))) =
        Nat.card F ^ Module.finrank F (commN (natImage ψ (Qv (puAmalgam h.le) β))) :=
      Module.natCard_eq_pow_finrank
    rw [h2] at h1
    exact (Nat.pow_right_injective hq h1).symm
  have hinv : ∀ g ∈ natImage ψ (Qv (puAmalgam h.le) β), ∀ x ∈ fixN (natImage ψ (Qv _ δ)),
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ fixN (natImage ψ (Qv _ δ)) := by
    intro g hg x hx
    obtain ⟨b, hbQ, rfl⟩ := mem_natImage.mp hg
    rw [mem_fixN] at hx ⊢
    intro t ht
    obtain ⟨y, hyQ, rfl⟩ := mem_natImage.mp ht
    have hby : ((b⁻¹ * y * b : ↥(stab (puAmalgam h.le) α)) : (puAmalgam h.le).Universal) ∈
        Qv (puAmalgam h.le) δ := by
      have := (Subgroup.mem_normalizer_iff.mp ((qv_le_stab_of_adj _ hβδ).trans
        (stab_le_normalizer_qv _ δ) (Subgroup.inv_mem _ hbQ)) _).mp hyQ
      simpa [mul_assoc] using this
    have hconj : toSL3 ψ y * toSL3 ψ b = toSL3 ψ b * toSL3 ψ (b⁻¹ * y * b) := by
      simp only [map_mul, map_inv]
      group
    have hfx := hx _ (mem_natImage.mpr ⟨b⁻¹ * y * b, hby, rfl⟩)
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, hconj,
      Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hfx]
  have hfixne : fixN (natImage ψ (Qv (puAmalgam h.le) δ)) ≠ ⊤ := by
    intro htop
    apply hYU
    intro y hy
    have h1 : toSL3 ψ ⟨y, (hQδβ.trans hQβα) hy⟩ = 1 := by
      apply eq_one_of_mulVec_eq_self
      intro x
      have hx : x ∈ fixN (natImage ψ (Qv (puAmalgam h.le) δ)) := htop ▸ Submodule.mem_top
      exact (mem_fixN.mp hx) _ (mem_natImage.mpr ⟨_, hy, rfl⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have := (toSL3_eq_one_iff hψ _).mp h1 u hu
    calc u * y = y * u * y⁻¹ * y := by rw [show y * u * y⁻¹ = u from this]
      _ = y * u := by group
  have hfixle := le_commN_of_invariant hT2 hrank hinv hfixne
  have hDn : stab (puAmalgam h.le) α ≤
      Subgroup.normalizer (Dloc h.le L α : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) α
  have hUs : Uloc h.le L α ≤ stab (puAmalgam h.le) α := puTrans_le_stab h.le _ α
  have hUD' : Uloc h.le L α ⊓ Dloc h.le L α = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxU, hxD⟩
    rw [Dloc, h.puTrans_Dq hα] at hxD
    have hUZ : Uloc h.le L α ⊓ Zloc h.le L α = ⊥ := uloc_inf_zloc h hfull α
    have hxZ : x ∈ Zloc h.le L α := by
      rw [Zloc, h.puTrans_Zq hα]
      exact ⟨xm_eq_zm h hfull hα ▸ uloc_le_zm h hfull hα hxU, hxD.2⟩
    have : x ∈ Uloc h.le L α ⊓ Zloc h.le L α := ⟨hxU, hxZ⟩
    rwa [hUZ] at this
  intro w hw
  have hw' : w ∈ ((Uloc h.le L α ⊔ Dloc h.le L α : Subgroup _) : Set _) := hUD hw
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hUs.trans hDn)] at hw'
  obtain ⟨u, hu, d, hd, rfl⟩ := hw'
  have huc : u ∈ Subgroup.centralizer (Qv (puAmalgam h.le) δ : Set (puAmalgam h.le).Universal) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hys : y ∈ stab (puAmalgam h.le) α := (hQδβ.trans hQβα) hy
    have hud : u = (u * d) * d⁻¹ := by group
    have hc1 : y * (u * d) * y⁻¹ = u * d :=
      by rw [(Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hδ (hWZ hw)) y hy),
        mul_inv_cancel_right]
    have hyd : y * d⁻¹ * y⁻¹ ∈ Dloc h.le L α :=
      (Subgroup.mem_normalizer_iff.mp (hDn hys) _).mp (Subgroup.inv_mem _ hd)
    have hcomm : u⁻¹ * (y * u * y⁻¹) ∈ Uloc h.le L α ⊓ Dloc h.le L α := by
      constructor
      · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hu)
          ((Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α
            hys) _).mp hu)
      · have : u⁻¹ * (y * u * y⁻¹) = d * (y * d⁻¹ * y⁻¹) := by
          have e1 : y * u * y⁻¹ = (y * (u * d) * y⁻¹) * (y * d⁻¹ * y⁻¹) := by group
          rw [e1, hc1]
          group
        rw [this]
        exact Subgroup.mul_mem _ hd hyd
    rw [hUD', Subgroup.mem_bot] at hcomm
    have : y * u * y⁻¹ = u := by
      have := congrArg (fun z => u * z) hcomm
      simpa using this
    calc y * u = y * u * y⁻¹ * y := by group
      _ = u * y := by rw [this]
  have huT : u ∈ Usup (puAmalgam h.le) α β := by
    rw [usup_eq_commutator_uloc h hfull hα hαβ]
    have h1 := (mem_centralizer_iff_natVec hψ (hQδβ.trans hQβα) ⟨u, hu⟩).mp huc
    exact (mem_commutator_iff_natVec hψ hQβα ⟨u, hu⟩).mpr (hfixle h1)
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left huT) (Subgroup.mem_sup_right hd)

end Step

section Min

include h

theorem imM_sup {K K' : Subgroup G} (hK : K ≤ M) (hK' : K' ≤ M) :
    imM h.le (K ⊔ K') = imM h.le K ⊔ imM h.le K' := by
  rw [imM, imM, imM, Subgroup.subgroupOf_sup hK hK', Subgroup.map_sup]

theorem usup_le_zh_base (hmin : PUMin M T L) {N : Subgroup (puAmalgam h.le).Universal}
    (hN : stab (puAmalgam h.le) (baseB _) ≤
      Subgroup.normalizer (N : Set (puAmalgam h.le).Universal))
    (hUN : Usup (puAmalgam h.le) (baseA _) (baseB _) ≤ N)
    (hND : N ≤ Usup (puAmalgam h.le) (baseA _) (baseB _) ⊔ Dloc h.le L (baseA _)) :
    Usup (puAmalgam h.le) (baseA _) (baseB _) ≤ ZH _ (baseB _) := by
  have h20 := h.hyp20
  have hα : IsMVtx (puAmalgam h.le) (baseA _) := PU.isMVtx_baseA _
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hUZ : Usup (puAmalgam h.le) (baseA _) (baseB _) ≤ ZM _ (baseA _) := by
    rw [Usup, zv_of_isMVtx _ hα]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((qv_le_stab_of_adj _ hαβ.symm).trans (stab_le_normalizer_zm _ _))
  have hDn : stab (puAmalgam h.le) (baseA _) ≤
      Subgroup.normalizer (Dloc h.le L (baseA _) : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) _
  have hZs : ZM (puAmalgam h.le) (baseA _) ≤ stab _ (baseA _) :=
    (zm_le_qv_self _ hα h.critDist_pos).trans (qv_le_stab _ _)
  set T₁ := Qv (puAmalgam h.le) (baseB _) ⊓
    Subgroup.centralizer (N : Set (puAmalgam h.le).Universal) with hT₁
  have hT₁n : stab (puAmalgam h.le) (baseB _) ≤
      Subgroup.normalizer (T₁ : Set (puAmalgam h.le).Universal) :=
    le_normalizer_inf (stab_le_normalizer_qv _ _) (le_normalizer_centralizer hN)
  have hLD : Ltil h.le L (baseA _) ≤ Subgroup.centralizer
      (Dloc h.le L (baseA _) : Set (puAmalgam h.le).Universal) := by
    rw [Subgroup.le_centralizer_iff, Dloc, h.puTrans_Dq hα]
    exact inf_le_right
  have hkey : (Ltil h.le L (baseA _) ⊔ T₁) ⊓ Qv _ (baseA _) ≤ T₁ := by
    rintro x ⟨hxLT, hxQ⟩
    refine ⟨qv_le_qv _ h20 hα hαβ hxQ, Subgroup.mem_centralizer_iff.mpr fun n hn => ?_⟩
    have hn' : n ∈ ((Usup (puAmalgam h.le) (baseA _) (baseB _) ⊔ Dloc h.le L (baseA _) :
        Subgroup _) : Set _) := hND hn
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ ((hUZ.trans hZs).trans hDn)] at hn'
    obtain ⟨u, hu, d, hd, rfl⟩ := hn'
    have hdN : d ∈ N := by
      have := N.mul_mem (N.inv_mem (hUN hu)) hn
      simpa using this
    have hxu : x * u = u * x :=
      Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hα (hUZ hu)) x hxQ
    have hLTc : Ltil h.le L (baseA _) ⊔ T₁ ≤ Subgroup.centralizer
        ((N ⊓ Dloc h.le L (baseA _) : Subgroup _) : Set (puAmalgam h.le).Universal) :=
      sup_le (hLD.trans (Subgroup.centralizer_le inf_le_right))
        (inf_le_right.trans (Subgroup.centralizer_le inf_le_left))
    have hxd : d * x = x * d := Subgroup.mem_centralizer_iff.mp (hLTc hxLT) d ⟨hdN, hd⟩
    calc u * d * x = u * (x * d) := by rw [mul_assoc, hxd]
      _ = x * (u * d) := by rw [← mul_assoc, ← hxu, mul_assoc]
  set T₁' : Subgroup G := (T₁.comap (puAmalgam.ofT h.le)).map T.subtype with hT₁'
  have hT₁'T : T₁' ≤ T := Subgroup.map_subtype_le _
  have hsub : T₁'.subgroupOf T = T₁.comap (puAmalgam.ofT h.le) := PU.map_subtype_subgroupOf _
  have hrange : imM h.le T = (puAmalgam.ofT h.le).range := by
    rw [imM_of_le h.le le_rfl, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
  have himT₁ : imM h.le T₁' = T₁ := by
    rw [imM_of_le h.le hT₁'T, hsub, Subgroup.map_comap_eq, inf_eq_right, ← hrange,
      ← puAmalgam.qv_baseB h.le]
    exact inf_le_left
  have hchar : (T₁'.subgroupOf T).Characteristic := by
    rw [hsub, Subgroup.characteristic_iff_map_le]
    intro σ
    rintro _ ⟨t, ht, rfl⟩
    show puAmalgam.ofT h.le (σ t) ∈ T₁
    have hg : (puAmalgam h.le).ofB (SemidirectProduct.inr σ) ∈ stab (puAmalgam h.le) (baseB _) := by
      rw [puAmalgam.stab_baseB]
      exact ⟨_, rfl⟩
    have heq : puAmalgam.ofT h.le (σ t) = (puAmalgam h.le).ofB (SemidirectProduct.inr σ) *
        puAmalgam.ofT h.le t * ((puAmalgam h.le).ofB (SemidirectProduct.inr σ))⁻¹ := by
      simp only [puAmalgam.ofT, MonoidHom.coe_comp, Function.comp_apply]
      rw [← map_inv, ← map_mul, ← map_mul, Hol.inr_mul_inl_mul_inr_inv]
    rw [heq]
    exact (Subgroup.mem_normalizer_iff.mp (hT₁n hg) _).mp ht
  have hmincond : (L ⊔ T₁') ⊓ pCoreOf 2 M ≤ T₁' := by
    have hKM : (L ⊔ T₁') ⊓ pCoreOf 2 M ≤ M := inf_le_right.trans (pCoreOf_le' M)
    rw [← imM_le_imM_iff h.le hKM, imM_inf, imM_sup h h.L_le (hT₁'T.trans h.le), himT₁,
      ← puTrans_baseA h.le (S4A.L_normal h),
      ← puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le]
    exact hkey
  have hT₁eq : T₁' = T := hmin T₁' hT₁'T hchar hmincond
  have hT₁top : T₁ = Qv (puAmalgam h.le) (baseB _) := by
    rw [← himT₁, hT₁eq, puAmalgam.qv_baseB]
  intro x hx
  have hxZ : x ∈ ZM (puAmalgam h.le) (baseA _) := hUZ hx
  have hxQ : x ∈ Qv (puAmalgam h.le) (baseB _) :=
    qv_le_qv _ h20 hα hαβ (zm_le_qv_self _ hα h.critDist_pos hxZ)
  have hxc : x ∈ Subgroup.centralizer
      (Qv (puAmalgam h.le) (baseB _) : Set (puAmalgam h.le).Universal) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyT₁ : y ∈ T₁ := hT₁top ▸ hy
    exact (Subgroup.mem_centralizer_iff.mp hyT₁.2 x (hUN hx)).symm
  have hx2 : x ^ 2 = 1 := (isElemAbelian_zm _ h20 h.critDist_pos hα).2 x hxZ
  exact Subgroup.subset_closure ⟨⟨hxQ, hxc⟩, hx2⟩

end Min

end CFSG.Quasithin.MS93.S4A

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

theorem s42_of (h32 : S32) : S42 := by
  intro G _ _ M T L h hmin hb F _ _ φ hφ α β hα hαβ
  have hfull : IsSL3Full M T L :=
    isSL3Full_iff_exists_via.mpr ⟨F, inferInstance, inferInstance, φ, hφ⟩
  refine ⟨fun hU hcard => ?_,
    fun Y hYn hYQ hVY => S4A.commutator_vv_le_dloc h hfull hb hα hYn hYQ hVY⟩
  have hC := centHyp_of_S32 h32 h
  obtain ⟨n, hn⟩ := hφ.1
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
  have : CharP F 2 := FFC.charP_two_of_card_pow hFn
  rw [← Nat.card_eq_fintype_card] at hcard
  obtain ⟨g, rfl, rfl⟩ := exists_smul_base_edge _ hα hαβ
  rw [usup_smul, zh_smul]
  refine Subgroup.map_mono ?_
  have hα0 : IsMVtx (puAmalgam h.le) (baseA _) := PU.isMVtx_baseA _
  have hαβ0 := adj_baseA_baseB (puAmalgam h.le)
  obtain ⟨ψ, hsurj, hψ⟩ := exists_natural_Uloc h hφ hα0
  have hU0 : ∀ δ, (puAmalgam h.le).treeGraph.Adj (baseB _) δ →
      Usup (puAmalgam h.le) δ (baseB _) ≤ Bloc h.le L (baseA _) := by
    intro δ hδ
    have := hU (g • δ) ((adj_smul _ g _ _).mpr hδ)
    rw [usup_smul, bloc_smul h] at this
    exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective).mp this
  have hcard0 : Nat.card ↥(Usup (puAmalgam h.le) (baseA _) (baseB _)) = Nat.card F ^ 2 := by
    rw [usup_smul, Subgroup.card_map_of_injective (MulAut.conj g).injective] at hcard
    exact hcard
  set N := ⨆ δ ∈ (puAmalgam h.le).treeGraph.neighborSet (baseB _),
    Usup (puAmalgam h.le) δ (baseB _) with hNdef
  have hN : stab (puAmalgam h.le) (baseB _) ≤
      Subgroup.normalizer (N : Set (puAmalgam h.le).Universal) := by
    refine le_normalizer_of_map_conj_le fun s hs => ?_
    rw [hNdef, Subgroup.map_iSup]
    refine iSup_le fun δ => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hδ => ?_
    have hsβ : s • baseB (puAmalgam h.le) = baseB _ := (mem_stab _).mp hs
    rw [← usup_smul, hsβ]
    refine le_iSup₂_of_le (f := fun δ (_ : δ ∈ (puAmalgam h.le).treeGraph.neighborSet (baseB _)) =>
      Usup (puAmalgam h.le) δ (baseB _)) (s • δ) ?_ le_rfl
    rw [SimpleGraph.mem_neighborSet, ← hsβ]
    exact (adj_smul _ s _ _).mpr hδ
  have hUN : Usup (puAmalgam h.le) (baseA _) (baseB _) ≤ N :=
    le_iSup₂_of_le (f := fun δ (_ : δ ∈ (puAmalgam h.le).treeGraph.neighborSet (baseB _)) =>
      Usup (puAmalgam h.le) δ (baseB _)) (baseA _) hαβ0.symm le_rfl
  have hND : N ≤ Usup (puAmalgam h.le) (baseA _) (baseB _) ⊔ Dloc h.le L (baseA _) :=
    iSup₂_le fun δ hδ => S4A.usup_le_usup_sup_dloc h hfull hC hb hα0 hαβ0 hδ hsurj hψ
      (hU0 δ hδ) hcard0
  exact S4A.usup_le_zh_base h hmin hN hUN hND

end CFSG.Quasithin.MS93
