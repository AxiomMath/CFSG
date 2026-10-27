module

public import CFSG.Quasithin.EmptyFaithful.S153Sub

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417

section Generic

variable {G : Type} [Group G] [Finite G]

theorem eq_of_inf_normalizer_le {P S : Subgroup G} (hP : IsPGroup 2 P) (hSP : S ≤ P)
    (hN : P ⊓ Subgroup.normalizer (S : Set G) ≤ S) : S = P := by
  by_contra hne
  have hIPlt : S.subgroupOf P < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hne ?_
    refine le_antisymm hSP fun x hx => ?_
    have : (⟨x, hx⟩ : P) ∈ S.subgroupOf P := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.mp this
  have : Group.IsNilpotent P := hP.isNilpotent
  have hnc : NormalizerCondition P := Group.normalizerCondition_of_isNilpotent (G := P)
  have hlt : S.subgroupOf P < Subgroup.normalizer ((S.subgroupOf P : Subgroup P) : Set P) :=
    hnc _ hIPlt
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt hlt
  have hxNorm : (x : G) ∈ Subgroup.normalizer (S : Set G) := by
    have hxsub : x ∈ (Subgroup.normalizer (S : Set G)).subgroupOf P := by
      rw [Subgroup.subgroupOf_normalizer_eq hSP]
      exact hxN
    exact Subgroup.mem_subgroupOf.mp hxsub
  exact hxnot (Subgroup.mem_subgroupOf.mpr (hN ⟨x.2, hxNorm⟩))

theorem isSylowTwoOf_of_normalizer_le {K S M : Subgroup G} (hSK : S ≤ K)
    (hNM : Subgroup.normalizer (S : Set G) ≤ M) (hSyl : IsSylowTwoOf S (K ⊓ M)) :
    IsSylowTwoOf S K := by
  rw [A4.isSylowTwoOf_iff_maximal] at hSyl ⊢
  refine ⟨hSK, hSyl.2.1, fun P hPK hP hSP => ?_⟩
  have h1 : P ⊓ Subgroup.normalizer (S : Set G) ≤ S :=
    hSyl.2.2 _ (le_inf (inf_le_left.trans hPK) (inf_le_right.trans hNM)) hP.to_inf_left
      (le_inf hSP Subgroup.le_normalizer)
  exact (eq_of_inf_normalizer_le hP hSP h1).ge

end Generic

section Bridge

variable {G : Type} [Group G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

theorem mem_of_convI_mem_autI {X K : Subgroup G} (hXN : X ≤ Subgroup.normalizer (V : Set G))
    (hKX : K ≤ X) (hC : X ⊓ Subgroup.centralizer (V : Set G) ≤ K) {x : G} (hx : x ∈ X)
    (hxK : convI hV ⟨x, hXN hx⟩ ∈ autI hV K) : x ∈ K := by
  obtain ⟨k, hkK, hk⟩ := (mem_autI hV).1 hxK
  have h1 : convI hV (⟨x, hXN hx⟩ * k⁻¹) = 1 := by rw [map_mul, map_inv, hk, mul_inv_cancel]
  have h2 : x * (k : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) := (convI_eq_one_iff hV _).1 h1
  have h3 : x * (k : G)⁻¹ ∈ X := X.mul_mem hx (X.inv_mem (hKX hkK))
  have h4 : x * (k : G)⁻¹ ∈ K := hC ⟨h3, h2⟩
  have : x = (x * (k : G)⁻¹) * k := by group
  rw [this]
  exact K.mul_mem h4 hkK

theorem inf_centralizer_eq_of_autI_eq {X K : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hKN : K ≤ Subgroup.normalizer (V : Set G))
    (h : autI hV X = autI hV K) :
    V ⊓ Subgroup.centralizer (X : Set G) = V ⊓ Subgroup.centralizer (K : Set G) := by
  ext v
  constructor
  · rintro ⟨hvV, hvX⟩
    refine ⟨hvV, ?_⟩
    have h1 : IntMod.mk hV ⟨v, hvV⟩ ∈ fixV (autI hV X) := (mem_fixV_autI hV hXN _).2 hvX
    rw [h] at h1
    exact (mem_fixV_autI hV hKN _).1 h1
  · rintro ⟨hvV, hvK⟩
    refine ⟨hvV, ?_⟩
    have h1 : IntMod.mk hV ⟨v, hvV⟩ ∈ fixV (autI hV K) := (mem_fixV_autI hV hKN _).2 hvK
    rw [← h] at h1
    exact (mem_fixV_autI hV hXN _).1 h1

end Bridge

section Model

variable {G : Type} [Group G] [Finite G] {V M T : Subgroup G} (hV : IsElemAbelian 2 V)
  {L₁ L₂ : Subgroup (MulAut (IntMod V hV))} {tb : MulAut (IntMod V hV)}

theorem card_le_of_isFFStarOffender {W : Type*} [CommGroup W] [Finite W]
    {X A : Subgroup (MulAut W)} (hA : IsFFStarOffender X A) :
    Nat.card W ≤ Nat.card A * Nat.card (fixV A) := by
  have := hA.card_le (bot_le : (⊥ : Subgroup (MulAut W)) ≤ A)
  rwa [B1.card_bot_mul_card_fixV] at this

theorem autI_thompsonJ_eq (hS : OfourStruct (autI hV M) L₁ L₂ tb) (hTM : T ≤ M)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) (hVT : V ≤ T)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (hsyl : IsSylowTwoOf (autI hV T) (autI hV M)) :
    autI hV (thompsonJ T) = autI hV T ⊓ (L₁ ⊔ L₂) := by
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTM.trans hMN
  obtain ⟨-, -, hJeq, -⟩ := B2_7_of_not_le hV hVT hTN hJ
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF, hoff⟩ := hS.offender_classification hsyl
  rw [hJeq]
  have hmem : ∀ B ∈ offenderImages hV T, B ≤ ffJP (offenderImages hV T) (autI hV T) :=
    fun B hB => le_iSup₂_of_le B hB
      (le_iSup_of_le (offenderImages_isFFStarOffender hV hVT hTN hB).1 le_rfl)
  apply le_antisymm
  · refine iSup_le fun B => iSup_le fun hB => iSup_le fun hBT => ?_
    have hFF := offenderImages_isFFStarOffender hV hVT hTN hB
    exact (hoff B hBT hFF.2.1 hFF.2.2.1 (card_le_of_isFFStarOffender hFF)).1
  · obtain ⟨B₀, hB₀⟩ := (offenderImages_nonempty_iff_not_le hV).2 hJ
    have hFF₀ := offenderImages_isFFStarOffender hV hVT hTN hB₀
    have hτT : τ ∈ autI hV T := hF.τ_T
    have hcl := (hoff B₀ hFF₀.1 hFF₀.2.1 hFF₀.2.2.1 (card_le_of_isFFStarOffender hFF₀)).2
    have hs : s₁ ∈ ffJP (offenderImages hV T) (autI hV T) ∧
        s₂ ∈ ffJP (offenderImages hV T) (autI hV T) := by
      have hB₁ := offenderImages_conj hV hB₀ hτT
      rcases hcl with hs | hs
      · refine ⟨hmem B₀ hB₀ hs, hmem _ hB₁ ⟨s₁, hs, ?_⟩⟩
        simpa [MulAut.conj_apply] using hF.τs₁
      · refine ⟨hmem _ hB₁ ⟨s₂, hs, ?_⟩, hmem B₀ hB₀ hs⟩
        simpa [MulAut.conj_apply] using hF.τs₂
    intro x hx
    rcases (hF.S_eq x).1 hx with h1 | h1 | h1 | h1
    · rw [h1]; exact Subgroup.one_mem _
    · rw [h1]; exact hs.1
    · rw [h1]; exact hs.2
    · rw [h1]; exact Subgroup.mul_mem _ hs.1 hs.2

theorem thompsonJ_le_nS (hS : OfourStruct (autI hV M) L₁ L₂ tb) (hTM : T ≤ M)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) (hVT : V ≤ T)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (hsyl : IsSylowTwoOf (autI hV T) (autI hV M)) :
    thompsonJ T ≤
      T ⊓ Subgroup.normalizer (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) := by
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTM.trans hMN
  have hJbar := autI_thompsonJ_eq hV hS hTM hMN hVT hJ hsyl
  have hSbar := autI_nS hV hS hTM
  intro x hx
  have hxT : x ∈ T := (iSup_le fun _ => iSup_le fun hA => hA.1 : thompsonJ T ≤ T) hx
  refine ⟨hxT, ?_⟩
  have hxJ : convI hV ⟨x, hTN hxT⟩ ∈ autI hV (thompsonJ T) := convI_mem_autI hV hx (hTN hxT)
  rw [hJbar, ← hSbar] at hxJ
  exact (mem_of_convI_mem_autI hV hTN inf_le_left
    (inf_centralizer_le_nS T _ (map_inclMod_le hV _)) hxT hxJ).2

end Model

section ZS

variable {G : Type} [Group G] [Finite G] {V M T : Subgroup G} (hV : IsElemAbelian 2 V)
  {L₁ L₂ : Subgroup (MulAut (IntMod V hV))} {tb : MulAut (IntMod V hV)}

theorem inf_centralizer_ZS_le_nS (hS : OfourStruct (autI hV M) L₁ L₂ tb) (hTM : T ≤ M)
    (hMN : M ≤ Subgroup.normalizer (V : Set G))
    (hsyl : IsSylowTwoOf (autI hV T) (autI hV M)) :
    T ⊓ Subgroup.centralizer ((V ⊓ Subgroup.centralizer
        ((T ⊓ Subgroup.normalizer (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) :
          Subgroup G) : Set G) : Subgroup G) : Set G) ≤
      T ⊓ Subgroup.normalizer (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) := by
  set V₁ : Subgroup G := (commV L₁).map (inclMod hV) with hV₁
  set S : Subgroup G := T ⊓ Subgroup.normalizer (V₁ : Set G) with hSdef
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTM.trans hMN
  have hSbar : autI hV S = autI hV T ⊓ (L₁ ⊔ L₂) := autI_nS hV hS hTM
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF⟩ := hS.exists_sylowFacts hsyl
  rintro b ⟨hbT, hbC⟩
  by_contra hbS
  have hbN : b ∈ Subgroup.normalizer (V : Set G) := hTN hbT
  have hbbar : convI hV ⟨b, hbN⟩ ∈ autI hV T := convI_mem_autI hV hbT hbN
  have hnot : convI hV ⟨b, hbN⟩ ∉ autI hV T ⊓ (L₁ ⊔ L₂) := fun hmem => hbS (by
    rw [← hSbar] at hmem
    exact mem_of_convI_mem_autI hV hTN (inf_le_left : S ≤ T)
      (inf_centralizer_le_nS T V₁ (map_inclMod_le hV _)) hbT hmem)
  have hcos : convI hV ⟨b, hbN⟩ * τ⁻¹ ∈ autI hV T ⊓ (L₁ ⊔ L₂) :=
    (coset_of_relIndex_two (hS.relIndex_S hsyl) hbbar hF.τ_T
      (fun hτS => hF.τ_N hτS.2)).resolve_left hnot
  have ha₂ : ∀ x ∈ autI hV T ⊓ (L₁ ⊔ L₂), x a₂ = a₂ := fun x hx =>
    (hF.sylow.fixS a₂).2 (Or.inr (Or.inr (Or.inl rfl))) x hx
  have ha₁ : ∀ x ∈ autI hV T ⊓ (L₁ ⊔ L₂), x a₁ = a₁ := fun x hx =>
    (hF.sylow.fixS a₁).2 (Or.inr (Or.inl rfl)) x hx
  have hba : convI hV ⟨b, hbN⟩ a₁ = a₂ := by
    have e : convI hV ⟨b, hbN⟩ = (convI hV ⟨b, hbN⟩ * τ⁻¹) * τ := by group
    rw [e, MulAut.mul_apply, hF.τa₁, ha₂ _ hcos]
  have ha₁Z : a₁.val ∈ V ⊓ Subgroup.centralizer (S : Set G) := by
    refine ⟨a₁.val_mem, ?_⟩
    have : a₁ ∈ fixV (autI hV S) := by
      rw [hSbar]
      exact mem_fixV.2 ha₁
    exact (mem_fixV_autI hV (inf_le_left.trans hTN) a₁).1 this
  have hbc : a₁.val * b = b * a₁.val := Subgroup.mem_centralizer_iff.mp hbC _ ha₁Z
  have hfix : convI hV ⟨b, hbN⟩ a₁ = a₁ := by
    apply IntMod.val_injective
    rw [convI_apply_val]
    calc b * a₁.val * b⁻¹ = (a₁.val * b) * b⁻¹ := by rw [hbc]
      _ = a₁.val := by group
  exact hF.a_ne (hfix.symm.trans hba)

theorem baum_le_nS_of_not_le (hS : OfourStruct (autI hV M) L₁ L₂ tb) (hTM : T ≤ M)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) (hVT : V ≤ T)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (hsyl : IsSylowTwoOf (autI hV T) (autI hV M)) :
    baum T ≤ T ⊓ Subgroup.normalizer (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) := by
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTM.trans hMN
  have hJS := thompsonJ_le_nS hV hS hTM hMN hVT hJ hsyl
  intro b hb
  have hb' : b ∈ T ⊓ Subgroup.centralizer (omegaOneCenterOf (thompsonJ T) : Set G) := hb
  have hZE : V ⊓ Subgroup.centralizer
      ((T ⊓ Subgroup.normalizer (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) :
        Subgroup G) : Set G) ≤ omegaOneCenterOf (thompsonJ T) := by
    rw [(omegaOne_centralizer_thompsonJ T).2]
    refine le_iInf₂ fun A hA => ?_
    have hAS : A ≤ T ⊓ Subgroup.normalizer (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) :=
      (le_iSup₂_of_le A hA le_rfl : A ≤ thompsonJ T).trans hJS
    exact (inf_le_inf_left V (Subgroup.centralizer_le hAS)).trans
      (inf_centralizer_le_of_isMaxElemAbelian hV hVT hA)
  exact inf_centralizer_ZS_le_nS hV hS hTM hMN hsyl ⟨hb'.1, Subgroup.centralizer_le hZE hb'.2⟩

theorem omegaOneCenter_inf_eq (hS : OfourStruct (autI hV M) L₁ L₂ tb) (hTM : T ≤ M)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) (hVT : V ≤ T)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (hsyl : IsSylowTwoOf (autI hV T) (autI hV M)) :
    omegaOneCenterOf (thompsonJ T) ⊓ V = V ⊓ Subgroup.centralizer
      ((T ⊓ Subgroup.normalizer (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) :
        Subgroup G) : Set G) := by
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTM.trans hMN
  have hJS := thompsonJ_le_nS hV hS hTM hMN hVT hJ hsyl
  have hJbar := autI_thompsonJ_eq hV hS hTM hMN hVT hJ hsyl
  have hSbar := autI_nS hV hS hTM
  have hJN : thompsonJ T ≤ Subgroup.normalizer (V : Set G) := (hJS.trans inf_le_left).trans hTN
  have hSN : T ⊓ Subgroup.normalizer (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (V : Set G) := inf_le_left.trans hTN
  have hCeq := inf_centralizer_eq_of_autI_eq hV hJN hSN (hJbar.trans hSbar.symm)
  apply le_antisymm
  · rintro x ⟨hxE, hxV⟩
    rw [← hCeq]
    exact ⟨hxV, A4.centerOf_le_centralizer _ (A4.omegaOneCenterOf_le_centerOf _ hxE)⟩
  · intro x hx
    refine ⟨?_, hx.1⟩
    rw [(omegaOne_centralizer_thompsonJ T).2]
    refine (Subgroup.mem_iInf.2 fun A => Subgroup.mem_iInf.2 fun hA => ?_)
    have hAS : A ≤ T ⊓ Subgroup.normalizer (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) :=
      (le_iSup₂_of_le A hA le_rfl : A ≤ thompsonJ T).trans hJS
    exact (inf_le_inf_left V (Subgroup.centralizer_le hAS)).trans
      (inf_centralizer_le_of_isMaxElemAbelian hV hVT hA) hx

end ZS

section ModelE4

variable {W : Type*} [CommGroup W] [Finite W] {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W}

theorem OfourStruct.isElemAbelian_inf_sup (h : OfourStruct X L₁ L₂ t)
    {T' : Subgroup (MulAut W)} (hT : IsSylowTwoOf T' X) : IsElemAbelian 2 (T' ⊓ (L₁ ⊔ L₂)) := by
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF⟩ := h.exists_sylowFacts hT
  have hEq : T' ⊓ (L₁ ⊔ L₂) = Subgroup.closure {s₁, s₂} := by
    apply le_antisymm
    · intro x hx
      rcases (hF.S_eq x).1 hx with h1 | h1 | h1 | h1
      · rw [h1]; exact Subgroup.one_mem _
      · rw [h1]; exact Subgroup.subset_closure (by simp)
      · rw [h1]; exact Subgroup.subset_closure (by simp)
      · rw [h1]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
    · rw [Subgroup.closure_le]
      rintro x (hx | hx)
      · rw [hx]; exact hF.sylow.s₁_mem_S
      · rw [Set.mem_singleton_iff.mp hx]; exact hF.sylow.s₂_mem_S
  rw [hEq]
  refine B2F.isElemAbelian_closure ?_ ?_
  · rintro a (ha | ha) b (hb | hb)
    · rw [ha, hb]
    · rw [ha, Set.mem_singleton_iff.mp hb]; exact hF.comm
    · rw [Set.mem_singleton_iff.mp ha, hb]; exact hF.comm.symm
    · rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb]
  · rintro a (ha | ha)
    · rw [ha, pow_two]; exact hF.s₁_sq
    · rw [Set.mem_singleton_iff.mp ha, pow_two]; exact hF.s₂_sq

end ModelE4

namespace Hyp153

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem lemma_14_1_2_of_le (h : Hyp153 G T Mc M)
    (hJ : thompsonJ T ≤ Subgroup.centralizer (VZ T M : Set G)) :
    VZ T M ≤ omegaOneCenterOf (thompsonJ T) ∧
      baum T = baum (T ⊓ Subgroup.centralizer (VZ T M : Set G)) ∧
      IsUniqueM (M ⊓ Subgroup.normalizer (baum T : Set G)) M ∧ CGS (baum T) ≤ M := by
  obtain ⟨S₀, rfl⟩ := h.qtfe.exists_sylow
  have hJ' : thompsonJ (S₀ : Subgroup G) ≤
      M ⊓ Subgroup.centralizer (VZ (S₀ : Subgroup G) M : Set G) :=
    le_inf ((iSup_le fun _ => iSup_le fun hA => hA.1 : thompsonJ (S₀ : Subgroup G) ≤ S₀).trans
      h.T_le) hJ
  have h1 := lemma_14_1_2_one S₀ h.T_le h.twoReduced.1 hJ'
  have h2 := lemma_14_1_2_two h.qtfe.qtke.2.1 S₀ h.mf.1 h.twoReduced.1 hJ' (Or.inl rfl)
  exact ⟨h1.1, h1.2, h2⟩

end Hyp153


section ModelSyl

variable {W : Type*} [CommGroup W] [Finite W] {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W}

omit [Finite W] in
theorem OfourStruct.mem_sup_of_apply_eq (h : OfourStruct X L₁ L₂ t) {x : MulAut W} (hx : x ∈ X)
    {a : W} (ha : a ∈ commV L₁) (ha1 : a ≠ 1) (hxa : x a = a) : x ∈ L₁ ⊔ L₂ := by
  rcases h.perm x hx with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact (h.mem_sup_iff hx).2 fun u hu => commV_apply_mem x L₁ L₁ h1 hu
  · exfalso
    have h2 : x a ∈ commV L₂ := commV_apply_mem x L₁ L₂ h1 ha
    rw [hxa] at h2
    have : a ∈ commV L₁ ⊓ commV L₂ := ⟨ha, h2⟩
    rw [h.inf, Subgroup.mem_bot] at this
    exact ha1 this

end ModelSyl

section Syl

variable {G : Type} [Group G] [Finite G] {V M T : Subgroup G} (hV : IsElemAbelian 2 V)
  {L₁ L₂ : Subgroup (MulAut (IntMod V hV))} {tb : MulAut (IntMod V hV)}

theorem isSylowTwoOf_nS (hS : OfourStruct (autI hV M) L₁ L₂ tb) (hTM : T ≤ M)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) (hsyl : IsSylowTwoOf (autI hV T) (autI hV M))
    (hT : IsSylowTwoOf T M) {A : Subgroup G}
    (hSA : T ⊓ Subgroup.normalizer (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) ≤ A)
    (hAM : A ≤ M) (hCA : M ⊓ Subgroup.centralizer (V : Set G) ≤ A)
    (hAbar : autI hV A ≤ L₁ ⊔ L₂) :
    IsSylowTwoOf
      (T ⊓ Subgroup.normalizer (((commV L₁).map (inclMod hV) : Subgroup G) : Set G)) A := by
  set V₁ : Subgroup G := (commV L₁).map (inclMod hV) with hV₁
  set S : Subgroup G := T ⊓ Subgroup.normalizer (V₁ : Set G) with hSdef
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hAM.trans hMN
  have hSbar : autI hV S = autI hV T ⊓ (L₁ ⊔ L₂) := autI_nS hV hS hTM
  have hS2 : IsPGroup 2 S := hT.2.1.to_inf_left
  have h1 : IsSylowTwoOf (S ⊓ Subgroup.centralizer (V : Set G))
      (A ⊓ Subgroup.centralizer (V : Set G)) := by
    have e1 : S ⊓ Subgroup.centralizer (V : Set G) =
        T ⊓ (M ⊓ Subgroup.centralizer (V : Set G)) := by
      apply le_antisymm
      · rintro x ⟨⟨hxT, -⟩, hxC⟩
        exact ⟨hxT, hTM hxT, hxC⟩
      · rintro x ⟨hxT, -, hxC⟩
        exact ⟨inf_centralizer_le_nS T V₁ (map_inclMod_le hV _) ⟨hxT, hxC⟩, hxC⟩
    have e2 : A ⊓ Subgroup.centralizer (V : Set G) = M ⊓ Subgroup.centralizer (V : Set G) :=
      le_antisymm (inf_le_inf_right _ hAM) fun x hx => ⟨hCA hx, hx.2⟩
    rw [e1, e2]
    exact A4.isSylowTwoOf_inf_normal hT inf_le_left
      (B2F.le_normalizer_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer hMN))
  have h2 : IsSylowTwoOf (autI hV S) (autI hV A) := by
    rw [hSbar]
    exact A4.isSylowTwoOf_mono (hS.isSylow_sup hsyl) (hSbar ▸ autI_mono hV hSA) hAbar
  exact B2F.isSylowTwoOf_of_isSylowTwoOf_autI hV hAN hSA hS2 h1 h2

theorem autI_inf_centralizer_le (hS : OfourStruct (autI hV M) L₁ L₂ tb) (hTM : T ≤ M)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) (hsyl : IsSylowTwoOf (autI hV T) (autI hV M)) :
    autI hV (M ⊓ Subgroup.centralizer
      (((commV L₁).map (inclMod hV) ⊓ Subgroup.centralizer
        ((T ⊓ Subgroup.normalizer (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) :
          Subgroup G) : Set G) : Subgroup G) : Set G)) ≤ L₁ ⊔ L₂ := by
  set V₁ : Subgroup G := (commV L₁).map (inclMod hV) with hV₁
  set S : Subgroup G := T ⊓ Subgroup.normalizer (V₁ : Set G) with hSdef
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTM.trans hMN
  have hSbar : autI hV S = autI hV T ⊓ (L₁ ⊔ L₂) := autI_nS hV hS hTM
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF⟩ := hS.exists_sylowFacts hsyl
  have ha₁ : ∀ x ∈ autI hV T ⊓ (L₁ ⊔ L₂), x a₁ = a₁ := fun x hx =>
    (hF.sylow.fixS a₁).2 (Or.inr (Or.inl rfl)) x hx
  have ha₁Z : a₁.val ∈ V₁ ⊓ Subgroup.centralizer (S : Set G) := by
    refine ⟨⟨a₁, hF.sylow.a₁_mem, rfl⟩, ?_⟩
    have : a₁ ∈ fixV (autI hV S) := by
      rw [hSbar]
      exact mem_fixV.2 ha₁
    exact (mem_fixV_autI hV (inf_le_left.trans hTN) a₁).1 this
  intro φ hφ
  obtain ⟨g, ⟨hgM, hgC⟩, rfl⟩ := (mem_autI hV).1 hφ
  have hgX : convI hV g ∈ autI hV M := convI_mem_autI hV hgM g.2
  have hg1 : convI hV g a₁ = a₁ := by
    apply IntMod.val_injective
    rw [convI_apply_val]
    have hc : a₁.val * (g : G) = (g : G) * a₁.val := Subgroup.mem_centralizer_iff.mp hgC _ ha₁Z
    calc (g : G) * a₁.val * (g : G)⁻¹ = (a₁.val * (g : G)) * (g : G)⁻¹ := by rw [hc]
      _ = a₁.val := by group
  exact hS.mem_sup_of_apply_eq hgX hF.sylow.a₁_mem hF.sylow.a₁_ne hg1

theorem isSylowTwoOf_nS_normalizer (hS : OfourStruct (autI hV M) L₁ L₂ tb) (hTM : T ≤ M)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) (hsyl : IsSylowTwoOf (autI hV T) (autI hV M))
    (hT : IsSylowTwoOf T M)
    (hNM : Subgroup.normalizer
      ((T ⊓ Subgroup.normalizer (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) :
        Subgroup G) : Set G) ≤ M) :
    IsSylowTwoOf (T ⊓ Subgroup.normalizer (((commV L₁).map (inclMod hV) : Subgroup G) : Set G))
      (Subgroup.normalizer (((commV L₁).map (inclMod hV) : Subgroup G) : Set G)) := by
  set V₁ : Subgroup G := (commV L₁).map (inclMod hV) with hV₁
  have hV₁V : V₁ ≤ V := map_inclMod_le hV _
  have hSyl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (V₁ : Set G))
      (M ⊓ Subgroup.normalizer (V₁ : Set G)) :=
    isSylowTwoOf_nS hV hS hTM hMN hsyl hT
      (le_inf (inf_le_left.trans hTM) inf_le_right) inf_le_left
      (inf_le_inf_left M ((Subgroup.centralizer_le hV₁V).trans
        (Subgroup.centralizer_le_normalizer _)))
      ((autI_nS hV hS le_rfl).le.trans inf_le_right)
  exact isSylowTwoOf_of_normalizer_le inf_le_right hNM
    (by rw [inf_comm (Subgroup.normalizer (V₁ : Set G)) M]; exact hSyl)

theorem isSylowTwoOf_nS_centralizer (hS : OfourStruct (autI hV M) L₁ L₂ tb) (hTM : T ≤ M)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) (hsyl : IsSylowTwoOf (autI hV T) (autI hV M))
    (hT : IsSylowTwoOf T M)
    (hNM : Subgroup.normalizer
      ((T ⊓ Subgroup.normalizer (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) :
        Subgroup G) : Set G) ≤ M) :
    IsSylowTwoOf (T ⊓ Subgroup.normalizer (((commV L₁).map (inclMod hV) : Subgroup G) : Set G))
      (Subgroup.centralizer ((((commV L₁).map (inclMod hV) : Subgroup G) ⊓
        Subgroup.centralizer
          ((T ⊓ Subgroup.normalizer (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) :
            Subgroup G) : Set G) : Subgroup G) : Set G)) := by
  set V₁ : Subgroup G := (commV L₁).map (inclMod hV) with hV₁
  set S : Subgroup G := T ⊓ Subgroup.normalizer (V₁ : Set G) with hSdef
  have hV₁V : V₁ ≤ V := map_inclMod_le hV _
  have hSC : S ≤ Subgroup.centralizer ((V₁ ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) :
      Set G) := fun x hx z hz => (Subgroup.mem_centralizer_iff.mp hz.2 x hx).symm
  have hSyl : IsSylowTwoOf S (M ⊓ Subgroup.centralizer
      ((V₁ ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) : Set G)) :=
    isSylowTwoOf_nS hV hS hTM hMN hsyl hT
      (le_inf (inf_le_left.trans hTM) hSC) inf_le_left
      (inf_le_inf_left M (Subgroup.centralizer_le (inf_le_left.trans hV₁V)))
      (autI_inf_centralizer_le hV hS hTM hMN hsyl)
  exact isSylowTwoOf_of_normalizer_le hSC hNM
    (by rw [inf_comm (Subgroup.centralizer
      ((V₁ ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) : Set G)) M]; exact hSyl)

end Syl


namespace Hyp153

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

omit [Finite G] in
private theorem thompsonJ_le_baum_self (T : Subgroup G) : thompsonJ T ≤ baum T := by
  intro j hj
  refine ⟨(iSup_le fun _ => iSup_le fun hA => hA.1 : thompsonJ T ≤ T) hj,
    Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩
  exact (Subgroup.mem_centralizer_iff.mp
    (A4.centerOf_le_centralizer _ (A4.omegaOneCenterOf_le_centerOf _ he)) j hj).symm

theorem lemma_15_3_5 (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) :
    (thompsonJ T ≤ Subgroup.centralizer (VZ T M : Set G) ∧
        baum T = baum (T ⊓ Subgroup.centralizer (VZ T M : Set G)) ∧
        VZ T M ≤ omegaOneCenterOf (thompsonJ T) ∧ CGS (baum T) ≤ M) ∨
      (autOn (baum T) (VZ T M) = autOn (thompsonJ T) (VZ T M) ∧
        autOn (thompsonJ T) (VZ T M) = autOn (T ⊓ Subgroup.normalizer (V₁ : Set G)) (VZ T M) ∧
        (IsElemAbelian 2 (autOn (T ⊓ Subgroup.normalizer (V₁ : Set G)) (VZ T M)) ∧
          Nat.card (autOn (T ⊓ Subgroup.normalizer (V₁ : Set G)) (VZ T M)) = 4) ∧
        omegaOneCenterOf (thompsonJ T) ⊓ VZ T M = VZ T M ⊓ Subgroup.centralizer
          ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) ∧
        (IsElemAbelian 2 (VZ T M ⊓ Subgroup.centralizer
          ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G)) ∧
          Nat.card ↥(VZ T M ⊓ Subgroup.centralizer
            ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G)) = 4)) := by
  by_cases hJ : thompsonJ T ≤ Subgroup.centralizer (VZ T M : Set G)
  · obtain ⟨h1, h2, -, h4⟩ := h.lemma_14_1_2_of_le hJ
    exact Or.inl ⟨hJ, h2, h1, h4⟩
  · right
    obtain ⟨hV, L₁, L₂, tb, hS, rfl, -, -, -⟩ := D.model
    have hsyl : IsSylowTwoOf (autI hV T) (autI hV M) := h.isSylowTwoOf_autI
    have hJbar := autI_thompsonJ_eq hV hS h.T_le h.le_normalizer h.VZ_le_T hJ hsyl
    have hSbar := autI_nS hV hS h.T_le
    have hBS := baum_le_nS_of_not_le hV hS h.T_le h.le_normalizer h.VZ_le_T hJ hsyl
    have hBbar : autI hV (baum T) = autI hV (thompsonJ T) :=
      le_antisymm ((autI_mono hV hBS).trans (hSbar.trans hJbar.symm).le)
        (autI_mono hV (thompsonJ_le_baum_self T))
    refine ⟨hBbar, hJbar.trans hSbar.symm, ?_, ?_, ?_⟩
    · have hS4 : Nat.card ↥(autI hV T ⊓ (L₁ ⊔ L₂)) = 4 := hS.card_S hsyl
      have hEA := hS.isElemAbelian_inf_sup hsyl
      rw [← hSbar] at hS4 hEA
      exact ⟨hEA, hS4⟩
    · exact omegaOneCenter_inf_eq hV hS h.T_le h.le_normalizer h.VZ_le_T hJ hsyl
    · exact ⟨B2F.isElemAbelian_mono inf_le_left h.elemAbelian, D.card_ZS h⟩


theorem baum_le_nS (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) :
    baum T ≤ T ⊓ Subgroup.normalizer (V₁ : Set G) := by
  by_cases hJ : thompsonJ T ≤ Subgroup.centralizer (VZ T M : Set G)
  · obtain ⟨-, h2, -, -⟩ := h.lemma_14_1_2_of_le hJ
    rw [h2]
    exact (inf_le_left : baum (T ⊓ Subgroup.centralizer (VZ T M : Set G)) ≤ _).trans
      (inf_le_inf_left T ((Subgroup.centralizer_le D.le₁).trans
        (Subgroup.centralizer_le_normalizer _)))
  · obtain ⟨hV, L₁, L₂, tb, hS, rfl, -, -, -⟩ := D.model
    exact baum_le_nS_of_not_le hV hS h.T_le h.le_normalizer h.VZ_le_T hJ h.isSylowTwoOf_autI

theorem lemma_15_3_6 (h11 : StageLemma14111) (h : Hyp153 G T Mc M)
    (D : Decomp153 T M V₁ V₂ t) :
    baum T = baum (T ⊓ Subgroup.normalizer (V₁ : Set G)) ∧
      (Subgroup.normalizer ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) ≤
          Subgroup.normalizer (baum (T ⊓ Subgroup.normalizer (V₁ : Set G)) : Set G) ∧
        Subgroup.normalizer (baum (T ⊓ Subgroup.normalizer (V₁ : Set G)) : Set G) ≤ M) ∧
      IsSylowTwoOf (T ⊓ Subgroup.normalizer (V₁ : Set G))
        (Subgroup.centralizer ((V₁ ⊓ Subgroup.centralizer
          ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) : Subgroup G) :
            Set G)) ∧
      IsSylowTwoOf (T ⊓ Subgroup.normalizer (V₁ : Set G)) (Subgroup.normalizer (V₁ : Set G)) := by
  obtain ⟨C₂, hC, hN⟩ := h.exists_C₂ h11
  have hBS := h.baum_le_nS D
  obtain ⟨h1, h2, h3⟩ := lemma_15_3_3_two h hC hN hBS (inf_le_left : T ⊓ _ ≤ T)
  refine ⟨h1, ⟨h2, h3⟩, ?_⟩
  have hNSM : Subgroup.normalizer ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) ≤
      M := h2.trans h3
  obtain ⟨hV, L₁, L₂, tb, hS, rfl, -, -, -⟩ := D.model
  have hsyl : IsSylowTwoOf (autI hV T) (autI hV M) := h.isSylowTwoOf_autI
  exact ⟨isSylowTwoOf_nS_centralizer hV hS h.T_le h.le_normalizer hsyl h.isSylowTwoOf hNSM,
    isSylowTwoOf_nS_normalizer hV hS h.T_le h.le_normalizer hsyl h.isSylowTwoOf hNSM⟩

end Hyp153


end CFSG.Quasithin
