module

public import CFSG.Quasithin.EmptyFaithful.S151cStmt
public import CFSG.Quasithin.EmptyFaithful.S151cSetting
public import CFSG.Quasithin.EmptyFaithful.S151Dual
public import CFSG.Quasithin.Background.B2FactorizationSolvable
public import CFSG.Quasithin.EmptyFaithful.S1414Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem qhatOf_autI_le_two (h1511 : StageLemma1511) (h : quasithinQTFE14Cat G T Mc)
    (hM : IsMf T Mc M) (hVe : IsElemAbelian 2 (VZ T M)) : qhatOf (autI hVe M) ≤ 2 := by
  have := (h1511 G T Mc M h hM).2.1
  simp only [qhatOn, hVe, ↓reduceDIte] at this
  exact this

theorem isSolvable_autI_VZ (h1416 : StageLemma1416) (h : quasithinQTFE14Cat G T Mc)
    (hM : IsMf T Mc M) (hVe : IsElemAbelian 2 (VZ T M)) : Group.IsSolvable ↥(autI hVe M) := by
  have hred : IsTwoReducedIn M (VZ T M) := (isTwoReducedIn_VZ h hM.1.1).1
  exact isSolvable_autOn_of_perfectCore_le hred.2.1 ((h1416 G T Mc h).1 M _ hM.1.1 hred)

theorem pCoreOf_autI_VZ (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (hVe : IsElemAbelian 2 (VZ T M)) : pCoreOf 2 (autI hVe M) = ⊥ := by
  have hred : IsTwoReducedIn M (VZ T M) := (isTwoReducedIn_VZ h hM.1.1).1
  have h1 := autOn_pCore_trivial hred
  have hQX : pCoreOf 2 (autOn M (VZ T M)) ≤ autOn M (VZ T M) := pCoreOf_le 2 _
  exact h1 _ hQX ((Subgroup.normal_subgroupOf_iff_le_normalizer hQX).mpr (le_normalizer_pCoreOf 2 _))
    (pCoreOf_isPGroup 2 _)


theorem isQuotientOfSQTK_autI (h : quasithinIsQTKECat G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    [IsSimpleGroup G] {M : Subgroup G} (hMl : quasithinIsMaxTwoLocal M) {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMN : M ≤ Subgroup.normalizer (V : Set G)) :
    IsQuotientOfSQTKTC ↥(autI hV M) := by
  have hcore := QuasithinUnique.qtkeCore_of_cat hnonab h
  have hsqtk := hcore.1 M (pCoreOf_ne_bot_of_isTwoLocal hMl.1)
  refine ⟨↥M, inferInstance, inferInstance, ?_, hsqtk.2, ?_⟩
  · exact (CFSG.SectionRank.isStronglyQuasithin_iff.mp hsqtk.1)
  · let φ0 : ↥M →* MulAut (IntMod V hV) := (convI hV).comp (Subgroup.inclusion hMN)
    refine ⟨φ0.codRestrict (autI hV M) (fun m => convI_mem_autI hV m.2 (hMN m.2)), ?_⟩
    rintro ⟨φ, hφ⟩
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
    exact ⟨⟨g, hg⟩, rfl⟩


theorem isSylowTwoOf_T_M151c (h : quasithinQTFE14Cat G T Mc) (hM : InM T M) :
    IsSylowTwoOf T M :=
  ⟨hM.2, h.sylow.1, fun hd => h.sylow.2 (dvd_trans hd (by
    simpa [Subgroup.relIndex] using Subgroup.relIndex_dvd_index_of_le hM.2))⟩

theorem autI_mem_sylow2Of (h : quasithinQTFE14Cat G T Mc) (hM : InM T M) {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMN : M ≤ Subgroup.normalizer (V : Set G)) :
    autI hV T ∈ sylow2Of (autI hV M) :=
  B2F.isSylowTwoOf_autI hV hMN (isSylowTwoOf_T_M151c h hM)

theorem gen_autI_VZ (h : quasithinQTFE14Cat G T Mc) (hM : InM T M)
    (hVe : IsElemAbelian 2 (VZ T M)) :
    ∀ W : Subgroup (IntMod (VZ T M) hVe),
      (∀ g ∈ autI hVe M, ∀ z ∈ fixV (autI hVe T), g z ∈ W) → W = ⊤ := by
  intro W hW
  have hMN : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_VZ T M
  have hVT : VZ T M ≤ T := (isTwoReducedIn_VZ h hM).2
  have hTN : T ≤ Subgroup.normalizer (VZ T M : Set G) := hM.2.trans hMN
  let ι : IntMod (VZ T M) hVe →* G := ⟨⟨IntMod.val, rfl⟩, IntMod.val_mul⟩
  have h1 : VZ T M ≤ W.map ι := by
    refine conjClosure_le fun m hm z hz => ?_
    have hzV : z ∈ VZ T M := le_conjClosure _ _ hz
    set z' : IntMod (VZ T M) hVe := IntMod.mk hVe ⟨z, hzV⟩ with hz'def
    have hz' : z' ∈ fixV (autI hVe T) := by
      rw [mem_fixV_autI hVe hTN]
      exact (quasithinOmegaOneCenter_le_center T hz).2
    have := hW (convI hVe ⟨m, hMN hm⟩) (convI_mem_autI hVe hm (hMN hm)) z' hz'
    refine ⟨_, this, ?_⟩
    show (convI hVe ⟨m, hMN hm⟩ z').val = m * z * m⁻¹
    rw [convI_apply_val]
    rfl
  rw [eq_top_iff]
  intro w _
  obtain ⟨w', hw', hw'e⟩ := h1 w.val_mem
  have : w' = w := IntMod.val_injective hw'e
  rwa [this] at hw'

omit [Finite G] in
@[expose] def valHom151c (V : Subgroup G) (hV : IsElemAbelian 2 V) : IntMod V hV →* G :=
  ⟨⟨IntMod.val, rfl⟩, IntMod.val_mul⟩

omit [Finite G] in
theorem valHom151c_apply {V : Subgroup G} {hV : IsElemAbelian 2 V} (v : IntMod V hV) :
    valHom151c V hV v = v.val := rfl

omit [Finite G] in
theorem valHom151c_injective (V : Subgroup G) (hV : IsElemAbelian 2 V) :
    Function.Injective (valHom151c V hV) := IntMod.val_injective

theorem centralizer_VZ_le_mc (h : quasithinQTFE14Cat G T Mc) :
    Subgroup.centralizer (VZ T M : Set G) ≤ Mc :=
  (Subgroup.centralizer_le (fun _ hz => le_conjClosure _ _ hz)).trans h.centralizer_le_mc

theorem not_le_mc151c (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M) : ¬ M ≤ Mc :=
  fun hle => hM.2.1 (hM.1.1.1.2 Mc h.mc_max.1 hle).symm

theorem xc_ne_autI (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (hVe : IsElemAbelian 2 (VZ T M)) : ¬ autI hVe M ≤ autI hVe (M ⊓ Mc) := by
  intro hle
  apply not_le_mc151c h hM
  intro m hm
  have hMN : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_VZ T M
  obtain ⟨g, hgK, hg⟩ := (mem_autI hVe).1 (hle (convI_mem_autI hVe hm (hMN hm)))
  have hgmc : (g : G) ∈ Mc := hgK.2
  have h1 : convI hVe ((⟨m, hMN hm⟩ : Subgroup.normalizer (VZ T M : Set G)) * g⁻¹) = 1 := by
    rw [map_mul, map_inv, hg, mul_inv_cancel]
  have h2 := (convI_eq_one_iff hVe _).1 h1
  have h3 : m * (g : G)⁻¹ ∈ Mc := centralizer_VZ_le_mc h h2
  have h4 : m = (m * (g : G)⁻¹) * g := by group
  rw [h4]
  exact Mc.mul_mem h3 hgmc


theorem mem_omegaOneCenter_of_fixV (h : quasithinQTFE14Cat G T Mc) (hM : InM T M)
    (hVe : IsElemAbelian 2 (VZ T M)) {z : IntMod (VZ T M) hVe}
    (hz : z ∈ fixV (autI hVe T)) : z.val ∈ quasithinOmegaOneCenter T := by
  have hMN : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_VZ T M
  have hVT : VZ T M ≤ T := (isTwoReducedIn_VZ h hM).2
  have hTN : T ≤ Subgroup.normalizer (VZ T M : Set G) := hM.2.trans hMN
  have hc : z.val ∈ Subgroup.centralizer (T : Set G) := (mem_fixV_autI hVe hTN z).1 hz
  have hzT : z.val ∈ T := hVT z.val_mem
  apply Subgroup.subset_closure
  refine ⟨⟨hzT, hc⟩, ?_⟩
  have := IntMod.sq_eq_one z
  have := congrArg IntMod.val this
  simpa [pow_two] using this

theorem hU_autI (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (hVe : IsElemAbelian 2 (VZ T M)) :
    ∀ Z₁ : Subgroup (IntMod (VZ T M) hVe), Z₁ ≤ fixV (autI hVe T) → Z₁ ≠ ⊥ →
      autI hVe M ⊓ centSub Z₁ ≤ autI hVe (M ⊓ Mc) := by
  intro Z₁ hZ₁ hne φ hφ
  have hMN : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_VZ T M
  obtain ⟨z', hz'ne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  obtain ⟨m, hmM, rfl⟩ := (mem_autI hVe).1 hφ.1
  have hzZ : (z' : IntMod (VZ T M) hVe).val ∈ quasithinOmegaOneCenter T :=
    mem_omegaOneCenter_of_fixV h hM.1.1 hVe (hZ₁ z'.2)
  have hz1 : (z' : IntMod (VZ T M) hVe).val ≠ 1 := fun e => hz'ne (Subtype.ext (IntMod.val_injective e))
  have hfix : convI hVe m (z' : IntMod (VZ T M) hVe) = z' := hφ.2 z' z'.2
  have hcomm : (m : G) ∈ Subgroup.centralizer ({(z' : IntMod (VZ T M) hVe).val} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have := congrArg IntMod.val hfix
    rw [convI_apply_val] at this
    have h2 : ((m : G) * (z' : IntMod (VZ T M) hVe).val * (m : G)⁻¹) * m =
        (z' : IntMod (VZ T M) hVe).val * m := by rw [this]
    calc (z' : IntMod (VZ T M) hVe).val * m
        = ((m : G) * (z' : IntMod (VZ T M) hVe).val * (m : G)⁻¹) * m := h2.symm
      _ = m * (z' : IntMod (VZ T M) hVe).val := by group
  have hmc : (m : G) ∈ Mc := centralizer_singleton_le_mc_of_mem_omegaOneCenter h hzZ hz1 hcomm
  exact convI_mem_autI hVe (K := M ⊓ Mc) ⟨hmM, hmc⟩ m.2


theorem star_autI (h1414 : StageLemma1414) (h1417 : StageLemma1417)
    (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M) (hCE : IsCE1513 T M)
    (hVe : IsElemAbelian 2 (VZ T M)) :
    ∀ W : Subgroup (IntMod (VZ T M) hVe), W ≠ ⊥ → (∀ g ∈ autI hVe M, ∀ w ∈ W, g w ∈ W) →
      W ≤ Subgroup.closure {x | ∃ g ∈ autI hVe (M ⊓ Mc),
        ∃ z ∈ fixV (autI hVe T) ⊓ W, g z = x} → False := by
  intro W hWne hWinv hWgen
  have hMN : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_VZ T M
  have hred := (isTwoReducedIn_VZ h hM.1.1).1
  have hJ : thompsonJ T ≤ M ⊓ Subgroup.centralizer (VZ T M : Set G) := by
    by_contra hJ
    rcases h1417 G T Mc h M (VZ T M) hM.1.1 hred hJ (Or.inl hM.2.1) with h1 | h1
    · exact hCE.1 h1.1
    · exact hCE.2 h1.1
  have hgreat : IsGreatestOrd T M := by
    have := h.simple
    exact h1414 G T h.simple h.nonabelian h.qtke h.sylow h.faithful_empty M hM.1 hJ
  have hle : OrdLE T Mc M := hgreat.2 Mc ⟨h.mc_max, h.t_le_mc⟩
  have hV'ne : W.map (valHom151c (VZ T M) hVe) ≠ ⊥ := by
    intro hb
    exact hWne ((Subgroup.map_eq_bot_iff_of_injective _ (valHom151c_injective _ hVe)).1 hb)
  have hV'2 : IsPGroup 2 (W.map (valHom151c (VZ T M) hVe)) := by
    rintro ⟨x, w, hw, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    have := IntMod.sq_eq_one w
    have := congrArg IntMod.val this
    simpa [pow_two, valHom151c_apply] using this
  have hinv : ∀ m ∈ M, ∀ x ∈ W.map (valHom151c (VZ T M) hVe),
      m * x * m⁻¹ ∈ W.map (valHom151c (VZ T M) hVe) := by
    rintro m hm x ⟨w, hw, rfl⟩
    have := hWinv (convI hVe ⟨m, hMN hm⟩) (convI_mem_autI hVe hm (hMN hm)) w hw
    refine ⟨_, this, ?_⟩
    show (convI hVe ⟨m, hMN hm⟩ w).val = m * w.val * m⁻¹
    rw [convI_apply_val]
  have hVM : M ≤ Subgroup.normalizer ((W.map (valHom151c (VZ T M) hVe) : Subgroup G) : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hinv m hm x, fun hx => ?_⟩
    have := hinv m⁻¹ (M.inv_mem hm) _ hx
    simpa [mul_assoc] using this
  have hgen : W.map (valHom151c (VZ T M) hVe) =
      conjClosure (W.map (valHom151c (VZ T M) hVe) ⊓ quasithinOmegaOneCenter T) (Mc ⊓ M) := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      refine hWgen.trans ((Subgroup.closure_le _).2 ?_)
      rintro x ⟨g, hg, z, hz, rfl⟩
      obtain ⟨m, hmK, rfl⟩ := (mem_autI hVe).1 hg
      have hzV' : z.val ∈ W.map (valHom151c (VZ T M) hVe) := ⟨z, hz.2, rfl⟩
      have hzZ : z.val ∈ quasithinOmegaOneCenter T := mem_omegaOneCenter_of_fixV h hM.1.1 hVe hz.1
      have := mem_conjClosure (Z := W.map (valHom151c (VZ T M) hVe) ⊓ quasithinOmegaOneCenter T)
        (H := Mc ⊓ M) ⟨hmK.2, hmK.1⟩ ⟨hzV', hzZ⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, valHom151c_apply, convI_apply_val]
      exact this
    · refine conjClosure_le fun m hm z hz => ?_
      exact hinv m hm.2 z hz.1
  have hMcM : Mc ≤ M := le_of_ordLE_of_normal hM.1.1.1 hle hV'ne hV'2 hVM hgen
  exact hM.2.1 (h.mc_max.2 M hM.1.1.1.1 hMcM)


theorem JhatOn_eq_Jhat_autI (M : Subgroup G) {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    JhatOn M V = Jhat (autI hV M) := by
  simp only [JhatOn, hV, ↓reduceDIte]
  rfl

theorem central_autI (hC : CentralOnComplement1512) (h : quasithinQTFE14Cat G T Mc)
    (hM : IsMf T Mc M) (hVe : IsElemAbelian 2 (VZ T M)) :
    ∀ c ∈ fixV (fittingOf (Jhat (autI hVe M))), ∀ j ∈ Jhat (autI hVe M), j c = c := by
  intro c hc j hj
  have hMN : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_VZ T M
  have hcomm := hC G T Mc M h hM
  rw [JhatOn_eq_Jhat_autI M hVe] at hcomm
  set J := Jhat (autI hVe M) with hJ
  have hJX : J ≤ autOn M (VZ T M) := Jhat_le _
  have hFJ : fittingOf J ≤ autOn M (VZ T M) := (fittingOf_le J).trans hJX
  have hA : preOn M (VZ T M) (fittingIn J) ≤ Subgroup.normalizer (VZ T M : Set G) :=
    (preOn_le _ _ _).trans hMN
  have hAut : autI hVe (preOn M (VZ T M) (fittingIn J)) = fittingOf J := autOn_preOn hFJ
  have hc' : c ∈ fixV (autI hVe (preOn M (VZ T M) (fittingIn J))) := by rw [hAut]; exact hc
  have hcA := (mem_fixV_autI hVe hA c).1 hc'
  have hcV : c.val ∈ VZ T M ⊓ Subgroup.centralizer
      (preOn M (VZ T M) (fittingIn J) : Set G) := ⟨c.val_mem, hcA⟩
  have hcJ : c.val ∈ Subgroup.centralizer (mJ154 T M : Set G) := by
    have := (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm
    exact this hcV
  have hjJ : j ∈ autI hVe (mJ154 T M) := by
    have : autI hVe (preOn M (VZ T M) J) = J := autOn_preOn hJX
    unfold mJ154
    rw [JhatOn_eq_Jhat_autI M hVe, this]
    exact hj
  obtain ⟨m, hm, rfl⟩ := (mem_autI hVe).1 hjJ
  refine IntMod.val_injective ?_
  rw [convI_apply_val]
  have := Subgroup.mem_centralizer_iff.mp hcJ m hm
  calc (m : G) * c.val * (m : G)⁻¹ = (c.val * m) * (m : G)⁻¹ := by rw [this]
    _ = c.val := by group


theorem setting151c_of (h1511 : StageLemma1511) (h1414 : StageLemma1414)
    (h1416 : StageLemma1416) (h1417 : StageLemma1417) (hC : CentralOnComplement1512)
    (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M) (hCE : IsCE1513 T M)
    (hVe : IsElemAbelian 2 (VZ T M)) :
    Setting151c (autI hVe M) (autI hVe T) (autI hVe (M ⊓ Mc)) := by
  have hMN : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_VZ T M
  have := h.simple
  exact
    { sq := IntMod.sq_eq_one
      solv := isSolvable_autI_VZ h1416 h hM hVe
      o2 := pCoreOf_autI_VZ h hM hVe
      sqtk := isQuotientOfSQTK_autI h.qtke h.nonabelian hM.1.1.1 hVe hMN
      qhat := qhatOf_autI_le_two h1511 h hM hVe
      syl := autI_mem_sylow2Of h hM.1.1 hVe hMN
      gen := gen_autI_VZ h hM.1.1 hVe
      xc_le := autI_mono hVe inf_le_left
      tb_le := autI_mono hVe (le_inf hM.1.1.2 h.t_le_mc)
      xc_ne := xc_ne_autI h hM hVe
      hU := hU_autI h hM hVe
      star := star_autI h1414 h1417 h hM hCE hVe
      central := central_autI hC h hM hVe }

end CFSG.Quasithin
