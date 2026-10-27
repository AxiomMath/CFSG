module

public import CFSG.Quasithin.EmptyFaithful.A38c8Defs
public import CFSG.Quasithin.EmptyFaithful.A38c8Outer
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecA11Bar
public import CFSG.Quasithin.Vol2.Ch11SecSPGL2

public section

namespace CFSG.Quasithin.A38c8

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

private theorem le_normalizer_of_conj_mem' {A : Type*} [Group A] {X L : Subgroup A}
    (h : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L) : X ≤ Subgroup.normalizer (L : Set A) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro l
  refine ⟨h x hx l, fun hl => ?_⟩
  have := h x⁻¹ (X.inv_mem hx) _ hl
  have e : x⁻¹ * (x * l * x⁻¹) * x⁻¹⁻¹ = l := by group
  rwa [e] at this

@[expose] def L4Rows : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (N T B : Subgroup Y), N.Normal → IsSylowTwoOf T ⊤ → B ≤ N →
    B ∈ lFamily T → T ≤ Subgroup.normalizer (B : Set Y) → IsPSL 4 2 1 (ModO2 B) →
      (A312Case B N ∨ A312Nonquasi B N) → ∀ t ∈ T, InnerOnModO2 B t

theorem input32ThreeComp_of_rows (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hpre : Input32Preamble) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h312 : A312ForSQTK) (hrows : L4Rows) : Input32ThreeComp := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c h1 h2
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t :=
    c.toCtx15331.toCtx15330.toCtx15328.toCtx15327.toCtx15325L
  have hyp : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have hh : Hyp153 G T Mc M := hyp.hyp
  have Dc : Decomp153 T M V₁ V₂ t := hyp.decomp
  obtain ⟨hLcJ, hLnM, -, -, hStarQ, hLQ⟩ := c25.conc
  have hLc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ hLcJ
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hIeq : I = L ⊔ Sgp153 T V₁ := c.I_eq
  have hSI : Sgp153 T V₁ ≤ I := hIeq ▸ le_sup_right
  have hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := hSI.trans hIL
  have hpre' := hpre G T Mc M V₁ V₂ Yp I L t c
  have hLI₁ : L ≤ Subgroup.centralizer ((ZS153 T M V₁ ⊓ V₁ : Subgroup G) : Set G) := by
    intro l hl
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    have hzL : z ∈ ZS153 T M V₁ ⊓ Subgroup.centralizer (L : Set G) := h2.1 ▸ hz
    exact (Subgroup.mem_centralizer_iff.mp hzL.2 l hl).symm
  have hSI₁ : Sgp153 T V₁ ≤ Subgroup.centralizer ((ZS153 T M V₁ ⊓ V₁ : Subgroup G) : Set G) := by
    intro s hs
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    have hzC : z ∈ Subgroup.centralizer (Sgp153 T V₁ : Set G) := hz.1.2
    exact (Subgroup.mem_centralizer_iff.mp hzC s hs).symm
  have hZ₁V : ZS153 T M V₁ ⊓ V₁ ≤ VZ T M := inf_le_right.trans Dc.le₁
  have hZ₁I₁ : (ZS153 T M V₁ ⊓ V₁ : Subgroup G) ≤
      Subgroup.centralizer ((ZS153 T M V₁ ⊓ V₁ : Subgroup G) : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      B2F.isElemAbelian_comm hh.elemAbelian (hZ₁V hy) (hZ₁V hx)
  have hZ₁2 : IsPGroup 2 ↥(ZS153 T M V₁ ⊓ V₁) :=
    (B2F.isPGroup_of_isElemAbelian hh.elemAbelian).to_le hZ₁V
  have hZ₁N : Subgroup.centralizer ((ZS153 T M V₁ ⊓ V₁ : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((ZS153 T M V₁ ⊓ V₁ : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hZ₁pc : ZS153 T M V₁ ⊓ V₁ ≤
      pCoreOf 2 (Subgroup.centralizer ((ZS153 T M V₁ ⊓ V₁ : Subgroup G) : Set G)) :=
    le_pCoreOf_of_le_normalizer 2 hZ₁I₁ hZ₁N hZ₁2
  have hZ₁ne : ZS153 T M V₁ ⊓ V₁ ≠ ⊥ := by
    intro hb
    have := h2.2
    rw [hb, Subgroup.card_bot] at this
    omega
  have hO2 : pCoreOf 2 (Subgroup.centralizer ((ZS153 T M V₁ ⊓ V₁ : Subgroup G) : Set G)) ≠ ⊥ :=
    fun hb => hZ₁ne (le_bot_iff.mp (hb ▸ hZ₁pc))
  set I₁ : Subgroup G := Subgroup.centralizer ((ZS153 T M V₁ ⊓ V₁ : Subgroup G) : Set G) with hI₁
  have hYS : Yp ⊔ Sgp153 T V₁ ≤ I₁ := sup_le (c.c27.Yp_le.trans hLI₁) hSI₁
  have hnotM : ¬ I₁ ≤ M := fun hle => hLnM (le_inf (hLI₁.trans hle) hLI)
  have hS₁ : IsSylowTwoOf (Sgp153 T V₁) I₁ :=
    hyp.lemma_15_3_11_one h11 h113 ⟨⟨hYS, hO2⟩, hnotM⟩
  have hB : L ∈ lFamily (Sgp153 T V₁) := by
    show L ∈ cComp (L ⊔ Sgp153 T V₁)
    rw [← hIeq]
    exact hLc
  have hK := hh.qtfe.qtke
  have hs := hh.qtfe.simple
  have hnab := hh.qtfe.nonabelian
  obtain ⟨L₁, ⟨hL₁, hLL₁⟩, -⟩ := lemma_1_2_4_existsUnique hK hs hnab h37 h39 hO2 hS₁ hLI₁ hB
  have hnorm := lemma_1_2_4_normal hK hs hnab h37 h38 hO2 hS₁ hB hLL₁ hL₁ hSL
  have hL₁I₁ := le_of_mem_cComp hL₁
  rcases lemma_1_2_4_list hK hs hnab h312 hO2 hS₁ hLI₁ hB hL₁ hLL₁ with heq | hlist
  ·
    have hLeq :=
      Vol2.Ch11.SecA.eq_of_modO2Image_eq hS₁ hL₁I₁ hLL₁ (perfect_of_mem_cComp hL₁) hSL heq
    exact hLeq ▸ hL₁
  ·
    exfalso
    obtain ⟨s, hsS, hsout⟩ := exists_outer_action c hpre'
    set π := QuotientGroup.mk' (CFSG.pCore 2 ↥I₁) with hπ
    have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
    have hsI₁ : s ∈ I₁ := hSI₁ hsS
    have hNn : (modO2Image I₁ L₁).Normal := Subgroup.Normal.map hnorm π hπs
    have hTbar : IsSylowTwoOf (((Sgp153 T V₁).subgroupOf I₁).map π) ⊤ :=
      isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hS₁) π hπs
    have hBN : modO2Image I₁ L ≤ modO2Image I₁ L₁ :=
      Subgroup.map_mono (fun x hx => hLL₁ hx)
    have hBl : modO2Image I₁ L ∈ lFamily (((Sgp153 T V₁).subgroupOf I₁).map π) :=
      modO2Image_mem_lFamily hS₁ hLI₁ hB
    have hTB : ((Sgp153 T V₁).subgroupOf I₁).map π ≤
        Subgroup.normalizer (modO2Image I₁ L : Set (↥I₁ ⧸ CFSG.pCore 2 ↥I₁)) := by
      refine le_normalizer_of_conj_mem' fun ss hss bb hbb => ?_
      obtain ⟨s', hs', rfl⟩ := hss
      obtain ⟨l', hl', rfl⟩ := hbb
      have hs'' : (s' : G) ∈ Sgp153 T V₁ := hs'
      have hl'' : (l' : G) ∈ L := hl'
      refine ⟨s' * l' * s'⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      show ((s' * l' * s'⁻¹ : ↥I₁) : G) ∈ L
      have := (Subgroup.mem_normalizer_iff.1 (hSL hs'') (l' : G)).1 hl''
      simpa using this
    have h4 : IsPSL 4 2 1 (ModO2 (modO2Image I₁ L)) := by
      obtain ⟨e⟩ := c.c31
      obtain ⟨eA⟩ := SBc5.starL_equiv_alt8 hLI hIL hStarQ e
      have hPSL : IsPSL 4 2 1 ↥(Star153 T I L) :=
        SBc5.isPSL_two_of_statedSL (by norm_num) (eA.trans SBc5.alt8EquivStatedSL)
      have hker : pCoreOf 2 L ≤ Subgroup.centralizer (UI153 T I : Set G) := fun y hy =>
        (hpre'.1 ▸ hy : y ∈ L ⊓ Subgroup.centralizer (UI153 T I : Set G)).2
      have hLN : L ≤ Subgroup.normalizer (UI153 T I : Set G) :=
        hLI.trans (le_normalizer_conjClosure _ _)
      have hinj : Function.Injective (S153D.autOnQuot hLN hker) := by
        rw [injective_iff_map_eq_one]
        intro q hq
        obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
        rw [S153D.autOnQuot_mk, S153D.autOnHom_eq_one_iff] at hq
        have hmem : (l : G) ∈ pCoreOf 2 L := hpre'.1 ▸ ⟨l.2, hq⟩
        exact (QuotientGroup.eq_one_iff l).2 ((S153D.mem_pCore_iff l).2 hmem)
      let eM : ModO2 L ≃* ↥(Star153 T I L) :=
        MulEquiv.ofBijective (S153D.autOnQuot hLN hker) ⟨hinj, S153D.autOnQuot_surjective hLN hker⟩
      obtain ⟨e₂⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv hLI₁
      exact IsPSL.of_mulEquiv (eM.symm.trans e₂) hPSL
    have hinner := hrows _ _ _ _ hNn hTbar hBN hBl hTB h4 hlist (π ⟨s, hsI₁⟩)
      ⟨⟨s, hsI₁⟩, Subgroup.mem_subgroupOf.2 hsS, rfl⟩
    obtain ⟨bb, hbb, hall⟩ := hinner
    obtain ⟨l', hl', hl'b⟩ := hbb
    have hl'' : (l' : G) ∈ L := hl'
    refine hsout ⟨(l' : G), hl'', fun x hx => ?_⟩
    have hxI₁ : x ∈ I₁ := hLI₁ hx
    have hw : (s * x * s⁻¹)⁻¹ * ((l' : G) * x * (l' : G)⁻¹) ∈ L := by
      have h1 : s * x * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hSL hsS) x).1 hx
      have h2 : (l' : G) * x * (l' : G)⁻¹ ∈ L := L.mul_mem (L.mul_mem hl'' hx) (L.inv_mem hl'')
      exact L.mul_mem (L.inv_mem h1) h2
    have hmk := hall (π ⟨x, hxI₁⟩) ⟨⟨x, hxI₁⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    refine Vol2.Ch11.SecS.mem_pCoreOf_of_mk_mem hLI₁ hw ?_
    have : π ⟨(s * x * s⁻¹)⁻¹ * ((l' : G) * x * (l' : G)⁻¹), hLI₁ hw⟩ =
        (π ⟨s, hsI₁⟩ * π ⟨x, hxI₁⟩ * (π ⟨s, hsI₁⟩)⁻¹)⁻¹ * (bb * π ⟨x, hxI₁⟩ * bb⁻¹) := by
      rw [← hl'b]
      simp only [← map_inv, ← map_mul]
      rfl
    rw [this]
    exact hmk

end CFSG.Quasithin.A38c8
