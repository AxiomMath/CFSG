module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFSub
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFSqtk
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFLayer
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFOne
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFT7Main
public import CFSG.Quasithin.EmptyFaithful.SBd18Main

public section

namespace CFSG.Quasithin.SBd19F

open CFSG CFSG.LocalCores CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem mem_normalizer_map_conj {G : Type} [Group G] {K : Subgroup G} {k g : G}
    (hN : k⁻¹ * g * k ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((K.map (MulAut.conj k).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨(k⁻¹ * g * k) * w * (k⁻¹ * g * k)⁻¹,
      (Subgroup.mem_normalizer_iff.mp hN w).mp hw, ?_⟩
    change k * ((k⁻¹ * g * k) * w * (k⁻¹ * g * k)⁻¹) * k⁻¹ = g * (k * w * k⁻¹) * g⁻¹
    group
  · rintro ⟨w, hw, hwz⟩
    have hinv : (k⁻¹ * g * k)⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hN
    refine ⟨(k⁻¹ * g * k)⁻¹ * w * ((k⁻¹ * g * k)⁻¹)⁻¹, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp hinv w).mp hw
      exact this
    · change k * ((k⁻¹ * g * k)⁻¹ * w * ((k⁻¹ * g * k)⁻¹)⁻¹) * k⁻¹ = z
      have h1 : k * w * k⁻¹ = g * z * g⁻¹ := hwz
      calc k * ((k⁻¹ * g * k)⁻¹ * w * ((k⁻¹ * g * k)⁻¹)⁻¹) * k⁻¹
          = g⁻¹ * (k * w * k⁻¹) * g := by group
        _ = z := by rw [h1]; group

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
  {X : Subgroup G} {τ f : G}

theorem KFHyp.false_of_fusion (hF : A318Facts)
    (h113 : StageLemma14113)
    (hA : Input15338Rank1) (hZ : Input15338CenterRank) (hIdent : Input15338Ident)
    (hCJ : Input15338NonsolvJ) (hCL : Input15338FinalL34)
    (h : KFHyp T Mc M V₁ V₂ Yp I L t X τ f) (hg : ∃ g : G, g⁻¹ * τ * g = f) : False := by
  classical
  have hσ2 := h.sigma_sq
  have hσ1 := h.sigma_ne_one
  obtain ⟨Lτ, Lf, hLτ, hLf, hcases⟩ := h.hcore
  obtain ⟨x, Lx, hxe, hLx, hcard⟩ : ∃ (x : G) (Lx : Subgroup G), (x = τ ∨ x = f) ∧
      SBd14.CoreProps L V₁ I Lx x ∧ Nat.card (↥Lx ⧸ Subgroup.center ↥Lx) = 168 := by
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨τ, Lτ, Or.inl rfl, hLτ, h1⟩
    · exact ⟨f, Lf, Or.inr rfl, hLf, h2⟩
  have hZ1 : Subgroup.center ↥Lx = ⊥ := h.core_center_eq_bot h113 hLx hcard
  obtain ⟨k, hk⟩ := h.exists_conj_sigma hg hxe
  obtain ⟨hxS, hxx, hxI, -⟩ := h.invol_data hxe
  obtain ⟨v, hvV, hv1, hvx⟩ := h.exists_fixed_vector hxI hxx
  have hK3 := h.core_le_layer h113 hxe hLx hcard ⟨k, hk⟩
  have hLxL : ∀ l ∈ Lx, l ∈ L := fun l hl => hLx.1 hl
  have hxc : ∀ l ∈ Lx, x * l = l * x := hLx.2.2.2.1
  have hxn : ∀ g ∈ I, g * x = x * g → g ∈ Subgroup.normalizer (Lx : Set G) := hLx.2.2.2.2
  subst hk
  set σ : G := τ * f with hσ
  set Hs : Subgroup G := Subgroup.centralizer ({σ} : Set G) with hHs
  have hvL : ∀ l ∈ L, l * v = v * l := fun l hl =>
    Subgroup.mem_centralizer_iff.mp (h.r.h1 hvV) l hl
  have hsqtk := h.sqtkGroup_centralizer hσ2 hσ1
  have hlist : ∀ C : Subgroup ↥Hs, IsComponent C → A23List (↥C ⧸ Subgroup.center ↥C) :=
    fun C hC => h.list_centralizer hF hσ2 hσ1 C hC
  obtain ⟨F, B, hFL, hFB, hBI, hBσ, hFel, hF9, hFnormI, -, hB3, b, hbB, hb3, v₀, hv₀V, hbmove⟩ :=
    h.exists_threeOnePlusTwo h113
  have hBH : B ≤ Hs := hBσ
  have hUH : V₁ ≤ Hs := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.hcent w hw).symm
  have hU4 : Nat.card ↥V₁ = 4 := h.r.ctx.hyp.decomp.card₁
  have hUel : CFSG.Assembly.IsElemAbelian 2 V₁ :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 h.r.ctx.hyp.hyp.elemAbelian
      h.r.ctx.hyp.decomp.le₁
  have hsolv : ∀ u ∈ V₁, u ≠ 1 →
      Group.IsSolvable ↥(Subgroup.centralizer ({u} : Set G) ⊓ Hs) := by
    intro u hu hu1
    have hEq : Subgroup.centralizer ({u} : Set G) ⊓ Hs = Subgroup.centralizer ({u, σ} : Set G) := by
      ext g
      simp only [Subgroup.mem_inf, hHs, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
        Set.mem_insert_iff, forall_eq_or_imp, forall_eq]
    rw [hEq]
    exact h.solvable_centralizer_pair h113 hu hu1
  set Lσ : Subgroup G := Lx.map (MulAut.conj k).toMonoidHom with hLσ
  have hLσH : Lσ ≤ Hs := by
    rintro _ ⟨l, hl, rfl⟩
    rw [hHs, Subgroup.mem_centralizer_singleton_iff]
    have h1 := hxc l hl
    calc k * l * k⁻¹ * σ = k * (l * (k⁻¹ * σ * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * σ * k) * l) * k⁻¹ := by rw [← h1]
      _ = σ * (k * l * k⁻¹) := by group
  have eLx : ↥Lx ≃* ↥Lσ :=
    Subgroup.equivMapOfInjective Lx (MulAut.conj k).toMonoidHom (MulAut.conj k).injective
  have hqσ : CFSG.IsQuasisimple ↥Lσ := isQuasisimple_of_mulEquiv eLx hLx.2.1
  have hcardσ : Nat.card (↥Lσ ⧸ Subgroup.center ↥Lσ) = 168 := by
    let eq : (↥Lx ⧸ Subgroup.center ↥Lx) ≃* (↥Lσ ⧸ Subgroup.center ↥Lσ) :=
      QuotientGroup.congr _ _ eLx (Subgroup.map_center_eq eLx)
    rw [← Nat.card_congr eq.toEquiv]
    exact hcard
  have hZσ : Subgroup.center ↥Lσ = ⊥ := by
    have h1 := Subgroup.map_center_eq eLx
    rw [hZ1, Subgroup.map_bot] at h1
    exact h1.symm
  have hLσE : Lσ.subgroupOf Hs ≤ layer ↥Hs := by
    intro y hy
    have hyL : (y : G) ∈ Lσ := hy
    obtain ⟨l, hl, hly⟩ := hyL
    obtain ⟨c, hc, hcl⟩ := hK3 hl
    let e := centralizerConjEquiv σ k
    have hc' : e.symm c ∈ CFSG.ComponentClassification.Layer.subgroup ↥Hs := by
      have := CFSG.ComponentClassification.Layer.equiv_invariant e.symm
      rw [← this]
      exact Subgroup.mem_map_of_mem _ hc
    have hey : e.symm c = y := by
      apply Subtype.ext
      change k * (c : G) * k⁻¹ = (y : G)
      have hcl' : (c : G) = l := hcl
      rw [hcl']
      exact hly
    rw [layer_subgroup_eq_layer] at hc'
    rw [← hey]
    exact hc'
  have hvσH : k * v * k⁻¹ ∈ Hs := by
    rw [hHs, Subgroup.mem_centralizer_singleton_iff]
    calc k * v * k⁻¹ * σ = k * (v * (k⁻¹ * σ * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * σ * k) * v) * k⁻¹ := by rw [hvx]
      _ = σ * (k * v * k⁻¹) := by group
  have hvσ2 : (k * v * k⁻¹) * (k * v * k⁻¹) = 1 := by
    have : v * v = 1 := h.r.V_sq v (h.r.ctx.hyp.decomp.le₁ hvV)
    calc (k * v * k⁻¹) * (k * v * k⁻¹) = k * (v * v) * k⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hvσLx : ∀ l ∈ Lσ, (k * v * k⁻¹) * l = l * (k * v * k⁻¹) := by
    rintro _ ⟨l, hl, rfl⟩
    have h1 := hvL l (hLxL l hl)
    change k * v * k⁻¹ * (k * l * k⁻¹) = k * l * k⁻¹ * (k * v * k⁻¹)
    calc k * v * k⁻¹ * (k * l * k⁻¹) = k * (v * l) * k⁻¹ := by group
      _ = k * (l * v) * k⁻¹ := by rw [h1.symm]
      _ = k * l * k⁻¹ * (k * v * k⁻¹) := by group
  have hnormσ : ∀ g ∈ Hs, g * (k * v * k⁻¹) = (k * v * k⁻¹) * g →
      g ∈ Subgroup.normalizer (Lσ : Set G) := by
    intro g hg hgv
    have hgσ : g * σ = σ * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hg'v : (k⁻¹ * g * k) * v = v * (k⁻¹ * g * k) := by
      calc (k⁻¹ * g * k) * v = k⁻¹ * (g * (k * v * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * v * k⁻¹) * g) * k := by rw [hgv]
        _ = v * (k⁻¹ * g * k) := by group
    have hg'x : (k⁻¹ * g * k) * (k⁻¹ * σ * k) = (k⁻¹ * σ * k) * (k⁻¹ * g * k) := by
      calc (k⁻¹ * g * k) * (k⁻¹ * σ * k) = k⁻¹ * (g * σ) * k := by group
        _ = k⁻¹ * (σ * g) * k := by rw [hgσ]
        _ = (k⁻¹ * σ * k) * (k⁻¹ * g * k) := by group
    have hg'I : k⁻¹ * g * k ∈ I :=
      h.hCv v hvV hv1 (Subgroup.mem_centralizer_singleton_iff.mpr hg'v)
    exact mem_normalizer_map_conj (hxn _ hg'I hg'x)
  exact endgame_false_sub (Hs := Hs) hsqtk hlist hA hZ hIdent hCJ hCL hBH hB3 hLσH hqσ hLσE
    hcardσ hZσ hvσH hvσ2 hvσLx hnormσ hUH hU4 hUel hsolv (y := b) (hBσ hbB)
    (h.hI ▸ hBI hbB) hb3 ⟨v₀, hv₀V, hbmove⟩ (F := F) (hFB.trans hBσ) hFel hF9
    (fun a ha w hw => Subgroup.mem_centralizer_iff.mp (h.r.h1 hw) a (hFL ha))
    (fun u hu hu1 g hg hgu => hFnormI g (by
      exact h.hCv u hu hu1 (Subgroup.mem_centralizer_singleton_iff.mpr hgu))
      (by exact (Subgroup.mem_centralizer_singleton_iff.mp hg).symm))

theorem input15338FusionF_of_residues (h113 : StageLemma14113)
    (hA : Input15338Rank1)
    (hZ : Input15338CenterRank) (hIdent : Input15338Ident) (hCJ : Input15338NonsolvJ)
    (hCL : Input15338FinalL34) : SBd18.Input15338FusionF := by
  intro hF G _ _ T Mc M V₁ V₂ Yp I L t r hI hCv hTI hCIL hidx hIsup X τ f hXY hX3 hXidx hreg hτS
    hfS hτN hfN hττ hff hτf hτ1 hf1 hτf' hcl hinv hcent hmove hσL hcl' ht₀ hNV hNz hcore g hgf
  have hK : KFHyp T Mc M V₁ V₂ Yp I L t X τ f :=
    ⟨r, hI, hCv, hTI, hCIL, hidx, hIsup, hXY, hX3, hXidx, hreg, hτS, hfS, hτN, hfN, hττ, hff, hτf,
      hτ1, hf1, hτf', hcl, hinv, hcent, hmove, hσL, hcl', ht₀, hNV, hNz, hcore⟩
  exact hK.false_of_fusion hF h113 hA hZ hIdent hCJ hCL ⟨g, hgf⟩

end CFSG.Quasithin.SBd19F
