module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Om4Psi
public import CFSG.RankThree.GF2n.Stroth80.Sec7NuData
public import CFSG.RankThree.GF2n.Stroth80.Sec7SemilinearProportional
public import CFSG.RankThree.GF2n.Stroth80.Sec7InducedForm
public import CFSG.RankThree.GF2n.Stroth80.Sec7Om4Ovoid
public import CFSG.RankThree.GF2n.Stroth80.Sec7OvoidTwoField
public import CFSG.RankThree.GF2n.Stroth80.Sec7Om4PerpFamily
public import CFSG.RankThree.GF2n.Stroth80.Sec7FormScalarTransport
public import CFSG.RankThree.GF2n.Stroth80.Sec7Om4Model

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

theorem sec7_model_form {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ) :
    M₀.B.Nondegenerate ∧ M₀.B.IsRefl := by
  have halt : M₀.B.IsAlt := M₀.alt
  refine ⟨⟨fun e he => M₀.nondeg e he, fun e he => M₀.nondeg e fun f => ?_⟩, halt.isRefl⟩
  rw [Tim79.QuadModel.B_comm, he f, neg_zero]

theorem sec7_finrank_eq_of_semiEquiv {K K' U W : Type*} [Field K] [Field K']
    [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K' W] (θ : K ≃+* K') (Ψ : U ≃+ W)
    (hΨ : ∀ (a : K) (u : U), Ψ (a • u) = θ a • Ψ u) :
    Module.finrank K U = Module.finrank K' W := by
  have h := sec7_two_finrank_map_semi θ (sec7_two_semi θ Ψ hΨ) Ψ.injective ⊤
  rw [Submodule.map_top, LinearMap.range_eq_top.mpr Ψ.surjective, finrank_top, finrank_top] at h
  exact h.symm

theorem sec7_exists_coord_equiv {K E W : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup W] (U : Submodule K E) (Ψ : U ≃+ W) (ν : E ≃+ E)
    (hνU : ∀ e, e ∈ U ↔ ν e ∈ U) :
    ∃ T : W ≃ W, ∀ y, ((Ψ.symm (T y) : U) : E) = ν ((Ψ.symm y : U) : E) := by
  let f : U → U := fun x => ⟨ν (x : E), (hνU (x : E)).mp x.2⟩
  let g : U → U := fun x => ⟨ν.symm (x : E),
    (hνU (ν.symm (x : E))).mpr (by rw [ν.apply_symm_apply]; exact x.2)⟩
  have hfg : ∀ x, f (g x) = x := fun x => Subtype.ext (ν.apply_symm_apply (x : E))
  have hgf : ∀ x, g (f x) = x := fun x => Subtype.ext (ν.symm_apply_apply (x : E))
  refine ⟨Ψ.symm.toEquiv.trans ((Equiv.mk f g hgf hfg).trans Ψ.toEquiv), fun y => ?_⟩
  show ((Ψ.symm (Ψ (f (Ψ.symm y))) : U) : E) = _
  rw [Ψ.symm_apply_apply]

section Main


theorem stroth73aOm4PsiCore_of (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement) :
    Stroth73aOm4PsiCoreStatement := by
  intro G _ _ M Q Z B _ hc n t hs hno hom Z0 hZ0 ht K _ _ γ M₀ ρ b hS ψ hψ hrange hW hinj hA5 hA6
    m hm hmV
  classical
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have htM : t ∈ M := hc.LB_le_M ht
  obtain ⟨hf, hr⟩ := sec7_model_form M₀
  have hr1 : LinearMap.range ψ = hc.VtSub hS.model t := Submodule.ext fun e => hrange e
  have hk1 : LinearMap.ker ψ = M₀.B.orthogonal (hc.VtSub hS.model t) := by
    ext e
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    rw [LinearMap.mem_ker, ← hW x hxQ]
    have hZW : Z ≤ Wt Q (Vt M (LB M Q B) B Z t) := fun z hz =>
      ⟨hc.Z_le_Q hz, Subgroup.mem_centralizer_iff.mpr fun v hv => by
        have := hc.conj_Z_of_mem_Q (hVQ hv) hz
        calc v * z = (v * z * v⁻¹) * v := by group
          _ = z * v := by rw [this]⟩
    rw [← Tim79.QuadModel.mem_img_iff M₀ hZW hxQ, mem_img_Wt_iff M₀ hS.model.reg hVQ,
      LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h u hu
      exact (LinearMap.BilinForm.isOrtho_def).mpr
        (by rw [Tim79.QuadModel.B_comm, h u hu, neg_zero])
    · intro h v hv
      have := LinearMap.BilinForm.isOrtho_def.mp (h v hv)
      rw [Tim79.QuadModel.B_comm, this, neg_zero]
  obtain ⟨K', fK', finK', hchar, b', c', hirr, φ, θ, Ψ, hKK, hφ, hΨc, hΨr, e₀, he₀U, he₀0, hline,
    hΨe₀0, hQΨe₀, hHperp⟩ := sec7_om4_setup h34 hRoot hc hs hom M₀ ρ b hS
  have hU : Module.finrank K (hc.VtSub hS.model t) = 4 := by
    rw [sec7_finrank_eq_of_semiEquiv θ Ψ hΨc, Module.finrank_fintype_fun_eq_card]
    simp only [Sec7Om4Idx, Fintype.card_sum, Fintype.card_fin]
  obtain ⟨β₁, h₁, hβ₁⟩ := sec7_induced_form M₀.B hf hr (hc.VtSub hS.model t) ψ hr1 hk1
  have hbarR : ∀ r : ↥(Rt M (LB M Q B) t),
      (QuotientGroup.mk ⟨(r : G), hRM r.2⟩ : Mbar M Q) ∈ bar M Q (Rt M (LB M Q B) t) := fun r =>
    Subgroup.mem_map.mpr ⟨⟨(r : G), hRM r.2⟩, Subgroup.mem_subgroupOf.mpr r.2, rfl⟩
  have hbarH : ∀ r : ↥(Rt M (LB M Q B) t),
      (QuotientGroup.mk ⟨(r : G), hRM r.2⟩ : Mbar M Q) ∈ bar M Q (H0 M Z) := fun r =>
    Subgroup.mem_map.mpr ⟨⟨(r : G), hRM r.2⟩, Subgroup.mem_subgroupOf.mpr (hc.Rt_le_H0 t r.2),
      rfl⟩
  have hactmem : ∀ (r : ↥(Rt M (LB M Q B) t)) (w : M₀.E), w ∈ hc.VtSub hS.model t →
      (ρ (QuotientGroup.mk ⟨(r : G), hRM r.2⟩)).toAdd w ∈ hc.VtSub hS.model t :=
    fun r w hw => hc.act_mem_VtSub hS ht _ (hbarR r) w hw
  let act : ↥(Rt M (LB M Q B) t) → ↥(hc.VtSub hS.model t) → ↥(hc.VtSub hS.model t) :=
    fun r w => ⟨(ρ (QuotientGroup.mk ⟨(r : G), hRM r.2⟩)).toAdd (w : M₀.E), hactmem r w w.2⟩
  have hactΨ : ∀ (r : ↥(Rt M (LB M Q B) t)) (u : ↥(hc.VtSub hS.model t)),
      Ψ (act r u) = ((φ r : GL Sec7Om4Idx K') : Matrix Sec7Om4Idx Sec7Om4Idx K') *ᵥ Ψ u :=
    fun r u => hΨr r u (hactmem r u u.2)
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have hcomm_act : ∀ a b : Mbar M Q, a * b = b * a → ∀ e,
      (ρ a).toAdd ((ρ b).toAdd e) = (ρ b).toAdd ((ρ a).toAdd e) := by
    intro a b hab e
    rw [← act_mul_apply ρ a b e, ← act_mul_apply ρ b a e, hab]
  have hψS : ∀ (r : ↥(Rt M (LB M Q B) t)) (e : M₀.E),
      ψ ((ρ (QuotientGroup.mk ⟨(r : G), hRM r.2⟩)).toAdd e) =
        (ρ (QuotientGroup.mk ⟨(r : G), hRM r.2⟩)).toAdd (ψ e) := by
    intro r e
    rw [hψ, hψ, map_sub,
      hcomm_act _ _ (endg_comm_centre hZ0 hRM (z := ⟨t, htM⟩) htZ0 (hbarR r)) e]
  have hinvβ : ∀ (r : ↥(Rt M (LB M Q B) t)) (x y : ↥(hc.VtSub hS.model t)),
      β₁ (act r x) (act r y) = β₁ x y := by
    intro r x y
    obtain ⟨c, hc'⟩ : ∃ c, ψ c = (y : M₀.E) := by
      have : (y : M₀.E) ∈ LinearMap.range ψ := by rw [hr1]; exact y.2
      exact LinearMap.mem_range.mp this
    have h1 : ψ ((ρ (QuotientGroup.mk ⟨(r : G), hRM r.2⟩)).toAdd c) =
        ((act r y : ↥(hc.VtSub hS.model t)) : M₀.E) := by
      rw [hψS, hc']
    rw [hβ₁ (act r x) (act r y) _ h1, hβ₁ x y c hc']
    exact hS.iso _ (hbarH r) _ _
  obtain ⟨κ, hκ⟩ := sec7_form_scalar_of_invariant hirr θ Ψ hΨc β₁ φ hφ act hactΨ hinvβ
  have hκ0 : κ ≠ 0 := by
    intro h0
    have hz : ∀ x y : ↥(hc.VtSub hS.model t), β₁ x y = 0 := fun x y => by
      have := hκ x y
      rw [h0, zero_mul] at this
      exact θ.map_eq_zero_iff.mp this
    have := h₁.1 ⟨e₀, he₀U⟩ (fun y => hz _ y)
    exact he₀0 (congrArg Subtype.val this)
  have hβzero : ∀ a b : ↥(hc.VtSub hS.model t),
      β₁ a b = 0 ↔ polar (quadMinus 2 K' b' c') (Ψ a) (Ψ b) = 0 := fun a b => by
    rw [← θ.map_eq_zero_iff, hκ a b, mul_eq_zero, or_iff_right hκ0]
  let 𝒢 : Type := {g : G // g ∈ M ∧ g ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G)}
  have hνU : ∀ (g : 𝒢) (e : M₀.E), e ∈ hc.VtSub hS.model t ↔
      (ρ (QuotientGroup.mk ⟨g.1, g.2.1⟩)).toAdd e ∈ hc.VtSub hS.model t := fun g e =>
    sec7_nu_img hc M₀ ρ b hS g.2.1 hZV hVQ (conjSubgroup_eq_self_iff.mpr g.2.2) e
  let eg : 𝒢 → M₀.E := fun g => (ρ (QuotientGroup.mk ⟨g.1, g.2.1⟩)).toAdd e₀
  have heg : ∀ g : 𝒢, eg g ∈ hc.VtSub hS.model t := fun g => (hνU g e₀).mp he₀U
  let xg : 𝒢 → (Sec7Om4Idx → K') := fun g => Ψ ⟨eg g, heg g⟩
  let Hg : 𝒢 → AddSubgroup (Sec7Om4Idx → K') := fun g =>
    (sec7Hset M₀ (Vt M (LB M Q B) B Z t) (conjSubgroup g.1 B)).comap
      (((hc.VtSub hS.model t).subtype.toAddMonoidHom).comp Ψ.symm.toAddMonoidHom)
  have hHg : ∀ (g : 𝒢) (y : Sec7Om4Idx → K'), y ∈ Hg g ↔
      ((Ψ.symm y : ↥(hc.VtSub hS.model t)) : M₀.E) ∈
        sec7Hset M₀ (Vt M (LB M Q B) B Z t) (conjSubgroup g.1 B) := fun g y => Iff.rfl
  let g₀ : 𝒢 := ⟨1, M.one_mem, Subgroup.one_mem _⟩
  have heg0 : eg g₀ = e₀ := by
    show (ρ (QuotientGroup.mk (1 : ↥M))).toAdd e₀ = e₀
    rw [QuotientGroup.mk_one, map_one]
    rfl
  have hxg0 : xg g₀ = Ψ ⟨e₀, he₀U⟩ :=
    congrArg Ψ (Subtype.ext heg0 : (⟨eg g₀, heg g₀⟩ : ↥(hc.VtSub hS.model t)) = ⟨e₀, he₀U⟩)
  have hx₀ : xg g₀ ≠ 0 := by rw [hxg0]; exact hΨe₀0
  have hQ₀ : quadMinus 2 K' b' c' (xg g₀) = 0 := by rw [hxg0]; exact hQΨe₀
  have hH₀ : ∀ y, y ∈ Hg g₀ ↔ polar (quadMinus 2 K' b' c') (xg g₀) y = 0 := by
    intro y
    rw [hHg, hxg0]
    show ((Ψ.symm y : ↥(hc.VtSub hS.model t)) : M₀.E) ∈
      sec7Hset M₀ (Vt M (LB M Q B) B Z t) (conjSubgroup 1 B) ↔ _
    rw [conjSubgroup_one]
    exact hHperp y
  have hscal : ∀ (g : 𝒢) (s : K'), s • xg g ∈ Hg g := by
    intro g s
    rw [hHg]
    have h1 : Ψ.symm (s • xg g) = θ.symm s • (⟨eg g, heg g⟩ : ↥(hc.VtSub hS.model t)) := by
      apply Ψ.injective
      rw [Ψ.apply_symm_apply, hΨc, θ.apply_symm_apply]
    rw [h1]
    show θ.symm s • eg g ∈ sec7Hset M₀ (Vt M (LB M Q B) B Z t) (conjSubgroup g.1 B)
    obtain ⟨-, hlg⟩ := sec7_img_conj_line hc M₀ ρ b hS g.2.1 he₀0 hline
    have hmem : θ.symm s • eg g ∈ M₀.img (conjSubgroup g.1 B) := (hlg _).mpr ⟨θ.symm s, rfl⟩
    have hBV : conjSubgroup g.1 B ≤ Vt M (LB M Q B) B Z t :=
      calc conjSubgroup g.1 B ≤ conjSubgroup g.1 (Vt M (LB M Q B) B Z t) :=
            Subgroup.map_mono (hc.B_le_Vt ht)
        _ = Vt M (LB M Q B) B Z t := conjSubgroup_eq_self_iff.mpr g.2.2
    exact M₀.img_mono (le_sup_of_le_left (le_inf hBV (Ctx.B_le_QB (hc.conj_of_mem g.2.1)))) hmem
  have hcard : ∀ g : 𝒢, Nat.card (Hg g) = Nat.card K' ^ 3 := by
    intro g
    have h0 : Nat.card (Hg g₀) = Nat.card K' ^ 3 :=
      sec7_natCard_polar_perp hirr hx₀ (Hg g₀) hH₀
    rw [← h0]
    obtain ⟨T, hT'⟩ := sec7_exists_coord_equiv (hc.VtSub hS.model t) Ψ
      (ρ (QuotientGroup.mk ⟨g.1, g.2.1⟩)).toAdd (hνU g)
    have hT : ∀ y, y ∈ Hg g₀ ↔ T y ∈ Hg g := by
      intro y
      rw [hHg, hHg]
      rw [hT' y]
      have h2 := sec7_Hset_conj hc M₀ ρ b hS g.2.1 (Vt M (LB M Q B) B Z t)
        (conjSubgroup_eq_self_iff.mpr g.2.2) 1
        ((Ψ.symm y : ↥(hc.VtSub hS.model t)) : M₀.E)
      rw [mul_one, conjSubgroup_one] at h2
      show ((Ψ.symm y : ↥(hc.VtSub hS.model t)) : M₀.E) ∈
        sec7Hset M₀ (Vt M (LB M Q B) B Z t) (conjSubgroup 1 B) ↔ _
      rw [conjSubgroup_one]
      exact h2.symm
    refine Nat.card_congr (Equiv.subtypeEquiv T.symm (fun y => ?_))
    rw [hT (T.symm y), Equiv.apply_symm_apply]
  have hsame : ∀ (g g' : 𝒢) (s : K'), s ≠ 0 → xg g' = s • xg g → Hg g' = Hg g := by
    intro g g' s hs0 hxs
    have h1 : eg g' = θ.symm s • eg g := by
      have : (⟨eg g', heg g'⟩ : ↥(hc.VtSub hS.model t)) =
          θ.symm s • (⟨eg g, heg g⟩ : ↥(hc.VtSub hS.model t)) := by
        apply Ψ.injective
        rw [hΨc, θ.apply_symm_apply]
        exact hxs
      exact congrArg Subtype.val this
    obtain ⟨-, hlg⟩ := sec7_img_conj_line hc M₀ ρ b hS g.2.1 he₀0 hline
    obtain ⟨-, hlg'⟩ := sec7_img_conj_line hc M₀ ρ b hS g'.2.1 he₀0 hline
    have hle : M₀.img (conjSubgroup g'.1 B) ≤ M₀.img (conjSubgroup g.1 B) := by
      intro v hv
      obtain ⟨s', rfl⟩ := (hlg' v).mp hv
      refine (hlg _).mpr ⟨s' * θ.symm s, ?_⟩
      show s' • eg g' = (s' * θ.symm s) • eg g
      rw [h1, smul_smul]
    have h2 := sec7_Hset_eq_of_img_le hc M₀ g.2.1 g'.2.1 (Vt M (LB M Q B) B Z t) hZV hVQ hle
    ext y
    rw [hHg, hHg, h2]
  have hact : ∀ (g : 𝒢) (r : ↥(Rt M (LB M Q B) t)), ∃ g' : 𝒢,
      xg g' = ((φ r : GL Sec7Om4Idx K') : Matrix Sec7Om4Idx Sec7Om4Idx K') *ᵥ xg g ∧
      ∀ y, y ∈ Hg g' ↔ ((((φ r)⁻¹ : GL Sec7Om4Idx K')) : Matrix Sec7Om4Idx Sec7Om4Idx K') *ᵥ y ∈
        Hg g := by
    intro g r
    have hrM : (r : G) ∈ M := hRM r.2
    have hrV : (r : G) ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
      hc.Rt_normalizes_Vt ht r.2
    refine ⟨⟨(r : G) * g.1, M.mul_mem hrM g.2.1, Subgroup.mul_mem _ hrV g.2.2⟩, ?_, ?_⟩
    · have e1 : (ρ (QuotientGroup.mk ⟨(r : G) * g.1, M.mul_mem hrM g.2.1⟩)).toAdd e₀ =
          (ρ (QuotientGroup.mk ⟨(r : G), hrM⟩)).toAdd (eg g) := by
        have : (QuotientGroup.mk ⟨(r : G) * g.1, M.mul_mem hrM g.2.1⟩ : Mbar M Q) =
            QuotientGroup.mk ⟨(r : G), hrM⟩ * QuotientGroup.mk ⟨g.1, g.2.1⟩ := rfl
        rw [this, act_mul_apply]
      have e2 : xg ⟨(r : G) * g.1, M.mul_mem hrM g.2.1, Subgroup.mul_mem _ hrV g.2.2⟩ =
          Ψ (act r ⟨eg g, heg g⟩) := congrArg Ψ (Subtype.ext e1)
      rw [e2, hactΨ]
    · intro y
      rw [hHg, hHg]
      have hφz : ((φ r : GL Sec7Om4Idx K') : Matrix Sec7Om4Idx Sec7Om4Idx K') *ᵥ
          (((((φ r)⁻¹ : GL Sec7Om4Idx K')) : Matrix Sec7Om4Idx Sec7Om4Idx K') *ᵥ y) = y := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec]
      have hy : Ψ.symm y = act r (Ψ.symm (((((φ r)⁻¹ : GL Sec7Om4Idx K')) :
          Matrix Sec7Om4Idx Sec7Om4Idx K') *ᵥ y)) := by
        apply Ψ.injective
        rw [Ψ.apply_symm_apply, hactΨ, Ψ.apply_symm_apply, hφz]
      rw [hy]
      exact sec7_Hset_conj hc M₀ ρ b hS hrM (Vt M (LB M Q B) B Z t)
        (conjSubgroup_eq_self_iff.mpr hrV) g.1
        ((Ψ.symm (((((φ r)⁻¹ : GL Sec7Om4Idx K')) : Matrix Sec7Om4Idx Sec7Om4Idx K') *ᵥ y) :
          ↥(hc.VtSub hS.model t)) : M₀.E)
  have hperp := sec7_om4_perp_family hirr φ hφ xg Hg g₀ hx₀ hQ₀ hH₀ hscal hcard hsame hact
  have hΨsymm : ∀ (c : K') (v : Sec7Om4Idx → K'), Ψ.symm (c • v) = θ.symm c • Ψ.symm v := by
    intro c v
    apply Ψ.injective
    rw [Ψ.apply_symm_apply, hΨc, θ.apply_symm_apply, Ψ.apply_symm_apply]
  obtain ⟨O, -, hObwd, hO1, hOcard, hOline, hOplane⟩ :=
    sec7_ovoid_map_semilinear2 θ.symm Ψ.symm hΨsymm hKK
      (sec7SingPts (quadMinus 2 K' b' c')) (fun P hP => hP.1) (sec7_singPts_ncard hirr)
      (sec7_singPts_line_ncard_le_two hirr) (sec7_singPts_plane_ncard_le hirr)
  obtain ⟨σ, a, ha, hνσ, hνf⟩ := sec7_nu_data hc M₀ ρ b hS hm
  have hmV' : conjSubgroup m (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t :=
    conjSubgroup_eq_self_iff.mpr hmV
  have hνU' : ∀ e, e ∈ hc.VtSub hS.model t ↔
      (ρ (QuotientGroup.mk ⟨m, hm⟩)).toAdd e ∈ hc.VtSub hS.model t := fun e =>
    sec7_nu_img hc M₀ ρ b hS hm hZV hVQ hmV' e
  have hG : ∀ P ∈ O, ∀ x ∈ P, ∀ y x' y' : ↥(hc.VtSub hS.model t),
      (x' : M₀.E) = (ρ (QuotientGroup.mk ⟨m, hm⟩)).toAdd (x : M₀.E) →
      (y' : M₀.E) = (ρ (QuotientGroup.mk ⟨m, hm⟩)).toAdd (y : M₀.E) →
      (β₁ x' y' = 0 ↔ β₁ x y = 0) := by
    intro P hP x hxP y x' y' hx' hy'
    obtain ⟨P₀, hP₀, hPeq⟩ := hObwd P hP
    have hxΨ : Ψ x ∈ P₀ := by
      have h : x ∈ (P : Set ↥(hc.VtSub hS.model t)) := hxP
      rw [hPeq] at h
      obtain ⟨w, hw, hwx⟩ := h
      rw [← hwx, Ψ.apply_symm_apply]
      exact hw
    by_cases hx0 : x = 0
    · subst hx0
      have hx'0 : x' = 0 := by
        apply Subtype.ext
        rw [hx']
        simp
      subst hx'0
      simp
    · have hΨx0 : Ψ x ≠ 0 := fun h => hx0 (Ψ.injective (h.trans (map_zero Ψ).symm))
      have hQx : quadMinus 2 K' b' c' (Ψ x) = 0 := hP₀.2 (Ψ x) hxΨ
      obtain ⟨A, hA, hAu⟩ :=
        omegaMinusFourSingularTrans_holds K' b' c' hirr (Ψ ⟨e₀, he₀U⟩) (Ψ x) hΨe₀0 hΨx0
          hQΨe₀ hQx
      obtain ⟨r, hr'⟩ : A ∈ φ.range := hφ ▸ hA
      have hrM : (r : G) ∈ M := hRM r.2
      have hrV : (r : G) ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
        hc.Rt_normalizes_Vt ht r.2
      let g₁ : 𝒢 := ⟨(r : G), hrM, hrV⟩
      let g₂ : 𝒢 := ⟨m * (r : G), M.mul_mem hm hrM, Subgroup.mul_mem _ hmV hrV⟩
      have hx1 : xg g₁ = Ψ x := by
        have h1 : xg g₁ = Ψ (act r ⟨e₀, he₀U⟩) := rfl
        rw [h1, hactΨ, hr', hAu]
      have hxeg1 : eg g₁ = (x : M₀.E) := by
        have : (⟨eg g₁, heg g₁⟩ : ↥(hc.VtSub hS.model t)) = x := Ψ.injective hx1
        exact congrArg Subtype.val this
      have heg2 : eg g₂ = (x' : M₀.E) := by
        have e1 : eg g₂ = (ρ (QuotientGroup.mk ⟨m, hm⟩)).toAdd (eg g₁) := by
          have : (QuotientGroup.mk ⟨m * (r : G), M.mul_mem hm hrM⟩ : Mbar M Q) =
              QuotientGroup.mk ⟨m, hm⟩ * QuotientGroup.mk ⟨(r : G), hrM⟩ := rfl
          show (ρ (QuotientGroup.mk ⟨m * (r : G), M.mul_mem hm hrM⟩)).toAdd e₀ = _
          rw [this, act_mul_apply]
        rw [e1, hxeg1, hx']
      have hx2 : xg g₂ = Ψ x' := congrArg Ψ (Subtype.ext heg2 :
        (⟨eg g₂, heg g₂⟩ : ↥(hc.VtSub hS.model t)) = x')
      have hx'0 : x' ≠ 0 := by
        intro h0
        apply hx0
        have h1 : (ρ (QuotientGroup.mk ⟨m, hm⟩)).toAdd (x : M₀.E) = 0 := by rw [← hx', h0]; rfl
        have h2 : (x : M₀.E) = 0 := (AddEquiv.map_eq_zero_iff _).mp h1
        exact Subtype.ext h2
      have hΨx'0 : Ψ x' ≠ 0 := fun h => hx'0 (Ψ.injective (h.trans (map_zero Ψ).symm))
      have hp1 := hperp g₁ (by rw [hx1]; exact hΨx0) (Ψ y)
      have hp2 := hperp g₂ (by rw [hx2]; exact hΨx'0) (Ψ y')
      rw [hx1, hHg, Ψ.symm_apply_apply] at hp1
      rw [hx2, hHg, Ψ.symm_apply_apply] at hp2
      have hconj := sec7_Hset_conj hc M₀ ρ b hS hm (Vt M (LB M Q B) B Z t) hmV' (r : G)
        (y : M₀.E)
      rw [hβzero, hβzero, ← hp1, ← hp2, hy']
      exact hconj
  obtain ⟨μ, hμ0, hμ⟩ := sec7_semilinear_proportional M₀.B hf hr (hc.VtSub hS.model t) hU ψ hr1
    hk1 σ (ρ (QuotientGroup.mk ⟨m, hm⟩)).toAdd hνσ a ha hνf hνU' β₁ hβ₁ h₁ O hO1 hOcard hOline
    hOplane hG
  exact ⟨μ, hμ0, hμ⟩

end Main

end CFSG.RankThree.GF2n.Stroth80
