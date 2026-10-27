module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS4bAux2
public import CFSG.LocalAnalysis.StandardType.GGWeylCartan
public import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl

public section

namespace CFSG.StandardType.LevTwo

open CFSG CFSG.Assembly CFSG.LieType.RootSystem LevTwoType
open CFSG.StandardType.S2MathFi1451 CFSG.StandardType.SecFiveRootRefl CFSG.LieType.Steinberg.OfCartan

attribute [local irreducible] rRefl levTwoS4b_beta levTwoS4b_w levTwoS4b_i levTwoS4b_eL

theorem levTwoS4b_exists_cartan {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) :
    ∃ (C : Matrix c.ιL c.ιL ℤ) (hC : TauCeti.IsFiniteType C),
      GGIntCartan c.ML C ∧ coxeterMatrix hC = c.ML :=
  ggWeylCartan (levTwoS4b_isWeylMatrix c) (levTwoS4b_le_three c)

theorem levTwoS4b_connected {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) :
    GGSimplyLacedConnected c.ML :=
  ggSimplyLacedConnected_of_weyl (levTwoS4b_isWeylMatrix c) (levTwoS4b_le_three c)

theorem levTwoS4b_notG2 {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) :
    ¬ ∃ e : Fin 2 ≃ c.ιL, c.ML = CoxeterMatrix.G₂.reindex e := by
  rintro ⟨e, he⟩
  have hne : e 0 ≠ e 1 := by
    intro h
    have hv := congrArg Fin.val (e.injective h)
    norm_num at hv
  have hle := levTwoS4b_le_three c (e 0) (e 1) hne
  rw [he] at hle
  have hlab : (CoxeterMatrix.G₂.reindex e).M (e 0) (e 1) = 6 := by
    rw [CoxeterMatrix.reindex_apply]
    simp [CoxeterMatrix.G₂, Matrix.of_apply, Matrix.cons_val']
  rw [hlab] at hle
  omega

theorem levTwoS4b_a_form {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) (k l : c.ιL) :
    (levTwoS4b_a c k l : ℚ) * form c.T.rootFT (toRat (levTwoS4b_beta c k))
        (toRat (levTwoS4b_beta c k)) =
      2 * form c.T.rootFT (toRat (levTwoS4b_beta c k)) (toRat (levTwoS4b_beta c l)) := by
  have h := coroot_mul_form_self c.T.rootFT (levTwoS4b_w c k) (levTwoS4b_i c k)
    (weylAction c.T.rootFT (levTwoS4b_w c l) (Pi.single (levTwoS4b_i c l) 1))
  rw [levTwoS4b_beta_eq_weylAction c k, levTwoS4b_beta_eq_weylAction c l] at h
  change (coroot c.T.root (levTwoS4b_i c k)
      (weylAction c.T.rootFT (levTwoS4b_w c k)⁻¹
        (weylAction c.T.rootFT (levTwoS4b_w c l) (Pi.single (levTwoS4b_i c l) 1))) : ℚ) *
      form c.T.rootFT (toRat (levTwoS4b_beta c k)) (toRat (levTwoS4b_beta c k)) =
    2 * form c.T.rootFT (toRat (levTwoS4b_beta c k)) (toRat (levTwoS4b_beta c l))
  rw [levTwoS4b_beta_eq_weylAction c l]
  exact h

theorem levTwoS4b_form_self_pos {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    (k : c.ιL) : 0 < form c.T.rootFT (toRat (levTwoS4b_beta c k))
      (toRat (levTwoS4b_beta c k)) := by
  have hne : levTwoS4b_beta c k ≠ 0 := by
    obtain ⟨w, i, hw⟩ := levTwoS4b_beta_isRt c k
    rw [← hw]
    intro h
    have h0 : (Pi.single i (1 : ℤ) : Fin c.T.n → ℤ) = 0 := by
      have h1 := congrArg (weylAction c.T.rootFT w⁻¹) h
      rw [weylAction_inv_apply_apply, map_zero] at h1
      exact h1
    have h2 := congrFun h0 i
    simp at h2
  have hne' : toRat (levTwoS4b_beta c k) ≠ 0 := by
    intro h
    exact hne (toRat_injective (by rw [h, map_zero]))
  exact form_pos c.T.rootFT hne'

theorem levTwoS4b_a_mul_self_of_edge {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    {k l : c.ιL} (h : c.ML.M k l = 3) :
    levTwoS4b_a c k l = levTwoS4b_a c l k ∧ levTwoS4b_a c k l * levTwoS4b_a c k l = 1 := by
  have hkl : k ≠ l := by
    intro heq; have hd := c.ML.diagonal k; rw [heq] at h hd; omega
  obtain ⟨C, hC, hCart, hcox⟩ := levTwoS4b_exists_cartan c
  have hprod := levTwoS4b_a_offdiag c C hC hcox k l hkl
  rcases hCart.2 k l hkl with ⟨hM2, -⟩ | ⟨-, hckl, hclk⟩ | ⟨hM4, -⟩ | ⟨hM6, -⟩
  · omega
  · have hp : levTwoS4b_a c k l * levTwoS4b_a c l k = 1 := by
      rw [hprod, hckl, hclk]; norm_num
    obtain ha | ha := Int.eq_one_or_neg_one_of_mul_eq_one hp
    · have hb : levTwoS4b_a c l k = 1 := by rw [ha] at hp; omega
      exact ⟨by rw [ha, hb], by rw [ha]; norm_num⟩
    · have hb : levTwoS4b_a c l k = -1 := by rw [ha] at hp; omega
      exact ⟨by rw [ha, hb], by rw [ha]; norm_num⟩
  · omega
  · omega

theorem levTwoS4b_form_ne_zero_of_edge {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    {k l : c.ιL} (h : c.ML.M k l = 3) :
    form c.T.rootFT (toRat (levTwoS4b_beta c k)) (toRat (levTwoS4b_beta c l)) ≠ 0 := by
  have ha1 := (levTwoS4b_a_mul_self_of_edge c h).2
  have ha0 : (levTwoS4b_a c k l : ℚ) ≠ 0 := by
    intro h0
    have : (levTwoS4b_a c k l : ℚ) * (levTwoS4b_a c k l : ℚ) = 1 := by exact_mod_cast ha1
    rw [h0] at this; norm_num at this
  intro hX
  have hf := levTwoS4b_a_form c k l
  rw [hX, mul_zero] at hf
  have hN := (levTwoS4b_form_self_pos c k).ne'
  rcases mul_eq_zero.mp hf with h0 | h0
  · exact ha0 h0
  · exact hN h0

theorem levTwoS4b_form_self_eq_of_edge {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    {k l : c.ιL} (h : c.ML.M k l = 3) :
    form c.T.rootFT (toRat (levTwoS4b_beta c k)) (toRat (levTwoS4b_beta c k)) =
      form c.T.rootFT (toRat (levTwoS4b_beta c l)) (toRat (levTwoS4b_beta c l)) := by
  have hkl : k ≠ l := by
    intro heq; have hd := c.ML.diagonal k; rw [heq] at h hd; omega
  obtain ⟨haeq, ha1⟩ := levTwoS4b_a_mul_self_of_edge c h
  have ha0 : (levTwoS4b_a c k l : ℚ) ≠ 0 := by
    intro h0
    have : (levTwoS4b_a c k l : ℚ) * (levTwoS4b_a c k l : ℚ) = 1 := by exact_mod_cast ha1
    rw [h0] at this; norm_num at this
  have h1 := levTwoS4b_a_form c k l
  have h2 := levTwoS4b_a_form c l k
  rw [← haeq, form_comm c.T.rootFT (toRat (levTwoS4b_beta c l)) (toRat (levTwoS4b_beta c k))]
    at h2
  exact mul_left_cancel₀ ha0 (h1.trans h2.symm)

theorem levTwoS4b_form_self_eq {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) (j k : c.ιL) :
    form c.T.rootFT (toRat (levTwoS4b_beta c j)) (toRat (levTwoS4b_beta c j)) =
      form c.T.rootFT (toRat (levTwoS4b_beta c k)) (toRat (levTwoS4b_beta c k)) := by
  let ctx := c
  let N : ctx.ιL → ℚ := fun i =>
    form ctx.T.rootFT (toRat (levTwoS4b_beta ctx i)) (toRat (levTwoS4b_beta ctx i))
  have key : ∀ a b, Relation.ReflTransGen (fun a b => ctx.ML.M a b = 3) a b → N a = N b := by
    intro a b hab
    induction hab with
    | refl => rfl
    | tail hab hbc ih =>
      exact ih.trans (levTwoS4b_form_self_eq_of_edge ctx hbc)
  exact key j k ((levTwoS4b_connected c).2 j k)

abbrev levTwoS4b_rel {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    (a b : Fin c.T.n → ℤ) : Prop :=
  b ∈ levTwoS4b_Phi c ∧ form c.T.rootFT (toRat a) (toRat b) ≠ 0

theorem levTwoS4b_mem_wsub_iff {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    (w : Wg c.T.rootFT) :
    w ∈ Wsub c.T.rootFT (levTwoS4b_Phi c) ↔
      ∃ h : ↥c.AL, (h : MulAut ↥c.Bs) = ((c.ρ w : ↥c.A) : MulAut ↥c.Bs) := by
  have hsub := levTwoS4b_wsub c
  constructor
  · intro hw
    refine ⟨⟨((c.ρ w : ↥c.A) : MulAut ↥c.Bs), ?_⟩, rfl⟩
    have hmem : (c.A.subtype.comp c.ρ.toMonoidHom) w ∈
        (Wsub c.T.rootFT (levTwoS4b_Phi c)).map (c.A.subtype.comp c.ρ.toMonoidHom) :=
      Subgroup.mem_map_of_mem _ hw
    rwa [hsub] at hmem
  · rintro ⟨h, hh⟩
    have hmemAL : ((c.ρ w : ↥c.A) : MulAut ↥c.Bs) ∈ c.AL := hh ▸ h.2
    have hmem : (c.A.subtype.comp c.ρ.toMonoidHom) w ∈
        (Wsub c.T.rootFT (levTwoS4b_Phi c)).map (c.A.subtype.comp c.ρ.toMonoidHom) := by
      rw [hsub]; exact hmemAL
    obtain ⟨y, hy, hyw⟩ := Subgroup.mem_map.mp hmem
    have hyw' : c.ρ y = c.ρ w := by
      apply Subtype.ext
      exact hyw
    rwa [c.ρ.injective hyw'] at hy

theorem levTwoS4b_reduce {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    {γ : Fin c.T.n → ℤ} (hγ : γ ∈ levTwoS4b_Phi c) :
    ∃ (j : c.ιL) (w : Wg c.T.rootFT), w ∈ Wsub c.T.rootFT (levTwoS4b_Phi c) ∧
      (γ = weylAction c.T.rootFT w (levTwoS4b_beta c j) ∨
        γ = -weylAction c.T.rootFT w (levTwoS4b_beta c j)) := by
  have hrefl : GGIsReflection c.p (((c.ρ (rRefl c.T.rootFT γ) : ↥c.A) : MulAut ↥c.Bs)) :=
    ((c.hdict _).2 ⟨rRefl c.T.rootFT γ, (mem_Refl_iff c.T.rootFT).2 ⟨γ, hγ.1, rfl⟩, rfl⟩).2
  let aL : ↥c.AL := ⟨((c.ρ (rRefl c.T.rootFT γ) : ↥c.A) : MulAut ↥c.Bs), hγ.2⟩
  have hreflL : GGIsReflection c.p (aL : MulAut ↥c.Bs) := hrefl
  have hALind : c.AL ≤ ggInduced ⊤ c.Bs := fun x hx => c.hA (c.hAL hx)
  obtain ⟨i, g, hg⟩ := ggSecFiveRootReflInput_holds (G := G) (p := c.p) (Bs := c.Bs)
    c.hp c.hp2 c.hEl c.hNT c.AL hALind c.ιL c.ML (levTwoS4b_isWeylMatrix c)
    (levTwoS4b_notG2 c) (levTwoS4b_eL c) (levTwoS4b_eL_spec c) aL hreflL
  have hgc_val : ((c.ρ (rRefl c.T.rootFT γ) : ↥c.A) : MulAut ↥c.Bs) =
      ((levTwoS4b_eL c (g * c.ML.simple i * g⁻¹) : ↥c.AL) : MulAut ↥c.Bs) :=
    congrArg (fun z : ↥c.AL => (z : MulAut ↥c.Bs)) hg
  have hgc : c.ρ (rRefl c.T.rootFT γ) =
      Subgroup.inclusion c.hAL (levTwoS4b_eL c (g * c.ML.simple i * g⁻¹)) :=
    Subtype.ext hgc_val
  let w' : Wg c.T.rootFT := c.ρ.symm (Subgroup.inclusion c.hAL (levTwoS4b_eL c g))
  have hρw' : c.ρ w' = Subgroup.inclusion c.hAL (levTwoS4b_eL c g) := by
    simp only [w', MulEquiv.apply_symm_apply]
  have hρbeta : c.ρ (rRefl c.T.rootFT (levTwoS4b_beta c i)) =
      Subgroup.inclusion c.hAL (levTwoS4b_eL c (c.ML.simple i)) :=
    Subtype.ext (levTwoS4b_beta_rho c i)
  have hrfl : rRefl c.T.rootFT γ = w' * rRefl c.T.rootFT (levTwoS4b_beta c i) * w'⁻¹ := by
    apply c.ρ.injective
    rw [map_mul, map_mul, map_inv, hρw', hρbeta, hgc]
    simp only [map_mul, map_inv]
  have hrβ : w' * rRefl c.T.rootFT (levTwoS4b_beta c i) * w'⁻¹ =
      (w' * levTwoS4b_w c i) * sg c.T.rootFT (levTwoS4b_i c i) * (w' * levTwoS4b_w c i)⁻¹ := by
    rw [levTwoS4b_rRefl_eq c i]; group
  obtain ⟨wγ, iγ, hwγ⟩ := hγ.1
  have hrγ : rRefl c.T.rootFT γ = wγ * sg c.T.rootFT iγ * wγ⁻¹ :=
    rRefl_eq_conj c.T.rootFT hwγ
  have hconj : wγ * sg c.T.rootFT iγ * wγ⁻¹ =
      (w' * levTwoS4b_w c i) * sg c.T.rootFT (levTwoS4b_i c i) *
        (w' * levTwoS4b_w c i)⁻¹ := by
    rw [← hrγ, hrfl, hrβ]
  have hw' : w' ∈ Wsub c.T.rootFT (levTwoS4b_Phi c) := by
    rw [levTwoS4b_mem_wsub_iff c w']
    exact ⟨levTwoS4b_eL c g, by rw [hρw']; rfl⟩
  obtain hγeq | hγeq := weylAction_eq_or_eq_neg_of_conj_eq c.T.rootFT hconj
  · refine ⟨i, w', hw', Or.inl ?_⟩
    rw [← hwγ, hγeq, weylAction_mul_apply, levTwoS4b_beta_eq_weylAction c i]
  · refine ⟨i, w', hw', Or.inr ?_⟩
    rw [← hwγ, hγeq, weylAction_mul_apply, levTwoS4b_beta_eq_weylAction c i]

theorem levTwoS4b_toRat_ne_zero {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    {δ : Fin c.T.n → ℤ} (hδ : IsRt c.T.rootFT δ) : toRat δ ≠ 0 := by
  obtain ⟨w, i, hw⟩ := hδ
  have hsingle : (Pi.single i (1 : ℤ) : Fin c.T.n → ℤ) ≠ 0 := by
    intro hh; have := congrFun hh i; simp at this
  intro h
  have h1 : weylAction c.T.rootFT w (Pi.single i 1) = 0 := by rw [hw]; exact toRat_injective (by rw [h, map_zero])
  have h2 : (Pi.single i (1 : ℤ) : Fin c.T.n → ℤ) = 0 := by
    have := congrArg (weylAction c.T.rootFT w⁻¹) h1
    rwa [weylAction_inv_apply_apply, map_zero] at this
  exact hsingle h2

theorem levTwoS4b_form_self_pos_of_mem {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    {δ : Fin c.T.n → ℤ} (hδ : δ ∈ levTwoS4b_Phi c) :
    0 < form c.T.rootFT (toRat δ) (toRat δ) :=
  form_pos c.T.rootFT (levTwoS4b_toRat_ne_zero c hδ.1)

theorem levTwoS4b_rel_symm {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    {a b : Fin c.T.n → ℤ} (ha : a ∈ levTwoS4b_Phi c) (_hb : b ∈ levTwoS4b_Phi c)
    (h : levTwoS4b_rel c a b) : levTwoS4b_rel c b a :=
  ⟨ha, by rw [form_comm c.T.rootFT (toRat b) (toRat a)]; exact h.2⟩

theorem levTwoS4b_reach_mem {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    {a : Fin c.T.n → ℤ} (ha : a ∈ levTwoS4b_Phi c) {b : Fin c.T.n → ℤ}
    (h : Relation.ReflTransGen (levTwoS4b_rel c) a b) : b ∈ levTwoS4b_Phi c := by
  induction h with
  | refl => exact ha
  | tail _ hbc _ => exact hbc.1

theorem levTwoS4b_neg {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    {β : Fin c.T.n → ℤ} (hβ : β ∈ levTwoS4b_Phi c) : -β ∈ levTwoS4b_Phi c := by
  refine ⟨isRt_neg c.T.rootFT hβ.1, ?_⟩
  rw [rRefl_neg c.T.rootFT hβ.1]
  exact hβ.2

theorem levTwoS4b_closed {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    {α β : Fin c.T.n → ℤ} (hα : α ∈ levTwoS4b_Phi c) (hβ : β ∈ levTwoS4b_Phi c) :
    weylAction c.T.rootFT (rRefl c.T.rootFT α) β ∈ levTwoS4b_Phi c := by
  refine ⟨isRt_smul c.T.rootFT hβ.1 (rRefl c.T.rootFT α), ?_⟩
  rw [rRefl_smul c.T.rootFT hβ.1 (rRefl c.T.rootFT α)]
  rw [map_mul, map_mul, map_inv]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hα.2 hβ.2) (Subgroup.inv_mem _ hα.2)

theorem levTwoS4b_rRefl_inv {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    {δ : Fin c.T.n → ℤ} (hδ : IsRt c.T.rootFT δ) :
    (rRefl c.T.rootFT δ)⁻¹ = rRefl c.T.rootFT δ := by
  obtain ⟨u, j, hu⟩ := hδ
  have hj : (sg c.T.rootFT j)⁻¹ = sg c.T.rootFT j :=
    inv_eq_of_mul_eq_one_right
      ((coxeterMatrix c.T.rootFT).toCoxeterSystem.simple_mul_simple_self j)
  rw [rRefl_eq_conj c.T.rootFT hu, mul_inv_rev, mul_inv_rev, inv_inv, hj]
  group

theorem levTwoS4b_reach_refl {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    {δ δ' : Fin c.T.n → ℤ} (hδ : δ ∈ levTwoS4b_Phi c) (hδ' : δ' ∈ levTwoS4b_Phi c) :
    Relation.ReflTransGen (levTwoS4b_rel c) δ (weylAction c.T.rootFT (rRefl c.T.rootFT δ') δ) := by
  obtain ⟨k, hk, hwk⟩ := weylAction_rRefl c.T.rootFT hδ'.1 δ
  by_cases h0 : form c.T.rootFT (toRat δ) (toRat δ') = 0
  · have hk0 : k = 0 := by
      have hfac : (k : ℚ) * form c.T.rootFT (toRat δ') (toRat δ') = 0 := by
        rw [hk, form_comm c.T.rootFT (toRat δ') (toRat δ), h0, mul_zero]
      rcases mul_eq_zero.mp hfac with h | h
      · exact_mod_cast h
      · exact absurd h (levTwoS4b_form_self_pos_of_mem c hδ').ne'
    rw [hwk, hk0]
    simp only [zero_smul, sub_zero]
    exact Relation.ReflTransGen.refl
  · have hδ'' : weylAction c.T.rootFT (rRefl c.T.rootFT δ') δ ∈ levTwoS4b_Phi c :=
      levTwoS4b_closed c hδ' hδ
    refine Relation.ReflTransGen.tail (Relation.ReflTransGen.single ⟨hδ', h0⟩) ?_
    refine ⟨hδ'', ?_⟩
    rw [hwk]
    have hsub : form c.T.rootFT (toRat δ') (toRat (δ - k • δ')) =
        form c.T.rootFT (toRat δ') (toRat δ) -
          (k : ℚ) * form c.T.rootFT (toRat δ') (toRat δ') := by
      rw [map_sub, map_zsmul, map_sub, map_zsmul, zsmul_eq_mul]
    rw [hsub, hk]
    have hval : form c.T.rootFT (toRat δ') (toRat δ) -
        2 * form c.T.rootFT (toRat δ') (toRat δ) =
        -(form c.T.rootFT (toRat δ) (toRat δ')) := by
      rw [form_comm c.T.rootFT (toRat δ') (toRat δ)]; ring
    rw [hval]
    exact neg_ne_zero.mpr h0

theorem levTwoS4b_reach_closure {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    {w : Wg c.T.rootFT} (hw : w ∈ Wsub c.T.rootFT (levTwoS4b_Phi c))
    {δ : Fin c.T.n → ℤ} (hδ : δ ∈ levTwoS4b_Phi c) :
    Relation.ReflTransGen (levTwoS4b_rel c) δ (weylAction c.T.rootFT w δ) := by
  let p : Wg c.T.rootFT → Prop := fun x =>
    ∀ δ ∈ levTwoS4b_Phi c, Relation.ReflTransGen (levTwoS4b_rel c) δ (weylAction c.T.rootFT x δ)
  have hgen : ∀ x ∈ rRefl c.T.rootFT '' levTwoS4b_Phi c, p x := by
    rintro _ ⟨δ', hδ', rfl⟩ δ hδ
    exact levTwoS4b_reach_refl c hδ hδ'
  have h := Subgroup.closure_induction_left (s := rRefl c.T.rootFT '' levTwoS4b_Phi c)
    (p := fun x _ => p x)
    (by intro δ hδ; exact Relation.ReflTransGen.refl)
    (by
      rintro x hx y hy ih δ hδ
      obtain ⟨δ', hδ', rfl⟩ := hx
      have hyδ : weylAction c.T.rootFT y δ ∈ levTwoS4b_Phi c :=
        levTwoS4b_reach_mem c hδ (ih δ hδ)
      rw [weylAction_mul_apply]
      exact (ih δ hδ).trans (levTwoS4b_reach_refl c hyδ hδ'))
    (by
      rintro x hx y hy ih δ hδ
      obtain ⟨δ', hδ', rfl⟩ := hx
      rw [levTwoS4b_rRefl_inv c hδ'.1]
      have hyδ : weylAction c.T.rootFT y δ ∈ levTwoS4b_Phi c :=
        levTwoS4b_reach_mem c hδ (ih δ hδ)
      rw [weylAction_mul_apply]
      exact (ih δ hδ).trans (levTwoS4b_reach_refl c hyδ hδ'))
    hw
  exact h δ hδ

theorem levTwoS4b_reflTransGen_symm {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    {a b : Fin c.T.n → ℤ} (ha : a ∈ levTwoS4b_Phi c) (_hb : b ∈ levTwoS4b_Phi c)
    (h : Relation.ReflTransGen (levTwoS4b_rel c) a b) :
    Relation.ReflTransGen (levTwoS4b_rel c) b a := by
  clear _hb
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
    exact Relation.ReflTransGen.head
      (levTwoS4b_rel_symm c (levTwoS4b_reach_mem c ha hab) hbc.1 hbc) ih

theorem levTwoS4b_form_neg_neg {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    (x : Fin c.T.n → ℤ) :
    form c.T.rootFT (toRat (-x)) (toRat (-x)) = form c.T.rootFT (toRat x) (toRat x) := by
  rw [map_neg, map_neg]
  simp only [LinearMap.map_neg, LinearMap.neg_apply, neg_neg]

theorem levTwoS4b_reach_beta {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    (j k : c.ιL) :
    Relation.ReflTransGen (levTwoS4b_rel c) (levTwoS4b_beta c j) (levTwoS4b_beta c k) := by
  have key : ∀ a b, Relation.ReflTransGen (fun a b => c.ML.M a b = 3) a b →
      Relation.ReflTransGen (levTwoS4b_rel c) (levTwoS4b_beta c a) (levTwoS4b_beta c b) := by
    intro a b hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih =>
      exact ih.tail ⟨levTwoS4b_beta_mem c _, levTwoS4b_form_ne_zero_of_edge c hbc⟩
  exact key j k ((levTwoS4b_connected c).2 j k)

theorem levTwoS4b_irred {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    {α β : Fin c.T.n → ℤ} (hα : α ∈ levTwoS4b_Phi c) (hβ : β ∈ levTwoS4b_Phi c) :
    Relation.ReflTransGen (fun a b => b ∈ levTwoS4b_Phi c ∧
      form c.T.rootFT (toRat a) (toRat b) ≠ 0) α β := by
  change Relation.ReflTransGen (levTwoS4b_rel c) α β
  obtain ⟨jα, wα, hwα, hαeq⟩ := levTwoS4b_reduce c hα
  obtain ⟨jβ, wβ, hwβ, hβeq⟩ := levTwoS4b_reduce c hβ
  have hwjα : weylAction c.T.rootFT wα (levTwoS4b_beta c jα) ∈ levTwoS4b_Phi c :=
    levTwoS4b_reach_mem c (levTwoS4b_beta_mem c jα)
      (levTwoS4b_reach_closure c hwα (levTwoS4b_beta_mem c jα))
  have hwjβ : weylAction c.T.rootFT wβ (levTwoS4b_beta c jβ) ∈ levTwoS4b_Phi c :=
    levTwoS4b_reach_mem c (levTwoS4b_beta_mem c jβ)
      (levTwoS4b_reach_closure c hwβ (levTwoS4b_beta_mem c jβ))
  have hneα : form c.T.rootFT (toRat (-(weylAction c.T.rootFT wα (levTwoS4b_beta c jα))))
      (toRat (weylAction c.T.rootFT wα (levTwoS4b_beta c jα))) ≠ 0 := by
    rw [map_neg, LinearMap.map_neg]
    exact neg_ne_zero.mpr (levTwoS4b_form_self_pos_of_mem c hwjα).ne'
  have hneβ : form c.T.rootFT (toRat (weylAction c.T.rootFT wβ (levTwoS4b_beta c jβ)))
      (toRat (-(weylAction c.T.rootFT wβ (levTwoS4b_beta c jβ)))) ≠ 0 := by
    rw [map_neg, LinearMap.map_neg]
    exact neg_ne_zero.mpr (levTwoS4b_form_self_pos_of_mem c hwjβ).ne'
  have hbackα : Relation.ReflTransGen (levTwoS4b_rel c)
      (weylAction c.T.rootFT wα (levTwoS4b_beta c jα)) (levTwoS4b_beta c jα) :=
    levTwoS4b_reflTransGen_symm c (levTwoS4b_beta_mem c jα) hwjα
      (levTwoS4b_reach_closure c hwα (levTwoS4b_beta_mem c jα))
  have hαj : Relation.ReflTransGen (levTwoS4b_rel c) α (levTwoS4b_beta c jα) := by
    rcases hαeq with h | h
    · rw [h]; exact hbackα
    · rw [h]
      exact (Relation.ReflTransGen.single ⟨hwjα, hneα⟩).trans hbackα
  have hβj : Relation.ReflTransGen (levTwoS4b_rel c) (levTwoS4b_beta c jβ) β := by
    rcases hβeq with h | h
    · rw [h]; exact levTwoS4b_reach_closure c hwβ (levTwoS4b_beta_mem c jβ)
    · rw [h]
      exact (levTwoS4b_reach_closure c hwβ (levTwoS4b_beta_mem c jβ)).tail
        ⟨levTwoS4b_neg c hwjβ, hneβ⟩
  exact (hαj).trans ((levTwoS4b_reach_beta c jα jβ).trans hβj)

theorem levTwoS4b_oneLen {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    {α β : Fin c.T.n → ℤ} (hα : α ∈ levTwoS4b_Phi c) (hβ : β ∈ levTwoS4b_Phi c) :
    form c.T.rootFT (toRat α) (toRat α) = form c.T.rootFT (toRat β) (toRat β) := by
  have hlen : ∀ (w : Wg c.T.rootFT) (j : c.ιL),
      form c.T.rootFT (toRat (weylAction c.T.rootFT w (levTwoS4b_beta c j)))
        (toRat (weylAction c.T.rootFT w (levTwoS4b_beta c j))) =
      form c.T.rootFT (toRat (levTwoS4b_beta c j)) (toRat (levTwoS4b_beta c j)) :=
    fun w j => form_weylAction c.T.rootFT w _ _
  obtain ⟨jα, wα, -, hαeq⟩ := levTwoS4b_reduce c hα
  obtain ⟨jβ, wβ, -, hβeq⟩ := levTwoS4b_reduce c hβ
  have hαlen : form c.T.rootFT (toRat α) (toRat α) =
      form c.T.rootFT (toRat (levTwoS4b_beta c jα)) (toRat (levTwoS4b_beta c jα)) := by
    rcases hαeq with h | h
    · rw [h]; exact hlen wα jα
    · rw [h, levTwoS4b_form_neg_neg]; exact hlen wα jα
  have hβlen : form c.T.rootFT (toRat β) (toRat β) =
      form c.T.rootFT (toRat (levTwoS4b_beta c jβ)) (toRat (levTwoS4b_beta c jβ)) := by
    rcases hβeq with h | h
    · rw [h]; exact hlen wβ jβ
    · rw [h, levTwoS4b_form_neg_neg]; exact hlen wβ jβ
  rw [hαlen, hβlen, levTwoS4b_form_self_eq c jα jβ]

theorem levTwoS4b_phiStruct_basic {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) :
    PhiStruct c.T.rootFT (levTwoS4b_Phi c) :=
  ⟨fun _ hβ => hβ.1, fun _ hβ => levTwoS4b_neg c hβ, fun _ hα _ hβ => levTwoS4b_closed c hα hβ,
    fun _ hα _ hβ => levTwoS4b_irred c hα hβ, fun _ hα _ hβ => levTwoS4b_oneLen c hα hβ⟩

end CFSG.StandardType.LevTwo
