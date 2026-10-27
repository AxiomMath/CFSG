module

public import CFSG.Quasithin.EmptyFaithful.S153D35

public section

namespace CFSG.Quasithin.SBd9

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417
open scoped commutatorElement

section Involution

theorem conjAct_mul_self_eq_one {G : Type} [Group G] {V : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (V : Set G)) (h : t * t ∈ Subgroup.centralizer (V : Set G)) :
    conjAct V ⟨t, ht⟩ * conjAct V ⟨t, ht⟩ = 1 := by
  have e : ∀ (g : Subgroup.normalizer (V : Set G)) (w : V),
      ((conjAct V g w : V) : G) = (g : G) * (w : G) * (g : G)⁻¹ := fun g w =>
    Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion le_rfl g) w
  ext v
  rw [MulAut.mul_apply, MulAut.one_apply]
  rw [e, e]
  have h2 := Subgroup.mem_centralizer_iff.mp h v v.2
  calc t * (t * (v : G) * t⁻¹) * t⁻¹ = (t * t) * (v : G) * (t * t)⁻¹ := by group
    _ = (v : G) := by rw [← h2, mul_inv_cancel_right]

theorem map_conj_map_conj {H : Type*} [Group H] {τ : H} (hτ : τ * τ = 1) (A : Subgroup H) :
    (A.map (MulAut.conj τ).toMonoidHom).map (MulAut.conj τ).toMonoidHom = A := by
  have hinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have hcc : (MulAut.conj τ).toMonoidHom.comp (MulAut.conj τ).toMonoidHom = MonoidHom.id H := by
    ext x
    show τ * (τ * x * τ⁻¹) * τ⁻¹ = x
    rw [hinv]
    calc τ * (τ * x * τ) * τ = (τ * τ) * x * (τ * τ) := by group
      _ = x := by rw [hτ]; group
  rw [Subgroup.map_map, hcc, Subgroup.map_id]

end Involution

section Decomposition

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem decomp153_swap (D : Decomp153 T M V₁ V₂ t) : Decomp153 T M V₂ V₁ t where
  le₁ := D.le₂
  le₂ := D.le₁
  inf := by rw [inf_comm]; exact D.inf
  sup := by rw [sup_comm]; exact D.sup
  card₁ := D.card₂
  card₂ := D.card₁
  definite := by
    obtain ⟨q, h1, h2, h3, h4, h5⟩ := D.definite
    exact ⟨q, h1, h2, h3, h4, fun v hv => by rw [h5 v hv]; exact and_congr_left' or_comm⟩
  t_mem := D.t_mem
  swap₁ := D.swap₂
  swap₂ := D.swap₁
  t_sq := D.t_sq
  t_ne := D.t_ne
  comm₁ := D.comm₂
  comm₂ := D.comm₁
  iso₁ := D.iso₂
  iso₂ := D.iso₁
  inf_aut := by rw [inf_comm]; exact D.inf_aut
  comm_aut := fun a ha b hb => (D.comm_aut b hb a ha).symm
  conj_aut := fun ht => by
    rw [← D.conj_aut ht]
    exact map_conj_map_conj (conjAct_mul_self_eq_one ht D.t_sq) _
  factor := fun ht => by
    rw [sup_comm (autOn (M ⊓ Subgroup.centralizer (V₁ : Set G)) (VZ T M))]
    exact D.factor ht
  model := by
    obtain ⟨hV, L₁, L₂, tb, hS, h1, h2, ht⟩ := D.model
    exact ⟨hV, L₂, L₁, tb, hS.symm, h2, h1, ht⟩

theorem sgp153_swap (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) :
    Sgp153 T V₂ = Sgp153 T V₁ :=
  le_antisymm (le_inf inf_le_left (h.Sgp153_le_normalizer_V₂ (decomp153_swap D)))
    (le_inf inf_le_left (h.Sgp153_le_normalizer_V₂ D))

theorem mem_V₂_iff_conj_mem_V₁ (D : Decomp153 T M V₁ V₂ t) (g : G) :
    g ∈ V₂ ↔ t⁻¹ * g * t ∈ V₁ := by
  constructor
  · intro hg
    have hc := Subgroup.mem_centralizer_iff.mp D.t_sq g (D.le₂ hg)
    have e : t⁻¹ * g * t = t * g * t⁻¹ :=
      calc t⁻¹ * g * t = t⁻¹ * (g * (t * t)) * t⁻¹ := by group
        _ = t⁻¹ * ((t * t) * g) * t⁻¹ := by rw [hc]
        _ = t * g * t⁻¹ := by group
    rw [e]
    exact D.swap₂ g hg
  · intro hg
    have h1 := D.swap₁ _ hg
    have e : t * (t⁻¹ * g * t) * t⁻¹ = g := by group
    rwa [e] at h1

end Decomposition

section Contexts

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem hyp15310_swap (h : Hyp15310 G T Mc M V₁ V₂ Yp t) (hY : Yp = Y153 Mc M) :
    Hyp15310 G T Mc M V₂ V₁ Yp t :=
  ⟨h.hyp, decomp153_swap h.decomp, Or.inl hY⟩

theorem facts153_congr (hS : Sgp153 T V₂ = Sgp153 T V₁) (f : Facts153 T M V₁ Yp I) :
    Facts153 T M V₂ Yp I :=
  { f with sylow := by rw [hS]; exact f.sylow }

theorem facts15311_congr (hS : Sgp153 T V₂ = Sgp153 T V₁) (f : Facts15311 T M V₁ Yp I) :
    Facts15311 T M V₂ Yp I := by
  have hR : R153 T V₂ Yp = R153 T V₁ Yp := by
    unfold R153
    rw [hS]
  exact { f with
    sylow := by rw [hS]; exact f.sylow
    R_eq := by rw [hR]; exact f.R_eq
    radical := by rw [hR]; exact f.radical
    sylow_R := by rw [hR]; exact f.sylow_R
    cgs := by rw [hR]; exact f.cgs }

theorem concl15333_congr (hS : Sgp153 T V₂ = Sgp153 T V₁) (c : Concl15333 T M V₁ Yp I L) :
    Concl15333 T M V₂ Yp I L :=
  { c with inv_le := by rw [hS]; exact c.inv_le }

theorem ctxComp_swap (c : CtxComp T Mc M V₁ V₂ Yp I t) (hY : Yp = Y153 Mc M) :
    CtxComp T Mc M V₂ V₁ Yp I t := by
  have hS : Sgp153 T V₂ = Sgp153 T V₁ := sgp153_swap c.hyp.hyp c.hyp.decomp
  exact
    { hyp := hyp15310_swap c.hyp hY
      inH := by rw [hS]; exact c.inH
      notCharTwo := c.notCharTwo
      facts := facts153_congr hS c.facts
      charTwo_MI := c.charTwo_MI
      oddCore := c.oddCore }

theorem ctxComp2_swap (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hY : Yp = Y153 Mc M) :
    CtxComp2 T Mc M V₂ V₁ Yp I L t := by
  have hS : Sgp153 T V₂ = Sgp153 T V₁ := sgp153_swap c.hyp.hyp c.hyp.decomp
  exact
    { toCtxComp := ctxComp_swap c.toCtxComp hY
      rank := c.rank
      facts11 := facts15311_congr hS c.facts11
      s3s3 := by rw [hS]; exact c.s3s3
      c33 := concl15333_congr hS c.c33
      c34 := c.c34 }

end Contexts

end CFSG.Quasithin.SBd9
