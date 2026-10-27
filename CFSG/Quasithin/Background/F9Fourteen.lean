module

public import CFSG.Quasithin.Background.F9Geometry

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom
open scoped Pointwise

variable {G : Type*} [Group G]

section Fin

variable [Finite G]

theorem commutator_Vv_Vv_eq_bot_of_mem_Γ1 {G₀ G₁ G₂ T V : Subgroup G}
    (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) {β β' : CosetGeom G₀ G₁ G₂}
    (hβ : β ∈ Γ1 G₀ G₁ G₂) (hβ' : β' ∈ Γ1 G₀ G₁ G₂)
    (hd : dist β β' + 2 < critDist G₀ G₁ G₂ V) : ⁅Vv V β, Vv V β'⁆ = ⊥ := by
  obtain ⟨y, rfl⟩ := hβ
  obtain ⟨y', rfl⟩ := hβ'
  rw [Vv_inr, Vv_inr, Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine iSup₂_le fun x hx => ?_
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm,
    Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine iSup₂_le fun x' hx' => ?_
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  have hν : (Sum.inl x : CosetGeom G₀ G₁ G₂) ∈ Γ0 G₀ G₁ G₂ := ⟨x, rfl⟩
  have hμ : (Sum.inl x' : CosetGeom G₀ G₁ G₂) ∈ Γ0 G₀ G₁ G₂ := ⟨x', rfl⟩
  have d1 : dist (Sum.inl x : CosetGeom G₀ G₁ G₂) (Sum.inr y) = 1 := by
    rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr hx
  have d2 : dist (Sum.inr y' : CosetGeom G₀ G₁ G₂) (Sum.inl x') = 1 :=
    dist_eq_one_iff_adj.mpr hx'
  have t1 := dist_triangle hyp.gen (Sum.inl x : CosetGeom G₀ G₁ G₂) (Sum.inr y)
    (Sum.inl x')
  have t2 := dist_triangle hyp.gen (Sum.inr y : CosetGeom G₀ G₁ G₂) (Sum.inr y')
    (Sum.inl x')
  have hd' : dist (Sum.inl x : CosetGeom G₀ G₁ G₂) (Sum.inl x') < critDist G₀ G₁ G₂ V := by
    omega
  have := commutator_Vv_Vv_eq_bot hyp hV hν hμ hd'
  rw [Vv_inl, Vv_inl] at this
  exact this

namespace HypF98

variable {T V L V₁ Vp H : Subgroup G} {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}

theorem F914_2 (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g)
    (hb : F8.b T V L H = 3) : ∃ k ∈ H, F8.A₁ V₁ (g : G) ≤ conjSub k⁻¹ V := by
  have hyp := h.amalgamHypV
  have h1 : CosetGeom.dist (F8.γ₁ T L H) γ' = 1 := by
    have := s.geodesic
    omega
  have hγ'nb : γ' ∈ nbrs (F8.γ₁ T L H) := dist_eq_one_iff_adj.mp h1
  have hγ₀nb : F8.γ₀ T L H ∈ nbrs (F8.γ₁ T L H) :=
    (adj_γ₀_γ₁ (G₀ := (L ⊔ T) ⊔ H)).symm
  obtain ⟨k, hk, hk0⟩ := stab_transitive_on_nbrs hγ₀nb hγ'nb
  have hkH : (k : G) ∈ H := by rwa [stab_γ₁ hyp.le₂] at hk
  have e1 := Vv_smul_γ₀ (G₂ := H) hyp.normalizes g
  have e2 := Vv_smul_γ₀ (G₂ := H) hyp.normalizes k
  rw [s.edge₀] at e1
  rw [hk0] at e2
  refine ⟨(k : G)⁻¹, H.inv_mem hkH, ?_⟩
  rw [inv_inv]
  exact (conjSub_mono (g : G) h.V₁_le_V).trans (e1.symm.trans e2).le

theorem F914_3 (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g)
    (htrans : ∀ v ∈ V, ∀ w ∈ V, v ≠ 1 → w ≠ 1 → ∃ l ∈ L, l * v * l⁻¹ = w)
    (hH : H = Subgroup.centralizer (V₁ : Set G)) {k : G} (hk : k ∈ H)
    (hA : conjSub k⁻¹ (F8.A₁ V₁ (g : G)) ≤ V) :
    F8.b T V L H = 3 ∧
      ∃ l ∈ L, conjSub k⁻¹ (F8.Uγ Vp H (g : G)) = conjSub l (conjClosure Vp H) := by
  have hyp := h.amalgamHypV
  obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h.V₁_ne_bot
  have hz1' : z ≠ 1 := fun e => hz1 (Subtype.ext e)
  have ha : (g : G) * z * (g : G)⁻¹ ∈ F8.A₁ V₁ (g : G) := mul_mem_conjSub hz
  have ha1 : (g : G) * z * (g : G)⁻¹ ≠ 1 := fun e => hz1' (conj_eq_one_iff.mp e)
  have hv : k⁻¹ * z * k⁻¹⁻¹ ∈ V₁ :=
    (Subgroup.mem_normalizer_iff.mp (h.H_normalizes_V₁ (H.inv_mem hk)) z).mp hz
  have hv1 : k⁻¹ * z * k⁻¹⁻¹ ≠ 1 := fun e => hz1' (conj_eq_one_iff.mp e)
  have hw : k⁻¹ * ((g : G) * z * (g : G)⁻¹) * k⁻¹⁻¹ ∈ V := hA (mul_mem_conjSub ha)
  have hw1 : k⁻¹ * ((g : G) * z * (g : G)⁻¹) * k⁻¹⁻¹ ≠ 1 := fun e => ha1 (conj_eq_one_iff.mp e)
  obtain ⟨l, hl, hlvw⟩ := htrans _ (h.V₁_le_V hv) _ hw hv1 hw1
  set x : G := k * l * k⁻¹ with hx
  have hxz : x * z * x⁻¹ = (g : G) * z * (g : G)⁻¹ := by
    calc x * z * x⁻¹ = k * (l * (k⁻¹ * z * k⁻¹⁻¹) * l⁻¹) * k⁻¹ := by rw [hx]; group
      _ = k * (k⁻¹ * ((g : G) * z * (g : G)⁻¹) * k⁻¹⁻¹) * k⁻¹ := by rw [hlvw]
      _ = (g : G) * z * (g : G)⁻¹ := by group
  have hcardx : Nat.card (conjSub x V₁) = 2 := (card_conjSub _ _).trans h.card_V₁
  have hcardA : Nat.card (F8.A₁ V₁ (g : G)) = 2 := (card_conjSub _ _).trans h.card_V₁
  have hne : conjSub x V₁ ⊓ F8.A₁ V₁ (g : G) ≠ ⊥ := by
    intro hbot
    have hmem : x * z * x⁻¹ ∈ conjSub x V₁ ⊓ F8.A₁ V₁ (g : G) := by
      refine ⟨mul_mem_conjSub hz, ?_⟩
      rw [hxz]; exact ha
    rw [hbot, Subgroup.mem_bot, hxz] at hmem
    exact ha1 hmem
  have hle : conjSub x V₁ ≤ F8.A₁ V₁ (g : G) := le_of_card_eq_two_of_inf_ne_bot hcardx hne
  have heq : conjSub x V₁ = F8.A₁ V₁ (g : G) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardA, hcardx])
  have hc : conjSub ((g : G)⁻¹ * x) V₁ = V₁ := by
    rw [conjSub_mul, heq]
    exact conjSub_conjSub_inv (g : G) V₁
  have hcH : (g : G)⁻¹ * x ∈ H := by
    refine hH.ge ?_
    rw [← normalizer_eq_centralizer_of_card_eq_two h.card_V₁]
    exact mem_normalizer_of_conjSub_eq hc
  have hlG : l ∈ (L ⊔ T) ⊔ H := Subgroup.mem_sup_left (Subgroup.mem_sup_left hl)
  have hkG : k ∈ (L ⊔ T) ⊔ H := Subgroup.mem_sup_right hk
  set l' : ↥((L ⊔ T) ⊔ H) := ⟨l, hlG⟩ with hl'
  set k' : ↥((L ⊔ T) ⊔ H) := ⟨k, hkG⟩ with hk'
  have hl0 : l' • F8.γ₀ T L H = F8.γ₀ T L H :=
    smul_γ₀_of_mem hyp.le₁ (le_sup_left (a := L) (b := T) hl)
  have hl1 : l' • F8.γ₁ T L H ∈ nbrs (F8.γ₀ T L H) := by
    have := (smul_adj l').mpr (adj_γ₀_γ₁ (G₀ := (L ⊔ T) ⊔ H) (G₁ := L ⊔ T) (G₂ := H))
    rw [hl0] at this
    exact this
  have hk1 : k' • F8.γ₁ T L H = F8.γ₁ T L H := smul_γ₁_of_mem hyp.le₂ hk
  have hk1' : k'⁻¹ • F8.γ₁ T L H = F8.γ₁ T L H := by
    rw [inv_smul_eq_iff]; exact hk1.symm
  set X : ↥((L ⊔ T) ⊔ H) := k' * l' * k'⁻¹ with hX
  have hgX : (g⁻¹ * X) • F8.γ₁ T L H = F8.γ₁ T L H := by
    refine smul_eq_of_mem_stab ?_
    rw [stab_γ₁ hyp.le₂]
    exact hcH
  have hXγ : X • F8.γ₁ T L H = γ := by
    have e : X = g * (g⁻¹ * X) := by group
    rw [e, mul_smul, hgX, s.edge₁]
  have hγeq : k'⁻¹ • γ = l' • F8.γ₁ T L H := by
    rw [← hXγ, ← mul_smul, hX]
    have e : k'⁻¹ * (k' * l' * k'⁻¹) = l' * k'⁻¹ := by group
    rw [e, mul_smul, hk1']
  have hd2 : CosetGeom.dist (F8.γ₁ T L H) γ ≤ 2 := by
    have e := dist_smul k'⁻¹ (F8.γ₁ T L H) γ
    rw [hk1', hγeq] at e
    rw [← e]
    have t := dist_triangle hyp.gen (F8.γ₁ T L H) (F8.γ₀ T L H) (l' • F8.γ₁ T L H)
    have d1 : CosetGeom.dist (F8.γ₁ T L H) (F8.γ₀ T L H) = 1 := by
      rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr adj_γ₀_γ₁
    have d2 : CosetGeom.dist (F8.γ₀ T L H) (l' • F8.γ₁ T L H) = 1 :=
      dist_eq_one_iff_adj.mpr hl1
    omega
  have hb3 : 3 ≤ F8.b T V L H := h.three_le_b_and_odd.1
  have hb : F8.b T V L H = 3 := by
    have t := dist_triangle hyp.gen (F8.γ₀ T L H) (F8.γ₁ T L H) γ
    have d1 : CosetGeom.dist (F8.γ₀ T L H) (F8.γ₁ T L H) = 1 :=
      dist_eq_one_iff_adj.mpr adj_γ₀_γ₁
    have hdγ : CosetGeom.dist (F8.γ₀ T L H) γ = F8.b T V L H := s.critical.dist_eq
    omega
  refine ⟨hb, l, hl, ?_⟩
  have hkc : k⁻¹ * ((g : G)⁻¹ * x)⁻¹ ∈ Subgroup.normalizer (conjClosure Vp H : Set G) :=
    le_normalizer_conjClosure Vp H (H.mul_mem (H.inv_mem hk) (H.inv_mem hcH))
  have e : k⁻¹ * (g : G) = l * (k⁻¹ * ((g : G)⁻¹ * x)⁻¹) := by
    rw [hx]; group
  unfold F8.Uγ
  rw [← conjSub_mul, e, conjSub_mul, F7.conjSub_eq_of_mem_normalizer hkc]

theorem exists_noncomm_of_b_eq_three (h : HypF98 T V L V₁ Vp H) (hb : F8.b T V L H = 3) :
    ∃ l ∈ L, ∃ v ∈ conjClosure V H, ∃ u ∈ conjSub l (conjClosure Vp H), v * u ≠ u * v := by
  have hyp := h.amalgamHypV
  have hV := h.V_ne_bot
  obtain ⟨γ, γ', g, s⟩ := h.exists_F8Setup
  have h1 : CosetGeom.dist (F8.γ₁ T L H) γ' = 1 := by
    have := s.geodesic
    omega
  have hγ'nb : γ' ∈ nbrs (F8.γ₁ T L H) := dist_eq_one_iff_adj.mp h1
  have hg0 : g⁻¹ • γ' = F8.γ₀ T L H := by rw [← s.edge₀, inv_smul_smul]
  have hβ : g⁻¹ • F8.γ₁ T L H ∈ nbrs (F8.γ₀ T L H) := by
    have := (smul_adj g⁻¹).mpr (show (graph ((L ⊔ T) ⊔ H) (L ⊔ T) H).Adj γ' (F8.γ₁ T L H) from
      mem_nbrs_symm hγ'nb)
    rw [hg0] at this
    exact this
  have hγ₁nb : F8.γ₁ T L H ∈ nbrs (F8.γ₀ T L H) := adj_γ₀_γ₁
  obtain ⟨y, hy, hyβ⟩ := stab_transitive_on_nbrs hβ hγ₁nb
  set z₀ : ↥((L ⊔ T) ⊔ H) := y * g⁻¹ with hz₀
  have hz₁ : z₀ • F8.γ₁ T L H = F8.γ₁ T L H := by rw [hz₀, mul_smul]; exact hyβ
  have hz₀H : (z₀ : G) ∈ H := by
    have := mem_stab_of_smul_eq hz₁
    rwa [stab_γ₁ hyp.le₂] at this
  have hz₀γ : z₀ • γ = y • F8.γ₁ T L H := by
    rw [hz₀, mul_smul, ← s.edge₁, inv_smul_smul]
  have hyLT : (y : G) ∈ L ⊔ T := by rwa [stab_γ₀ hyp.le₁] at hy
  have hmul : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * T :=
    Subgroup.coe_mul_of_right_le_normalizer_left L T h.normalizes_L
  obtain ⟨l, hl, t, ht, hyeq⟩ : (y : G) ∈ (L : Set G) * T := by rw [← hmul]; exact hyLT
  have hstabε : stab (z₀ • γ) = conjSub l H := by
    rw [hz₀γ, stab_smul, stab_γ₁ hyp.le₂, ← hyeq, conjSub_mul, F7.conjSub_eq_of_mem (h.T_le_H ht)]
  have hball : ¬ conjSub (z₀ : G) V ≤ ballStab 1 (z₀ • γ) := by
    rw [ballStab_smul, conjSub_le_iff, conjSub_conjSub_inv]
    exact s.critical.not_le
  have hVstab : V ≤ stab γ := V_le_stab_of_dist_le hyp hV s.critical.dist_eq.le
  have hVε : conjSub (z₀ : G) V ≤ stab (z₀ • γ) := by
    rw [stab_smul]; exact conjSub_mono _ hVstab
  have hnot : ¬ conjSub (z₀ : G) V ≤ pCoreOf 2 (stab (z₀ • γ)) := fun hle =>
    hball (hle.trans (pCoreOf_stab_le_ballStab_one hyp.toAmalgamHyp _))
  have hP : pCoreOf 2 (stab (z₀ • γ)) = centralizerMod (conjSub l V₁) (conjSub l H)
      (conjSub l (conjClosure Vp H)) := by
    rw [hstabε, pCoreOf_conjSub, h.pCoreOf_eq_centralizerMod, conjSub_centralizerMod]
  rw [hP] at hnot
  obtain ⟨v, hvV, hvn⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hvH : v ∈ conjSub l H := by
    have := hVε hvV
    rwa [hstabε] at this
  have hvN : v ∈ Subgroup.normalizer (conjSub l V₁ : Set G) :=
    conjSub_le_normalizer h.H_normalizes_V₁ hvH
  obtain ⟨u, hu, hvu⟩ : ∃ u ∈ conjSub l (conjClosure Vp H), v * u * v⁻¹ * u⁻¹ ∉ conjSub l V₁ := by
    by_contra hcon
    push Not at hcon
    exact hvn ⟨hvH, hvN, hcon⟩
  refine ⟨l, hl, v, HypF91.conjSub_le_conjClosure hz₀H hvV, u, hu, fun e => hvu ?_⟩
  rw [e]
  simp

theorem F914_1_V_of_lt (h : HypF98 T V L V₁ Vp H) (hb : 3 < F8.b T V L H) :
    IsElemAbelian 2 (conjClosure (conjClosure V H) L) := by
  have hyp := h.amalgamHypV
  have hV := h.V_ne_bot
  have hb5 : 5 ≤ F8.b T V L H := by
    obtain ⟨m, hm⟩ := h.three_le_b_and_odd.2
    omega
  refine HypF91.isElemAbelian_conjClosure_of_forall h.F911_2 fun k hk => ?_
  have hkG : k ∈ (L ⊔ T) ⊔ H := Subgroup.mem_sup_left (Subgroup.mem_sup_left hk)
  set k' : ↥((L ⊔ T) ⊔ H) := ⟨k, hkG⟩ with hk'
  have hk0 : k' • F8.γ₀ T L H = F8.γ₀ T L H := smul_γ₀_of_mem hyp.le₁ (Subgroup.mem_sup_left hk)
  have hnb : k' • F8.γ₁ T L H ∈ nbrs (F8.γ₀ T L H) := by
    have := (smul_adj k').mpr (adj_γ₀_γ₁ (G₀ := (L ⊔ T) ⊔ H) (G₁ := L ⊔ T) (G₂ := H))
    rwa [hk0] at this
  have hdist : CosetGeom.dist (F8.γ₁ T L H) (k' • F8.γ₁ T L H) + 2 < F8.b T V L H := by
    have t := dist_triangle hyp.gen (F8.γ₁ T L H) (F8.γ₀ T L H) (k' • F8.γ₁ T L H)
    have d1 : CosetGeom.dist (F8.γ₁ T L H) (F8.γ₀ T L H) = 1 := by
      rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr adj_γ₀_γ₁
    have d2 : CosetGeom.dist (F8.γ₀ T L H) (k' • F8.γ₁ T L H) = 1 :=
      dist_eq_one_iff_adj.mpr hnb
    omega
  have hcomm := commutator_Vv_Vv_eq_bot_of_mem_Γ1 hyp hV (β := F8.γ₁ T L H)
    (β' := k' • F8.γ₁ T L H) ⟨_, rfl⟩ (by rw [smul_γ₁]; exact ⟨_, rfl⟩) hdist
  have e1 : Vv V (F8.γ₁ T L H) = conjClosure V H := (h.toHypF91.conjClosure_eq_Vv_γ₁).symm
  have e2 : Vv V (k' • F8.γ₁ T L H) = conjSub k (conjClosure V H) := by
    rw [Vv_smul hyp.normalizes, e1]
  rw [e1, e2] at hcomm
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm

theorem F914_1_V_of_eq (h : HypF98 T V L V₁ Vp H) (hb : F8.b T V L H = 3) :
    ¬ ∀ x ∈ conjClosure (conjClosure V H) L, ∀ y ∈ conjClosure (conjClosure V H) L,
      x * y = y * x := by
  intro hab
  obtain ⟨l, hl, v, hv, u, hu, hne⟩ := h.exists_noncomm_of_b_eq_three hb
  refine hne (hab v (le_conjClosure _ L hv) u ?_)
  exact HypF91.conjSub_le_conjClosure hl
    (conjSub_mono l (conjClosure_mono h.Vp_le_V le_rfl) hu)

theorem F914_1_of_lt (h : HypF98 T V L V₁ Vp H) (hb : 3 < F8.b T V L H) :
    IsElemAbelian 2 (conjClosure (conjClosure Vp H) L) :=
  isElemAbelian_mono (h.F914_1_V_of_lt hb)
    (conjClosure_mono (conjClosure_mono h.Vp_le_V le_rfl) le_rfl)

theorem F914_1_of_eq (h : HypF98 T V L V₁ Vp H) (hb : F8.b T V L H = 3)
    (hVU : V ≤ conjClosure Vp H) :
    ¬ ∀ x ∈ conjClosure (conjClosure Vp H) L, ∀ y ∈ conjClosure (conjClosure Vp H) L,
      x * y = y * x := by
  intro hab
  obtain ⟨l, hl, v, hv, u, hu, hne⟩ := h.exists_noncomm_of_b_eq_three hb
  have hVH : conjClosure V H ≤ conjClosure Vp H :=
    conjClosure_le fun k hk z hz =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure Vp H hk) z).mp (hVU hz)
  exact hne (hab v (le_conjClosure _ L (hVH hv)) u (HypF91.conjSub_le_conjClosure hl hu))

theorem F914_1 (h : HypF98 T V L V₁ Vp H) (hVU : V ≤ conjClosure Vp H) :
    (∀ x ∈ conjClosure (conjClosure Vp H) L, ∀ y ∈ conjClosure (conjClosure Vp H) L,
      x * y = y * x) ↔ 3 < F8.b T V L H := by
  constructor
  · intro hab
    by_contra hnot
    have hb3 := h.three_le_b_and_odd.1
    exact h.F914_1_of_eq (by omega) hVU hab
  · intro hb x hx y hy
    exact isElemAbelian_comm (h.F914_1_of_lt hb) hx hy

end HypF98

end Fin

end CFSG.Quasithin
