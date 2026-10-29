module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIFacts
public import CFSG.Monster.B.TwoA.Base.Subspaces

public section

namespace CFSG.Quasithin.H13.C1294

open Module

section Glue

variable {I : Type} [AddCommGroup I] [Module (ZMod 2) I]

theorem add_self_eq_zero_zmod2 (v : I) : v + v = 0 := by
  have h : (2 : ZMod 2) = 0 := rfl
  rw [← two_smul (ZMod 2) v, h, zero_smul]

theorem exists_glue {W C : Submodule (ZMod 2) I} (h : IsCompl W C) (a : W ≃ₗ[ZMod 2] W)
    (β : C ≃ₗ[ZMod 2] C) :
    ∃ g : I ≃ₗ[ZMod 2] I, (∀ w : W, g (w : I) = a w) ∧ (∀ c : C, g (c : I) = β c) := by
  refine ⟨(Submodule.prodEquivOfIsCompl W C h).symm.trans
    ((a.prodCongr β).trans (Submodule.prodEquivOfIsCompl W C h)), fun w => ?_, fun c => ?_⟩
  · simp [Submodule.prodEquivOfIsCompl_symm_apply_left]
  · simp [Submodule.prodEquivOfIsCompl_symm_apply_right]

theorem mem_stabS_of_restrict {W : Submodule (ZMod 2) I} {g : I ≃ₗ[ZMod 2] I}
    (a : W ≃ₗ[ZMod 2] W) (ha : ∀ w : W, g (w : I) = a w) : g ∈ stabS W := by
  show ∀ v, v ∈ W ↔ g v ∈ W
  intro v
  constructor
  · intro hv
    rw [show g v = ((a ⟨v, hv⟩ : W) : I) from ha ⟨v, hv⟩]
    exact (a ⟨v, hv⟩).2
  · intro hv
    have h2 : g ((a.symm ⟨g v, hv⟩ : W) : I) = g v := by
      rw [ha, LinearEquiv.apply_symm_apply]
    have h3 : ((a.symm ⟨g v, hv⟩ : W) : I) = v := g.injective h2
    rw [← h3]
    exact (a.symm ⟨g v, hv⟩).2

end Glue

section GLTwo

theorem eq_bot_of_normal_two_gl {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (M : Subgroup (V ≃ₗ[ZMod 2] V)) (h2 : IsPGroup 2 M)
    (hn : ∀ g : V ≃ₗ[ZMod 2] V, ∀ m ∈ M, g * m * g⁻¹ ∈ M) : M = ⊥ := by
  classical
  rcases subsingleton_or_nontrivial V with hV | hV
  · refine (Subgroup.eq_bot_iff_forall M).2 fun m _ => ?_
    exact (Subgroup.mem_bot).2 (LinearEquiv.ext fun v => Subsingleton.elim _ _)
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  haveI : Fintype V := Fintype.ofFinite V
  have hfd : 0 < finrank (ZMod 2) V := Module.finrank_pos
  have hNat : Nat.card V = 2 ^ finrank (ZMod 2) V := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := V)]
    rfl
  have hdvd : 2 ∣ Nat.card V := by
    rw [hNat]
    exact dvd_pow_self 2 hfd.ne'
  have hmod := IsPGroup.card_modEq_card_fixedPoints h2 V
  have hF2 : Nat.card (MulAction.fixedPoints ↥M V) % 2 = 0 := by
    have h1 : Nat.card V % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨v, hv, hv0⟩ : ∃ v ∈ MulAction.fixedPoints ↥M V, v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hzero : (0 : V) ∈ MulAction.fixedPoints ↥M V := by
      show ∀ m : ↥M, m • (0 : V) = 0
      intro m
      exact map_zero (m : V ≃ₗ[ZMod 2] V)
    have hF : MulAction.fixedPoints ↥M V = {0} :=
      Set.eq_singleton_iff_unique_mem.2 ⟨hzero, fun x hx => hcon x hx⟩
    rw [hF, Nat.card_coe_set_eq, Set.ncard_singleton] at hF2
    exact absurd hF2 (by norm_num)
  have htrans : ∀ w : V, w ≠ 0 → ∃ g : V ≃ₗ[ZMod 2] V, g v = w := by
    intro w hw
    have hrank : finrank (ZMod 2) (Submodule.span (ZMod 2) {v}) =
        finrank (ZMod 2) (Submodule.span (ZMod 2) {w}) := by
      rw [finrank_span_singleton hv0, finrank_span_singleton hw]
    obtain ⟨g, hg⟩ := CFSG.Monster.B.TwoA.exists_linearEquiv_map_eq hrank
    refine ⟨g, ?_⟩
    have hmem : g v ∈ Submodule.span (ZMod 2) {w} := by
      rw [← hg]
      exact Submodule.mem_map_of_mem (Submodule.subset_span rfl)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · exact absurd (g.map_eq_zero_iff.1 (by rw [← hc, zero_smul])) hv0
    · rw [← hc, one_smul]
  refine (Subgroup.eq_bot_iff_forall M).2 fun m hm => ?_
  refine (Subgroup.mem_bot).2 (LinearEquiv.ext fun w => ?_)
  by_cases hw : w = 0
  · subst hw
    rw [map_zero, map_zero]
  · obtain ⟨g, rfl⟩ := htrans w hw
    have hk : g⁻¹ * m * g⁻¹⁻¹ ∈ M := hn g⁻¹ m hm
    have hv' : ∀ k : ↥M, k • v = v := hv
    have hfix : ((g⁻¹ * m * g⁻¹⁻¹ : V ≃ₗ[ZMod 2] V)) v = v := hv' ⟨_, hk⟩
    have h1 : g.symm (m (g v)) = v := by
      have e : (g⁻¹ * m * g⁻¹⁻¹ : V ≃ₗ[ZMod 2] V) v = g.symm (m (g v)) := by
        simp [LinearEquiv.mul_apply]
      rw [← e]
      exact hfix
    show m (g v) = g v
    calc m (g v) = g (g.symm (m (g v))) := (g.apply_symm_apply _).symm
      _ = g v := by rw [h1]

end GLTwo

section Restrict

variable {I : Type} [AddCommGroup I] [Module (ZMod 2) I]

theorem map_eq_of_mem_stabS {W : Submodule (ZMod 2) I} {g : I ≃ₗ[ZMod 2] I} (hg : g ∈ stabS W) :
    W.map (g : I →ₗ[ZMod 2] I) = W := by
  have hg' : ∀ v, v ∈ W ↔ g v ∈ W := hg
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (hg' x).1 hx
  · intro y hy
    exact ⟨g.symm y, (hg' (g.symm y)).2 (by simpa using hy), by simp⟩

@[expose] def restrictEquiv {W : Submodule (ZMod 2) I} (g : stabS W) : W ≃ₗ[ZMod 2] W :=
  LinearEquiv.ofSubmodules (g : I ≃ₗ[ZMod 2] I) W W (map_eq_of_mem_stabS g.2)

@[expose] def restrictHom (W : Submodule (ZMod 2) I) : stabS W →* (W ≃ₗ[ZMod 2] W) where
  toFun := restrictEquiv
  map_one' := LinearEquiv.ext fun w => Subtype.ext rfl
  map_mul' g h := LinearEquiv.ext fun w => Subtype.ext rfl

@[expose] def quotEquiv {W : Submodule (ZMod 2) I} (g : stabS W) : (I ⧸ W) ≃ₗ[ZMod 2] (I ⧸ W) :=
  Submodule.Quotient.equiv W W (g : I ≃ₗ[ZMod 2] I) (map_eq_of_mem_stabS g.2)

@[expose] def quotHom (W : Submodule (ZMod 2) I) : stabS W →* ((I ⧸ W) ≃ₗ[ZMod 2] (I ⧸ W)) where
  toFun := quotEquiv
  map_one' := LinearEquiv.ext fun x => Submodule.Quotient.induction_on _ x fun y => rfl
  map_mul' g h := LinearEquiv.ext fun x => Submodule.Quotient.induction_on _ x fun y => rfl

theorem quotHom_apply {W : Submodule (ZMod 2) I} (g : stabS W) (y : I) :
    quotHom W g (Submodule.Quotient.mk y) = Submodule.Quotient.mk ((g : I ≃ₗ[ZMod 2] I) y) :=
  rfl

end Restrict

section Unipotent

variable {I : Type} [AddCommGroup I] [Module (ZMod 2) I] [Module.Finite (ZMod 2) I]

@[expose] def unipRad (W : Submodule (ZMod 2) I) : Subgroup (I ≃ₗ[ZMod 2] I) where
  carrier := {g | (∀ w ∈ W, g w = w) ∧ ∀ x, g x - x ∈ W}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun w hw => ?_, fun x => ?_⟩
    · show a (b w) = w
      rw [hb1 w hw, ha1 w hw]
    · show a (b x) - x ∈ W
      have e : a (b x) - x = (a (b x) - b x) + (b x - x) := by abel
      rw [e]
      exact W.add_mem (ha2 (b x)) (hb2 x)
  one_mem' := ⟨fun w _ => rfl, fun x => by simp⟩
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨fun w hw => ?_, fun x => ?_⟩
    · show a.symm w = w
      calc a.symm w = a.symm (a w) := by rw [ha1 w hw]
        _ = w := a.symm_apply_apply w
    · have h := ha2 (a.symm x)
      rw [LinearEquiv.apply_symm_apply] at h
      show a.symm x - x ∈ W
      have h' := W.neg_mem h
      rw [neg_sub] at h'
      simpa using h'

theorem unipRad_le_stabS (W : Submodule (ZMod 2) I) : unipRad W ≤ stabS W := by
  intro g hg
  show ∀ v, v ∈ W ↔ g v ∈ W
  intro v
  constructor
  · intro hv
    rw [hg.1 v hv]
    exact hv
  · intro hv
    have h := W.sub_mem hv (hg.2 v)
    simpa using h

theorem unipRad_add_self_eq (W : Submodule (ZMod 2) I) (g : I ≃ₗ[ZMod 2] I) (hg : g ∈ unipRad W)
    (x : I) : g (g x) = x := by
  have hf : g x - x ∈ W := hg.2 x
  have hkf : g (g x - x) = g x - x := hg.1 _ hf
  rw [map_sub] at hkf
  have h0 : g (g x) - x = (g x - x) + (g x - x) := by
    have e : g (g x) - x = (g (g x) - g x) + (g x - x) := by abel
    rw [e, hkf]
  rw [add_self_eq_zero_zmod2, sub_eq_zero] at h0
  exact h0

theorem unipRad_normal (W : Submodule (ZMod 2) I) (h : stabS W) (g : I ≃ₗ[ZMod 2] I)
    (hg : g ∈ unipRad W) : (h : I ≃ₗ[ZMod 2] I) * g * (h : I ≃ₗ[ZMod 2] I)⁻¹ ∈ unipRad W := by
  have hh : ∀ v, v ∈ W ↔ (h : I ≃ₗ[ZMod 2] I) v ∈ W := h.2
  have hhinv : ∀ v, v ∈ W ↔ (h : I ≃ₗ[ZMod 2] I)⁻¹ v ∈ W := (stabS W).inv_mem h.2
  refine ⟨fun w hw => ?_, fun x => ?_⟩
  · show (h : I ≃ₗ[ZMod 2] I) (g ((h : I ≃ₗ[ZMod 2] I)⁻¹ w)) = w
    rw [hg.1 _ ((hhinv w).1 hw)]
    exact (h : I ≃ₗ[ZMod 2] I).apply_symm_apply w
  · show (h : I ≃ₗ[ZMod 2] I) (g ((h : I ≃ₗ[ZMod 2] I)⁻¹ x)) - x ∈ W
    have hy : (h : I ≃ₗ[ZMod 2] I) ((h : I ≃ₗ[ZMod 2] I)⁻¹ x) = x :=
      (h : I ≃ₗ[ZMod 2] I).apply_symm_apply x
    have hgy := hg.2 ((h : I ≃ₗ[ZMod 2] I)⁻¹ x)
    have hmem : (h : I ≃ₗ[ZMod 2] I) (g ((h : I ≃ₗ[ZMod 2] I)⁻¹ x) - (h : I ≃ₗ[ZMod 2] I)⁻¹ x) ∈ W := by
      have := (hh _).1 hgy
      exact this
    rw [map_sub] at hmem
    rwa [hy] at hmem

theorem unipRad_sq (W : Submodule (ZMod 2) I) (g : I ≃ₗ[ZMod 2] I) (hg : g ∈ unipRad W) :
    g ^ 2 = 1 := by
  refine LinearEquiv.ext fun x => ?_
  rw [pow_two, LinearEquiv.mul_apply]
  exact unipRad_add_self_eq W g hg x

theorem restrictHom_surjective (W : Submodule (ZMod 2) I) : Function.Surjective (restrictHom W) := by
  intro g
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  obtain ⟨G, hGW, -⟩ := exists_glue hC g (LinearEquiv.refl (ZMod 2) C)
  exact ⟨⟨G, mem_stabS_of_restrict g hGW⟩, LinearEquiv.ext fun w => Subtype.ext (hGW w)⟩

theorem quotHom_surjective (W : Submodule (ZMod 2) I) : Function.Surjective (quotHom W) := by
  intro b
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  let Q : (I ⧸ W) ≃ₗ[ZMod 2] C := Submodule.quotientEquivOfIsCompl W C hC
  have hQ : ∀ u : I ⧸ W, Submodule.Quotient.mk ((Q u : C) : I) = u := by
    intro u
    have h := Q.symm_apply_apply u
    rw [Submodule.quotientEquivOfIsCompl_symm_apply] at h
    exact h
  let β : C ≃ₗ[ZMod 2] C := (Q.symm.trans b).trans Q
  obtain ⟨G, hGW, hGC⟩ := exists_glue hC (LinearEquiv.refl (ZMod 2) W) β
  refine ⟨⟨G, mem_stabS_of_restrict (LinearEquiv.refl (ZMod 2) W) hGW⟩, ?_⟩
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective W x
  have hy : y ∈ W ⊔ C := by
    rw [hC.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.1 hy
  have hmk : (Submodule.Quotient.mk (w + c) : I ⧸ W) = Submodule.Quotient.mk c := by
    rw [Submodule.Quotient.eq]
    simpa using hw
  have hGc : G c = ((β ⟨c, hc⟩ : C) : I) := hGC ⟨c, hc⟩
  have hβ : Submodule.Quotient.mk ((β ⟨c, hc⟩ : C) : I) = b (Submodule.Quotient.mk c) := by
    have h1 : β ⟨c, hc⟩ = Q (b (Q.symm ⟨c, hc⟩)) := rfl
    rw [h1]
    have h2 : Q.symm ⟨c, hc⟩ = Submodule.Quotient.mk c := by
      rw [Submodule.quotientEquivOfIsCompl_symm_apply]
    rw [h2]
    exact hQ _
  rw [hmk, quotHom_apply, hGc]
  exact hβ

theorem isPGroup_two_map {H K : Type} [Group H] [Group K] (f : H →* K) (N : Subgroup H)
    (hN : ∀ n ∈ N, ∃ k : ℕ, n ^ 2 ^ k = 1) : IsPGroup 2 ↥(N.map f) := by
  intro y
  obtain ⟨n, hn, hy⟩ := Subgroup.mem_map.1 y.2
  obtain ⟨k, hk⟩ := hN n hn
  refine ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hy, ← map_pow, hk, map_one]

theorem le_unipRad_of_normal_two (W : Submodule (ZMod 2) I) (M : Subgroup (I ≃ₗ[ZMod 2] I))
    (hM : M ≤ stabS W) (hn : ∀ h ∈ stabS W, ∀ m ∈ M, h * m * h⁻¹ ∈ M) (h2 : IsPGroup 2 M) :
    M ≤ unipRad W := by
  classical
  let N : Subgroup (stabS W) := M.subgroupOf (stabS W)
  have hel : ∀ n ∈ N, ∃ k : ℕ, n ^ 2 ^ k = 1 := by
    intro n hn'
    obtain ⟨k, hk⟩ := h2 ⟨(n : I ≃ₗ[ZMod 2] I), Subgroup.mem_subgroupOf.1 hn'⟩
    refine ⟨k, Subtype.ext ?_⟩
    simpa using congrArg Subtype.val hk
  have hNn : ∀ h : stabS W, ∀ n ∈ N, h * n * h⁻¹ ∈ N := by
    intro h n hn'
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    simpa using hn (h : I ≃ₗ[ZMod 2] I) h.2 n hn'
  have hMr : (N.map (restrictHom W)) = ⊥ := by
    refine eq_bot_of_normal_two_gl _ (isPGroup_two_map (restrictHom W) N hel) ?_
    intro g x hx
    obtain ⟨n, hn', rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨h, rfl⟩ := restrictHom_surjective W g
    refine Subgroup.mem_map.2 ⟨h * n * h⁻¹, hNn h n hn', ?_⟩
    simp only [map_mul, map_inv]
  have hMq : (N.map (quotHom W)) = ⊥ := by
    refine eq_bot_of_normal_two_gl _ (isPGroup_two_map (quotHom W) N hel) ?_
    intro b x hx
    obtain ⟨n, hn', rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨h, rfl⟩ := quotHom_surjective W b
    refine Subgroup.mem_map.2 ⟨h * n * h⁻¹, hNn h n hn', ?_⟩
    simp only [map_mul, map_inv]
  intro m hm
  have hmN : (⟨m, hM hm⟩ : stabS W) ∈ N := Subgroup.mem_subgroupOf.2 hm
  have h1 : restrictHom W ⟨m, hM hm⟩ = 1 := by
    have : restrictHom W ⟨m, hM hm⟩ ∈ N.map (restrictHom W) := Subgroup.mem_map_of_mem _ hmN
    rw [hMr, Subgroup.mem_bot] at this
    exact this
  have h2' : quotHom W ⟨m, hM hm⟩ = 1 := by
    have : quotHom W ⟨m, hM hm⟩ ∈ N.map (quotHom W) := Subgroup.mem_map_of_mem _ hmN
    rw [hMq, Subgroup.mem_bot] at this
    exact this
  refine ⟨fun w hw => ?_, fun x => ?_⟩
  · have h := congrArg (fun f : (W ≃ₗ[ZMod 2] W) => ((f ⟨w, hw⟩ : W) : I)) h1
    exact h
  · have h3 : Submodule.Quotient.mk (m x) = (Submodule.Quotient.mk x : I ⧸ W) :=
      congrArg (fun f : ((I ⧸ W) ≃ₗ[ZMod 2] (I ⧸ W)) => f (Submodule.Quotient.mk x)) h2'
    exact (Submodule.Quotient.eq W).1 h3

theorem pCoreOf_two_stabS (W : Submodule (ZMod 2) I) :
    CFSG.Open.pCoreOf 2 (stabS W) = unipRad W := by
  apply le_antisymm
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hg
    let M : Subgroup (I ≃ₗ[ZMod 2] I) := (CFSG.pCore 2 ↥(stabS W)).map (stabS W).subtype
    have hMle : M ≤ stabS W := by
      intro x hx
      obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.1 hx
      exact y.2
    have hn : ∀ h ∈ stabS W, ∀ m ∈ M, h * m * h⁻¹ ∈ M := by
      intro h hh m hm
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hm
      refine Subgroup.mem_map.2 ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹, ?_, rfl⟩
      exact Subgroup.Normal.conj_mem inferInstance y hy ⟨h, hh⟩
    have h2 : IsPGroup 2 M := by
      intro m
      obtain ⟨y, hy, hym⟩ := Subgroup.mem_map.1 m.2
      obtain ⟨k', hk'⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥(stabS W)) ⟨y, hy⟩
      have key : ((y : stabS W) : I ≃ₗ[ZMod 2] I) ^ 2 ^ k' = 1 := by
        have := congrArg (fun z : ↥(CFSG.pCore 2 ↥(stabS W)) => ((z : stabS W) : I ≃ₗ[ZMod 2] I))
          hk'
        simpa using this
      refine ⟨k', Subtype.ext ?_⟩
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hym]
      exact key
    exact le_unipRad_of_normal_two W M hMle hn h2 (Subgroup.mem_map_of_mem _ hk)
  · intro g hg
    have hgH : g ∈ stabS W := unipRad_le_stabS W hg
    refine Subgroup.mem_map.2 ⟨⟨g, hgH⟩, ?_, rfl⟩
    let K : Subgroup (stabS W) := (unipRad W).subgroupOf (stabS W)
    have hKn : K.Normal := by
      refine ⟨fun k hk h => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      simpa using unipRad_normal W h (k : I ≃ₗ[ZMod 2] I) hk
    have hKp : IsPGroup 2 K := by
      intro k
      refine ⟨1, ?_⟩
      have hk : ((k : stabS W) : I ≃ₗ[ZMod 2] I) ∈ unipRad W := Subgroup.mem_subgroupOf.1 k.2
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
      exact unipRad_sq W _ hk
    have hle : K ≤ CFSG.pCore 2 ↥(stabS W) := le_sSup ⟨hKn, hKp⟩
    exact hle (Subgroup.mem_subgroupOf.2 hg)

end Unipotent

end CFSG.Quasithin.H13.C1294
