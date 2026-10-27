module

public import CFSG.Monster.B.TwoA.Fischer.FullIntertwinerFiber
public import CFSG.Monster.B.Fischer.InducedEncoding

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.Mog22
open scoped IsMulCommutative

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

variable (act lab Y) in
structure IsCliqueIntertwiner
    (C : Set V)
    [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] (x : V) (η : C ≃ X₀)
    (φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀) (α : setStab act lab Y C →* F₀)
    (Φ : Y ≃ CFSG.Monster.B.Fischer.Y) : Prop where
  equivariant : ∀ (f : setStab act lab Y C) (v w : Y), (w : V) = act (f : S) v →
    Φ w = α f • Φ v
  clique : ∀ (z : C) (v : Y), (v : V) = z → Φ v = Sum.inl (η z)
  omega : ∀ (r : Subgroup.closure (lab '' C)) (v : Y), (v : V) = act (r : S) x →
    Φ v = Sum.inr (Sum.inl (φ (Additive.ofMul r)))
  fiber : ∀ T : Finset C, Subtype.val '' (T : Set C) ∈ cliqueBlocks lab C →
    Φ '' {v : Y | (v : V) ∈ hexadFiber lab Y C (Subtype.val '' (T : Set C))} =
      {y | ∃ z, y = Sum.inr (Sum.inr z) ∧ hexadOf z = T.image fun z => (η z : Fin 24)}

variable (act lab Y) in
open _root_.Classical in
@[expose] def intertwinerFun
    (C : Set V) [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
    (x : V) (η : C ≃ X₀) (φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀)
    (α : setStab act lab Y C →* F₀) (y₀ : V) (P₀ : CFSG.Monster.B.Fischer.Y) (v : V) :
    CFSG.Monster.B.Fischer.Y :=
  if hv : v ∈ C then Sum.inl (η ⟨v, hv⟩)
  else if h : ∃ r : Subgroup.closure (lab '' C), act (r : S) x = v then
    Sum.inr (Sum.inl (φ (Additive.ofMul h.choose)))
  else orbitTransport (act.comp (setStab act lab Y C).subtype)
    ((MulAction.toPermHom F₀ CFSG.Monster.B.Fischer.Y).comp α) y₀ P₀ v

theorem intertwinerFun_clique
    {C : Set V} [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
    {x : V} {η : C ≃ X₀} {φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀}
    {α : setStab act lab Y C →* F₀} {y₀ : V} {P₀ : CFSG.Monster.B.Fischer.Y} (z : C) :
    intertwinerFun act lab Y C x η φ α y₀ P₀ (z : V) = Sum.inl (η z) := by
  rw [intertwinerFun, dite_eq_left z.2]

namespace FullIntertwinerHyp

variable {C : Set V} [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] {x : V}
  {η : C ≃ X₀}
  {θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
    CFSG.Blueprint.NativeSporadic.M22}
  {φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀} {α : setStab act lab Y C →* F₀}
  (H : FullIntertwinerHyp act lab Y C x η θ φ α)
include H

section Fiber

variable {T₀ : Finset C} (hT₀ : T₀.image (fun z => (η z : Fin 24)) = B₀)
include hT₀

section Base

variable {y₀ : V} (hy₀ : y₀ ∈ hexadFiber lab Y C (Subtype.val '' (T₀ : Set C)))
include hy₀

theorem intertwiner_fiber_eq {Φ' : Y ≃ CFSG.Monster.B.Fischer.Y}
    (hΦ' : IsCliqueIntertwiner act lab Y C x η φ α Φ') {q' : Q₀}
    (hq' : Φ' ⟨y₀, hy₀.1⟩ = Sum.inr (Sum.inr (zMk 1 q'))) (v : Y)
    (hv : (v : V) ∈ hexadFiber lab Y C (Subtype.val '' (T₀ : Set C))) :
    Φ' v = Sum.inr (Sum.inr (zMk 1 (q' + fibCoord act φ y₀ v))) := by
  obtain ⟨s, hs⟩ := H.exists_closure_act_eq_fiber hT₀ hy₀ hv
  rw [hΦ'.equivariant ⟨s, H.mem_setStab s⟩ ⟨y₀, hy₀.1⟩ v hs.symm, hq',
    H.alpha_closure s _ rfl, wF_smul_zMk_one, H.fibCoord_spec hT₀ hy₀ s hs]

theorem isAffOrigin_of_intertwiner {Φ' : Y ≃ CFSG.Monster.B.Fischer.Y}
    (hΦ' : IsCliqueIntertwiner act lab Y C x η φ α Φ') {q' : Q₀}
    (hq' : Φ' ⟨y₀, hy₀.1⟩ = Sum.inr (Sum.inr (zMk 1 q'))) :
    IsAffOrigin act lab Y θ φ x y₀ (Subtype.val '' (T₀ : Set C)) q' := by
  intro k hKB hkx v hv
  have hkv := (H.act_mem_fiber_iff ((H.mem_KB_iff_image_block hT₀).1 hKB) v).2 hv
  have h1 := H.intertwiner_fiber_eq hT₀ hy₀ hΦ' hq' ⟨v, hv.1⟩ hv
  have h2 := H.intertwiner_fiber_eq hT₀ hy₀ hΦ' hq' ⟨act (k : S) v, hkv.1⟩ hkv
  have h3 := hΦ'.equivariant k ⟨v, hv.1⟩ ⟨act (k : S) v, hkv.1⟩ rfl
  rw [h2, h1, H.alpha_fix k hkx, kF_smul_zMk_one hKB] at h3
  have h4 := zMk_one_injective (Sum.inr_injective (Sum.inr_injective h3))
  rw [add_comm q', add_comm q'] at h4
  exact h4

section Origin

variable {t : Q₀} (ht : IsAffOrigin act lab Y θ φ x y₀ (Subtype.val '' (T₀ : Set C)) t)
include ht

omit hT₀ hy₀ ht in
theorem intertwinerFun_omega (r : Subgroup.closure (lab '' C)) :
    intertwinerFun act lab Y C x η φ α y₀ (Sum.inr (Sum.inr (zMk 1 t))) (act (r : S) x) =
      Sum.inr (Sum.inl (φ (Additive.ofMul r))) := by
  have hnot : act (r : S) x ∉ C := (H.act_mem_omega r).2.1
  have hex : ∃ r' : Subgroup.closure (lab '' C), act (r' : S) x = act (r : S) x := ⟨r, rfl⟩
  rw [intertwinerFun, dite_eq_right hnot, dite_eq_left hex, H.eq_of_act_eq hex.choose_spec]

theorem intertwinerFun_fiber (f : setStab act lab Y C) :
    intertwinerFun act lab Y C x η φ α y₀ (Sum.inr (Sum.inr (zMk 1 t))) (act (f : S) y₀) =
      α f • (Sum.inr (Sum.inr (zMk 1 t)) : CFSG.Monster.B.Fischer.Y) := by
  have hnot : act (f : S) y₀ ∉ C := H.act_not_mem_clique hy₀ f
  have hnex : ¬∃ r : Subgroup.closure (lab '' C), act (r : S) x = act (f : S) y₀ :=
    fun ⟨r, hr⟩ => H.act_ne_act_omega hT₀ hy₀ f r hr
  rw [intertwinerFun, dite_eq_right hnot, dite_eq_right hnex]
  exact orbitTransport_apply (fun g hg => (H.act_fix_iff hT₀ hy₀ ht g).1 hg) f

theorem intertwinerFun_base :
    intertwinerFun act lab Y C x η φ α y₀ (Sum.inr (Sum.inr (zMk 1 t))) y₀ =
      Sum.inr (Sum.inr (zMk 1 t)) := by
  have h := H.intertwinerFun_fiber hT₀ hy₀ ht 1
  rwa [Subgroup.coe_one, map_one, Equiv.Perm.one_apply, map_one, one_smul] at h

theorem intertwinerFun_injective : Function.Injective fun v : Y =>
    intertwinerFun act lab Y C x η φ α y₀ (Sum.inr (Sum.inr (zMk 1 t))) v := by
  have hZ : ∀ f : setStab act lab Y C, ∃ z, intertwinerFun act lab Y C x η φ α y₀
      (Sum.inr (Sum.inr (zMk 1 t))) (act (f : S) y₀) = Sum.inr (Sum.inr z) :=
    fun f => ⟨_, (H.intertwinerFun_fiber hT₀ hy₀ ht f).trans (smul_inr_inr_eq _ _)⟩
  intro v w h
  simp only at h
  apply Subtype.ext
  rcases H.regions hT₀ hy₀ v.2 with ⟨z, hz⟩ | ⟨r, hr⟩ | ⟨f, hf⟩ <;>
    rcases H.regions hT₀ hy₀ w.2 with ⟨z', hz'⟩ | ⟨r', hr'⟩ | ⟨f', hf'⟩
  · rw [← hz, ← hz', intertwinerFun_clique, intertwinerFun_clique] at h
    rw [← hz, ← hz', η.injective (Sum.inl_injective h)]
  · rw [← hz, ← hr', intertwinerFun_clique, H.intertwinerFun_omega] at h
    exact absurd h Sum.inl_ne_inr
  · obtain ⟨z₁, hz₁⟩ := hZ f'
    rw [← hz, ← hf', intertwinerFun_clique, hz₁] at h
    exact absurd h Sum.inl_ne_inr
  · rw [← hr, ← hz', intertwinerFun_clique, H.intertwinerFun_omega] at h
    exact absurd h Sum.inr_ne_inl
  · rw [← hr, ← hr', H.intertwinerFun_omega, H.intertwinerFun_omega] at h
    have hrr : r = r' :=
      Additive.ofMul.injective (φ.injective (Sum.inl_injective (Sum.inr_injective h)))
    rw [← hr, ← hr', hrr]
  · obtain ⟨z₁, hz₁⟩ := hZ f'
    rw [← hr, ← hf', H.intertwinerFun_omega, hz₁] at h
    exact absurd (Sum.inr_injective h) Sum.inl_ne_inr
  · obtain ⟨z₁, hz₁⟩ := hZ f
    rw [← hf, ← hz', intertwinerFun_clique, hz₁] at h
    exact absurd h Sum.inr_ne_inl
  · obtain ⟨z₁, hz₁⟩ := hZ f
    rw [← hf, ← hr', H.intertwinerFun_omega, hz₁] at h
    exact absurd (Sum.inr_injective h) Sum.inr_ne_inl
  · rw [← hf, ← hf', H.intertwinerFun_fiber hT₀ hy₀ ht, H.intertwinerFun_fiber hT₀ hy₀ ht] at h
    rw [← hf, ← hf']
    exact act_eq_of_orbit_eq (a := act.comp (setStab act lab Y C).subtype)
      (b := (MulAction.toPermHom F₀ CFSG.Monster.B.Fischer.Y).comp α) (p₀ := y₀)
      (p₀' := Sum.inr (Sum.inr (zMk 1 t))) (fun g hg => (H.act_fix_iff hT₀ hy₀ ht g).2 hg) h

end Origin

end Base

end Fiber

theorem exists_intertwiner
    (hconj : ∀ (f : setStab act lab Y C)
      (r : Subgroup.closure (lab '' C)) (h : (f : S) * r * (f : S)⁻¹ ∈ Subgroup.closure (lab '' C)),
      φ (Additive.ofMul ⟨(f : S) * r * (f : S)⁻¹, h⟩) = rhoW (θ f) (φ (Additive.ofMul r))) :
    ∃ Φ : Y ≃ CFSG.Monster.B.Fischer.Y,
    IsCliqueIntertwiner act lab Y C x η φ α Φ ∧
    (∀ v : Y, (v : V) = x → Φ v = o) ∧
    (∀ T₀ : Finset C, T₀.image (fun z => (η z : Fin 24)) = B₀ →
      (∀ v : Y, (v : V) ∈ hexadFiber lab Y C (Subtype.val '' (T₀ : Set C)) →
        ∃ q : Q₀, Φ v = Sum.inr (Sum.inr (zMk 1 q))) ∧
      (∀ (r : Subgroup.closure (lab '' C)) (v w : Y) (q : Q₀),
        (v : V) ∈ hexadFiber lab Y C (Subtype.val '' (T₀ : Set C)) →
        (w : V) = act (r : S) v → Φ v = Sum.inr (Sum.inr (zMk 1 q)) →
        Φ w = Sum.inr (Sum.inr (zMk 1 (q + U₀.mkQ (φ (Additive.ofMul r)))))) ∧
      ∀ (k : setStab act lab Y C) (hk : θ k ∈ KB) (v w : Y) (q : Q₀), act (k : S) x = x →
        (v : V) ∈ hexadFiber lab Y C (Subtype.val '' (T₀ : Set C)) →
        (w : V) = act (k : S) v → Φ v = Sum.inr (Sum.inr (zMk 1 q)) →
        Φ w = Sum.inr (Sum.inr (zMk 1 (affA ⟨θ k, hk⟩ q)))) ∧
    ∀ Φ' : Y ≃ CFSG.Monster.B.Fischer.Y, IsCliqueIntertwiner act lab Y C x η φ α Φ' →
      Φ' = Φ := by
  classical
  obtain ⟨T₀, hT₀⟩ := H.exists_T₀
  have hB := H.block_mem hT₀
  obtain ⟨y₀, hy₀⟩ : (hexadFiber lab Y C (Subtype.val '' (T₀ : Set C))).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by
      rw [(H.slice.hexadFiber_of_mem_cliqueBlocks H.clique hB).1]; norm_num)
  obtain ⟨t, ht⟩ := H.exists_isAffOrigin hT₀ hy₀ hconj
  have : Finite CFSG.Monster.B.Fischer.Y :=
    Nat.finite_of_card_ne_zero (by rw [natCard_Y]; norm_num)
  have hbij := (H.intertwinerFun_injective hT₀ hy₀ ht).bijective_of_nat_card_le (by
    rw [natCard_Y, Nat.card_coe_set_eq, H.slice.ncard])
  set Φ : Y ≃ CFSG.Monster.B.Fischer.Y := Equiv.ofBijective _ hbij with hΦ
  have hΦv : ∀ v : Y, Φ v =
      intertwinerFun act lab Y C x η φ α y₀ (Sum.inr (Sum.inr (zMk 1 t))) v := fun _ => rfl
  have hcl : ∀ (z : C) (v : Y), (v : V) = z → Φ v = Sum.inl (η z) := by
    intro z v hv
    rw [hΦv, hv, intertwinerFun_clique]
  have hom : ∀ (r : Subgroup.closure (lab '' C)) (v : Y), (v : V) = act (r : S) x →
      Φ v = Sum.inr (Sum.inl (φ (Additive.ofMul r))) := by
    intro r v hv
    rw [hΦv, hv, H.intertwinerFun_omega]
  have hfib : ∀ (f : setStab act lab Y C) (v : Y), (v : V) = act (f : S) y₀ →
      Φ v = α f • (Sum.inr (Sum.inr (zMk 1 t)) : CFSG.Monster.B.Fischer.Y) := by
    intro f v hv
    rw [hΦv, hv, H.intertwinerFun_fiber hT₀ hy₀ ht]
  have heq : ∀ (f : setStab act lab Y C) (v w : Y), (w : V) = act (f : S) v →
      Φ w = α f • Φ v := by
    intro f v w hw
    rcases H.regions hT₀ hy₀ v.2 with ⟨z, hz⟩ | ⟨s, hs⟩ | ⟨g, hg⟩
    · have hwz : (w : V) = (setStabPerm act lab Y C f z : V) := by
        rw [hw, ← hz]
        rfl
      rw [hcl _ w hwz, hcl z v hz.symm, smul_inl_eq, H.alpha_right]
      congr 1
      apply Subtype.ext
      rw [psiX_apply, H.perm]
    · obtain ⟨r, k, hf, hk⟩ := H.exists_eq_mul_fix f
      have hkC : ∀ z ∈ C, act (k : S) z ∈ C := fun z hz => (k.2.2 z).2 hz
      have hconj₁ : (k : S) * s * (k : S)⁻¹ ∈ Subgroup.closure (lab '' C) :=
        conj_mem_closure H.slice.lab_act hkC s s.2
      have hk' : act (k : S)⁻¹ x = x := by
        conv_lhs => rw [← hk]
        exact act_inv_act _ _
      have hw' : (w : V) = act ((r * ⟨(k : S) * s * (k : S)⁻¹, hconj₁⟩ :
          Subgroup.closure (lab '' C)) : S) x := by
        rw [hw, ← hs, hf, Subgroup.coe_mul]
        simp only [map_mul, Equiv.Perm.mul_apply, hk']
      rw [hom _ w hw', hom s v hs.symm, H.alpha r f k hf hk, wF_mul_kF, smul_inr_inl_eq,
        ofMul_mul, map_add, hconj k s hconj₁]
      rfl
    · have hw' : (w : V) = act ((f * g : setStab act lab Y C) : S) y₀ := by
        rw [hw, ← hg, Subgroup.coe_mul, map_mul, Equiv.Perm.mul_apply]
      rw [hfib _ w hw', hfib g v hg.symm, map_mul, mul_smul]
  have hhex : ∀ f : setStab act lab Y C, ∃ z,
      α f • (Sum.inr (Sum.inr (zMk 1 t)) : CFSG.Monster.B.Fischer.Y) = Sum.inr (Sum.inr z) ∧
        hexadOf z = (T₀.image (setStabPerm act lab Y C f)).image (fun z => (η z : Fin 24)) := by
    intro f
    refine ⟨_, smul_inr_inr_eq _ _, ?_⟩
    rw [hexadOf_zW, zK_mk, hexadOf_zMk, mul_one, H.alpha_right, H.map_B₀_eq hT₀ f]
  have hfiber : ∀ T : Finset C, Subtype.val '' (T : Set C) ∈ cliqueBlocks lab C →
      Φ '' {v : Y | (v : V) ∈ hexadFiber lab Y C (Subtype.val '' (T : Set C))} =
        {y | ∃ z, y = Sum.inr (Sum.inr z) ∧ hexadOf z = T.image fun z => (η z : Fin 24)} := by
    intro T hT
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨f, hf, hfv⟩ := H.exists_act_eq_of_mem_hexadFiber hB hT hy₀ hv
      obtain ⟨z, hz1, hz2⟩ := hhex ⟨f, hf⟩
      refine ⟨z, by rw [hfib ⟨f, hf⟩ v hfv.symm, hz1], ?_⟩
      have hfv' : act f y₀ ∈ hexadFiber lab Y C (Subtype.val '' (T : Set C)) := by
        rw [hfv]
        exact hv
      have hfB := eq_of_mem_hexadFiber (H.act_mem_image_fiber hy₀ ⟨f, hf⟩) hfv'
      rw [image_val_image] at hfB
      rw [hz2, Finset.coe_injective (Set.image_injective.2 Subtype.val_injective hfB)]
    · rintro ⟨z, rfl, hz⟩
      obtain ⟨v, hv⟩ := Φ.surjective (Sum.inr (Sum.inr z))
      refine ⟨v, ?_, hv⟩
      rcases H.regions hT₀ hy₀ v.2 with ⟨z', hz'⟩ | ⟨r, hr⟩ | ⟨f, hf⟩
      · rw [hcl z' v hz'.symm] at hv
        exact absurd hv Sum.inl_ne_inr
      · rw [hom r v hr.symm] at hv
        exact absurd (Sum.inr_injective hv) Sum.inl_ne_inr
      · rw [hfib f v hf.symm] at hv
        obtain ⟨z₁, hz1, hz2⟩ := hhex f
        rw [hz1] at hv
        rw [Sum.inr_injective (Sum.inr_injective hv), hz] at hz2
        have hTT := Finset.image_injective
          (fun a b h => η.injective (Subtype.ext h) : Function.Injective
            fun z : C => (η z : Fin 24)) hz2
        have hmem := H.act_mem_image_fiber hy₀ f
        rw [image_val_image, ← hTT, hf] at hmem
        exact hmem
  have hI : IsCliqueIntertwiner act lab Y C x η φ α Φ := ⟨heq, hcl, hom, hfiber⟩
  refine ⟨Φ, hI, fun v hv => ?_, fun T₀' hT₀' => ?_, fun Φ' hΦ' => ?_⟩
  · rw [hom 1 v (by rw [hv, Subgroup.coe_one, map_one, Equiv.Perm.one_apply]), ofMul_one,
      map_zero]
    rfl
  · have hB' := H.block_mem hT₀'
    refine ⟨fun v hv => ?_, fun r v w q hv hw hq => ?_, fun k hk v w q hkx hv hw hq => ?_⟩
    · have hmem : Φ v ∈ Φ '' {v : Y | (v : V) ∈
          hexadFiber lab Y C (Subtype.val '' (T₀' : Set C))} := ⟨v, hv, rfl⟩
      rw [hfiber T₀' hB'] at hmem
      obtain ⟨z, hz, hzB⟩ := hmem
      rw [hT₀'] at hzB
      obtain ⟨q, rfl⟩ := exists_eq_zMk_one hzB
      exact ⟨q, hz⟩
    · rw [heq ⟨r, H.mem_setStab r⟩ v w hw, hq, H.alpha_closure r _ rfl, wF_smul_zMk_one]
    · rw [heq k v w hw, hq, H.alpha_fix k hkx, kF_smul_zMk_one hk]
  · obtain ⟨q', hq'⟩ : ∃ q', Φ' ⟨y₀, hy₀.1⟩ = Sum.inr (Sum.inr (zMk 1 q')) := by
      have hmem : Φ' ⟨y₀, hy₀.1⟩ ∈ Φ' '' {v : Y | (v : V) ∈
          hexadFiber lab Y C (Subtype.val '' (T₀ : Set C))} := ⟨_, hy₀, rfl⟩
      rw [hΦ'.fiber T₀ hB] at hmem
      obtain ⟨z, hz, hzB⟩ := hmem
      rw [hT₀] at hzB
      obtain ⟨q, rfl⟩ := exists_eq_zMk_one hzB
      exact ⟨q, hz⟩
    have hq't : q' = t :=
      H.isAffOrigin_unique hT₀ hy₀ hconj (H.isAffOrigin_of_intertwiner hT₀ hy₀ hΦ' hq') ht
    refine Equiv.ext fun v => ?_
    rcases H.regions hT₀ hy₀ v.2 with ⟨z, hz⟩ | ⟨r, hr⟩ | ⟨f, hf⟩
    · rw [hΦ'.clique z v hz.symm, hcl z v hz.symm]
    · rw [hΦ'.omega r v hr.symm, hom r v hr.symm]
    · rw [hΦ'.equivariant f ⟨y₀, hy₀.1⟩ v hf.symm, hq', hq't, hfib f v hf.symm]

end FullIntertwinerHyp

namespace IsFischerSlice

theorem full_clique_action_intertwiner
    (hS : IsFischerSlice act lab Y) {C : Set V}
    (hC : IsSliceMaxClique lab Y C) [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
    {x : V} (hx : x ∈ hexadFiber lab Y C ∅) {η : C ≃ X₀}
    {θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
      CFSG.Blueprint.NativeSporadic.M22}
    (hη : ∀ T : Finset C, Subtype.val '' (T : Set C) ∈ cliqueBlocks lab C ↔
      T.image (fun z => (η z : Fin 24)) ∈ ℬ₀)
    (hθ : ∀ (f : setStab act lab Y C) (z : C),
      (η (setStabPerm act lab Y C f z) : Fin 24) = psiHom (θ f) (η z))
    {φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀}
    (hφ : ∀ z : C, φ (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η z)))
    (hφθ : ∀ (f : setStab act lab Y C) (r : Subgroup.closure (lab '' C))
      (h : (f : S) * r * (f : S)⁻¹ ∈ Subgroup.closure (lab '' C)),
      φ (Additive.ofMul ⟨(f : S) * r * (f : S)⁻¹, h⟩) = rhoW (θ f) (φ (Additive.ofMul r)))
    {α : setStab act lab Y C →* F₀}
    (hα : ∀ (r : Subgroup.closure (lab '' C)) (f k : setStab act lab Y C),
      (f : S) = r * k → act (k : S) x = x → α f = wF (φ (Additive.ofMul r)) * kF (θ k)) :
    ∃ Φ : Y ≃ CFSG.Monster.B.Fischer.Y,
      IsCliqueIntertwiner act lab Y C x η φ α Φ ∧
      (∀ v : Y, (v : V) = x → Φ v = o) ∧
      (∀ T₀ : Finset C, T₀.image (fun z => (η z : Fin 24)) = B₀ →
        (∀ v : Y, (v : V) ∈ hexadFiber lab Y C (Subtype.val '' (T₀ : Set C)) →
          ∃ q : Q₀, Φ v = Sum.inr (Sum.inr (zMk 1 q))) ∧
        (∀ (r : Subgroup.closure (lab '' C)) (v w : Y) (q : Q₀),
          (v : V) ∈ hexadFiber lab Y C (Subtype.val '' (T₀ : Set C)) →
          (w : V) = act (r : S) v → Φ v = Sum.inr (Sum.inr (zMk 1 q)) →
          Φ w = Sum.inr (Sum.inr (zMk 1 (q + U₀.mkQ (φ (Additive.ofMul r)))))) ∧
        ∀ (k : setStab act lab Y C) (hk : θ k ∈ KB) (v w : Y) (q : Q₀), act (k : S) x = x →
          (v : V) ∈ hexadFiber lab Y C (Subtype.val '' (T₀ : Set C)) →
          (w : V) = act (k : S) v → Φ v = Sum.inr (Sum.inr (zMk 1 q)) →
          Φ w = Sum.inr (Sum.inr (zMk 1 (affA ⟨θ k, hk⟩ q)))) ∧
      ∀ Φ' : Y ≃ CFSG.Monster.B.Fischer.Y, IsCliqueIntertwiner act lab Y C x η φ α Φ' →
        Φ' = Φ :=
  (FullIntertwinerHyp.mk hS hC hx hη hθ hφ hα).exists_intertwiner hφθ

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
