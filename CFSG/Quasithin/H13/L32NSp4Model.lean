module

public import CFSG.Quasithin.H13.L32NSp4Basis

public section

namespace CFSG.Quasithin.H13.Sp4Cert

open KGCert CFSG.ComponentClassification.PresentationLocal Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def cf (b : Module.Basis (Fin 4) (ZMod 2) V) (γ : V ≃ₗ[ZMod 2] V) :
    List ℕ :=
  colsOf4 ((phi4 b γ : GL (Fin 4) (ZMod 2)) : Mat4)

theorem validC4_cf (b : Module.Basis (Fin 4) (ZMod 2) V) (γ : V ≃ₗ[ZMod 2] V) :
    ValidC4 (cf b γ) := validC4_colsOf4 _

theorem decodeC4_cf (b : Module.Basis (Fin 4) (ZMod 2) V) (γ : V ≃ₗ[ZMod 2] V) :
    decodeC4 (cf b γ) = ((phi4 b γ : GL (Fin 4) (ZMod 2)) : Mat4) := decodeC4_colsOf4 _

theorem cf_injective (b : Module.Basis (Fin 4) (ZMod 2) V) : Function.Injective (cf b) := by
  intro γ δ h
  apply phi4_injective b
  apply Units.ext
  rw [← decodeC4_cf, ← decodeC4_cf, h]

theorem cf_mul (b : Module.Basis (Fin 4) (ZMod 2) V) (γ δ : V ≃ₗ[ZMod 2] V) :
    cf b (γ * δ) = mulC (cf b γ) (cf b δ) := by
  apply decodeC4_injOn (validC4_cf b _) (validC4_mulC (validC4_cf b γ) (validC4_cf b δ))
  rw [decodeC4_mulC (validC4_cf b γ).1 (validC4_cf b δ).1, decodeC4_cf, decodeC4_cf, decodeC4_cf,
    map_mul, Units.val_mul]

theorem cf_one (b : Module.Basis (Fin 4) (ZMod 2) V) : cf b 1 = oneC4 := by
  apply decodeC4_injOn (validC4_cf b _) validC4_oneC4
  rw [decodeC4_cf, decodeC4_oneC4, map_one, Units.val_one]

theorem cf_eq_oneC4_iff (b : Module.Basis (Fin 4) (ZMod 2) V) (γ : V ≃ₗ[ZMod 2] V) :
    cf b γ = oneC4 ↔ γ = 1 := by
  rw [← cf_one b]
  exact (cf_injective b).eq_iff

@[expose] noncomputable def vc (b : Module.Basis (Fin 4) (ZMod 2) V) (v : V) : ℕ :=
  enc4 (b.equivFun v)

theorem vc_lt (b : Module.Basis (Fin 4) (ZMod 2) V) (v : V) : vc b v < 16 := enc4_lt _

theorem vec4_vc (b : Module.Basis (Fin 4) (ZMod 2) V) (v : V) :
    vec4 (vc b v) = b.equivFun v :=
  vec4_enc4 _

theorem vc_injective (b : Module.Basis (Fin 4) (ZMod 2) V) : Function.Injective (vc b) := by
  intro v w h
  have := congrArg vec4 h
  rw [vec4_vc, vec4_vc] at this
  exact b.equivFun.injective this

theorem vc_add (b : Module.Basis (Fin 4) (ZMod 2) V) (v w : V) :
    vc b (v + w) = vc b v ^^^ vc b w := by
  apply vec4_inj (vc_lt b _) (Nat.xor_lt_two_pow (n := 4) (vc_lt b v) (vc_lt b w))
  rw [vec4_vc, vec4_xor, vec4_vc, vec4_vc, map_add]

theorem vc_zero (b : Module.Basis (Fin 4) (ZMod 2) V) : vc b 0 = 0 := by
  apply vec4_inj (vc_lt b _) (by norm_num)
  rw [vec4_vc, vec4_zero, map_zero]

theorem vc_eq_zero_iff (b : Module.Basis (Fin 4) (ZMod 2) V) (v : V) : vc b v = 0 ↔ v = 0 := by
  rw [← vc_zero b]
  exact (vc_injective b).eq_iff

theorem mulVecC_cf (b : Module.Basis (Fin 4) (ZMod 2) V) (γ : V ≃ₗ[ZMod 2] V) (v : V) :
    mulVecC (cf b γ) (vc b v) = vc b (γ v) := by
  apply vec4_inj (mulVecC_lt16 (validC4_cf b γ) _) (vc_lt b _)
  rw [← decodeC4_mulVec (validC4_cf b γ).1, decodeC4_cf, coe_phi4, vec4_vc, vec4_vc,
    Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
  exact LinearMap.toMatrix_mulVec_repr b b (γ : V →ₗ[ZMod 2] V) v

theorem bJ_vc {B : LinearMap.BilinForm (ZMod 2) V} (b : Module.Basis (Fin 4) (ZMod 2) V)
    (hgram : ∀ i j, B (b i) (b j) = antidiagGram i j) (v w : V) :
    b2z (bJ (vc b v) (vc b w)) = B v w := by
  rw [b2z_bJ, vec4_vc, vec4_vc, form_eq_formJ b hgram, Module.Basis.equivFun_apply,
    Module.Basis.equivFun_apply]

section Node

variable (b : Module.Basis (Fin 4) (ZMod 2) V) (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (s : Node)

structure IsNodeOf : Prop where
  mem : ∀ γ, γ ∈ Γ ↔ cf b γ ∈ s.els
  surj : ∀ x ∈ s.els, ∃ γ ∈ Γ, cf b γ = x
  nodup : s.els.Nodup

variable {b Γ s}

theorem isNodeOf_of (hs : ∀ x ∈ s.els, InD (Γ.map (phi4 b)) x)
    (hs' : ∀ g ∈ Γ.map (phi4 b), colsOf4 (g : Mat4) ∈ s.els) (hnd : s.els.Nodup) :
    IsNodeOf b Γ s := by
  have hsurj : ∀ x ∈ s.els, ∃ γ ∈ Γ, cf b γ = x := by
    intro x hx
    obtain ⟨hxv, g, hg, hgx⟩ := hs x hx
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
    refine ⟨γ, hγ, ?_⟩
    rw [cf, hgx, colsOf4_decodeC4 hxv]
  refine ⟨fun γ => ⟨fun hγ => hs' _ ⟨γ, hγ, rfl⟩, fun h => ?_⟩, hsurj, hnd⟩
  obtain ⟨δ, hδ, hδe⟩ := hsurj _ h
  rwa [← cf_injective b hδe]

theorem IsNodeOf.card_filter (h : IsNodeOf b Γ s) (p : List ℕ → Bool)
    (K : Subgroup (V ≃ₗ[ZMod 2] V)) (hK : ∀ γ ∈ Γ, γ ∈ K ↔ p (cf b γ) = true) :
    Nat.card ↥(Γ ⊓ K) = (s.els.filter p).length := by
  classical
  have hnd : (s.els.filter p).Nodup := h.nodup.filter p
  rw [← List.toFinset_card_of_nodup hnd, ← Nat.card_eq_finsetCard]
  let f : ↥(Γ ⊓ K) → {x // x ∈ (s.els.filter p).toFinset} := fun γ =>
    ⟨cf b γ, by
      simp only [List.mem_toFinset, List.mem_filter]
      exact ⟨(h.mem γ).mp γ.2.1, (hK γ γ.2.1).mp γ.2.2⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun γ δ hγδ => Subtype.ext (cf_injective b (congrArg Subtype.val hγδ)), ?_⟩
    rintro ⟨x, hx⟩
    simp only [List.mem_toFinset, List.mem_filter] at hx
    obtain ⟨γ, hγ, hγx⟩ := h.surj x hx.1
    refine ⟨⟨γ, hγ, (hK γ hγ).mpr (by rw [hγx]; exact hx.2)⟩, Subtype.ext hγx⟩
  exact Nat.card_congr (Equiv.ofBijective f hf)

theorem IsNodeOf.card_eq (h : IsNodeOf b Γ s) : Nat.card Γ = s.els.length := by
  have := h.card_filter (fun _ => true) ⊤ (fun γ _ => by simp)
  rw [inf_top_eq, List.filter_true] at this
  exact this

theorem IsNodeOf.mem_els (h : IsNodeOf b Γ s) {γ : V ≃ₗ[ZMod 2] V} (hγ : γ ∈ Γ) :
    cf b γ ∈ s.els := (h.mem γ).mp hγ

end Node

theorem ord3_cf (b : Module.Basis (Fin 4) (ZMod 2) V) (γ : V ≃ₗ[ZMod 2] V) :
    ord3 (cf b γ) = true ↔ γ ≠ 1 ∧ γ ^ 3 = 1 := by
  simp only [ord3, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, cf_eq_oneC4_iff]
  rw [← cf_mul, ← cf_mul, ← cf_one b, (cf_injective b).eq_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;>
    [rw [pow_succ, pow_two, mul_assoc]; rw [pow_succ, pow_two, mul_assoc] at h2] <;> exact h2

theorem invl_cf (b : Module.Basis (Fin 4) (ZMod 2) V) (γ : V ≃ₗ[ZMod 2] V) :
    invl (cf b γ) = true ↔ γ ≠ 1 ∧ γ ^ 2 = 1 := by
  simp only [invl, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, cf_eq_oneC4_iff]
  rw [← cf_mul, ← cf_one b, (cf_injective b).eq_iff, pow_two]

theorem comm_cf (b : Module.Basis (Fin 4) (ZMod 2) V) (γ δ : V ≃ₗ[ZMod 2] V) :
    (mulC (cf b γ) (cf b δ) == mulC (cf b δ) (cf b γ)) = true ↔ γ * δ = δ * γ := by
  rw [beq_iff_eq, ← cf_mul, ← cf_mul, (cf_injective b).eq_iff]

@[expose] def stabW [Finite V] (W : Submodule (ZMod 2) V) : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {γ | ∀ w ∈ W, γ w ∈ W}
  mul_mem' {γ δ} hγ hδ w hw := hγ _ (hδ w hw)
  one_mem' w hw := hw
  inv_mem' {γ} hγ := by
    intro w hw
    have := Finite.of_injective (fun v : ↥W => (v : V)) Subtype.val_injective
    let f : ↥W → ↥W := fun v => ⟨γ v, hγ v v.2⟩
    have hf : Function.Injective f := fun v v' h => Subtype.ext (γ.injective (congrArg
      Subtype.val h))
    obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.mp hf) ⟨w, hw⟩
    have hv' : γ v = w := congrArg Subtype.val hv
    have e1 : γ⁻¹ w = v := by
      rw [← hv', ← LinearEquiv.mul_apply, inv_mul_cancel]
      rfl
    rw [e1]
    exact v.2

theorem mem_stabW [Finite V] {W : Submodule (ZMod 2) V} {γ : V ≃ₗ[ZMod 2] V} :
    γ ∈ stabW W ↔ ∀ w ∈ W, γ w ∈ W := Iff.rfl

theorem mem_fixingSubgroup_iff' {W : Submodule (ZMod 2) V} {γ : V ≃ₗ[ZMod 2] V} :
    γ ∈ fixingSubgroup (V ≃ₗ[ZMod 2] V) (W : Set V) ↔ ∀ w ∈ W, γ w = w := by
  rw [mem_fixingSubgroup_iff]
  rfl

section Line

variable {B : LinearMap.BilinForm (ZMod 2) V} (b : Module.Basis (Fin 4) (ZMod 2) V)

@[expose] noncomputable def lineOf (u w : V) : List ℕ := [vc b u, vc b w, vc b (u + w)]

theorem lineOf_mem (hgram : ∀ i j, B (b i) (b j) = antidiagGram i j) {u w : V} (hu : u ≠ 0)
    (hw : w ≠ 0) (huw : u ≠ w) (hB : B u w = 0) : lineOf b u w ∈ tiLinesC := by
  have h1 : 0 < vc b u := Nat.pos_of_ne_zero fun h => hu ((vc_eq_zero_iff b u).mp h)
  have h2 : 0 < vc b w := Nat.pos_of_ne_zero fun h => hw ((vc_eq_zero_iff b w).mp h)
  have h3 : vc b u ≠ vc b w := fun h => huw (vc_injective b h)
  have h4 : bJ (vc b u) (vc b w) = false := by
    have := bJ_vc b hgram u w
    rw [hB] at this
    cases h : bJ (vc b u) (vc b w)
    · rfl
    · rw [h] at this
      exact absurd this (by decide)
  simp only [tiLinesC, List.mem_flatMap, List.mem_range, List.mem_filterMap]
  refine ⟨vc b u, vc_lt b u, vc b w, vc_lt b w, ?_⟩
  simp [h1, h2, h3, h4, lineOf, vc_add]

theorem mem_plane_iff {W : Submodule (ZMod 2) V} {u w : V} (hW : ∀ x ∈ W, x = 0 ∨ x = u ∨
    x = w ∨ x = u + w) (huW : u ∈ W) (hwW : w ∈ W) (x : V) :
    x ∈ W ↔ x = 0 ∨ x = u ∨ x = w ∨ x = u + w := by
  refine ⟨hW x, ?_⟩
  rintro (rfl | rfl | rfl | rfl)
  · exact W.zero_mem
  · exact huW
  · exact hwW
  · exact W.add_mem huW hwW

theorem all_lineOf (u w : V) (P : ℕ → Bool) :
    (lineOf b u w).all P = true ↔
      P (vc b u) = true ∧ P (vc b w) = true ∧ P (vc b (u + w)) = true := by
  simp [lineOf]

theorem contains_lineOf (u w : V) (y : ℕ) :
    (lineOf b u w).contains y = true ↔ y = vc b u ∨ y = vc b w ∨ y = vc b (u + w) := by
  simp [lineOf]

theorem any_lineOf (u w : V) (P : ℕ → Bool) :
    (lineOf b u w).any P = true ↔
      P (vc b u) = true ∨ P (vc b w) = true ∨ P (vc b (u + w)) = true := by
  simp [lineOf]

omit b in
theorem add_ne_zero_of {u w : V} (huw : u ≠ w) : u + w ≠ 0 := by
  intro h
  apply huw
  have : u = -w := eq_neg_of_add_eq_zero_left h
  rw [this]
  have key : ∀ x : V, -x = x := fun x => by
    have h2 : (2 : ZMod 2) = 0 := rfl
    calc -x = -x + 0 := by rw [add_zero]
      _ = -x + (2 : ZMod 2) • x := by rw [h2, zero_smul]
      _ = x := by rw [two_smul]; abel
  exact key w

variable {W : Submodule (ZMod 2) V} {u w : V} (hW : ∀ x ∈ W, x = 0 ∨ x = u ∨ x = w ∨ x = u + w)
  (huW : u ∈ W) (hwW : w ∈ W)
include hW huW hwW

omit b in
theorem mem_W_iff_of_ne {x : V} (hx : x ≠ 0) : x ∈ W ↔ x = u ∨ x = w ∨ x = u + w := by
  rw [mem_plane_iff hW huW hwW]
  constructor
  · rintro (h | h)
    · exact absurd h hx
    · exact h
  · intro h; exact Or.inr h

omit b in
theorem forall_W_iff (P : V → Prop) (h0 : P 0) :
    (∀ x ∈ W, P x) ↔ P u ∧ P w ∧ P (u + w) := by
  constructor
  · intro h
    exact ⟨h u huW, h w hwW, h _ (W.add_mem huW hwW)⟩
  · rintro ⟨h1, h2, h3⟩ x hx
    rcases hW x hx with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3

theorem nrm_cf (hu : u ≠ 0) (hw : w ≠ 0) (huw : u ≠ w) (γ : V ≃ₗ[ZMod 2] V) :
    ((lineOf b u w).all fun y => (lineOf b u w).contains (mulVecC (cf b γ) y)) = true ↔
      ∀ x ∈ W, γ x ∈ W := by
  have huw0 := add_ne_zero_of huw
  have key : ∀ x ≠ 0, ((lineOf b u w).contains (mulVecC (cf b γ) (vc b x)) = true ↔ γ x ∈ W) := by
    intro x hx
    have hγx : γ x ≠ 0 := by rwa [ne_eq, LinearEquiv.map_eq_zero_iff]
    rw [contains_lineOf, mulVecC_cf, (vc_injective b).eq_iff, (vc_injective b).eq_iff,
      (vc_injective b).eq_iff, mem_W_iff_of_ne hW huW hwW hγx]
  rw [all_lineOf, key u hu, key w hw, key _ huw0,
    forall_W_iff hW huW hwW (fun x => γ x ∈ W) (by rw [map_zero]; exact W.zero_mem)]

theorem fix_cf (γ : V ≃ₗ[ZMod 2] V) :
    ((lineOf b u w).all fun y => mulVecC (cf b γ) y == y) = true ↔ ∀ x ∈ W, γ x = x := by
  have key : ∀ x : V, ((mulVecC (cf b γ) (vc b x) == vc b x) = true ↔ γ x = x) := by
    intro x
    rw [beq_iff_eq, mulVecC_cf, (vc_injective b).eq_iff]
  rw [all_lineOf, key, key, key,
    forall_W_iff hW huW hwW (fun x => γ x = x) (by rw [map_zero])]

theorem isNT_cf (γ : V ≃ₗ[ZMod 2] V) : isNT (cf b γ) (lineOf b u w) = true ↔ ∃ x ∈ W, γ x ≠ x := by
  have key : ∀ x : V, ((mulVecC (cf b γ) (vc b x) != vc b x) = true ↔ γ x ≠ x) := by
    intro x
    rw [bne_iff_ne, mulVecC_cf, ne_eq, (vc_injective b).eq_iff]
  rw [isNT, any_lineOf, key, key, key]
  constructor
  · rintro (h | h | h)
    · exact ⟨u, huW, h⟩
    · exact ⟨w, hwW, h⟩
    · exact ⟨u + w, W.add_mem huW hwW, h⟩
  · rintro ⟨x, hx, hne⟩
    rcases hW x hx with rfl | rfl | rfl | rfl
    · exact absurd (map_zero γ) hne
    · exact Or.inl hne
    · exact Or.inr (Or.inl hne)
    · exact Or.inr (Or.inr hne)

end Line

end CFSG.Quasithin.H13.Sp4Cert
