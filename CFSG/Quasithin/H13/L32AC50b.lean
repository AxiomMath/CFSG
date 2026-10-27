module

public import CFSG.Quasithin.H13.L32AC50a
public import CFSG.Quasithin.Background.G6Natural
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

public section

namespace CFSG.Quasithin.H13.L32A.C.Alt7

open Equiv Equiv.Perm

@[expose] def listSub (l : List (Perm (Fin 7)))
    (h : (1 : Perm (Fin 7)) ∈ l ∧ (∀ a ∈ l, ∀ b ∈ l, a * b ∈ l) ∧ ∀ a ∈ l, a⁻¹ ∈ l) :
    Subgroup (Perm (Fin 7)) where
  carrier := {g | g ∈ l}
  one_mem' := h.1
  mul_mem' := fun ha hb => h.2.1 _ ha _ hb
  inv_mem' := fun ha => h.2.2 _ ha

theorem mem_listSub {l : List (Perm (Fin 7))}
    {h : (1 : Perm (Fin 7)) ∈ l ∧ (∀ a ∈ l, ∀ b ∈ l, a * b ∈ l) ∧ ∀ a ∈ l, a⁻¹ ∈ l}
    {g : Perm (Fin 7)} : g ∈ listSub l h ↔ g ∈ l := Iff.rfl

theorem card_listSub (l : List (Perm (Fin 7)))
    (h : (1 : Perm (Fin 7)) ∈ l ∧ (∀ a ∈ l, ∀ b ∈ l, a * b ∈ l) ∧ ∀ a ∈ l, a⁻¹ ∈ l)
    (hl : l.Nodup) : Nat.card (listSub l h) = l.length := by
  have e : ↥(listSub l h) ≃ {σ : Perm (Fin 7) // σ ∈ l.toFinset} :=
    { toFun := fun g => ⟨g, List.mem_toFinset.mpr g.2⟩
      invFun := fun σ => ⟨σ.1, List.mem_toFinset.mp σ.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup hl]

@[expose] def tsSub : Subgroup (Perm (Fin 7)) := listSub tsList ts_closed

@[expose] def taSub : Subgroup (Perm (Fin 7)) := listSub taList ta_closed

@[expose] def v4Sub : Subgroup (Perm (Fin 7)) := listSub v4List v4_closed

@[expose] def raSSub : Subgroup (Perm (Fin 7)) := listSub raSList raS_closed

@[expose] def raASub : Subgroup (Perm (Fin 7)) := listSub raAList raA_closed

@[expose] def rbSSub : Subgroup (Perm (Fin 7)) := listSub rbSList rbS_closed

@[expose] def rbASub : Subgroup (Perm (Fin 7)) := listSub rbAList rbA_closed

@[expose] def rcSSub : Subgroup (Perm (Fin 7)) := listSub rcSList rcS_closed

@[expose] def rcASub : Subgroup (Perm (Fin 7)) := listSub rcAList rcA_closed

theorem card_tsSub : Nat.card tsSub = 16 := by
  rw [tsSub, card_listSub _ _ ts_nodup.1, ts_nodup.2]

theorem card_taSub : Nat.card taSub = 8 := by
  rw [taSub, card_listSub _ _ ta_nodup.1, ta_nodup.2]

theorem card_raSSub : Nat.card raSSub = 48 := by
  rw [raSSub, card_listSub _ _ raS_nodup.1, raS_nodup.2]

theorem card_raASub : Nat.card raASub = 24 := by
  rw [raASub, card_listSub _ _ raA_nodup.1, raA_nodup.2]

theorem card_rbSSub : Nat.card rbSSub = 48 := by
  rw [rbSSub, card_listSub _ _ rbS_nodup.1, rbS_nodup.2]

theorem card_rbASub : Nat.card rbASub = 24 := by
  rw [rbASub, card_listSub _ _ rbA_nodup.1, rbA_nodup.2]

theorem card_rcSSub : Nat.card rcSSub = 48 := by
  rw [rcSSub, card_listSub _ _ rcS_nodup.1, rcS_nodup.2]

theorem card_rcASub : Nat.card rcASub = 24 := by
  rw [rcASub, card_listSub _ _ rcA_nodup.1, rcA_nodup.2]

theorem mem_iff_of_maps {Δ : Finset (Fin 7)} {g : Perm (Fin 7)} (hg : ∀ i ∈ Δ, g i ∈ Δ)
    (x : Fin 7) : g x ∈ Δ ↔ x ∈ Δ := by
  have hsub : Δ.map g.toEmbedding ⊆ Δ := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hy
    exact hg i hi
  have heq : Δ.map g.toEmbedding = Δ :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_map])
  conv_lhs => rw [← heq]
  exact Finset.mem_map' g.toEmbedding

@[expose] def stabSub : Subgroup (Perm (Fin 7)) where
  carrier := {g | sign g = 1 ∧ ∀ i ∈ d3, g i ∈ d3}
  one_mem' := ⟨map_one _, fun _ hi => hi⟩
  mul_mem' := fun {a b} ha hb => ⟨by rw [map_mul, ha.1, hb.1, one_mul],
    fun i hi => ha.2 _ (hb.2 i hi)⟩
  inv_mem' := fun {a} ha => by
    refine ⟨by rw [map_inv, ha.1, inv_one], fun i hi => ?_⟩
    rw [← mem_iff_of_maps ha.2]
    have e : a (a⁻¹ i) = i := a.apply_symm_apply i
    rw [e]
    exact hi

theorem mem_stabSub {g : Perm (Fin 7)} : g ∈ stabSub ↔ sign g = 1 ∧ ∀ i ∈ d3, g i ∈ d3 :=
  Iff.rfl

theorem mem_stabList {g : Perm (Fin 7)} (hg : g ∈ stabSub) : g ∈ stabList := by
  have hiff := mem_iff_of_maps hg.2
  have hiffc : ∀ x, g x ∈ d3c ↔ x ∈ d3c := fun x => by
    rw [mem_d3c, mem_d3c, hiff]
  set b := ofSubtype (g.subtypePerm (p := fun x => x ∈ d3) hiff) with hb
  set a := ofSubtype (g.subtypePerm (p := fun x => x ∈ d3c) hiffc) with ha
  have hab : g = a * b := by
    ext x
    by_cases hx : x ∈ d3
    · have hgx : g x ∈ d3 := (hiff x).mpr hx
      have hgx' : g x ∉ d3c := fun h => (mem_d3c _).mp h hgx
      rw [Perm.mul_apply, hb, ofSubtype_apply_of_mem _ hx, subtypePerm_apply, ha,
        ofSubtype_apply_of_not_mem _ hgx']
    · have hx' : x ∈ d3c := (mem_d3c x).mpr hx
      rw [Perm.mul_apply, hb, ofSubtype_apply_of_not_mem _ hx, ha, ofSubtype_apply_of_mem _ hx',
        subtypePerm_apply]
  rw [hab]
  refine stab_of_mul a (ofSubtype_mem_s4 _) b (ofSubtype_mem_s3 _) ?_
  rw [← hab]
  exact hg.1

theorem mem_stabSub_iff {g : Perm (Fin 7)} : g ∈ stabSub ↔ g ∈ stabList :=
  ⟨mem_stabList, fun h => ⟨stab_sign g h, stab_maps g h⟩⟩

theorem card_stabSub : Nat.card stabSub = 72 := by
  have e : ↥stabSub ≃ {σ : Perm (Fin 7) // σ ∈ stabList.toFinset} :=
    { toFun := fun g => ⟨g, List.mem_toFinset.mpr (mem_stabList g.2)⟩
      invFun := fun σ => ⟨σ.1, mem_stabSub_iff.mpr (List.mem_toFinset.mp σ.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup stab_nodup.1, stab_nodup.2]

abbrev coords (w : G6.coreMod 7) : Fin 7 → ZMod 2 := Multiplicative.toAdd (w : G6.PermMod 7)

theorem coords_coreAct (σ : Perm (Fin 7)) (w : G6.coreMod 7) (i : Fin 7) :
    coords (G6.coreAct 7 σ w) i = coords w (σ⁻¹ i) := rfl

theorem coords_mul (w₁ w₂ : G6.coreMod 7) : coords (w₁ * w₂) = coords w₁ + coords w₂ := rfl

theorem coords_injective : Function.Injective coords := fun _ _ h =>
  Subtype.ext (Multiplicative.toAdd.injective h)

theorem toAdd_fixed {w : G6.coreMod 7} (hw : ∀ t ∈ taList, G6.coreAct 7 t w = w) :
    coords w = 0 ∨ coords w = e45 ∨ coords w = e0123 ∨ coords w = e012345 :=
  fixed_vec (coords w) (G6.mem_coreMod.mp w.2) fun t ht i => by
    have := congrFun (congrArg coords (hw t ht)) i
    rwa [coords_coreAct] at this

theorem coords_pow (y : G6.coreMod 7) (n : ℕ) : coords (y ^ n) = n • coords y := rfl

theorem zmod_two_val_smul : ∀ k x : ZMod 2, k.val • x = k * x := by
  decide

theorem eight_le_card {Z : Subgroup (G6.coreMod 7)} {u v w : G6.coreMod 7} (hu : u ∈ Z)
    (hv : v ∈ Z) (hw : w ∈ Z)
    (hind : ∀ a b c : ZMod 2, (fun i => a * coords u i + b * coords v i + c * coords w i) = 0 →
      a = 0 ∧ b = 0 ∧ c = 0) : 8 ≤ Nat.card Z := by
  let f : ZMod 2 × ZMod 2 × ZMod 2 → Z := fun x =>
    ⟨u ^ (x.1.val) * v ^ (x.2.1.val) * w ^ (x.2.2.val),
      Z.mul_mem (Z.mul_mem (Z.pow_mem hu _) (Z.pow_mem hv _)) (Z.pow_mem hw _)⟩
  have hfc : ∀ x i, coords ((f x : Z) : G6.coreMod 7) i =
      x.1 * coords u i + x.2.1 * coords v i + x.2.2 * coords w i := by
    intro x i
    show coords (u ^ (x.1.val) * v ^ (x.2.1.val) * w ^ (x.2.2.val)) i = _
    rw [coords_mul, coords_mul, coords_pow, coords_pow, coords_pow]
    simp only [Pi.add_apply, Pi.smul_apply, zmod_two_val_smul]
  have hf : Function.Injective f := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    have h1 : ∀ i, coords ((f (a, b, c) : Z) : G6.coreMod 7) i =
        coords ((f (a', b', c') : Z) : G6.coreMod 7) i := fun i => by rw [h]
    obtain ⟨ha, hb, hc⟩ := hind (a - a') (b - b') (c - c') (by
      funext i
      have := h1 i
      rw [hfc, hfc] at this
      simp only [Pi.zero_apply]
      linear_combination this)
    simp only [Prod.mk.injEq]
    exact ⟨sub_eq_zero.mp ha, sub_eq_zero.mp hb, sub_eq_zero.mp hc⟩
  have h8 : Nat.card (ZMod 2 × ZMod 2 × ZMod 2) = 8 := by
    simp
  rw [← h8]
  exact Nat.card_le_card_of_injective f hf

end CFSG.Quasithin.H13.L32A.C.Alt7
