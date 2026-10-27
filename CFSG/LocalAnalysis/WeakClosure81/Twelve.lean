module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.G11Basic
public import CFSG.SignalizerFunctorTheorem.Quadratic.Toolkit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] def cE (G : Subgroup (LGL 2 V)) : Submodule (ZMod 2) V :=
  fixSub G ⊓ commSub G

theorem cE_le_fixSub (G : Subgroup (LGL 2 V)) : cE G ≤ fixSub G := inf_le_left

theorem cE_le_commSub (G : Subgroup (LGL 2 V)) : cE G ≤ commSub G := inf_le_right

theorem mem_cE {G : Subgroup (LGL 2 V)} {v : V} :
    v ∈ cE G ↔ (∀ t ∈ G, t v = v) ∧ v ∈ commSub G :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

@[expose] def fixMod (W : Submodule (ZMod 2) V) (t : LGL 2 V) : Submodule (ZMod 2) V where
  carrier := {v | t v - v ∈ W}
  add_mem' := fun {x y} hx hy => by
    show t (x + y) - (x + y) ∈ W
    have h : t (x + y) - (x + y) = (t x - x) + (t y - y) := by rw [map_add]; abel
    rw [h]; exact W.add_mem hx hy
  zero_mem' := by
    show t 0 - 0 ∈ W
    simp
  smul_mem' := fun c x hx => by
    show t (c • x) - c • x ∈ W
    have h : t (c • x) - c • x = c • (t x - x) := by rw [map_smul, smul_sub]
    rw [h]; exact W.smul_mem c hx

theorem mem_fixMod {W : Submodule (ZMod 2) V} {t : LGL 2 V} {v : V} :
    v ∈ fixMod W t ↔ t v - v ∈ W := Iff.rfl

theorem commSub_le_fixSub_of_quadratic {A : Subgroup (LGL 2 V)}
    (h : commSpace A (commSub A) = ⊥) : commSub A ≤ fixSub A := by
  intro w hw b hb
  have h1 : b w - w ∈ commSpace A (commSub A) := sub_mem_commSpace hb hw
  rw [h, Submodule.mem_bot, sub_eq_zero] at h1
  exact h1

theorem commSpace_cj (g : LGL 2 V) (A : Subgroup (LGL 2 V)) :
    commSpace (cj g A) (commSub (cj g A)) =
      (commSpace A (commSub A)).map (g : V →ₗ[ZMod 2] V) := by
  refine le_antisymm ?_ ?_
  · rw [commSpace_le_iff]
    intro b hb w hw
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
    rw [commSub_cj] at hw
    obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.mp hw
    refine Submodule.mem_map.mpr ⟨a w' - w', sub_mem_commSpace ha hw', ?_⟩
    have h2 : (g * a * g⁻¹) (g w') = g (a w') := by
      change g (a (g⁻¹ (g w'))) = g (a w')
      rw [inv_apply_apply']
    change g (a w' - w') = (g * a * g⁻¹) (g w') - g w'
    rw [map_sub, h2]
  · rw [Submodule.map_le_iff_le_comap, commSpace_le_iff]
    intro a ha w hw
    rw [Submodule.mem_comap]
    have hb : g * a * g⁻¹ ∈ cj g A := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    have hw' : g w ∈ commSub (cj g A) := by
      rw [commSub_cj]
      exact Submodule.mem_map.mpr ⟨w, hw, rfl⟩
    have h1 := sub_mem_commSpace hb hw'
    have h2 : (g * a * g⁻¹) (g w) = g (a w) := by
      change g (a (g⁻¹ (g w))) = g (a w)
      rw [inv_apply_apply']
    convert h1 using 1
    change g (a w - w) = (g * a * g⁻¹) (g w) - g w
    rw [map_sub, h2]

theorem commSpace_cj_eq_bot {A : Subgroup (LGL 2 V)}
    (h : commSpace A (commSub A) = ⊥) (g : LGL 2 V) :
    commSpace (cj g A) (commSub (cj g A)) = ⊥ := by
  rw [commSpace_cj, h, Submodule.map_bot]

theorem fixSub_sup (A B : Subgroup (LGL 2 V)) : fixSub (A ⊔ B) = fixSub A ⊓ fixSub B := by
  refine le_antisymm ?_ ?_
  · intro v hv
    exact ⟨fun a ha => hv a (Subgroup.mem_sup_left ha),
      fun b hb => hv b (Subgroup.mem_sup_right hb)⟩
  · rintro v ⟨ha, hb⟩ t ht
    let K : Subgroup (LGL 2 V) :=
      { carrier := {t | t v = v}
        one_mem' := rfl
        mul_mem' := fun {s t} hs ht => by
          have hs' : s v = v := hs
          have ht' : t v = v := ht
          change (s * t) v = v
          rw [LinearEquiv.mul_apply, ht', hs']
        inv_mem' := fun {s} hs => by
          have hs' : s v = v := hs
          change s⁻¹ v = v
          conv_lhs => rw [← hs']
          exact LinearEquiv.symm_apply_apply s v }
    have hle : A ⊔ B ≤ K := sup_le (fun a ha' => ha a ha') (fun b hb' => hb b hb')
    exact hle ht

theorem mem_fixSub_sup {A B : Subgroup (LGL 2 V)} {v : V} (hA : v ∈ fixSub A)
    (hB : v ∈ fixSub B) : v ∈ fixSub (A ⊔ B) := by
  let K : Subgroup (LGL 2 V) :=
    { carrier := {t | t v = v}
      one_mem' := rfl
      mul_mem' := fun {s t} hs ht => by
        have hs' : s v = v := hs
        have ht' : t v = v := ht
        change (s * t) v = v
        rw [LinearEquiv.mul_apply, ht', hs']
      inv_mem' := fun {s} hs => by
        have hs' : s v = v := hs
        change s⁻¹ v = v
        conv_lhs => rw [← hs']
        exact LinearEquiv.symm_apply_apply s v }
  have hle : A ⊔ B ≤ K := sup_le (fun a ha => hA a ha) (fun b hb => hB b hb)
  intro t ht
  exact hle ht

theorem cj_cj (h k : LGL 2 V) (A : Subgroup (LGL 2 V)) :
    cj h (cj k A) = cj (h * k) A := by
  unfold cj
  rw [Subgroup.map_map]
  congr 1

theorem cj_one (A : Subgroup (LGL 2 V)) : cj 1 A = A := by
  have h1 : MulAut.conj (1 : LGL 2 V) = 1 := map_one _
  unfold cj
  rw [h1]
  exact Subgroup.map_id A

theorem cj_self_inv (g : LGL 2 V) (A : Subgroup (LGL 2 V)) : cj g⁻¹ (cj g A) = A := by
  rw [cj_cj, inv_mul_cancel, cj_one]

theorem map_mem_cE (G : Subgroup (LGL 2 V)) {t : LGL 2 V} (ht : t ∈ G) {y : V}
    (hy : y ∈ cE G) : t y ∈ cE G := by
  refine ⟨?_, map_mem_commSub G ht (cE_le_commSub G hy)⟩
  intro s hs
  rw [(cE_le_fixSub G hy) t ht]
  exact (cE_le_fixSub G hy) s hs

@[expose] def SchurMultiplierInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X) [K.Normal] (A : Subgroup X),
    K ≤ Subgroup.center X → Odd (Nat.card K) → IsPGroup 2 A → A ⊓ K = ⊥ →
    (∃ n : ℕ, 1 < n ∧ (CFSG.Quasithin.IsPSL 2 2 n (X ⧸ K) ∨ CFSG.Quasithin.IsSz n (X ⧸ K))) →
    ∃ D : Subgroup X, D.Normal ∧ K ⊓ D = ⊥ ∧ K ⊔ D = ⊤ ∧ A ≤ D

theorem twelveSix {X : Type} [Group X] [Finite X] (hMult : SchurMultiplierInput)
    {K : Subgroup X} [K.Normal] {A : Subgroup X}
    (hKcen : K ≤ Subgroup.center X) (hKodd : Odd (Nat.card K))
    (hA2 : IsPGroup 2 A) (hAK : A ⊓ K = ⊥)
    (htype : ∃ n : ℕ, 1 < n ∧ (CFSG.Quasithin.IsPSL 2 2 n (X ⧸ K) ∨ CFSG.Quasithin.IsSz n (X ⧸ K)))
    (hgen : Subgroup.normalClosure (A : Set X) = ⊤) :
    K = ⊥ := by
  obtain ⟨D, hDnorm, hKD, _hKsup, hAD⟩ := hMult X K A hKcen hKodd hA2 hAK htype
  haveI := hDnorm
  have hle : Subgroup.normalClosure (A : Set X) ≤ D := Subgroup.normalClosure_le_normal hAD
  have hDtop : D = ⊤ := top_le_iff.mp (hgen ▸ hle)
  calc K = K ⊓ ⊤ := (inf_top_eq K).symm
    _ = K ⊓ D := by rw [hDtop]
    _ = ⊥ := hKD

end CFSG.LocalAnalysis.WeakClosure81
