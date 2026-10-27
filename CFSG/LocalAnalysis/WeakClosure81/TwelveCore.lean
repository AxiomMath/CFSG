module

public import CFSG.LocalAnalysis.WeakClosure81.Twelve
public import CFSG.LocalAnalysis.WeakClosure81.TenFive

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private theorem b12_TwelveCore_add_self_eq_zero (x : V) : x + x = 0 := by
  have h := two_smul (ZMod 2) x
  rw [show (2 : ZMod 2) = 0 by decide, zero_smul] at h
  exact h.symm

private theorem b12_TwelveCore_neg_eq_self (x : V) : -x = x := by
  have hx := b12_TwelveCore_add_self_eq_zero x
  calc -x = -x + 0 := by rw [add_zero]
    _ = -x + (x + x) := by rw [hx]
    _ = (-x + x) + x := by abel
    _ = 0 + x := by rw [neg_add_cancel]
    _ = x := by rw [zero_add]

theorem isElemAbelian_of_quadratic {A : Subgroup (LGL 2 V)}
    (h : commSpace A (commSub A) = ⊥) : IsElemAbelian 2 A := by
  have h1 : commSub A ≤ fixSub A := commSub_le_fixSub_of_quadratic h
  have hstep : ∀ a ∈ A, ∀ b ∈ A, ∀ v : V, a (b v) = a v + b v - v := by
    intro a ha b hb v
    have hb1 : a (b v - v) = b v - v := h1 (sub_mem_commSub A hb v) a ha
    calc a (b v) = (a (b v) - a v) + a v := by abel
      _ = (b v - v) + a v := by rw [← map_sub, hb1]
      _ = a v + b v - v := by abel
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    ext v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      hstep a ha b hb v, hstep b hb a ha v]
    abel
  have hsq : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    ext v
    rw [LinearEquiv.mul_apply, hstep a ha a ha v,
      b12_TwelveCore_add_self_eq_zero, zero_sub, b12_TwelveCore_neg_eq_self]
    rfl
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · exact hcomm a.1 a.2 b.1 b.2
  · rw [pow_two]
    exact hsq x hx

theorem fixMod_of_closure {G : Subgroup (LGL 2 V)} {S : Set (LGL 2 V)}
    (hgen : G = Subgroup.closure S) {v : V} (hS : ∀ t ∈ S, t v - v ∈ cE G) :
    ∀ t ∈ G, t v - v ∈ cE G := by
  let K : Subgroup (LGL 2 V) :=
    { carrier := {t | t ∈ G ∧ t v - v ∈ cE G}
      one_mem' := ⟨G.one_mem, by simp⟩
      mul_mem' := fun {s t} hs ht => by
        refine ⟨G.mul_mem hs.1 ht.1, ?_⟩
        have hs' : s v - v ∈ cE G := hs.2
        have ht' : t v - v ∈ cE G := ht.2
        have h1 : (s * t) v - v = s (t v - v) + (s v - v) := by
          rw [LinearEquiv.mul_apply]
          have h2 : t v = (t v - v) + v := by abel
          rw [h2, map_add]; abel
        rw [h1, (cE_le_fixSub G ht') s hs.1]
        exact (cE G).add_mem ht' hs'
      inv_mem' := fun {s} hs => by
        refine ⟨G.inv_mem hs.1, ?_⟩
        let f : V := s v - v
        have hfv : f ∈ cE G := hs.2
        have hsv : s v = v + f := by dsimp [f]; abel
        have hsf : s⁻¹ f = f := (cE_le_fixSub G hfv) s⁻¹ (G.inv_mem hs.1)
        have h1 : v = s⁻¹ v + f := by
          calc v = s⁻¹ (s v) := (LinearEquiv.symm_apply_apply s v).symm
            _ = s⁻¹ (v + f) := by rw [hsv]
            _ = s⁻¹ v + s⁻¹ f := by rw [map_add]
            _ = s⁻¹ v + f := by rw [hsf]
        have h2 : s⁻¹ v = v + f := by
          conv_rhs => rw [h1]
          rw [add_assoc, b12_TwelveCore_add_self_eq_zero, add_zero]
        have h3 : s⁻¹ v - v = f := by rw [h2]; abel
        rw [h3]; exact hfv }
  have hclK : Subgroup.closure S ≤ K := by
    rw [Subgroup.closure_le]
    intro t ht
    exact ⟨by rw [hgen]; exact Subgroup.subset_closure ht, hS t ht⟩
  have hGK : G ≤ K := by rw [hgen]; exact hclK
  intro t ht
  exact (hGK ht).2

structure Hyp121K (G A : Subgroup (LGL 2 V)) (g : LGL 2 V) : Prop where
  g_mem : g ∈ G
  gen : G = A ⊔ cj g A
  quadratic : commSpace A (commSub A) = ⊥

theorem Hyp121K.elemAb {G A : Subgroup (LGL 2 V)} {g : LGL 2 V} (h : Hyp121K G A g) :
    IsElemAbelian 2 A :=
  isElemAbelian_of_quadratic h.quadratic

theorem Hyp121K.conj {G A : Subgroup (LGL 2 V)} {g : LGL 2 V} (h : Hyp121K G A g) :
    Hyp121K G (cj g A) g⁻¹ where
  g_mem := G.inv_mem h.g_mem
  gen := by rw [cj_self_inv, sup_comm]; exact h.gen
  quadratic := commSpace_cj_eq_bot h.quadratic g

theorem twelveOneK_sum {G A : Subgroup (LGL 2 V)} {g : LGL 2 V} (h : Hyp121K G A g) :
    commSub G = commSub A ⊔ commSub (cj g A) := by
  rw [h.gen, commSub_sup]

theorem twelveOneK_map_sup {G A : Subgroup (LGL 2 V)} {g : LGL 2 V} (h : Hyp121K G A g) :
    (commSub A).map (cE G).mkQ ⊔ (commSub (cj g A)).map (cE G).mkQ =
      (commSub G).map (cE G).mkQ := by
  rw [← Submodule.map_sup, twelveOneK_sum h]

theorem twelveOneK_map_inf {G A : Subgroup (LGL 2 V)} {g : LGL 2 V} (h : Hyp121K G A g) :
    (commSub A).map (cE G).mkQ ⊓ (commSub (cj g A)).map (cE G).mkQ = ⊥ := by
  have hAG : A ≤ G := by rw [h.gen]; exact le_sup_left
  have hAgG : cj g A ≤ G := by rw [h.gen]; exact le_sup_right
  rw [eq_bot_iff]
  intro y hy
  have hyG : y ∈ (commSub G).map (cE G).mkQ := by
    rw [← twelveOneK_map_sup h]
    exact Submodule.mem_sup_left hy.1
  obtain ⟨x, hxG, rfl⟩ := Submodule.mem_map.mp hyG
  obtain ⟨u, huA, hu⟩ := Submodule.mem_map.mp hy.1
  obtain ⟨u', huAg, hu'⟩ := Submodule.mem_map.mp hy.2
  have hxu : x - u ∈ cE G := (Submodule.Quotient.eq (cE G)).mp hu.symm
  have hxu' : x - u' ∈ cE G := (Submodule.Quotient.eq (cE G)).mp hu'.symm
  have hfix : ∀ t ∈ A ⊔ cj g A, t x = x := by
    intro t ht
    let K : Subgroup (LGL 2 V) :=
      { carrier := {t | t x = x}
        one_mem' := rfl
        mul_mem' := fun {s t} hs ht => by
          have hs' : s x = x := hs
          have ht' : t x = x := ht
          change (s * t) x = x
          rw [LinearEquiv.mul_apply, ht', hs']
        inv_mem' := fun {s} hs => by
          have hs' : s x = x := hs
          change s⁻¹ x = x
          conv_lhs => rw [← hs']
          exact LinearEquiv.symm_apply_apply s x }
    have hAK : A ≤ K := fun a ha' => by
      change a x = x
      have hu_fix : a u = u := commSub_le_fixSub_of_quadratic h.quadratic huA a ha'
      have hxsub : x = (x - u) + u := by abel
      rw [hxsub, map_add, hu_fix, (cE_le_fixSub G hxu) a (hAG ha')]
    have hAgK : cj g A ≤ K := fun b hb' => by
      change b x = x
      have hu'_fix : b u' = u' :=
        commSub_le_fixSub_of_quadratic (commSpace_cj_eq_bot h.quadratic g) huAg b hb'
      have hxsub : x = (x - u') + u' := by abel
      rw [hxsub, map_add, hu'_fix, (cE_le_fixSub G hxu') b (hAgG hb')]
    exact sup_le hAK hAgK ht
  have hxfixG : x ∈ fixSub G := by
    rw [h.gen]
    exact hfix
  have hxW : x ∈ cE G := ⟨hxfixG, hxG⟩
  exact (Submodule.Quotient.mk_eq_zero (cE G)).mpr hxW

theorem mem_cE_of_fixed_mod_cj {G A : Subgroup (LGL 2 V)} {g : LGL 2 V} (h : Hyp121K G A g)
    {v : V} (hv : v ∈ commSub (cj g A)) (hfix : ∀ t ∈ G, t v - v ∈ cE G) : v ∈ cE G := by
  have hAgG : cj g A ≤ G := by rw [h.gen]; exact le_sup_right
  have hquadB := commSpace_cj_eq_bot h.quadratic g
  have hvB : ∀ b ∈ cj g A, b v = v := commSub_le_fixSub_of_quadratic hquadB hv
  have hvA : ∀ a ∈ A, a v = v := by
    intro a ha
    have hga : g * a * g⁻¹ ∈ cj g A := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    have hf := hfix g h.g_mem
    have hbf : (g * a * g⁻¹) (g v - v) = g v - v := (cE_le_fixSub G hf) _ (hAgG hga)
    have hbgv : (g * a * g⁻¹) (g v) = g v := by
      have h1 : (g * a * g⁻¹) (g v) =
          (g * a * g⁻¹) v + (g * a * g⁻¹) (g v - v) := by
        have h2 : g v = v + (g v - v) := by abel
        conv_lhs => rw [h2]
        rw [map_add]
      rw [h1, hvB _ hga, hbf]
      abel
    have hav : a v = g⁻¹ ((g * a * g⁻¹) (g v)) := by
      have h1 : (g * a * g⁻¹) (g v) = g (a v) := by
        change g (a (g⁻¹ (g v))) = g (a v)
        rw [inv_apply_apply']
      rw [h1]
      exact (g.symm_apply_apply (a v)).symm
    rw [hav, hbgv]
    exact g.symm_apply_apply v
  refine mem_cE.mpr ⟨?_, ?_⟩
  · rw [h.gen]
    exact mem_fixSub_sup hvA hvB
  · exact commSub_mono (cj g A) G hAgG hv

theorem inf_sup_cE_leK {G A : Subgroup (LGL 2 V)} {g : LGL 2 V} (h : Hyp121K G A g) :
    commSub A ⊓ (commSub (cj g A) ⊔ cE G) ≤ cE G := by
  intro x hx
  have hmem : (cE G).mkQ x ∈
      (commSub A).map (cE G).mkQ ⊓ (commSub (cj g A)).map (cE G).mkQ := by
    refine ⟨Submodule.mem_map.mpr ⟨x, hx.1, rfl⟩, ?_⟩
    obtain ⟨b, hb, w, hw, hbw⟩ := Submodule.mem_sup.mp hx.2
    have hw0 : (cE G).mkQ w = 0 := (Submodule.Quotient.mk_eq_zero (cE G)).mpr hw
    refine Submodule.mem_map.mpr ⟨b, hb, ?_⟩
    rw [← hbw, map_add, hw0, add_zero]
  rw [twelveOneK_map_inf h] at hmem
  exact (Submodule.Quotient.mk_eq_zero (cE G)).mp (by simpa using hmem)

theorem inf_sup_cE_le_agK {G A : Subgroup (LGL 2 V)} {g : LGL 2 V} (h : Hyp121K G A g) :
    commSub (cj g A) ⊓ (commSub A ⊔ cE G) ≤ cE G := by
  intro x hx
  have hmem : (cE G).mkQ x ∈
      (commSub (cj g A)).map (cE G).mkQ ⊓ (commSub A).map (cE G).mkQ := by
    refine ⟨Submodule.mem_map.mpr ⟨x, hx.1, rfl⟩, ?_⟩
    obtain ⟨b, hb, w, hw, hbw⟩ := Submodule.mem_sup.mp hx.2
    have hw0 : (cE G).mkQ w = 0 := (Submodule.Quotient.mk_eq_zero (cE G)).mpr hw
    refine Submodule.mem_map.mpr ⟨b, hb, ?_⟩
    rw [← hbw, map_add, hw0, add_zero]
  rw [inf_comm, twelveOneK_map_inf h] at hmem
  exact (Submodule.Quotient.mk_eq_zero (cE G)).mp (by simpa using hmem)

end CFSG.LocalAnalysis.WeakClosure81
