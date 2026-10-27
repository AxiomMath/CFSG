module

public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerSplitStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] {K X Hb : Type} [Field K] [AddCommGroup X] [Module K X] [Group Hb]

structure IsLayerBridge (V W R : Subgroup G) (act : Hb →* (X ≃ₗ[K] X)) (f : G → X)
    (bar : ↥R → Hb) : Prop where
  V_le_W : V ≤ W
  f_mul : ∀ x ∈ W, ∀ y ∈ W, f (x * y) = f x + f y
  f_surj : ∀ v : X, ∃ x ∈ W, f x = v
  f_ker : ∀ x ∈ W, f x = 0 ↔ x ∈ V
  conj_W : ∀ r : ↥R, ∀ x ∈ W, (r : G) * x * (r : G)⁻¹ ∈ W
  conj_f : ∀ r : ↥R, ∀ x ∈ W, f ((r : G) * x * (r : G)⁻¹) = act (bar r) (f x)
  bar_surj : ∀ h : Hb, ∃ r : ↥R, bar r = h

namespace IsLayerBridge

variable {V W R : Subgroup G} {act : Hb →* (X ≃ₗ[K] X)} {f : G → X} {bar : ↥R → Hb}
  (hB : IsLayerBridge V W R act f bar)

include hB

theorem f_one : f 1 = 0 := by
  have h := hB.f_mul 1 W.one_mem 1 W.one_mem
  rw [one_mul] at h
  exact (add_eq_left.mp h.symm)

theorem f_inv {x : G} (hx : x ∈ W) : f x⁻¹ = -f x := by
  have h := hB.f_mul x hx x⁻¹ (W.inv_mem hx)
  rw [mul_inv_cancel, hB.f_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

@[expose] def pre (U : Submodule K X) : Subgroup G where
  carrier := {x | x ∈ W ∧ f x ∈ U}
  one_mem' := ⟨W.one_mem, by rw [hB.f_one]; exact U.zero_mem⟩
  mul_mem' := fun {x y} hx hy => ⟨W.mul_mem hx.1 hy.1, by
    rw [hB.f_mul x hx.1 y hy.1]; exact U.add_mem hx.2 hy.2⟩
  inv_mem' := fun {x} hx => ⟨W.inv_mem hx.1, by rw [hB.f_inv hx.1]; exact U.neg_mem hx.2⟩

theorem V_le_pre (U : Submodule K X) : V ≤ hB.pre U := fun x hx =>
  ⟨hB.V_le_W hx, by rw [(hB.f_ker x (hB.V_le_W hx)).mpr hx]; exact U.zero_mem⟩

theorem pre_le_W (U : Submodule K X) : hB.pre U ≤ W := fun _ hx => hx.1

theorem pre_ne_of_ne_bot {U : Submodule K X} (hU : U ≠ ⊥) : hB.pre U ≠ V := by
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  obtain ⟨x, hxW, rfl⟩ := hB.f_surj u
  intro h
  have hxV : x ∈ V := h ▸ (show x ∈ hB.pre U from ⟨hxW, huU⟩)
  exact hu0 ((hB.f_ker x hxW).mpr hxV)

theorem conj_pre {U : Submodule K X} (hU : IsInvSub act U) (r : G) (hr : r ∈ R) :
    conjSubgroup r (hB.pre U) = hB.pre U := by
  have key : ∀ s : ↥R, ∀ x ∈ hB.pre U, (s : G) * x * (s : G)⁻¹ ∈ hB.pre U := fun s x hx =>
    ⟨hB.conj_W s x hx.1, by rw [hB.conj_f s x hx.1]; exact hU _ _ hx.2⟩
  ext x
  rw [mem_conjSubgroup]
  constructor
  · intro hx
    have := key ⟨r, hr⟩ _ hx
    simpa [mul_assoc] using this
  · intro hx
    have := key ⟨r⁻¹, R.inv_mem hr⟩ x hx
    simpa [mul_assoc] using this

variable [Finite G]

theorem card_pre (U : Submodule K X) : Nat.card (hB.pre U) = Nat.card V * Nat.card U := by
  classical
  let F : ↥(hB.pre U) →* Multiplicative ↥U :=
    { toFun := fun x => Multiplicative.ofAdd ⟨f x, x.2.2⟩
      map_one' := by
        apply Multiplicative.toAdd.injective
        exact Subtype.ext hB.f_one
      map_mul' := fun x y => by
        apply Multiplicative.toAdd.injective
        exact Subtype.ext (hB.f_mul x x.2.1 y y.2.1) }
  have hsurj : Function.Surjective F := by
    intro u
    obtain ⟨x, hxW, hx⟩ := hB.f_surj (Multiplicative.toAdd u : ↥U)
    refine ⟨⟨x, hxW, by rw [hx]; exact (Multiplicative.toAdd u).2⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    exact Subtype.ext hx
  have hker : F.ker = V.subgroupOf (hB.pre U) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have : f x = 0 := congrArg Subtype.val (congrArg Multiplicative.toAdd h)
      exact (hB.f_ker x x.2.1).mp this
    · intro h
      apply Multiplicative.toAdd.injective
      exact Subtype.ext ((hB.f_ker x x.2.1).mpr h)
  have e := QuotientGroup.quotientKerEquivOfSurjective F hsurj
  have h1 := Subgroup.card_mul_index F.ker
  rw [Subgroup.index, Nat.card_congr e.toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative ↥U ≃ ↥U), hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hB.V_le_pre U)).toEquiv] at h1
  exact h1.symm

@[expose] def fW : ↥W →* Multiplicative X where
  toFun x := Multiplicative.ofAdd (f x)
  map_one' := by
    show Multiplicative.ofAdd (f 1) = 1
    rw [hB.f_one]
    rfl
  map_mul' x y := by
    show Multiplicative.ofAdd (f (x * y)) = Multiplicative.ofAdd (f x) * Multiplicative.ofAdd (f y)
    rw [hB.f_mul x x.2 y y.2]
    rfl

theorem f_zpow {a : G} (ha : a ∈ W) (c : ℤ) : f (a ^ c) = c • f a := by
  have h := map_zpow hB.fW ⟨a, ha⟩ c
  have h' := congrArg Multiplicative.toAdd h
  simpa [fW] using h'

theorem exists_proj {U : Submodule K X} (hU : IsInvSub act U) (A' : Subgroup G) (hA'W : A' ≤ W)
    (hA'R : ∀ r ∈ R, conjSubgroup r A' = A') (hsup : hB.pre U ⊔ A' = W)
    (hinf : hB.pre U ⊓ A' = V) :
    ∃ p : X →+ X, (∀ v, p v ∈ U) ∧ (∀ u ∈ U, p u = u) ∧ ∀ h v, p (act h v) = act h (p v) := by
  classical
  let S : Set X := {v | ∃ a ∈ A', f a = v}
  let U' : Submodule ℤ X := Submodule.span ℤ S
  have hU'mem : ∀ v, v ∈ U' ↔ ∃ a ∈ A', f a = v := by
    intro v
    refine ⟨fun hv => ?_, fun hv => Submodule.subset_span hv⟩
    induction hv using Submodule.span_induction with
    | mem v hv => exact hv
    | zero => exact ⟨1, A'.one_mem, hB.f_one⟩
    | add v w _ _ hv hw =>
      obtain ⟨a, ha, rfl⟩ := hv
      obtain ⟨b, hb, rfl⟩ := hw
      exact ⟨a * b, A'.mul_mem ha hb, hB.f_mul a (hA'W ha) b (hA'W hb)⟩
    | smul c v _ hv =>
      obtain ⟨a, ha, rfl⟩ := hv
      exact ⟨a ^ c, A'.zpow_mem ha c, hB.f_zpow (hA'W ha) c⟩
  let U₀ : Submodule ℤ X := U.toAddSubgroup.toIntSubmodule
  have hU₀mem : ∀ v, v ∈ U₀ ↔ v ∈ U := fun v => Iff.rfl
  have hdisj : Disjoint U₀ U' := by
    rw [Submodule.disjoint_def]
    intro v hv hv'
    obtain ⟨a, ha, rfl⟩ := (hU'mem _).mp hv'
    have hapre : a ∈ hB.pre U := ⟨hA'W ha, (hU₀mem _).mp hv⟩
    have haV : a ∈ V := hinf ▸ (show a ∈ hB.pre U ⊓ A' from ⟨hapre, ha⟩)
    exact (hB.f_ker a (hA'W ha)).mpr haV
  have hcl : Subgroup.closure ((hB.pre U : Set G) ∪ A') ≤ W := by
    rw [← Subgroup.sup_eq_closure, hsup]
  have hgen : ∀ x ∈ Subgroup.closure ((hB.pre U : Set G) ∪ A'), f x ∈ U₀ ⊔ U' := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact Submodule.mem_sup_left ((hU₀mem _).mpr hx.2)
      · exact Submodule.mem_sup_right ((hU'mem _).mpr ⟨x, hx, rfl⟩)
    | one => rw [hB.f_one]; exact Submodule.zero_mem _
    | mul x y hx hy ihx ihy =>
      rw [hB.f_mul x (hcl hx) y (hcl hy)]
      exact Submodule.add_mem _ ihx ihy
    | inv x hx ihx =>
      rw [hB.f_inv (hcl hx)]
      exact Submodule.neg_mem _ ihx
  have hcodisj : Codisjoint U₀ U' := by
    rw [codisjoint_iff, eq_top_iff]
    intro v _
    obtain ⟨w, hwW, rfl⟩ := hB.f_surj v
    have hw : w ∈ Subgroup.closure ((hB.pre U : Set G) ∪ A') := by
      rw [← Subgroup.sup_eq_closure, hsup]
      exact hwW
    exact hgen w hw
  have hcompl : IsCompl U₀ U' := ⟨hdisj, hcodisj⟩
  let pZ : X →ₗ[ℤ] X := U₀.projection U' hcompl
  have hpU : ∀ v, pZ v ∈ U := fun v => (hU₀mem _).mp (Submodule.projection_apply_mem hcompl v)
  have hpid : ∀ u ∈ U, pZ u = u := fun u hu =>
    Submodule.projection_apply_of_mem_left hcompl ((hU₀mem u).mpr hu)
  have hp0 : ∀ v ∈ U', pZ v = 0 := fun v hv =>
    (Submodule.projection_apply_eq_zero_iff hcompl).mpr hv
  have hU'inv : ∀ h : Hb, ∀ v ∈ U', act h v ∈ U' := by
    intro h v hv
    obtain ⟨r, rfl⟩ := hB.bar_surj h
    obtain ⟨a, ha, rfl⟩ := (hU'mem _).mp hv
    rw [← hB.conj_f r a (hA'W ha)]
    refine (hU'mem _).mpr ⟨_, ?_, rfl⟩
    have := hA'R r r.2
    rw [← this]
    refine mem_conjSubgroup.mpr ?_
    simpa [mul_assoc] using ha
  refine ⟨pZ.toAddMonoidHom, hpU, hpid, fun h v => ?_⟩
  obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.mp (hcodisj.eq_top ▸ Submodule.mem_top :
    v ∈ U₀ ⊔ U')
  show pZ (act h (u + u')) = act h (pZ (u + u'))
  rw [map_add, map_add, map_add, hpid _ ((hU₀mem u).mp hu), hpid _ (hU _ _ ((hU₀mem u).mp hu)),
    hp0 _ hu', hp0 _ (hU'inv h _ hu')]
  simp only [add_zero]

end IsLayerBridge

end CFSG.RankThree.GF2n.Stroth80.S715L
