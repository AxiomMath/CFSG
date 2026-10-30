module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThreeRep

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup
open CFSG.RankThree.FFModules (fixSub mem_fixSub)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

attribute [local instance] Fintype.ofFinite

@[expose] def restrictRep (ρ : Representation (ZMod 2) G W) (W₂ : Submodule (ZMod 2) W)
    (h : ∀ g : G, ∀ w ∈ W₂, ρ g w ∈ W₂) : Representation (ZMod 2) G W₂ where
  toFun g := (ρ g).restrict (h g)
  map_one' := by
    ext w
    simp
  map_mul' g g' := by
    ext w
    simp

@[simp] theorem coe_restrictRep_apply (ρ : Representation (ZMod 2) G W)
    (W₂ : Submodule (ZMod 2) W) (h : ∀ g : G, ∀ w ∈ W₂, ρ g w ∈ W₂) (g : G) (w : W₂) :
    ((restrictRep ρ W₂ h g w : W₂) : W) = ρ g (w : W) :=
  rfl

@[expose] def commSpace (ρ : Representation (ZMod 2) G W) (Q : Subgroup G) :
    Submodule (ZMod 2) W :=
  ⨆ y ∈ Q, LinearMap.range (ρ y - 1)

private noncomputable def avg (ρ : Representation (ZMod 2) G W) (Q : Subgroup G) :
    W →ₗ[ZMod 2] W :=
  ∑ x : Q, ρ (x : G)

private lemma avg_apply (ρ : Representation (ZMod 2) G W) (Q : Subgroup G) (w : W) :
    avg ρ Q w = ∑ x : Q, ρ (x : G) w := by
  simp [avg]

private noncomputable def mulRightEquiv (Q : Subgroup G) (y : Q) : Q ≃ Q where
  toFun x := ⟨(x : G) * (y : G), Q.mul_mem x.2 y.2⟩
  invFun x := ⟨(x : G) * (y : G)⁻¹, Q.mul_mem x.2 (Q.inv_mem y.2)⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

theorem commSpace_inf_fixSub_eq_bot (ρ : Representation (ZMod 2) G W) {Q : Subgroup G}
    (hodd : Odd (Nat.card Q)) : commSpace ρ Q ⊓ fixSub ρ Q = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro w hw
  rw [Submodule.mem_inf] at hw
  obtain ⟨hwc, hwf⟩ := hw
  have hfix : avg ρ Q w = w := by
    rw [avg_apply]
    rw [show (∑ x : Q, ρ (x : G) w) = ∑ _ : Q, w from
      Finset.sum_congr rfl fun x _ => (mem_fixSub.mp hwf) (x : G) x.2]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      ← Nat.cast_smul_eq_nsmul (R := ZMod 2) (Nat.card Q) w,
      ZMod.natCast_eq_one_iff_odd.mpr hodd, one_smul]
  have hle : commSpace ρ Q ≤ LinearMap.ker (avg ρ Q) := by
    rw [commSpace]
    refine iSup₂_le ?_
    intro y hy
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    rw [avg_apply]
    have hreindex : ∑ x : Q, ρ ((x : G) * (y : G)) v = ∑ x : Q, ρ (x : G) v :=
      Equiv.sum_comp (mulRightEquiv Q ⟨y, hy⟩) (fun x : Q => ρ (x : G) v)
    calc ∑ x : Q, ρ (x : G) ((ρ y - 1) v)
        = ∑ x : Q, (ρ ((x : G) * (y : G)) v - ρ (x : G) v) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [LinearMap.sub_apply, map_sub, Module.End.one_apply,
            ← Module.End.mul_apply, ← map_mul]
      _ = (∑ x : Q, ρ ((x : G) * (y : G)) v) - ∑ x : Q, ρ (x : G) v := by
          rw [Finset.sum_sub_distrib]
      _ = 0 := by rw [hreindex, sub_self]
  have hker : avg ρ Q w = 0 := hle hwc
  rw [hfix] at hker
  exact hker

theorem map_mem_commSpace (ρ : Representation (ZMod 2) G W) {Q : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) {w : W} (hw : w ∈ commSpace ρ Q) :
    ρ g w ∈ commSpace ρ Q := by
  have hy' : ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  have hmap : Submodule.map (ρ g) (commSpace ρ Q) ≤ commSpace ρ Q := by
    rw [commSpace]
    simp only [Submodule.map_iSup]
    refine iSup₂_le ?_
    intro y hy
    have hsub : Submodule.map (ρ g) (LinearMap.range (ρ y - 1)) ≤
        LinearMap.range (ρ (g * y * g⁻¹) - 1) := by
      rintro _ ⟨v, hv, rfl⟩
      obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hv
      refine LinearMap.mem_range.mpr ⟨ρ g z, ?_⟩
      have hgy : (g * y * g⁻¹) * g = g * y := by group
      calc (ρ (g * y * g⁻¹) - 1) (ρ g z)
          = ρ (g * y * g⁻¹) (ρ g z) - ρ g z := by
            rw [LinearMap.sub_apply, Module.End.one_apply]
        _ = ρ ((g * y * g⁻¹) * g) z - ρ g z := by
            rw [← Module.End.mul_apply, ← map_mul]
        _ = ρ (g * y) z - ρ g z := by rw [hgy]
        _ = ρ g (ρ y z) - ρ g z := by rw [map_mul, Module.End.mul_apply]
        _ = ρ g ((ρ y - 1) z) := by
            rw [LinearMap.sub_apply, map_sub, Module.End.one_apply]
    exact hsub.trans (le_iSup₂ (f := fun y (_ : y ∈ Q) => LinearMap.range (ρ y - 1))
      (g * y * g⁻¹) (hy' y hy))
  exact hmap (Submodule.mem_map_of_mem hw)

theorem forall_map_mem_of_sup_zpowers_eq_top (ρ : Representation (ZMod 2) G W) {Q : Subgroup G}
    {u : G} (hu : u * u = 1) (hgen : Q ⊔ Subgroup.zpowers u = ⊤) {W' : Submodule (ZMod 2) W}
    (hQ : ∀ x ∈ Q, ∀ w ∈ W', ρ x w ∈ W') (hu' : ∀ w ∈ W', ρ u w ∈ W') :
    ∀ g : G, ∀ w ∈ W', ρ g w ∈ W' := by
  let K : Subgroup G :=
    { carrier := {g : G | ∀ w ∈ W', ρ g w ∈ W' ∧ ρ g⁻¹ w ∈ W'}
      mul_mem' := by
        intro a b ha hb w hw
        refine ⟨?_, ?_⟩
        · rw [map_mul, Module.End.mul_apply]
          exact (ha _ (hb w hw).1).1
        · rw [mul_inv_rev, map_mul, Module.End.mul_apply]
          exact (hb _ (ha w hw).2).2
      one_mem' := by
        intro w hw
        exact ⟨by simpa using hw, by simpa using hw⟩
      inv_mem' := by
        intro a ha w hw
        exact ⟨(ha w hw).2, by simpa using (ha w hw).1⟩ }
  have hQK : Q ≤ K := by
    intro x hx w hw
    exact ⟨hQ x hx w hw, hQ x⁻¹ (Q.inv_mem hx) w hw⟩
  have huK : u ∈ K := by
    intro w hw
    refine ⟨hu' w hw, ?_⟩
    rw [inv_eq_of_mul_eq_one_right hu]
    exact hu' w hw
  have htop : K = ⊤ := by
    apply le_antisymm le_top
    rw [← hgen]
    exact sup_le hQK (Subgroup.zpowers_le.mpr huK)
  intro g w hw
  have hgK : g ∈ K := by rw [htop]; exact Subgroup.mem_top g
  exact (hgK w hw).1

private def Good (ρ : Representation (ZMod 2) G W) (Q : Subgroup G) (u : G)
    (X : Submodule (ZMod 2) W) : Prop :=
  X ≤ commSpace ρ Q ∧ X ≠ ⊥ ∧
    (∀ x ∈ Q, ∀ w ∈ X, ρ x w ∈ X) ∧ (∀ w ∈ X, ρ u w ∈ X)

theorem exists_irreducible_le_commSpace (ρ : Representation (ZMod 2) G W) {Q : Subgroup G}
    {u : G} (hu : u * u = 1) (hu' : u ∈ Subgroup.normalizer (Q : Set G))
    (hgen : Q ⊔ Subgroup.zpowers u = ⊤) (hne : commSpace ρ Q ≠ ⊥) :
    ∃ (W₂ : Submodule (ZMod 2) W) (hW₂ : ∀ g : G, ∀ w ∈ W₂, ρ g w ∈ W₂),
      W₂ ≤ commSpace ρ Q ∧ Nontrivial W₂ ∧
      (∀ W' : Submodule (ZMod 2) W₂, (∀ x ∈ Q, ∀ w ∈ W', restrictRep ρ W₂ hW₂ x w ∈ W') →
        (∀ w ∈ W', restrictRep ρ W₂ hW₂ u w ∈ W') → W' = ⊥ ∨ W' = ⊤) := by
  classical
  have hcommGood : Good ρ Q u (commSpace ρ Q) := by
    refine ⟨le_rfl, hne, ?_, ?_⟩
    · intro x hx w hw
      exact map_mem_commSpace ρ (Subgroup.le_normalizer hx) hw
    · intro w hw
      exact map_mem_commSpace ρ hu' hw
  have hP : ∃ n, ∃ X, Good ρ Q u X ∧ Nat.card X = n := ⟨_, _, hcommGood, rfl⟩
  obtain ⟨W₂, hW₂good, hW₂card⟩ := Nat.find_spec hP
  have hW₂ : ∀ g : G, ∀ w ∈ W₂, ρ g w ∈ W₂ :=
    forall_map_mem_of_sup_zpowers_eq_top ρ hu hgen hW₂good.2.2.1 hW₂good.2.2.2
  refine ⟨W₂, hW₂, hW₂good.1, Submodule.nontrivial_iff_ne_bot.mpr hW₂good.2.1, ?_⟩
  intro W' hQ' hu''
  by_cases hbot : W' = ⊥
  · exact Or.inl hbot
  · refine Or.inr ?_
    let X : Submodule (ZMod 2) W := W'.map W₂.subtype
    have hsub : X ≤ W₂ := Submodule.map_subtype_le (p := W₂) W'
    have hXle : X ≤ commSpace ρ Q := hsub.trans hW₂good.1
    have hXne : X ≠ ⊥ := by
      intro hXbot
      apply hbot
      have hinj : Function.Injective (Submodule.map W₂.subtype) :=
        Submodule.map_injective_of_injective (f := W₂.subtype)
          (Submodule.injective_subtype W₂)
      have h : W'.map W₂.subtype = (⊥ : Submodule (ZMod 2) W₂).map W₂.subtype := by
        rw [Submodule.map_bot]
        exact hXbot
      exact hinj h
    have hXgood : Good ρ Q u X := by
      refine ⟨hXle, hXne, ?_, ?_⟩
      · intro x hx w hw
        rw [Submodule.mem_map] at hw ⊢
        obtain ⟨v, hv, rfl⟩ := hw
        exact ⟨restrictRep ρ W₂ hW₂ x v, hQ' x hx v hv, by simp⟩
      · intro w hw
        rw [Submodule.mem_map] at hw ⊢
        obtain ⟨v, hv, rfl⟩ := hw
        exact ⟨restrictRep ρ W₂ hW₂ u v, hu'' v hv, by simp⟩
    have hcardX : Nat.card X ≤ Nat.card W₂ := by
      change (X : Set W).ncard ≤ (W₂ : Set W).ncard
      exact Set.ncard_le_ncard hsub
    have hcardW : Nat.card W₂ ≤ Nat.card X := by
      have := Nat.find_min' hP ⟨X, hXgood, rfl⟩
      rwa [← hW₂card] at this
    have hcard : Nat.card X = Nat.card W₂ := le_antisymm hcardX hcardW
    have hXeq : X = W₂ := by
      have hset : (X : Set W) = (W₂ : Set W) := by
        refine Set.eq_of_subset_of_ncard_le hsub ?_
        change (W₂ : Set W).ncard ≤ (X : Set W).ncard
        exact hcardW
      exact Submodule.ext fun x => by
        show x ∈ (X : Set W) ↔ x ∈ (W₂ : Set W)
        rw [hset]
    have hmap_eq : W'.map W₂.subtype = (⊤ : Submodule (ZMod 2) W₂).map W₂.subtype := by
      rw [Submodule.map_subtype_top]
      exact hXeq
    exact Submodule.map_injective_of_injective (f := W₂.subtype)
      (Submodule.injective_subtype W₂) hmap_eq

theorem PInvol.exists_irreducible_restriction (ρ : Representation (ZMod 2) G W) {p : ℕ}
    {Q : Subgroup G} {u : G} (h : PInvol p Q u) (hgen : Q ⊔ Subgroup.zpowers u = ⊤)
    (hQ : Q ≠ ⊥) (hne : traceSpace ρ u ≠ ⊥)
    (hTI : ∀ y ∈ Q, traceSpace ρ u ⊓ (traceSpace ρ u).map (ρ y) ≠ ⊥ → y * u = u * y) :
    ∃ (W₂ : Submodule (ZMod 2) W) (hW₂ : ∀ g : G, ∀ w ∈ W₂, ρ g w ∈ W₂),
      Nontrivial W₂ ∧
      (∀ W' : Submodule (ZMod 2) W₂, (∀ x ∈ Q, ∀ w ∈ W', restrictRep ρ W₂ hW₂ x w ∈ W') →
        (∀ w ∈ W', restrictRep ρ W₂ hW₂ u w ∈ W') → W' = ⊥ ∨ W' = ⊤) ∧
      traceSpace (restrictRep ρ W₂ hW₂) u ≠ ⊥ ∧
      (∀ y ∈ Q, traceSpace (restrictRep ρ W₂ hW₂) u ⊓
        (traceSpace (restrictRep ρ W₂ hW₂) u).map (restrictRep ρ W₂ hW₂ y) ≠ ⊥ →
          y * u = u * y) := by
  classical
  have hodd : Odd (Nat.card Q) := by
    haveI : Fact p.Prime := ⟨h.prime⟩
    have hQp : IsPGroup p Q := fun x =>
      ⟨1, by
        rw [pow_one]
        exact Subtype.ext (by simpa using h.exp (x : G) x.2)⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := Q)).mp hQp
    rw [hn]
    exact (h.prime.eq_two_or_odd'.resolve_left h.odd).pow
  have hcomm_ne : commSpace ρ Q ≠ ⊥ := by
    by_contra hbot
    have hall : ∀ y ∈ Q, ρ y = 1 := by
      intro y hy
      by_contra hy1
      have hrange : LinearMap.range (ρ y - 1) ≠ ⊥ := by
        intro hsub
        rw [LinearMap.range_eq_bot] at hsub
        exact hy1 (sub_eq_zero.mp hsub)
      have hle : LinearMap.range (ρ y - 1) ≤ commSpace ρ Q :=
        le_iSup₂ (f := fun y (_ : y ∈ Q) => LinearMap.range (ρ y - 1)) y hy
      exact hrange (eq_bot_iff.mpr (hle.trans (le_of_eq hbot)))
    have hcent : Q ≤ Subgroup.centralizer (Subgroup.zpowers u : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      have hcomm : Commute y u := by
        have hmap : (traceSpace ρ u).map (ρ y) = traceSpace ρ u := by
          rw [hall y hy]
          change Submodule.map (LinearMap.id : W →ₗ[ZMod 2] W) (traceSpace ρ u) =
            traceSpace ρ u
          have hmid : Submodule.map (LinearMap.id : W →ₗ[ZMod 2] W) (traceSpace ρ u) =
              traceSpace ρ u := Submodule.map_id (traceSpace ρ u)
          exact hmid
        have hinf : traceSpace ρ u ⊓ (traceSpace ρ u).map (ρ y) ≠ ⊥ := by
          rw [hmap, inf_idem]
          exact hne
        exact hTI y hy hinf
      exact (hcomm.zpow_right k).symm
    have hcomm_bot : ⁅Q, Subgroup.zpowers u⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent
    exact hQ (le_bot_iff.mp (h.le_commutator.trans (le_of_eq hcomm_bot)))
  obtain ⟨W₂, hW₂, hW₂le, hW₂nt, hW₂irr⟩ :=
    exists_irreducible_le_commSpace ρ h.sq_eq_one h.mem_normalizer hgen hcomm_ne
  have hntQ : ∃ y ∈ Q, ∃ w ∈ W₂, ρ y w ≠ w := by
    by_contra hcon
    push Not at hcon
    have hfix : W₂ ≤ fixSub ρ Q := by
      intro w hw
      rw [mem_fixSub]
      intro y hy
      exact hcon y hy w hw
    have hW₂bot : W₂ = ⊥ := by
      have : W₂ ≤ commSpace ρ Q ⊓ fixSub ρ Q := le_inf hW₂le hfix
      rw [commSpace_inf_fixSub_eq_bot (Q := Q) ρ hodd] at this
      exact le_bot_iff.mp this
    exact Submodule.nontrivial_iff_ne_bot.mp hW₂nt hW₂bot
  have hne₂ : traceSpace (restrictRep ρ W₂ hW₂) u ≠ ⊥ := by
    by_contra hbot
    have hbot' : LinearMap.range (restrictRep ρ W₂ hW₂ u - 1) = ⊥ := by
      simpa [traceSpace] using hbot
    have hzero : restrictRep ρ W₂ hW₂ u - 1 = 0 := LinearMap.range_eq_bot.mp hbot'
    have hu_fix : ∀ w : W₂, restrictRep ρ W₂ hW₂ u w = w := by
      intro w
      have h1 : (restrictRep ρ W₂ hW₂ u - 1) w = 0 := by rw [hzero]; simp
      rw [LinearMap.sub_apply, Module.End.one_apply] at h1
      exact sub_eq_zero.mp h1
    have hu1 : restrictRep ρ W₂ hW₂ u = 1 := by
      apply LinearMap.ext
      intro w
      rw [Module.End.one_apply]
      exact hu_fix w
    let K : Subgroup G :=
      { carrier := {g : G | ∀ w ∈ W₂, ρ g w = w}
        mul_mem' := by
          intro a b ha hb w hw
          rw [map_mul, Module.End.mul_apply, hb w hw]
          exact ha w hw
        one_mem' := by
          intro w hw
          simp
        inv_mem' := by
          intro a ha w hw
          calc ρ a⁻¹ w = ρ a⁻¹ (ρ a w) := by rw [ha w hw]
            _ = ρ (a⁻¹ * a) w := by rw [← Module.End.mul_apply, ← map_mul]
            _ = w := by simp }
    have hcommK : ⁅Q, Subgroup.zpowers u⁆ ≤ K := by
      rw [Subgroup.commutator_le]
      intro a ha v hv w hw
      have haa : restrictRep ρ W₂ hW₂ a * restrictRep ρ W₂ hW₂ a⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      have hC : ∀ g ∈ Subgroup.zpowers u, restrictRep ρ W₂ hW₂ g = 1 := by
        intro g hg
        let C : Subgroup G :=
          { carrier := {x : G | restrictRep ρ W₂ hW₂ x = 1}
            mul_mem' := by
              intro a b ha hb
              change restrictRep ρ W₂ hW₂ (a * b) = 1
              rw [map_mul, show restrictRep ρ W₂ hW₂ a = 1 from ha,
                show restrictRep ρ W₂ hW₂ b = 1 from hb, one_mul]
            one_mem' := by
              change restrictRep ρ W₂ hW₂ 1 = 1
              exact map_one (restrictRep ρ W₂ hW₂)
            inv_mem' := by
              intro a ha
              change restrictRep ρ W₂ hW₂ a⁻¹ = 1
              have h : restrictRep ρ W₂ hW₂ a * restrictRep ρ W₂ hW₂ a⁻¹ = 1 := by
                rw [← map_mul, mul_inv_cancel, map_one]
              rw [show restrictRep ρ W₂ hW₂ a = 1 from ha, one_mul] at h
              exact h }
        exact Subgroup.zpowers_le.mpr (show u ∈ C from hu1) hg
      have hv1 : restrictRep ρ W₂ hW₂ v = 1 := hC v hv
      have hv1' : restrictRep ρ W₂ hW₂ v⁻¹ = 1 :=
        hC v⁻¹ ((Subgroup.zpowers u).inv_mem hv)
      have hcomm1 : restrictRep ρ W₂ hW₂ ⁅a, v⁆ = 1 := by
        rw [commutatorElement_def, map_mul, map_mul, map_mul]
        simp only [hv1, hv1', mul_one, one_mul]
        exact haa
      have h2 := congrArg (fun f : W₂ →ₗ[ZMod 2] W₂ => f ⟨w, hw⟩) hcomm1
      have h := congrArg (Subtype.val) h2
      simpa using h
    have hQK : Q ≤ K := h.le_commutator.trans hcommK
    obtain ⟨y, hy, w, hw, hyw⟩ := hntQ
    exact hyw (hQK hy w hw)
  refine ⟨W₂, hW₂, hW₂nt, hW₂irr, hne₂, ?_⟩
  intro y hy hneTI
  rw [Submodule.ne_bot_iff] at hneTI
  obtain ⟨t, ht, ht0⟩ := hneTI
  rw [Submodule.mem_inf] at ht
  obtain ⟨htT, htmap⟩ := ht
  rw [Submodule.mem_map] at htmap
  obtain ⟨t', ht'T, ht'eq⟩ := htmap
  have htT' : t ∈ LinearMap.range ((restrictRep ρ W₂ hW₂) u - 1) := by
    simpa [traceSpace] using htT
  obtain ⟨w₀, hw₀⟩ := LinearMap.mem_range.mp htT'
  have htW : (t : W) ∈ traceSpace ρ u := by
    rw [traceSpace]
    refine LinearMap.mem_range.mpr ⟨(w₀ : W), ?_⟩
    have h := congrArg (Subtype.val) hw₀
    simpa [LinearMap.sub_apply] using h
  have ht'map : (t : W) ∈ (traceSpace ρ u).map (ρ y) := by
    rw [Submodule.mem_map]
    refine ⟨(t' : W), ?_, ?_⟩
    · have ht'T' : t' ∈ LinearMap.range ((restrictRep ρ W₂ hW₂) u - 1) := by
        simpa [traceSpace] using ht'T
      obtain ⟨v₀, hv₀⟩ := LinearMap.mem_range.mp ht'T'
      exact LinearMap.mem_range.mpr ⟨(v₀ : W), by
        have h := congrArg (Subtype.val) hv₀
        simpa [LinearMap.sub_apply] using h⟩
    · have h := congrArg (Subtype.val) ht'eq
      simpa using h
  have hinf : traceSpace ρ u ⊓ (traceSpace ρ u).map (ρ y) ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨(t : W), Submodule.mem_inf.mpr ⟨htW, ht'map⟩,
      fun hzero => ht0 (Subtype.ext hzero)⟩
  exact hTI y hy hinf

end CFSG.LocalAnalysis.WeakClosure81
