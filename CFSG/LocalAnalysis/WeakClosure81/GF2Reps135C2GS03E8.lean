module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2GS03E8Inner
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2GS03E8Outer
import CFSG.LocalAnalysis.SeitzReduction.E8PilotUniqueFieldStep3
public import CFSG.LieType.Chevalley.OddF4CosetDescent

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.SeitzReduction.E8Pilot

section Supplier

theorem gs03Alpha_e8_inner {G : Type} [Group G] {S : Subgroup G} {n f : ℕ}
    (hlie : LieModel ↥S .E8 n 2 f) {x : G} (hx : orderOf x = 2) (hxS : x ∈ S) :
    ∃ T : Finset G, T.card ≤ 11 ∧ (∀ y ∈ T, ∃ s ∈ S, y = s * x * s⁻¹) ∧
      S ≤ Subgroup.closure (T : Set G) := by
  classical
  obtain ⟨hadm, hun⟩ := hlie.chevalleyExceptionalModel (by decide)
  obtain ⟨K, _, _, hK, ⟨e0⟩⟩ := hun
  have hf : 1 ≤ f := hadm.2.1
  have hKC : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hf hK
  let e : ↥S ≃* adjointGroup .E8 K := e0.trans
    ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E8) (K := K))).trans
        QuotientGroup.quotientBot)
  let t : adjointGroup .E8 K := e ⟨x, hxS⟩
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have ht2 : t ^ 2 = 1 := by
    change e ⟨x, hxS⟩ ^ 2 = 1
    rw [← map_pow, show (⟨x, hxS⟩ : ↥S) ^ 2 = 1 by exact Subtype.ext hx2, map_one]
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    exact absurd hx (by decide)
  have ht1 : t ≠ 1 := by
    intro h
    apply hx1
    have h' : (⟨x, hxS⟩ : ↥S) = 1 := by
      simpa [t] using congrArg (fun y => e.symm y) h
    simpa using congrArg Subtype.val h'
  obtain ⟨L, hLcard, hLtop⟩ := GS03E8.exists_closure_conj_eq_top ht2 ht1
  let fG : adjointGroup .E8 K →* G := S.subtype.comp e.symm.toMonoidHom
  have hrange : fG.range = S := by
    ext g
    constructor
    · rintro ⟨s, rfl⟩
      exact (e.symm s).2
    · intro hg
      exact ⟨e ⟨g, hg⟩, by simp [fG]⟩
  let T : Finset G := (L.map fun s =>
    ((e.symm s : ↥S) : G) * x * ((e.symm s : ↥S) : G)⁻¹).toFinset
  have hTmem : ∀ y ∈ T, ∃ s ∈ S, y = s * x * s⁻¹ := by
    intro y hy
    rw [show T = _ from rfl, List.mem_toFinset] at hy
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hy
    exact ⟨((e.symm s : ↥S) : G), (e.symm s).2, rfl⟩
  have hsub : fG '' {y | ∃ s ∈ L, y = s * t * s⁻¹} ⊆ (T : Set G) := by
    rintro z ⟨a, ⟨s, hs, rfl⟩, rfl⟩
    refine List.mem_toFinset.mpr (List.mem_map.mpr ⟨s, hs, ?_⟩)
    simp [fG, t]
  have hclosure : Subgroup.closure (fG '' {y | ∃ s ∈ L, y = s * t * s⁻¹}) = S := by
    have hmap := MonoidHom.map_closure fG {y | ∃ s ∈ L, y = s * t * s⁻¹}
    rw [hLtop, Subgroup.map_top, hrange] at hmap
    exact hmap.symm
  refine ⟨T, ?_, hTmem, ?_⟩
  · calc T.card ≤ (L.map fun s =>
        ((e.symm s : ↥S) : G) * x * ((e.symm s : ↥S) : G)⁻¹).length := List.toFinset_card_le _
      _ = L.length := List.length_map _
      _ ≤ 11 := hLcard
  · rw [← hclosure]
    exact Subgroup.closure_mono hsub


theorem gs03Alpha_e8_outer {G : Type} [Group G] {S : Subgroup G} (hS : S.Normal)
    (hC : Subgroup.centralizer (S : Set G) = ⊥) {n f : ℕ} (hlie : LieModel ↥S .E8 n 2 f)
    {x : G} (hx : orderOf x = 2) (hxS : x ∉ S) :
    ∃ T : Finset G, T.card ≤ 11 ∧ (∀ y ∈ T, ∃ s ∈ S, y = s * x * s⁻¹) ∧
      S ≤ Subgroup.closure (T : Set G) := by
  classical
  obtain ⟨hadm, hun⟩ := hlie.chevalleyExceptionalModel (by decide)
  obtain ⟨K, _, _, hK, ⟨e0⟩⟩ := hun
  have hf : 1 ≤ f := hadm.2.1
  have hKC : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hf hK
  let e : ↥S ≃* adjointGroup .E8 K := e0.trans
    ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E8) (K := K))).trans
        QuotientGroup.quotientBot)
  let φ : G →* MulAut ↥S := MulAut.conjNormal (H := S)
  let α : MulAut (adjointGroup .E8 K) := e.symm.trans ((φ x).trans e)
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx22 : x * x = 1 := by rw [← pow_two, hx2]
  have hα_apply : ∀ y : adjointGroup .E8 K,
      ((e.symm (α y) : ↥S) : G) = x * ((e.symm y : ↥S) : G) * x⁻¹ := by
    intro y
    have h1 : e.symm (α y) = φ x (e.symm y) := by simp [α]
    rw [h1, MulAut.conjNormal_apply]
  have hα2 : α ^ 2 = 1 := by
    refine MulEquiv.ext fun y => ?_
    have h1 := hα_apply (α y)
    have h2 := hα_apply y
    have h3 : ((e.symm (α (α y)) : ↥S) : G) = ((e.symm y : ↥S) : G) := by
      rw [h1, h2]
      calc x * (x * ((e.symm y : ↥S) : G) * x⁻¹) * x⁻¹
          = (x * x) * ((e.symm y : ↥S) : G) * (x⁻¹ * x⁻¹) := by group
        _ = ((e.symm y : ↥S) : G) := by
          have hxinv : x⁻¹ * x⁻¹ = 1 := by
            rw [show x⁻¹ * x⁻¹ = (x * x)⁻¹ by group, hx22, inv_one]
          rw [hx22, hxinv, one_mul, mul_one]
    have h4 : e.symm (α (α y)) = e.symm y := Subtype.ext h3
    simpa [pow_two, MulAut.mul_apply, MulAut.one_apply] using e.symm.injective h4
  have hαo : α ∉ (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range := by
    rintro ⟨g, hg⟩
    have hcentral : ((e.symm g : ↥S) : G)⁻¹ * x ∈ Subgroup.centralizer (S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      set y : adjointGroup .E8 K := e ⟨s, hs⟩ with hydef
      have hy : ((e.symm y : ↥S) : G) = s := by simp [y]
      have hαy : α y = g * y * g⁻¹ := by
        rw [← hg]
        exact MulAut.conj_apply g y
      have h := hα_apply y
      rw [hαy] at h
      have h2 : ((e.symm (g * y * g⁻¹) : ↥S) : G) =
          ((e.symm g : ↥S) : G) * s * ((e.symm g : ↥S) : G)⁻¹ := by
        simp [hy]
      rw [h2, hy] at h
      calc s * (((e.symm g : ↥S) : G)⁻¹ * x)
          = ((e.symm g : ↥S) : G)⁻¹ *
              (((e.symm g : ↥S) : G) * s * ((e.symm g : ↥S) : G)⁻¹) * x := by group
        _ = ((e.symm g : ↥S) : G)⁻¹ * (x * s * x⁻¹) * x := by rw [← h]
        _ = (((e.symm g : ↥S) : G)⁻¹ * x) * s := by group
    have h1 : ((e.symm g : ↥S) : G)⁻¹ * x = 1 := by
      rw [hC] at hcentral
      exact Subgroup.mem_bot.1 hcentral
    apply hxS
    have hxeq : x = ((e.symm g : ↥S) : G) := by
      calc x = ((e.symm g : ↥S) : G) * (((e.symm g : ↥S) : G)⁻¹ * x) := by group
        _ = ((e.symm g : ↥S) : G) * 1 := by rw [h1]
        _ = ((e.symm g : ↥S) : G) := mul_one _
    rw [hxeq]
    exact (e.symm g).2
  let i0 : Fin Tag.E8.rank := ⟨0, by decide⟩
  obtain ⟨g, ι, hι2, hι1, hαeq⟩ := exists_eq_conj_mul_of_outer_E8 (K := K) hf hK hα2 hαo
  obtain ⟨δ, hδ⟩ := ι.2
  let ii : MulAut (adjointGroup .E8 K) := entrywiseAdjointAut .E8 δ
  have hι2' : (ι : MulAut (adjointGroup .E8 K)) ^ 2 = 1 := by
    simpa using congrArg Subtype.val hι2
  have hsq : (entrywiseAdjointAutHom (τ := .E8) (K := K) δ) ^ 2 = 1 := by
    rw [hδ]
    exact hι2'
  have hδ22 : entrywiseAdjointAut .E8 (δ ^ 2) = 1 := by
    change (entrywiseAdjointAutHom (τ := .E8) (K := K)) (δ ^ 2) = 1
    rw [map_pow, hsq]
  have hδ2 : ∀ c, δ (δ c) = c := by
    intro c
    let g0 : adjointGroup .E8 K := ⟨pinnedX .E8 K (Pi.single i0 1) c,
      pinnedX_mem_adjointGroup (Pi.single i0 1) c⟩
    have h1 : entrywiseAdjointAut .E8 (δ ^ 2) g0 = g0 := by rw [hδ22]; rfl
    have h2 : ((entrywiseAdjointAut .E8 (δ ^ 2) g0 : ModGL .E8 K) :
        Module.End K (RootModule .E8 K)) = ((g0 : ModGL .E8 K) :
        Module.End K (RootModule .E8 K)) :=
      congrArg (fun u : adjointGroup .E8 K =>
        ((u : ModGL .E8 K) : Module.End K (RootModule .E8 K))) h1
    rw [coe_entrywiseAdjointAut] at h2
    have h3 : entrywise (δ ^ 2).toRingHom
        (pinnedX .E8 K (Pi.single i0 1) c : Module.End K (RootModule .E8 K)) =
        (pinnedX .E8 K (Pi.single i0 1) c : Module.End K (RootModule .E8 K)) := by
      simpa [g0, entrywiseHom] using h2
    rw [entrywise_pinnedX] at h3
    have h4 : (pinnedX .E8 K (Pi.single i0 1) ((δ ^ 2) c) : ModGL .E8 K) =
        pinnedX .E8 K (Pi.single i0 1) c := Units.ext h3
    have h5 : (δ ^ 2) c = c := pinnedX_injective .E8 K (Pi.single i0 1) h4
    simpa [pow_two] using h5
  have hδ1 : ∃ c, δ c ≠ c := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hι1
    apply Subtype.ext
    rw [← hδ]
    have hδeq : δ = 1 := RingEquiv.ext h
    rw [hδeq, map_one]
    rfl
  obtain ⟨L, hLcard, hLtop⟩ :=
    GS03E8.exists_closure_twist_eq_top hδ2 hδ1
  have hiiι : ii = (ι : MulAut (adjointGroup .E8 K)) := hδ
  have key : ∀ s : adjointGroup .E8 K,
      ((e.symm (g * s * g⁻¹) : ↥S) : G) * x * ((e.symm (g * s * g⁻¹) : ↥S) : G)⁻¹ =
      ((e.symm (g * (s * (ii s)⁻¹) * g⁻¹) : ↥S) : G) * x := by
    intro s
    have hαconj : ∀ w : adjointGroup .E8 K,
        α w = g * ii (g⁻¹ * w * g) * g⁻¹ := by
      intro w
      rw [hαeq, ← hiiι]
      simp only [MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_apply, MulAut.conj_symm_apply]
    have hαw : α (g * s⁻¹ * g⁻¹) = g * (ii s)⁻¹ * g⁻¹ := by
      rw [hαconj]
      rw [show g⁻¹ * (g * s⁻¹ * g⁻¹) * g = s⁻¹ by group]
      rw [map_inv]
    have hyinv : ((e.symm (g * s * g⁻¹) : ↥S) : G)⁻¹ =
        ((e.symm (g * s⁻¹ * g⁻¹) : ↥S) : G) := by
      rw [← Subgroup.coe_inv, ← map_inv]
      rfl
    have hxz : x * ((e.symm (g * s⁻¹ * g⁻¹) : ↥S) : G) * x⁻¹ =
        ((e.symm (g * (ii s)⁻¹ * g⁻¹) : ↥S) : G) := by
      rw [← hα_apply (g * s⁻¹ * g⁻¹)]
      exact congrArg (fun y => ((e.symm y : ↥S) : G)) hαw
    calc ((e.symm (g * s * g⁻¹) : ↥S) : G) * x * ((e.symm (g * s * g⁻¹) : ↥S) : G)⁻¹
        = ((e.symm (g * s * g⁻¹) : ↥S) : G) *
            (x * ((e.symm (g * s⁻¹ * g⁻¹) : ↥S) : G) * x⁻¹) * x := by
          rw [hyinv]; group
      _ = ((e.symm (g * s * g⁻¹) : ↥S) : G) *
            ((e.symm (g * (ii s)⁻¹ * g⁻¹) : ↥S) : G) * x := by
          rw [hxz]
      _ = ((e.symm (g * (s * (ii s)⁻¹) * g⁻¹) : ↥S) : G) * x := by
          rw [← Subgroup.coe_mul, ← map_mul]
          exact congrArg (fun y => ((e.symm y : ↥S) : G) * x) (by group)
  let T : Finset G := insert x (L.map fun s =>
    ((e.symm (g * s * g⁻¹) : ↥S) : G) * x * ((e.symm (g * s * g⁻¹) : ↥S) : G)⁻¹).toFinset
  have hTmem : ∀ y ∈ T, ∃ s ∈ S, y = s * x * s⁻¹ := by
    intro y hy
    rw [show T = insert x (L.map fun s =>
      ((e.symm (g * s * g⁻¹) : ↥S) : G) * x * ((e.symm (g * s * g⁻¹) : ↥S) : G)⁻¹).toFinset
        from rfl, Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact ⟨1, S.one_mem, by group⟩
    · rw [List.mem_toFinset] at hy
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 hy
      exact ⟨((e.symm (g * s * g⁻¹) : ↥S) : G), (e.symm (g * s * g⁻¹)).2, rfl⟩
  let H : Subgroup G := Subgroup.closure (T : Set G)
  have hxH : x ∈ H := Subgroup.subset_closure (by
    rw [show T = insert x _ from rfl, Finset.mem_coe, Finset.mem_insert]
    exact Or.inl rfl)
  have hB : ∀ s ∈ L,
      ((e.symm (g * (s * (ii s)⁻¹) * g⁻¹) : ↥S) : G) ∈ H := by
    intro s hs
    have h1 : ((e.symm (g * s * g⁻¹) : ↥S) : G) * x *
        ((e.symm (g * s * g⁻¹) : ↥S) : G)⁻¹ ∈ H := by
      apply Subgroup.subset_closure
      rw [show T = insert x _ from rfl, Finset.mem_coe, Finset.mem_insert]
      right
      rw [List.mem_toFinset]
      exact List.mem_map.mpr ⟨s, hs, rfl⟩
    have h2 : ((e.symm (g * s * g⁻¹) : ↥S) : G) * x *
        ((e.symm (g * s * g⁻¹) : ↥S) : G)⁻¹ * x ∈ H := H.mul_mem h1 hxH
    rw [key s] at h2
    rw [mul_assoc, hx22, mul_one] at h2
    exact h2
  let ψ : adjointGroup .E8 K →* G :=
    S.subtype.comp (e.symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom)
  have hψ_apply : ∀ z : adjointGroup .E8 K,
      ψ z = ((e.symm (g * z * g⁻¹) : ↥S) : G) := by
    intro z
    simp [ψ, MulAut.conj_apply]
  have hψrange : ψ.range = S := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact (e.symm (g * z * g⁻¹)).2
    · intro hy
      refine ⟨g⁻¹ * e ⟨y, hy⟩ * g, ?_⟩
      have harg : g * (g⁻¹ * e ⟨y, hy⟩ * g) * g⁻¹ = e ⟨y, hy⟩ := by group
      rw [hψ_apply, harg]
      simp
  have hclosure : Subgroup.closure (ψ '' {y | ∃ s ∈ L,
      y = s * (entrywiseAdjointAut .E8 δ s)⁻¹}) = S := by
    have hmap := MonoidHom.map_closure ψ
      {y | ∃ s ∈ L, y = s * (entrywiseAdjointAut .E8 δ s)⁻¹}
    rw [hLtop, Subgroup.map_top, hψrange] at hmap
    exact hmap.symm
  have hsub : ψ '' {y | ∃ s ∈ L, y = s * (entrywiseAdjointAut .E8 δ s)⁻¹} ⊆ (H : Set G) := by
    rintro z ⟨a, ⟨s, hs, rfl⟩, rfl⟩
    rw [hψ_apply]
    simpa [ii] using hB s hs
  have hSH : S ≤ H := by
    rw [← hclosure]
    exact (Subgroup.closure_le H).2 hsub
  refine ⟨T, ?_, hTmem, hSH⟩
  calc T.card ≤ (L.map fun s =>
        ((e.symm (g * s * g⁻¹) : ↥S) : G) * x *
          ((e.symm (g * s * g⁻¹) : ↥S) : G)⁻¹).toFinset.card + 1 :=
        Finset.card_insert_le _ _
    _ ≤ (L.map fun s =>
        ((e.symm (g * s * g⁻¹) : ↥S) : G) * x *
          ((e.symm (g * s * g⁻¹) : ↥S) : G)⁻¹).length + 1 :=
        Nat.add_le_add_right (List.toFinset_card_le _) 1
    _ = L.length + 1 := by rw [List.length_map]
    _ ≤ 10 + 1 := Nat.add_le_add_right hLcard 1
    _ = 11 := rfl

theorem gs03Alpha_e8 : GS03AlphaFor fun s _ _ => s = .E8 := by
  intro G _ _ S hS hC t n f ht hlie x hx
  subst t
  have hb : gs03Bound .E8 n f = 11 := rfl
  rw [hb]
  by_cases hxS : x ∈ S
  · exact gs03Alpha_e8_inner hlie hx hxS
  · exact gs03Alpha_e8_outer hS hC hlie hx hxS

end Supplier

end CFSG.LocalAnalysis.WeakClosure81

