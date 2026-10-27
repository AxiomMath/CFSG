module

public import CFSG.LocalAnalysis.StandardType.GGQ2InLD6AxesCheck

public section

namespace CFSG.StandardType.QTwoD6

open Module

private def qd6a_Usp : Submodule (ZMod 3) V7 :=
  Submodule.span (ZMod 3) (Set.range hvec)

private lemma qd6a_hvec_mem_Usp (i : Fin 6) : hvec i ∈ qd6a_Usp :=
  Submodule.subset_span (Set.mem_range_self i)

private def qd6a_U0 : Submodule (ZMod 3) V7 where
  carrier := {v | v 0 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy
    simp [Pi.add_apply, hx, hy]
  smul_mem' := by
    intro a x hx
    simp only [Set.mem_setOf_eq] at hx
    simp [hx]

private lemma qd6a_Usp_le_U0 : qd6a_Usp ≤ qd6a_U0 := by
  rw [qd6a_Usp, Submodule.span_le]
  rintro v ⟨i, rfl⟩
  simp [qd6a_U0, hvec]

private lemma qd6a_U0_le_Usp : qd6a_U0 ≤ qd6a_Usp := by
  intro v hv
  rw [← qd6a_toVec_cOf v hv]
  change (∑ i, v i.succ • hvec i) ∈ qd6a_Usp
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (qd6a_hvec_mem_Usp i))

private lemma qd6a_Usp_eq_U0 : qd6a_Usp = qd6a_U0 :=
  le_antisymm qd6a_Usp_le_U0 qd6a_U0_le_Usp

private lemma qd6a_epsVec_mem_Usp (a : Fin 6) : epsVec a ∈ qd6a_Usp := by
  rw [qd6a_Usp_eq_U0]
  exact qd6a_epsVec_zero a

private lemma qd6a_simpleD6_sub_mem (j : Fin 6) (v : V7) :
    simpleD6 j v - v ∈ qd6a_Usp := by
  rw [simpleD6, Module.reflection_apply]
  have h : v - (avec j v) • hvec j - v = (-(avec j v)) • hvec j := by
    funext k
    simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [h]
  exact Submodule.smul_mem _ (-(avec j v)) (qd6a_hvec_mem_Usp j)

private lemma qd6a_W6_sub_mem (g : V7 ≃ₗ[ZMod 3] V7) (hg : g ∈ W6) :
    (∀ v ∈ qd6a_Usp, g v ∈ qd6a_Usp) ∧ (∀ v, g v - v ∈ qd6a_Usp) := by
  have key : ∀ g : V7 ≃ₗ[ZMod 3] V7, g ∈ W6 →
      (∀ v ∈ qd6a_Usp, g v ∈ qd6a_Usp) ∧ (∀ v, g v - v ∈ qd6a_Usp) := by
    intro g hg
    rw [W6] at hg
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hg
    · rintro x ⟨j, rfl⟩
      constructor
      · intro v hv
        rw [simpleD6, Module.reflection_apply]
        exact Submodule.sub_mem _ hv
          (Submodule.smul_mem _ _ (qd6a_hvec_mem_Usp j))
      · exact qd6a_simpleD6_sub_mem j
    · constructor
      · intro v hv; simpa using hv
      · intro v; simp
    · intro x y _ _ ihx ihy
      constructor
      · intro v hv
        rw [LinearEquiv.mul_apply]
        exact ihx.1 _ (ihy.1 _ hv)
      · intro v
        have h : (x * y) v - v = x (y v - v) + (x v - v) := by
          rw [LinearEquiv.mul_apply, map_sub]; abel
        rw [h]
        exact Submodule.add_mem _ (ihx.1 _ (ihy.2 v)) (ihx.2 v)
    · intro x _ ihx
      have hx' : ∀ v, v - x⁻¹ v ∈ qd6a_Usp := fun v => by
        simpa using ihx.2 (x⁻¹ v)
      constructor
      · intro v hv
        have h1 := hx' v
        have h2 : x⁻¹ v = v - (v - x⁻¹ v) := by abel
        rw [h2]
        exact Submodule.sub_mem _ hv h1
      · intro v
        have h1 := hx' v
        have h2 : x⁻¹ v - v = -(v - x⁻¹ v) := by abel
        rw [h2]
        exact Submodule.neg_mem _ h1
  exact key g hg

private lemma qd6a_T_hvec_mem (T : V7 ≃ₗ[ZMod 3] V7)
    (hT : ∀ g : V7 ≃ₗ[ZMod 3] V7, g ∈ W6 ↔ T * g * T⁻¹ ∈ W6) (i : Fin 6) :
    T (hvec i) ∈ qd6a_Usp := by
  have hgen : simpleD6 i ∈ W6 := Subgroup.subset_closure ⟨i, rfl⟩
  have hg : T * simpleD6 i * T⁻¹ ∈ W6 := (hT (simpleD6 i)).mp hgen
  have hQ := (qd6a_W6_sub_mem _ hg).2 (T (hvec i))
  have hsh : simpleD6 i (hvec i) = -hvec i := by
    funext k
    have hy : ∀ y : ZMod 3, y - 2 * y = -y := by decide
    simpa [simpleD6, Module.reflection_apply, avec_hvec, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] using hy (hvec i k)
  have happ : (T * simpleD6 i * T⁻¹) (T (hvec i)) = -T (hvec i) := by
    simp [hsh]
  rw [happ] at hQ
  have hself : ∀ x : V7, -x - x = x := by
    intro x
    have hy : ∀ y : ZMod 3, -y - y = y := by decide
    funext k
    exact hy (x k)
  rwa [hself] at hQ

private lemma qd6a_T_mem_Usp (T : V7 ≃ₗ[ZMod 3] V7)
    (hT : ∀ g : V7 ≃ₗ[ZMod 3] V7, g ∈ W6 ↔ T * g * T⁻¹ ∈ W6) :
    ∀ v ∈ qd6a_Usp, T v ∈ qd6a_Usp := by
  have hmap : Submodule.map T.toLinearMap qd6a_Usp ≤ qd6a_Usp := by
    rw [Submodule.map_le_iff_le_comap, qd6a_Usp, Submodule.span_le]
    rintro v ⟨i, rfl⟩
    exact qd6a_T_hvec_mem T hT i
  intro v hv
  exact hmap (Submodule.mem_map_of_mem hv)

private def qd6a_orb (v : V7) : Set V7 := {u | ∃ g ∈ W6, u = g v}

private lemma qd6a_orb_image (T : V7 ≃ₗ[ZMod 3] V7)
    (hT : ∀ g : V7 ≃ₗ[ZMod 3] V7, g ∈ W6 ↔ T * g * T⁻¹ ∈ W6) (v : V7) :
    qd6a_orb (T v) = T '' qd6a_orb v := by
  ext u; constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨(T⁻¹ * g * T) v, ⟨T⁻¹ * g * T, ?_, rfl⟩, ?_⟩
    · rw [hT]
      have h : T * (T⁻¹ * g * T) * T⁻¹ = g := by group
      rw [h]
      exact hg
    · show T ((T⁻¹ * g * T) v) = g (T v)
      simp
  · rintro ⟨x, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨T * g * T⁻¹, (hT g).mp hg, ?_⟩
    simp

private lemma qd6a_orb_eq_of_mem {v v' : V7} (h : v' ∈ qd6a_orb v) :
    qd6a_orb v' = qd6a_orb v := by
  obtain ⟨g, hg, rfl⟩ := h
  ext u; constructor
  · rintro ⟨h', hh', rfl⟩
    exact ⟨h' * g, W6.mul_mem hh' hg, by rw [LinearEquiv.mul_apply]⟩
  · rintro ⟨h', hh', rfl⟩
    exact ⟨h' * g⁻¹, W6.mul_mem hh' (W6.inv_mem hg), by simp⟩

private def qd6a_axisF : Finset V7 :=
  {epsVec 0, epsVec 1, epsVec 2, epsVec 3, epsVec 4, epsVec 5,
    -epsVec 0, -epsVec 1, -epsVec 2, -epsVec 3, -epsVec 4, -epsVec 5}

private lemma qd6a_axisF_card : qd6a_axisF.card = 12 := by decide +kernel

private lemma qd6a_simpleD6_mem_stabAxis (j : Fin 6) :
    simpleD6 j '' (qd6a_axisF : Set V7) = (qd6a_axisF : Set V7) := by
  rw [← Finset.coe_image, Finset.coe_inj]
  fin_cases j <;> decide +kernel

private def qd6a_stabAxis : Subgroup (V7 ≃ₗ[ZMod 3] V7) where
  carrier := {g | g '' (qd6a_axisF : Set V7) = (qd6a_axisF : Set V7)}
  one_mem' := by ext x; simp
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    have hcoe : (⇑(g * h) : V7 → V7) = ⇑g ∘ ⇑h :=
      funext (fun x => LinearEquiv.mul_apply g h x)
    calc (g * h) '' (qd6a_axisF : Set V7) = (⇑g ∘ ⇑h) '' (qd6a_axisF : Set V7) := by
          rw [hcoe]
      _ = g '' (h '' (qd6a_axisF : Set V7)) := (Set.image_image g h _).symm
      _ = g '' (qd6a_axisF : Set V7) := by rw [hh]
      _ = (qd6a_axisF : Set V7) := hg
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    ext x; constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hy' : y ∈ g '' (qd6a_axisF : Set V7) := by rw [hg]; exact hy
      obtain ⟨z, hz, hzy⟩ := hy'
      rw [← hzy]
      simpa using hz
    · intro hx
      exact ⟨g x, by rw [← hg]; exact ⟨x, hx, rfl⟩, by simp⟩

private lemma qd6a_W6_le_stabAxis : W6 ≤ qd6a_stabAxis := by
  rw [W6, Subgroup.closure_le]
  rintro g ⟨j, rfl⟩
  show simpleD6 j '' (qd6a_axisF : Set V7) = (qd6a_axisF : Set V7)
  exact qd6a_simpleD6_mem_stabAxis j

private lemma qd6a_orb_axis_subset (a : Fin 6) :
    qd6a_orb (epsVec a) ⊆ (qd6a_axisF : Set V7) := by
  rintro u ⟨g, hg, rfl⟩
  have hg' : g '' (qd6a_axisF : Set V7) = (qd6a_axisF : Set V7) := qd6a_W6_le_stabAxis hg
  have hA : epsVec a ∈ (qd6a_axisF : Set V7) := by fin_cases a <;> decide
  have hmem : g (epsVec a) ∈ g '' (qd6a_axisF : Set V7) := ⟨epsVec a, hA, rfl⟩
  rwa [hg'] at hmem

private lemma qd6a_orb_axis_ncard_le (a : Fin 6) : (qd6a_orb (epsVec a)).ncard ≤ 12 := by
  calc (qd6a_orb (epsVec a)).ncard ≤ ((qd6a_axisF : Set V7)).ncard :=
        Set.ncard_le_ncard (qd6a_orb_axis_subset a)
    _ = qd6a_axisF.card := Set.ncard_coe_finset _
    _ = 12 := qd6a_axisF_card

private lemma qd6a_can_mem_orb (c : Fin 6 → ZMod 3) :
    qd6a_toVec (qd6a_can c) ∈ qd6a_orb (qd6a_toVec c) := by
  simp only [qd6a_orb, Set.mem_setOf_eq]
  refine ⟨qd6a_applyWord (qd6a_normWord c), qd6a_applyWord_mem _, ?_⟩
  rw [qd6a_can, qd6a_applyWord_toVec]

private lemma qd6a_thirteen_le_orb (u : V7) (hu0 : u 0 = 0) (hune : u ≠ 0)
    (huax : ∀ b : Fin 6, u ≠ epsVec b ∧ u ≠ -epsVec b) :
    13 ≤ (qd6a_orb u).ncard := by
  set c : Fin 6 → ZMod 3 := qd6a_cOf u with hc
  have htoVec : qd6a_toVec c = u := by rw [hc]; exact qd6a_toVec_cOf u hu0
  have hcne : c ≠ 0 := by
    intro h
    apply hune
    rw [← htoVec, h]
    simp [qd6a_toVec]
  have hcax : qd6a_NonAxis c := by
    refine ⟨fun b => ⟨?_, ?_⟩, hcne⟩
    · intro h
      exact (huax b).1 (by rw [← htoVec, h, qd6a_toVec_cOfEps])
    · intro h
      exact (huax b).2 (by rw [← htoVec, h, qd6a_toVec_neg, qd6a_toVec_cOfEps])
  have hcanmem : qd6a_can c ∈ qd6a_canNonAxisSet := qd6a_can_mem c hcax
  have hchk : 13 ≤ (qd6a_ws.map (fun w => qd6a_applyCWord w (qd6a_can c))).dedup.length :=
    qd6a_canon_check _ hcanmem
  set L : List (Fin 6 → ZMod 3) := qd6a_ws.map (fun w => qd6a_applyCWord w (qd6a_can c)) with hL
  set S : Finset (Fin 6 → ZMod 3) := L.toFinset with hS
  have hScard : S.card = L.dedup.length := by rw [hS, List.card_toFinset]
  have hS13 : 13 ≤ S.card := by rw [hScard]; exact hchk
  have hcanorb : qd6a_toVec (qd6a_can c) ∈ qd6a_orb u := by
    rw [← htoVec]
    exact qd6a_can_mem_orb c
  have horb : qd6a_orb (qd6a_toVec (qd6a_can c)) = qd6a_orb u :=
    qd6a_orb_eq_of_mem hcanorb
  have hsub : (↑(S.image qd6a_toVec) : Set V7) ⊆ qd6a_orb u := by
    intro x hx
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hx
    rw [hS, List.mem_toFinset, hL, List.mem_map] at hc'
    obtain ⟨w, _, rfl⟩ := hc'
    rw [qd6a_applyWord_toVec, ← horb]
    exact ⟨qd6a_applyWord w, qd6a_applyWord_mem w, rfl⟩
  have hcard : (S.image qd6a_toVec).card = S.card :=
    Finset.card_image_of_injective S qd6a_toVec_injective
  calc 13 ≤ S.card := hS13
    _ = (S.image qd6a_toVec).card := hcard.symm
    _ = (↑(S.image qd6a_toVec) : Set V7).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (qd6a_orb u).ncard := Set.ncard_le_ncard hsub

theorem axis_of_normalizer (T : V7 ≃ₗ[ZMod 3] V7)
    (hT : ∀ g : V7 ≃ₗ[ZMod 3] V7, g ∈ W6 ↔ T * g * T⁻¹ ∈ W6)
    (hT0 : T e0 ∈ Submodule.span (ZMod 3) {e0}) (a : Fin 6) :
    ∃ b : Fin 6, ∃ t : ZMod 3, (t = 1 ∨ t = -1) ∧ T (epsVec a) = t • epsVec b := by
  have hTepsU : T (epsVec a) ∈ qd6a_Usp :=
    qd6a_T_mem_Usp T hT _ (qd6a_epsVec_mem_Usp a)
  have hTeps0 : (T (epsVec a)) 0 = 0 := qd6a_Usp_le_U0 hTepsU
  have hepsne : epsVec a ≠ 0 := by fin_cases a <;> decide
  have hTurne : T (epsVec a) ≠ 0 := fun h => hepsne (T.injective (by simpa using h))
  have hcardeq : (qd6a_orb (T (epsVec a))).ncard = (qd6a_orb (epsVec a)).ncard := by
    rw [qd6a_orb_image T hT (epsVec a)]
    exact Set.InjOn.ncard_image (fun x _ y _ hxy => T.injective hxy)
  by_contra hcon
  have huax : ∀ b : Fin 6,
      T (epsVec a) ≠ epsVec b ∧ T (epsVec a) ≠ -epsVec b := by
    intro b
    constructor
    · intro h
      exact hcon ⟨b, 1, Or.inl rfl, by simpa using h⟩
    · intro h
      refine hcon ⟨b, -1, Or.inr rfl, ?_⟩
      rw [neg_one_smul]; exact h
  have hlow : 13 ≤ (qd6a_orb (T (epsVec a))).ncard :=
    qd6a_thirteen_le_orb _ hTeps0 hTurne huax
  have hup : (qd6a_orb (T (epsVec a))).ncard ≤ 12 := by
    rw [hcardeq]; exact qd6a_orb_axis_ncard_le a
  omega

end CFSG.StandardType.QTwoD6

end
