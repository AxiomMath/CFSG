module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelData

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three

section Closure

variable {L' : Type} [Group L'] [Finite L'] {Z : Subgroup L'} {A : Subgroup (MulAut L')}
  {Φ : A →* Multiplicative (Fin 6 → ZMod 3)} {T : Subgroup L'} {w : Fin 6 → L'}

theorem GGE6ThreeData.inv_stable (h : GGE6ThreeData Z A Φ T w) (i : Fin 6) :
    ∀ t ∈ T, (w i)⁻¹ * t * w i ∈ T := by
  intro t ht
  let f : T → T := fun s => ⟨w i * (s : L') * (w i)⁻¹, h.stable i s s.2⟩
  have hf : Function.Injective f := by
    intro s1 s2 h12
    apply Subtype.ext
    have hc : (MulAut.conj (w i)) (s1 : L') = (MulAut.conj (w i)) (s2 : L') := by
      simpa only [f, MulAut.conj_apply] using congrArg Subtype.val h12
    exact (MulAut.conj (w i)).injective hc
  obtain ⟨s, hs⟩ := Finite.surjective_of_injective hf ⟨t, ht⟩
  have hval : (s : L') = (w i)⁻¹ * t * w i := by
    have hc : w i * (s : L') * (w i)⁻¹ = t := by
      simpa only [f] using congrArg Subtype.val hs
    rw [← hc]
    group
  rw [← hval]
  exact s.2

theorem GGE6ThreeData.closure_stable (h : GGE6ThreeData Z A Φ T w) {n : L'}
    (hn : n ∈ Subgroup.closure (Set.range w)) : ∀ t ∈ T, n * t * n⁻¹ ∈ T := by
  have hmain : (∀ t ∈ T, n * t * n⁻¹ ∈ T) ∧ (∀ t ∈ T, n⁻¹ * t * n ∈ T) := by
    refine Subgroup.closure_induction
      (p := fun x _ => (∀ t ∈ T, x * t * x⁻¹ ∈ T) ∧ (∀ t ∈ T, x⁻¹ * t * x ∈ T))
      ?_ ?_ ?_ ?_ hn
    · rintro x ⟨i, rfl⟩
      exact ⟨h.stable i, h.inv_stable i⟩
    · exact ⟨fun t ht => by simpa using ht, fun t ht => by simpa using ht⟩
    · intro x y _ _ hPx hPy
      refine ⟨fun t ht => ?_, fun t ht => ?_⟩
      · have hyt : y * t * y⁻¹ ∈ T := hPy.1 t ht
        have h1 : x * (y * t * y⁻¹) * x⁻¹ ∈ T := hPx.1 _ hyt
        have heq : x * y * t * (x * y)⁻¹ = x * (y * t * y⁻¹) * x⁻¹ := by
          rw [mul_inv_rev]; group
        rw [heq]; exact h1
      · have hxt : x⁻¹ * t * x ∈ T := hPx.2 t ht
        have h1 : y⁻¹ * (x⁻¹ * t * x) * y ∈ T := hPy.2 _ hxt
        have heq : (x * y)⁻¹ * t * (x * y) = y⁻¹ * (x⁻¹ * t * x) * y := by
          rw [mul_inv_rev]; group
        rw [heq]; exact h1
    · intro x _ hPx
      exact ⟨fun t ht => by simpa using hPx.2 t ht, fun t ht => by simpa using hPx.1 t ht⟩
  exact hmain.1

theorem GGE6ThreeData.closure_coboundary (h : GGE6ThreeData Z A Φ T w) {n : L'}
    (hn : n ∈ Subgroup.closure (Set.range w)) :
    ∀ a ∈ A, n * (a n)⁻¹ ∈ T ∧ (n * (a n)⁻¹) ^ 3 = 1 := by
  refine Subgroup.closure_induction
    (p := fun x _ => ∀ a ∈ A, x * (a x)⁻¹ ∈ T ∧ (x * (a x)⁻¹) ^ 3 = 1) ?_ ?_ ?_ ?_ hn
  · rintro x ⟨i, rfl⟩
    exact h.coboundary i
  · intro a _
    constructor
    · simpa using T.one_mem
    · simp
  · intro x y hx hy hPx hPy a ha
    have hzy : y * (a y)⁻¹ ∈ T := (hPy a ha).1
    have hzx : x * (a x)⁻¹ ∈ T := (hPx a ha).1
    have hs1 : x * (y * (a y)⁻¹) * x⁻¹ ∈ T := h.closure_stable hx _ hzy
    have hbase : x * y * (a (x * y))⁻¹ =
        (x * (y * (a y)⁻¹) * x⁻¹) * (x * (a x)⁻¹) := by
      rw [map_mul, mul_inv_rev]; group
    have hc1 : (x * (y * (a y)⁻¹) * x⁻¹) ^ 3 = 1 := by
      rw [conj_pow, (hPy a ha).2, mul_one, mul_inv_cancel]
    have hcomm : Commute (x * (y * (a y)⁻¹) * x⁻¹) (x * (a x)⁻¹) :=
      h.comm _ hs1 _ hzx
    refine ⟨?_, ?_⟩
    · rw [hbase]; exact T.mul_mem hs1 hzx
    · rw [hbase, hcomm.mul_pow, hc1, (hPx a ha).2, mul_one]
  · intro x hx hPx a ha
    have hzx : x * (a x)⁻¹ ∈ T := (hPx a ha).1
    have hs : x⁻¹ * (x * (a x)⁻¹)⁻¹ * x ∈ T := by
      have h := h.closure_stable (Subgroup.inv_mem (Subgroup.closure (Set.range w)) hx) _ (T.inv_mem hzx)
      simpa using h
    have hbase : x⁻¹ * (a x⁻¹)⁻¹ = x⁻¹ * (x * (a x)⁻¹)⁻¹ * x := by
      rw [map_inv, inv_inv]; group
    have hcube : (x⁻¹ * (x * (a x)⁻¹)⁻¹ * x) ^ 3 = 1 := by
      have hconj : x⁻¹ * (x * (a x)⁻¹)⁻¹ * x =
          (MulAut.conj x⁻¹) ((x * (a x)⁻¹)⁻¹) := by
        rw [MulAut.conj_apply, inv_inv]
      rw [hconj, ← map_pow, inv_pow, (hPx a ha).2, inv_one, map_one]
    exact ⟨by rw [hbase]; exact hs, by rw [hbase]; exact hcube⟩

theorem GGE6ThreeData.closure_weyl (h : GGE6ThreeData Z A Φ T w) {n : L'}
    (hn : n ∈ Subgroup.closure (Set.range w)) :
    ∀ a ∈ A, (n * (a n)⁻¹) ^ 3 = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹ := by
  intro a ha
  obtain ⟨hT, hcube⟩ := h.closure_coboundary hn a ha
  exact ⟨hcube, fun a' ha' => h.fixed a' ha' _ hT⟩

theorem GGE6ThreeData.closure_act (h : GGE6ThreeData Z A Φ T w) {n : L'}
    (hn : n ∈ Subgroup.closure (Set.range w)) :
    ∃ u : WeylGroup .E6, ∀ a : A, ∃ b : A, (b : MulAut L') =
        MulAut.conj n * (a : MulAut L') * (MulAut.conj n)⁻¹ ∧
      Multiplicative.toAdd (Φ b) = adAct .E6 3 u (Multiplicative.toAdd (Φ a)) := by
  classical
  refine Subgroup.closure_induction
    (p := fun x _ => ∃ u : WeylGroup .E6, ∀ a : A, ∃ b : A, (b : MulAut L') =
        MulAut.conj x * (a : MulAut L') * (MulAut.conj x)⁻¹ ∧
      Multiplicative.toAdd (Φ b) = adAct .E6 3 u (Multiplicative.toAdd (Φ a))) ?_ ?_ ?_ ?_ hn
  · rintro x ⟨i, rfl⟩
    refine ⟨simple .E6 i, fun a => ?_⟩
    obtain ⟨b, hb1, hb2⟩ := h.act i a
    exact ⟨b, hb1.symm,
      hb2.trans (adAct_simple (τ := .E6) (p := 3) i (Multiplicative.toAdd (Φ a))).symm⟩
  · refine ⟨1, fun a => ⟨a, ?_, ?_⟩⟩
    · simp
    · exact (adAct_one (τ := .E6) (p := 3) (Multiplicative.toAdd (Φ a))).symm
  · rintro x y hx hy ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩
    refine ⟨u₁ * u₂, fun a => ?_⟩
    obtain ⟨c, hc1, hc2⟩ := hu₂ a
    obtain ⟨b, hb1, hb2⟩ := hu₁ c
    refine ⟨b, ?_, ?_⟩
    · rw [hb1, hc1, map_mul]; group
    · exact hb2.trans ((congrArg (adAct .E6 3 u₁) hc2).trans
        (adAct_mul (τ := .E6) (p := 3) u₁ u₂ (Multiplicative.toAdd (Φ a))).symm)
  · rintro x hx ⟨u, hu⟩
    let f : A → A := fun a' => Classical.choose (hu a')
    have hf_spec : ∀ a' : A, (f a' : MulAut L') =
          MulAut.conj x * (a' : MulAut L') * (MulAut.conj x)⁻¹ ∧
        Multiplicative.toAdd (Φ (f a')) = adAct .E6 3 u (Multiplicative.toAdd (Φ a')) :=
      fun a' => Classical.choose_spec (hu a')
    have hf : Function.Injective f := by
      intro a1 a2 h12
      apply Subtype.ext
      have h12' : (f a1 : MulAut L') = (f a2 : MulAut L') := congrArg Subtype.val h12
      rw [(hf_spec a1).1, (hf_spec a2).1] at h12'
      have hstep : (a1 : MulAut L') * (MulAut.conj x)⁻¹ =
          (a2 : MulAut L') * (MulAut.conj x)⁻¹ :=
        mul_left_cancel (by simpa only [mul_assoc] using h12')
      exact mul_right_cancel hstep
    haveI : Finite (MulAut L') := MulEquiv.finite_left
    haveI : Finite A := Subtype.finite
    have hsurj : Function.Surjective f := Finite.surjective_of_injective hf
    refine ⟨u⁻¹, fun a => ?_⟩
    obtain ⟨a', ha'⟩ := hsurj a
    have hfa : (f a' : MulAut L') = (a : MulAut L') := by rw [ha']
    refine ⟨a', ?_, ?_⟩
    · have hspec1 : MulAut.conj x * (a' : MulAut L') * (MulAut.conj x)⁻¹ = (a : MulAut L') := by
        rw [← (hf_spec a').1, hfa]
      have hx1 : MulAut.conj x⁻¹ = (MulAut.conj x)⁻¹ := map_inv (MulAut.conj) x
      simp only [hx1]
      rw [← hspec1]; group
    · have h1 : Multiplicative.toAdd (Φ a) = adAct .E6 3 u (Multiplicative.toAdd (Φ a')) :=
        (congrArg (fun b : A => Multiplicative.toAdd (Φ b)) ha').symm.trans (hf_spec a').2
      have h2 : adAct .E6 3 u⁻¹ (adAct .E6 3 u (Multiplicative.toAdd (Φ a'))) =
          Multiplicative.toAdd (Φ a') := by
        rw [← adAct_mul, inv_mul_cancel, adAct_one]
        rfl
      exact ((congrArg (adAct .E6 3 u⁻¹) h1).trans h2).symm

theorem GGE6ThreeData.closure_conj_mem (h : GGE6ThreeData Z A Φ T w) {n : L'}
    (hn : n ∈ Subgroup.closure (Set.range w)) :
    ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A := by
  obtain ⟨u, hu⟩ := h.closure_act hn
  intro a ha
  obtain ⟨b, hb1, _⟩ := hu ⟨a, ha⟩
  rw [← hb1]
  exact b.2

end Closure

end CFSG.StandardType
