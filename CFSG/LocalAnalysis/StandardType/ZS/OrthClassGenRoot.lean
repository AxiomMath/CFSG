module

public import CFSG.ClassicalGroups.Orthogonal.RootCenters
public import CFSG.ClassicalGroups.Orthogonal.Derived
public import Mathlib.Algebra.Field.ZMod
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
theorem reflect_mul_reflect_add_smul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {u w : V} (hu : Q u = 0) (huw : polar Q u w = 0) (hw : Q w ≠ 0)
    (t : K) : reflect Q w * reflect Q (w + t • u) = eichler Q u ((t / Q w) • w) := by
  have hwu : polar Q w u = 0 := by rw [polar_comm, huw]
  have hQw' : Q (w + t • u) = Q w := by
    rw [QuadraticMap.map_add Q, map_smul_eq_sq, hu, polar_smul_right_eq, hwu]
    ring
  have hp : polar Q u ((t / Q w) • w) = 0 := by rw [polar_smul_right_eq, huw, mul_zero]
  refine LinearEquiv.ext fun x => ?_
  have hQw'' : Q (w + t • u) ≠ 0 := by rw [hQw']; exact hw
  rw [LinearEquiv.mul_apply, reflect_apply hQw'', reflect_apply hw,
    eichler_apply hu hp, hQw', polar_sub_right, polar_smul_right_eq, polar_add_right,
    polar_smul_right_eq, polar_self_eq_two_mul, hwu, polar_add_left, polar_smul_left_eq,
    polar_smul_right_eq, map_smul_eq_sq, polar_comm Q x u, polar_comm Q x w]
  match_scalars <;> field_simp; ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_conj_eichler_mem {Q : QuadraticForm (ZMod p) U}
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {e a : U} (he : Q e = 0) (hea : polar Q e a = 0)
    (ha : Q a ≠ 0) (hra : reflect Q a ∈ X) (hrae : reflect Q (a + e) ∈ X) {ι : Type*}
    (v : ι → U) (hve : ∀ i, polar Q e (v i) = 0) (hv : ∀ i, reflect Q (v i) ∈ X) :
    (polar Q e ((Q a)⁻¹ • a) = 0 ∧ eichler Q e ((Q a)⁻¹ • a) ∈ X) ∧
      ∀ i, polar Q e ((Q a)⁻¹ • reflect Q (v i) a) = 0 ∧
        eichler Q e ((Q a)⁻¹ • reflect Q (v i) a) ∈ X := by
  have hbase : eichler Q e ((Q a)⁻¹ • a) ∈ X := by
    have h := reflect_mul_reflect_add_smul (Q := Q) he hea ha (1 : ZMod p)
    rw [one_smul, one_div] at h
    rw [← h]
    exact X.mul_mem hra hrae
  have hpol_a : polar Q e ((Q a)⁻¹ • a) = 0 := by
    rw [polar_smul_right_eq, hea, mul_zero]
  have hfix (i : ι) : reflect Q (v i) e = e := by
    apply reflect_apply_of_polar_eq_zero
    rw [polar_comm]
    exact hve i
  refine ⟨⟨hpol_a, hbase⟩, fun i => ⟨?_, ?_⟩⟩
  · have hpv : polar Q e (reflect Q (v i) a) = 0 := by
      calc polar Q e (reflect Q (v i) a)
          = polar Q (reflect Q (v i) e) (reflect Q (v i) a) := by rw [hfix i]
        _ = polar Q e a := polar_map_of_mem (reflect_mem_orthogonalGroup Q (v i)) e a
        _ = 0 := hea
    rw [polar_smul_right_eq, hpv, mul_zero]
  · have h := eichler_conj (reflect_mem_orthogonalGroup Q (v i)) e ((Q a)⁻¹ • a)
    rw [hfix i, map_smul] at h
    rw [← h]
    exact X.mul_mem (X.mul_mem (hv i) hbase) (X.inv_mem (hv i))

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_gens_mem_closure {Q : QuadraticForm (ZMod p) U} {e a : U} (ha : Q a ≠ 0)
    {ι : Type*} (v : ι → U) :
    ∀ x ∈ insert e (insert a (Set.range fun i => reflect Q (v i) a)),
      x ∈ AddSubgroup.toZModSubmodule p (AddSubgroup.closure (({(Q a)⁻¹ • a} ∪
        Set.range (fun i => (Q a)⁻¹ • reflect Q (v i) a)) ∪ {e})) := by
  intro x hx
  rw [Set.mem_insert_iff, Set.mem_insert_iff] at hx
  rcases hx with hx | hx | ⟨i, rfl⟩
  · rw [hx]
    exact AddSubgroup.subset_closure (Or.inr (Set.mem_singleton e))
  · rw [hx]
    have hm1 : (Q a)⁻¹ • a ∈ ({(Q a)⁻¹ • a} ∪
        Set.range (fun i => (Q a)⁻¹ • reflect Q (v i) a)) := Or.inl (Set.mem_singleton _)
    have hm : (Q a)⁻¹ • a ∈ AddSubgroup.closure (({(Q a)⁻¹ • a} ∪
        Set.range (fun i => (Q a)⁻¹ • reflect Q (v i) a)) ∪ {e}) :=
      AddSubgroup.subset_closure (Or.inl hm1)
    have h3 := ZMod.smul_mem hm (Q a)
    rw [smul_smul, mul_inv_cancel₀ ha, one_smul] at h3
    exact h3
  · have hm1 : (Q a)⁻¹ • reflect Q (v i) a ∈ ({(Q a)⁻¹ • a} ∪
        Set.range (fun i => (Q a)⁻¹ • reflect Q (v i) a)) := Or.inr ⟨i, rfl⟩
    have hm : (Q a)⁻¹ • reflect Q (v i) a ∈ AddSubgroup.closure (({(Q a)⁻¹ • a} ∪
        Set.range (fun i => (Q a)⁻¹ • reflect Q (v i) a)) ∪ {e}) :=
      AddSubgroup.subset_closure (Or.inl hm1)
    have h3 := ZMod.smul_mem hm (Q a)
    rw [smul_smul, mul_inv_cancel₀ ha, one_smul] at h3
    exact h3

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
theorem isRootCenter_of_reflect_mem {Q : QuadraticForm (ZMod p) U}
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {e a : U}
    (he0 : e ≠ 0) (he : Q e = 0) (hea : polar Q e a = 0) (ha : Q a ≠ 0)
    (hra : reflect Q a ∈ X) (hrae : reflect Q (a + e) ∈ X) {ι : Type*} (v : ι → U)
    (hve : ∀ i, polar Q e (v i) = 0) (hv : ∀ i, reflect Q (v i) ∈ X)
    (hspan : ∀ w, polar Q e w = 0 →
      w ∈ Submodule.span (ZMod p) (insert e (insert a (Set.range fun i => reflect Q (v i) a)))) :
    IsRootCenter Q X e := by
  obtain ⟨⟨hpol_a, hbase⟩, hconj⟩ :=
    ocg_conj_eichler_mem he hea ha hra hrae v hve hv
  refine IsRootCenter.of_span he0 he
    ({(Q a)⁻¹ • a} ∪ Set.range (fun i => (Q a)⁻¹ • reflect Q (v i) a)) ?_ ?_
  · intro w hw
    rcases hw with hw | ⟨i, rfl⟩
    · rw [Set.mem_singleton_iff] at hw
      rw [hw]
      exact ⟨hpol_a, hbase⟩
    · exact hconj i
  · intro w hw
    exact (Submodule.span_le.mpr (ocg_gens_mem_closure (Q := Q) (e := e) ha v)) (hspan w hw)

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_perp_eq_span_pair [Module.Finite (ZMod p) U]
    (h3 : Module.finrank (ZMod p) U = 3) {Q : QuadraticForm (ZMod p) U}
    (hQ : (polarBilin Q).Nondegenerate) {e w : U} (he0 : e ≠ 0) (he : Q e = 0)
    (hw : polar Q e w = 0) (hw_not : w ∉ Submodule.span (ZMod p) ({e} : Set U)) :
    Submodule.span (ZMod p) ({e, w} : Set U) = LinearMap.ker (polarBilin Q e) := by
  have hfne : polarBilin Q e ≠ 0 := by
    intro h0
    exact he0 (hQ.1 e fun y => by rw [h0]; rfl)
  have hker2 : Module.finrank (ZMod p) (LinearMap.ker (polarBilin Q e)) = 2 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero (K := ZMod p) hfne
    rw [h3] at h
    omega
  have hrange : Set.range ![e, w] = ({e, w} : Set U) := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]
  have hspan2 : Module.finrank (ZMod p)
      (Submodule.span (ZMod p) ({e, w} : Set U)) = 2 := by
    have hli : LinearIndependent (ZMod p) ![e, w] := by
      rw [LinearIndependent.pair_iff' he0]
      intro s hs
      exact hw_not (Submodule.mem_span_singleton.mpr ⟨s, hs⟩)
    have h := finrank_span_eq_card (R := ZMod p) hli
    rw [hrange] at h
    simpa using h
  have hle : Submodule.span (ZMod p) ({e, w} : Set U) ≤ LinearMap.ker (polarBilin Q e) := by
    apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact LinearMap.mem_ker.mpr (by simpa using polar_self_eq_zero he)
    · rw [hx]
      exact LinearMap.mem_ker.mpr (by simpa using hw)
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hspan2, hker2])

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
theorem isRootCenter_of_mem_rootGroup_ne_one [Module.Finite (ZMod p) U]
    (h3 : Module.finrank (ZMod p) U = 3) {Q : QuadraticForm (ZMod p) U}
    (hQ : (polarBilin Q).Nondegenerate) {X : Subgroup (U ≃ₗ[ZMod p] U)} {e : U} (he0 : e ≠ 0)
    (he : Q e = 0) {g : U ≃ₗ[ZMod p] U} (hgX : g ∈ X) (hgU : g ∈ rootGroup Q e) (hg1 : g ≠ 1) :
    IsRootCenter Q X e := by
  obtain ⟨w, hw, rfl⟩ := mem_rootGroup.mp hgU
  have hw_not : w ∉ Submodule.span (ZMod p) ({e} : Set U) := by
    intro hwmem
    rw [Submodule.mem_span_singleton] at hwmem
    obtain ⟨s, hs⟩ := hwmem
    apply hg1
    rw [← hs]
    have h := eichler_add_smul_self he (0 : U) s
    rw [zero_add] at h
    rw [h, eichler_zero_right]
  have hker := ocg_perp_eq_span_pair (Q := Q) (e := e) (w := w) h3 hQ he0 he hw hw_not
  refine IsRootCenter.of_span he0 he ({w} : Set U) ?_ ?_
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact ⟨hw, hgX⟩
  · intro u hu
    have hu' : u ∈ Submodule.span (ZMod p) ({e, w} : Set U) := by
      rw [hker]
      exact LinearMap.mem_ker.mpr (by simpa using hu)
    have h2 : u ∈ AddSubgroup.toZModSubmodule p (AddSubgroup.closure ({w} ∪ {e})) := by
      refine (Submodule.span_le.mpr ?_) hu'
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx]
        exact AddSubgroup.subset_closure (Or.inr (Set.mem_singleton e))
      · rw [hx]
        exact AddSubgroup.subset_closure (Or.inl (Set.mem_singleton w))
    exact h2

end CFSG.StandardType.ZS
