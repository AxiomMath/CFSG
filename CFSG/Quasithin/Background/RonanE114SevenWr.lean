module

public import CFSG.CharacterTheory.Wreathed.SimpleFusion
public import CFSG.CharacterTheory.Wreathed.BaseFourCentralizerStructure
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Quasithin.RonanE114.Seven

open CFSG.Wreathed CFSG.Wreathed.BaseFourCentralizerStructure

section Base

variable {L : Type} [Group L] [Finite L]

theorem modelBase_comm {n : ℕ} (S : Sylow 2 L) (e : ↥(S : Subgroup L) ≃* Wreath (2 ^ n))
    {x y : L} (hx : x ∈ modelBase S e) (hy : y ∈ modelBase S e) : x * y = y * x := by
  obtain ⟨w₁, hw₁, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨w₂, hw₂, rfl⟩ := Subgroup.mem_map.mp hy
  have h := (base_is_abelian (2 ^ n)).is_comm.comm (⟨w₁, hw₁⟩ : baseSubgroup (2 ^ n))
    (⟨w₂, hw₂⟩ : baseSubgroup (2 ^ n))
  have h' := congrArg (fun w : baseSubgroup (2 ^ n) => wreathModelHom S e w.val) h
  simpa [map_mul] using h'

theorem isSolvable_centralizer_modelT (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 L)
    (e : ↥(S : Subgroup L) ≃* Wreath (2 ^ n)) :
    Group.IsSolvable ↥(Subgroup.centralizer (modelT n S e : Set L)) := by
  set C := Subgroup.centralizer (modelT n S e : Set L) with hC
  have hcomp := modelBaseFourCentralizer_oddCore_complement n hn S e
  haveI : (CFSG.oddCore ↥C).Characteristic := oddCore_characteristic
  haveI : Group.IsSolvable ↥(CFSG.oddCore ↥C) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (weakClosure_oddCore_card C)
  haveI : Group.IsSolvable (↥C ⧸ CFSG.oddCore ↥C) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        obtain ⟨p, hp⟩ := hcomp.surjective a
        obtain ⟨q, hq⟩ := hcomp.surjective b
        have hpq : p.2.1 * q.2.1 = q.2.1 * p.2.1 := by
          apply Subtype.ext
          exact modelBase_comm S e (Subgroup.mem_subgroupOf.mp p.2.2)
            (Subgroup.mem_subgroupOf.mp q.2.2)
        have ha : (QuotientGroup.mk a : ↥C ⧸ CFSG.oddCore ↥C) = QuotientGroup.mk p.2.1 := by
          rw [← hp, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff p.1.1).mpr p.1.2, one_mul]
        have hb : (QuotientGroup.mk b : ↥C ⧸ CFSG.oddCore ↥C) = QuotientGroup.mk q.2.1 := by
          rw [← hq, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff q.1.1).mpr q.1.2, one_mul]
        rw [ha, hb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hpq]
  exact Group.isSolvable_of_subgroup_quotient (CFSG.oddCore ↥C)

theorem isSolvable_normalizer_modelBase (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 L)
    (e : ↥(S : Subgroup L) ≃* Wreath (2 ^ n)) :
    Group.IsSolvable ↥(Subgroup.normalizer (modelBase S e : Set L)) := by
  set B := modelBase S e with hB
  set N := Subgroup.normalizer (B : Set L) with hN
  have hCB : Group.IsSolvable ↥(Subgroup.centralizer (B : Set L)) := by
    haveI := isSolvable_centralizer_modelT n hn S e
    have hle : Subgroup.centralizer (B : Set L) ≤ Subgroup.centralizer (modelT n S e : Set L) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (modelT_le_base n (by omega) S e))
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  haveI : Group.IsSolvable ↥((Subgroup.centralizer (B : Set L)).subgroupOf N) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe
        (Subgroup.centralizer_le_normalizer (s := (B : Set L)))).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe _).injective
  haveI : Group.IsSolvable (↥N ⧸ (Subgroup.centralizer (B : Set L)).subgroupOf N) := by
    rcases modelBaseNormalizerQuotient_alternatives n (by omega) S e with h2 | h6
    · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hp : IsPGroup 2 (↥N ⧸ (Subgroup.centralizer (B : Set L)).subgroupOf N) :=
        IsPGroup.of_card (n := 1) (by rw [h2]; norm_num)
      haveI : Group.IsNilpotent (↥N ⧸ (Subgroup.centralizer (B : Set L)).subgroupOf N) :=
        hp.isNilpotent
      infer_instance
    · obtain ⟨f⟩ := h6
      haveI : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
      exact Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective
  exact Group.isSolvable_of_subgroup_quotient ((Subgroup.centralizer (B : Set L)).subgroupOf N)

theorem exists_normalizer_moves [IsSimpleGroup L] (hnab : ∃ a b : L, a * b ≠ b * a) (n : ℕ)
    (hn : 2 ≤ n) (S : Sylow 2 L) (e : ↥(S : Subgroup L) ≃* Wreath (2 ^ n)) {z : L}
    (hz : z ∈ modelBase S e) (hz2 : orderOf z = 2) :
    ∃ g ∈ Subgroup.normalizer (modelBase S e : Set L), g * z * g⁻¹ ≠ z := by
  have hsym := modelBaseNormalizerQuotient_sym3_of_simple hnab n hn S e
  have hstructure := wreath_center_involution_and_quaternion_coordinates n hn
  have hxB : wreathModelHom S e (Original.x (2 ^ n)) ∈ modelBase S e :=
    Subgroup.mem_map.mpr ⟨Original.x (2 ^ n), by simp, rfl⟩
  have hx2B : wreathModelHom S e (Original.x2 (2 ^ n)) ∈ modelBase S e :=
    Subgroup.mem_map.mpr ⟨Original.x2 (2 ^ n), by simp, rfl⟩
  have hxo : orderOf (wreathModelHom S e (Original.x (2 ^ n))) = 2 :=
    (orderOf_injective _ (wreathModelHom_injective S e) _).trans hstructure.involution_orders.1
  have hx2o : orderOf (wreathModelHom S e (Original.x2 (2 ^ n))) = 2 :=
    (orderOf_injective _ (wreathModelHom_injective S e) _).trans
      hstructure.involution_orders.2.1
  have hne : wreathModelHom S e (Original.x (2 ^ n)) ≠
      wreathModelHom S e (Original.x2 (2 ^ n)) := by
    intro h
    have h' := wreathModelHom_injective S e h
    exact hstructure.distinct_classes.1 (h' ▸ IsConj.refl _)
  by_cases hzx : z = wreathModelHom S e (Original.x (2 ^ n))
  · obtain ⟨g, hg, hgz⟩ := modelBaseNormalizer_involutions_transitive n (by omega) S e hsym z _
      hz hx2B hz2 hx2o
    exact ⟨g, hg, by rw [hgz, hzx]; exact hne.symm⟩
  · obtain ⟨g, hg, hgz⟩ := modelBaseNormalizer_involutions_transitive n (by omega) S e hsym z _
      hz hxB hz2 hxo
    exact ⟨g, hg, by rw [hgz]; exact fun h => hzx h.symm⟩

theorem mem_modelBase_of_central (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 L)
    (e : ↥(S : Subgroup L) ≃* Wreath (2 ^ n)) {z : L} (hzS : z ∈ (S : Subgroup L))
    (hc : ∀ s ∈ (S : Subgroup L), s * z = z * s) : z ∈ modelBase S e := by
  have hcen : (⟨z, hzS⟩ : ↥(S : Subgroup L)) ∈ Subgroup.center ↥(S : Subgroup L) := by
    rw [Subgroup.mem_center_iff]
    intro s
    exact Subtype.ext (hc s s.2)
  have h1 : e ⟨z, hzS⟩ ∈ Subgroup.center (Wreath (2 ^ n)) := by
    rw [← Subgroup.map_center_eq e]
    exact Subgroup.mem_map_of_mem _ hcen
  rw [(wreath_center_involution_and_quaternion_coordinates n hn).center] at h1
  have ha : Original.a (2 ^ n) ∈ baseSubgroup (2 ^ n) := by
    rw [Original.a_eq]
    exact (element_mem_base _ _ _ _).mpr rfl
  have h2 : e ⟨z, hzS⟩ ∈ baseSubgroup (2 ^ n) := (Subgroup.zpowers_le.mpr ha) h1
  have h3 : wreathModelHom S e (e ⟨z, hzS⟩) = z :=
    congrArg Subtype.val (e.symm_apply_apply ⟨z, hzS⟩)
  rw [← h3]
  exact Subgroup.mem_map_of_mem _ h2

end Base

section Characteristic

theorem mem_normalizer_map_of_characteristic {W X : Type*} [Group W] [Group X] (ι : W →* X)
    (hι : Function.Injective ι) {B : Subgroup W} (hB : B.Characteristic) {t : X}
    (ht : t ∈ Subgroup.normalizer (ι.range : Set X)) :
    t ∈ Subgroup.normalizer ((B.map ι : Subgroup X) : Set X) := by
  let ι' : W ≃* ι.range := MonoidHom.ofInjective hι
  let c : MulAut ι.range := ι.range.normalizerMonoidHom ⟨t, ht⟩
  let α : MulAut W := (ι'.trans c).trans ι'.symm
  have hα : ∀ w, ι (α w) = t * ι w * t⁻¹ := by
    intro w
    have h1 : ι' (α w) = c (ι' w) := by simp [α]
    have h2 : ((ι' (α w) : ι.range) : X) = ((c (ι' w) : ι.range) : X) := by rw [h1]
    have h3 : ((c (ι' w) : ι.range) : X) = t * ι w * t⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe ι.range ⟨t, ht⟩ (ι' w)
    rw [h3] at h2
    exact h2
  have hBα : B.map α.toMonoidHom = B := Subgroup.characteristic_iff_map_eq.mp hB α
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨α b, ?_, hα b⟩
    rw [← hBα]
    exact Subgroup.mem_map_of_mem _ hb
  · rintro ⟨b, hb, hby⟩
    have hb' : b ∈ B.map α.toMonoidHom := by
      rw [hBα]
      exact hb
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb'
    refine ⟨b₀, hb₀, ?_⟩
    have h3 : t * ι b₀ * t⁻¹ = t * y * t⁻¹ := by
      rw [← hα b₀]
      exact hby
    simpa using h3

end Characteristic

end CFSG.Quasithin.RonanE114.Seven
