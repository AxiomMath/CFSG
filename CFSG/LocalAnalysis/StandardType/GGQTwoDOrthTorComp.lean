module

public import CFSG.Assembly.Defs
import CFSG.LocalAnalysis.ComponentClassification.LocalComponents

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly

private theorem plh_mem_sup_iff_of_commute {G : Type*} [Group G] {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} :
    x ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  constructor
  · intro hx
    rw [Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · exact ⟨y, hy, 1, B.one_mem, by simp⟩
      · exact ⟨1, A.one_mem, y, hy, by simp⟩
    | one => exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
    | mul y z hy hz ihy ihz =>
      obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := ihy
      obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := ihz
      refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
      rw [mul_assoc a₁ a₂ (b₁ * b₂), ← mul_assoc a₂ b₁ b₂, hc a₂ ha₂ b₁ hb₁]
      group
    | inv y hy ihy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := ihy
      exact ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb,
        by rw [mul_inv_rev, hc a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)]⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

private theorem plh_conj_mem_of_mem_sup_of_commute {G : Type*} [Group G] {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : G} (hg : g ∈ A ⊔ B) {n : G} (hn : n ∈ A) :
    g * n * g⁻¹ ∈ A := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (plh_mem_sup_iff_of_commute hc).1 hg
  have hbn : b * n = n * b := (hc n hn b hb).symm
  have heq : a * b * n * (a * b)⁻¹ = a * n * a⁻¹ := by
    rw [mul_inv_rev]
    calc a * b * n * (b⁻¹ * a⁻¹) = a * (b * n) * b⁻¹ * a⁻¹ := by group
      _ = a * (n * b) * b⁻¹ * a⁻¹ := by rw [hbn]
      _ = a * n * a⁻¹ := by group
  rw [heq]
  exact A.mul_mem (A.mul_mem ha hn) (A.inv_mem ha)

private theorem plh_twoG_le_of_perfect_of_isSolvable {G : Type*} [Group G] {A B P : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hPAB : P ≤ A ⊔ B)
    (hP : Group.IsPerfect ↥P) (hB : Group.IsSolvable ↥B) : P ≤ A := by
  set H := A ⊔ B with hH
  have hBH : B ≤ H := le_sup_right
  have hNn : (A.subgroupOf H).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact plh_conj_mem_of_mem_sup_of_commute hc g.2 hn
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (A.subgroupOf H)).comp (Subgroup.inclusion hBH)) := by
    intro q
    obtain ⟨⟨h, hh⟩, rfl⟩ := QuotientGroup.mk'_surjective (A.subgroupOf H) q
    obtain ⟨a, ha, b, hb, rfl⟩ := (plh_mem_sup_iff_of_commute hc).1 hh
    refine ⟨⟨b, hb⟩, ?_⟩
    show QuotientGroup.mk' (A.subgroupOf H) ⟨b, hBH hb⟩ =
      QuotientGroup.mk' (A.subgroupOf H) ⟨a * b, hh⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    show b⁻¹ * (a * b) ∈ A
    rw [hc a ha b hb, inv_mul_cancel_left]
    exact ha
  have hsolv : Group.IsSolvable (↥H ⧸ A.subgroupOf H) :=
    Group.isSolvable_of_surjective hsurj
  have hPH : P ≤ H := hPAB
  let φ : ↥P →* ↥H ⧸ A.subgroupOf H :=
    (QuotientGroup.mk' (A.subgroupOf H)).comp (Subgroup.inclusion hPH)
  have hr : φ.range = ⊥ := by
    by_contra hne
    have hnt : Nontrivial ↥φ.range := (Subgroup.nontrivial_iff_ne_bot φ.range).2 hne
    have hperf : Group.IsPerfect ↥φ.range :=
      Group.IsPerfect.ofSurjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
    exact Group.IsPerfect.not_isSolvable ↥φ.range inferInstance
  intro p hp
  have h1 : φ ⟨p, hp⟩ ∈ φ.range := ⟨_, rfl⟩
  rw [hr, Subgroup.mem_bot] at h1
  have h2 : (⟨p, hPH hp⟩ : ↥H) ∈ A.subgroupOf H := (QuotientGroup.eq_one_iff _).1 h1
  exact h2

private theorem plh_isComponentOf_subgroupOf_top {G : Type*} [Group G] {A K : Subgroup G}
    (hA : IsComponentOf A K) : CFSG.Open.IsComponentOf (A.subgroupOf K) ⊤ := by
  have hA' : CFSG.Open.IsComponentOf A K := isComponentOf_iff_open.mp hA
  refine ⟨le_top, ?_, ?_⟩
  · exact CFSG.Open.IsSubnormal.top_iff.mpr
      ((CFSG.Open.IsSubnormal.iff_subgroupOf hA'.1).mp hA'.2.1)
  · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe hA'.1) hA'.2.2

private theorem plh_commute_of_isComponentOf_ne {G : Type*} [Group G] [Finite G]
    {A B K : Subgroup G} (hA : IsComponentOf A K) (hB : IsComponentOf B K) (hne : A ≠ B) :
    ⁅A, B⁆ = ⊥ := by
  have hA' := plh_isComponentOf_subgroupOf_top hA
  have hB' := plh_isComponentOf_subgroupOf_top hB
  have hne' : A.subgroupOf K ≠ B.subgroupOf K := by
    intro h
    exact hne (by
      have h' := Subgroup.subgroupOf_inj.mp h
      rwa [inf_eq_left.mpr hA.1, inf_eq_left.mpr hB.1] at h')
  have h := CFSG.ComponentClassification.LocalComponents.commute_of_ne
    (A.subgroupOf K) (B.subgroupOf K) hA' hB' hne'
  have hmap := congrArg (Subgroup.map K.subtype) h
  rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA.1,
    Subgroup.map_subgroupOf_eq_of_le hB.1, Subgroup.map_bot] at hmap

private theorem plh_eq_of_isComponentOf_of_le {G : Type*} [Group G] [Finite G]
    {A B K : Subgroup G} (hA : IsComponentOf A K) (hB : IsComponentOf B K) (hAB : A ≤ B) :
    A = B := by
  have hA' := plh_isComponentOf_subgroupOf_top hA
  have hB' := plh_isComponentOf_subgroupOf_top hB
  have hle : A.subgroupOf K ≤ B.subgroupOf K := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hAB hx
  have h := CFSG.ComponentClassification.LocalComponents.eq_of_le
    (A.subgroupOf K) (B.subgroupOf K) hA' hB' hle
  have h' := Subgroup.subgroupOf_inj.mp h
  rwa [inf_eq_left.mpr hA.1, inf_eq_left.mpr hB.1] at h'

theorem torComp_eq_of_isComponentOf {G : Type} [Group G] [Finite G] {H P₀ P₁ J : Subgroup G}
    (hP₀ : P₀ ≤ H) (hP₁ : P₁ ≤ H) (hn₀ : (P₀.subgroupOf H).Normal)
    (hn₁ : (P₁.subgroupOf H).Normal) (hcomm : ∀ a ∈ P₀, ∀ b ∈ P₁, a * b = b * a)
    (hperf : ∀ K : Subgroup G, K ≤ H → ⁅K, K⁆ = K → K ≤ P₀ ⊔ P₁)
    (hs₀ : Group.IsSolvable ↥P₀ ∨ IsQuasisimple ↥P₀)
    (hs₁ : Group.IsSolvable ↥P₁ ∨ IsQuasisimple ↥P₁) (hJ : IsComponentOf J H) :
    J = P₀ ∨ J = P₁ := by
  have hJH : J ≤ H := hJ.1
  have hJq : IsQuasisimple ↥J := hJ.2.2
  have hJperf : Group.IsPerfect ↥J := ⟨hJq.1⟩
  have hJntriv : Nontrivial ↥J := CFSG.ComponentClassification.Quasisimple.nontrivial hJq
  have hJsol : ¬ Group.IsSolvable ↥J := Group.IsPerfect.not_isSolvable ↥J
  have hJle : J ≤ P₀ ⊔ P₁ := hperf J hJH (Subgroup.isPerfect_iff.mp hJperf)
  rcases hs₁ with hs₁sol | hs₁q
  ·
    have hJP0 : J ≤ P₀ :=
      plh_twoG_le_of_perfect_of_isSolvable hcomm hJle hJperf hs₁sol
    rcases hs₀ with hs₀sol | hs₀q
    · exact (hJsol (Group.isSolvable_of_isSolvable_injective
        (Subgroup.inclusion_injective hJP0))).elim
    · exact Or.inl (plh_eq_of_isComponentOf_of_le hJ
        ⟨hP₀, IsSubnormal.step hP₀ hn₀ (IsSubnormal.refl H), hs₀q⟩ hJP0)
  · rcases hs₀ with hs₀sol | hs₀q
    ·
      have hJP1 : J ≤ P₁ := plh_twoG_le_of_perfect_of_isSolvable
        (fun a ha b hb => (hcomm b hb a ha).symm)
        (hJle.trans (le_of_eq (sup_comm P₀ P₁))) hJperf hs₀sol
      exact Or.inr (plh_eq_of_isComponentOf_of_le hJ
        ⟨hP₁, IsSubnormal.step hP₁ hn₁ (IsSubnormal.refl H), hs₁q⟩ hJP1)
    ·
      by_cases hJ0 : J = P₀
      · exact Or.inl hJ0
      by_cases hJ1 : J = P₁
      · exact Or.inr hJ1
      exfalso
      have hcomp0 : IsComponentOf P₀ H :=
        ⟨hP₀, IsSubnormal.step hP₀ hn₀ (IsSubnormal.refl H), hs₀q⟩
      have hcomp1 : IsComponentOf P₁ H :=
        ⟨hP₁, IsSubnormal.step hP₁ hn₁ (IsSubnormal.refl H), hs₁q⟩
      have hcen0 : J ≤ Subgroup.centralizer (P₀ : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (plh_commute_of_isComponentOf_ne hJ hcomp0 hJ0)
      have hcen1 : J ≤ Subgroup.centralizer (P₁ : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (plh_commute_of_isComponentOf_ne hJ hcomp1 hJ1)
      have hab : ∀ j ∈ J, ∀ k ∈ J, j * k = k * j := by
        intro j hj k hk
        obtain ⟨a, ha, b, hb, rfl⟩ := (plh_mem_sup_iff_of_commute hcomm).1 (hJle hk)
        have hja : j * a = a * j :=
          (Subgroup.mem_centralizer_iff.mp (hcen0 hj) a ha).symm
        have hjb : j * b = b * j :=
          (Subgroup.mem_centralizer_iff.mp (hcen1 hj) b hb).symm
        calc j * (a * b) = (j * a) * b := by rw [mul_assoc]
          _ = (a * j) * b := by rw [hja]
          _ = a * (j * b) := by rw [mul_assoc]
          _ = a * (b * j) := by rw [hjb]
          _ = (a * b) * j := by rw [mul_assoc]
      have : IsMulCommutative ↥J :=
        IsMulCommutative.of_comm fun x y => Subtype.ext (hab x x.2 y y.2)
      exact hJsol inferInstance

end CFSG.StandardType.QTwo

end
