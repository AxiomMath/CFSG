module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.CoprimeAutomorphisms
public import CFSG.GroupTheory.CenterlessInnerCentralizer

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

universe u

private def restrictAutL125 {G : Type u} [Group G] (R : Subgroup G) (γ : MulAut G)
    (h : ∀ g : G, g ∈ R ↔ γ g ∈ R) : MulAut R where
  toFun r := ⟨γ r.1, (h r.1).mp r.2⟩
  invFun r := ⟨γ.symm r.1, (h _).mpr (by simpa using r.2)⟩
  left_inv r := Subtype.ext (γ.symm_apply_apply _)
  right_inv r := Subtype.ext (γ.apply_symm_apply _)
  map_mul' a b := Subtype.ext (map_mul γ a.1 b.1)

private theorem restrictAutL125_pow_eq_one {G : Type u} [Group G] (R : Subgroup G)
    (γ : MulAut G) (h : ∀ g : G, g ∈ R ↔ γ g ∈ R) {m : ℕ} (hm : γ ^ m = 1) :
    restrictAutL125 R γ h ^ m = 1 := by
  have key : ∀ (n : ℕ) (r : R),
      (((restrictAutL125 R γ h ^ n) r : R) : G) = (γ ^ n) r := by
    intro n
    induction n with
    | zero => intro r; rfl
    | succ n ih =>
      intro r
      rw [pow_succ', pow_succ']
      exact congrArg γ (ih r)
  apply MulEquiv.ext
  intro r
  apply Subtype.ext
  rw [key m r, hm]
  rfl

private theorem mulAut_mul_conj_mul_inv_L125 {S : Type u} [Group S] (α : MulAut S) (s : S) :
    α * MulAut.conj s * α⁻¹ = MulAut.conj (α s) := by
  ext x
  simp [MulAut.conj_apply]

private theorem displacement_mem_inner_L125 {S : Type u} [Group S]
    (hOut : Odd (Nat.card (commutator (Outer S))))
    {V : Subgroup (MulAut S)} (hV : IsPGroup 2 V) {α : MulAut S}
    (hα : α ∈ Subgroup.normalizer (V : Set (MulAut S))) {v : MulAut S} (hv : v ∈ V) :
    v⁻¹ * (α * v * α⁻¹) ∈ inner S := by
  set d : MulAut S := v⁻¹ * (α * v * α⁻¹) with hd
  have hdV : d ∈ V :=
    V.mul_mem (V.inv_mem hv) ((Subgroup.mem_set_normalizer_iff.mp hα v).mp hv)
  set q : MulAut S →* Outer S := QuotientGroup.mk' (inner S)
  have hcomm : q d ∈ commutator (Outer S) := by
    have h : q d = ⁅(q v)⁻¹, q α⁆ := by
      rw [hd, map_mul, map_mul, map_mul, map_inv, map_inv, commutatorElement_def]
      group
    rw [h, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  obtain ⟨k, hk⟩ := hV ⟨d, hdV⟩
  have hdk : d ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h2 : orderOf (q d) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hdk, map_one])
  have hodd : orderOf (q d) ∣ Nat.card (commutator (Outer S)) := by
    rw [← Subgroup.orderOf_mk (q d) hcomm]
    exact orderOf_dvd_natCard _
  have h1 : orderOf (q d) = 1 :=
    Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left h2 ((Nat.coprime_two_left.mpr hOut).pow_left k)) hodd
  exact (QuotientGroup.eq_one_iff d).mp (orderOf_eq_one_iff.mp h1)

private theorem fix_of_conj_mem_L125 {S : Type u} [Group S] [Finite S]
    (hZ : Subgroup.center S = ⊥)
    (hW : ∀ R : Subgroup S, IsPGroup 2 R →
      ∃ A : Subgroup R, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ A.index ≤ 2)
    (hE : ∀ E : Subgroup S, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a ^ 2 = 1) →
      Nat.card E ≤ 4)
    (hWp : ∀ (R : Type u) [Group R] [Finite R], IsPGroup 2 R →
      ∀ A : Subgroup R, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → A.index ≤ 2 →
      (∀ E : Subgroup R, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a ^ 2 = 1) →
        Nat.card E ≤ 4) →
      ∀ β : MulAut R, Nat.Coprime (orderOf β) 6 → β = 1)
    {V : Subgroup (MulAut S)} (hV : IsPGroup 2 V) {α : MulAut S}
    (hα : α ∈ Subgroup.normalizer (V : Set (MulAut S))) (hcop : Nat.Coprime (orderOf α) 6)
    {s : S} (hs : (MulAut.conj s : MulAut S) ∈ V) : α s = s := by
  have hinj := CFSG.mulAutConj_injective_of_center_eq_bot hZ
  set R1 : Subgroup S := V.comap (MulAut.conj : S →* MulAut S)
  have hmem : ∀ x : S, x ∈ R1 ↔ (MulAut.conj x : MulAut S) ∈ V := fun x => Iff.rfl
  have hR1p : IsPGroup 2 R1 :=
    hV.of_injective ((MulAut.conj : S →* MulAut S).subgroupComap V)
      (MonoidHom.subgroupComap_injective _ _ hinj)
  obtain ⟨A, hA, hidx⟩ := hW R1 hR1p
  have hE1 : ∀ E : Subgroup R1, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a ^ 2 = 1) → Nat.card E ≤ 4 := by
    intro E hEc hE2
    have h := hE (E.map R1.subtype) ?_ ?_
    · rwa [Subgroup.card_map_of_injective R1.subtype_injective] at h
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (hEc a ha b hb)
    · rintro _ ⟨a, ha, rfl⟩
      exact congrArg Subtype.val (hE2 a ha)
  have hstab : ∀ x : S, x ∈ R1 ↔ α x ∈ R1 := by
    intro x
    rw [hmem, hmem, ← mulAut_mul_conj_mul_inv_L125]
    exact Subgroup.mem_set_normalizer_iff.mp hα _
  set β : MulAut R1 := restrictAutL125 R1 α hstab
  have hβcop : Nat.Coprime (orderOf β) 6 :=
    Nat.Coprime.coprime_dvd_left
      (orderOf_dvd_of_pow_eq_one (restrictAutL125_pow_eq_one R1 α hstab (pow_orderOf_eq_one α)))
      hcop
  have hβ1 : β = 1 := hWp R1 hR1p A hA hidx hE1 β hβcop
  exact congrArg (fun γ : MulAut R1 => ((γ ⟨s, hs⟩ : R1) : S)) hβ1

theorem res3L125_centralizes_of_normalizes {S : Type u} [Group S] [Finite S]
    (hZ : Subgroup.center S = ⊥)
    (hOut : Odd (Nat.card (commutator (Outer S))))
    (hW : ∀ R : Subgroup S, IsPGroup 2 R →
      ∃ A : Subgroup R, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ A.index ≤ 2)
    (hE : ∀ E : Subgroup S, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a ^ 2 = 1) →
      Nat.card E ≤ 4)
    (hWp : ∀ (R : Type u) [Group R] [Finite R], IsPGroup 2 R →
      ∀ A : Subgroup R, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → A.index ≤ 2 →
      (∀ E : Subgroup R, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a ^ 2 = 1) →
        Nat.card E ≤ 4) →
      ∀ β : MulAut R, Nat.Coprime (orderOf β) 6 → β = 1)
    {V : Subgroup (MulAut S)} (hV : IsPGroup 2 V) {α : MulAut S}
    (hα : α ∈ Subgroup.normalizer (V : Set (MulAut S))) (hcop : Nat.Coprime (orderOf α) 6) :
    ∀ v ∈ V, α * v = v * α := by
  intro v hv
  have hstabV : ∀ x : MulAut S, x ∈ V ↔ MulAut.conj α x ∈ V :=
    fun x => Subgroup.mem_set_normalizer_iff.mp hα x
  set φ : MulAut V := restrictAutL125 V (MulAut.conj α) hstabV
  have hφ : ∀ x : V, ((φ x : V) : MulAut S) = α * x * α⁻¹ := fun x => rfl
  set N : Subgroup V := (inner S).subgroupOf V
  have hφ1 : φ = 1 := by
    refine CFSG.ComponentClassification.CoprimeAutomorphisms.eq_one_of_fixed_displacement
      N φ (orderOf α) ?_ ?_ ?_ ?_
    · exact restrictAutL125_pow_eq_one V (MulAut.conj α) hstabV
        (by rw [← map_pow, pow_orderOf_eq_one, map_one])
    · obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp (hV.to_subgroup N)
      rw [hn]
      exact (Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 6) hcop).pow_right n
    · intro x hx
      apply Subtype.ext
      rw [hφ]
      obtain ⟨s, hs⟩ := Subgroup.mem_subgroupOf.mp hx
      have hsV : (MulAut.conj s : MulAut S) ∈ V := hs ▸ x.2
      have hfix := fix_of_conj_mem_L125 hZ hW hE hWp hV hα hcop hsV
      rw [← hs, mulAut_mul_conj_mul_inv_L125, hfix]
    · intro x
      refine Subgroup.mem_subgroupOf.mpr ?_
      exact displacement_mem_inner_L125 hOut hV hα x.2
  have h := congrArg (fun γ : MulAut V => ((γ ⟨v, hv⟩ : V) : MulAut S)) hφ1
  change α * v * α⁻¹ = v at h
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
