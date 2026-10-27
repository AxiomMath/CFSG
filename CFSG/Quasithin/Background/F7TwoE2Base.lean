module

public import CFSG.Quasithin.Background.F7TwoDefs

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Open

variable {Q : Type*} [Group Q]

theorem mem_nonTwoConj_top {B : Subgroup Q} {q : Q} :
    q ∈ nonTwoConj B ⊤ ↔ ¬ IsPGroup 2 ↥(B ⊔ conjSubgroup B q) := by
  simp [nonTwoConj]

theorem pow_eq_one_of_mem_isPGroup {P : Subgroup Q} (hP : IsPGroup 2 P) {c : Q} (hc : c ∈ P) :
    ∃ k : ℕ, c ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨c, hc⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem mem_nonTwoConj_of_map {Q' : Type*} [Group Q'] (π : Q →* Q') {B : Subgroup Q} {q : Q}
    (h : π q ∈ nonTwoConj (B.map π) ⊤) : q ∈ nonTwoConj B ⊤ := by
  rw [mem_nonTwoConj_top] at h ⊢
  intro hP
  refine h ((hP.map π).to_le ?_)
  refine sup_le (Subgroup.map_mono le_sup_left) ?_
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  obtain ⟨b, hb, hbx⟩ := hx
  refine ⟨q⁻¹ * b * q, Subgroup.mem_sup_right ?_, ?_⟩
  · rw [mem_conjSubgroup_iff]
    simpa [mul_assoc] using hb
  · simp only [map_mul, map_inv, hbx]
    group

theorem comap_closure_le_closure_nonTwoConj (R : Subgroup Q) [R.Normal] {B : Subgroup Q}
    (hne : (nonTwoConj (B.map (QuotientGroup.mk' R)) ⊤).Nonempty) :
    (Subgroup.closure (nonTwoConj (B.map (QuotientGroup.mk' R)) ⊤)).comap
        (QuotientGroup.mk' R) ≤ Subgroup.closure (nonTwoConj B ⊤) := by
  set π := QuotientGroup.mk' R with hπ
  set Z := Subgroup.closure (nonTwoConj B ⊤) with hZ
  have hmem : ∀ x : Q, π x ∈ nonTwoConj (B.map π) ⊤ → x ∈ Z := fun x hx =>
    Subgroup.subset_closure (mem_nonTwoConj_of_map π hx)
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk'_surjective R y₀
  have hR : R ≤ Z := by
    intro r hr
    have hπr : π r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
    have h1 : x₀ * r ∈ Z := hmem _ (by
      rw [map_mul, hπr, mul_one]
      exact hy₀)
    simpa using Z.mul_mem (Z.inv_mem (hmem x₀ hy₀)) h1
  have hsub : nonTwoConj (B.map π) ⊤ ⊆ (Z.map π : Set (Q ⧸ R)) := by
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R y
    exact ⟨x, hmem x hy, rfl⟩
  have hcl : Subgroup.closure (nonTwoConj (B.map π) ⊤) ≤ Z.map π :=
    (Subgroup.closure_le _).mpr hsub
  intro q hq
  obtain ⟨x, hxZ, hx⟩ := hcl hq
  have h2 : x⁻¹ * q ∈ R := QuotientGroup.eq.mp hx
  have h3 : q = x * (x⁻¹ * q) := by group
  rw [h3]
  exact Z.mul_mem hxZ (hR h2)

theorem isPGroup_sup_conjSubgroup_conj {B : Subgroup Q} {c : Q} (hc : ∀ b ∈ B, c * b = b * c)
    {y : Q} (hP : IsPGroup 2 ↥(B ⊔ conjSubgroup B y)) :
    IsPGroup 2 ↥(B ⊔ conjSubgroup B (c * y * c⁻¹)) := by
  refine (hP.map (MulAut.conj c).toMonoidHom).to_le ?_
  have hcB : ∀ b ∈ B, c⁻¹ * b * c = b := fun b hb => by
    have := hc b hb
    calc c⁻¹ * b * c = c⁻¹ * (b * c) := by group
      _ = c⁻¹ * (c * b) := by rw [this]
      _ = b := by group
  refine sup_le (fun b hb => ⟨b, Subgroup.mem_sup_left hb, ?_⟩) (fun x hx => ?_)
  · show c * b * c⁻¹ = b
    rw [hc b hb]
    group
  · rw [mem_conjSubgroup_iff] at hx
    refine ⟨c⁻¹ * x * c, Subgroup.mem_sup_right ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    rw [mem_conjSubgroup_iff]
    have h1 := hcB _ hx
    have e : y * (c⁻¹ * x * c) * y⁻¹ = c⁻¹ * (c * y * c⁻¹ * x * (c * y * c⁻¹)⁻¹) * c := by group
    rw [e, h1]
    exact hx

theorem conj_mem_nonTwoConj {B : Subgroup Q} {c : Q} (hc : ∀ b ∈ B, c * b = b * c) {y : Q}
    (hy : y ∈ nonTwoConj B ⊤) : c * y * c⁻¹ ∈ nonTwoConj B ⊤ := by
  rw [mem_nonTwoConj_top] at hy ⊢
  intro hP
  have hc' : ∀ b ∈ B, c⁻¹ * b = b * c⁻¹ := fun b hb => by
    have := hc b hb
    calc c⁻¹ * b = c⁻¹ * (b * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * b) * c⁻¹ := by rw [this]
      _ = b * c⁻¹ := by group
  refine hy ?_
  have h1 := isPGroup_sup_conjSubgroup_conj hc' hP
  have e : c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y := by group
  rwa [e] at h1

theorem conj_mem_closure_nonTwoConj {B : Subgroup Q} {c : Q} (hc : ∀ b ∈ B, c * b = b * c)
    {x : Q} (hx : x ∈ Subgroup.closure (nonTwoConj B ⊤)) :
    c * x * c⁻¹ ∈ Subgroup.closure (nonTwoConj B ⊤) := by
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact Subgroup.subset_closure (conj_mem_nonTwoConj hc hy)
  | one => simp
  | mul y z _ _ hy hz =>
    have e : c * (y * z) * c⁻¹ = (c * y * c⁻¹) * (c * z * c⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hy hz
  | inv y _ hy =>
    have e : c * y⁻¹ * c⁻¹ = (c * y * c⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hy

end CFSG.Quasithin.F7Two
