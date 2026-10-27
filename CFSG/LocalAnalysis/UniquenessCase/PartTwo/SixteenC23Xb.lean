module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23ModB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

variable {U : Type*} [CommGroup U] [Finite U] {Y₁ Y₂ : Subgroup U}
  {A₁ A₂ Mb : Subgroup (MulAut U)}

theorem c23_exists_fixed_sylow (h : C23Core Y₁ Y₂ A₁ A₂ Mb) {u₀ : U}
    (hu₀ : u₀ ∈ c23Omega Y₁ Y₂) {S : Subgroup (MulAut U)}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (A₁ ⊔ A₂))
    (hSfix : ∀ s ∈ S, (s : MulAut U) u₀ = u₀) :
    ∃ Xb : Subgroup (MulAut U), Xb ≤ A₁ ⊔ A₂ ∧ Nat.card Xb = 9 ∧
      (∀ x ∈ Xb, (x : MulAut U) u₀ = u₀) ∧
      ∀ j ∈ A₁ ⊔ A₂, (j : MulAut U) u₀ = u₀ → ∃ x ∈ Xb, ∃ s ∈ S, j = x * s := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : MulAction ↥(A₁ ⊔ A₂) U := MulAction.compHom U (A₁ ⊔ A₂).subtype
  have hA_Mb : A₁ ⊔ A₂ ≤ Mb := sup_le h.le₁ h.le₂
  have horb : MulAction.orbit ↥(A₁ ⊔ A₂) u₀ = c23Omega Y₁ Y₂ := by
    ext u
    constructor
    · intro hu
      rw [MulAction.mem_orbit_iff] at hu
      obtain ⟨a, rfl⟩ := hu
      simpa [MulAction.compHom_smul_def] using c23_omega_stable h (hA_Mb a.2) hu₀
    · intro hu
      obtain ⟨a, ha, b, hb, hab⟩ := c23_omega_trans h hu₀ hu
      refine ⟨⟨a * b, mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)⟩, ?_⟩
      show (a * b : MulAut U) u₀ = u
      simpa only [MulAut.mul_apply] using hab
  have hstabcard : Nat.card ↥(MulAction.stabilizer ↥(A₁ ⊔ A₂) u₀) = 576 := by
    have hidx := MulAction.index_stabilizer ↥(A₁ ⊔ A₂) u₀
    have hcard := Subgroup.card_mul_index (MulAction.stabilizer ↥(A₁ ⊔ A₂) u₀)
    rw [hidx, horb, c23_ncard_omega h, c23_core_card_sup h] at hcard
    omega
  set Stab : Subgroup (MulAut U) :=
    (A₁ ⊔ A₂) ⊓ MulAction.stabilizer (MulAut U) u₀ with hStab_def
  have hstabmap : (MulAction.stabilizer ↥(A₁ ⊔ A₂) u₀).map (A₁ ⊔ A₂).subtype = Stab := by
    ext g
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [hStab_def]
      refine ⟨a.2, ?_⟩
      change (A₁ ⊔ A₂).subtype a • u₀ = u₀
      simpa [MulAction.compHom_smul_def] using (MulAction.mem_stabilizer_iff.1 ha)
    · intro hg
      rw [hStab_def] at hg
      obtain ⟨hgA, hgstab⟩ := hg
      refine ⟨⟨g, hgA⟩, ?_, rfl⟩
      change (⟨g, hgA⟩ : ↥(A₁ ⊔ A₂)) • u₀ = u₀
      simpa [MulAction.compHom_smul_def] using (MulAction.mem_stabilizer_iff.1 hgstab)
  have hStabcard : Nat.card ↥Stab = 576 := by
    rw [← hstabmap]
    exact (Subgroup.card_subtype (A₁ ⊔ A₂)
      (MulAction.stabilizer ↥(A₁ ⊔ A₂) u₀)).trans hstabcard
  have hStab_le : Stab ≤ A₁ ⊔ A₂ := by
    rw [hStab_def]
    exact inf_le_left
  have hdvd : 3 ^ 2 ∣ Nat.card ↥Stab := by
    rw [hStabcard]
    norm_num
  obtain ⟨Q, hQcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥Stab) 3 (n := 2) hdvd
  have hXb_le_Stab : Q.map Stab.subtype ≤ Stab := Subgroup.map_subtype_le Q
  have hXbcard : Nat.card ↥(Q.map Stab.subtype) = 9 := by
    rw [Subgroup.card_subtype Stab Q, hQcard]
    norm_num
  have hXbfix : ∀ x ∈ Q.map Stab.subtype, (x : MulAut U) u₀ = u₀ := by
    rintro x ⟨q, -, rfl⟩
    have hq : (q : MulAut U) ∈ MulAction.stabilizer (MulAut U) u₀ := q.2.2
    simpa using (MulAction.mem_stabilizer_iff.1 hq)
  have hSstab : S ≤ Stab := by
    rw [hStab_def]
    refine le_inf hS.le ?_
    intro s hs
    rw [MulAction.mem_stabilizer_iff]
    exact hSfix s hs
  have hScard : Nat.card ↥S = 64 := by
    have h1 := hS.card_eq
    have hfac : (168 * 168 : ℕ).factorization 2 = 6 := by
      have hsplit : (168 * 168 : ℕ) = 2 ^ 6 * 441 := by norm_num
      rw [hsplit, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.factorization_pow_self Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (2 : ℕ) ∣ 441)]
    rw [c23_core_card_sup h, hfac] at h1
    norm_num at h1
    exact h1
  have hdisj : Q.map Stab.subtype ⊓ S = ⊥ := by
    have hcard1 : Nat.card ↥(Q.map Stab.subtype ⊓ S) = 1 := by
      have hdvd1 : Nat.card ↥(Q.map Stab.subtype ⊓ S) ∣ 9 := by
        have := Subgroup.card_dvd_of_le
          (inf_le_left : Q.map Stab.subtype ⊓ S ≤ Q.map Stab.subtype)
        rwa [hXbcard] at this
      have hdvd2 : Nat.card ↥(Q.map Stab.subtype ⊓ S) ∣ 64 := by
        have := Subgroup.card_dvd_of_le (inf_le_right : Q.map Stab.subtype ⊓ S ≤ S)
        rwa [hScard] at this
      exact Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 9 64) hdvd1 hdvd2
    rwa [Subgroup.card_eq_one] at hcard1
  let f : ↥(Q.map Stab.subtype) × ↥S → ↥Stab := fun p =>
    ⟨(p.1 : MulAut U) * (p.2 : MulAut U),
      Stab.mul_mem (hXb_le_Stab p.1.2) (hSstab p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨x₁, s₁⟩ ⟨x₂, s₂⟩ heq
    have heq' : (x₁ : MulAut U) * (s₁ : MulAut U) =
        (x₂ : MulAut U) * (s₂ : MulAut U) := congrArg Subtype.val heq
    have hkey : (x₂ : MulAut U)⁻¹ * (x₁ : MulAut U) =
        (s₂ : MulAut U) * (s₁ : MulAut U)⁻¹ := by
      have h2 : (x₂ : MulAut U)⁻¹ * ((x₁ : MulAut U) * (s₁ : MulAut U)) *
          (s₁ : MulAut U)⁻¹ = (s₂ : MulAut U) * (s₁ : MulAut U)⁻¹ := by
        rw [heq', ← mul_assoc, inv_mul_cancel, one_mul]
      rwa [mul_assoc, mul_assoc, mul_inv_cancel, mul_one] at h2
    have hmemX : (x₂ : MulAut U)⁻¹ * (x₁ : MulAut U) ∈ Q.map Stab.subtype :=
      (Q.map Stab.subtype).mul_mem ((Q.map Stab.subtype).inv_mem x₂.2) x₁.2
    have hmemS : (x₂ : MulAut U)⁻¹ * (x₁ : MulAut U) ∈ S := by
      rw [hkey]
      exact S.mul_mem s₂.2 (S.inv_mem s₁.2)
    have hone : (x₂ : MulAut U)⁻¹ * (x₁ : MulAut U) = 1 := by
      have hmem : (x₂ : MulAut U)⁻¹ * (x₁ : MulAut U) ∈ Q.map Stab.subtype ⊓ S :=
        ⟨hmemX, hmemS⟩
      rwa [hdisj, Subgroup.mem_bot] at hmem
    have hx : (x₁ : MulAut U) = (x₂ : MulAut U) := (inv_mul_eq_one.mp hone).symm
    have hs : (s₁ : MulAut U) = (s₂ : MulAut U) := by
      have h2 := heq'
      rw [hx] at h2
      exact mul_left_cancel h2
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hs)
  have hle : Nat.card ↥Stab ≤ Nat.card (↥(Q.map Stab.subtype) × ↥S) := by
    rw [Nat.card_prod, hXbcard, hScard, hStabcard]
  have hsurj : Function.Surjective f := (hf.bijective_of_nat_card_le hle).2
  refine ⟨Q.map Stab.subtype, ?_, hXbcard, hXbfix, ?_⟩
  · exact le_trans hXb_le_Stab hStab_le
  · intro j hjA hjfix
    have hjStab : j ∈ Stab := by
      rw [hStab_def]
      exact ⟨hjA, MulAction.mem_stabilizer_iff.2 hjfix⟩
    obtain ⟨p, hp⟩ := hsurj ⟨j, hjStab⟩
    exact ⟨(p.1 : MulAut U), p.1.2, (p.2 : MulAut U), p.2.2,
      (congrArg Subtype.val hp).symm⟩

theorem c23_fixed_of_mem_normalizer (h : C23Core Y₁ Y₂ A₁ A₂ Mb) {Xb : Subgroup (MulAut U)}
    (hX : Xb ≤ A₁ ⊔ A₂) (hcard : Nat.card Xb = 9) {u₀ : U} (hu₀ : u₀ ∈ c23Omega Y₁ Y₂)
    (hfix : ∀ x ∈ Xb, (x : MulAut U) u₀ = u₀) {n : MulAut U} (hn : n ∈ Mb)
    (hnX : n ∈ normalizer (Xb : Set (MulAut U))) : (n : MulAut U) u₀ = u₀ := by
  have hu' : (n : MulAut U) u₀ ∈ c23Omega Y₁ Y₂ := c23_omega_stable h hn hu₀
  have hfix' : ∀ x ∈ Xb, (x : MulAut U) ((n : MulAut U) u₀) = (n : MulAut U) u₀ := by
    intro x hx
    have hnX' : n⁻¹ ∈ normalizer (Xb : Set (MulAut U)) :=
      (normalizer (Xb : Set (MulAut U))).inv_mem hnX
    have hmem : n⁻¹ * x * n ∈ Xb := (Subgroup.mem_normalizer_iff.1 hnX' x).1 hx
    have h1 : (n⁻¹ * x * n : MulAut U) u₀ = u₀ := hfix _ hmem
    have h2 : (n * (n⁻¹ * x * n) : MulAut U) u₀ = (n : MulAut U) u₀ := by
      rw [MulAut.mul_apply, h1]
    have h3 : (x * n : MulAut U) = n * (n⁻¹ * x * n) := by group
    rw [← MulAut.mul_apply, h3]
    exact h2
  exact (c23_unique_fixed h hX hcard hu₀ hu' hfix hfix').symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
