module

public import CFSG.Quasithin.Background.F7TwoInvSporM22
public import CFSG.Sporadic.Mathieu.Asc1113M22Data

public section

namespace CFSG.LocalAnalysis.WeakClosure81.W115

open CFSG.Blueprint
open CFSG.Mathieu.Asc1113M22
open MulAction

def w115_fixCount (σ : Equiv.Perm (Fin 22)) : ℕ :=
  (Finset.univ.filter fun i => σ i = i).card

theorem w115_fixCount_conj (σ τ : Equiv.Perm (Fin 22)) :
    w115_fixCount (σ * τ * σ⁻¹) = w115_fixCount τ := by
  have e : {i : Fin 22 // τ i = i} ≃ {i : Fin 22 // (σ * τ * σ⁻¹) i = i} :=
    Equiv.subtypeEquiv σ (fun i => by
      show τ i = i ↔ (σ * τ * σ⁻¹) (σ i) = σ i
      have h1 : σ⁻¹ (σ i) = i := Equiv.symm_apply_apply σ i
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1]
      constructor
      · intro h; rw [h]
      · intro h; exact σ.injective h)
  simp only [w115_fixCount]
  rw [← Fintype.card_subtype (fun i => (σ * τ * σ⁻¹) i = i),
      ← Fintype.card_subtype (fun i => τ i = i)]
  exact Fintype.card_congr e.symm

theorem w115_fixCount_t : w115_fixCount t = 0 := by decide

theorem w115_fixCount_u : w115_fixCount u = 8 := by decide

theorem w115_fixCount_m22Rep1 :
    w115_fixCount CFSG.Sporadic.Schreier.m22Rep1 = 6 := by decide

section Centralizer


private theorem w115_two_transitive :
    IsMultiplyPretransitive ↥NativeSporadic.M22 (Fin 22) 2 :=
  CFSG.Sporadic.Mathieu.isMultiplyPretransitive_two CFSG.Sporadic.Mathieu.m22_hyp
    (by decide) (by decide)

private theorem w115_transitive (x : Fin 22) :
    ∃ g : ↥NativeSporadic.M22, (g : Equiv.Perm (Fin 22)) 0 = x := by
  haveI : IsMultiplyPretransitive ↥NativeSporadic.M22 (Fin 22) 2 := w115_two_transitive
  haveI : IsPretransitive ↥NativeSporadic.M22 (Fin 22) :=
    isPretransitive_of_is_two_pretransitive (G := ↥NativeSporadic.M22) (α := Fin 22)
  obtain ⟨g, hg⟩ := exists_smul_eq ↥NativeSporadic.M22 (0 : Fin 22) x
  exact ⟨g, by simpa [Subgroup.smul_def] using hg⟩

private theorem w115_stab_zero_transitive (a b : Fin 22) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ g : ↥NativeSporadic.M22, (g : Equiv.Perm (Fin 22)) 0 = 0 ∧
      (g : Equiv.Perm (Fin 22)) a = b := by
  have h2 : IsMultiplyPretransitive ↥NativeSporadic.M22 (Fin 22) 2 := w115_two_transitive
  rw [is_two_pretransitive_iff] at h2
  obtain ⟨g, hg0, hga⟩ := h2 (a := (0 : Fin 22)) (b := a) (c := (0 : Fin 22)) (d := b)
    (Ne.symm ha) (Ne.symm hb)
  exact ⟨g, by simpa [Subgroup.smul_def] using hg0, by simpa [Subgroup.smul_def] using hga⟩

private theorem w115_centralizer_fixes_zero {σ : Equiv.Perm (Fin 22)}
    (hσ : σ ∈ Subgroup.centralizer
      (CFSG.Sporadic.Mathieu.Asc1113M22.H0 : Set (Equiv.Perm (Fin 22)))) : σ 0 = 0 := by
  by_contra h
  have key : ∀ b : Fin 22, b ≠ 0 → b = σ 0 := by
    intro b hb
    obtain ⟨g, hg0, hgb⟩ := w115_stab_zero_transitive (σ 0) b h hb
    have hcomm := Subgroup.mem_centralizer_iff.mp hσ g g.2
    have h1 : (g : Equiv.Perm (Fin 22)) (σ 0) = σ 0 := by
      have := congrArg (fun p : Equiv.Perm (Fin 22) => p 0) hcomm
      simp only [Equiv.Perm.mul_apply] at this
      rw [hg0] at this
      exact this
    rw [hgb] at h1
    exact h1
  exact (by decide : (1 : Fin 22) ≠ 2) ((key 1 (by decide)).trans (key 2 (by decide)).symm)

theorem w115_centralizer_H0_eq_bot :
    Subgroup.centralizer
      (CFSG.Sporadic.Mathieu.Asc1113M22.H0 : Set (Equiv.Perm (Fin 22))) = ⊥ := by
  ext σ
  constructor
  · intro hσ
    rw [Subgroup.mem_bot]
    apply Equiv.ext
    intro x
    have hσ0 : σ 0 = 0 := w115_centralizer_fixes_zero hσ
    obtain ⟨g, hg0⟩ := w115_transitive x
    have hcomm := Subgroup.mem_centralizer_iff.mp hσ g g.2
    calc σ x = σ ((g : Equiv.Perm (Fin 22)) 0) := by rw [← hg0]
      _ = (g : Equiv.Perm (Fin 22)) (σ 0) := by
            have := congrArg (fun p : Equiv.Perm (Fin 22) => p 0) hcomm
            simp only [Equiv.Perm.mul_apply] at this
            exact this.symm
      _ = (g : Equiv.Perm (Fin 22)) 0 := by rw [hσ0]
      _ = x := hg0
  · intro hσ
    rw [Subgroup.mem_bot] at hσ
    rw [hσ]
    exact Subgroup.one_mem _

end Centralizer

theorem w115_t_not_mem_H0 :
    t ∉ CFSG.Sporadic.Mathieu.Asc1113M22.H0 := by
  intro ht
  have ht2 : orderOf t = 2 := by
    have h2 : t * t = 1 := by decide
    have h1 : t ≠ 1 := by decide
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rwa [pow_two]) h1
  obtain ⟨c, hc, hct⟩ := CFSG.Quasithin.F7Two.m22_inner_cover ht ht2
  have hfix : w115_fixCount t = w115_fixCount CFSG.Sporadic.Schreier.m22Rep1 := by
    rw [hct]
    exact w115_fixCount_conj (c : Equiv.Perm (Fin 22)) CFSG.Sporadic.Schreier.m22Rep1
  rw [w115_fixCount_t, w115_fixCount_m22Rep1] at hfix
  exact absurd hfix (by decide)

private theorem w115_range_S3_eq :
    Set.range S3 = Set.range S2 ∪ ({u} : Set (Equiv.Perm (Fin 22))) := by
  ext x
  simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · left; exact ⟨0, rfl⟩
    · left; exact ⟨1, rfl⟩
    · right; rfl
  · rintro (⟨i, rfl⟩ | rfl)
    · exact ⟨i.castSucc, by fin_cases i <;> rfl⟩
    · exact ⟨2, rfl⟩

private theorem w115_N0_eq_sup :
    CFSG.Sporadic.Mathieu.Asc1113M22.N0 =
      CFSG.Sporadic.Mathieu.Asc1113M22.H0 ⊔
        Subgroup.closure ({u} : Set (Equiv.Perm (Fin 22))) := by
  rw [show CFSG.Sporadic.Mathieu.Asc1113M22.N0 =
      Subgroup.closure (Set.range S3) from rfl]
  rw [show CFSG.Sporadic.Mathieu.Asc1113M22.H0 =
      Subgroup.closure (Set.range S2) from
    CFSG.Sporadic.Mathieu.Asc1113M22.closure_range_S2.symm]
  rw [w115_range_S3_eq, Subgroup.closure_union]

theorem w115_H0_le_N0 : CFSG.Sporadic.Mathieu.Asc1113M22.H0 ≤
    CFSG.Sporadic.Mathieu.Asc1113M22.N0 := by
  rw [show CFSG.Sporadic.Mathieu.Asc1113M22.H0 =
      Subgroup.closure (Set.range S2) from
    CFSG.Sporadic.Mathieu.Asc1113M22.closure_range_S2.symm]
  rw [show CFSG.Sporadic.Mathieu.Asc1113M22.N0 =
      Subgroup.closure (Set.range S3) from rfl]
  apply Subgroup.closure_mono
  rintro x ⟨i, rfl⟩
  exact ⟨i.castSucc, by fin_cases i <;> rfl⟩

theorem w115_N0_mem_cases_u
    (x : CFSG.Sporadic.Mathieu.Asc1113M22.N0) :
    (∃ h : CFSG.Sporadic.Mathieu.Asc1113M22.H0,
        (x : Equiv.Perm (Fin 22)) = h) ∨
      (∃ h : CFSG.Sporadic.Mathieu.Asc1113M22.H0,
        (x : Equiv.Perm (Fin 22)) = h * u) := by
  have h2 : u * u = 1 := CFSG.Sporadic.Mathieu.Asc1113M22.uU_sq
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right h2
  let K : Subgroup (Equiv.Perm (Fin 22)) :=
    { carrier := {y | (∃ h : CFSG.Sporadic.Mathieu.Asc1113M22.H0, y = h) ∨
        (∃ h : CFSG.Sporadic.Mathieu.Asc1113M22.H0, y = h * u)}
      one_mem' := Or.inl ⟨1, by simp⟩
      mul_mem' := by
        rintro a b (⟨ha, rfl⟩ | ⟨ha, rfl⟩) (⟨hb, rfl⟩ | ⟨hb, rfl⟩)
        · exact Or.inl ⟨ha * hb, by rw [Subgroup.coe_mul]⟩
        · exact Or.inr ⟨ha * hb, by rw [Subgroup.coe_mul, mul_assoc]⟩
        · refine Or.inr ⟨ha * ⟨u * ↑hb * u⁻¹,
              CFSG.Sporadic.Mathieu.Asc1113M22.u_conj_mem hb.2⟩, ?_⟩
          rw [Subgroup.coe_mul]
          show ha * u * ↑hb = ha * (u * ↑hb * u⁻¹) * u
          rw [hu_inv]
          simp [mul_assoc, h2]
        · refine Or.inl ⟨ha * ⟨u * ↑hb * u⁻¹,
              CFSG.Sporadic.Mathieu.Asc1113M22.u_conj_mem hb.2⟩, ?_⟩
          rw [Subgroup.coe_mul]
          show ha * u * (↑hb * u) = ha * (u * ↑hb * u⁻¹)
          rw [hu_inv]
          simp [mul_assoc, h2]
      inv_mem' := by
        rintro a (⟨ha, rfl⟩ | ⟨ha, rfl⟩)
        · exact Or.inl ⟨ha⁻¹, by rw [Subgroup.coe_inv]⟩
        · refine Or.inr ⟨⟨u * ↑ha⁻¹ * u⁻¹,
              CFSG.Sporadic.Mathieu.Asc1113M22.u_conj_mem
                (CFSG.Sporadic.Mathieu.Asc1113M22.H0.inv_mem ha.2)⟩, ?_⟩
          show (ha * u)⁻¹ = (u * ↑ha⁻¹ * u⁻¹) * u
          simp [hu_inv, mul_assoc, h2] }
  have hH : CFSG.Sporadic.Mathieu.Asc1113M22.H0 ≤ K := by
    intro y hy
    exact Or.inl ⟨⟨y, hy⟩, rfl⟩
  have hU : Subgroup.closure ({u} : Set (Equiv.Perm (Fin 22))) ≤ K := by
    rw [Subgroup.closure_le]
    rintro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact Or.inr ⟨1, by simp⟩
  have hsup : CFSG.Sporadic.Mathieu.Asc1113M22.H0 ⊔
      Subgroup.closure ({u} : Set (Equiv.Perm (Fin 22))) ≤ K := sup_le hH hU
  have hx : (x : Equiv.Perm (Fin 22)) ∈ CFSG.Sporadic.Mathieu.Asc1113M22.H0 ⊔
      Subgroup.closure ({u} : Set (Equiv.Perm (Fin 22))) := by
    rw [← w115_N0_eq_sup]
    exact x.2
  exact hsup hx

theorem w115_N0_mem_cases_t
    (x : CFSG.Sporadic.Mathieu.Asc1113M22.N0) :
    (∃ h : CFSG.Sporadic.Mathieu.Asc1113M22.H0,
        (x : Equiv.Perm (Fin 22)) = h) ∨
      (∃ h : CFSG.Sporadic.Mathieu.Asc1113M22.H0,
        (x : Equiv.Perm (Fin 22)) = h * t) := by
  rcases w115_N0_mem_cases_u x with ⟨h, hh⟩ | ⟨h, hu⟩
  · exact Or.inl ⟨h, hh⟩
  · have htN0 : t ∈ CFSG.Sporadic.Mathieu.Asc1113M22.N0 :=
      CFSG.Sporadic.Mathieu.Asc1113M22.t_mem_N0
    have ht_not : t ∉ CFSG.Sporadic.Mathieu.Asc1113M22.H0 := w115_t_not_mem_H0
    rcases w115_N0_mem_cases_u ⟨t, htN0⟩ with ⟨h', hh'⟩ | ⟨h', hu'⟩
    · exact absurd hh' (fun heq => ht_not (by
        have h2 : (h' : Equiv.Perm (Fin 22)) ∈ CFSG.Sporadic.Mathieu.Asc1113M22.H0 := h'.2
        rw [← heq] at h2
        exact h2))
    · refine Or.inr ⟨h * h'⁻¹, ?_⟩
      have hu'' : t = (h' : Equiv.Perm (Fin 22)) * u := hu'
      rw [hu, hu'']
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group

end CFSG.LocalAnalysis.WeakClosure81.W115
