module

public import CFSG.Sporadic.ThI301.RowLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Max
public import Certificates.Certificate810303
public import CFSG.Sporadic.ThI301.RowBasic

public noncomputable section

namespace CFSG.Sporadic.ThI301

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Recog CFSG.Sporadic.Th.Recog.MFactsB
  CFSG.LocalAnalysis.GLTheoremA.H301

theorem a9_facts : ∀ X : Equiv.Perm (Fin 9), X * X = 1 → X ≠ 1 →
    ∃ Y ∈ a9Conj, X * (Y * X * Y⁻¹) ≠ Y * X * Y⁻¹ * X :=
  Certificates.certificate810303


private theorem exists_mem_M_of_not_le {R : Subgroup J} (hR : IsPGroup 2 R) (hQR : Max3.Q ≤ R)
    (hne : ¬ R ≤ Max3.Q) : ∃ x ∈ R, x ∈ Max3.M ∧ x ∉ Max3.Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hR.isNilpotent
  set Q' : Subgroup R := Max3.Q.subgroupOf R
  have hlt : Q' < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hne fun r hr => ?_
    have h1 : (⟨r, hr⟩ : R) ∈ Q' := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 h1
  obtain ⟨y, hyN, hyQ⟩ := SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent Q' hlt)
  have hconj : ∀ u : R, u ∈ Subgroup.normalizer (Q' : Set R) → ∀ q ∈ Max3.Q,
      (u : J) * q * (u : J)⁻¹ ∈ Max3.Q := by
    intro u hu q hq
    have h1 := ((Subgroup.mem_normalizer_iff (G := ↥R)).1 hu ⟨q, hQR hq⟩).1
      (Subgroup.mem_subgroupOf.2 hq)
    have h2 := Subgroup.mem_subgroupOf.1 h1
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h2
  have hN : (y : J) ∈ Subgroup.normalizer (Max3.Q : Set J) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨hconj y hyN q, fun hq => ?_⟩
    have h := hconj y⁻¹ ((Subgroup.normalizer (Q' : Set R)).inv_mem hyN) _ hq
    rw [Subgroup.coe_inv, inv_inv] at h
    have e : ((y : J))⁻¹ * ((y : J) * q * (y : J)⁻¹) * (y : J) = q := by group
    rwa [e] at h
  exact ⟨y, y.2, mem_M_of_mem_normalizer hN, fun h => hyQ (Subgroup.mem_subgroupOf.2 h)⟩

private abbrev φ : ↥Max3.M →* Equiv.Perm (Fin 9) :=
  (alternatingGroup (Fin 9)).subtype.comp Max3.InvRep.kap

private theorem ω₁_mem_B1 : ((ω₁ : ↥Max3.M) : J) ∈ B1 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

private theorem ω₂_mem_B1 : ((ω₂ : ↥Max3.M) : J) ∈ B1 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

private theorem t_mem_B1 : ((tLetter : ↥Max3.M) : J) ∈ B1 :=
  Subgroup.subset_closure (Set.mem_insert _ _)

private theorem phi_facts : φ ω₂ = permW2 ∧ φ (ω₁ * ω₂) = permW1 * permW2 ∧
    φ (tLetter * ω₂) = permT * permW2 := by
  refine ⟨coe_kap_ω₂, ?_, ?_⟩
  · rw [map_mul]
    exact congrArg₂ (· * ·) coe_kap_ω₁ coe_kap_ω₂
  · rw [map_mul]
    exact congrArg₂ (· * ·) coe_kap_tLetter coe_kap_ω₂

theorem eq_Q_of_invariant (R : Subgroup J) (hR : IsPGroup 2 R)
    (hB : B1 ≤ Subgroup.normalizer (R : Set J)) (hQR : Max3.Q ≤ R) : R = Max3.Q := by
  refine le_antisymm ?_ hQR
  by_contra hne
  obtain ⟨x, hxR, hxM, hxQ⟩ := exists_mem_M_of_not_le hR hQR hne
  let TC : Subgroup ↥Max3.M := R.comap Max3.M.subtype
  let S : Subgroup (Equiv.Perm (Fin 9)) := TC.map φ
  have hS2 : IsPGroup 2 S := (hR.comap_of_injective _ Max3.M.subtype_injective).map φ
  have hSne : S ≠ ⊥ := by
    intro hS
    have hmem : φ ⟨x, hxM⟩ ∈ S :=
      Subgroup.mem_map_of_mem φ (show Max3.M.subtype ⟨x, hxM⟩ ∈ R from hxR)
    rw [hS, Subgroup.mem_bot] at hmem
    have h1 : Max3.InvRep.kap ⟨x, hxM⟩ = 1 := Subtype.ext hmem
    exact hxQ (Max3.InvRep.kap_eq_one_iff.1 h1)
  obtain ⟨X, hXS, hX1, hX2, hXc⟩ := exists_central_involution hS2 hSne
  have hnorm : ∀ c : ↥Max3.M, (c : J) ∈ B1 →
      φ c ∈ Subgroup.normalizer (S : Set (Equiv.Perm (Fin 9))) :=
    fun c hc => Subgroup.le_normalizer_map φ (Subgroup.mem_map_of_mem φ
      (Subgroup.le_normalizer_comap Max3.M.subtype (hB hc)))
  obtain ⟨h1, h2, h3⟩ := phi_facts
  obtain ⟨Y, hY, hYX⟩ := a9_facts X hX2 hX1
  have hYN : Y ∈ Subgroup.normalizer (S : Set (Equiv.Perm (Fin 9))) := by
    simp only [a9Conj, List.mem_cons, List.mem_nil_iff, or_false] at hY
    rcases hY with rfl | rfl | rfl
    · rw [← h1]
      exact hnorm ω₂ ω₂_mem_B1
    · rw [← h2]
      refine hnorm (ω₁ * ω₂) ?_
      rw [Subgroup.coe_mul]
      exact B1.mul_mem ω₁_mem_B1 ω₂_mem_B1
    · rw [← h3]
      refine hnorm (tLetter * ω₂) ?_
      rw [Subgroup.coe_mul]
      exact B1.mul_mem t_mem_B1 ω₂_mem_B1
  exact hYX (hXc _ ((Subgroup.mem_normalizer_iff.1 hYN X).1 hXS)).eq

end CFSG.Sporadic.ThI301
