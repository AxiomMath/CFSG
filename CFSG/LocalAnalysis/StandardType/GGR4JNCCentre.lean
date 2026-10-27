module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetDecomp

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

private theorem ncc_one_le_of_card {K : Type} [Field K] [Finite K] {n : ℕ}
    (h : Nat.card K = 2 ^ n) : 1 ≤ n := by
  by_contra hn
  have hn0 : n = 0 := by omega
  subst hn0
  have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
  rw [h] at h2
  norm_num at h2

private theorem ncc_one_le_of_hasLabel_twA {f : ℕ} {R : Type} [Group R]
    (h : GGHasLabel ⟨.twA, 5, f⟩ R) : 1 ≤ f := by
  obtain ⟨K, hK, hKfin, hKcard, -⟩ := h
  haveI := hK
  haveI := hKfin
  have h2 : 1 ≤ 2 * f := by
    apply ncc_one_le_of_card (K := K) (n := 2 * f)
    rw [← pow_mul] at hKcard
    rw [Nat.mul_comm f 2] at hKcard
    exact hKcard
  omega

private theorem ncc_one_le_of_hasLabel_A {f : ℕ} {R : Type} [Group R]
    (h : GGHasLabel ⟨.A, 5, f⟩ R) : 1 ≤ f := by
  obtain ⟨K, hK, hKfin, hKcard, -⟩ := h
  haveI := hK
  haveI := hKfin
  exact ncc_one_le_of_card hKcard

private theorem ncc_one_le_of_hasLabel_twD {f : ℕ} {R : Type} [Group R]
    (h : GGHasLabel ⟨.twD, 4, f⟩ R) : 1 ≤ f := by
  unfold GGHasLabel at h
  rw [show CFSG.StandardType.LargeEvenRawDatum ⟨.twD, 4, f⟩ =
      LargeEvenRecipeOmegaMinus 3 (2 ^ f) from rfl] at h
  unfold LargeEvenRecipeOmegaMinus at h
  obtain ⟨K, hK, hKfin, hKcard, -⟩ := h
  haveI := hK
  haveI := hKfin
  exact ncc_one_le_of_card hKcard

private theorem ncc_center_bot {lab : LargeEvenLabel}
    (hAll : LargeEvenLabelAll lab fun R _ _ _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Subgroup.center L' = ⊥)
    {Y : Type} [Group Y] [Finite Y] (hperf : commutator Y = ⊤)
    (hlab : GGHasLabel lab (Y ⧸ Subgroup.center Y)) : Subgroup.center Y = ⊥ := by
  have hmain := hAll (fun R _ _ _ => Nonempty ((Y ⧸ Subgroup.center Y) ≃* R)) hlab
  obtain ⟨R, _, I, F, hQe, hP⟩ := largeEvenRawDatum_exists hmain
  obtain ⟨e⟩ := hQe
  let ψ : Y →* R := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))
  have hsurj : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker = Subgroup.center Y := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (Subgroup.center Y) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hP Y ψ hsurj hker.le hperf

theorem ggR4J_center_coprime_tw (hZk : GGCentreTrivialTwKnown) {G : Type} [Group G] [Finite G]
    {J : Subgroup G} (hJperf : commutator ↥J = ⊤) {f : ℕ}
    (hlab : (3 ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.twA, 5, f⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
      (3 ∣ 2 ^ f + 1 ∧ GGHasLabel ⟨.A, 5, f⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
      GGHasLabel ⟨.twD, 4, f⟩ (↥J ⧸ Subgroup.center ↥J)) :
    ∀ g ∈ Subgroup.center ↥J, Nat.Coprime 3 (orderOf g) := by
  have hbot : Subgroup.center ↥J = ⊥ := by
    rcases hlab with ⟨h3, hA⟩ | ⟨h3, hA⟩ | hA
    · exact ncc_center_bot ((hZk f (ncc_one_le_of_hasLabel_twA hA)).1 h3) hJperf hA
    · exact ncc_center_bot ((hZk f (ncc_one_le_of_hasLabel_A hA)).2.1 h3) hJperf hA
    · exact ncc_center_bot ((hZk f (ncc_one_le_of_hasLabel_twD hA)).2.2) hJperf hA
  intro g hg
  rw [hbot, Subgroup.mem_bot] at hg
  rw [hg, orderOf_one]
  exact Nat.coprime_one_right 3

end CFSG.StandardType

end
