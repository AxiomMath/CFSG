module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitness

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

theorem not_exists_injective_of_ordProj_two_lt {H K : Type*} [Group H] [Group K] [Finite K]
    (Q : Subgroup K) [Q.Normal] (hQ : IsPGroup 2 Q) {a : ℕ}
    (hab : ∀ A : Subgroup K, A ≤ Q → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → Nat.card A ≤ a)
    (hH : ∀ N : Subgroup H, N.Normal → IsPGroup 2 N → ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hlt : a * ordProj[2] (Nat.card (K ⧸ Q)) < ordProj[2] (Nat.card H)) :
    ¬ ∃ φ : H →* K, Function.Injective φ := by
  rintro ⟨φ, hφ⟩
  have : Finite H := Finite.of_injective φ hφ
  set f : H →* K ⧸ Q := (QuotientGroup.mk' Q).comp φ with hf
  have hNQ : f.ker ≤ Q.comap φ := by
    intro h hh
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hh
    exact hh
  have hNc := hH f.ker (MonoidHom.normal_ker f) ((hQ.comap_of_injective φ hφ).to_le hNQ)
  have hcardN : Nat.card f.ker ≤ a := by
    rw [← Subgroup.card_map_of_injective hφ]
    refine hab _ ?_ ?_
    · rintro _ ⟨h, hh, rfl⟩
      exact hNQ hh
    · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      rw [← map_mul, ← map_mul, hNc u hu v hv]
  have hcard : Nat.card H = Nat.card f.ker * Nat.card f.range :=
    (Subgroup.card_ker_mul_card_range f).symm
  have hdvd : Nat.card f.range ∣ Nat.card (K ⧸ Q) := Subgroup.card_subgroup_dvd_card _
  have hN0 : Nat.card f.ker ≠ 0 := Nat.card_pos.ne'
  have hR0 : Nat.card f.range ≠ 0 := Nat.card_pos.ne'
  have hKQ0 : Nat.card (K ⧸ Q) ≠ 0 := Nat.card_pos.ne'
  have h2 : ordProj[2] (Nat.card f.ker) ≤ a := (Nat.ordProj_le 2 hN0).trans hcardN
  have h3 : ordProj[2] (Nat.card f.range) ≤ ordProj[2] (Nat.card (K ⧸ Q)) :=
    Nat.le_of_dvd (by positivity) (Nat.ordProj_dvd_ordProj_of_dvd hKQ0 hdvd 2)
  have hle : ordProj[2] (Nat.card H) ≤ a * ordProj[2] (Nat.card (K ⧸ Q)) :=
    calc ordProj[2] (Nat.card H)
        = ordProj[2] (Nat.card f.ker) * ordProj[2] (Nat.card f.range) := by
          rw [hcard, Nat.ordProj_mul 2 hN0 hR0]
      _ ≤ a * ordProj[2] (Nat.card (K ⧸ Q)) := Nat.mul_le_mul h2 h3
  exact (not_le.mpr hlt) hle

theorem ggRootFusionAlt_of_ordProj_two_lt {G : Type*} [Group G] [Finite G] {G₀ M : Subgroup G}
    {r s : G} (Q : Subgroup ↥(ggCentOTwoPrime G₀ r)) [Q.Normal] (hQ : IsPGroup 2 Q) {a : ℕ}
    (hab : ∀ A : Subgroup ↥(ggCentOTwoPrime G₀ r), A ≤ Q →
      (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → Nat.card A ≤ a)
    (hH : ∀ N : Subgroup ↥(ggCentOTwoPrime G₀ s), N.Normal → IsPGroup 2 N →
      ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hlt : a * ordProj[2] (Nat.card (↥(ggCentOTwoPrime G₀ r) ⧸ Q)) <
      ordProj[2] (Nat.card ↥(ggCentOTwoPrime G₀ s))) :
    GGRootFusionAlt G₀ M r s :=
  Or.inr (Or.inr (not_exists_injective_of_ordProj_two_lt Q hQ hab hH hlt))

theorem ggRootFusionWitnessAlt_of_ordProj_two_lt {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs D E G₀ M : Subgroup G} {t : StatedLieTag} {f : ℕ} {r s : G}
    (Q : Subgroup ↥(ggCentOTwoPrime G₀ r)) [Q.Normal] (hQ : IsPGroup 2 Q) {a : ℕ}
    (hab : ∀ A : Subgroup ↥(ggCentOTwoPrime G₀ r), A ≤ Q →
      (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → Nat.card A ≤ a)
    (hH : ∀ N : Subgroup ↥(ggCentOTwoPrime G₀ s), N.Normal → IsPGroup 2 N →
      ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hlt : a * ordProj[2] (Nat.card (↥(ggCentOTwoPrime G₀ r) ⧸ Q)) <
      ordProj[2] (Nat.card ↥(ggCentOTwoPrime G₀ s))) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t f r s :=
  Or.inr (Or.inr (not_exists_injective_of_ordProj_two_lt Q hQ hab hH hlt))

end CFSG.StandardType
