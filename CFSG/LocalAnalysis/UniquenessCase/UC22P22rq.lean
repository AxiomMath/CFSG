module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

section Hall

theorem uc22p22r_exists_conj_le {X A Y : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hXp : IsPGroup p X) (hXY : X ≤ Y) {k : ℕ} (hk : (A.subgroupOf Y).index = 2 ^ k) :
    ∃ y ∈ Y, ∀ x ∈ X, y⁻¹ * x * y ∈ A := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hXp' : IsPGroup p ↥(X.subgroupOf Y) :=
    hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hXY).symm
  have hndvd : ¬ p ∣ Nat.card (↥Y ⧸ A.subgroupOf Y) := by
    rw [← Subgroup.index_eq_card, hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  obtain ⟨c, hc⟩ := hXp'.nonempty_fixed_point_of_prime_not_dvd_card (↥Y ⧸ A.subgroupOf Y) hndvd
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
  refine ⟨y, y.2, fun x hx => ?_⟩
  have h1 := hc ⟨⟨x, hXY hx⟩, hx⟩
  have h2 : ((⟨x, hXY hx⟩ * y : ↥Y) : ↥Y ⧸ A.subgroupOf Y) = (y : ↥Y ⧸ A.subgroupOf Y) := h1
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h2
  have h3 : ((((⟨x, hXY hx⟩ : ↥Y) * y)⁻¹ * y : ↥Y) : G) = (y : G)⁻¹ * x⁻¹ * y := by simp [mul_assoc]
  rw [h3] at h2
  have h4 := A.inv_mem h2
  simpa [mul_assoc] using h4

theorem uc22p22r_mul_eq_of_card {A T Y : Subgroup G} (hAY : A ≤ Y) (hTY : T ≤ Y) (hAT : A ⊓ T = ⊥)
    (hcard : Nat.card A * Nat.card T = Nat.card Y) : (A : Set G) * (T : Set G) = (Y : Set G) := by
  classical
  have hsub : (A : Set G) * (T : Set G) ⊆ (Y : Set G) := by
    rintro _ ⟨a, ha, t, ht, rfl⟩
    exact Y.mul_mem (hAY ha) (hTY ht)
  have hinj : Set.InjOn (fun p : G × G => p.1 * p.2) ((A : Set G) ×ˢ (T : Set G)) := by
    rintro ⟨a, t⟩ ⟨ha, ht⟩ ⟨a', t'⟩ ⟨ha', ht'⟩ h
    simp only at h
    have h1 : a'⁻¹ * a = t' * t⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * t) * t⁻¹ := by group
        _ = a'⁻¹ * (a' * t') * t⁻¹ := by rw [h]
        _ = t' * t⁻¹ := by group
    have h2 : a'⁻¹ * a ∈ A ⊓ T := ⟨A.mul_mem (A.inv_mem ha') ha, h1 ▸ T.mul_mem ht' (T.inv_mem ht)⟩
    rw [hAT, Subgroup.mem_bot] at h2
    have hae : a = a' := by
      calc a = a' * (a'⁻¹ * a) := by group
        _ = a' := by rw [h2, mul_one]
    have hte : t = t' := by
      rw [hae] at h
      exact mul_left_cancel h
    rw [hae, hte]
  have hncard : ((A : Set G) * (T : Set G)).ncard = (Y : Set G).ncard := by
    rw [← Set.image_mul_prod, hinj.ncard_image, Set.ncard_prod, ← Nat.card_coe_set_eq,
      ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact hcard
  exact Set.eq_of_subset_of_ncard_le hsub hncard.ge (Set.toFinite _)

theorem uc22p22r_permutes_of_hall {A T Y : Subgroup G} (hAY : A ≤ Y) (hAo : Odd (Nat.card A))
    {k : ℕ} (hY : Nat.card Y = Nat.card A * 2 ^ k) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T Y) :
    Permutes A T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTY := hT.le
  have hTcard : Nat.card T = 2 ^ k := by
    rw [hT.card_eq, hY, Nat.factorization_mul (Nat.card_pos.ne') (by positivity),
      Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two]
    · have h0 : (Nat.card A).factorization 2 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.2 hAo) (even_iff_two_dvd.2 h))
      rw [h0, zero_add]
  have hAT : A ⊓ T = ⊥ := by
    refine Subgroup.eq_bot_of_card_eq _ ?_
    have h1 : Nat.card ↥(A ⊓ T) ∣ Nat.card A := Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(A ⊓ T) ∣ 2 ^ k := hTcard ▸ Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    rcases j with _ | j
    · simpa using hj
    · exfalso
      rw [hj, pow_succ] at h1
      exact (Nat.not_even_iff_odd.2 hAo) (even_iff_two_dvd.2 ((dvd_mul_left 2 _).trans h1))
  have hTA : T ⊓ A = ⊥ := by rw [inf_comm]; exact hAT
  have h1 := uc22p22r_mul_eq_of_card hAY hTY hAT (by rw [hY, hTcard])
  have h2 := uc22p22r_mul_eq_of_card hTY hAY hTA (by rw [hY, hTcard, mul_comm])
  unfold Permutes
  rw [h1, h2]

end Hall

section Unique

theorem uc22p22r_mem_of_conj_le_of_unique (D : Data G) {X : Subgroup G} (hU : X ∈ uniqueSet D.M) {g : G}
    (hg : ∀ y ∈ X, g⁻¹ * y * g ∈ D.M) : g ∈ D.M := by
  have hXg : X ≤ D.M.map (MulAut.conj g).toMonoidHom := by
    intro y hy
    refine ⟨g⁻¹ * y * g, hg y hy, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have h := hU.2 g hXg
  rw [← CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing D.M D.maxLocal]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h

theorem uc22p22r_mem_of_conj_mem_of_unique (D : Data G) {x : G} (hU : Subgroup.zpowers x ∈ uniqueSet D.M)
    {g : G} (hg : g⁻¹ * x * g ∈ D.M) : g ∈ D.M := by
  refine uc22p22r_mem_of_conj_le_of_unique D hU fun y hy => ?_
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have e : g⁻¹ * x ^ i * g = (g⁻¹ * x * g) ^ i := by
    simpa using (conj_zpow (a := g⁻¹) (b := x) (i := i)).symm
  rw [e]
  exact D.M.zpow_mem hg i

theorem uc22p22r_card_eq_mul_index {A Y : Subgroup G} (hAY : A ≤ Y) :
    Nat.card Y = Nat.card A * (A.subgroupOf Y).index := by
  have h1 := Subgroup.card_mul_index (A.subgroupOf Y)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv] at h1
  exact h1.symm

end Unique

end CFSG.LocalAnalysis.UniquenessCase.UC22
