module

public import CFSG.Quasithin.Vol2.KGNatSp4Flag

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.Open (pCoreOf)

namespace KA

theorem exists_flag_coords {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) {W : Type*} [CommGroup W] (hW : ∀ w : W, w ^ 2 = 1)
    {H : Subgroup (MulAut W)} {Z : Subgroup W} {π : ↥(StatedSp 2 K) →* ↥H}
    (hπ : (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ Z π) {P : Subgroup (MulAut W)}
    (hP : QuasithinUnique.IsSylowTwoOf P H) {U₁ U₂ U₃ : Subgroup W}
    (hU₁ : Ch11.SecA.IsFlagW H P Z (2 ^ n) 1 U₁) (hU₂ : Ch11.SecA.IsFlagW H P Z (2 ^ n) 2 U₂)
    (hU₃ : Ch11.SecA.IsFlagW H P Z (2 ^ n) 3 U₃) :
    ∃ (f : W → (Fin 2 ⊕ Fin 2 → K)) (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
      (g : StatedSp 2 K),
      (∀ x : MulAut W, x ∈ P ↔ ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥H) : MulAut W)) ∧
        U₁ = hf.pre (gmapSp g (spLine K)).toAddSubgroup ∧
        U₂ = hf.pre (gmapSp g (spPlane K)).toAddSubgroup ∧
        U₃ = hf.pre (gmapSp g (spHyp K)).toAddSubgroup := by
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usp hK (by omega) hf hP
  rw [← hK] at hU₁ hU₂ hU₃
  obtain ⟨S₁, hS₁, hc₁, rfl⟩ := exists_eq_pre_of_isFlagW_sp hW hf hg hU₁
  obtain ⟨S₂, hS₂, hc₂, rfl⟩ := exists_eq_pre_of_isFlagW_sp hW hf hg hU₂
  obtain ⟨S₃, hS₃, hc₃, rfl⟩ := exists_eq_pre_of_isFlagW_sp hW hf hg hU₃
  exact ⟨f, hf, g, hg, by rw [(eq_std_of_stable_sp hS₁).1 (by rw [hc₁, pow_one])],
    by rw [(eq_std_of_stable_sp hS₂).2.1 hc₂], by rw [(eq_std_of_stable_sp hS₃).2.2 hc₃]⟩

theorem eq_of_isSylowTwoOf_le {G : Type*} [Group G] [Finite G] {R P Γ : Subgroup G}
    (hR : QuasithinUnique.IsSylowTwoOf R Γ) (hRP : R ≤ P) (hPΓ : P ≤ Γ) (hP : IsPGroup 2 P) :
    R = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hodd⟩ := hR
  have h1 : R.relIndex P * P.relIndex Γ = R.relIndex Γ :=
    Subgroup.relIndex_mul_relIndex R P Γ hRP hPΓ
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have h2 : R.relIndex P ∣ 2 ^ k := hk ▸ Subgroup.relIndex_dvd_card R P
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have h3 : R.relIndex P = 1 := by
    rcases j with _ | j
    · simpa using hj
    · exfalso
      apply hodd
      change 2 ∣ R.relIndex Γ
      rw [← h1, hj]
      exact Dvd.dvd.mul_right (dvd_pow_self 2 (Nat.succ_ne_zero j)) _
  exact le_antisymm hRP (Subgroup.relIndex_eq_one.mp h3)

variable {K : Type} [Field K]

theorem eq_spPlane_of_stable [Finite K] {S : AddSubgroup (Fin 2 ⊕ Fin 2 → K)}
    (h1 : ∀ x ∈ spLine K, x ∈ S) (h3 : ∀ x ∈ S, x ∈ spHyp K)
    (hq : ∀ t : K, ∀ x ∈ S, mat 2 K (qSp 0 0 t) *ᵥ x ∈ S) (hcard : Nat.card S = Nat.card K ^ 2) :
    ∀ x, x ∈ S ↔ x ∈ spPlane K := by
  have hle : ∀ v ∈ S, v (.inr 1) ≠ 0 → (spPlane K).toAddSubgroup ≤ S := by
    intro v hv hv3 x hx
    have he1 : ∀ c : K, c • vec4 0 1 0 0 ∈ S := by
      intro c
      have h := S.sub_mem (hq (c / v (.inr 1)) v hv) hv
      convert h using 1
      rw [qSp_mulVec]
      refine vec4_eq ?_ ?_ ?_ ?_ <;> simp [vec4]
      field_simp
    obtain ⟨hx2, hx3⟩ := hx
    have hx' : x = x (.inl 0) • vec4 1 0 0 0 + x (.inl 1) • vec4 0 1 0 0 :=
      vec4_eq (by simp [vec4]) (by simp [vec4]) (by simp [vec4, hx2]) (by simp [vec4, hx3])
    rw [hx']
    exact S.add_mem (h1 _ ((spLine K).smul_mem _ ⟨rfl, rfl, rfl⟩)) (he1 _)
  have hcard' : Nat.card S ≤ Nat.card (spPlane K).toAddSubgroup := by
    rw [hcard]
    exact (card_spPlane (K := K)).ge
  by_cases h : ∃ v ∈ S, v (.inr 1) ≠ 0
  · obtain ⟨v, hv, hv3⟩ := h
    have heq := AddSubgroup.eq_of_le_of_card_ge (hle v hv hv3) hcard'
    exact fun x => by rw [← heq]; rfl
  · push Not at h
    have hle' : S ≤ (spPlane K).toAddSubgroup := fun x hx => ⟨h3 x hx, h x hx⟩
    have hcard'' : Nat.card (spPlane K).toAddSubgroup ≤ Nat.card S := by
      rw [hcard]
      exact (card_spPlane (K := K)).le
    have heq := AddSubgroup.eq_of_le_of_card_ge hle' hcard''
    exact fun x => by rw [heq]; rfl

end KA

end CFSG.Quasithin.Vol2.KGNat
