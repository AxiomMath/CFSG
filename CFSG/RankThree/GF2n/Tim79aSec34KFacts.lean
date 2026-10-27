module

public import CFSG.RankThree.GF2n.Tim79aSpStabModel
public import CFSG.RankThree.GF2n.Tim79aSpTorusModel
public import CFSG.RankThree.GF2n.Tim79aSpPair

public section

namespace CFSG.RankThree.GF2n.Tim79a

open Matrix CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic

structure TorusFacts (K : Type) [Group K] (A : Subgroup K) (q : ℕ) : Prop where
  torus : ∀ g : K, ¬ (∀ a ∈ A, ∀ b ∈ conjSub A g, a * b = b * a) →
    ∃ h ∈ Subgroup.normalizer (A : Set K),
      (∀ m ∈ Subgroup.normalizer (A : Set K), ∃ i : ℕ,
        ∃ c ∈ Subgroup.centralizer (A : Set K), m = c * h ^ i) ∧
      h ^ (q - 1) = 1 ∧
      ∀ i : ℕ, 0 < i → i < q - 1 →
        ∃ a₁ ∈ A, ∃ a₂ ∈ A, ∃ b₁ ∈ conjSub A g, ∃ b₂ ∈ conjSub A g, a₁ ≠ 1 ∧ a₂ ≠ 1 ∧ b₁ ≠ b₂ ∧
          orderOf (a₁ * b₁) = 3 ∧ orderOf (a₂ * b₂) = 3 ∧
          (a₁ * b₁ * a₁) * (a₂ * b₂ * a₂) = h ^ i

@[expose] def StabFacts (K : Type) [Group K] (A : Subgroup K) : Prop :=
  ∀ x ∈ Subgroup.centralizer (A : Set K), x ∈ Subgroup.closure
    {y | ∃ g' : K, conjSub A g' ≤ Subgroup.centralizer (A : Set K) ∧ y ∈ conjSub A g'}

variable {n : ℕ} {F : Type} [Field F]

theorem mat_mulVec_eq_of_mem_centralizer [CharP F 2] {a : Fin n ⊕ Fin n → F}
    {T : Subgroup (StatedSp n F)} (hT : IsTransGroup a T) (ha : a ≠ 0) {x : StatedSp n F}
    (hx : x ∈ Subgroup.centralizer (T : Set (StatedSp n F))) :
    SpExtras.mat n F x *ᵥ a = a := by
  have hconj : conjSub T x = T := by
    ext y
    rw [mem_conjSub]
    constructor
    · intro h
      have h1 : (x⁻¹ * y * x) * x = x * (x⁻¹ * y * x) := Subgroup.mem_centralizer_iff.mp hx _ h
      have h2 : y = x⁻¹ * y * x := by
        calc y = (x * (x⁻¹ * y * x)) * x⁻¹ := by group
          _ = ((x⁻¹ * y * x) * x) * x⁻¹ := by rw [h1]
          _ = x⁻¹ * y * x := by group
      rw [h2]; exact h
    · intro h
      have h1 : y * x = x * y := Subgroup.mem_centralizer_iff.mp hx _ h
      have h2 : x⁻¹ * y * x = y := by
        calc x⁻¹ * y * x = x⁻¹ * (y * x) := by group
          _ = x⁻¹ * (x * y) := by rw [h1]
          _ = y := by group
      rw [h2]; exact h
  have hTx : IsTransGroup (SpExtras.mat n F x *ᵥ a) T := by
    have := hT.conjSub x
    rwa [hconj] at this
  obtain ⟨μ, -, hμ⟩ := IsTransGroup.exists_eq_smul hTx hT (mat_mulVec_ne_zero' x ha)
  obtain ⟨t₁, ht₁⟩ := hT.2 1
  have ht₁T : t₁ ∈ T := (hT.1 t₁).2 ⟨1, ht₁⟩
  have h1 : x * t₁ * x⁻¹ = t₁ := by
    have := Subgroup.mem_centralizer_iff.mp hx _ ht₁T
    calc x * t₁ * x⁻¹ = (x * t₁) * x⁻¹ := rfl
      _ = (t₁ * x) * x⁻¹ := by rw [this]
      _ = t₁ := by group
  have h2 : spTrans a (μ * μ * 1) = spTrans a 1 := by
    have e1 := mat_conj_of_mat_eq ht₁ x
    rw [h1, ht₁, hμ, spTrans_smul] at e1
    exact e1.symm
  obtain ⟨w, hw⟩ := exists_spForm_ne_zero ha
  have h3 : (μ * μ * 1 * spForm a w) • a = (1 * spForm a w) • a := by
    have := congrArg (fun M => M *ᵥ w) h2
    simp only [spTrans_mulVec] at this
    exact add_left_cancel this
  have h4 : μ * μ * 1 * spForm a w = 1 * spForm a w := by
    by_contra hne
    have := sub_ne_zero.mpr hne
    have h5 : ((μ * μ * 1 * spForm a w) - (1 * spForm a w)) • a = 0 := by
      rw [sub_smul, h3, sub_self]
    rcases smul_eq_zero.mp h5 with h | h
    · exact this h
    · exact ha h
  have h6 : μ * μ = 1 := by
    have h5 : μ * μ * spForm a w = 1 * spForm a w := by simpa using h4
    simpa using mul_right_cancel₀ hw h5
  have hμ1 : μ = 1 := by
    rcases mul_self_eq_one_iff.mp h6 with h | h
    · exact h
    · rw [h]; exact CharTwo.neg_eq 1
  rw [hμ, hμ1, one_smul]

theorem spStabStatement_of_model : ∀ (K : Type) [Group K] [Finite K] (A : Subgroup K), ClassicalRootSp K A → StabFacts K A := by
  have h := spStabGenModel_holds
  rintro K _ _ A ⟨f, Δ, hf, hΔ, hA⟩
  obtain ⟨n, Φ, a, T, hΦ, ha, hT, rfl⟩ := exists_isTransGroup_of_transvConclusionSp hf hΔ hA
  intro x hx
  obtain ⟨x', rfl⟩ := hΦ.2 x
  have hx' : x' ∈ Subgroup.centralizer (T : Set (StatedSp n (GaloisField 2 f))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have := Subgroup.mem_centralizer_iff.mp hx (Φ t) (Subgroup.mem_map_of_mem Φ ht)
    apply hΦ.1
    rw [map_mul, map_mul]
    exact this
  have hfix := mat_mulVec_eq_of_mem_centralizer hT ha hx'
  have hcl := h n (GaloisField 2 f) a ha x' hfix
  have hmem : Φ x' ∈ (Subgroup.closure {x : StatedSp n (GaloisField 2 f) |
      ∃ (b : Fin n ⊕ Fin n → GaloisField 2 f) (c : GaloisField 2 f), spForm a b = 0 ∧
        SpExtras.mat n (GaloisField 2 f) x = spTrans b c}).map Φ := ⟨x', hcl, rfl⟩
  rw [MonoidHom.map_closure] at hmem
  refine Subgroup.closure_mono ?_ hmem
  rintro _ ⟨s, ⟨b, c, hb, hs⟩, rfl⟩
  by_cases hb0 : b = 0
  · subst hb0
    have hs1 : s = 1 := by
      apply SpExtras.mat_injective
      rw [hs, map_one]
      simp [spTrans, spNil]
    refine ⟨1, ?_, ?_⟩
    · rw [conjSub_one]
      rintro _ ⟨t, ht, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨t', ht', rfl⟩
      rw [← map_mul, ← map_mul, (hT.commuting hT (spForm_self a) t' ht' t ht)]
    · rw [conjSub_one, hs1, map_one]
      exact (T.map Φ).one_mem
  · obtain ⟨g, hg⟩ := exists_mat_mulVec_eq_of_ne_zero ha hb0
    have hTb : IsTransGroup b (conjSub T g) := hg ▸ hT.conjSub g
    have hsTb : s ∈ conjSub T g := (hTb.1 s).2 ⟨c, hs⟩
    refine ⟨Φ g, ?_, ?_⟩
    · rw [conjSub_map]
      rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨t, ht, rfl⟩
      rw [← map_mul, ← map_mul, (hT.commuting hTb hb t ht y hy)]
    · rw [conjSub_map]
      exact Subgroup.mem_map_of_mem Φ hsTb

end CFSG.RankThree.GF2n.Tim79a

namespace CFSG.RankThree.GF2n.Tim79a

open Matrix CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic

theorem spTorusStatement_of_model :
    ∀ (K : Type) [Group K] [Finite K] (A : Subgroup K) (f : ℕ) (Δ : Set (Subgroup K)),
      1 ≤ f → TransvConclusionSp K Δ f → A ∈ Δ → TorusFacts K A (2 ^ f) := by
  have h := spTorusModel_holds
  rintro K _ _ A f Δ hf hΔ hA
  obtain ⟨n, Φ, a, T, hΦ, -, hT, rfl⟩ := exists_isTransGroup_of_transvConclusionSp hf hΔ hA
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  refine ⟨fun g hg => ?_⟩
  obtain ⟨g', rfl⟩ := hΦ.2 g
  have h0 : spForm a (SpExtras.mat n (GaloisField 2 f) g' *ᵥ a) ≠ 0 := by
    intro h0
    apply hg
    rw [conjSub_map]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have := (hT.commuting (hT.conjSub g') h0) x hx y hy
    rw [← map_mul, ← map_mul, this.eq]
  obtain ⟨h₀, hN, hdec, hord, hprod⟩ := h n (GaloisField 2 f) a _ T (conjSub T g') hT
    (hT.conjSub g') h0
  have hnorm : ∀ x : StatedSp n (GaloisField 2 f),
      Φ x ∈ Subgroup.normalizer ((T.map Φ : Subgroup _) : Set _) ↔
        x ∈ Subgroup.normalizer (T : Set (StatedSp n (GaloisField 2 f))) := by
    intro x
    rw [← Subgroup.map_normalizer_eq_of_bijective T hΦ]
    exact ⟨fun hx => by
      obtain ⟨x', hx', hxx⟩ := hx
      rw [← hΦ.1 hxx]
      exact hx', fun hx => Subgroup.mem_map_of_mem Φ hx⟩
  refine ⟨Φ h₀, (hnorm h₀).2 hN, ?_, ?_, ?_⟩
  · intro m hm
    obtain ⟨m', rfl⟩ := hΦ.2 m
    obtain ⟨i, c, hc, hmc⟩ := hdec m' ((hnorm m').1 hm)
    refine ⟨i, Φ c, ?_, by rw [hmc, map_mul, map_pow]⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hc t ht]
  · rw [← map_pow, ← hcard, hord, map_one]
  · intro i hi0 hiq
    rw [← hcard] at hiq
    obtain ⟨a₁, ha₁, a₂, ha₂, b₁, hb₁, b₂, hb₂, ha₁1, ha₂1, hb12, hord₁, hord₂, hpr⟩ :=
      hprod i hi0 hiq
    refine ⟨Φ a₁, Subgroup.mem_map_of_mem Φ ha₁, Φ a₂, Subgroup.mem_map_of_mem Φ ha₂,
      Φ b₁, ?_, Φ b₂, ?_, fun h' => ha₁1 (hΦ.1 (by rw [h', map_one])),
      fun h' => ha₂1 (hΦ.1 (by rw [h', map_one])), fun h' => hb12 (hΦ.1 h'), ?_, ?_, ?_⟩
    · rw [conjSub_map]; exact Subgroup.mem_map_of_mem Φ hb₁
    · rw [conjSub_map]; exact Subgroup.mem_map_of_mem Φ hb₂
    · rw [← map_mul, orderOf_injective Φ hΦ.1, hord₁]
    · rw [← map_mul, orderOf_injective Φ hΦ.1, hord₂]
    · have := congrArg Φ hpr
      simpa only [map_mul, map_pow] using this

end CFSG.RankThree.GF2n.Tim79a
