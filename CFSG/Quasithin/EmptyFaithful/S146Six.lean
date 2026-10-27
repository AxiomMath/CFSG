module

public import CFSG.Quasithin.EmptyFaithful.S146Stmts
public import CFSG.Quasithin.EmptyFaithful.S146Inputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem exists_isSylowTwoOf_ge' {P H : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 2 P) :
    ∃ S : Subgroup G, IsSylowTwoOf S H ∧ P ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPH' : IsPGroup 2 (P.subgroupOf H) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  obtain ⟨Q, hQ⟩ := hPH'.exists_le_sylow
  refine ⟨(Q : Subgroup ↥H).map H.subtype, ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map _, ?_⟩, ?_⟩
  · have : ((Q : Subgroup ↥H).map H.subtype).subgroupOf H = (Q : Subgroup ↥H) :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [this]
    exact Q.not_dvd_index
  · intro x hx
    have := hQ (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hPH hx⟩ : ↥H) ∈ P.subgroupOf H)
    exact ⟨_, this, rfl⟩

theorem exists_mem_normalizer_of_lt_isPGroup {A S₀ : Subgroup G} (hS : IsPGroup 2 S₀)
    (hA : A < S₀) : ∃ x ∈ S₀, x ∉ A ∧ x ∈ Subgroup.normalizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥S₀ := hS.isNilpotent
  have hnc : NormalizerCondition ↥S₀ := Group.normalizerCondition_of_isNilpotent
  have hlt : A.subgroupOf S₀ < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    rw [Subgroup.subgroupOf_eq_top] at h
    exact absurd hA (not_lt_of_ge h)
  obtain ⟨x, hxN, hxA⟩ := IsConcreteLE.exists_of_lt (hnc (A.subgroupOf S₀) hlt)
  refine ⟨x, x.2, fun h => hxA (Subgroup.mem_subgroupOf.mpr h), ?_⟩
  rw [Subgroup.mem_normalizer_iff] at hxN ⊢
  intro a
  constructor
  · intro ha
    have h2 := (hxN ⟨a, hA.le ha⟩).mp (Subgroup.mem_subgroupOf.mpr ha)
    simpa using Subgroup.mem_subgroupOf.mp h2
  · intro ha
    have haS : a ∈ S₀ := by
      have h1 : (x : G)⁻¹ * ((x : G) * a * (x : G)⁻¹) * (x : G) ∈ S₀ :=
        S₀.mul_mem (S₀.mul_mem (S₀.inv_mem x.2) (hA.le ha)) x.2
      simpa [mul_assoc] using h1
    have h2 : x * ⟨a, haS⟩ * x⁻¹ ∈ A.subgroupOf S₀ :=
      Subgroup.mem_subgroupOf.mpr (by simpa using ha)
    exact Subgroup.mem_subgroupOf.mp ((hxN ⟨a, haS⟩).mpr h2)

omit [Finite G] in
theorem eq_or_eq_of_relIndex_eq_two {A B C : Subgroup G} (hAB : A ≤ B) (hBC : B ≤ C)
    (h : A.relIndex C = 2) : B = A ∨ B = C := by
  have hmul := Subgroup.relIndex_mul_relIndex A B C hAB hBC
  rw [h] at hmul
  have hdvd : A.relIndex B ∣ 2 := ⟨B.relIndex C, hmul.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.mp h1) hAB)
  · rw [h1] at hmul
    have : B.relIndex C = 1 := by omega
    exact Or.inr (le_antisymm hBC (Subgroup.relIndex_eq_one.mp this))

variable {T M : Subgroup G}

theorem isIStar_sylow_cases (S : Setting146 G T M) {H : Subgroup G} {u : G}
    (hu : IsInvU T M H u) (hidx : (tU T u).relIndex (tZero T u) = 2)
    (hN0 : Subgroup.normalizer (tZero T u : Set G) = T)
    (hNu : Subgroup.normalizer (tU T u : Set G) = tZero T u) {I : Subgroup G}
    (hI : IsIStar T M u I) :
    IsSylowTwoOf (T ⊓ I) I ∧ (T ⊓ I = tU T u ∨ T ⊓ I = tZero T u) := by
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hTu_I : tU T u ≤ I := hI.1.1.1
  have hTu_le : tU T u ≤ T ⊓ I := le_inf inf_le_left hTu_I
  have hT0_T : tZero T u ≤ T := centralizerMod_le_left _ _ _
  obtain ⟨S₀, hS₀, hle⟩ := exists_isSylowTwoOf_ge' (inf_le_right : T ⊓ I ≤ I)
    (hT2.to_le inf_le_left)
  by_cases hc : S₀ = tU T u
  · have h1 : T ⊓ I = tU T u := le_antisymm (hle.trans hc.le) hTu_le
    exact ⟨by rw [h1, ← hc]; exact hS₀, Or.inl h1⟩
  · have hlt : tU T u < S₀ := lt_of_le_of_ne (hTu_le.trans hle) (Ne.symm hc)
    obtain ⟨x, hxS, hxA, hxN⟩ := exists_mem_normalizer_of_lt_isPGroup hS₀.2.1 hlt
    have hx0 : x ∈ tZero T u := hNu ▸ hxN
    have hA₀ : tU T u ≤ tU T u ⊔ Subgroup.zpowers x := le_sup_left
    have hA₁ : tU T u ⊔ Subgroup.zpowers x ≤ tZero T u :=
      sup_le (tU_le_tZero T u) (Subgroup.zpowers_le.mpr hx0)
    have hA₂ : tU T u ⊔ Subgroup.zpowers x = tZero T u := by
      rcases eq_or_eq_of_relIndex_eq_two hA₀ hA₁ hidx with h | h
      · exact absurd (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)) hxA
      · exact h
    have hT0S : tZero T u ≤ S₀ := by
      rw [← hA₂]
      exact sup_le (hTu_le.trans hle) (Subgroup.zpowers_le.mpr hxS)
    have hT0TI : tZero T u ≤ T ⊓ I := le_inf hT0_T (hT0S.trans hS₀.1)
    have hTI : T ⊓ I = tZero T u := by
      rcases eq_or_eq_of_relIndex_eq_two hT0TI inf_le_left hu.index_two with h | h
      · exact h
      · exfalso
        have hTI' : T ≤ I := by rw [← h]; exact inf_le_right
        have hHTM : IsHTM T M I := ⟨⟨hTI', hI.1.1.2⟩, hI.1.2.2⟩
        exact hI.1.2.1 (S.le_mcOf hHTM)
    refine ⟨?_, Or.inr hTI⟩
    by_cases hS : S₀ = T ⊓ I
    · rw [← hS]; exact hS₀
    · exfalso
      have hlt2 : T ⊓ I < S₀ := lt_of_le_of_ne hle (Ne.symm hS)
      obtain ⟨y, hyS, hyA, hyN⟩ := exists_mem_normalizer_of_lt_isPGroup hS₀.2.1 hlt2
      rw [hTI, hN0] at hyN
      exact hyA ⟨hyN, hS₀.1 hyS⟩

theorem stage1466_one_of (h1 : Stage1463One) (h2 : Stage1463Two) (h4 : Stage1463Four) :
    Stage1466One := by
  intro G _ _ T M H u S hH hu I hI
  exact (isIStar_sylow_cases S hu (h1 G T M S H hH u hu).2.1 (h2 G T M S H hH u hu)
    (h4 G T M S H hH u hu).1 hI).2

end CFSG.Quasithin
