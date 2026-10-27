module

public import CFSG.RankThree.PartTwo.Sec21.Item226Data

public section

namespace CFSG.RankThree.PartTwo.Sec21

open Matrix

theorem t0_fix : ∀ i ∈ List.range 6, reflAt i *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  decide +kernel

theorem mem_of_cert {𝒟 : Set Mat4} (hcl : ∀ M ∈ 𝒟, ∀ N ∈ 𝒟, M * N * M ∈ 𝒟)
    (ht0 : ∀ i ∈ List.range 6, reflAt i ∈ 𝒟) {c : ℕ} (hc : reflAt c ∈ 𝒟) {cfg : List ℕ}
    (hcert : checkDeriv (c :: List.range 6) (certOf c) = true ∧
      ∀ i ∈ cfg, i ∈ (c :: List.range 6) ++ (certOf c).map Prod.fst) :
    ∀ i ∈ cfg, reflAt i ∈ 𝒟 := by
  intro i hi
  refine checkDeriv_sound 𝒟 hcl (certOf c) (c :: List.range 6) ?_ hcert.1 i (hcert.2 i hi)
  intro j hj
  rcases List.mem_cons.mp hj with rfl | hj
  · exact hc
  · exact ht0 j hj

theorem config_eq_s5 (𝒟 : Set Mat4)
    (hsub : ∀ M ∈ 𝒟, ∃ i < 45, M = reflAt i) (ht0 : ∀ i ∈ List.range 6, reflAt i ∈ 𝒟)
    (hcl : ∀ M ∈ 𝒟, ∀ N ∈ 𝒟, M * N * M ∈ 𝒟) (hcp : ∀ M ∈ 𝒟, ∀ N ∈ 𝒟, Compat4 M N)
    (hnt : ∀ i j k : ℕ, reflAt i ∈ 𝒟 → reflAt j ∈ 𝒟 → reflAt k ∈ 𝒟 → ¬ CommTriple i j k)
    (hfix : ∃ M ∈ 𝒟, M *ᵥ Pi.single 0 1 ≠ Pi.single 0 1)
    (hcen : ∃ M ∈ 𝒟, ∃ k : Fin 4, (M - 1) 0 k ≠ 0) :
    (∀ M, M ∈ 𝒟 ↔ ∃ i ∈ s5aL, M = reflAt i) ∨ (∀ M, M ∈ 𝒟 ↔ ∃ i ∈ s5bL, M = reflAt i) := by
  obtain ⟨c, hc, hcD⟩ : ∃ c ∈ List.range' 6 39, reflAt c ∈ 𝒟 := by
    by_contra hno
    push Not at hno
    obtain ⟨M, hM, hMfix⟩ := hfix
    obtain ⟨i, hi, rfl⟩ := hsub M hM
    by_cases hi6 : i < 6
    · exact hMfix (t0_fix i (List.mem_range.mpr hi6))
    · exact hno i (List.mem_range'_1.mpr ⟨by omega, by omega⟩) hM
  have hmax : ∀ {cfg ext : List ℕ}, (∀ i ∈ cfg, reflAt i ∈ 𝒟) →
      (∀ i ∈ List.range 45, (∀ j ∈ cfg, CompatAt i j) → i ∈ cfg ∨ i ∈ ext) →
      (∀ i ∈ ext, reflAt i ∈ 𝒟 → False) → ∀ M ∈ 𝒟, ∃ i ∈ cfg, M = reflAt i := by
    intro cfg ext hcfg hm hext M hM
    obtain ⟨i, hi, rfl⟩ := hsub M hM
    rcases hm i (List.mem_range.mpr hi) (fun j hj => hcp _ hM _ (hcfg j hj)) with h | h
    · exact ⟨i, h, rfl⟩
    · exact (hext i h hM).elim
  rcases refl_types c hc with htr | hs5a | hs5b | hga | hgb
  ·
    obtain ⟨⟨c', i, j⟩, hp, rfl⟩ := List.mem_map.mp htr
    obtain ⟨hct, hi, hj⟩ := tripleTable_spec _ hp
    exact (hnt i j c' (ht0 i (List.mem_range.mpr hi)) (ht0 j (List.mem_range.mpr hj)) hcD
      hct).elim
  ·
    left
    have hcfg := mem_of_cert hcl ht0 hcD (s5a_cert c hs5a)
    have hD := hmax hcfg s5a_max fun i hi hiD => by
      obtain ⟨⟨i', j, k⟩, hp, rfl⟩ := List.mem_map.mp hi
      obtain ⟨hct, hj, hk⟩ := s5aExt_spec _ hp
      exact hnt j k i' (hcfg j hj) (hcfg k hk) hiD hct
    intro M
    exact ⟨hD M, fun ⟨i, hi, hM⟩ => hM ▸ hcfg i hi⟩
  ·
    right
    have hcfg := mem_of_cert hcl ht0 hcD (s5b_cert c hs5b)
    have hD := hmax hcfg s5b_max fun i hi hiD => by
      obtain ⟨⟨i', j, k⟩, hp, rfl⟩ := List.mem_map.mp hi
      obtain ⟨hct, hj, hk⟩ := s5bExt_spec _ hp
      exact hnt j k i' (hcfg j hj) (hcfg k hk) hiD hct
    intro M
    exact ⟨hD M, fun ⟨i, hi, hM⟩ => hM ▸ hcfg i hi⟩
  ·
    exfalso
    have hcfg := mem_of_cert hcl ht0 hcD (g648a_cert c hga)
    have hD := hmax (ext := []) hcfg (fun i hi h => Or.inl (g648a_max i hi h))
      (fun i hi => absurd hi List.not_mem_nil)
    obtain ⟨M, hM, k, hk⟩ := hcen
    obtain ⟨i, hi, rfl⟩ := hD M hM
    exact hk (g648a_centers i hi k)
  ·
    exfalso
    have hcfg := mem_of_cert hcl ht0 hcD (g648b_cert c hgb)
    have hD := hmax (ext := []) hcfg (fun i hi h => Or.inl (g648b_max i hi h))
      (fun i hi => absurd hi List.not_mem_nil)
    obtain ⟨M, hM, hMfix⟩ := hfix
    obtain ⟨i, hi, rfl⟩ := hD M hM
    apply hMfix
    ext k
    rw [mulVec_single_one]
    have := g648b_fix i hi k
    simp only [Matrix.col_apply]
    rw [this]
    fin_cases k <;> rfl

end CFSG.RankThree.PartTwo.Sec21
