module

public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.Vol2.Ch1Comm

public section

namespace CFSG.Quasithin.RonanF918

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {T H K : Subgroup G}

theorem self_mem_conjSubgroupsBy (K H : Subgroup G) : K ∈ conjSubgroupsBy H K :=
  ⟨1, H.one_mem, (A38.map_conj_eq_iff.mpr (Subgroup.one_mem _)).symm⟩

theorem exists_mem_not_mem_normalizer_of_ncard_two (hT : IsSylowTwoOf T H)
    (hncard : Set.ncard (conjSubgroupsBy H K) = 2) :
    ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
  by_contra hcon
  push Not at hcon
  have hTH : T ≤ H := hT.1
  obtain ⟨x, y, hxy, hs⟩ := Set.ncard_eq_two.mp hncard
  have hKmem := self_mem_conjSubgroupsBy K H
  rw [hs] at hKmem
  obtain ⟨K', hK'ne, hΩ⟩ : ∃ K' : Subgroup G, K' ≠ K ∧ conjSubgroupsBy H K = {K, K'} := by
    rcases hKmem with rfl | rfl
    · exact ⟨y, hxy.symm, hs⟩
    · exact ⟨x, hxy, by rw [hs, Set.pair_comm]⟩
  have hK'mem : K' ∈ conjSubgroupsBy H K := by rw [hΩ]; exact Or.inr rfl
  obtain ⟨s, hsH, hs'⟩ := hK'mem
  have hsN : s ∉ Subgroup.normalizer (K : Set G) := fun hs'' =>
    hK'ne (hs'.trans (A38.map_conj_eq_iff.mpr hs''))
  set N : Subgroup G := Subgroup.normalizer (K : Set G) ⊓ H with hN
  have hdich : ∀ h ∈ H, h ∈ N ∨ s⁻¹ * h ∈ N := by
    intro h hh
    have hmem : K.map (MulAut.conj h).toMonoidHom ∈ conjSubgroupsBy H K := ⟨h, hh, rfl⟩
    rw [hΩ] at hmem
    rcases Set.mem_insert_iff.mp hmem with he | he
    · exact Or.inl ⟨A38.map_conj_eq_iff.mp he, hh⟩
    · have he := Set.mem_singleton_iff.mp he
      right
      refine ⟨?_, H.mul_mem (H.inv_mem hsH) hh⟩
      show s⁻¹ * h ∈ Subgroup.normalizer (K : Set G)
      rw [← A38.map_conj_eq_iff]
      have h2 : K.map (MulAut.conj h).toMonoidHom = K.map (MulAut.conj s).toMonoidHom :=
        he.trans hs'
      have h3 := congrArg (Subgroup.map (MulAut.conj s⁻¹).toMonoidHom) h2
      rw [Subgroup.map_map, Subgroup.map_map] at h3
      have e1 : (MulAut.conj s⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
          (MulAut.conj (s⁻¹ * h)).toMonoidHom := by
        ext z; simp [MulAut.conj_apply, mul_assoc]
      have e2 : (MulAut.conj s⁻¹).toMonoidHom.comp (MulAut.conj s).toMonoidHom =
          (MulAut.conj (1 : G)).toMonoidHom := by
        ext z; simp [MulAut.conj_apply, mul_assoc]
      rw [e1, e2] at h3
      rw [h3]
      exact A38.map_conj_eq_iff.mpr (Subgroup.one_mem _)
  have hsH' : s ∈ H := hsH
  have hindex : N.relIndex H = 2 := by
    unfold Subgroup.relIndex
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨s, hsH'⟩, fun b => ?_⟩
    have hsN' : s ∉ N := fun hh => hsN hh.1
    by_cases hb : b ∈ N.subgroupOf H
    · refine Or.inr ⟨hb, ?_⟩
      intro hbs
      apply hsN'
      have h1 : (b : G) ∈ N := hb
      have h2 : (b : G) * s ∈ N := hbs
      have := N.mul_mem (N.inv_mem h1) h2
      simpa using this
    · refine Or.inl ⟨?_, hb⟩
      have hbH : (b : G) ∈ H := b.2
      have hbN : (b : G) ∉ N := hb
      rcases hdich _ (H.inv_mem hbH) with h1 | h1
      · exact absurd (N.inv_mem h1 |> fun h => by simpa using h) hbN
      · have := N.inv_mem h1
        have e : (s⁻¹ * (b : G)⁻¹)⁻¹ = (b : G) * s := by group
        rw [e] at this
        exact this
  have hTN : T ≤ N := fun t ht => ⟨hcon t ht, hTH ht⟩
  have hNH : N ≤ H := inf_le_right
  have hmul := Subgroup.relIndex_mul_relIndex T N H hTN hNH
  apply hT.2.2
  show 2 ∣ T.relIndex H
  rw [← hmul]
  exact Dvd.dvd.mul_left (by rw [hindex]) _

theorem conjClosure_K_T_eq_conjClosure_K_H (hH : SQTKGroup ↥H) (hA37 : A37ForSQTK)
    (hA38 : A38ForSQTK) (hKc : K ∈ cComp H) (hT : IsSylowTwoOf T H) :
    conjClosure K T = conjClosure K H := by
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hTH : T ≤ H := hT.1
  refine le_antisymm (conjClosure_mono le_rfl hTH) ?_
  have hQ : SQTKHyp (↥H ⧸ CFSG.pCore 2 ↥H) := SQTKHyp.of_sqtkGroup ↥H hH
  rcases lemma_1_2_1_three_of_a3_sq (hA37 _ hQ) (hA38 _ hQ) hKc with hnorm | ⟨hncard, -⟩
  · have hKN : H ≤ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hnorm
    refine conjClosure_le fun h hh z hz => ?_
    exact le_conjClosure K T ((Subgroup.mem_normalizer_iff.mp (hKN hh) z).mp hz)
  · obtain ⟨t, ht, htK⟩ := exists_mem_not_mem_normalizer_of_ncard_two hT hncard
    have hKt : K.map (MulAut.conj t).toMonoidHom ≤ conjClosure K T := by
      rintro _ ⟨z, hz, rfl⟩
      exact mem_conjClosure ht hz
    obtain ⟨x, y, hxy, hs⟩ := Set.ncard_eq_two.mp hncard
    have hKmem := self_mem_conjSubgroupsBy K H
    have htmem : K.map (MulAut.conj t).toMonoidHom ∈ conjSubgroupsBy H K := ⟨t, hTH ht, rfl⟩
    have hne : K.map (MulAut.conj t).toMonoidHom ≠ K := fun he => htK (A38.map_conj_eq_iff.mp he)
    have hΩ : conjSubgroupsBy H K = {K, K.map (MulAut.conj t).toMonoidHom} := by
      refine (Set.eq_of_subset_of_ncard_le ?_ (by rw [hncard, Set.ncard_pair hne.symm])
        (Set.toFinite _)).symm
      rintro _ (rfl | rfl)
      · exact hKmem
      · exact htmem
    refine conjClosure_le fun h hh z hz => ?_
    have hmem : K.map (MulAut.conj h).toMonoidHom ∈ conjSubgroupsBy H K := ⟨h, hh, rfl⟩
    rw [hΩ] at hmem
    have hz' : h * z * h⁻¹ ∈ K.map (MulAut.conj h).toMonoidHom := ⟨z, hz, by simp [MulAut.conj_apply]⟩
    rcases Set.mem_insert_iff.mp hmem with he | he
    · rw [he] at hz'
      exact le_conjClosure K T hz'
    · rw [Set.mem_singleton_iff.mp he] at hz'
      exact hKt hz'

theorem H_le_normalizer_K₀ (hH : SQTKGroup ↥H) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK)
    (hKc : K ∈ cComp H) (hT : IsSylowTwoOf T H) :
    H ≤ Subgroup.normalizer (conjClosure K T : Set G) := by
  rw [conjClosure_K_T_eq_conjClosure_K_H hH hA37 hA38 hKc hT]
  exact le_normalizer_conjClosure K H

end CFSG.Quasithin.RonanF918
