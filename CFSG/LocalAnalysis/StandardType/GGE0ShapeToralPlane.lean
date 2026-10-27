module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem contextImage_card_of_le_normalizer {G : Type} [Group G]
    {G0 H : Subgroup G} (hH : H ≤ Subgroup.normalizer (G0 : Set G))
    (hC : Subgroup.centralizer (G0 : Set G) = ⊥) :
    Nat.card (contextImage G0 H) = Nat.card H := by
  have hker : (Subgroup.normalizerMonoidHom G0).ker = ⊥ := by
    rw [Subgroup.normalizerMonoidHom_ker, hC, Subgroup.bot_subgroupOf]
  have hinj : Function.Injective (Subgroup.normalizerMonoidHom G0) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  change Nat.card ((H.comap (Subgroup.normalizer (G0 : Set G)).subtype).map
    (Subgroup.normalizerMonoidHom G0)) = Nat.card H
  rw [Subgroup.card_map_of_injective hinj]
  have hmap : (H.comap (Subgroup.normalizer (G0 : Set G)).subtype).map
      (Subgroup.normalizer (G0 : Set G)).subtype = H := by
    rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
    exact inf_eq_right.mpr hH
  have hcard : Nat.card (H.comap (Subgroup.normalizer (G0 : Set G)).subtype) =
      Nat.card H := by
    conv_rhs => rw [← hmap]
    exact (Subgroup.card_map_of_injective
      (f := (Subgroup.normalizer (G0 : Set G)).subtype)
      (K := H.comap (Subgroup.normalizer (G0 : Set G)).subtype)
      (Subgroup.subtype_injective (Subgroup.normalizer (G0 : Set G)))).symm
  rw [hcard]

private theorem realizedSubgroup_card_of_le {C : Type} [Group C]
    {I : Subgroup (MulAut C)} {L : Type} [Field L] [IsAlgClosed L]
    (R : ShapeRealization C I L) {E : Subgroup (MulAut C)} (hE : E ≤ I) :
    Nat.card (realizedSubgroup R E) = Nat.card E := by
  change Nat.card ((E.comap I.subtype).map R.action) = Nat.card E
  rw [Subgroup.card_map_of_injective R.action_injective]
  have hmap : (E.comap I.subtype).map I.subtype = E := by
    rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
    exact inf_eq_right.mpr hE
  have hcard : Nat.card (E.comap I.subtype) = Nat.card E := by
    conv_rhs => rw [← hmap]
    exact (Subgroup.card_map_of_injective
      (f := I.subtype) (K := E.comap I.subtype) I.subtype_injective).symm
  rw [hcard]

private theorem exists_two_gens_of_card_nine_exp_three
    {A : Type} [Group A] {S : Subgroup A}
    (hcard : Nat.card S = 9) (hexp : ∀ s ∈ S, s ^ 3 = 1) :
    ∃ x ∈ S, ∃ y ∈ S, Subgroup.closure ({x, y} : Set A) = S := by
  haveI : Finite S := (Nat.card_pos_iff.mp (by rw [hcard]; norm_num)).2
  have hSne : S ≠ ⊥ := by
    intro h
    have h1 : Nat.card S = 1 := by rw [h, Subgroup.card_bot]
    rw [hcard] at h1
    norm_num at h1
  obtain ⟨x0, hx0ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hSne
  let x : A := (x0 : A)
  have hxS : x ∈ S := x0.2
  have hxne : x ≠ 1 := fun h => hx0ne (Subtype.ext h)
  let K1 : Subgroup A := Subgroup.closure ({x} : Set A)
  have hK1leS : K1 ≤ S := by
    change Subgroup.closure ({x} : Set A) ≤ S
    exact (Subgroup.closure_le S).mpr (fun a ha => by
      rw [Set.mem_singleton_iff] at ha
      rwa [ha])
  have hK1card : Nat.card K1 = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hx3 : x ^ 3 = 1 := hexp x hxS
    have ho : orderOf x = 3 := orderOf_eq_prime hx3 hxne
    change Nat.card (Subgroup.closure ({x} : Set A)) = 3
    rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers, ho]
  have hK1neS : K1 ≠ S := by
    intro h
    have h1 : Nat.card K1 = Nat.card S := by rw [h]
    rw [hK1card, hcard] at h1
    norm_num at h1
  obtain ⟨y, hyS, hyK1⟩ :=
    Set.not_subset.mp (fun hle => hK1neS (le_antisymm hK1leS hle))
  let K2 : Subgroup A := Subgroup.closure ({x, y} : Set A)
  have hK2leS : K2 ≤ S := by
    change Subgroup.closure ({x, y} : Set A) ≤ S
    exact (Subgroup.closure_le S).mpr (fun a ha => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact hxS
      · exact hyS)
  have hK1leK2 : K1 ≤ K2 := by
    change Subgroup.closure ({x} : Set A) ≤ Subgroup.closure ({x, y} : Set A)
    exact (Subgroup.closure_le K2).mpr (fun a ha => by
      rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact Subgroup.subset_closure (by simp))
  have hK1neK2 : K1 ≠ K2 := by
    intro h
    have hyK2 : y ∈ K2 := Subgroup.subset_closure (by simp)
    rw [← h] at hyK2
    exact hyK1 hyK2
  have hlt : K1 < K2 := lt_of_le_of_ne hK1leK2 hK1neK2
  haveI : Finite K2 := Finite.of_injective (Subgroup.inclusion hK2leS)
    (Subgroup.inclusion_injective hK2leS)
  have hgt : 3 < Nat.card K2 := by
    have h := Subgroup.card_lt_of_lt hlt
    rw [hK1card] at h
    exact h
  have hK2card : Nat.card K2 = 9 := by
    have hdvd9 : Nat.card K2 ∣ 9 := by
      rw [← hcard]
      exact Subgroup.card_dvd_of_le hK2leS
    have hdvd32 : Nat.card K2 ∣ (3 : ℕ) ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 from by norm_num]
      exact hdvd9
    obtain ⟨k, hk2, hk3⟩ :=
      (Nat.dvd_prime_pow (p := 3) (by norm_num) (m := 2)).mp hdvd32
    interval_cases k
    · rw [hk3] at hgt
      norm_num at hgt
    · rw [hk3] at hgt
      norm_num at hgt
    · rw [hk3]
      norm_num
  refine ⟨x, hxS, y, hyS, ?_⟩
  have hK2eqS : K2 = S :=
    Subgroup.eq_of_le_of_card_ge hK2leS (by simp [hK2card, hcard])
  simpa only [K2] using hK2eqS

theorem plane_of_realization
    {G : Type} [Group G] {G0 D : Subgroup G}
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {I : Subgroup (MulAut G0)} (R : ShapeRealization G0 I Ω)
    (hC : Subgroup.centralizer (G0 : Set G) = ⊥)
    (hDN : D ≤ Subgroup.normalizer (G0 : Set G)) (hDI : contextImage G0 D ≤ I)
    (hT : realizedSubgroup R (contextImage G0 D) ≤ torusGroup .E6 Ω)
    (hcard : Nat.card D = 9) (hexp : ∀ d ∈ D, d ^ 3 = 1) :
    ∃ a : Fin 2 → Fin Tag.E6.rank → Ωˣ,
      planeGroup a = realizedSubgroup R (contextImage G0 D) ∧ (∀ i j, a i j ^ 3 = 1) := by
  let E : Subgroup (ModGL .E6 Ω) := realizedSubgroup R (contextImage G0 D)
  have hinj : Function.Injective (rootDiagUnitHom .E6 Ω) := rootDiagUnit_injective
  have hcardE : Nat.card E = 9 := by
    change Nat.card (realizedSubgroup R (contextImage G0 D)) = 9
    rw [realizedSubgroup_card_of_le R hDI, contextImage_card_of_le_normalizer hDN hC, hcard]
  have hEexp : ∀ e ∈ E, e ^ 3 = 1 := by
    intro e he
    change e ∈ realizedSubgroup R (contextImage G0 D) at he
    rw [realizedSubgroup, Subgroup.mem_map] at he
    obtain ⟨φ, hφ, rfl⟩ := he
    have hφ' : φ.1 ∈ contextImage G0 D := hφ
    rw [contextImage, Subgroup.mem_map] at hφ'
    obtain ⟨n, hnD, hnφ⟩ := hφ'
    have hn3 : n ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hexp (n : G) hnD
    have hφ3 : φ ^ 3 = 1 := by
      apply Subtype.ext
      change (φ.1 : MulAut G0) ^ 3 = 1
      rw [← hnφ, ← map_pow, hn3, map_one]
    rw [← map_pow, hφ3, map_one]
  have hrange : (rootDiagUnitHom .E6 Ω).range = torusGroup .E6 Ω := by
    ext g
    constructor
    · rintro ⟨l, rfl⟩
      exact rootDiagUnit_mem_torusGroup l
    · intro hg
      obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hg
      exact ⟨l, hl.symm⟩
  have hErange : E ≤ (rootDiagUnitHom .E6 Ω).range := by
    rw [hrange]
    exact hT
  let S : Subgroup (Fin Tag.E6.rank → Ωˣ) := E.comap (rootDiagUnitHom .E6 Ω)
  have hSmap : S.map (rootDiagUnitHom .E6 Ω) = E := by
    change (E.comap (rootDiagUnitHom .E6 Ω)).map (rootDiagUnitHom .E6 Ω) = E
    exact Subgroup.map_comap_eq_self hErange
  have hcardS : Nat.card S = 9 := by
    calc Nat.card S
        = Nat.card (S.map (rootDiagUnitHom .E6 Ω)) :=
          (Subgroup.card_map_of_injective hinj).symm
      _ = Nat.card E := by rw [hSmap]
      _ = 9 := hcardE
  have hSexp : ∀ s ∈ S, s ^ 3 = 1 := by
    intro s hs
    have hsE : rootDiagUnitHom .E6 Ω s ∈ E := hs
    have h3 : (rootDiagUnitHom .E6 Ω s) ^ 3 = 1 := hEexp _ hsE
    exact hinj (by rw [map_pow, h3, map_one])
  obtain ⟨x, hxS, y, hyS, hxy⟩ := exists_two_gens_of_card_nine_exp_three hcardS hSexp
  let a : Fin 2 → Fin Tag.E6.rank → Ωˣ := ![x, y]
  have hrange_a : Set.range a = ({x, y} : Set (Fin Tag.E6.rank → Ωˣ)) := by
    ext z
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [a]
    · rintro (rfl | rfl)
      · exact ⟨0, by simp [a]⟩
      · exact ⟨1, by simp [a]⟩
  refine ⟨a, ?_, ?_⟩
  · have hrange_img : Set.range (fun i : Fin 2 => rootDiagUnit .E6 (a i))
        = (rootDiagUnitHom .E6 Ω) '' Set.range a := by
      change Set.range (fun i : Fin 2 => (rootDiagUnitHom .E6 Ω) (a i)) = _
      rw [Set.range_comp']
    change Subgroup.closure (Set.range fun i : Fin 2 => rootDiagUnit .E6 (a i)) = E
    calc Subgroup.closure (Set.range fun i : Fin 2 => rootDiagUnit .E6 (a i))
        = Subgroup.closure ((rootDiagUnitHom .E6 Ω) '' Set.range a) := by rw [hrange_img]
      _ = (Subgroup.closure (Set.range a)).map (rootDiagUnitHom .E6 Ω) := by
          rw [MonoidHom.map_closure]
      _ = S.map (rootDiagUnitHom .E6 Ω) := by rw [hrange_a, hxy]
      _ = E := hSmap
  · intro i j
    fin_cases i
    · have h3 : x ^ 3 = 1 := hSexp x hxS
      simpa [a, Pi.pow_apply] using congrFun h3 j
    · have h3 : y ^ 3 = 1 := hSexp y hyS
      simpa [a, Pi.pow_apply] using congrFun h3 j

end CFSG.StandardType
