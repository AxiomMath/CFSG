module

public import CFSG.LieType.Chevalley.FixedRootCentralizerGeneration
public import CFSG.LieType.Chevalley.GraphFixedCompatibleDiagonal
public import CFSG.LieType.Chevalley.GraphFixedRankOneImage
public import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.Blueprint.ChevalleyRootArtifact
import CFSG.LinearAlgebra.SteinbergBQEvenSL2OddCyclic

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace Res417Seven

section Roots


theorem d4_artifactRoots_outer : ∀ l ∈ Tag.D4.artifactRoots, l.getD 2 0 = 0 → 0 < l.sum →
    l = [1, 0, 0, 0] ∨ l = [0, 1, 0, 0] ∨ l = [0, 0, 0, 1] := by
  decide +kernel

theorem d4_artifactRoots_middle : ∀ l ∈ Tag.D4.artifactRoots, l.getD 0 0 = 0 →
    l.getD 1 0 = 0 → l.getD 3 0 = 0 → 0 < l.sum → l = [0, 0, 1, 0] := by
  decide +kernel

theorem d4_posRoots_aux (β : Fin 4 → ℤ) (hβ : List.ofFn β ∈ Tag.D4.artifactRoots)
    (hpos : 0 < ∑ j, β j) :
    (β 2 = 0 → β = Pi.single 0 1 ∨ β = Pi.single 1 1 ∨ β = Pi.single 3 1) ∧
      (β 0 = 0 → β 1 = 0 → β 3 = 0 → β = Pi.single 2 1) := by
  have hv : List.ofFn β = [β 0, β 1, β 2, β 3] := by
    simp [List.ofFn_succ]
  have hsum : 0 < (List.ofFn β).sum := by
    rw [List.sum_ofFn]
    exact hpos
  refine ⟨fun h2 => ?_, fun h0 h1 h3 => ?_⟩
  · rcases d4_artifactRoots_outer _ hβ (by rw [hv]; exact h2) hsum with h | h | h
    · exact Or.inl (List.ofFn_injective (h.trans (by decide)))
    · exact Or.inr (Or.inl (List.ofFn_injective (h.trans (by decide))))
    · exact Or.inr (Or.inr (List.ofFn_injective (h.trans (by decide))))
  · exact List.ofFn_injective ((d4_artifactRoots_middle _ hβ (by rw [hv]; exact h0)
      (by rw [hv]; exact h1) (by rw [hv]; exact h3) hsum).trans (by decide))

theorem d4_posRoots_orbit (a : Fin TwistTag.D4.foldedTag.rank) :
    parabolicPosRoots TwistTag.D4.tag (TwistTag.D4.orbitUnion {a}) ⊆
      (fun i => (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ)) '' ↑(TwistTag.D4.orbit a) := by
  rintro α ⟨⟨hα, hzero⟩, -, hht⟩
  have hz : ∀ i, i ∉ TwistTag.D4.orbit a → α i = 0 := fun i hi =>
    hzero i (by simpa [TwistTag.mem_orbitUnion] using hi)
  obtain ⟨hout, hmid⟩ := d4_posRoots_aux α (isRoot_iff_mem_artifactRoots.1 hα) hht
  fin_cases a
  · rcases hout (hz ⟨2, by decide⟩ (by decide)) with h | h | h
    · exact ⟨⟨0, by decide⟩, by decide, h.symm⟩
    · exact ⟨⟨1, by decide⟩, by decide, h.symm⟩
    · exact ⟨⟨3, by decide⟩, by decide, h.symm⟩
  · exact ⟨⟨2, by decide⟩, by decide, (hmid (hz ⟨0, by decide⟩ (by decide))
      (hz ⟨1, by decide⟩ (by decide)) (hz ⟨3, by decide⟩ (by decide))).symm⟩

end Roots

section Levi


variable {K : Type} [Field K]

theorem graphFixedParabolicLeviUnipotent_singleton_le (σ : K →+* K)
    (a : Fin TwistTag.D4.foldedTag.rank) :
    graphFixedParabolicLeviUnipotent TwistTag.D4 K σ {a} ≤
      (orbitRankOneHom TwistTag.D4 K σ a).range := by
  rintro u ⟨hu, -, hfix⟩
  have hu' : u ∈ rootSpan TwistTag.D4.tag K
      ((fun i => (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ)) '' ↑(TwistTag.D4.orbit a)) :=
    rootSpan_mono (d4_posRoots_orbit a) hu
  obtain ⟨c, hc⟩ := exists_orbitX_eq (σ := σ) hu' hfix
  exact ⟨uSL c, by rw [orbitRankOneHom_uSL, hc]⟩

theorem canonicalRep_orbitReflection_mem_range (σ : K →+* K)
    (a : Fin TwistTag.D4.foldedTag.rank) :
    canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) ∈
      (orbitRankOneHom TwistTag.D4 K σ a).range :=
  ⟨WSL, by rw [orbitRankOneHom_WSL, canonicalRep_orbitReflection_eq_orbitN]⟩

theorem range_le_graphFixedParabolicLevi (σ : K →+* K) (a : Fin TwistTag.D4.foldedTag.rank) :
    (orbitRankOneHom TwistTag.D4 K σ a).range ≤
      graphFixedParabolicLevi TwistTag.D4 K σ {a} := by
  rw [orbitRankOneHom_range, Subgroup.closure_le]
  have hj : ∀ k : ℕ, (TwistTag.D4.perm ^ k) (TwistTag.D4.orbitMin a) ∈
      TwistTag.D4.orbitUnion {a} := fun k =>
    (TwistTag.mem_orbitUnion _).2 ⟨a, rfl, TwistTag.D4.perm_pow_mem_orbit
      (TwistTag.D4.orbitMin_mem a) k⟩
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩) <;> dsimp only
  · refine ⟨?_, graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ
      (orbitX_mem_graphFixedPosUnipotent TwistTag.D4 σ a c)⟩
    rw [coe_orbitX]
    refine list_prod_mem fun x hx => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, hj k, _, Or.inl rfl⟩)
  · refine ⟨?_, graphFixedNegUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ
      (orbitY_mem_graphFixedNegUnipotent TwistTag.D4 σ a c)⟩
    rw [coe_orbitY]
    refine list_prod_mem fun x hx => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, hj k, _, Or.inr rfl⟩)

theorem graphFixedRootTorus_le_graphFixedParabolicLevi (σ : K →+* K)
    (J : Set (Fin TwistTag.D4.foldedTag.rank)) :
    graphFixedRootTorus TwistTag.D4 K σ ≤ graphFixedParabolicLevi TwistTag.D4 K σ J :=
  fun _ hx => ⟨Subgroup.mem_sup_left hx.1.1, hx.2⟩

theorem graphFixedRootTorus_conj_mem_range {σ : K →+* K} {h : ModGL TwistTag.D4.tag K}
    (hh : h ∈ graphFixedRootTorus TwistTag.D4 K σ) (a : Fin TwistTag.D4.foldedTag.rank)
    {m : ModGL TwistTag.D4.tag K} (hm : m ∈ (orbitRankOneHom TwistTag.D4 K σ a).range) :
    h * m * h⁻¹ ∈ (orbitRankOneHom TwistTag.D4 K σ a).range := by
  obtain ⟨⟨hT, -, hfix⟩, -⟩ := hh
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  obtain ⟨u, rfl⟩ := exists_compatDiag_eq (compat_of_twistHom_rootDiagUnit hfix)
  rw [orbitRankOneHom_range] at hm ⊢
  induction hm using Subgroup.closure_induction with
  | mem s hs =>
    rcases hs with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · rw [compatDiag_conj_orbitX]
      exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
    · rw [compatDiag_conj_orbitY]
      exact Subgroup.subset_closure (Or.inr ⟨_, rfl⟩)
  | one => simp
  | mul x y _ _ hx hy =>
    have e : rootDiagUnit TwistTag.D4.tag (compatDiag TwistTag.D4 σ u) * (x * y) *
        (rootDiagUnit TwistTag.D4.tag (compatDiag TwistTag.D4 σ u))⁻¹ =
        (rootDiagUnit TwistTag.D4.tag (compatDiag TwistTag.D4 σ u) * x *
          (rootDiagUnit TwistTag.D4.tag (compatDiag TwistTag.D4 σ u))⁻¹) *
        (rootDiagUnit TwistTag.D4.tag (compatDiag TwistTag.D4 σ u) * y *
          (rootDiagUnit TwistTag.D4.tag (compatDiag TwistTag.D4 σ u))⁻¹) := by group
    rw [e]
    exact mul_mem hx hy
  | inv x _ hx =>
    have e : rootDiagUnit TwistTag.D4.tag (compatDiag TwistTag.D4 σ u) * x⁻¹ *
        (rootDiagUnit TwistTag.D4.tag (compatDiag TwistTag.D4 σ u))⁻¹ =
        (rootDiagUnit TwistTag.D4.tag (compatDiag TwistTag.D4 σ u) * x *
          (rootDiagUnit TwistTag.D4.tag (compatDiag TwistTag.D4 σ u))⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hx

theorem graphFixedRootTorus_le_normalizer (σ : K →+* K) (a : Fin TwistTag.D4.foldedTag.rank) :
    graphFixedRootTorus TwistTag.D4 K σ ≤
      Subgroup.normalizer ((orbitRankOneHom TwistTag.D4 K σ a).range :
        Set (ModGL TwistTag.D4.tag K)) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro m
  refine ⟨fun hm => graphFixedRootTorus_conj_mem_range hh a hm, fun hm => ?_⟩
  have h1 := graphFixedRootTorus_conj_mem_range (inv_mem hh) a hm
  have e : h⁻¹ * (h * m * h⁻¹) * h⁻¹⁻¹ = m := by group
  rwa [e] at h1

theorem graphFixedParabolic_singleton_le_sup (σ : K ≃+* K) (a : Fin TwistTag.D4.foldedTag.rank) :
    graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} ≤
      graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {a} ⊔
        (graphFixedRootTorus TwistTag.D4 K σ.toRingHom ⊔
          (orbitRankOneHom TwistTag.D4 K σ.toRingHom a).range) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hB, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.D4 K σ {a}
  refine sup_le (fun b hb => ?_) ((Subgroup.closure_le _).2 ?_)
  · have hb' : b ∈ (graphFixedRootBorel TwistTag.D4 K σ.toRingHom :
        Set (ModGL TwistTag.D4.tag K)) := hb
    rw [hB] at hb'
    obtain ⟨q, hq, x, hx, rfl⟩ := hb'
    obtain ⟨h, hh, v, hv, rfl⟩ := hx
    exact mul_mem (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right (mul_mem
      (Subgroup.mem_sup_left hh)
      (Subgroup.mem_sup_right (graphFixedParabolicLeviUnipotent_singleton_le _ a hv))))
  · rintro _ ⟨b, hb, rfl⟩
    rw [Set.mem_singleton_iff] at hb
    subst hb
    exact Subgroup.mem_sup_right (Subgroup.mem_sup_right
      (canonicalRep_orbitReflection_mem_range _ _))

theorem graphFixedParabolicLevi_singleton_le_sup (σ : K ≃+* K)
    (a : Fin TwistTag.D4.foldedTag.rank) :
    graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom {a} ≤
      graphFixedRootTorus TwistTag.D4 K σ.toRingHom ⊔
        (orbitRankOneHom TwistTag.D4 K σ.toRingHom a).range := by
  obtain ⟨-, -, -, -, -, -, -, -, hQP, hQnorm, hLP, huniq, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.D4 K σ {a}
  set Q := graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {a}
  set N := graphFixedRootTorus TwistTag.D4 K σ.toRingHom ⊔
    (orbitRankOneHom TwistTag.D4 K σ.toRingHom a).range
  have hNL : N ≤ graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom {a} :=
    sup_le (graphFixedRootTorus_le_graphFixedParabolicLevi _ _)
      (range_le_graphFixedParabolicLevi _ a)
  have hNQ : N ≤ Subgroup.normalizer (Q : Set (ModGL TwistTag.D4.tag K)) :=
    (hNL.trans hLP).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hQP).1 hQnorm)
  intro l hl
  have hlP := hLP hl
  have hl' : l ∈ ((Q ⊔ N : Subgroup (ModGL TwistTag.D4.tag K)) : Set (ModGL TwistTag.D4.tag K)) :=
    graphFixedParabolic_singleton_le_sup σ a hlP
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Q N hNQ] at hl'
  obtain ⟨q, hq, n, hn, hqn⟩ := hl'
  obtain ⟨_, -, hu⟩ := huniq l hlP
  have h1 := hu (1, l) ⟨Subgroup.one_mem _, hl, (one_mul l).symm⟩
  have h2 := hu (q, n) ⟨hq, hNL hn, hqn.symm⟩
  have hnl : n = l := congrArg Prod.snd (h2.trans h1.symm)
  rw [← hnl]
  exact hn

theorem pow_card_units_eq_one_of_mem_torusGroup [Finite K] {τ : Tag} {h : ModGL τ K}
    (hh : h ∈ torusGroup τ K) : h ^ Nat.card Kˣ = 1 := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  have hl : l ^ Nat.card Kˣ = 1 := funext fun i => by
    rw [Pi.pow_apply, Pi.one_apply]
    exact pow_card_eq_one'
  change rootDiagUnitHom τ K l ^ _ = 1
  rw [← map_pow, hl, map_one]

theorem mem_zpowers_pow_three {G : Type*} [Group G] {h : G} {n : ℕ} (hn : h ^ n = 1)
    (h3 : ¬ 3 ∣ n) : h ∈ Subgroup.zpowers (h ^ 3) := by
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  have hgcd := Nat.gcd_eq_gcd_ab 3 n
  rw [hcop, Nat.cast_one] at hgcd
  refine ⟨Nat.gcdA 3 n, ?_⟩
  change (h ^ 3) ^ Nat.gcdA 3 n = h
  calc (h ^ 3) ^ Nat.gcdA 3 n = (h ^ 3) ^ Nat.gcdA 3 n * (h ^ n) ^ Nat.gcdB 3 n := by
        rw [hn, one_zpow, mul_one]
    _ = h ^ (((3 : ℕ) : ℤ) * Nat.gcdA 3 n + (n : ℤ) * Nat.gcdB 3 n) := by
        rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    _ = h := by rw [← hgcd, zpow_one]

theorem mem_range_of_mem_graphFixedParabolicLevi [Finite K] (σ : K ≃+* K)
    (h3 : ¬ 3 ∣ Nat.card Kˣ) (a : Fin TwistTag.D4.foldedTag.rank) {x : ModGL TwistTag.D4.tag K}
    (hx : x ∈ graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom {a}) (hx3 : x ^ 3 = 1) :
    x ∈ (orbitRankOneHom TwistTag.D4 K σ.toRingHom a).range := by
  set M := (orbitRankOneHom TwistTag.D4 K σ.toRingHom a).range
  set H := graphFixedRootTorus TwistTag.D4 K σ.toRingHom
  have hHM : H ≤ Subgroup.normalizer (M : Set (ModGL TwistTag.D4.tag K)) :=
    graphFixedRootTorus_le_normalizer _ a
  have hx' : x ∈ ((M ⊔ H : Subgroup (ModGL TwistTag.D4.tag K)) :
      Set (ModGL TwistTag.D4.tag K)) := by
    rw [sup_comm]
    exact graphFixedParabolicLevi_singleton_le_sup σ a hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left M H hHM] at hx'
  obtain ⟨m, hm, h, hh, rfl⟩ := hx'
  have hc : ∀ n ∈ M, h * n * h⁻¹ ∈ M := fun n hn =>
    (Subgroup.mem_normalizer_iff.1 (hHM hh) n).1 hn
  have hh3 : h ^ 3 ∈ M := by
    have e : (m * h) ^ 3 = m * (h * m * h⁻¹) * (h * (h * m * h⁻¹) * h⁻¹) * h ^ 3 := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc, inv_mul_cancel_left]
    have e' : h ^ 3 = (m * (h * m * h⁻¹) * (h * (h * m * h⁻¹) * h⁻¹))⁻¹ * (m * h) ^ 3 := by
      rw [e, inv_mul_cancel_left]
    change (m * h) ^ 3 = 1 at hx3
    rw [e', hx3, mul_one]
    exact inv_mem (mul_mem (mul_mem hm (hc m hm)) (hc _ (hc m hm)))
  have hhn : h ^ Nat.card Kˣ = 1 := pow_card_units_eq_one_of_mem_torusGroup hh.1.1
  have hhM : h ∈ M := (Subgroup.zpowers_le.2 hh3) (mem_zpowers_pow_three hhn h3)
  exact mul_mem hm hhM

theorem exists_subset_singleton_of_ne_univ {J : Set (Fin TwistTag.D4.foldedTag.rank)}
    (hJ : J ≠ Set.univ) : ∃ a : Fin TwistTag.D4.foldedTag.rank, J ⊆ {a} := by
  obtain ⟨b, hb⟩ : ∃ b, b ∉ J := by
    by_contra h
    push Not at h
    exact hJ (Set.eq_univ_of_forall h)
  have key : ∀ b' : Fin 2, ∃ c : Fin 2, ∀ d : Fin 2, d ≠ b' → d = c := by decide
  obtain ⟨c, hc⟩ := key b
  exact ⟨c, fun d hd => hc d (fun h => hb (h ▸ hd))⟩

theorem graphFixedParabolicLevi_mono (σ : K →+* K) {J J' : Set (Fin TwistTag.D4.foldedTag.rank)}
    (hJ : J ⊆ J') :
    graphFixedParabolicLevi TwistTag.D4 K σ J ≤ graphFixedParabolicLevi TwistTag.D4 K σ J' := by
  refine inf_le_inf_right _ (sup_le_sup_left (Subgroup.closure_mono ?_) _)
  rintro g ⟨j, hj, c, hc⟩
  refine ⟨j, ?_, c, hc⟩
  obtain ⟨b, hb, hjb⟩ := (TwistTag.mem_orbitUnion _).1 hj
  exact (TwistTag.mem_orbitUnion _).2 ⟨b, hJ hb, hjb⟩

theorem card_le_three_of_le_graphFixedParabolicLevi [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ : σ ^ 3 = 1) (h3 : ¬ 3 ∣ Nat.card Kˣ) {J : Set (Fin TwistTag.D4.foldedTag.rank)}
    (hJ : J ≠ Set.univ) {E : Subgroup (ModGL TwistTag.D4.tag K)}
    (hEL : E ≤ graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom J)
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) : Nat.card E ≤ 3 := by
  obtain ⟨a, haJ⟩ := exists_subset_singleton_of_ne_univ hJ
  set R := orbitRankOneHom TwistTag.D4 K σ.toRingHom a
  have hinj : Function.Injective R := orbitRankOneHom_injective_D4 hσ a
  have hEM : E ≤ R.range := fun x hx => mem_range_of_mem_graphFixedParabolicLevi σ h3 a
    (graphFixedParabolicLevi_mono _ haJ (hEL hx)) (hE3 x hx)
  set E' := E.comap R
  have hEE' : E'.map R = E := Subgroup.map_comap_eq_self hEM
  have hcard : Nat.card E = Nat.card E' := by
    rw [← hEE', Subgroup.card_map_of_injective hinj]
  have hE'3 : ∀ x : E', x ^ 3 = 1 := fun x => Subtype.ext (hinj (by
    rw [Subgroup.coe_pow, map_pow, Subgroup.coe_one, map_one]
    exact hE3 _ x.2))
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 E' := fun x => ⟨1, by rw [pow_one]; exact hE'3 x⟩
  have : Finite (orbitField TwistTag.D4 K σ.toRingHom a) := Subtype.finite
  have hcyc := CFSG.LinearAlgebra.even_SL2_odd_prime_subgroups_cyclic (by norm_num) E' hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E')
  have : Finite E' := Subtype.finite
  rw [hcard, ← orderOf_eq_card_of_forall_mem_zpowers hg]
  exact orderOf_le_of_pow_eq_one (by norm_num) (hE'3 g)

end Levi

end Res417Seven

end CFSG.RankThree.PartTwo.Sec4
