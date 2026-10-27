module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2GS03E8Gen

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GS03E8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement

@[expose] def outerSteps : List FrameStep :=
  [.comm 1 3 11, .comm 4 5 17, .comm 6 7 21, .comm 10 11 49, .comm 9 12 75, .comm 3 4 15,
    .comm 2 14 29, .comm 5 6 19, .comm 7 8 237, .comm 16 17 233, .comm 15 18 226, .comm 13 19 196,
    .comm 2 3 13, .comm 1 21 26, .comm 14 16 47, .comm 22 23 90, .comm 0 2 9, .comm 25 14 39,
    .comm 9 10 43, .comm 26 27 98, .comm 24 28 176, .comm 20 29 23, .comm 2 30 8, .comm 21 12 77,
    .comm 25 9 38, .comm 33 23 99, .comm 32 34 171, .comm 1 14 27, .comm 21 10 45, .comm 36 37 89,
    .comm 26 18 223, .comm 38 39 182, .comm 35 40 10, .comm 13 39 188, .comm 42 29 12,
    .comm 4 16 33, .comm 22 44 74, .comm 45 28 168, .comm 22 12 91, .comm 47 39 180, .comm 46 48 14,
    .comm 9 37 73, .comm 33 12 100, .comm 50 51 169, .comm 24 39 181, .comm 52 53 16, .comm 9 15 57,
    .comm 55 51 159, .comm 56 53 32, .comm 4 57 18, .comm 52 40 20, .comm 46 53 22]

@[expose] def outerFacts : List (List ℕ) := [[0], [1], [2], [3], [4], [5], [6], [7], [239]]

theorem outerCheck : simpleRootsB (runSteps outerFacts outerSteps) = true ∧
    commB 3 0 = true ∧ sumB 3 2 13 = true ∧ sumB 0 13 24 = true := by
  decide +kernel

section Outer

variable {K : Type} [Field K]

private lemma units_entrywise_pinnedX (δ : K ≃+* K) (α : Fin Tag.E8.rank → ℤ) (c : K) :
    Units.map (entrywiseHom (τ := .E8) δ.toRingHom) (pinnedX .E8 K α c) =
      pinnedX .E8 K α (δ c) := by
  refine Units.ext ?_
  rw [Units.coe_map]
  exact entrywise_pinnedX δ.toRingHom α c

private lemma pinnedX_mul_self [CharP K 2] (α : Fin Tag.E8.rank → ℤ) (c : K) :
    pinnedX .E8 K α c * pinnedX .E8 K α c = 1 := by
  rw [← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]

private lemma pinnedX_inv_self [CharP K 2] (α : Fin Tag.E8.rank → ℤ) (c : K) :
    (pinnedX .E8 K α c)⁻¹ = pinnedX .E8 K α c :=
  inv_eq_of_mul_eq_one_right (pinnedX_mul_self α c)

private lemma twist_pinnedX {δ : K ≃+* K} [CharP K 2] {d : K} (hd : d + δ d = 1)
    (α : Fin Tag.E8.rank → ℤ) :
    (⟨pinnedX .E8 K α d, pinnedX_mem_adjointGroup α d⟩ : adjointGroup .E8 K) *
        (entrywiseAdjointAut .E8 δ
          ⟨pinnedX .E8 K α d, pinnedX_mem_adjointGroup α d⟩)⁻¹ =
      ⟨pinnedX .E8 K α 1, pinnedX_mem_adjointGroup α 1⟩ := by
  refine Subtype.ext ?_
  change (pinnedX .E8 K α d : ModGL .E8 K) *
      (((entrywiseAdjointAut .E8 δ
        (⟨pinnedX .E8 K α d, pinnedX_mem_adjointGroup α d⟩ : adjointGroup .E8 K)) :
          ModGL .E8 K)⁻¹) = pinnedX .E8 K α 1
  rw [coe_entrywiseAdjointAut]
  change (pinnedX .E8 K α d : ModGL .E8 K) *
      ((Units.map (entrywiseHom (τ := .E8) δ.toRingHom) (pinnedX .E8 K α d))⁻¹) =
    pinnedX .E8 K α 1
  rw [units_entrywise_pinnedX, pinnedX_neg, ← pinnedX_add, CharTwo.neg_eq, hd]

theorem exists_closure_twist_eq_top [Finite K] [CharP K 2] {δ : K ≃+* K}
    (hδ : ∀ c, δ (δ c) = c) (hδ1 : ∃ c, δ c ≠ c) :
    ∃ L : List (adjointGroup .E8 K), L.length ≤ 10 ∧
      Subgroup.closure {y | ∃ s ∈ L, y = s * (entrywiseAdjointAut .E8 δ s)⁻¹} = ⊤ := by
  classical
  obtain ⟨a', ha'⟩ := hδ1
  have hβ : a' + δ a' ≠ 0 := by
    intro h
    apply ha'
    have h1 : δ a' = -a' := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact h
    rw [h1, CharTwo.neg_eq]
  have hδβ : δ (a' + δ a') = a' + δ a' := by
    rw [map_add, hδ a']
    exact add_comm _ _
  let d : K := a' / (a' + δ a')
  have hd : d + δ d = 1 := by
    have hδd : δ d = δ a' / (a' + δ a') := by
      change δ (a' / (a' + δ a')) = δ a' / (a' + δ a')
      rw [map_div₀, hδβ]
    rw [hδd, ← add_div]
    exact div_self hβ
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := Kˣ)
  let a : K := (g : K)
  have ha : ∀ c : K, c ≠ 0 → ∃ n : ℕ, a ^ n = c := by
    intro c hc
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (Units.mk0 c hc) g).1 (hg (Units.mk0 c hc))
    refine ⟨n, ?_⟩
    have h2 : ((g ^ n : Kˣ) : K) = c := by
      rw [hn]
      exact Units.val_mk0 hc
    simpa [a, Units.val_pow_eq_pow_val] using h2
  let basePos : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 239]
  let dElt : ℕ → adjointGroup .E8 K := fun k =>
    ⟨pinnedX .E8 K (Tag.E8.rootCertificate.root k) d, pinnedX_mem_adjointGroup _ _⟩
  let s10 : adjointGroup .E8 K :=
    ⟨pinnedX .E8 K (Tag.E8.rootCertificate.root 0) a *
        pinnedX .E8 K (Tag.E8.rootCertificate.root 2) d,
      mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _)⟩
  let L : List (adjointGroup .E8 K) := basePos.map dElt ++ [s10]
  refine ⟨L, ?_, ?_⟩
  · change (basePos.map dElt ++ [s10]).length ≤ 10
    simp [basePos]
  · let S0 : Set (adjointGroup .E8 K) :=
      {y | ∃ s ∈ L, y = s * (entrywiseAdjointAut .E8 δ s)⁻¹}
    let H : Subgroup (ModGL .E8 K) :=
      Subgroup.map (adjointGroup .E8 K).subtype (Subgroup.closure S0)
    have memH : ∀ t ∈ L, ((t * (entrywiseAdjointAut .E8 δ t)⁻¹ : adjointGroup .E8 K) :
        ModGL .E8 K) ∈ H := by
      intro t ht
      change ((t * (entrywiseAdjointAut .E8 δ t)⁻¹ : adjointGroup .E8 K) :
        ModGL .E8 K) ∈ Subgroup.map (adjointGroup .E8 K).subtype (Subgroup.closure S0)
      exact Subgroup.apply_coe_mem_map (adjointGroup .E8 K).subtype (Subgroup.closure S0)
        ⟨t * (entrywiseAdjointAut .E8 δ t)⁻¹, Subgroup.subset_closure ⟨t, ht, rfl⟩⟩
    have hlen : Tag.E8.rootCertificate.roots.length = 240 := rfl
    have hroot3 : IsRoot .E8 (Tag.E8.rootCertificate.root 3) :=
      RootCertificate.isRoot_root (Tag.rootCertificate_check .E8) 3 (by rw [hlen]; decide)
    have hroot13 : IsRoot .E8 (Tag.E8.rootCertificate.root 13) :=
      RootCertificate.isRoot_root (Tag.rootCertificate_check .E8) 13 (by rw [hlen]; decide)
    have hroot24 : IsRoot .E8 (Tag.E8.rootCertificate.root 24) :=
      RootCertificate.isRoot_root (Tag.rootCertificate_check .E8) 24 (by rw [hlen]; decide)
    have houter : outerFacts = basePos.map (fun k => [k]) := rfl
    have hFacts : ∀ L₀ ∈ outerFacts, e8FrameProd K L₀ ∈ H := by
      intro L₀ hL₀
      rw [houter] at hL₀
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hL₀
      have hmem : dElt k ∈ L := by
        change dElt k ∈ basePos.map dElt ++ [s10]
        exact List.mem_append_left _ (List.mem_map.2 ⟨k, hk, rfl⟩)
      have h := memH (dElt k) hmem
      rw [show dElt k = (⟨pinnedX .E8 K (Tag.E8.rootCertificate.root k) d,
        pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .E8 K) from rfl] at h
      rw [twist_pinnedX (δ := δ) hd, Subgroup.coe_mk] at h
      simpa [e8FrameProd] using h
    have hsteps : ∀ L₀ ∈ runSteps outerFacts outerSteps, e8FrameProd K L₀ ∈ H :=
      e8FrameProd_mem_of_mem_runSteps hFacts outerSteps
    have h1H : ∀ α, IsRoot .E8 α → pinnedX .E8 K α 1 ∈ H :=
      pinnedX_one_mem_of_simpleRootsB hsteps outerCheck.1
    set t3 : ModGL .E8 K := pinnedX .E8 K (Tag.E8.rootCertificate.root 3) 1 with ht3
    set p0 : ModGL .E8 K := pinnedX .E8 K (Tag.E8.rootCertificate.root 0) a with hp0
    set q2 : ModGL .E8 K := pinnedX .E8 K (Tag.E8.rootCertificate.root 2) 1 with hq2
    set r0 : ModGL .E8 K := pinnedX .E8 K (Tag.E8.rootCertificate.root 0) (δ a) with hr0
    set x13 : ModGL .E8 K := pinnedX .E8 K (Tag.E8.rootCertificate.root 13) 1 with hx13
    have ht3H : t3 ∈ H := by
      rw [ht3]
      exact h1H _ hroot3
    have hx13H : x13 ∈ H := by
      rw [hx13]
      exact h1H _ hroot13
    have hιu : ((entrywiseAdjointAut .E8 δ s10 : adjointGroup .E8 K) : ModGL .E8 K)⁻¹ =
        pinnedX .E8 K (Tag.E8.rootCertificate.root 2) (δ d) * r0 := by
      rw [coe_entrywiseAdjointAut]
      change ((Units.map (entrywiseHom (τ := .E8) δ.toRingHom)
        (pinnedX .E8 K (Tag.E8.rootCertificate.root 0) a *
          pinnedX .E8 K (Tag.E8.rootCertificate.root 2) d))⁻¹) =
        pinnedX .E8 K (Tag.E8.rootCertificate.root 2) (δ d) * r0
      rw [map_mul, mul_inv_rev, units_entrywise_pinnedX, units_entrywise_pinnedX,
        pinnedX_inv_self, pinnedX_inv_self, hr0]
    have huMod : ((s10 * (entrywiseAdjointAut .E8 δ s10)⁻¹ : adjointGroup .E8 K) :
        ModGL .E8 K) = p0 * q2 * r0 := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hιu]
      change (pinnedX .E8 K (Tag.E8.rootCertificate.root 0) a *
          pinnedX .E8 K (Tag.E8.rootCertificate.root 2) d) *
          (pinnedX .E8 K (Tag.E8.rootCertificate.root 2) (δ d) * r0) = p0 * q2 * r0
      rw [show (pinnedX .E8 K (Tag.E8.rootCertificate.root 0) a *
            pinnedX .E8 K (Tag.E8.rootCertificate.root 2) d) *
            (pinnedX .E8 K (Tag.E8.rootCertificate.root 2) (δ d) * r0) =
          pinnedX .E8 K (Tag.E8.rootCertificate.root 0) a *
            (pinnedX .E8 K (Tag.E8.rootCertificate.root 2) d *
              pinnedX .E8 K (Tag.E8.rootCertificate.root 2) (δ d)) * r0 from by group]
      rw [← pinnedX_add, hd, hp0, hq2]
    have htp : t3 * p0 = p0 * t3 := by
      rw [ht3, hp0]
      exact (commute_pinnedX_of_commB (a := 3) (c := 0) outerCheck.2.1 (1 : K) a).eq
    have htr : t3 * r0 = r0 * t3 := by
      rw [ht3, hr0]
      exact (commute_pinnedX_of_commB (a := 3) (c := 0) outerCheck.2.1 (1 : K) (δ a)).eq
    have ht3p : t3 * p0 * t3⁻¹ = p0 := by
      rw [htp]
      group
    have ht3r : t3 * r0 * t3⁻¹ = r0 := by
      rw [htr]
      group
    have hcomm13 : ⁅t3, q2⁆ = x13 := by
      rw [ht3, hq2, hx13]
      simpa using commutatorElement_pinnedX_of_sumB (a := 3) (b := 2) (p := 13)
        outerCheck.2.2.1 (1 : K) (1 : K)
    have ht3q : t3 * q2 * t3⁻¹ = x13 * q2 := by
      have h := hcomm13
      rw [commutatorElement_def] at h
      calc t3 * q2 * t3⁻¹ = (t3 * q2 * t3⁻¹ * q2⁻¹) * q2 := by group
        _ = x13 * q2 := by rw [h]
    set u : adjointGroup .E8 K := s10 * (entrywiseAdjointAut .E8 δ s10)⁻¹ with hu
    have huM : (u : ModGL .E8 K) = p0 * q2 * r0 := by
      rw [hu]
      exact huMod
    have huH : (u : ModGL .E8 K) ∈ H := by
      rw [hu]
      exact memH s10 (by
        change s10 ∈ basePos.map dElt ++ [s10]
        exact List.mem_append_right _ (List.mem_singleton_self _))
    have huInv : (u : ModGL .E8 K)⁻¹ = r0 * q2 * p0 := by
      rw [huM]
      simp only [mul_inv_rev]
      rw [hp0, hq2, hr0, pinnedX_inv_self, pinnedX_inv_self, pinnedX_inv_self]
      group
    have hconj : t3 * (u : ModGL .E8 K) * t3⁻¹ = p0 * (x13 * q2) * r0 := by
      rw [huM]
      calc t3 * (p0 * q2 * r0) * t3⁻¹
          = (t3 * p0 * t3⁻¹) * (t3 * q2 * t3⁻¹) * (t3 * r0 * t3⁻¹) := by group
        _ = p0 * (x13 * q2) * r0 := by rw [ht3p, ht3q, ht3r]
    have hcalc : p0 * (x13 * q2) * r0 * (r0 * q2 * p0) = p0 * x13 * p0⁻¹ := by
      calc p0 * (x13 * q2) * r0 * (r0 * q2 * p0)
          = p0 * x13 * (q2 * (r0 * r0) * q2) * p0 := by group
        _ = p0 * x13 * (q2 * 1 * q2) * p0 := by
              rw [show r0 * r0 = 1 from pinnedX_mul_self _ _]
        _ = p0 * x13 * (q2 * q2) * p0 := by rw [mul_one]
        _ = p0 * x13 * 1 * p0 := by
              rw [show q2 * q2 = 1 from pinnedX_mul_self _ _]
        _ = p0 * x13 * p0 := by rw [mul_one]
        _ = p0 * x13 * p0⁻¹ := by
              rw [show p0⁻¹ = p0 from pinnedX_inv_self _ _]
    have hcommH : t3 * (u : ModGL .E8 K) * t3⁻¹ * (u : ModGL .E8 K)⁻¹ ∈ H :=
      mul_mem (mul_mem (mul_mem ht3H huH) (inv_mem ht3H)) (inv_mem huH)
    rw [hconj, huInv, hcalc] at hcommH
    have h2 : pinnedX .E8 K (Tag.E8.rootCertificate.root 0) a *
        e8FrameProd K [13] * (pinnedX .E8 K (Tag.E8.rootCertificate.root 0) a)⁻¹ ∈ H := by
      simpa [hp0, hx13, e8FrameProd] using hcommH
    have h1 : e8FrameProd K (13 :: []) ∈ H := by
      have h := hx13H
      rw [hx13] at h
      simpa [e8FrameProd] using h
    have h24 : pinnedX .E8 K (Tag.E8.rootCertificate.root 24) a ∈ H :=
      pinnedX_mem_of_conj_e8FrameProd (H := H) (g := 0) (b := 13) (p := 24) (L := [])
        outerCheck.2.2.2 (by simp) a h1 h2
    have hAle : adjointGroup .E8 K ≤ H :=
      adjointGroup_le_of_pinnedX_generator (H := H) h1H ha hroot24 h24
    have hAle' : adjointGroup .E8 K ≤ Subgroup.map (adjointGroup .E8 K).subtype
        (Subgroup.closure S0) := hAle
    have hmap : Subgroup.map (adjointGroup .E8 K).subtype (Subgroup.closure S0) =
        adjointGroup .E8 K :=
      le_antisymm (Subgroup.map_subtype_le _) hAle'
    have htop : (⊤ : Subgroup (adjointGroup .E8 K)) ≤ Subgroup.closure S0 := by
      refine (Subgroup.map_le_map_iff_of_injective
        (Subgroup.subtype_injective (adjointGroup .E8 K))).1 ?_
      rw [Subgroup.map_top, Subgroup.range_subtype, hmap]
    change Subgroup.closure S0 = ⊤
    exact eq_top_iff.2 htop

end Outer

end CFSG.LocalAnalysis.WeakClosure81.GS03E8
