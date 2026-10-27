module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepFactsLevi

public section

namespace CFSG.StandardType

namespace SUFacts

open Matrix CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU)

section Radical

variable {F : Type} [Field F] [Finite F] [CharP F 2] {a : ℕ} (h : UnitaryFieldData 2 a F)

theorem centMat_eq_blockMat_of_mem_ker {g : centT F a} (hg : g ∈ (centPi h).ker) :
    centMat g = blockMat 1 0 ((centMat g).submatrix hi lo) 1 := by
  obtain ⟨h1, h2⟩ := blocks_of_mem_centralizer g.2
  have hA : blockA (centMat g) = 1 := by
    have := congrArg (fun x : unitarySU 2 a F 3 => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
      ((MonoidHom.mem_ker).mp hg)
    simpa [matrix_centPi] using this
  set G := (((g : SU (unitaryInvolution F 2 a) 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)
    with hGdef
  have hcm : centMat g = G := rfl
  rw [hcm] at hA ⊢
  have hll : ∀ i j, G (lo i) (lo j) = (1 : Matrix (Fin 3) (Fin 3) F) i j := fun i j => by
    rw [← hA]
    rfl
  ext x y
  rcases fin_six_cases x with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rcases fin_six_cases y with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [blockMat_lo_lo, hll]
  · rw [blockMat_lo_hi, h1, Matrix.zero_apply]
  · rw [blockMat_hi_lo, submatrix_apply]
  · rw [blockMat_hi_hi, h2, hll, one_apply, one_apply]
    by_cases hij : i = j
    · subst hij; rw [ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right (fun h' => hij (Fin.rev_injective h')), ite_eq_right hij]

theorem mul_comm_of_mem_ker {g g' : centT F a} (hg : g ∈ (centPi h).ker)
    (hg' : g' ∈ (centPi h).ker) : g * g' = g' * g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change centMat g * centMat g' = centMat g' * centMat g
  rw [centMat_eq_blockMat_of_mem_ker h hg, centMat_eq_blockMat_of_mem_ker h hg', blockMat_mul,
    blockMat_mul]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    add_comm]

theorem mul_self_of_mem_ker {g : centT F a} (hg : g ∈ (centPi h).ker) : g * g = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change centMat g * centMat g = 1
  rw [centMat_eq_blockMat_of_mem_ker h hg, blockMat_mul]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [CharTwo.add_self_eq_zero, blockMat_one]

theorem isPGroup_ker_centPi : IsPGroup 2 (centPi h).ker := fun g =>
  ⟨1, Subtype.ext (by rw [pow_one, sq]; exact mul_self_of_mem_ker h g.2)⟩

@[expose] noncomputable def leviT (S : Subgroup (unitarySU 2 a F 3)) : Subgroup (centT F a) :=
  (centPi h).ker ⊔ S.map (centDelta h)

theorem isPGroup_leviT {S : Subgroup (unitarySU 2 a F 3)} (hS : IsPGroup 2 S) :
    IsPGroup 2 (leviT h S) :=
  IsPGroup.to_sup_of_normal_left (isPGroup_ker_centPi h) (hS.map _)

theorem centPi_mem_of_mem_leviT {S : Subgroup (unitarySU 2 a F 3)} {t : centT F a}
    (ht : t ∈ leviT h S) : centPi h t ∈ S := by
  have hmap : (leviT h S).map (centPi h) ≤ S := by
    rw [leviT, Subgroup.map_sup, sup_le_iff]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [MonoidHom.mem_ker.mp hx]
      exact S.one_mem
    · rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      rw [centPi_centDelta]
      exact hs
  exact hmap ⟨t, ht, rfl⟩

theorem card_leviT_ge (S : Subgroup (unitarySU 2 a F 3)) :
    Nat.card (centPi h).ker * Nat.card S ≤ Nat.card (leviT h S) := by
  set f := (centPi h).comp (leviT h S).subtype with hf
  have hsplit := Subgroup.card_ker_mul_card_range f
  have hker : Nat.card (centPi h).ker ≤ Nat.card f.ker := by
    refine Nat.card_le_card_of_injective (fun x => ⟨⟨x, le_sup_left (a := (centPi h).ker) x.2⟩,
      by rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply]; exact x.2⟩) ?_
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : f.ker => ((z : leviT h S) : centT F a)) hxy)
  have hran : Nat.card S ≤ Nat.card f.range := by
    have hmem : ∀ s : S, centDelta h s ∈ leviT h S := fun s =>
      le_sup_right (a := (centPi h).ker) (b := S.map (centDelta h)) ⟨s, s.2, rfl⟩
    have hf' : ∀ s : S, f ⟨centDelta h s, hmem s⟩ = s := fun s => by
      rw [hf, MonoidHom.comp_apply]
      exact centPi_centDelta h s
    refine Nat.card_le_card_of_injective (fun s => ⟨s, ⟨centDelta h s, hmem s⟩, hf' s⟩) ?_
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : f.range => (z : unitarySU 2 a F 3)) hxy)
  rw [← hsplit]
  exact Nat.mul_le_mul hker hran

end Radical

section HSide

variable {F : Type} [Field F] [Finite F] [CharP F 2] {a : ℕ} {G : Type} [Group G]
  {ψ : SU (unitaryInvolution F 2 a) 6 →* G}

omit [Finite F] [CharP F 2] in
theorem ordProj_two_card_unitarySU_three (h : UnitaryFieldData 2 a F) :
    ordProj[2] (Nat.card (unitarySU 2 a F 3)) = 2 ^ (3 * a) := by
  rw [CFSG.SeitzReduction.LinearPilot.card_unitarySU_eq_nat (n := 3) h (by norm_num)]
  have hodd : Odd (∏ j ∈ Finset.Icc 2 3, CFSG.SeitzReduction.LinearPilot.unitaryFactor (2 ^ a) j) :=
    Finset.prod_induction _ Odd (fun _ _ h1 h2 => h1.mul h2) odd_one
      fun j hj => odd_unitaryFactor h.one_le (by simp at hj; omega)
  rw [Nat.factorization_mul (by positivity) hodd.pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (fun h2 => (Nat.not_even_iff_odd.mpr hodd)
      (even_iff_two_dvd.mpr h2)), add_zero, ← pow_mul, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two, smul_eq_mul, mul_one]
  congr 1
  norm_num
  ring

theorem card_le_ordProj_of_isPGroup {Y : Type*} [Group Y] {X K : Subgroup Y} [Finite K]
    (hX : IsPGroup 2 X) (hXK : X ≤ K) : Nat.card X ≤ ordProj[2] (Nat.card K) := by
  have : Finite X := Finite.of_injective (Subgroup.inclusion hXK) (Subgroup.inclusion_injective hXK)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hX
  have hdvd : Nat.card X ∣ Nat.card K := Subgroup.card_dvd_of_le hXK
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  rw [hn] at hdvd ⊢
  exact Nat.pow_le_pow_right (by norm_num)
    ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hK0).mp hdvd)

theorem ggCentOTwoPrime_three_le_map_centT
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 a) 6)) :
    ggCentOTwoPrime ψ.range (ψ (ggInvSU (unitaryInvolution F 2 a) 6 3)) ≤ (centT F a).map ψ := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨⟨g, rfl⟩, hys, -⟩
  exact ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr
    (commute_of_map_commute_SU hker (ggInvSU_mul_self_of_le (by norm_num)) hys), rfl⟩

theorem map_le_ggCentOTwoPrime_three {T : Subgroup (centT F a)} (hT : IsPGroup 2 T) :
    (T.map (centT F a).subtype).map ψ ≤
      ggCentOTwoPrime ψ.range (ψ (ggInvSU (unitaryInvolution F 2 a) 6 3)) := by
  rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  refine Subgroup.subset_closure ⟨⟨(t : SU (unitaryInvolution F 2 a) 6), rfl⟩, ?_, k, ?_⟩
  · change ψ (t : SU (unitaryInvolution F 2 a) 6) * ψ (ggInvSU (unitaryInvolution F 2 a) 6 3) =
      ψ (ggInvSU (unitaryInvolution F 2 a) 6 3) * ψ (t : SU (unitaryInvolution F 2 a) 6)
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp t.2]
  · have h1 := congrArg (fun x : T => ((x : centT F a) : SU (unitaryInvolution F 2 a) 6)) hk
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1
    change ψ (t : SU (unitaryInvolution F 2 a) 6) ^ 2 ^ k = 1
    rw [← map_pow, h1, map_one]

theorem card_map_centT_of_isPGroup
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 a) 6))
    {T : Subgroup (centT F a)} (hT : IsPGroup 2 T) :
    Nat.card ((T.map (centT F a).subtype).map ψ) = Nat.card T := by
  rw [card_map_of_isPGroup_SU hker (hT.map _),
    Subgroup.card_map_of_injective (centT F a).subtype_injective]

theorem ordProj_card_ggCentOTwoPrime_three_le [Finite G] (h : UnitaryFieldData 2 a F)
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 a) 6)) :
    ordProj[2] (Nat.card (ggCentOTwoPrime ψ.range (ψ (ggInvSU (unitaryInvolution F 2 a) 6 3)))) ≤
      Nat.card (centPi h).ker * 2 ^ (3 * a) := by
  have hle := ggCentOTwoPrime_three_le_map_centT hker
  have h0 : Nat.card ((centT F a).map ψ) ≠ 0 := Nat.card_pos.ne'
  have h1 := Nat.ordProj_dvd_ordProj_of_dvd h0 (Subgroup.card_dvd_of_le hle) 2
  have h2 : ordProj[2] (Nat.card ((centT F a).map ψ)) =
      Nat.card (centPi h).ker * ordProj[2] (Nat.card (centPi h).range) := by
    rw [ordProj_two_card_map_SU hker, ← Subgroup.card_ker_mul_card_range (centPi h),
      Nat.ordProj_mul 2 Nat.card_pos.ne' Nat.card_pos.ne',
      SLAlpha.ordProj_two_card_of_isPGroup (isPGroup_ker_centPi h)]
  have h3 : ordProj[2] (Nat.card (centPi h).range) ≤ 2 ^ (3 * a) := by
    rw [← ordProj_two_card_unitarySU_three h]
    exact Nat.le_of_dvd (Nat.ordProj_pos _ _)
      (Nat.ordProj_dvd_ordProj_of_dvd Nat.card_pos.ne' (Subgroup.card_subgroup_dvd_card _) 2)
  rw [h2] at h1
  exact (Nat.le_of_dvd (Nat.mul_pos Nat.card_pos (Nat.ordProj_pos _ _)) h1).trans
    (Nat.mul_le_mul_left _ h3)

end HSide

section Main

variable {F : Type} [Field F] [Finite F] [CharP F 2] {a : ℕ} {G : Type} [Group G]
  {ψ : SU (unitaryInvolution F 2 a) 6 →* G}

theorem mem_ker_of_map_eq (h : UnitaryFieldData 2 a F)
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 a) 6))
    {S₁ S₂ : Subgroup (unitarySU 2 a F 3)}
    (htr : ∀ g₁ ∈ S₁, ∀ g₂ ∈ S₂, ∀ z ∈ Subgroup.center (unitarySU 2 a F 3), g₁ = g₂ * z → g₁ = 1)
    {t₁ t₂ : centT F a} (ht₁ : t₁ ∈ leviT h S₁) (ht₂ : t₂ ∈ leviT h S₂)
    (he : ψ (t₁ : SU (unitaryInvolution F 2 a) 6) = ψ (t₂ : SU (unitaryInvolution F 2 a) 6)) :
    t₁ ∈ (centPi h).ker := by
  set k := (t₂ : SU (unitaryInvolution F 2 a) 6)⁻¹ * (t₁ : SU (unitaryInvolution F 2 a) 6) with hk
  have hkc : k ∈ Subgroup.center (SU (unitaryInvolution F 2 a) 6) :=
    hker (by rw [MonoidHom.mem_ker, hk, map_mul, map_inv, he, inv_mul_cancel])
  have hkT : k ∈ centT F a := Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_center_iff.mp hkc _).symm
  set k' : centT F a := ⟨k, hkT⟩ with hk'
  have ht : t₁ = t₂ * k' := Subtype.ext (by
    change (t₁ : SU (unitaryInvolution F 2 a) 6) = (t₂ : SU (unitaryInvolution F 2 a) 6) * k
    rw [hk, mul_inv_cancel_left])
  have hπk : centPi h k' ∈ Subgroup.center (unitarySU 2 a F 3) := by
    rw [Subgroup.mem_center_iff]
    intro A
    have hc : centDelta h A * k' = k' * centDelta h A :=
      Subtype.ext (Subgroup.mem_center_iff.mp hkc _)
    rw [← centPi_centDelta h A, ← map_mul, ← map_mul, hc]
  have h1 := htr _ (centPi_mem_of_mem_leviT h ht₁) _ (centPi_mem_of_mem_leviT h ht₂) _ hπk
    (by rw [ht, map_mul])
  exact MonoidHom.mem_ker.mpr h1

theorem ggCentOTwoPrime_three_facts [Finite G] (ha : 1 ≤ a) (hF : Nat.card F = (2 ^ a) ^ 2)
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 a) 6)) :
    2 ^ (12 * a) ≤ ordProj[2] (Nat.card ↥(ggCentOTwoPrime ψ.range
        (ψ (ggInvSU (unitaryInvolution F 2 a) 6 3)))) ∧
      ∀ N : Subgroup ↥(ggCentOTwoPrime ψ.range (ψ (ggInvSU (unitaryInvolution F 2 a) 6 3))),
        N.Normal → IsPGroup 2 N → ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
  have h : UnitaryFieldData 2 a F := ⟨Nat.prime_two, ha, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨S₁, S₂, hS₁, hS₂, hc₁, hc₂, htr⟩ := exists_transverse_sylow_pair h
  set H := ggCentOTwoPrime ψ.range (ψ (ggInvSU (unitaryInvolution F 2 a) 6 3)) with hH
  have hHup := ordProj_card_ggCentOTwoPrime_three_le h hker
  rw [← hH] at hHup
  have hsyl : ∀ S : Subgroup (unitarySU 2 a F 3), IsPGroup 2 S → 2 ^ (3 * a) ≤ Nat.card S →
      ((leviT h S).map (centT F a).subtype).map ψ ≤ H ∧
        ordProj[2] (Nat.card H) ≤ Nat.card (((leviT h S).map (centT F a).subtype).map ψ) ∧
        Nat.card (centPi h).ker * 2 ^ (3 * a) ≤
          Nat.card (((leviT h S).map (centT F a).subtype).map ψ) := by
    intro S hS hcS
    have hc := card_map_centT_of_isPGroup hker (isPGroup_leviT h hS)
    have hT : Nat.card (centPi h).ker * 2 ^ (3 * a) ≤ Nat.card (leviT h S) :=
      (Nat.mul_le_mul_left _ hcS).trans (card_leviT_ge h S)
    refine ⟨map_le_ggCentOTwoPrime_three (isPGroup_leviT h hS), ?_, by rw [hc]; exact hT⟩
    rw [hc]
    exact hHup.trans hT
  refine ⟨?_, fun N hN hN2 => ?_⟩
  · obtain ⟨hle, -, hcard⟩ := hsyl S₁ hS₁ hc₁
    have hP2 : IsPGroup 2 (((leviT h S₁).map (centT F a).subtype).map ψ) :=
      ((isPGroup_leviT h hS₁).map _).map ψ
    calc 2 ^ (12 * a) = 2 ^ (9 * a) * 2 ^ (3 * a) := by rw [← pow_add]; congr 1; ring
      _ ≤ Nat.card (centPi h).ker * 2 ^ (3 * a) :=
          Nat.mul_le_mul_right _ (card_ker_centPi_ge h)
      _ ≤ _ := hcard
      _ ≤ _ := card_le_ordProj_of_isPGroup hP2 hle
  have hin : ∀ S : Subgroup (unitarySU 2 a F 3), IsPGroup 2 S → 2 ^ (3 * a) ≤ Nat.card S →
      ∀ z ∈ N, (z : G) ∈ ((leviT h S).map (centT F a).subtype).map ψ := by
    intro S hS hcS z hz
    obtain ⟨hle, hord, -⟩ := hsyl S hS hcS
    set P := ((leviT h S).map (centT F a).subtype).map ψ with hP
    have hP2 : IsPGroup 2 P := ((isPGroup_leviT h hS).map _).map ψ
    set P' : Subgroup H := P.subgroupOf H with hP'
    have hP'2 : IsPGroup 2 P' := hP2.comap_of_injective H.subtype H.subtype_injective
    have hNP : IsPGroup 2 ↥(N ⊔ P') := IsPGroup.to_sup_of_normal_left hN2 hP'2
    have hcardP' : Nat.card P' = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    have hcard : Nat.card ↥(N ⊔ P') ≤ Nat.card P' := by
      rw [hcardP']
      calc Nat.card ↥(N ⊔ P') ≤ ordProj[2] (Nat.card (⊤ : Subgroup H)) :=
            card_le_ordProj_of_isPGroup hNP le_top
        _ = ordProj[2] (Nat.card H) := by rw [Subgroup.card_top]
        _ ≤ Nat.card P := hord
    have heq := Subgroup.eq_of_le_of_card_ge (le_sup_right : P' ≤ N ⊔ P') hcard
    have hzP' : z ∈ P' := by rw [heq]; exact le_sup_left (a := N) hz
    exact hzP'
  have hU : ∀ z ∈ N, ∃ u ∈ (centPi h).ker, (z : G) = ψ ((u : centT F a) : SU _ 6) := by
    intro z hz
    obtain ⟨_, ⟨t₁, ht₁, rfl⟩, hz₁⟩ := hin S₁ hS₁ hc₁ z hz
    obtain ⟨_, ⟨t₂, ht₂, rfl⟩, hz₂⟩ := hin S₂ hS₂ hc₂ z hz
    exact ⟨t₁, mem_ker_of_map_eq h hker htr ht₁ ht₂ (hz₁.trans hz₂.symm), hz₁.symm⟩
  intro x hx y hy
  obtain ⟨u, hu, hxu⟩ := hU x hx
  obtain ⟨v, hv, hyv⟩ := hU y hy
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hxu, hyv, ← map_mul, ← map_mul]
  congr 1
  exact congrArg Subtype.val (mul_comm_of_mem_ker h hu hv)

end Main

theorem ggSUSixHSideInput_holds : GGSUSixHSideInput := by
  intro G _ _ f ψ hker
  exact ggCentOTwoPrime_three_facts (F := GaloisField 2 (2 * (f + 1))) (by omega)
    (CFSG.LieType.Universal.card_galoisField_two_mul 2 (f + 1) (by omega)) hker

end SUFacts

end CFSG.StandardType
