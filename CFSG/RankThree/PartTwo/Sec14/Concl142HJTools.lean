module

public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

section Small

theorem perm_three_conj_mul_ne : ∀ s t : Equiv.Perm (Fin 3), s ≠ 1 → s * s = 1 → t ≠ 1 →
    t * t * t = 1 → (t * s * t⁻¹ * s) * (t * s * t⁻¹ * s) ≠ 1 := by
  decide +kernel

theorem natCard_perm_fin_three : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem natCard_alternatingGroup_fin_four : Nat.card (alternatingGroup (Fin 4)) = 12 :=
  alternatingGroup.card_of_card_eq_four (by simp)

theorem card_dvd_two_of_not_three_dvd {Γ : Type*} [Group Γ] [Finite Γ] (hΓ : Nat.card Γ = 6)
    {K : Subgroup Γ} (hK : ¬ 3 ∣ Nat.card K) : Nat.card K ∣ 2 := by
  have h6 : Nat.card K ∣ 6 := hΓ ▸ Subgroup.card_subgroup_dvd_card K
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hle : Nat.card K ≤ 6 := Nat.le_of_dvd (by norm_num) h6
  interval_cases h : Nat.card K <;> simp_all

theorem perm_three_eq_bot_of_normalizer {K T : Subgroup (Equiv.Perm (Fin 3))}
    (hK : ¬ 3 ∣ Nat.card K) (hT : Nat.card T = 3)
    (hTK : T ≤ Subgroup.normalizer (K : Set (Equiv.Perm (Fin 3)))) : K = ⊥ := by
  have h2 : Nat.card K ∣ 2 := card_dvd_two_of_not_three_dvd natCard_perm_fin_three hK
  have hsq : ∀ k ∈ K, k * k = 1 := by
    intro k hk
    have h := pow_card_eq_one' (G := K) (x := ⟨k, hk⟩)
    obtain ⟨m, hm⟩ := h2
    have h' : (⟨k, hk⟩ : K) ^ 2 = 1 := by
      rw [show (2 : ℕ) = Nat.card K * m by omega, pow_mul, h, one_pow]
    have := congrArg Subtype.val h'
    simpa [sq] using this
  have hTne : T ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hT
    omega
  obtain ⟨⟨t, htT⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hTne
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have ht3 : t * t * t = 1 := by
    have h := pow_card_eq_one' (G := T) (x := ⟨t, htT⟩)
    rw [hT] at h
    have := congrArg Subtype.val h
    simpa [pow_succ, pow_two, mul_assoc] using this
  refine eq_bot_iff.mpr fun k hk => ?_
  rw [Subgroup.mem_bot]
  by_contra hk1
  have hconj : t * k * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hTK htT) k).mp hk
  exact perm_three_conj_mul_ne k t hk1 (hsq k hk) ht1' ht3 (hsq _ (mul_mem hconj hk))

theorem alternating_four_le_kleinFour {K : Subgroup (alternatingGroup (Fin 4))}
    (hK : ¬ 3 ∣ Nat.card K) : K ≤ alternatingGroup.kleinFour (Fin 4) := by
  have h4 : Nat.card (Fin 4) = 4 := by simp
  have : (alternatingGroup.kleinFour (Fin 4)).Normal := alternatingGroup.normal_kleinFour h4
  set N := alternatingGroup.kleinFour (Fin 4)
  have hN4 : Nat.card N = 4 := alternatingGroup.kleinFour_card_of_card_eq_four h4
  have hQ : Nat.card (alternatingGroup (Fin 4) ⧸ N) = 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [natCard_alternatingGroup_fin_four, hN4] at h
    omega
  have hdvd1 : Nat.card (K.map (QuotientGroup.mk' N)) ∣ Nat.card K :=
    Subgroup.card_map_dvd K _
  have hdvd2 : Nat.card (K.map (QuotientGroup.mk' N)) ∣ 3 :=
    hQ ▸ Subgroup.card_subgroup_dvd_card _
  have h1 : Nat.card (K.map (QuotientGroup.mk' N)) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd2 with h | h
    · exact h
    · exact absurd (h ▸ hdvd1) hK
  rw [Subgroup.card_eq_one, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
  exact h1

theorem perm_three_prod_alternating_four_le
    {U T : Subgroup (Equiv.Perm (Fin 3) × alternatingGroup (Fin 4))} (hU : ¬ 3 ∣ Nat.card U)
    (hT : Nat.card T = 9)
    (hTU : T ≤ Subgroup.normalizer (U : Set (Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)))) :
    U ≤ (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup.kleinFour (Fin 4)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set f := MonoidHom.fst (Equiv.Perm (Fin 3)) (alternatingGroup (Fin 4)) with hf
  set g := MonoidHom.snd (Equiv.Perm (Fin 3)) (alternatingGroup (Fin 4)) with hg
  have hT3 : IsPGroup 3 T := IsPGroup.of_card (n := 2) (by rw [hT]; norm_num)
  have hfT : Nat.card (T.map f) = 3 := by
    obtain ⟨k, hk⟩ := (hT3.map f).exists_card_eq
    have h6 : Nat.card (T.map f) ∣ 6 := natCard_perm_fin_three ▸ Subgroup.card_subgroup_dvd_card _
    have hk1 : k ≤ 1 := by
      by_contra hk1
      have : 3 ^ 2 ∣ 6 := (pow_dvd_pow 3 (by omega)).trans (hk ▸ h6)
      norm_num at this
    interval_cases k
    · exfalso
      have hbot : T.map f = ⊥ := Subgroup.card_eq_one.mp (by rw [hk, pow_zero])
      have hker : T ≤ f.ker := by rwa [Subgroup.map_eq_bot_iff] at hbot
      have h12 : Nat.card f.ker = 12 := by
        rw [hf, MonoidHom.ker_fst, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,
          Nat.card_prod, Subgroup.card_bot, Subgroup.card_top, one_mul,
          natCard_alternatingGroup_fin_four]
      have h9 : 9 ∣ 12 := hT ▸ h12 ▸ Subgroup.card_dvd_of_le hker
      norm_num at h9
    · rw [hk, pow_one]
  have hfU : U.map f = ⊥ := by
    refine perm_three_eq_bot_of_normalizer (fun h3 => hU (h3.trans (Subgroup.card_map_dvd U f)))
      hfT ((Subgroup.map_mono hTU).trans (Subgroup.le_normalizer_map f))
  have hU1 : U ≤ f.ker := by rwa [Subgroup.map_eq_bot_iff] at hfU
  have hgU : U.map g ≤ alternatingGroup.kleinFour (Fin 4) :=
    alternating_four_le_kleinFour fun h3 => hU (h3.trans (Subgroup.card_map_dvd U g))
  intro u hu
  refine Subgroup.mem_prod.mpr ⟨?_, hgU ⟨u, hu, rfl⟩⟩
  have := hU1 hu
  rw [MonoidHom.mem_ker] at this
  exact (Subgroup.mem_bot).mpr this

end Small

section J2

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem subgroupOf_le_normalizer_subgroupOf' {N E U : Subgroup X}
    (hEU : E ≤ Subgroup.normalizer (U : Set X)) :
    E.subgroupOf N ≤ Subgroup.normalizer ((U.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simpa using Subgroup.mem_normalizer_iff.mp (hEU (Subgroup.mem_subgroupOf.mp ha)) (h : X)

theorem j2_le_of_invariant (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) (P : Sylow 3 X) {E : Subgroup X}
    (hEP : E ≤ P) (hE9 : Nat.card E = 9) {b : X} (hbE : b ∈ E)
    (hbZ : b ∉ (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X))
    (hEb : E ≤ Subgroup.centralizer ({b} : Set X)) :
    ∃ W : Subgroup X, ¬ 3 ∣ Nat.card W ∧
      Subgroup.centralizer ({b} : Set X) ≤ Subgroup.normalizer (W : Set X) ∧
      ∀ U : Subgroup X, U ≤ Subgroup.centralizer ({b} : Set X) → ¬ 3 ∣ Nat.card U →
        E ≤ Subgroup.normalizer (U : Set X) → U ≤ W := by
  obtain ⟨-, -, -, h4, -⟩ := h415 X hX P _ rfl _ rfl
  obtain ⟨-, ⟨e⟩, -⟩ := h4 E ⟨hEP, hE9⟩ b hbE hbZ
  set N := Subgroup.normalizer (Subgroup.zpowers b : Set X) with hN
  have hCN : Subgroup.centralizer ({b} : Set X) ≤ N := by
    rw [hN, Subgroup.zpowers_eq_closure, ← Subgroup.centralizer_closure]
    exact Subgroup.centralizer_le_normalizer _
  have h4 : Nat.card (Fin 4) = 4 := by simp
  have : (alternatingGroup.kleinFour (Fin 4)).Normal := alternatingGroup.normal_kleinFour h4
  set V : Subgroup (Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) :=
    (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup.kleinFour (Fin 4)) with hV
  set W₀ : Subgroup ↥N := V.comap e.toMonoidHom with hW₀
  have hW₀n : W₀.Normal := Subgroup.Normal.comap inferInstance _
  refine ⟨W₀.map N.subtype, ?_, ?_, ?_⟩
  ·
    have hcard : Nat.card (W₀.map N.subtype) = 4 := by
      rw [Subgroup.card_map_of_injective N.subtype_injective, hW₀,
        ← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective,
        Subgroup.map_comap_eq_self_of_surjective e.surjective, hV,
        Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_bot, one_mul,
        alternatingGroup.kleinFour_card_of_card_eq_four h4]
    rw [hcard]
    norm_num
  ·
    have h := Subgroup.le_normalizer_map (H := W₀) N.subtype
    rw [Subgroup.normalizer_eq_top_iff.mpr hW₀n, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
    exact hCN.trans h
  ·
    intro U hU hU3 hEU
    have hUN : U ≤ N := hU.trans hCN
    have hEN : E ≤ N := hEb.trans hCN
    have hU' : ¬ 3 ∣ Nat.card ((U.subgroupOf N).map e.toMonoidHom) := by
      rwa [Subgroup.card_map_of_injective e.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUN).toEquiv]
    have hT : Nat.card ((E.subgroupOf N).map e.toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective e.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv, hE9]
    have hTU := (Subgroup.map_mono (subgroupOf_le_normalizer_subgroupOf' (N := N) hEU)).trans
      (Subgroup.le_normalizer_map e.toMonoidHom)
    have hle := perm_three_prod_alternating_four_le hU' hT hTU
    intro u hu
    refine ⟨⟨u, hUN hu⟩, ?_, rfl⟩
    exact hle ⟨⟨u, hUN hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩

end J2

end CFSG.RankThree.PartTwo.Sec14
