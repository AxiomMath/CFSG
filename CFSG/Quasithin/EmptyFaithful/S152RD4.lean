module

public import CFSG.Quasithin.EmptyFaithful.S152RDef
public import CFSG.Quasithin.EmptyFaithful.S152RSL2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Triality
public import CFSG.LieType.BorelTits.Twisted

public section

namespace CFSG.Quasithin

open CFSG.LieType.Chevalley CFSG.QuasithinUnique.Setup.X6 CFSG.LieType.BorelTits CFSG.Blueprint
  CFSG.Blueprint.Chevalley
open scoped Pointwise

section D4

theorem set_foldedRank_D4_cases (J : Set (Fin TwistTag.D4.foldedTag.rank)) :
    J = ∅ ∨ J = {⟨0, by decide⟩} ∨ J = {⟨1, by decide⟩} ∨ J = Set.univ := by
  have hne : (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) ≠ ⟨1, by decide⟩ := by decide
  by_cases h0 : (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) ∈ J <;>
    by_cases h1 : (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) ∈ J
  · right; right; right
    exact Set.eq_univ_of_forall fun a => by
      rcases foldedRank_D4_cases a with rfl | rfl <;> assumption
  · right; left
    ext a
    rcases foldedRank_D4_cases a with rfl | rfl
    · simp [h0]
    · simp [h1, hne.symm]
  · right; right; left
    ext a
    rcases foldedRank_D4_cases a with rfl | rfl
    · simp [h0, hne]
    · simp [h1]
  · left
    ext a
    rcases foldedRank_D4_cases a with rfl | rfl
    · simp [h0]
    · simp [h1]


variable {K : Type} [Field K] [Finite K]

theorem not_three_dvd_card_graphFixedRootBorel_d4 (hK : Nat.card K = 8) (σ : K ≃+* K) :
    ¬ 3 ∣ Nat.card (graphFixedRootBorel TwistTag.D4 K σ.toRingHom) := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    (k := 3) Nat.prime_two (by norm_num) (by rw [hK]; norm_num)
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(graphFixedRootBorel TwistTag.D4 K σ.toRingHom)) 3 h3
  have hb3 : (b : ModGL TwistTag.D4.tag K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← hb, pow_orderOf_eq_one, Subgroup.coe_one]
  have hpow := pow_card_sub_one_mem_graphFixedPosUnipotent σ.surjective b.2
  have hb7 : (b : ModGL TwistTag.D4.tag K) ^ (Nat.card K - 1) = b := by
    rw [hK, show 8 - 1 = 3 * 2 + 1 from rfl, pow_succ, pow_mul, hb3, one_pow, one_mul]
  rw [hb7] at hpow
  obtain ⟨n, hn⟩ := isPGroup_posUnipotent 2 TwistTag.D4.tag (K := K)
    ⟨b, (inf_le_left : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ _) hpow⟩
  have h1 : (b : ModGL TwistTag.D4.tag K) ^ 2 ^ n = 1 := by
    simpa using congrArg Subtype.val hn
  have h2 : orderOf (b : ModGL TwistTag.D4.tag K) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h1
  rw [Subgroup.orderOf_coe, hb] at h2
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2) (by norm_num)

theorem card_graphFixedParabolic_singleton_d4 (σ : K ≃+* K) (a : Fin TwistTag.D4.foldedTag.rank) :
    Nat.card (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}) =
      Nat.card (graphFixedRootBorel TwistTag.D4 K σ.toRingHom) *
        (1 + Nat.card (orbitField TwistTag.D4 K σ.toRingHom a)) := by
  have h := relIndex_graphFixedParabolic_singleton (t := TwistTag.D4) σ a
  have hBP := graphFixedRootBorel_le_graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}
  have h2 := Subgroup.relIndex_mul_card (graphFixedRootBorel TwistTag.D4 K σ.toRingHom)
    (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a})
  rw [inf_eq_left.2 hBP, h] at h2
  rw [← h2]
  ring

theorem false_of_E9_le_overgroup_graphFixedRootBorel_d4 (hK : Nat.card K = 8) (σ : K ≃+* K)
    (hL₀ : Nat.card (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩) = 8)
    (hL₁ : Nat.card (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) = 2)
    {A : Subgroup (ModGL TwistTag.D4.tag K)}
    (hB : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤ A)
    (hA : A ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hAtop : A ≠ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    {E : Subgroup (ModGL TwistTag.D4.tag K)} (hEA : E ≤ A) (hE9 : Nat.card E = 9)
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) : False := by
  have h3B := not_three_dvd_card_graphFixedRootBorel_d4 hK σ
  obtain ⟨hAJ, -⟩ := fixed_Borel_overgroup_classification TwistTag.D4 K σ A hB hA
  obtain ⟨-, -, -, -, hP0, hPuniv⟩ := fixed_standard_parabolic_cells TwistTag.D4 K σ
  have hE9A : 9 ∣ Nat.card A := hE9 ▸ Subgroup.card_dvd_of_le hEA
  rcases set_foldedRank_D4_cases {a | canonicalRep (coxeterSystem TwistTag.D4.tag) K
      (TwistTag.D4.orbitReflection a) ∈ A} with hJ | hJ | hJ | hJ
  · rw [hJ, hP0] at hAJ
    rw [hAJ] at hE9A
    exact h3B (Nat.dvd_trans (by norm_num : 3 ∣ 9) hE9A)
  · rw [hJ] at hAJ
    have hc := card_graphFixedParabolic_singleton_d4 σ ⟨0, by decide⟩
    rw [hL₀] at hc
    have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
    obtain ⟨R, -, -, -, -, -, hRrange, -, hker, -⟩ :=
      exceptional_fixed_rank_one_central_image TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩
    have hchar : CharP ↥(orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩) 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic (k := 3)
        Nat.prime_two (by norm_num) hL₀
    have hRinj : Function.Injective R := by
      rw [injective_iff_map_eq_one]
      intro g hg
      obtain ⟨l, hl2, hgl⟩ := hker g (MonoidHom.mem_ker.2 hg)
      have hl1 : (l : ↥(orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩)) = 1 := by
        have h2 : (2 : ↥(orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩)) = 0 :=
          CharTwo.two_eq_zero
        have h3 : ((l : ↥(orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩)) - 1) ^ 2 = 0 := by
          linear_combination hl2 +
            (1 - (l : ↥(orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩))) * h2
        exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3)
      apply Subtype.ext
      rw [hgl, hl1, one_smul]
      rfl
    have hRA : R.range ≤ A := by
      rw [hRrange, Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact hB (graphFixedPosUnipotent_le_graphFixedRootBorel
          (orbitX_mem_graphFixedPosUnipotent TwistTag.D4 σ.toRingHom ⟨0, by decide⟩ c))
      · rw [hAJ]
        exact orbitY_mem_graphFixedParabolic ⟨0, by decide⟩ c
    obtain ⟨g9, hg9⟩ := exists_orderOf_nine_specialLinearGroup
      (F := ↥(orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩)) hL₀
    have hRg : R g9 ∈ A := hRA ⟨g9, rfl⟩
    have hord : orderOf (⟨R g9, hRg⟩ : ↥A) = 9 := by
      rw [← Subgroup.orderOf_coe]
      change orderOf (R g9) = 9
      rw [orderOf_injective R hRinj g9, hg9]
    have hcardA : Nat.card A = 9 * Nat.card (graphFixedRootBorel TwistTag.D4 K σ.toRingHom) := by
      rw [hAJ, hc]
      ring
    refine false_of_orderOf_nine_of_card_nine (Q := ↥A) hcardA h3B hord (E := E.subgroupOf A) ?_ ?_
    · rw [← hE9]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEA).toEquiv
    · intro x hx
      have := hE3 (x : ModGL TwistTag.D4.tag K) (Subgroup.mem_subgroupOf.1 hx)
      exact Subtype.ext (by simpa using this)
  · rw [hJ] at hAJ
    have hc := card_graphFixedParabolic_singleton_d4 σ ⟨1, by decide⟩
    rw [hL₁] at hc
    rw [hAJ, hc] at hE9A
    apply h3B
    omega
  · rw [hJ, hPuniv] at hAJ
    exact hAtop hAJ

theorem exists_standard_sylow_d4 (hK : Nat.card K = 8) (σ : K ≃+* K) :
    ∃ U : Sylow 2 ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      Subgroup.normalizer
          ((U : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
            Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) =
        (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    (k := 3) Nat.prime_two (by norm_num) (by rw [hK]; norm_num)
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hBnorm := (fixed_Borel_self_normalizers TwistTag.D4 K σ w₀ hw₀).2.2.2.2.2.2.1
  refine ⟨PU, ?_⟩
  rw [hPU, normalizer_subgroupOf_eq' hUC, hBnorm]

theorem false_of_E9_le_overgroup_normalizer_sylow_d4 (hK : Nat.card K = 8) (σ : K ≃+* K)
    (hL₀ : Nat.card (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩) = 8)
    (hL₁ : Nat.card (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) = 2)
    (S : Sylow 2 ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    {P : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hPtop : P ≠ ⊤)
    (hSP : Subgroup.normalizer
      ((S : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≤ P)
    {E : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hEP : E ≤ P)
    (hE9 : Nat.card E = 9) (hE3 : ∀ x ∈ E, x ^ 3 = 1) : False := by
  obtain ⟨U, hU⟩ := exists_standard_sylow_d4 hK σ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) U S
  set φ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≃*
      ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := MulAut.conj g⁻¹ with hφ
  have hSU : (S : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.toMonoidHom =
      (U : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    have h1 : ((g • U : Sylow 2 ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) =
        MulAut.conj g • (U : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
      Sylow.coe_subgroup_smul
    rw [hg] at h1
    ext x
    rw [Subgroup.mem_map_equiv, h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp only [hφ, MulAut.conj_symm_apply, MulAut.conj_inv_apply, inv_inv, MulAut.smul_def]
    have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [this]
  have hNU : Subgroup.normalizer ((U : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
      Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≤ P.map φ.toMonoidHom := by
    have h2 : (Subgroup.normalizer
        ((S : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))).map φ.toMonoidHom =
        Subgroup.normalizer
          (((S : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.toMonoidHom :
            Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
              Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
      Subgroup.map_equiv_normalizer_eq _ φ
    rw [hSU] at h2
    rw [← h2]
    exact Subgroup.map_mono hSP
  have hBC : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedRootBorel_le TwistTag.D4 K σ.toRingHom
  have hBP : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤
      (P.map φ.toMonoidHom).map (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hBC]
    exact Subgroup.map_mono (hU ▸ hNU)
  have hPC : (P.map φ.toMonoidHom).map (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := Subgroup.map_subtype_le _
  have hPtop' : (P.map φ.toMonoidHom).map
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype ≠
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    intro h
    apply hPtop
    have hP'top : P.map φ.toMonoidHom = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have : (y : ModGL TwistTag.D4.tag K) ∈ (P.map φ.toMonoidHom).map
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype := by
        rw [h]
        exact y.2
      obtain ⟨z, hz, hzy⟩ := this
      have : z = y := Subtype.ext hzy
      rwa [this] at hz
    rw [eq_top_iff]
    intro x _
    have hx : φ x ∈ P.map φ.toMonoidHom := by rw [hP'top]; trivial
    have := (Subgroup.mem_map_equiv (f := φ)).1 hx
    rwa [MulEquiv.symm_apply_apply] at this
  have hE'9 : Nat.card (E.map φ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective φ.injective, hE9]
  have hE'3 : ∀ x ∈ E.map φ.toMonoidHom, x ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    change φ y ^ 3 = 1
    rw [← map_pow, hE3 y hy, map_one]
  refine false_of_E9_le_overgroup_graphFixedRootBorel_d4 hK σ hL₀ hL₁
    (A := (P.map φ.toMonoidHom).map (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype)
    hBP hPC hPtop'
    (E := (E.map φ.toMonoidHom).map (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype)
    (Subgroup.map_mono (Subgroup.map_mono hEP)) ?_ ?_
  · rw [Subgroup.card_map_of_injective (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective,
      hE'9]
  · rintro _ ⟨y, hy, rfl⟩
    have h3 := hE'3 y hy
    change (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype y ^ 3 = 1
    rw [← map_pow, h3, map_one]

end D4

theorem noE9CentralizedByInvolution_of_trialityD4_two
    {X : Type} [Group X] [Finite X]
    (hX : ChevalleyExceptionalModel X .trialityD4 2 1) : NoE9CentralizedByInvolution X := by
  obtain ⟨hf, K, hFld, hFin, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model hX
  have hK8 : Nat.card K = 8 := by norm_num at hK; exact hK
  obtain ⟨σ', hσ', -, hcard', -, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two (le_refl 1) K hK
  have hσσ' : σ = σ' := RingEquiv.ext fun c => (hσ c).trans (hσ' c).symm
  subst hσσ'
  have hL₀ : Nat.card (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩) = 8 := by
    rw [hcard', card_orbit_D4.1]
    norm_num
  have hL₁ : Nat.card (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) = 2 := by
    rw [hcard', card_orbit_D4.2]
    norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBT : Holds X 2 := holds_of_chevalleyExceptionalModel hX
  have hBT' := hBT.of_mulEquiv e
  refine NoE9CentralizedByInvolution.of_mulEquiv e ?_
  intro l hl2 hl1 E hEl hE9 hE3
  have hord : orderOf l = 2 := orderOf_eq_prime (by rw [pow_two]; exact hl2) hl1
  have hUbot : Subgroup.zpowers l ≠ ⊥ := by
    intro hb
    apply hl1
    have : l ∈ Subgroup.zpowers l := Subgroup.mem_zpowers l
    rw [hb, Subgroup.mem_bot] at this
    exact this
  have hUp : IsPGroup 2 (Subgroup.zpowers l) := by
    have hc : Nat.card (Subgroup.zpowers l) = 2 := by rw [Nat.card_zpowers, hord]
    exact IsPGroup.of_card (n := 1) (by rw [hc]; norm_num)
  obtain ⟨S, P, hPtop, hN, -, -, hSP⟩ := hBT' _ hUbot hUp
  have hEP : E ≤ P := fun x hx => hN (centralizer_singleton_le_normalizer_zpowers l (hEl hx))
  exact false_of_E9_le_overgroup_normalizer_sylow_d4 hK8 σ hL₀ hL₁ S hPtop hSP hEP hE9 hE3

end CFSG.Quasithin
