module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviCentralizerX
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR6Y

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Std CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint

local instance twistedE6PilotLeviCentralizerYNeZero : NeZero Tag.E6.rank := ⟨by decide⟩

local instance twistedE6PilotLeviCentralizerYNeZero' : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

section Weyl

@[expose] def negN0 : Fin Tag.E6.rank → ℤ := (![-1, -1, -2, -2, -1, 0] : Fin 6 → ℤ)

@[expose] def negN5 : Fin Tag.E6.rank → ℤ := (![0, -1, -1, -2, -2, -1] : Fin 6 → ℤ)

theorem candidates_D4 : ∀ β ∈ rootFinset .E6,
    (coPair .E6 1 β = 0 ∧ coPair .E6 2 β = -1 ∧ coPair .E6 3 β = 0 ∧ coPair .E6 4 β = 0 →
      β = Pi.single 0 1 ∨ β = negN0) ∧
    (coPair .E6 1 β = 0 ∧ coPair .E6 2 β = 0 ∧ coPair .E6 3 β = 0 ∧ coPair .E6 4 β = -1 →
      β = Pi.single 5 1 ∨ β = negN5) := by
  decide +kernel

theorem negN_values : negN0 0 = -1 ∧ negN5 0 = 0 ∧ (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) 0 = 0 ∧
    (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) 0 = 1 ∧
    iform (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) negN5 = 1 ∧ negN0 5 = 0 := by
  decide

theorem iform_single_values :
    iform (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) (Pi.single 1 1) = 0 ∧
    iform (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) (Pi.single 2 1) = -1 ∧
    iform (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) (Pi.single 3 1) = 0 ∧
    iform (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) (Pi.single 4 1) = 0 ∧
    iform (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) (Pi.single 1 1) = 0 ∧
    iform (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) (Pi.single 2 1) = 0 ∧
    iform (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) (Pi.single 3 1) = 0 ∧
    iform (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) (Pi.single 4 1) = -1 ∧
    iform (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) (Pi.single 5 1) = 0 := by
  decide

theorem psiW_eq (w : WeylGroup .E6) :
    psiW w = (w • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) 0 -
      (w • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ)) 0 + (w • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ)) 0 -
        (w • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) 0 := by
  rw [psiW]
  change ∑ j : Fin 6, classVec j * (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) 0 = _
  rw [Fin.sum_univ_six]
  simp only [classVec]
  simp
  rfl


theorem coPair_smul_of_smul_eq {w : WeylGroup .E6} {x y : Fin Tag.E6.rank → ℤ} {j : Fin Tag.E6.rank}
    (hy : w • y = Pi.single j 1) : coPair .E6 j (w • x) = iform x y := by
  rw [← EPilot.iform_single_eq_coPair (Or.inl rfl), ← hy, iform_smul]

theorem eq_one_of_smul_D4 {w : WeylGroup .E6}
    (h1 : w • (Pi.single 1 1 : Fin Tag.E6.rank → ℤ) = Pi.single 1 1)
    (h2 : w • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) = Pi.single 2 1)
    (h3 : w • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) = Pi.single 3 1)
    (h4 : w • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) = Pi.single 4 1) : w = 1 := by
  obtain ⟨v01, v02, v03, v04, v51, v52, v53, v54, v05⟩ := iform_single_values
  obtain ⟨n00, n50, s50, s00, i0N5, -⟩ := negN_values
  have hr0 := IsRoot.smul (isRoot_single Tag.E6 0) w
  have hr5 := IsRoot.smul (isRoot_single Tag.E6 5) w
  have hA0 := (candidates_D4 _ (mem_rootFinset.2 hr0)).1
    ⟨by rw [coPair_smul_of_smul_eq h1, v01], by rw [coPair_smul_of_smul_eq h2, v02],
      by rw [coPair_smul_of_smul_eq h3, v03], by rw [coPair_smul_of_smul_eq h4, v04]⟩
  have hA5 := (candidates_D4 _ (mem_rootFinset.2 hr5)).2
    ⟨by rw [coPair_smul_of_smul_eq h1, v51], by rw [coPair_smul_of_smul_eq h2, v52],
      by rw [coPair_smul_of_smul_eq h3, v53], by rw [coPair_smul_of_smul_eq h4, v54]⟩
  have hψ := psiW_emod w
  rw [psiW_eq, h2, h4] at hψ
  have hz2 : (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) 0 = 0 := by decide
  have hz4 : (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) 0 = 0 := by decide
  rw [hz2, hz4] at hψ
  have h05 : iform (w • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) (w • Pi.single 5 1) = 0 := by
    rw [iform_smul, v05]
  rcases hA0 with h0 | h0
  · rcases hA5 with h5 | h5
    · refine eq_one_of_forall_height_pos fun i => ?_
      fin_cases i
      · rw [show ((⟨0, by decide⟩ : Fin Tag.E6.rank)) = 0 from rfl, h0, height_single]; norm_num
      · rw [show ((⟨1, by decide⟩ : Fin Tag.E6.rank)) = 1 from rfl, h1, height_single]; norm_num
      · rw [show ((⟨2, by decide⟩ : Fin Tag.E6.rank)) = 2 from rfl, h2, height_single]; norm_num
      · rw [show ((⟨3, by decide⟩ : Fin Tag.E6.rank)) = 3 from rfl, h3, height_single]; norm_num
      · rw [show ((⟨4, by decide⟩ : Fin Tag.E6.rank)) = 4 from rfl, h4, height_single]; norm_num
      · rw [show ((⟨5, by decide⟩ : Fin Tag.E6.rank)) = 5 from rfl, h5, height_single]; norm_num
    · rw [h0, h5, i0N5] at h05
      exact absurd h05 one_ne_zero
  · exfalso
    rw [h0, n00] at hψ
    rcases hA5 with h5 | h5
    · rw [h5, s50] at hψ
      norm_num at hψ
    · rw [h5, n50] at hψ
      norm_num at hψ

theorem smul_single_five_of_swap_D4 {w : WeylGroup .E6}
    (h1 : w • (Pi.single 1 1 : Fin Tag.E6.rank → ℤ) = Pi.single 1 1)
    (h2 : w • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) = Pi.single 4 1)
    (h3 : w • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) = Pi.single 3 1)
    (h4 : w • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) = Pi.single 2 1) :
    w • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) = negN0 := by
  obtain ⟨v01, v02, v03, v04, v51, v52, v53, v54, -⟩ := iform_single_values
  obtain ⟨-, n50, s50, s00, -, -⟩ := negN_values
  have hr0 := IsRoot.smul (isRoot_single Tag.E6 0) w
  have hr5 := IsRoot.smul (isRoot_single Tag.E6 5) w
  have hA5 := (candidates_D4 _ (mem_rootFinset.2 hr5)).1
    ⟨by rw [coPair_smul_of_smul_eq h1, v51], by rw [coPair_smul_of_smul_eq h4, v54],
      by rw [coPair_smul_of_smul_eq h3, v53], by rw [coPair_smul_of_smul_eq h2, v52]⟩
  have hA0 := (candidates_D4 _ (mem_rootFinset.2 hr0)).2
    ⟨by rw [coPair_smul_of_smul_eq h1, v01], by rw [coPair_smul_of_smul_eq h4, v04],
      by rw [coPair_smul_of_smul_eq h3, v03], by rw [coPair_smul_of_smul_eq h2, v02]⟩
  have hψ := psiW_emod w
  rw [psiW_eq, h2, h4] at hψ
  have hz2 : (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) 0 = 0 := by decide
  have hz4 : (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) 0 = 0 := by decide
  rw [hz2, hz4] at hψ
  have hw0 : (w • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) 0 = 0 := by
    rcases hA0 with h0 | h0
    · rw [h0, s50]
    · rw [h0, n50]
  rw [hw0] at hψ
  rcases hA5 with h5 | h5
  · rw [h5, s00] at hψ
    norm_num at hψ
  · exact h5

end Weyl

section Core


variable {K : Type} [Field K]

theorem mem_setD_nodes : (1 : Fin TwistTag.E6.tag.rank) ∈ setD ∧ (2 : Fin TwistTag.E6.tag.rank) ∈ setD ∧
    (3 : Fin TwistTag.E6.tag.rank) ∈ setD ∧ (4 : Fin TwistTag.E6.tag.rank) ∈ setD :=
  ⟨Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl)), Or.inr (Or.inr (Or.inr rfl))⟩

theorem core_Y {f : ℕ} {k : Type} [Field k] [Algebra k K] (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {g : ModGL .E6 K} (hg : g ∈ adjointGroup .E6 K)
    (a : Fin Tag.E6.rank → Kˣ) (δ : K ≃+* K)
    (hfix : ∀ x : ModGL .E6 K, x ∈ omegaMinusLevi σ → g * (rootDiagUnit .E6 a *
      Units.map (entrywiseHom δ.toRingHom) x * (rootDiagUnit .E6 a)⁻¹) * g⁻¹ = x)
    (hW : (∀ c, δ c = c) ∨ ∀ c : kˣ,
      g * (rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom)
        (rootDiagUnit .E6 (d4CentralDiag (Units.map (algebraMap k K).toMonoidHom c)
          (Units.map (algebraMap k K).toMonoidHom c))) * (rootDiagUnit .E6 a)⁻¹) * g⁻¹ =
          rootDiagUnit .E6 (d4CentralDiag (Units.map (algebraMap k K).toMonoidHom c)
            (Units.map (algebraMap k K).toMonoidHom c))) :
    (∀ c, δ c = c) ∧ g * rootDiagUnit .E6 a ∈ d4CentralTorus K := by
  classical
  have hf : 1 ≤ f := by omega
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Finite K := finite_of_card hK
  have : CharP K 2 := charP_two_of_card hf hK
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hσσ : ∀ c, σ (σ c) = c := apply_apply_eq hK hσ
  have hL : omegaMinusLevi σ = subsystemGroup TwistTag.E6.tag K setD ⊓
      twistedFixedGroup TwistTag.E6 K σ := omegaMinusLevi_eq_of_card hf hK hσ
  have hq : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  obtain ⟨c₀, hc₀⟩ := F4Pilot.exists_three_le_orderOf hq
  set μ : Kˣ := Units.map (algebraMap k K).toMonoidHom c₀ with hμdef
  have hμ1 : μ ≠ 1 := by
    intro h1
    have e := orderOf_injective _ (Units.map_injective (algebraMap k K).injective) c₀
    rw [← hμdef, h1, orderOf_one] at e
    omega
  have hσμ : Units.map σ.toMonoidHom μ = μ :=
    Units.ext (E6GraphLevi.fixed_algebraMap (sigma_eq_pow_card hk hσ) (c₀ : k))
  obtain ⟨ω, hω⟩ := exists_apply_ne hf hK hσ
  have hω0 : ω ≠ 0 := fun h => hω (by rw [h, map_zero])
  have hσω0 : σ ω ≠ 0 := (map_ne_zero σ).2 hω0
  set ζ : Kˣ := Units.mk0 (σ ω * ω⁻¹) (mul_ne_zero hσω0 (inv_ne_zero hω0)) with hζdef
  have hσζ : Units.map σ.toMonoidHom ζ = ζ⁻¹ := by
    refine Units.ext ?_
    rw [Units.coe_map, Units.val_inv_eq_inv_val, hζdef, Units.val_mk0]
    change σ (σ ω * ω⁻¹) = (σ ω * ω⁻¹)⁻¹
    rw [map_mul, map_inv₀, hσσ, mul_inv, inv_inv, mul_comm]
  have hζ1 : ζ ≠ 1 := by
    intro h1
    apply hω
    have e := congrArg Units.val h1
    rw [hζdef, Units.val_mk0, Units.val_one, mul_inv_eq_one₀ hω0] at e
    exact e
  have hσζ' : Units.map σ.toMonoidHom ζ⁻¹ = ζ := by rw [map_inv, hσζ, inv_inv]
  set μ' : Kˣ := Units.map δ.toRingHom.toMonoidHom μ with hμ'def
  set ζ' : Kˣ := Units.map δ.toRingHom.toMonoidHom ζ with hζ'def
  have hδinj : Function.Injective (Units.map δ.toRingHom.toMonoidHom) :=
    Units.map_injective δ.injective
  have hμ'1 : μ' ≠ 1 := fun h => hμ1 (hδinj (by rw [← hμ'def, h, map_one]))
  have hζ'1 : ζ' ≠ 1 := fun h => hζ1 (hδinj (by rw [← hζ'def, h, map_one]))
  have hg1 : g ∈ toralCentralizer .E6 K 1 := by
    refine mem_toralCentralizer.2 ⟨hg, ?_⟩
    rw [rootDiagUnit_one]
    group
  obtain ⟨w, -, h, hh, u, hu, v, hv, hgdec⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors .E6 K 1).1 g hg1
  have huU : u ∈ posUnipotent .E6 K := rootSpan_mono Set.inter_subset_right hu
  have hvI : v ∈ rootSpan .E6 K (inversionSet w) := rootSpan_mono Set.inter_subset_right hv
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  have hconj : ∀ b : Fin Tag.E6.rank → Kˣ, rootDiagUnit .E6 b ∈ omegaMinusLevi σ →
      rootDiagUnit .E6 l * u * canonicalRep (coxeterSystem Tag.E6) K w * v *
          rootDiagUnit .E6 (fun i => Units.map δ.toRingHom.toMonoidHom (b i)) =
        rootDiagUnit .E6 b * (rootDiagUnit .E6 l * u * canonicalRep (coxeterSystem Tag.E6) K w * v) := by
    intro b hb
    have e := hfix _ hb
    rw [diagField_rootDiagUnit, hgdec] at e
    rw [← e]
    group
  have hρ1 : TwistTag.E6.perm 1 = 1 := by decide
  have hρ3 : TwistTag.E6.perm 3 = 3 := by decide
  have hT1 : rootDiagUnit .E6 (fun i => μ ^ Tag.E6.cartan 1 i) ∈ omegaMinusLevi σ := by
    rw [hL]
    have h := torusElt_mem_inf (t := TwistTag.E6) (K := K) (σ := σ) (A := setD)
      mem_setD_nodes.1 hρ1 hσμ
    rw [torusElt_eq_rootDiagUnit] at h
    exact h
  have hT3 : rootDiagUnit .E6 (fun i => μ ^ Tag.E6.cartan 3 i) ∈ omegaMinusLevi σ := by
    rw [hL]
    have h := torusElt_mem_inf (t := TwistTag.E6) (K := K) (σ := σ) (A := setD)
      mem_setD_nodes.2.2.1 hρ3 hσμ
    rw [torusElt_eq_rootDiagUnit] at h
    exact h
  have hP2 : ∀ {ν ν' : Kˣ}, Units.map σ.toMonoidHom ν = ν' → Units.map σ.toMonoidHom ν' = ν →
      rootDiagUnit .E6 (pairDiag 2 (rhoE6 2) ν ν') ∈ omegaMinusLevi σ := by
    intro ν ν' h1 h2'
    rw [hL]
    exact rootDiagUnit_pairDiag_mem_inf (t := TwistTag.E6) mem_setD_nodes.2.1
      (by rw [show TwistTag.E6.perm 2 = 4 by decide]; exact mem_setD_nodes.2.2.2) (perm_E6_perm 2) h1 h2'
  have e24 : rhoE6 2 = 4 := by decide
  obtain ⟨hu', hv', -⟩ := bruhat_factors_of_conj_list hh huU hvI
    [((fun i => μ ^ Tag.E6.cartan 1 i), (fun i => μ' ^ Tag.E6.cartan 1 i)),
      ((fun i => μ ^ Tag.E6.cartan 3 i), (fun i => μ' ^ Tag.E6.cartan 3 i)),
      (pairDiag 2 4 μ μ, pairDiag 2 4 μ' μ'), (pairDiag 2 4 ζ ζ⁻¹, pairDiag 2 4 ζ' ζ'⁻¹)] (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · refine ⟨by rw [← torusElt_eq_rootDiagUnit]; exact torusElt_mem_torusGroup _ _,
        by rw [← torusElt_eq_rootDiagUnit]; exact torusElt_mem_torusGroup _ _, ?_⟩
      have e := hconj _ hT1
      rw [map_cartanRow] at e
      exact e
    · refine ⟨by rw [← torusElt_eq_rootDiagUnit]; exact torusElt_mem_torusGroup _ _,
        by rw [← torusElt_eq_rootDiagUnit]; exact torusElt_mem_torusGroup _ _, ?_⟩
      have e := hconj _ hT3
      rw [map_cartanRow] at e
      exact e
    · refine ⟨rootDiagUnit_pairDiag_mem_torusGroup _ _ _ _,
        rootDiagUnit_pairDiag_mem_torusGroup _ _ _ _, ?_⟩
      have e := hconj _ (hP2 hσμ hσμ)
      rw [map_pairDiag, e24] at e
      exact e
    · refine ⟨rootDiagUnit_pairDiag_mem_torusGroup _ _ _ _,
        rootDiagUnit_pairDiag_mem_torusGroup _ _ _ _, ?_⟩
      have e := hconj _ (hP2 hσζ hσζ')
      rw [map_pairDiag, e24, map_inv] at e
      exact e)
  have hempty : ∀ {S : Set (Fin Tag.E6.rank → ℤ)}, (∀ α ∈ S, False) → rootSpan .E6 K S ≤ ⊥ :=
    fun hS => iSup₂_le fun α hα => absurd (hS α hα) id
  have hu1 : u = 1 := by
    refine (Subgroup.mem_bot).1 (hempty (fun α hα => ?_) hu')
    obtain ⟨⟨hαr, -⟩, hαL⟩ := hα
    exact false_of_rootChar_Y hμ1 hζ1 hαr (hαL _ (by simp)) (hαL _ (by simp)) (hαL _ (by simp))
      (hαL _ (by simp))
  have hv1 : v = 1 := by
    refine (Subgroup.mem_bot).1 (hempty (fun α hα => ?_) hv')
    obtain ⟨hαI, hαL⟩ := hα
    exact false_of_rootChar_Y hμ'1 hζ'1 (inversionSet_pos hαI).1 (hαL _ (by simp))
      (hαL _ (by simp)) (hαL _ (by simp)) (hαL _ (by simp))
  subst hu1 hv1
  have hm : ∀ x : ModGL .E6 K, x ∈ omegaMinusLevi σ →
      (rootDiagUnit .E6 l * canonicalRep (coxeterSystem Tag.E6) K w) *
          (rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom) x * (rootDiagUnit .E6 a)⁻¹) *
        (rootDiagUnit .E6 l * canonicalRep (coxeterSystem Tag.E6) K w)⁻¹ = x := by
    intro x hx
    have e := hfix x hx
    rw [hgdec, mul_one, mul_one] at e
    exact e
  have hroot : ∀ j : Fin Tag.E6.rank, (j = 1 ∨ j = 3) →
      w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1 ∧ (l j : K) * (a j : K) = 1 := by
    intro j hj
    have hjD : pinnedX .E6 K (Pi.single j 1) 1 ∈ omegaMinusLevi σ := by
      rw [hL]
      rcases hj with rfl | rfl
      · exact pinnedX_single_mem_inf (t := TwistTag.E6) (σ := σ) h2 (A := setD)
          mem_setD_nodes.1 hρ1 (map_one σ)
      · exact pinnedX_single_mem_inf (t := TwistTag.E6) (σ := σ) h2 (A := setD)
          mem_setD_nodes.2.2.1 hρ3 (map_one σ)
    have e := hm _ hjD
    rw [diagField_pinnedX a δ (isRoot_single _ j),
      conj_rootDiagUnit_canonicalRep_pinnedX h2 l w (isRoot_single _ j)] at e
    have hw : w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1 :=
      EPilot.eq_of_pinnedX_eq_pinnedX_of_pos (IsRoot.smul (isRoot_single _ j) w)
        (isRoot_single _ j) (by rw [height_single]; norm_num) one_ne_zero e
    rw [hw, EPilot.rootChar_single_eq, EPilot.rootChar_single_eq, map_one, mul_one] at e
    exact ⟨hw, pinnedX_injective .E6 K _ e⟩
  obtain ⟨hw1, hla1⟩ := hroot 1 (Or.inl rfl)
  obtain ⟨hw3, hla3⟩ := hroot 3 (Or.inr rfl)
  have hcase : ∀ c : K, c ≠ 0 →
      (w • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) = Pi.single 2 1 ∧
          w • (Pi.single (rhoE6 2) 1 : Fin Tag.E6.rank → ℤ) = Pi.single (rhoE6 2) 1 ∧
          (l 2 : K) * ((a 2 : K) * δ c) = c ∧
          (l (rhoE6 2) : K) * ((a (rhoE6 2) : K) * δ (σ c)) = σ c) ∨
        (w • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) = Pi.single (rhoE6 2) 1 ∧
          w • (Pi.single (rhoE6 2) 1 : Fin Tag.E6.rank → ℤ) = Pi.single 2 1 ∧
          (l (rhoE6 2) : K) * ((a 2 : K) * δ c) = σ c ∧
          (l 2 : K) * ((a (rhoE6 2) : K) * δ (σ c)) = c) := by
    intro c hc
    have hyD : pinnedX .E6 K (Pi.single 2 1) c * pinnedX .E6 K (Pi.single (rhoE6 2) 1) (σ c) ∈
        omegaMinusLevi σ := by
      rw [hL]
      have h := twistedE6PairX_single_mem_inf (K := K) hσσ (A := setD) (j := 2)
        mem_setD_nodes.2.1 (by rw [show TwistTag.E6.perm 2 = 4 by decide]; exact mem_setD_nodes.2.2.2) c
      have hpl : @permLattice TwistTag.E6.tag TwistTag.E6.perm
          (Pi.single 2 1 : Fin TwistTag.E6.tag.rank → ℤ) =
            (Pi.single (rhoE6 2) 1 : Fin Tag.E6.rank → ℤ) :=
        permLattice_single _ _
      rw [twistedE6PairX, hpl] at h
      exact h
    exact pair_cases σ l a δ (by decide) hc (hm _ hyD)
  have hs24 : (Pi.single (rhoE6 2) 1 : Fin Tag.E6.rank → ℤ) ≠ Pi.single 2 1 := by
    rw [e24]; exact fun h => absurd (E6Pilot.eq_of_single_eq_single_E6 h) (by decide)
  rcases hcase 1 one_ne_zero with ⟨hw2, hw4, hs2, hs4⟩ | ⟨hw2, hw4, hs2, hs4⟩
  ·
    rw [map_one, mul_one] at hs2
    rw [map_one, map_one, mul_one] at hs4
    have hδ1 : ∀ c, δ c = c := by
      intro c
      by_cases hc0 : c = 0
      · rw [hc0, map_zero]
      rcases hcase c hc0 with ⟨-, -, h3, -⟩ | ⟨h3, -, -, -⟩
      · calc δ c = ((l 2 : K) * (a 2 : K)) * δ c := by rw [hs2, one_mul]
          _ = c := by rw [mul_assoc]; exact h3
      · exact absurd (h3.symm.trans hw2) hs24
    refine ⟨hδ1, ?_⟩
    rw [e24] at hw4 hs4
    have hw1' : w = 1 := eq_one_of_smul_D4 hw1 hw2 hw3 hw4
    subst hw1'
    rw [hgdec, canonicalRep_one, mul_one, mul_one, mul_one, ← rootDiagUnit_mul]
    refine mem_d4CentralTorus.2 ⟨(l * a) 0, (l * a) 5, ?_⟩
    congr 1
    have hla : ∀ j : Fin Tag.E6.rank, (l j : K) * (a j : K) = 1 → (l * a) j = 1 := fun j h =>
      Units.ext (by rw [Pi.mul_apply, Units.val_mul, Units.val_one]; exact h)
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by revert i; decide
    have n10 : (1 : Fin Tag.E6.rank) ≠ 0 := by decide
    have n15 : (1 : Fin Tag.E6.rank) ≠ 5 := by decide
    have n20 : (2 : Fin Tag.E6.rank) ≠ 0 := by decide
    have n25 : (2 : Fin Tag.E6.rank) ≠ 5 := by decide
    have n30 : (3 : Fin Tag.E6.rank) ≠ 0 := by decide
    have n35 : (3 : Fin Tag.E6.rank) ≠ 5 := by decide
    have n40 : (4 : Fin Tag.E6.rank) ≠ 0 := by decide
    have n45 : (4 : Fin Tag.E6.rank) ≠ 5 := by decide
    have n50 : (5 : Fin Tag.E6.rank) ≠ 0 := by decide
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [d4CentralDiag, Ne.symm n50]
    · rw [hla _ hla1]; simp [d4CentralDiag, n10, n15]
    · rw [hla _ hs2]; simp [d4CentralDiag, n20, n25]
    · rw [hla _ hla3]; simp [d4CentralDiag, n30, n35]
    · rw [hla _ hs4]; simp [d4CentralDiag, n40, n45]
    · simp [d4CentralDiag, n50]
  ·
    exfalso
    rw [map_one, mul_one, map_one] at hs2
    have hδσ1 : ∀ c, δ c = σ c := by
      intro c
      by_cases hc0 : c = 0
      · rw [hc0, map_zero, map_zero]
      rcases hcase c hc0 with ⟨h3, -, -, -⟩ | ⟨-, -, h3, -⟩
      · exact absurd (h3.symm.trans hw2) (Ne.symm hs24)
      · calc δ c = ((l (rhoE6 2) : K) * (a 2 : K)) * δ c := by rw [hs2, one_mul]
          _ = σ c := by rw [mul_assoc]; exact h3
    rcases hW with hδ1 | hW
    · exact hω ((hδσ1 ω).symm.trans (hδ1 ω))
    rw [e24] at hw2 hw4
    have hw5 := smul_single_five_of_swap_D4 hw1 hw2 hw3 hw4
    have e := hW c₀
    have hδμ : Units.map δ.toRingHom.toMonoidHom μ = μ :=
      Units.ext ((hδσ1 μ).trans (congrArg Units.val hσμ))
    have hδb : (fun i => Units.map δ.toRingHom.toMonoidHom (d4CentralDiag μ μ i)) =
        d4CentralDiag μ μ := by
      have hδμv : δ (μ : K) = μ := (hδσ1 μ).trans (congrArg Units.val hσμ)
      funext i
      simp only [d4CentralDiag, Pi.mul_apply, map_mul, Pi.mulSingle_apply]
      split_ifs <;> (apply Units.ext; simp [hδμv])
    rw [diagField_rootDiagUnit, hδb, hgdec, mul_one, mul_one] at e
    have e' : rootDiagUnit .E6 (d4CentralDiag μ μ) =
        canonicalRep (coxeterSystem Tag.E6) K w * rootDiagUnit .E6 (d4CentralDiag μ μ) *
          (canonicalRep (coxeterSystem Tag.E6) K w)⁻¹ := by
      have e1 : canonicalRep (coxeterSystem Tag.E6) K w * rootDiagUnit .E6 (d4CentralDiag μ μ) *
          (canonicalRep (coxeterSystem Tag.E6) K w)⁻¹ =
            (rootDiagUnit .E6 l)⁻¹ * rootDiagUnit .E6 (d4CentralDiag μ μ) * rootDiagUnit .E6 l := by
        calc _ = (rootDiagUnit .E6 l)⁻¹ * ((rootDiagUnit .E6 l *
              canonicalRep (coxeterSystem Tag.E6) K w) * rootDiagUnit .E6 (d4CentralDiag μ μ) *
                (rootDiagUnit .E6 l * canonicalRep (coxeterSystem Tag.E6) K w)⁻¹) *
                  rootDiagUnit .E6 l := by group
          _ = _ := by rw [e]
      rw [e1, rootDiagUnit_inv, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
      congr 1
      rw [mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [rootDiagUnit_eq_conj_canonicalRep_iff] at e'
    have e5 := e' (Pi.single 5 1)
    obtain ⟨n00, -, s50, -, -, n05⟩ := negN_values
    have s55 : (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) 5 = 1 := by decide
    rw [hw5, rootChar_d4CentralDiag, rootChar_d4CentralDiag, n00, n05, s50, s55] at e5
    have hsq : μ ^ (2 : ℤ) = 1 := by
      have e6 : μ⁻¹ = μ := by simpa using e5
      rw [show (2 : ℤ) = 1 + 1 by norm_num, zpow_add, zpow_one]
      nth_rewrite 1 [← e6]
      exact inv_mul_cancel μ
    have := EPilot.eq_zero_of_zpow_eq_one_of_charTwo hμ1 (n := 2) (by norm_num) hsq
    norm_num at this

end Core

section Centralizer


variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem mem_d4CentralTorus_of_mem_centralizer_omegaMinusLevi (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {g : ModGL .E6 K} (hgA : g ∈ adjointGroup .E6 K)
    (hgD : ∀ x : ModGL .E6 K, x ∈ omegaMinusLevi σ → g * x = x * g) : g ∈ d4CentralTorus K := by
  obtain ⟨-, hgZ⟩ := core_Y (k := k) hf2 hk hK hσ hgA 1 (RingEquiv.refl K) (fun x hx => by
    have e1 : Units.map (entrywiseHom (RingEquiv.refl K).toRingHom) x = x :=
      Units.ext (entrywise_id _)
    rw [rootDiagUnit_one, e1, one_mul, inv_one, mul_one, hgD x hx, mul_inv_cancel_right])
    (Or.inl fun _ => rfl)
  rwa [rootDiagUnit_one, mul_one] at hgZ

theorem centralizer_omegaMinusLevi_inf_C0_eq (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    centralizer (omegaMinusLevi σ : Set (ModGL TwistTag.E6.tag K)) ⊓
        graphFixedRootGroup TwistTag.E6 K σ = w1Complement σ ∧
      ¬ 2 ∣ Nat.card (w1Complement σ) ∧
      w1Complement σ ≤ centralizer (w1Complement σ : Set (ModGL TwistTag.E6.tag K)) ∧
      shortRootTorus (algebraMap k K) ≤ w1Complement σ := by
  obtain ⟨-, hYc, -, hodd, hW1⟩ := centralizer_w1Torus_inf_eq hf2 hk hK hσ
  refine ⟨le_antisymm (fun g hg => ?_) (le_inf hYc (w1Complement_le_C0 σ)), hodd, ?_, hW1⟩
  · obtain ⟨hgc, hgC⟩ := mem_inf.1 hg
    have hgA : g ∈ adjointGroup TwistTag.E6.tag K := (graphFixedRootGroup_le _ _ _ hgC).1
    exact ⟨mem_d4CentralTorus_of_mem_centralizer_omegaMinusLevi (k := k) (g := g) hf2 hk hK hσ hgA
      fun x hx => (mem_centralizer_iff.1 hgc x hx).symm, hgC⟩
  · intro z hz
    rw [mem_centralizer_iff]
    intro z' hz'
    obtain ⟨μ, ν, rfl⟩ := mem_d4CentralTorus.1 (mem_inf.1 hz).1
    obtain ⟨μ', ν', rfl⟩ := mem_d4CentralTorus.1 (mem_inf.1 hz').1
    change rootDiagUnit .E6 (d4CentralDiag μ' ν') * rootDiagUnit .E6 (d4CentralDiag μ ν) =
      rootDiagUnit .E6 (d4CentralDiag μ ν) * rootDiagUnit .E6 (d4CentralDiag μ' ν')
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

end Centralizer

end CFSG.SeitzReduction.TwistedE6Pilot
