module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviCentralizerY
public import CFSG.Mathlib.Decide.Bounded
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp

public section

namespace CFSG.StandardType.LieKnownR2.TwE6

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Std CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.SeitzReduction CFSG.SeitzReduction.TwistedE6Pilot

local instance : NeZero Tag.E6.rank := ⟨by decide⟩
local instance : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

@[expose] def twE6ShortCoreRoots : Set (Fin Tag.E6.rank → ℤ) :=
  {(![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ),
    (![0, 0, 1, 1, 1, 0] : Fin 6 → ℤ)}

open scoped CFSG.Decide.Bounded in
private theorem l10se2a_candidates :
    ∀ ρ ∈ rootFinset .E6,
      coPair .E6 1 ρ = 0 ∧ coPair .E6 3 ρ = -1 ∧
        iform ρ (Pi.single 2 1 + Pi.single 4 1 : Fin Tag.E6.rank → ℤ) = 2 →
      ρ = Pi.single 2 1 ∨ ρ = Pi.single 4 1 ∨
        ρ = (Pi.single 0 1 + Pi.single 1 1 + 2 • Pi.single 2 1 + 2 • Pi.single 3 1 +
          2 • Pi.single 4 1 + Pi.single 5 1 : Fin Tag.E6.rank → ℤ) ∨
        ρ = (-(Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1 + 2 • Pi.single 3 1 +
          Pi.single 4 1 + Pi.single 5 1) : Fin Tag.E6.rank → ℤ) := by decide +kernel

private def l10se2a_e1 : Fin Tag.E6.rank → ℤ := ![0, 1, 0, 0, 0, 0]
private def l10se2a_e3 : Fin Tag.E6.rank → ℤ := ![0, 0, 0, 1, 0, 0]
private def l10se2a_r : Fin Tag.E6.rank → ℤ := ![0, 0, 1, 1, 1, 0]

open scoped CFSG.Decide.Bounded in
private theorem l10se2a_shortRoots_data :
    l10se2a_e1 ∈ rootFinset .E6 ∧ l10se2a_e3 ∈ rootFinset .E6 ∧ l10se2a_r ∈ rootFinset .E6 ∧
    0 < height (τ := Tag.E6) l10se2a_e1 ∧ 0 < height (τ := Tag.E6) l10se2a_e3 ∧
    0 < height (τ := Tag.E6) l10se2a_r := by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem core_shortRoot
    {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K] (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {g : ModGL .E6 K} (hg : g ∈ adjointGroup .E6 K)
    (a : Fin Tag.E6.rank → Kˣ) (δ : K ≃+* K)
    (hT : ∀ x : ModGL .E6 K, x ∈ omegaMinusLevi σ → x ∈ torusGroup TwistTag.E6.tag K →
      g * (rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom) x *
        (rootDiagUnit .E6 a)⁻¹) * g⁻¹ = x)
    (hW : ∀ c : kˣ,
      g * (rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom)
        (rootDiagUnit .E6 (d4CentralDiag (Units.map (algebraMap k K).toMonoidHom c)
          (Units.map (algebraMap k K).toMonoidHom c))) * (rootDiagUnit .E6 a)⁻¹) * g⁻¹ =
          rootDiagUnit .E6 (d4CentralDiag (Units.map (algebraMap k K).toMonoidHom c)
            (Units.map (algebraMap k K).toMonoidHom c)))
    (hR : ∀ γ ∈ twE6ShortCoreRoots,
      g * (rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom) (pinnedX .E6 K γ 1) *
        (rootDiagUnit .E6 a)⁻¹) * g⁻¹ = pinnedX .E6 K γ 1) :
    (∀ c, δ c = c) ∧ ∃ b : Fin Tag.E6.rank → Kˣ, g * rootDiagUnit .E6 a = rootDiagUnit .E6 b := by
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
      rootDiagUnit .E6 b ∈ torusGroup TwistTag.E6.tag K →
      rootDiagUnit .E6 l * u * canonicalRep (coxeterSystem Tag.E6) K w * v *
          rootDiagUnit .E6 (fun i => Units.map δ.toRingHom.toMonoidHom (b i)) =
        rootDiagUnit .E6 b *
          (rootDiagUnit .E6 l * u * canonicalRep (coxeterSystem Tag.E6) K w * v) := by
    intro b hb hbT
    have e := hT _ hb hbT
    rw [diagField_rootDiagUnit, hgdec] at e
    rw [← e]
    group
  have hT1 : rootDiagUnit .E6 (fun i => μ ^ Tag.E6.cartan 1 i) ∈ omegaMinusLevi σ := by
    rw [hL]
    have h := torusElt_mem_inf (t := TwistTag.E6) (K := K) (σ := σ) (A := setD)
      mem_setD_nodes.1 (by decide) hσμ
    rw [torusElt_eq_rootDiagUnit] at h
    exact h
  have hT3 : rootDiagUnit .E6 (fun i => μ ^ Tag.E6.cartan 3 i) ∈ omegaMinusLevi σ := by
    rw [hL]
    have h := torusElt_mem_inf (t := TwistTag.E6) (K := K) (σ := σ) (A := setD)
      mem_setD_nodes.2.2.1 (by decide) hσμ
    rw [torusElt_eq_rootDiagUnit] at h
    exact h
  have hP2 : ∀ {ν ν' : Kˣ}, Units.map σ.toMonoidHom ν = ν' → Units.map σ.toMonoidHom ν' = ν →
      rootDiagUnit .E6 (pairDiag 2 (TwistedE6Pilot.rhoE6 2) ν ν') ∈ omegaMinusLevi σ := by
    intro ν ν' h1 h2'
    rw [hL]
    exact rootDiagUnit_pairDiag_mem_inf (t := TwistTag.E6) mem_setD_nodes.2.1
      (by rw [show TwistTag.E6.perm 2 = 4 by decide]; exact mem_setD_nodes.2.2.2)
      (perm_E6_perm 2) h1 h2'
  have e24 : TwistedE6Pilot.rhoE6 2 = 4 := by decide
  obtain ⟨hu', hv', -⟩ := bruhat_factors_of_conj_list hh huU hvI
    [((fun i => μ ^ Tag.E6.cartan 1 i), (fun i => μ' ^ Tag.E6.cartan 1 i)),
      ((fun i => μ ^ Tag.E6.cartan 3 i), (fun i => μ' ^ Tag.E6.cartan 3 i)),
      (pairDiag 2 4 μ μ, pairDiag 2 4 μ' μ'), (pairDiag 2 4 ζ ζ⁻¹, pairDiag 2 4 ζ' ζ'⁻¹)] (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · refine ⟨by rw [← torusElt_eq_rootDiagUnit]; exact torusElt_mem_torusGroup _ _,
        by rw [← torusElt_eq_rootDiagUnit]; exact torusElt_mem_torusGroup _ _, ?_⟩
      have e := hconj _ hT1 (by rw [← torusElt_eq_rootDiagUnit]; exact torusElt_mem_torusGroup _ _)
      rw [map_cartanRow] at e
      exact e
    · refine ⟨by rw [← torusElt_eq_rootDiagUnit]; exact torusElt_mem_torusGroup _ _,
        by rw [← torusElt_eq_rootDiagUnit]; exact torusElt_mem_torusGroup _ _, ?_⟩
      have e := hconj _ hT3 (by rw [← torusElt_eq_rootDiagUnit]; exact torusElt_mem_torusGroup _ _)
      rw [map_cartanRow] at e
      exact e
    · refine ⟨rootDiagUnit_pairDiag_mem_torusGroup _ _ _ _,
        rootDiagUnit_pairDiag_mem_torusGroup _ _ _ _, ?_⟩
      have e := hconj _ (hP2 hσμ hσμ) (rootDiagUnit_pairDiag_mem_torusGroup _ _ _ _)
      rw [map_pairDiag, e24] at e
      exact e
    · refine ⟨rootDiagUnit_pairDiag_mem_torusGroup _ _ _ _,
        rootDiagUnit_pairDiag_mem_torusGroup _ _ _ _, ?_⟩
      have e := hconj _ (hP2 hσζ hσζ') (rootDiagUnit_pairDiag_mem_torusGroup _ _ _ _)
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
  have hm : ∀ x : ModGL .E6 K, x ∈ omegaMinusLevi σ → x ∈ torusGroup TwistTag.E6.tag K →
      (rootDiagUnit .E6 l * canonicalRep (coxeterSystem Tag.E6) K w) *
          (rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom) x *
            (rootDiagUnit .E6 a)⁻¹) *
        (rootDiagUnit .E6 l * canonicalRep (coxeterSystem Tag.E6) K w)⁻¹ = x := by
    intro x hx hxT
    have e := hT x hx hxT
    rw [hgdec, mul_one, mul_one] at e
    exact e
  have he1 : l10se2a_e1 = (Pi.single 1 1 : Fin Tag.E6.rank → ℤ) := by funext i; fin_cases i <;> rfl
  have he3 : l10se2a_e3 = (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) := by funext i; fin_cases i <;> rfl
  have her : l10se2a_r = (Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1 : Fin Tag.E6.rank → ℤ) := by
    funext i; fin_cases i <;> rfl
  have hm1 : l10se2a_e1 ∈ twE6ShortCoreRoots := Or.inl rfl
  have hm3 : l10se2a_e3 ∈ twE6ShortCoreRoots := Or.inr (Or.inl rfl)
  have hmr : l10se2a_r ∈ twE6ShortCoreRoots := Or.inr (Or.inr rfl)
  have hrootAt : ∀ γ ∈ twE6ShortCoreRoots, IsRoot .E6 γ → 0 < height γ → w • γ = γ := by
    intro γ hγm hγ hγp
    have e := hR γ hγm
    rw [hgdec, mul_one, mul_one] at e
    rw [diagField_pinnedX a δ hγ, conj_rootDiagUnit_canonicalRep_pinnedX h2 l w hγ] at e
    exact EPilot.eq_of_pinnedX_eq_pinnedX_of_pos (IsRoot.smul hγ w) hγ hγp one_ne_zero e
  obtain ⟨hr1, hr3, hrr, hh1, hh3, hhr⟩ := l10se2a_shortRoots_data
  have hw1 : w • (Pi.single 1 1 : Fin Tag.E6.rank → ℤ) = Pi.single 1 1 := by
    have h := hrootAt _ hm1 (mem_rootFinset.1 hr1) hh1
    rwa [he1] at h
  have hw3 : w • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) = Pi.single 3 1 := by
    have h := hrootAt _ hm3 (mem_rootFinset.1 hr3) hh3
    rwa [he3] at h
  have hwr : w • (Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1 : Fin Tag.E6.rank → ℤ) =
      Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1 := by
    have h := hrootAt _ hmr (mem_rootFinset.1 hrr) hhr
    rwa [her] at h
  have hw24 : w • (Pi.single 2 1 + Pi.single 4 1 : Fin Tag.E6.rank → ℤ) =
      Pi.single 2 1 + Pi.single 4 1 := by
    have hsplit : w • (Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1 : Fin Tag.E6.rank → ℤ) =
        w • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) +
          w • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) +
            w • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) := by rw [smul_add, smul_add]
    have hsum : w • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) +
          w • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) +
            w • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) =
        (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) + Pi.single 3 1 + Pi.single 4 1 :=
      hsplit ▸ hwr
    have hcancel : w • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) +
          w • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) =
        (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) + Pi.single 4 1 := by
      have hsum' : w • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) +
            (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) +
              w • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) =
          (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) + Pi.single 3 1 + Pi.single 4 1 := by
        have h := hsum
        rwa [hw3] at h
      have h1 : (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) +
            (w • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) +
              w • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ)) =
          (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) +
            ((Pi.single 2 1 : Fin Tag.E6.rank → ℤ) + Pi.single 4 1) := by
        calc (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) +
              (w • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) +
                w • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ))
            = w • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) +
                (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) +
                  w • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) := by abel
          _ = (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) + Pi.single 3 1 + Pi.single 4 1 := hsum'
          _ = (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) +
                ((Pi.single 2 1 : Fin Tag.E6.rank → ℤ) + Pi.single 4 1) := by abel
      exact add_left_cancel h1
    rw [smul_add]
    exact hcancel
  have hρmem : w • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) ∈ rootFinset .E6 :=
    mem_rootFinset.2 (IsRoot.smul (isRoot_single .E6 2) w)
  have hco1 : coPair .E6 1 (w • Pi.single 2 1) = 0 := by
    rw [coPair_smul_of_smul_eq (x := Pi.single 2 1) (y := Pi.single 1 1) (j := 1) hw1,
      EPilot.iform_single_eq_coPair (Or.inl rfl)]
    decide +kernel
  have hco3 : coPair .E6 3 (w • Pi.single 2 1) = -1 := by
    rw [coPair_smul_of_smul_eq (x := Pi.single 2 1) (y := Pi.single 3 1) (j := 3) hw3,
      EPilot.iform_single_eq_coPair (Or.inl rfl)]
    decide +kernel
  have hif : iform (w • Pi.single 2 1)
      (Pi.single 2 1 + Pi.single 4 1 : Fin Tag.E6.rank → ℤ) = 2 := by
    have h := iform_smul w (Pi.single 2 1) (Pi.single 2 1 + Pi.single 4 1)
    rw [hw24] at h
    rw [h, iform_add_right, EPilot.iform_single_eq_coPair (Or.inl rfl),
      EPilot.iform_single_eq_coPair (Or.inl rfl)]
    decide +kernel
  have hcases := l10se2a_candidates (w • Pi.single 2 1) hρmem ⟨hco1, hco3, hif⟩
  have hσunits : ∀ ν : Kˣ, Units.map σ.toMonoidHom (Units.map σ.toMonoidHom ν) = ν :=
    fun ν => Units.ext (hσσ (ν : K))
  have hP2' : ∀ ν : Kˣ,
      rootDiagUnit .E6 (pairDiag 2 4 ν (Units.map σ.toMonoidHom ν)) ∈ omegaMinusLevi σ := by
    intro ν
    rw [← e24]
    exact hP2 rfl (hσunits ν)
  have hchar2 : ∀ ν : Kˣ,
      rootChar (τ := Tag.E6) (pairDiag 2 4 ν (Units.map σ.toMonoidHom ν))
          (w • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ)) =
        (Units.map δ.toRingHom.toMonoidHom ν) ^ (2 : ℤ) := by
    intro ν
    have hbT : rootDiagUnit .E6 (pairDiag 2 4 ν (Units.map σ.toMonoidHom ν)) ∈
        torusGroup TwistTag.E6.tag K := rootDiagUnit_pairDiag_mem_torusGroup _ _ _ _
    have e := hm _ (hP2' ν) hbT
    rw [diagField_rootDiagUnit] at e
    have hcomm : rootDiagUnit .E6 l *
          rootDiagUnit .E6 (pairDiag 2 4 ν (Units.map σ.toMonoidHom ν)) =
        rootDiagUnit .E6 (pairDiag 2 4 ν (Units.map σ.toMonoidHom ν)) *
          rootDiagUnit .E6 l :=
      mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hh)
        (torusGroup_le_diagonalGroup hbT)
    have hcancel : canonicalRep (coxeterSystem Tag.E6) K w *
          rootDiagUnit .E6 (fun i => Units.map δ.toRingHom.toMonoidHom
            (pairDiag 2 4 ν (Units.map σ.toMonoidHom ν) i)) *
          (canonicalRep (coxeterSystem Tag.E6) K w)⁻¹ =
        rootDiagUnit .E6 (pairDiag 2 4 ν (Units.map σ.toMonoidHom ν)) := by
      calc canonicalRep (coxeterSystem Tag.E6) K w *
            rootDiagUnit .E6 (fun i => Units.map δ.toRingHom.toMonoidHom
              (pairDiag 2 4 ν (Units.map σ.toMonoidHom ν) i)) *
            (canonicalRep (coxeterSystem Tag.E6) K w)⁻¹
          = (rootDiagUnit .E6 l)⁻¹ *
              ((rootDiagUnit .E6 l * canonicalRep (coxeterSystem Tag.E6) K w) *
                rootDiagUnit .E6 (fun i => Units.map δ.toRingHom.toMonoidHom
                  (pairDiag 2 4 ν (Units.map σ.toMonoidHom ν) i)) *
                (rootDiagUnit .E6 l * canonicalRep (coxeterSystem Tag.E6) K w)⁻¹) *
              rootDiagUnit .E6 l := by group
        _ = (rootDiagUnit .E6 l)⁻¹ *
              rootDiagUnit .E6 (pairDiag 2 4 ν (Units.map σ.toMonoidHom ν)) *
              rootDiagUnit .E6 l := by rw [e]
        _ = rootDiagUnit .E6 (pairDiag 2 4 ν (Units.map σ.toMonoidHom ν)) := by
          rw [mul_assoc, hcomm.symm, ← mul_assoc, inv_mul_cancel, one_mul]
    have hchar := (rootDiagUnit_eq_conj_canonicalRep_iff
        (pairDiag 2 4 ν (Units.map σ.toMonoidHom ν))
        (fun i => Units.map δ.toRingHom.toMonoidHom
          (pairDiag 2 4 ν (Units.map σ.toMonoidHom ν) i)) w).1 hcancel.symm
    have h2' := hchar (Pi.single 2 1)
    have hRHS : rootChar (τ := Tag.E6) (fun i => Units.map δ.toRingHom.toMonoidHom
          (pairDiag 2 4 ν (Units.map σ.toMonoidHom ν) i))
          (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) =
        (Units.map δ.toRingHom.toMonoidHom ν) ^ (2 : ℤ) := by
      rw [show (fun i => Units.map δ.toRingHom.toMonoidHom
            (pairDiag 2 4 ν (Units.map σ.toMonoidHom ν) i)) =
          pairDiag 2 4 (Units.map δ.toRingHom.toMonoidHom ν)
            (Units.map δ.toRingHom.toMonoidHom (Units.map σ.toMonoidHom ν)) from
        map_pairDiag δ 2 4 ν (Units.map σ.toMonoidHom ν)]
      rw [rootChar_pairDiag]
      rw [show coPair .E6 2 (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) = 2 by decide +kernel,
          show coPair .E6 4 (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) = 0 by decide +kernel]
      rw [zpow_zero, mul_one]
    rw [hRHS] at h2'
    exact h2'
  have hsqK : ∀ {x y : K}, x ^ 2 = y ^ 2 → x = y := by
    intro x y hxy
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxy with h | h
    · exact h
    · rwa [CharTwo.neg_eq] at h
  have hsqU : ∀ {u v : Kˣ}, u ^ (2 : ℤ) = v ^ (2 : ℤ) → u = v := by
    intro u v huv
    have huv2 : u ^ 2 = v ^ 2 := by simpa using huv
    exact Units.ext (hsqK (by simpa only [Units.val_pow_eq_pow_val] using congrArg Units.val huv2))
  have hPN : ∀ ρ : Fin Tag.E6.rank → ℤ, w • Pi.single 2 1 = ρ →
      coPair .E6 2 ρ = 1 → coPair .E6 4 ρ = 1 → False := by
    intro ρ hwρ hc2 hc4
    have hP : ∀ ν : Kˣ, ν * Units.map σ.toMonoidHom ν =
        (Units.map δ.toRingHom.toMonoidHom ν) ^ (2 : ℤ) := by
      intro ν
      have hthis := hchar2 ν
      rw [hwρ] at hthis
      rw [rootChar_pairDiag] at hthis
      rw [hc2, hc4] at hthis
      simp only [zpow_one] at hthis
      exact hthis
    have h1 : (Units.map δ.toRingHom.toMonoidHom (Units.mk0 ω hω0)) ^ (2 : ℤ) =
        (Units.map δ.toRingHom.toMonoidHom
          (Units.map σ.toMonoidHom (Units.mk0 ω hω0))) ^ (2 : ℤ) := by
      have e1 := hP (Units.mk0 ω hω0)
      have e2 := hP (Units.map σ.toMonoidHom (Units.mk0 ω hω0))
      rw [hσunits] at e2
      rw [mul_comm] at e1
      exact e1.symm.trans e2
    have h2 : Units.map δ.toRingHom.toMonoidHom (Units.mk0 ω hω0) =
        Units.map δ.toRingHom.toMonoidHom (Units.map σ.toMonoidHom (Units.mk0 ω hω0)) :=
      hsqU h1
    have h3 : ω = σ ω := by
      have h := congrArg Units.val h2
      simpa [Units.val_mk0] using h
    exact hω h3.symm
  rcases hcases with hw2 | hw2 | hw2 | hw2
  · have hw4 : w • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) = Pi.single 4 1 := by
      have h := hw24
      rw [smul_add, hw2] at h
      exact add_left_cancel h
    have hweq : w = 1 := eq_one_of_smul_D4 hw1 hw2 hw3 hw4
    have hδ1 : ∀ c, δ c = c := by
      intro c
      by_cases hc : c = 0
      · rw [hc, map_zero]
      · have hν := hchar2 (Units.mk0 c hc)
        rw [hw2] at hν
        rw [rootChar_pairDiag] at hν
        rw [show coPair .E6 2 (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) = 2 by decide +kernel,
            show coPair .E6 4 (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) = 0 by decide +kernel] at hν
        rw [zpow_zero, mul_one] at hν
        have hval : (c : K) ^ 2 = (δ c) ^ 2 := by
          have h2 : (Units.mk0 c hc) ^ 2 =
              (Units.map δ.toRingHom.toMonoidHom (Units.mk0 c hc)) ^ 2 := by simpa using hν
          simpa [Units.val_mk0] using congrArg Units.val h2
        exact (hsqK hval).symm
    refine ⟨hδ1, l * a, ?_⟩
    rw [hgdec, mul_one, mul_one, hweq, canonicalRep_one]
    simp only [mul_one]
    exact (rootDiagUnit_mul l a).symm
  · exfalso
    have hμchar : (Units.map δ.toRingHom.toMonoidHom μ) ^ (2 : ℤ) =
        (Units.map σ.toMonoidHom μ) ^ (2 : ℤ) := by
      have hthis := hchar2 μ
      rw [hw2] at hthis
      rw [rootChar_pairDiag] at hthis
      rw [show coPair .E6 2 (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) = 0 by decide +kernel,
          show coPair .E6 4 (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) = 2 by decide +kernel] at hthis
      rw [zpow_zero, one_mul] at hthis
      exact hthis.symm
    have hδμeq : Units.map δ.toRingHom.toMonoidHom μ = μ := by rw [hsqU hμchar, hσμ]
    have hδμv : δ (μ : K) = (μ : K) := congrArg Units.val hδμeq
    have hw4 : w • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) = Pi.single 2 1 := by
      have h := hw24
      rw [smul_add, hw2] at h
      rw [add_comm (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) (Pi.single 4 1)] at h
      exact add_left_cancel h
    have hw5 := smul_single_five_of_swap_D4 hw1 hw2 hw3 hw4
    have e := hW c₀
    have hδb : (fun i => Units.map δ.toRingHom.toMonoidHom (d4CentralDiag μ μ i)) =
        d4CentralDiag μ μ := by
      funext i
      simp only [d4CentralDiag, Pi.mul_apply, map_mul, Pi.mulSingle_apply]
      split_ifs <;> (apply Units.ext; simp [hδμv])
    rw [diagField_rootDiagUnit, hδb, hgdec, mul_one, mul_one] at e
    have e' : rootDiagUnit .E6 (d4CentralDiag μ μ) =
        canonicalRep (coxeterSystem Tag.E6) K w * rootDiagUnit .E6 (d4CentralDiag μ μ) *
          (canonicalRep (coxeterSystem Tag.E6) K w)⁻¹ := by
      have e1 : canonicalRep (coxeterSystem Tag.E6) K w * rootDiagUnit .E6 (d4CentralDiag μ μ) *
          (canonicalRep (coxeterSystem Tag.E6) K w)⁻¹ =
            (rootDiagUnit .E6 l)⁻¹ * rootDiagUnit .E6 (d4CentralDiag μ μ) *
              rootDiagUnit .E6 l := by
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
  · exfalso
    exact hPN (Pi.single 0 1 + Pi.single 1 1 + 2 • Pi.single 2 1 + 2 • Pi.single 3 1 +
        2 • Pi.single 4 1 + Pi.single 5 1) hw2 (by decide +kernel) (by decide +kernel)
  · exfalso
    exact hPN (-(Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1 + 2 • Pi.single 3 1 +
        Pi.single 4 1 + Pi.single 5 1)) hw2 (by decide +kernel) (by decide +kernel)

end CFSG.StandardType.LieKnownR2.TwE6
