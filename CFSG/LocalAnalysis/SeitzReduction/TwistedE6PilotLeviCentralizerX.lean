module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviCentralizerBasic
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR6X

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint

section Weyl

@[expose] def rhoE6 (j : Fin Tag.E6.rank) : Fin Tag.E6.rank := TwistTag.E6.perm j

theorem perm_E6_eq_highNode_iff : ∀ j : Fin Tag.E6.rank,
    rhoE6 j = highNode .E6 ↔ j = highNode .E6 := by
  decide

theorem perm_E6_perm : ∀ j : Fin Tag.E6.rank, rhoE6 (rhoE6 j) = j := by
  decide

theorem iform_single_perm_E6 : ∀ i j : Fin Tag.E6.rank,
    iform (Pi.single (rhoE6 i) 1 : Fin Tag.E6.rank → ℤ)
        (Pi.single (rhoE6 j) 1) =
      iform (Pi.single i 1 : Fin Tag.E6.rank → ℤ) (Pi.single j 1) := by
  decide


theorem false_of_smul_single_perm {w : WeylGroup .E6}
    (hw : ∀ j : Fin Tag.E6.rank, j ≠ highNode .E6 →
      w • (Pi.single (rhoE6 j) 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1) : False := by
  have hτ : Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨ Tag.E6 = .E8 := Or.inl rfl
  have hr := isRoot_highRoot Tag.E6
  have hj0 : rhoE6 (highNode .E6) = highNode .E6 :=
    (perm_E6_eq_highNode_iff _).2 rfl
  have hw0 := EPilot.eq_single_or_sub_highRoot_of_iform_eq hτ
    (IsRoot.smul (isRoot_single Tag.E6 (highNode .E6)) w) fun j hj => by
      have hj' : rhoE6 j ≠ highNode .E6 := fun e =>
        hj ((perm_E6_eq_highNode_iff j).1 e)
      have e := iform_single_perm_E6 (highNode .E6) (rhoE6 j)
      rw [hj0, perm_E6_perm] at e
      calc iform (w • (Pi.single (highNode .E6) 1 : Fin Tag.E6.rank → ℤ)) (Pi.single j 1) =
          iform (w • (Pi.single (highNode .E6) 1 : Fin Tag.E6.rank → ℤ))
            (w • (Pi.single (rhoE6 j) 1 : Fin Tag.E6.rank → ℤ)) := by rw [hw j hj]
        _ = iform (Pi.single (highNode .E6) 1 : Fin Tag.E6.rank → ℤ)
            (Pi.single (rhoE6 j) 1) := iform_smul w _ _
        _ = iform (Pi.single (highNode .E6) 1 : Fin Tag.E6.rank → ℤ) (Pi.single j 1) :=
          e.symm
  have hwk : ∀ k : Fin Tag.E6.rank, k ≠ highNode .E6 →
      w • (Pi.single k 1 : Fin Tag.E6.rank → ℤ) = Pi.single (rhoE6 k) 1 := by
    intro k hk
    have hk' : rhoE6 k ≠ highNode .E6 := fun e =>
      hk ((perm_E6_eq_highNode_iff k).1 e)
    have := hw (rhoE6 k) hk'
    rwa [perm_E6_perm] at this
  have j1 : (⟨0, by decide⟩ : Fin Tag.E6.rank) ≠ highNode .E6 := by decide
  have hρ0 : rhoE6 (⟨0, by decide⟩ : Fin Tag.E6.rank) ≠ ⟨0, by decide⟩ := by decide
  have hne : (Pi.single (rhoE6 (⟨0, by decide⟩ : Fin Tag.E6.rank)) 1 :
      Fin Tag.E6.rank → ℤ) ≠ Pi.single ⟨0, by decide⟩ 1 := fun e =>
    hρ0 (E6Pilot.eq_of_single_eq_single_E6 e)
  rcases hw0 with h0 | h0
  ·
    have hw1 : w = 1 := eq_one_of_forall_height_pos fun i => by
      by_cases hi : i = highNode .E6
      · subst hi
        rw [h0, height_single]
        norm_num
      · rw [hwk i hi, height_single]
        norm_num
    have e := hw _ j1
    rw [hw1, one_smul] at e
    exact hne e
  ·
    obtain ⟨v', i, hv'⟩ := isRoot_iff_exists_smul_single.1 hr
    have hsx := EPilot.smul_conj_simple_eq hτ hv'
    have hsw : (v' * simple Tag.E6 i * v'⁻¹) * w = 1 := eq_one_of_forall_height_pos fun k => by
      by_cases hk : k = highNode .E6
      · subst hk
        rw [mul_smul, h0, hsx]
        have e : (Pi.single (highNode .E6) 1 - highRoot .E6 : Fin Tag.E6.rank → ℤ) -
            (Pi.single (highNode .E6) 1 - highRoot .E6 : Fin Tag.E6.rank → ℤ)
              (highNode .E6) • highRoot .E6 = Pi.single (highNode .E6) 1 := by
          rw [Pi.sub_apply, Pi.single_eq_same, EPilot.highRoot_highNode hτ]
          ext k
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [e, height_single]
        norm_num
      · have hk' : rhoE6 k ≠ highNode .E6 := fun e =>
          hk ((perm_E6_eq_highNode_iff k).1 e)
        rw [mul_smul, hwk k hk, hsx, Pi.single_eq_of_ne (Ne.symm hk'), zero_smul, sub_zero,
          height_single]
        norm_num
    have e : ((v' * simple Tag.E6 i * v'⁻¹) * w) •
        (Pi.single (rhoE6 ⟨0, by decide⟩) 1 : Fin Tag.E6.rank → ℤ) =
          Pi.single ⟨0, by decide⟩ 1 := by
      rw [mul_smul, hw _ j1, hsx, Pi.single_eq_of_ne (Ne.symm j1), zero_smul, sub_zero]
    rw [hsw, one_smul] at e
    exact hne e

end Weyl

section Formulas

variable {τ : Tag} {K : Type} [Field K]

theorem map_pairDiag (δ : K ≃+* K) (j j' : Fin τ.rank) (μ ν : Kˣ) :
    (fun i => Units.map δ.toRingHom.toMonoidHom (pairDiag j j' μ ν i)) =
      pairDiag j j' (Units.map δ.toRingHom.toMonoidHom μ) (Units.map δ.toRingHom.toMonoidHom ν) := by
  funext i
  simp [pairDiag, map_mul, map_zpow]

theorem map_cartanRow (δ : K ≃+* K) (j : Fin τ.rank) (μ : Kˣ) :
    (fun i => Units.map δ.toRingHom.toMonoidHom (μ ^ τ.cartan j i)) =
      fun i => (Units.map δ.toRingHom.toMonoidHom μ) ^ τ.cartan j i := by
  funext i
  simp [map_zpow]

theorem diagField_rootDiagUnit (a b : Fin τ.rank → Kˣ) (δ : K ≃+* K) :
    rootDiagUnit τ a * Units.map (entrywiseHom δ.toRingHom) (rootDiagUnit τ b) *
        (rootDiagUnit τ a)⁻¹ =
      rootDiagUnit τ (fun i => Units.map δ.toRingHom.toMonoidHom (b i)) := by
  rw [units_map_entrywiseHom_rootDiagUnit_ringEquiv, ← rootDiagUnit_mul, mul_comm,
    rootDiagUnit_mul, mul_inv_cancel_right]


theorem diagField_pinnedX (a : Fin τ.rank → Kˣ) (δ : K ≃+* K) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (c : K) :
    rootDiagUnit τ a * Units.map (entrywiseHom δ.toRingHom) (pinnedX τ K α c) *
        (rootDiagUnit τ a)⁻¹ = pinnedX τ K α ((rootChar a α : K) * δ c) := by
  have e : Units.map (entrywiseHom δ.toRingHom) (pinnedX τ K α c) = pinnedX τ K α (δ c) :=
    Units.ext (entrywise_pinnedX δ.toRingHom α c)
  rw [e, rootDiagUnit_conj_pinnedX a hα]

theorem conj_rootDiagUnit_canonicalRep_pinnedX (h2 : (2 : K) = 0) (l : Fin τ.rank → Kˣ)
    (w : WeylGroup τ) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (c : K) :
    (rootDiagUnit τ l * canonicalRep (coxeterSystem τ) K w) * pinnedX τ K α c *
        (rootDiagUnit τ l * canonicalRep (coxeterSystem τ) K w)⁻¹ =
      pinnedX τ K (w • α) ((rootChar l (w • α) : K) * c) := by
  rw [← rootDiagUnit_conj_pinnedX l (IsRoot.smul hα w), ← canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hα]
  group

end Formulas

section Core

local instance twistedE6PilotLeviCentralizerXNeZero : NeZero Tag.E6.rank := ⟨by decide⟩

local instance twistedE6PilotLeviCentralizerXNeZero' : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩


variable {K : Type} [Field K]

theorem mem_rootSubgroup_highRoot_of_conj_X [CharP K 2] {w : WeylGroup .E6}
    {l : Fin Tag.E6.rank → Kˣ} (hl : rootDiagUnit .E6 l ∈ torusGroup .E6 K) {u v : ModGL .E6 K}
    (hu : u ∈ posUnipotent .E6 K)
    (hv : v ∈ rootSpan .E6 K (inversionSet w)) {μ ζ μ' ζ' : Kˣ} (hμ : μ ≠ 1) (hζ : ζ ≠ 1)
    (hμ' : μ' ≠ 1) (hζ' : ζ' ≠ 1)
    (hc : ∀ p ∈ [(pairDiag 0 5 μ μ, pairDiag 0 5 μ' μ'), (pairDiag 0 5 ζ ζ⁻¹, pairDiag 0 5 ζ' ζ'⁻¹),
        (pairDiag 2 4 μ μ, pairDiag 2 4 μ' μ'), (pairDiag 2 4 ζ ζ⁻¹, pairDiag 2 4 ζ' ζ'⁻¹),
        ((fun i => μ ^ Tag.E6.cartan 3 i), (fun i => μ' ^ Tag.E6.cartan 3 i))],
      rootDiagUnit .E6 l * u * canonicalRep (coxeterSystem Tag.E6) K w * v * rootDiagUnit .E6 p.2 =
        rootDiagUnit .E6 p.1 *
          (rootDiagUnit .E6 l * u * canonicalRep (coxeterSystem Tag.E6) K w * v)) :
    u ∈ rootSubgroup .E6 K (highRoot .E6) ∧ v ∈ rootSubgroup .E6 K (highRoot .E6) := by
  have hT : ∀ p ∈ [(pairDiag 0 5 μ μ, pairDiag 0 5 μ' μ'), (pairDiag 0 5 ζ ζ⁻¹, pairDiag 0 5 ζ' ζ'⁻¹),
        (pairDiag 2 4 μ μ, pairDiag 2 4 μ' μ'), (pairDiag 2 4 ζ ζ⁻¹, pairDiag 2 4 ζ' ζ'⁻¹),
        ((fun i => μ ^ Tag.E6.cartan 3 i), (fun i => μ' ^ Tag.E6.cartan 3 i))],
      rootDiagUnit .E6 p.1 ∈ torusGroup .E6 K ∧ rootDiagUnit .E6 p.2 ∈ torusGroup .E6 K := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact ⟨rootDiagUnit_pairDiag_mem_torusGroup _ _ _ _,
        rootDiagUnit_pairDiag_mem_torusGroup _ _ _ _⟩
    · exact ⟨rootDiagUnit_pairDiag_mem_torusGroup _ _ _ _,
        rootDiagUnit_pairDiag_mem_torusGroup _ _ _ _⟩
    · exact ⟨rootDiagUnit_pairDiag_mem_torusGroup _ _ _ _,
        rootDiagUnit_pairDiag_mem_torusGroup _ _ _ _⟩
    · exact ⟨rootDiagUnit_pairDiag_mem_torusGroup _ _ _ _,
        rootDiagUnit_pairDiag_mem_torusGroup _ _ _ _⟩
    · exact ⟨by rw [← torusElt_eq_rootDiagUnit]; exact torusElt_mem_torusGroup _ _,
        by rw [← torusElt_eq_rootDiagUnit]; exact torusElt_mem_torusGroup _ _⟩
  obtain ⟨hu', hv', -⟩ := bruhat_factors_of_conj_list hl hu hv _ fun p hp =>
    ⟨(hT p hp).1, (hT p hp).2, hc p hp⟩
  have hθ : ∀ {S : Set (Fin Tag.E6.rank → ℤ)}, (∀ α ∈ S, α = highRoot .E6) →
      rootSpan .E6 K S ≤ rootSubgroup .E6 K (highRoot .E6) := fun hS =>
    iSup₂_le fun α hα => by rw [hS α hα]
  refine ⟨hθ (fun α hα => ?_) hu', hθ (fun α hα => ?_) hv'⟩
  · obtain ⟨⟨hαr, hαp⟩, hαL⟩ := hα
    rcases eq_highRoot_or_neg_of_rootChar_X hμ hζ hαr (hαL _ (by simp)) (hαL _ (by simp))
      (hαL _ (by simp)) (hαL _ (by simp)) (hαL _ (by simp)) with h | h
    · exact h
    · exfalso
      rw [h, height_neg] at hαp
      have := height_highRoot_pos Tag.E6
      omega
  · obtain ⟨hαI, hαL⟩ := hα
    obtain ⟨hαr, hαp⟩ := inversionSet_pos hαI
    rcases eq_highRoot_or_neg_of_rootChar_X hμ' hζ' hαr (hαL _ (by simp)) (hαL _ (by simp))
      (hαL _ (by simp)) (hαL _ (by simp)) (hαL _ (by simp)) with h | h
    · exact h
    · exfalso
      rw [h, height_neg] at hαp
      have := height_highRoot_pos Tag.E6
      omega

theorem conj_rootDiagUnit_mem_highRootSL2 (b : Fin Tag.E6.rank → Kˣ) {x : ModGL .E6 K}
    (hx : x ∈ EPilot.highRootSL2 .E6 K) :
    rootDiagUnit .E6 b * x * (rootDiagUnit .E6 b)⁻¹ ∈ EPilot.highRootSL2 .E6 K := by
  have hr := isRoot_highRoot Tag.E6
  have e : (EPilot.highRootSL2 .E6 K).map (MulAut.conj (rootDiagUnit .E6 b)).toMonoidHom =
      EPilot.highRootSL2 .E6 K := by
    rw [EPilot.highRootSL2, Subgroup.map_sup, map_conj_rootDiagUnit_rootSubgroup b hr,
      map_conj_rootDiagUnit_rootSubgroup b (IsRoot.neg hr)]
  rw [← e]
  exact ⟨x, hx, rfl⟩

theorem rootDiagUnit_mem_highRootSL2_of {b : Fin Tag.E6.rank → Kˣ}
    (hb : ∀ j, j ≠ highNode .E6 → b j = 1) : rootDiagUnit .E6 b ∈ EPilot.highRootSL2 .E6 K := by
  have e : b = EPilot.highDiag .E6 (b (highNode .E6)) := by
    funext j
    by_cases hj : j = highNode .E6
    · subst hj
      rw [EPilot.highDiag, Pi.mulSingle_eq_same]
    · rw [EPilot.highDiag, Pi.mulSingle_eq_of_ne hj, hb j hj]
  rw [e]
  exact EPilot.rootDiagUnit_highDiag_mem_highRootSL2 (Or.inl rfl) _

theorem rootDiagUnit_canonicalRep_mul_mem_highRootSL2 [CharP K 2] {w : WeylGroup .E6}
    {l a : Fin Tag.E6.rank → Kˣ} (hl : rootDiagUnit .E6 l ∈ torusGroup .E6 K)
    (hw : ∀ j, j ≠ highNode .E6 → w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1)
    (hla : ∀ j, j ≠ highNode .E6 → l j * a j = 1) :
    rootDiagUnit .E6 l * canonicalRep (coxeterSystem Tag.E6) K w * rootDiagUnit .E6 a ∈
      EPilot.highRootSL2 .E6 K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hτ : Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨ Tag.E6 = .E8 := Or.inl rfl
  have hr := isRoot_highRoot Tag.E6
  have hJD := EPilot.highRootSL2_le_centralizer_perpLevi (K := K) hτ
  have hw0 := EPilot.eq_single_or_sub_highRoot_of_iform_eq hτ
    (IsRoot.smul (isRoot_single Tag.E6 (highNode .E6)) w) fun j hj => by
      calc iform (w • (Pi.single (highNode .E6) 1 : Fin Tag.E6.rank → ℤ)) (Pi.single j 1) =
          iform (w • (Pi.single (highNode .E6) 1 : Fin Tag.E6.rank → ℤ))
            (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) := by rw [hw j hj]
        _ = iform (Pi.single (highNode .E6) 1 : Fin Tag.E6.rank → ℤ) (Pi.single j 1) :=
          iform_smul w _ _
  rcases hw0 with h0 | h0
  ·
    have hw1 : w = 1 := eq_one_of_forall_height_pos fun i => by
      by_cases hi : i = highNode .E6
      · subst hi
        rw [h0, height_single]
        norm_num
      · rw [hw i hi, height_single]
        norm_num
    subst hw1
    rw [canonicalRep_one, mul_one, ← rootDiagUnit_mul]
    exact rootDiagUnit_mem_highRootSL2_of fun j hj => hla j hj
  ·
    obtain ⟨v', i, hv'⟩ := isRoot_iff_exists_smul_single.1 hr
    set s := v' * simple Tag.E6 i * v'⁻¹ with hs
    have hsx := EPilot.smul_conj_simple_eq hτ hv'
    have hsw : s * w = 1 := eq_one_of_forall_height_pos fun j => by
      by_cases hj : j = highNode .E6
      · subst hj
        rw [mul_smul, h0, hsx]
        have e : (Pi.single (highNode .E6) 1 - highRoot .E6 : Fin Tag.E6.rank → ℤ) -
            (Pi.single (highNode .E6) 1 - highRoot .E6 : Fin Tag.E6.rank → ℤ) (highNode .E6) •
              highRoot .E6 = Pi.single (highNode .E6) 1 := by
          rw [Pi.sub_apply, Pi.single_eq_same, EPilot.highRoot_highNode hτ]
          ext k
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [e, height_single]
        norm_num
      · rw [mul_smul, hw j hj, hsx, Pi.single_eq_of_ne (Ne.symm hj), zero_smul, sub_zero,
          height_single]
        norm_num
    have hws : w * s = 1 := by
      rw [eq_inv_of_mul_eq_one_left hsw, mul_inv_cancel]
    set nθ := canonicalRep (coxeterSystem Tag.E6) K v' * weylElt Tag.E6 K i 1 *
      (canonicalRep (coxeterSystem Tag.E6) K v')⁻¹ with hnθ
    have hnθJ : nθ ∈ EPilot.highRootSL2 .E6 K :=
      EPilot.conj_mem_highRootSL2 hv' (EPilot.weylElt_mem_rootPair i 1)
    set t₀ := rootDiagUnit .E6 l * canonicalRep (coxeterSystem Tag.E6) K w * nθ with ht₀
    have ht₀T : t₀ ∈ torusGroup .E6 K := by
      refine mem_torusGroup_of_mapsRootLines_one ?_ ?_
      · exact mul_mem (mul_mem (Subgroup.mem_sup_left hl) (canonicalRep_mem_monomialSubgroup K w))
          (mul_mem (mul_mem (canonicalRep_mem_monomialSubgroup K _)
            (weylElt_mem_monomialSubgroup i))
            (inv_mem (canonicalRep_mem_monomialSubgroup K _)))
      · have hmaps := ((mapsRootLines_of_mem_torusGroup hl).mul (mapsRootLines_canonicalRep w)).mul
          (((mapsRootLines_canonicalRep v').mul (mapsRootLines_weylElt i)).mul
            (mapsRootLines_canonicalRep v').inv)
        rwa [one_mul, ← hs, hws] at hmaps
    obtain ⟨l₀, hl₀⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht₀T
    have hl₀j : ∀ j, j ≠ highNode .E6 → l₀ j = l j := by
      intro j hj
      have hx := EPilot.pinnedX_single_mem_perpLevi (K := K) hj (1 : K)
      have hc := Subgroup.mem_centralizer_iff.1 (hJD hnθJ) _ hx
      have e1 : t₀ * pinnedX .E6 K (Pi.single j 1) 1 * t₀⁻¹ =
          pinnedX .E6 K (Pi.single j 1) (l₀ j) := by
        rw [hl₀, rootDiagUnit_conj_pinnedX l₀ (isRoot_single _ j), EPilot.rootChar_single_eq,
          mul_one]
      have e2 : t₀ * pinnedX .E6 K (Pi.single j 1) 1 * t₀⁻¹ =
          pinnedX .E6 K (Pi.single j 1) (l j) := by
        have e3 : t₀ * pinnedX .E6 K (Pi.single j 1) 1 * t₀⁻¹ =
            (rootDiagUnit .E6 l * canonicalRep (coxeterSystem Tag.E6) K w) *
              pinnedX .E6 K (Pi.single j 1) 1 *
                (rootDiagUnit .E6 l * canonicalRep (coxeterSystem Tag.E6) K w)⁻¹ := by
          calc t₀ * pinnedX .E6 K (Pi.single j 1) 1 * t₀⁻¹ =
              (rootDiagUnit .E6 l * canonicalRep (coxeterSystem Tag.E6) K w) *
                (nθ * pinnedX .E6 K (Pi.single j 1) 1) * nθ⁻¹ *
                  (rootDiagUnit .E6 l * canonicalRep (coxeterSystem Tag.E6) K w)⁻¹ := by
                rw [ht₀]; group
            _ = _ := by rw [← hc]; group
        rw [e3, conj_rootDiagUnit_canonicalRep_pinnedX h2 l w (isRoot_single _ j), hw j hj,
          EPilot.rootChar_single_eq, mul_one]
      exact Units.ext (pinnedX_injective .E6 K _ (e1.symm.trans e2))
    have e : rootDiagUnit .E6 l * canonicalRep (coxeterSystem Tag.E6) K w * rootDiagUnit .E6 a =
        rootDiagUnit .E6 (l₀ * a) *
          (rootDiagUnit .E6 a⁻¹ * nθ⁻¹ * (rootDiagUnit .E6 a⁻¹)⁻¹) := by
      rw [← rootDiagUnit_inv, inv_inv, rootDiagUnit_mul, ← hl₀, ht₀]
      group
    rw [e]
    refine mul_mem (rootDiagUnit_mem_highRootSL2_of fun j hj => ?_)
      (conj_rootDiagUnit_mem_highRootSL2 _ (inv_mem hnθJ))
    rw [Pi.mul_apply, hl₀j j hj, hla j hj]

theorem diagField_mul (a : Fin Tag.E6.rank → Kˣ) (δ : K ≃+* K) (x y : ModGL .E6 K) :
    rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom) (x * y) * (rootDiagUnit .E6 a)⁻¹ =
      (rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom) x * (rootDiagUnit .E6 a)⁻¹) *
        (rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom) y * (rootDiagUnit .E6 a)⁻¹) := by
  rw [map_mul]
  group

theorem pair_cases [CharP K 2] (σ : K →+* K) {w : WeylGroup .E6} (l a : Fin Tag.E6.rank → Kˣ)
    (δ : K ≃+* K) {j : Fin Tag.E6.rank} (hjne : rhoE6 j ≠ j) {c : K} (hc : c ≠ 0)
    (e : (rootDiagUnit .E6 l * canonicalRep (coxeterSystem Tag.E6) K w) *
        (rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom)
          (pinnedX .E6 K (Pi.single j 1) c * pinnedX .E6 K (Pi.single (rhoE6 j) 1) (σ c)) *
          (rootDiagUnit .E6 a)⁻¹) *
        (rootDiagUnit .E6 l * canonicalRep (coxeterSystem Tag.E6) K w)⁻¹ =
      pinnedX .E6 K (Pi.single j 1) c * pinnedX .E6 K (Pi.single (rhoE6 j) 1) (σ c)) :
    (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1 ∧
        w • (Pi.single (rhoE6 j) 1 : Fin Tag.E6.rank → ℤ) = Pi.single (rhoE6 j) 1 ∧
        (l j : K) * ((a j : K) * δ c) = c ∧ (l (rhoE6 j) : K) * ((a (rhoE6 j) : K) * δ (σ c)) = σ c) ∨
      (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single (rhoE6 j) 1 ∧
        w • (Pi.single (rhoE6 j) 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1 ∧
        (l (rhoE6 j) : K) * ((a j : K) * δ c) = σ c ∧ (l j : K) * ((a (rhoE6 j) : K) * δ (σ c)) = c) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hj := isRoot_single Tag.E6 j
  have hρj := isRoot_single Tag.E6 (rhoE6 j)
  rw [diagField_mul, diagField_pinnedX a δ hj, diagField_pinnedX a δ hρj,
    EPilot.rootChar_single_eq, EPilot.rootChar_single_eq] at e
  have e' : pinnedX .E6 K (w • Pi.single j 1)
        ((rootChar l (w • Pi.single j 1) : K) * ((a j : K) * δ c)) *
      pinnedX .E6 K (w • Pi.single (rhoE6 j) 1)
        ((rootChar l (w • Pi.single (rhoE6 j) 1) : K) * ((a (rhoE6 j) : K) * δ (σ c))) =
      pinnedX .E6 K (Pi.single j 1) c * pinnedX .E6 K (Pi.single (rhoE6 j) 1) (σ c) := by
    rw [← conj_rootDiagUnit_canonicalRep_pinnedX h2 l w hj,
      ← conj_rootDiagUnit_canonicalRep_pinnedX h2 l w hρj, ← e]
    group
  have hcomm0 : ∀ s t : K, pinnedX .E6 K (Pi.single j 1) s * pinnedX .E6 K (Pi.single (rhoE6 j) 1) t =
      pinnedX .E6 K (Pi.single (rhoE6 j) 1) t * pinnedX .E6 K (Pi.single j 1) s := by
    intro s t
    have h := (commute_pinnedX_permLattice_twistedE6 (K := K)
      (isRoot_single TwistTag.E6.tag j) s t).eq
    have hpl : @permLattice TwistTag.E6.tag TwistTag.E6.perm
        (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) =
          (Pi.single (rhoE6 j) 1 : Fin Tag.E6.rank → ℤ) :=
      permLattice_single _ _
    rw [hpl] at h
    exact h
  have hcommβ : ∀ s t : K, pinnedX .E6 K (w • Pi.single j 1) s *
      pinnedX .E6 K (w • Pi.single (rhoE6 j) 1) t =
      pinnedX .E6 K (w • Pi.single (rhoE6 j) 1) t * pinnedX .E6 K (w • Pi.single j 1) s := by
    intro s t
    rw [← canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hj,
      ← canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hρj]
    have h := hcomm0 s t
    calc _ = canonicalRep (coxeterSystem Tag.E6) K w *
          (pinnedX .E6 K (Pi.single j 1) s * pinnedX .E6 K (Pi.single (rhoE6 j) 1) t) *
            (canonicalRep (coxeterSystem Tag.E6) K w)⁻¹ := by group
      _ = canonicalRep (coxeterSystem Tag.E6) K w *
          (pinnedX .E6 K (Pi.single (rhoE6 j) 1) t * pinnedX .E6 K (Pi.single j 1) s) *
            (canonicalRep (coxeterSystem Tag.E6) K w)⁻¹ := by rw [h]
      _ = _ := by group
  have hsne : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ≠ Pi.single (rhoE6 j) 1 := fun h =>
    hjne (E6Pilot.eq_of_single_eq_single_E6 h).symm
  have hne : w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ≠ w • Pi.single (rhoE6 j) 1 := fun h =>
    hsne (MulAction.injective w h)
  have hp1 : (rootChar l (w • Pi.single j 1) : K) * ((a j : K) * δ c) ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (mul_ne_zero (Units.ne_zero _) ((map_ne_zero δ).2 hc))
  have hp2 : (rootChar l (w • Pi.single (rhoE6 j) 1) : K) * ((a (rhoE6 j) : K) * δ (σ c)) ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (mul_ne_zero (Units.ne_zero _)
      ((map_ne_zero δ).2 ((map_ne_zero σ).2 hc)))
  rcases pinnedX_mul_eq_pinnedX_mul (IsRoot.smul hj w) (IsRoot.smul hρj w)
      ⟨hj, by rw [height_single]; norm_num⟩ ⟨hρj, by rw [height_single]; norm_num⟩ hne hsne
      hcommβ hcomm0 hp1 hp2 hc e' with ⟨h1, h2', h3, h4⟩ | ⟨h1, h2', h3, h4⟩
  · left
    rw [h1, EPilot.rootChar_single_eq] at h3
    rw [h2', EPilot.rootChar_single_eq] at h4
    exact ⟨h1, h2', h3, h4⟩
  · right
    rw [h1, EPilot.rootChar_single_eq] at h3
    rw [h2', EPilot.rootChar_single_eq] at h4
    exact ⟨h1, h2', h3, h4⟩

theorem core_X {f : ℕ} {k : Type} [Field k] [Algebra k K] (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {g : ModGL .E6 K} (hg : g ∈ adjointGroup .E6 K)
    (a : Fin Tag.E6.rank → Kˣ) (δ : K ≃+* K)
    (hfix : ∀ x : ModGL .E6 K, x ∈ su6Levi σ → g * (rootDiagUnit .E6 a *
      Units.map (entrywiseHom δ.toRingHom) x * (rootDiagUnit .E6 a)⁻¹) * g⁻¹ = x) :
    (∀ c, δ c = c) ∧ g * rootDiagUnit .E6 a ∈ EPilot.highRootSL2 .E6 K := by
  classical
  have hf : 1 ≤ f := by omega
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Finite K := finite_of_card hK
  have : CharP K 2 := charP_two_of_card hf hK
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hτ : Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨ Tag.E6 = .E8 := Or.inl rfl
  have hr := isRoot_highRoot Tag.E6
  have hσσ : ∀ c, σ (σ c) = c := apply_apply_eq hK hσ
  have hD : su6Levi σ = subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ⊓
      twistedFixedGroup TwistTag.E6 K σ := (su6Levi_facts hf hk hK hσ).2.2.2.2.1
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
  have hconj : ∀ b : Fin Tag.E6.rank → Kˣ, rootDiagUnit .E6 b ∈ su6Levi σ →
      rootDiagUnit .E6 l * u * canonicalRep (coxeterSystem Tag.E6) K w * v *
          rootDiagUnit .E6 (fun i => Units.map δ.toRingHom.toMonoidHom (b i)) =
        rootDiagUnit .E6 b * (rootDiagUnit .E6 l * u * canonicalRep (coxeterSystem Tag.E6) K w * v) := by
    intro b hb
    have e := hfix _ hb
    rw [diagField_rootDiagUnit, hgdec] at e
    rw [← e]
    group
  have hpairD : ∀ {j : Fin Tag.E6.rank} {ν ν' : Kˣ}, j ≠ 1 → rhoE6 j ≠ 1 →
      Units.map σ.toMonoidHom ν = ν' → Units.map σ.toMonoidHom ν' = ν →
      rootDiagUnit .E6 (pairDiag j (rhoE6 j) ν ν') ∈ su6Levi σ := by
    intro j ν ν' hj hρj h1 h2'
    rw [hD]
    exact rootDiagUnit_pairDiag_mem_inf (t := TwistTag.E6) hj hρj (perm_E6_perm j) h1 h2'
  have h3D : rootDiagUnit .E6 (fun i => μ ^ Tag.E6.cartan 3 i) ∈ su6Levi σ := by
    rw [hD]
    have h := torusElt_mem_inf (t := TwistTag.E6) (K := K) (σ := σ) (A := E6GraphLevi.setA)
      (j := 3) (show (3 : Fin TwistTag.E6.tag.rank) ≠ 1 by decide) (by decide) hσμ
    rw [torusElt_eq_rootDiagUnit] at h
    exact h
  have e05 : rhoE6 0 = 5 := by decide
  have e24 : rhoE6 2 = 4 := by decide
  obtain ⟨hur, hvr⟩ := mem_rootSubgroup_highRoot_of_conj_X hh huU hvI hμ1 hζ1 hμ'1 hζ'1 (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · have e := hconj _ (hpairD (j := 0) (by decide) (by decide) hσμ hσμ)
      rw [map_pairDiag, e05] at e
      exact e
    · have e := hconj _ (hpairD (j := 0) (by decide) (by decide) hσζ hσζ')
      rw [map_pairDiag, e05, map_inv] at e
      exact e
    · have e := hconj _ (hpairD (j := 2) (by decide) (by decide) hσμ hσμ)
      rw [map_pairDiag, e24] at e
      exact e
    · have e := hconj _ (hpairD (j := 2) (by decide) (by decide) hσζ hσζ')
      rw [map_pairDiag, e24, map_inv] at e
      exact e
    · have e := hconj _ h3D
      rw [map_cartanRow] at e
      exact e)
  have hJD := EPilot.highRootSL2_le_centralizer_perpLevi (K := K) hτ
  have hJ : ∀ {x : ModGL .E6 K}, x ∈ rootSubgroup .E6 K (highRoot .E6) →
      x ∈ EPilot.highRootSL2 .E6 K := fun hx => Subgroup.mem_sup_left hx
  have hu' : rootDiagUnit .E6 l * u * (rootDiagUnit .E6 l)⁻¹ ∈
      rootSubgroup .E6 K (highRoot .E6) :=
    (Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_rootSubgroup hr hh) u).1 hur
  have hm : ∀ {x : ModGL .E6 K}, x ∈ su6Levi σ → x ∈ rootSpan .E6 K (EPilot.perpRoots .E6) →
      rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom) x * (rootDiagUnit .E6 a)⁻¹ ∈
        rootSpan .E6 K (EPilot.perpRoots .E6) →
      (rootDiagUnit .E6 l * canonicalRep (coxeterSystem Tag.E6) K w) *
          (rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom) x * (rootDiagUnit .E6 a)⁻¹) *
        (rootDiagUnit .E6 l * canonicalRep (coxeterSystem Tag.E6) K w)⁻¹ = x := by
    intro x hxD hx hψx
    set y := rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom) x * (rootDiagUnit .E6 a)⁻¹
    have e := hfix x hxD
    rw [hgdec] at e
    have hvc : v * y * v⁻¹ = y := by
      rw [← Subgroup.mem_centralizer_iff.1 (hJD (hJ hvr)) _ hψx, mul_inv_cancel_right]
    have hkc : (rootDiagUnit .E6 l * u * (rootDiagUnit .E6 l)⁻¹)⁻¹ * x *
        (rootDiagUnit .E6 l * u * (rootDiagUnit .E6 l)⁻¹) = x := by
      rw [mul_assoc, Subgroup.mem_centralizer_iff.1 (hJD (hJ hu')) _ hx, inv_mul_cancel_left]
    calc (rootDiagUnit .E6 l * canonicalRep (coxeterSystem Tag.E6) K w) * y *
          (rootDiagUnit .E6 l * canonicalRep (coxeterSystem Tag.E6) K w)⁻¹ =
        (rootDiagUnit .E6 l * canonicalRep (coxeterSystem Tag.E6) K w) * (v * y * v⁻¹) *
          (rootDiagUnit .E6 l * canonicalRep (coxeterSystem Tag.E6) K w)⁻¹ := by rw [hvc]
      _ = (rootDiagUnit .E6 l * u * (rootDiagUnit .E6 l)⁻¹)⁻¹ *
          (rootDiagUnit .E6 l * u * canonicalRep (coxeterSystem Tag.E6) K w * v * y *
            (rootDiagUnit .E6 l * u * canonicalRep (coxeterSystem Tag.E6) K w * v)⁻¹) *
          (rootDiagUnit .E6 l * u * (rootDiagUnit .E6 l)⁻¹) := by group
      _ = (rootDiagUnit .E6 l * u * (rootDiagUnit .E6 l)⁻¹)⁻¹ * x *
          (rootDiagUnit .E6 l * u * (rootDiagUnit .E6 l)⁻¹) := by rw [e]
      _ = x := hkc
  have h3ne : (3 : Fin Tag.E6.rank) ≠ highNode .E6 := by decide
  have hx3D : pinnedX .E6 K (Pi.single 3 1) 1 ∈ su6Levi σ := by
    rw [hD]
    exact pinnedX_single_mem_inf (t := TwistTag.E6) (σ := σ) h2 (A := E6GraphLevi.setA)
      (j := 3) (show (3 : Fin TwistTag.E6.tag.rank) ≠ 1 by decide) (by decide) (map_one σ)
  have e3 := hm hx3D (EPilot.pinnedX_single_mem_perpLevi h3ne 1) (by
    rw [diagField_pinnedX a δ (isRoot_single _ 3)]
    exact EPilot.pinnedX_single_mem_perpLevi h3ne _)
  rw [diagField_pinnedX a δ (isRoot_single _ 3),
    conj_rootDiagUnit_canonicalRep_pinnedX h2 l w (isRoot_single _ 3)] at e3
  have hw3 : w • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) = Pi.single 3 1 :=
    EPilot.eq_of_pinnedX_eq_pinnedX_of_pos (IsRoot.smul (isRoot_single _ 3) w)
      (isRoot_single _ 3) (by rw [height_single]; norm_num) one_ne_zero e3
  rw [hw3, EPilot.rootChar_single_eq, EPilot.rootChar_single_eq, map_one, mul_one] at e3
  have hla3 : (l 3 : K) * (a 3 : K) = 1 := pinnedX_injective .E6 K _ e3
  have hcase : ∀ j : Fin Tag.E6.rank, j ≠ 1 → rhoE6 j ≠ 1 → rhoE6 j ≠ j → ∀ c : K, c ≠ 0 →
      (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1 ∧
          w • (Pi.single (rhoE6 j) 1 : Fin Tag.E6.rank → ℤ) = Pi.single (rhoE6 j) 1 ∧
          (l j : K) * ((a j : K) * δ c) = c ∧
          (l (rhoE6 j) : K) * ((a (rhoE6 j) : K) * δ (σ c)) = σ c) ∨
        (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single (rhoE6 j) 1 ∧
          w • (Pi.single (rhoE6 j) 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1 ∧
          (l (rhoE6 j) : K) * ((a j : K) * δ c) = σ c ∧
          (l j : K) * ((a (rhoE6 j) : K) * δ (σ c)) = c) := by
    intro j hj hρj hjne c hc
    have hj' : j ≠ highNode .E6 := hj
    have hρj' : rhoE6 j ≠ highNode .E6 := hρj
    have hyD : pinnedX .E6 K (Pi.single j 1) c * pinnedX .E6 K (Pi.single (rhoE6 j) 1) (σ c) ∈
        su6Levi σ := by
      rw [hD]
      have h := twistedE6PairX_single_mem_inf (K := K) hσσ (A := E6GraphLevi.setA) (j := j)
        hj hρj c
      have hpl : @permLattice TwistTag.E6.tag TwistTag.E6.perm
          (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) =
            (Pi.single (rhoE6 j) 1 : Fin Tag.E6.rank → ℤ) :=
        permLattice_single _ _
      rw [twistedE6PairX, hpl] at h
      exact h
    refine pair_cases σ l a δ hjne hc (hm hyD (mul_mem (EPilot.pinnedX_single_mem_perpLevi hj' c)
      (EPilot.pinnedX_single_mem_perpLevi hρj' _)) ?_)
    rw [diagField_mul, diagField_pinnedX a δ (isRoot_single _ j),
      diagField_pinnedX a δ (isRoot_single _ (rhoE6 j))]
    exact mul_mem (EPilot.pinnedX_single_mem_perpLevi hj' _)
      (EPilot.pinnedX_single_mem_perpLevi hρj' _)
  have e33 : rhoE6 3 = 3 := by decide
  have e42 : rhoE6 4 = 2 := by decide
  have e50 : rhoE6 5 = 0 := by decide
  have hs05 : (Pi.single (rhoE6 0) 1 : Fin Tag.E6.rank → ℤ) ≠ Pi.single 0 1 := by
    rw [e05]; exact fun h => absurd (E6Pilot.eq_of_single_eq_single_E6 h) (by decide)
  have hs24 : (Pi.single (rhoE6 2) 1 : Fin Tag.E6.rank → ℤ) ≠ Pi.single 2 1 := by
    rw [e24]; exact fun h => absurd (E6Pilot.eq_of_single_eq_single_E6 h) (by decide)
  have c0 := hcase 0 (by decide) (by decide) (by decide)
  have c2 := hcase 2 (by decide) (by decide) (by decide)
  have hA : ∀ {j : Fin Tag.E6.rank}, (∀ c : K, c ≠ 0 →
      (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1 ∧
          w • (Pi.single (rhoE6 j) 1 : Fin Tag.E6.rank → ℤ) = Pi.single (rhoE6 j) 1 ∧
          (l j : K) * ((a j : K) * δ c) = c ∧
          (l (rhoE6 j) : K) * ((a (rhoE6 j) : K) * δ (σ c)) = σ c) ∨
        (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single (rhoE6 j) 1 ∧
          w • (Pi.single (rhoE6 j) 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1 ∧
          (l (rhoE6 j) : K) * ((a j : K) * δ c) = σ c ∧
          (l j : K) * ((a (rhoE6 j) : K) * δ (σ c)) = c)) →
      (Pi.single (rhoE6 j) 1 : Fin Tag.E6.rank → ℤ) ≠ Pi.single j 1 →
      w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1 → ∀ c, δ c = c := by
    intro j hc hne hwj c
    rcases hc 1 one_ne_zero with ⟨-, -, h1, -⟩ | ⟨h1, -, -, -⟩
    · rw [map_one, mul_one] at h1
      by_cases hc0 : c = 0
      · rw [hc0, map_zero]
      rcases hc c hc0 with ⟨-, -, h3, -⟩ | ⟨h3, -, -, -⟩
      · calc δ c = ((l j : K) * (a j : K)) * δ c := by rw [h1, one_mul]
          _ = c := by rw [mul_assoc]; exact h3
      · exact absurd (h3.symm.trans hwj) hne
    · exact absurd (h1.symm.trans hwj) hne
  have hB : ∀ {j : Fin Tag.E6.rank}, (∀ c : K, c ≠ 0 →
      (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1 ∧
          w • (Pi.single (rhoE6 j) 1 : Fin Tag.E6.rank → ℤ) = Pi.single (rhoE6 j) 1 ∧
          (l j : K) * ((a j : K) * δ c) = c ∧
          (l (rhoE6 j) : K) * ((a (rhoE6 j) : K) * δ (σ c)) = σ c) ∨
        (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single (rhoE6 j) 1 ∧
          w • (Pi.single (rhoE6 j) 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1 ∧
          (l (rhoE6 j) : K) * ((a j : K) * δ c) = σ c ∧
          (l j : K) * ((a (rhoE6 j) : K) * δ (σ c)) = c)) →
      (Pi.single (rhoE6 j) 1 : Fin Tag.E6.rank → ℤ) ≠ Pi.single j 1 →
      w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single (rhoE6 j) 1 → ∀ c, δ c = σ c := by
    intro j hc hne hwj c
    rcases hc 1 one_ne_zero with ⟨h1, -, -, -⟩ | ⟨-, -, h1, -⟩
    · exact absurd (h1.symm.trans hwj) (Ne.symm hne)
    · rw [map_one, mul_one, map_one] at h1
      by_cases hc0 : c = 0
      · rw [hc0, map_zero, map_zero]
      rcases hc c hc0 with ⟨h3, -, -, -⟩ | ⟨-, -, h3, -⟩
      · exact absurd (h3.symm.trans hwj) (Ne.symm hne)
      · calc δ c = ((l (rhoE6 j) : K) * (a j : K)) * δ c := by rw [h1, one_mul]
          _ = σ c := by rw [mul_assoc]; exact h3
  have hwB : ∀ {j : Fin Tag.E6.rank}, (∀ c : K, c ≠ 0 →
      (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1 ∧
          w • (Pi.single (rhoE6 j) 1 : Fin Tag.E6.rank → ℤ) = Pi.single (rhoE6 j) 1 ∧
          (l j : K) * ((a j : K) * δ c) = c ∧
          (l (rhoE6 j) : K) * ((a (rhoE6 j) : K) * δ (σ c)) = σ c) ∨
        (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single (rhoE6 j) 1 ∧
          w • (Pi.single (rhoE6 j) 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1 ∧
          (l (rhoE6 j) : K) * ((a j : K) * δ c) = σ c ∧
          (l j : K) * ((a (rhoE6 j) : K) * δ (σ c)) = c)) →
      (Pi.single (rhoE6 j) 1 : Fin Tag.E6.rank → ℤ) ≠ Pi.single j 1 →
      (∀ c, δ c = c) → w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1 := by
    intro j hc hne hδ1
    rcases hc 1 one_ne_zero with ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩
    · exact h1
    · exfalso
      apply hω
      have := hB hc hne h1 ω
      rw [hδ1] at this
      exact this.symm
  rcases c0 1 one_ne_zero with ⟨hw0, -, -, -⟩ | ⟨hw0, -, -, -⟩
  ·
    have hδ1 := hA c0 hs05 hw0
    have hw2 := hwB c2 hs24 hδ1
    obtain ⟨-, hw5, hs0, hs5⟩ : _ ∧ w • (Pi.single (rhoE6 0) 1 : Fin Tag.E6.rank → ℤ) =
        Pi.single (rhoE6 0) 1 ∧ (l 0 : K) * ((a 0 : K) * δ 1) = 1 ∧
          (l (rhoE6 0) : K) * ((a (rhoE6 0) : K) * δ (σ 1)) = σ 1 := by
      rcases c0 1 one_ne_zero with h | ⟨h1, -, -, -⟩
      · exact h
      · exact absurd (h1.symm.trans hw0) hs05
    obtain ⟨-, hw4, hs2, hs4⟩ : _ ∧ w • (Pi.single (rhoE6 2) 1 : Fin Tag.E6.rank → ℤ) =
        Pi.single (rhoE6 2) 1 ∧ (l 2 : K) * ((a 2 : K) * δ 1) = 1 ∧
          (l (rhoE6 2) : K) * ((a (rhoE6 2) : K) * δ (σ 1)) = σ 1 := by
      rcases c2 1 one_ne_zero with h | ⟨h1, -, -, -⟩
      · exact h
      · exact absurd (h1.symm.trans hw2) hs24
    refine ⟨hδ1, ?_⟩
    have hwall : ∀ j, j ≠ highNode .E6 →
        w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1 := by
      intro j hj
      fin_cases j
      · exact hw0
      · exact absurd rfl hj
      · exact hw2
      · exact hw3
      · rw [e24] at hw4
        exact hw4
      · rw [e05] at hw5
        exact hw5
    have hla : ∀ j, j ≠ highNode .E6 → l j * a j = 1 := by
      intro j hj
      refine Units.ext ?_
      rw [Units.val_mul, Units.val_one]
      rw [map_one, mul_one] at hs0 hs2
      rw [map_one, map_one, mul_one] at hs4 hs5
      fin_cases j
      · exact hs0
      · exact absurd rfl hj
      · exact hs2
      · exact hla3
      · rw [e24] at hs4
        exact hs4
      · rw [e05] at hs5
        exact hs5
    have hm' := rootDiagUnit_canonicalRep_mul_mem_highRootSL2 hh hwall hla
    have e : g * rootDiagUnit .E6 a = (rootDiagUnit .E6 l * u * (rootDiagUnit .E6 l)⁻¹) *
        (rootDiagUnit .E6 l * canonicalRep (coxeterSystem Tag.E6) K w * rootDiagUnit .E6 a) *
          (rootDiagUnit .E6 a⁻¹ * v * (rootDiagUnit .E6 a⁻¹)⁻¹) := by
      rw [hgdec, ← rootDiagUnit_inv, inv_inv]
      group
    rw [e]
    exact mul_mem (mul_mem (hJ hu') hm') (conj_rootDiagUnit_mem_highRootSL2 _ (hJ hvr))
  ·
    exfalso
    have hδσ1 := hB c0 hs05 hw0
    have hw2 : w • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) = Pi.single (rhoE6 2) 1 := by
      rcases c2 1 one_ne_zero with ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩
      · exact absurd ((hδσ1 ω).symm.trans (hA c2 hs24 h1 ω)) hω
      · exact h1
    obtain ⟨hw5, -, -⟩ : w • (Pi.single (rhoE6 0) 1 : Fin Tag.E6.rank → ℤ) = Pi.single 0 1 ∧
        True ∧ True := by
      rcases c0 1 one_ne_zero with ⟨h1, -, -, -⟩ | ⟨-, h2', -, -⟩
      · exact absurd (h1.symm.trans hw0) (Ne.symm hs05)
      · exact ⟨h2', trivial, trivial⟩
    obtain ⟨hw4, -, -⟩ : w • (Pi.single (rhoE6 2) 1 : Fin Tag.E6.rank → ℤ) = Pi.single 2 1 ∧
        True ∧ True := by
      rcases c2 1 one_ne_zero with ⟨h1, -, -, -⟩ | ⟨-, h2', -, -⟩
      · exact absurd (h1.symm.trans hw2) (Ne.symm hs24)
      · exact ⟨h2', trivial, trivial⟩
    refine false_of_smul_single_perm (w := w) fun j hj => ?_
    fin_cases j
    · exact hw5
    · exact absurd rfl hj
    · exact hw4
    · change w • (Pi.single (rhoE6 3) 1 : Fin Tag.E6.rank → ℤ) = Pi.single 3 1
      rw [e33]
      exact hw3
    · change w • (Pi.single (rhoE6 4) 1 : Fin Tag.E6.rank → ℤ) = Pi.single 4 1
      rw [e42]
      rw [e24] at hw2
      exact hw2
    · change w • (Pi.single (rhoE6 5) 1 : Fin Tag.E6.rank → ℤ) = Pi.single 5 1
      rw [e50]
      rw [e05] at hw0
      exact hw0

end Core

end CFSG.SeitzReduction.TwistedE6Pilot
