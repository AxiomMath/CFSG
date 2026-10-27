module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoOffender22
public import CFSG.Quasithin.Background.HMathieuFacts22Base

public section

namespace CFSG.ASVolI.AppH

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1
  CFSG.Monster.Code

private theorem chain_card {V : Type*} [CommGroup V] {P : Type*} [Group P] [DecidableEq P]
    {aut : P →* MulAut V} {l : List P} {A : Subgroup (MulAut V)} (hA : IsChainSub aut l A)
    (hinj : Function.Injective aut) (hl : IndepList l) : Nat.card A = 2 ^ l.length := by
  have hset : (A : Set (MulAut V)) = aut '' ((subprods l).toFinset : Set P) := by
    ext a
    simp only [SetLike.mem_coe, Set.mem_image, List.coe_toFinset, Set.mem_ofPred_eq]
    rw [hA a]
    exact ⟨fun ⟨s, hs, h⟩ => ⟨s, hs, h.symm⟩, fun ⟨s, hs, h⟩ => ⟨s, hs, h.symm⟩⟩
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset, Set.ncard_image_of_injective _ hinj,
    Set.ncard_coe_finset, List.toFinset_card_of_nodup (nodup_subprods hl), length_subprods]

theorem chain_shape22 {V : Type*} [CommGroup V] [Finite V] (e : V ≃* W10)
    {A : Subgroup (MulAut V)} (hAR : A.map (congrHom e) ≤ psi22.range)
    (hA2 : IsElemAbelian2 A) (hA1 : A ≠ ⊥) (hF : rkIdx (fixV A) ≤ rk ↥A + 1) :
    ∃ (g : ↥mog22plus) (l : List T22s2.Elem), IndepList l ∧ l.length = 4 ∧
      (∀ s ∈ l, fixesOff22 s = true) ∧ IsChainSub (chainAut e psi22 phi22 g) l A := by
  have hpg : IsPGroup 2 A := isPGroup_two_of_sq_eq_one fun a => Subtype.ext (hA2.2 a a.2)
  have hcardA : Nat.card A = 2 ^ rk ↥A := card_eq_two_pow_of_isPGroup hpg
  have hk1 : 1 ≤ rk ↥A := by
    have h0 : rk ↥A ≠ 0 := fun h0 => hA1 ((rk_eq_zero_iff_of_isPGroup hpg).1 h0)
    omega
  have hk5 : rk ↥A ≤ 5 := by
    by_contra h
    push Not at h
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Finite A := Nat.finite_of_card_ne_zero (by rw [hcardA]; positivity)
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 (G := A) (n := 6)
      (by rw [hcardA]; exact Nat.pow_dvd_pow 2 (by omega))
    set B := K.map A.subtype
    have hBA : B ≤ A := Subgroup.map_subtype_le K
    have hBcard : Nat.card B = 2 ^ 6 := by
      rw [Subgroup.card_map_of_injective A.subtype_injective, hK]
    have hBe : IsElemAbelian2 B :=
      ⟨fun a ha b hb => hA2.1 a (hBA ha) b (hBA hb),
        fun a ha => hA2.2 a (hBA ha)⟩
    have hBR : B.map (congrHom e) ≤ psi22.range := (Subgroup.map_mono hBA).trans hAR
    obtain ⟨g, l, -, hpred, -⟩ :=
      exists_chainModel psi22 rho10_mog22plus_injective phi22 (T22s2.toSub_injective _ _)
        card_T22s2 (fun _ h1 h2 => T22s2.mem_invols h1 h2) (greedyOff22 6 (by simp))
        e hBR hBe hBcard
    have h65 : (6 : ℕ) ≤ 5 := by
      have := hpred
      simp only [predOff22, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1
    omega
  have hkmem : rk ↥A ∈ [1, 2, 3, 4, 5, 6] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  obtain ⟨g, l, hind, hpred, hchain⟩ :=
    exists_chainModel psi22 rho10_mog22plus_injective phi22 (T22s2.toSub_injective _ _)
      card_T22s2 (fun _ h1 h2 => T22s2.mem_invols h1 h2) (greedyOff22 (rk ↥A) hkmem)
      e hAR hA2 hcardA
  have hlen : l.length = rk ↥A := by
    have h1 := chain_card hchain (chainAut22_injective e g) hind
    rw [hcardA] at h1
    exact (Nat.pow_right_injective (le_refl 2) h1).symm
  have hd : rkIdx (fixV A) = 10 - Nat.log 2 (fixMasks 10 act22s2 l).length :=
    (MaskCoords.ofEquiv (twistEquiv e psi22 g)).rkIdx_of_card (card_fixV (chainAct22 e g) hchain)
  have hF' := hF
  rw [hd] at hF'
  simp only [predOff22, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, bne_iff_ne, ne_eq, beq_iff_eq] at hpred
  obtain ⟨-, hrest⟩ := hpred
  rcases hrest with hnot | hboth
  · exact absurd hF' hnot
  · obtain ⟨hk4, hall⟩ := hboth
    exact ⟨g, l, hind, by rw [hlen, hk4], List.all_eq_true.1 hall, hchain⟩

end CFSG.ASVolI.AppH

