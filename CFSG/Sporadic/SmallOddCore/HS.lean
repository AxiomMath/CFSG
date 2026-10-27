module

public import CFSG.Sporadic.SmallOddCore.HSCheck
public import CFSG.Sporadic.SmallOddCore.Normalizing
public import CFSG.Sporadic.SmallOddCore.TableFacts
public import CFSG.Sporadic.Schreier.PairHSOrder

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Certificates

theorem hs_groupData :
    GroupData 3850 hsP hsPGTbls hsGen hsSift where
  lt := by norm_num
  rep := by
    intro l hl
    have hl2 : l < 2 := by simpa [hsPGTbls] using hl
    interval_cases l
    · rw [show hsPGTbls[0]! = hsStrongArrs[0]!.map UInt32.ofNat by simp [hsPGTbls]]
      exact rep_arrayMap_ofNat (by norm_num) (rep_hsStrongPerm (by norm_num))
    · rw [show hsPGTbls[1]! = hsStrongArrs[1]!.map UInt32.ofNat by simp [hsPGTbls]]
      exact rep_arrayMap_ofNat (by norm_num) (rep_hsStrongPerm (by norm_num))
  gen := by
    rw [hsP]
    congr 1
    ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image, Set.mem_ofPred_eq]
    have hsz : hsPGTbls.size = 2 := rfl
    rw [hsz]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, rfl⟩
      · exact ⟨1, by norm_num, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      interval_cases l
      · exact Or.inl rfl
      · exact Or.inr rfl
  sift := by
    intro T g hT
    rw [hsP_eq_original]
    exact siftA_iff_mem_originalSubgroup hsChainArrays (by norm_num) PairHS.chain_check.1
      (co2Rep_natArr_iff.2 hT)

theorem hs_primes : ∀ r ∈ hsRows, ∀ q : ℕ, q.Prime → q ∣ r.centOrder → q ≠ 2 →
    q ∈ r.oddPrimes := by
  intro r hr q hq hdvd hq2
  simp only [hsRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · obtain ⟨f, hf, rfl⟩ := eq_of_prime_dvd_prod hq [(2, 9), (3, 1), (5, 1)] (by norm_num)
      (by simpa using hdvd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;> simp_all
  · obtain ⟨f, hf, rfl⟩ := eq_of_prime_dvd_prod hq [(2, 6), (3, 2), (5, 1)] (by norm_num)
      (by simpa using hdvd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;> simp_all
  · obtain ⟨f, hf, rfl⟩ := eq_of_prime_dvd_prod hq [(2, 7), (3, 2), (5, 1), (7, 1)] (by norm_num)
      (by simpa using hdvd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl <;> simp_all
  · obtain ⟨f, hf, rfl⟩ := eq_of_prime_dvd_prod hq [(2, 7), (3, 1), (5, 1)] (by norm_num)
      (by simpa using hdvd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;> simp_all

theorem hs_sylowOrder : hsSylowOrder = 2 ^ (2 * 44352000).factorization 2 := by
  rw [show 2 * 44352000 = 2 ^ 10 * 86625 by norm_num,
    factorization_two_pow_mul (by norm_num)]
  rfl

theorem hs_stab :
    ∀ x : Fin 3850, x ≠ 0 → ∃ s ∈ hsP, s 0 = 0 ∧ s x ≠ x :=
  hs_stab_facts

theorem hs_centralizer_eq_bot :
    centralizer (hsP : Set (Equiv.Perm (Fin 3850))) = ⊥ := by
  have h0 : 0 < hsChain.baseCount := by rw [hsChain_baseCount]; norm_num
  have hb : hsChain.base.get ⟨0, h0⟩ = 0 := by
    apply Fin.ext
    have := hsChain_base
    have h1 : (hsChain.base.toList.map Fin.val)[0]'(by simp [h0]) = 0 := by simp [this]
    simpa [Vector.get_eq_getElem] using h1
  have htrans := transitive_of_orbitSize hsChain hsChain_valid.1 h0
    (by rw [hsChain_orbitSize]; rfl)
  rw [hb, ← hsP_eq_original] at htrans
  exact centralizer_eq_bot_of_transitive 0 htrans hs_stab

theorem hs_normalizing_model :
    hsU ^ 2 = 1 ∧ hsU ≠ 1 ∧ hsU ∉ hsP ∧ hsP.map (MulAut.conj hsU).toMonoidHom = hsP ∧
      centralizer (hsP : Set (Equiv.Perm (Fin 3850))) = ⊥ ∧
      (∀ x, x ∈ hsR ↔ x ∈ hsP ∨ x * hsU ∈ hsP) ∧ hsP ⊓ zpowers hsU = ⊥ ∧
      (hsP.subgroupOf hsR).Normal ∧ Nat.card hsR = 88704000 ∧
      ∃ φ : hsR →* MulAut hsP, Function.Injective φ ∧
        (∀ (x : hsR) (p : hsP),
          ((φ x p : hsP) : Equiv.Perm (Fin 3850)) = (x : Equiv.Perm (Fin 3850)) * p * (x : _)⁻¹) ∧
        (hsP.subgroupOf hsR).map φ = (MulAut.conj : hsP →* MulAut hsP).range ∧
        Function.Injective (MulAut.conj : hsP →* MulAut hsP) := by
  obtain ⟨hU2, hU1, hUP, hUn⟩ := hs_u_facts
  obtain ⟨hmap, hRmem, hinf, hnormal, hcard, φ, hφinj, hφ, himage, hconjinj⟩ :=
    normalizing_model hU2 hUP hUn hs_centralizer_eq_bot
  refine ⟨hU2, hU1, hUP, hmap, hs_centralizer_eq_bot, hRmem, hinf, hnormal, ?_, φ, hφinj, hφ,
    himage, hconjinj⟩
  show Nat.card ↥(hsP ⊔ zpowers hsU) = 88704000
  rw [hcard, card_hsP]

theorem hs_involution_centralizers :
    hsS ≤ hsR ∧ Nat.card hsS = 1024 ∧
      (∃ T : Sylow 2 hsR, (T : Subgroup hsR) = hsS.subgroupOf hsR) ∧
      (∀ r ∈ hsRows, tp 3850 r.rep ∈ hsR ∧ orderOf (tp 3850 r.rep) = 2 ∧
        (r.outer = true ↔ tp 3850 r.rep ∉ hsP) ∧
        hsC r = hsP ⊓ centralizer ({tp 3850 r.rep} : Set _) ∧
        Nat.card ↥(hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850)))) =
          r.centOrder ∧
        (conjClass hsP (tp 3850 r.rep)).ncard = r.classSize) ∧
      (∀ t ∈ hsR, orderOf t = 2 → ∃ r ∈ hsRows, ∃ g ∈ hsP, t = g * tp 3850 r.rep * g⁻¹) ∧
      (∀ i j : Fin hsRows.length, (∃ g ∈ hsP,
        tp 3850 hsRows[j].rep = g * tp 3850 hsRows[i].rep * g⁻¹) → i = j) ∧
      hsRows.map (fun r => (r.outer, r.classSize, r.centOrder)) =
        [(false, 5775, 7680), (false, 15400, 2880), (true, 1100, 40320),
          (true, 23100, 1920)] ∧
      (∀ t ∈ hsR, orderOf t = 2 →
        CFSG.oddCore ↥(hsP ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 3850)))) = ⊥) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSR, hS⟩ := hs_sylow_facts
  have hrows := hs_rows_facts
  have hcover := hs_cover
  have hodd : ∀ t ∈ hsR, orderOf t = 2 →
      CFSG.oddCore ↥(hsP ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 3850)))) = ⊥ := by
    intro t ht ht2
    obtain ⟨r, hr, g, hg, rfl⟩ := hcover t ht ht2
    exact oddCore_inf_centralizer_conj hsP hg (hrows r hr).2.2.2.2.2.2.2
  have hRcard' : Nat.card hsR = 88704000 := hs_normalizing_model.2.2.2.2.2.2.2.2.1
  have hSR' : hsS ≤ hsR := hSR
  refine ⟨hSR, hS, ?_, fun r hr => ?_, hcover, ?_, rfl, hodd⟩
  · refine ⟨Sylow.ofCard (hsS.subgroupOf hsR) ?_, Sylow.coe_ofCard _ _⟩
    rw [Nat.card_congr (subgroupOfEquivOfLe hSR').toEquiv, hS, hRcard',
      show (88704000 : ℕ) = 2 ^ 10 * 86625 by norm_num,
      factorization_two_pow_mul (by norm_num)]
    norm_num
  · obtain ⟨-, h1, h2, h3, h4, h5, h6, -⟩ := hrows r hr
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  ·
    intro i j ⟨g, hg, hij⟩
    have hinv : ∀ r ∈ hsRows, ∀ r' ∈ hsRows, (∃ g ∈ hsP,
        tp 3850 r'.rep = g * tp 3850 r.rep * g⁻¹) →
          r.outer = r'.outer ∧ r.centOrder = r'.centOrder := by
      rintro r hr r' hr' ⟨g, hg, hgr⟩
      obtain ⟨-, -, -, hout, -, hcent, -, -⟩ := hrows r hr
      obtain ⟨-, -, -, hout', -, hcent', -, -⟩ := hrows r' hr'
      constructor
      · have hmem : tp 3850 r.rep ∈ hsP ↔ tp 3850 r'.rep ∈ hsP := by
          rw [hgr]
          constructor
          · intro h; exact hsP.mul_mem (hsP.mul_mem hg h) (hsP.inv_mem hg)
          · intro h
            have := hsP.mul_mem (hsP.mul_mem (hsP.inv_mem hg) h) hg
            rwa [show g⁻¹ * (g * tp 3850 r.rep * g⁻¹) * g = tp 3850 r.rep by group] at this
        cases hro : r.outer <;> cases hro' : r'.outer
        · rfl
        · rw [hro'] at hout'
          rw [hro, Bool.false_eq_true, false_iff, not_not] at hout
          exact absurd (hmem.1 hout) (hout'.1 rfl)
        · rw [hro] at hout
          rw [hro', Bool.false_eq_true, false_iff, not_not] at hout'
          exact absurd (hmem.2 hout') (hout.1 rfl)
        · rfl
      · rw [← hcent, ← hcent', hgr, inf_centralizer_conj hsP hg,
          Subgroup.card_map_of_injective (MulAut.conj g).injective]
    have h := hinv _ (List.getElem_mem _) _ (List.getElem_mem _) ⟨g, hg, hij⟩
    have hnodup : (hsRows.map fun r => (r.outer, r.centOrder)).Nodup := by decide
    have hi : (i : ℕ) < (hsRows.map fun r => (r.outer, r.centOrder)).length := by simp
    have hj : (j : ℕ) < (hsRows.map fun r => (r.outer, r.centOrder)).length := by simp
    have hij' : (hsRows.map fun r => (r.outer, r.centOrder))[(i : ℕ)] =
        (hsRows.map fun r => (r.outer, r.centOrder))[(j : ℕ)] := by
      simp only [List.getElem_map]
      rw [h.1, h.2]
    exact Fin.ext (hnodup.getElem_inj_iff.mp hij')

end CFSG.Sporadic.SmallOddCore
