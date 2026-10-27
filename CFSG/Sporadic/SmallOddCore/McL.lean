module

public import CFSG.Sporadic.SmallOddCore.McLCheck
public import CFSG.Sporadic.SmallOddCore.Normalizing
public import CFSG.Sporadic.SmallOddCore.TableFacts
public import CFSG.Sporadic.Schreier.PairMcLOrder

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Certificates

theorem mcl_groupData :
    GroupData 275 mclP mclPGTbls mclGen mclSift where
  lt := by norm_num
  rep := by
    intro l hl
    have hl2 : l < 2 := by simpa [mclPGTbls] using hl
    interval_cases l
    · rw [show mclPGTbls[0]! = mclStrongArrs[0]!.map UInt32.ofNat by simp [mclPGTbls]]
      exact rep_arrayMap_ofNat (by norm_num) (rep_mclStrongPerm (by norm_num))
    · rw [show mclPGTbls[1]! = mclStrongArrs[1]!.map UInt32.ofNat by simp [mclPGTbls]]
      exact rep_arrayMap_ofNat (by norm_num) (rep_mclStrongPerm (by norm_num))
  gen := by
    rw [mclP]
    congr 1
    ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image, Set.mem_ofPred_eq]
    have hsz : mclPGTbls.size = 2 := rfl
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
    rw [mclP_eq_original]
    exact siftA_iff_mem_originalSubgroup mclChainArrays (by norm_num) PairMcL.chain_check.1
      (co2Rep_natArr_iff.2 hT)

theorem mcl_primes : ∀ r ∈ mclRows, ∀ q : ℕ, q.Prime → q ∣ r.centOrder → q ≠ 2 →
    q ∈ r.oddPrimes := by
  intro r hr q hq hdvd hq2
  simp only [mclRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · obtain ⟨f, hf, rfl⟩ := eq_of_prime_dvd_prod hq [(2, 7), (3, 2), (5, 1), (7, 1)] (by norm_num)
      (by simpa using hdvd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl <;> simp_all
  · obtain ⟨f, hf, rfl⟩ := eq_of_prime_dvd_prod hq [(2, 4), (3, 2), (5, 1), (11, 1)] (by norm_num)
      (by simpa using hdvd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl <;> simp_all

theorem mcl_sylowOrder : mclSylowOrder = 2 ^ (2 * 898128000).factorization 2 := by
  rw [show 2 * 898128000 = 2 ^ 8 * 7016625 by norm_num,
    factorization_two_pow_mul (by norm_num)]
  rfl

theorem mcl_stab :
    ∀ x : Fin 275, x ≠ 0 → ∃ s ∈ mclP, s 0 = 0 ∧ s x ≠ x := by
  have h := mcl_stabOK
  simp only [mclStabOK, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq, List.mem_range] at h
  obtain ⟨hst, hmove⟩ := h
  intro x hx
  obtain ⟨T, hT, hTx⟩ := (hmove x.val x.isLt).resolve_left (fun h => hx (Fin.ext h))
  have hT' := hT
  simp only [mclStabTbls, List.mem_filter, List.mem_map, List.mem_range] at hT'
  obtain ⟨⟨j, hj, rfl⟩, -⟩ := hT'
  have hrep := rep_arrayMap_ofNat (n := 275) (by norm_num) (rep_mclStrongPerm hj)
  obtain ⟨hsift, h1⟩ := hst _ hT
  refine ⟨mclStrongPerm j, (mcl_groupData.sift _ _ hrep).1 hsift, ?_, ?_⟩
  · apply Fin.ext
    have := hrep 0 (by norm_num)
    rw [idx_of_lt _ (by norm_num), h1, Equiv.Perm.smul_def] at this
    rw [show (0 : Fin 275) = ⟨0, by norm_num⟩ from rfl]
    exact this.symm
  · intro hfix
    apply hTx
    have := hrep x.val x.isLt
    rw [idx_of_lt _ x.isLt, Equiv.Perm.smul_def, Fin.eta, hfix] at this
    exact this

theorem mcl_centralizer_eq_bot :
    centralizer (mclP : Set (Equiv.Perm (Fin 275))) = ⊥ := by
  have h0 : 0 < mclChain.baseCount := by rw [mclChain_baseCount]; norm_num
  have hb : mclChain.base.get ⟨0, h0⟩ = 0 := by
    apply Fin.ext
    have := mclChain_base
    have h1 : (mclChain.base.toList.map Fin.val)[0]'(by simp [h0]) = 0 := by simp [this]
    simpa [Vector.get_eq_getElem] using h1
  have htrans := transitive_of_orbitSize mclChain mclChain_valid.1 h0
    (by rw [mclChain_orbitSize]; rfl)
  rw [hb, ← mclP_eq_original] at htrans
  exact centralizer_eq_bot_of_transitive 0 htrans mcl_stab

theorem mcl_normalizing_model :
    mclU ^ 2 = 1 ∧ mclU ≠ 1 ∧ mclU ∉ mclP ∧ mclP.map (MulAut.conj mclU).toMonoidHom = mclP ∧
      centralizer (mclP : Set (Equiv.Perm (Fin 275))) = ⊥ ∧
      (∀ x, x ∈ mclR ↔ x ∈ mclP ∨ x * mclU ∈ mclP) ∧ mclP ⊓ zpowers mclU = ⊥ ∧
      (mclP.subgroupOf mclR).Normal ∧ Nat.card mclR = 1796256000 ∧
      ∃ φ : mclR →* MulAut mclP, Function.Injective φ ∧
        (∀ (x : mclR) (p : mclP),
          ((φ x p : mclP) : Equiv.Perm (Fin 275)) = (x : Equiv.Perm (Fin 275)) * p * (x : _)⁻¹) ∧
        (mclP.subgroupOf mclR).map φ = (MulAut.conj : mclP →* MulAut mclP).range ∧
        Function.Injective (MulAut.conj : mclP →* MulAut mclP) := by
  obtain ⟨hU2, hU1, hUP, hmap', -, -, -, -, -, -, -⟩ :=
    centData_spec mcl_groupData card_mclP mcl_primes mcl_sylowOrder mcl_centDataOK
  have hUn : ∀ p ∈ mclP, mclU * p * mclU⁻¹ ∈ mclP := fun p hp => by
    rw [← hmap']
    exact ⟨p, hp, rfl⟩
  obtain ⟨hmap, hRmem, hinf, hnormal, hcard, φ, hφinj, hφ, himage, hconjinj⟩ :=
    normalizing_model hU2 hUP hUn mcl_centralizer_eq_bot
  refine ⟨hU2, hU1, hUP, hmap, mcl_centralizer_eq_bot, hRmem, hinf, hnormal, ?_, φ, hφinj, hφ,
    himage, hconjinj⟩
  show Nat.card ↥(mclP ⊔ zpowers (tp 275 mclOuterTbl)) = 1796256000
  rw [hcard, card_mclP]

theorem mcl_involution_centralizers :
    mclS ≤ mclR ∧ Nat.card mclS = 256 ∧
      (∃ T : Sylow 2 mclR, (T : Subgroup mclR) = mclS.subgroupOf mclR) ∧
      (∀ r ∈ mclRows, tp 275 r.rep ∈ mclR ∧ orderOf (tp 275 r.rep) = 2 ∧
        (r.outer = true ↔ tp 275 r.rep ∉ mclP) ∧
        mclC r = mclP ⊓ centralizer ({tp 275 r.rep} : Set _) ∧
        Nat.card ↥(mclP ⊓ centralizer ({tp 275 r.rep} : Set (Equiv.Perm (Fin 275)))) =
          r.centOrder ∧
        (conjClass mclP (tp 275 r.rep)).ncard = r.classSize) ∧
      (∀ t ∈ mclR, orderOf t = 2 → ∃ r ∈ mclRows, ∃ g ∈ mclP, t = g * tp 275 r.rep * g⁻¹) ∧
      (∀ i j : Fin mclRows.length, (∃ g ∈ mclP,
        tp 275 mclRows[j].rep = g * tp 275 mclRows[i].rep * g⁻¹) → i = j) ∧
      mclRows.map (fun r => (r.outer, r.classSize, r.centOrder)) =
        [(false, 22275, 40320), (true, 113400, 7920)] ∧
      (∀ t ∈ mclR, orderOf t = 2 →
        CFSG.oddCore ↥(mclP ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 275)))) = ⊥) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, hRcard, hSR, hScard, hrows, hcover, hodd⟩ :=
    centData_spec mcl_groupData card_mclP mcl_primes mcl_sylowOrder mcl_centDataOK
  have hRcard' : Nat.card mclR = 1796256000 := hRcard
  have hS : Nat.card mclS = 256 := hScard
  have hSR' : mclS ≤ mclR := hSR
  refine ⟨hSR, hS, ?_, fun r hr => ?_, hcover, ?_, rfl, hodd⟩
  · refine ⟨Sylow.ofCard (mclS.subgroupOf mclR) ?_, Sylow.coe_ofCard _ _⟩
    rw [Nat.card_congr (subgroupOfEquivOfLe hSR').toEquiv, hS, hRcard',
      show (1796256000 : ℕ) = 2 ^ 8 * 7016625 by norm_num,
      factorization_two_pow_mul (by norm_num)]
    norm_num
  · obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hrows r hr
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  ·
    intro i j ⟨g, hg, hij⟩
    have hinv : ∀ r ∈ mclRows, ∀ r' ∈ mclRows, (∃ g ∈ mclP,
        tp 275 r'.rep = g * tp 275 r.rep * g⁻¹) →
          r.outer = r'.outer ∧ r.centOrder = r'.centOrder := by
      rintro r hr r' hr' ⟨g, hg, hgr⟩
      obtain ⟨-, -, hout, -, hcent, -, -⟩ := hrows r hr
      obtain ⟨-, -, hout', -, hcent', -, -⟩ := hrows r' hr'
      constructor
      · have hmem : tp 275 r.rep ∈ mclP ↔ tp 275 r'.rep ∈ mclP := by
          rw [hgr]
          constructor
          · intro h; exact mclP.mul_mem (mclP.mul_mem hg h) (mclP.inv_mem hg)
          · intro h
            have := mclP.mul_mem (mclP.mul_mem (mclP.inv_mem hg) h) hg
            rwa [show g⁻¹ * (g * tp 275 r.rep * g⁻¹) * g = tp 275 r.rep by group] at this
        cases hro : r.outer <;> cases hro' : r'.outer
        · rfl
        · rw [hro'] at hout'
          rw [hro, Bool.false_eq_true, false_iff, not_not] at hout
          exact absurd (hmem.1 hout) (hout'.1 rfl)
        · rw [hro] at hout
          rw [hro', Bool.false_eq_true, false_iff, not_not] at hout'
          exact absurd (hmem.2 hout') (hout.1 rfl)
        · rfl
      · rw [← hcent, ← hcent', hgr, inf_centralizer_conj mclP hg,
          Subgroup.card_map_of_injective (MulAut.conj g).injective]
    have h := hinv _ (List.getElem_mem _) _ (List.getElem_mem _) ⟨g, hg, hij⟩
    have hnodup : (mclRows.map fun r => (r.outer, r.centOrder)).Nodup := by decide
    have hi : (i : ℕ) < (mclRows.map fun r => (r.outer, r.centOrder)).length := by simp
    have hj : (j : ℕ) < (mclRows.map fun r => (r.outer, r.centOrder)).length := by simp
    have hij' : (mclRows.map fun r => (r.outer, r.centOrder))[(i : ℕ)] =
        (mclRows.map fun r => (r.outer, r.centOrder))[(j : ℕ)] := by
      simp only [List.getElem_map]
      rw [h.1, h.2]
    exact Fin.ext (hnodup.getElem_inj_iff.mp hij')

end CFSG.Sporadic.SmallOddCore
