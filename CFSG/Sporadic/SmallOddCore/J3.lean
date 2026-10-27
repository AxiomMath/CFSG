module

public import CFSG.Sporadic.SmallOddCore.J3Check
public import CFSG.Sporadic.SmallOddCore.Normalizing
public import CFSG.Sporadic.Schreier.PairJ3Order
public import CFSG.Sporadic.SmallOddCore.J3CheckInputs

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Certificates
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.Blueprint

private theorem rep_map_ofNat {n : ℕ} (hn : n < 2 ^ 32) {a : Array ℕ} {g : Equiv.Perm (Fin n)}
    (h : CFSG.Monster.B.Co2.Rep n a g) : Th.Rep n (a.map UInt32.ofNat) g := by
  intro i hi
  have h1 := h ⟨i, hi⟩
  rw [idx_of_lt _ hi]
  unfold ap
  by_cases hs : i < a.size
  · rw [getElem!_pos (a.map UInt32.ofNat) i (by simpa using hs), Array.getElem_map,
      UInt32.toNat_ofNat', ← getElem!_pos a i hs, h1, Nat.mod_eq_of_lt ((g _).isLt.trans hn)]
    rfl
  · rw [getElem!_neg (a.map UInt32.ofNat) i (by simpa using hs)]
    rw [getElem!_neg a i hs] at h1
    rw [show (g • (⟨i, hi⟩ : Fin n) : Fin n) = g ⟨i, hi⟩ from rfl, ← h1]
    rfl

theorem j3_groupData :
    GroupData 6156 j3P j3PGTbls j3Gen j3Sift where
  lt := by norm_num
  rep := by
    intro l hl
    have hl2 : l < 2 := by simpa [j3PGTbls] using hl
    interval_cases l
    · rw [show j3PGTbls[0]! = j3StrongArrs[0]!.map UInt32.ofNat by simp [j3PGTbls]]
      exact rep_map_ofNat (by norm_num) (rep_j3StrongPerm (by norm_num))
    · rw [show j3PGTbls[1]! = j3StrongArrs[1]!.map UInt32.ofNat by simp [j3PGTbls]]
      exact rep_map_ofNat (by norm_num) (rep_j3StrongPerm (by norm_num))
  gen := by
    rw [j3P]
    congr 1
    ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image, Set.mem_ofPred_eq]
    have hsz : j3PGTbls.size = 2 := rfl
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
    rw [j3P_eq_original]
    exact siftA_iff_mem_originalSubgroup j3ChainArrays (by norm_num) PairJ3.chain_check.1
      (co2Rep_natArr_iff.2 hT)

theorem factorization_100465920 : (100465920 : ℕ).factorization 2 = 8 := by
  rw [show (100465920 : ℕ) = 2 ^ 8 * 392445 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

private theorem dvd_of_dvd_two_pow_mul {q a m : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (h : q ∣ 2 ^ a * m) : q ∣ m := by
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)) hq2
  · exact h

theorem j3_primes : ∀ r ∈ j3Rows, ∀ q : ℕ, q.Prime → q ∣ r.centOrder → q ≠ 2 →
    q ∈ r.oddPrimes := by
  intro r hr q hq hdvd hq2
  simp only [j3Rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have h := dvd_of_dvd_two_pow_mul (a := 7) (m := 15) hq hq2 (by simpa using hdvd)
    have hle := Nat.le_of_dvd (by norm_num) h
    interval_cases q <;> simp_all (config := { decide := true })
  · have h := dvd_of_dvd_two_pow_mul (a := 4) (m := 153) hq hq2 (by simpa using hdvd)
    have hle := Nat.le_of_dvd (by norm_num) h
    interval_cases q <;> simp_all (config := { decide := true })

theorem j3_sylowOrder : j3SylowOrder = 2 ^ (2 * 50232960).factorization 2 := by
  rw [show 2 * 50232960 = 100465920 by norm_num, factorization_100465920]
  rfl

theorem j3_stab :
    ∀ x : Fin 6156, x ≠ 0 → ∃ s ∈ j3P, s 0 = 0 ∧ s x ≠ x :=
  j3_stabFact

theorem j3_centralizer_eq_bot :
    centralizer (j3P : Set (Equiv.Perm (Fin 6156))) = ⊥ := by
  have h0 : 0 < j3Chain.baseCount := by rw [j3Chain_baseCount]; norm_num
  have hb : j3Chain.base.get ⟨0, h0⟩ = 0 := by
    apply Fin.ext
    have := j3Chain_base
    have h1 : (j3Chain.base.toList.map Fin.val)[0]'(by simp [h0]) = 0 := by simp [this]
    simpa [Vector.get_eq_getElem] using h1
  have htrans := transitive_of_orbitSize j3Chain j3Chain_valid.1 h0
    (by rw [j3Chain_orbitSize]; rfl)
  rw [hb, ← j3P_eq_original] at htrans
  exact centralizer_eq_bot_of_transitive 0 htrans j3_stab

theorem ctuc_j3_normalizing_involution_permutation_model :
    j3u ^ 2 = 1 ∧ j3u ≠ 1 ∧ j3u ∉ j3P ∧ j3P.map (MulAut.conj j3u).toMonoidHom = j3P ∧
      centralizer (j3P : Set (Equiv.Perm (Fin 6156))) = ⊥ ∧
      (∀ x, x ∈ j3R ↔ x ∈ j3P ∨ x * j3u ∈ j3P) ∧ j3P ⊓ zpowers j3u = ⊥ ∧
      (j3P.subgroupOf j3R).Normal ∧ Nat.card j3R = 100465920 ∧
      ∃ φ : j3R →* MulAut j3P, Function.Injective φ ∧
        (∀ (x : j3R) (p : j3P),
          ((φ x p : j3P) : Equiv.Perm (Fin 6156)) = (x : Equiv.Perm (Fin 6156)) * p * (x : _)⁻¹) ∧
        (j3P.subgroupOf j3R).map φ = (MulAut.conj : j3P →* MulAut j3P).range ∧
        Function.Injective (MulAut.conj : j3P →* MulAut j3P) := by
  obtain ⟨hU2, hU1, hUP, hmap', -, -, -, -, -, -, -⟩ :=
    j3_centData
  have hUn : ∀ p ∈ j3P, j3u * p * j3u⁻¹ ∈ j3P := fun p hp => by
    rw [← hmap']
    exact ⟨p, hp, rfl⟩
  obtain ⟨hmap, hRmem, hinf, hnormal, hcard, φ, hφinj, hφ, himage, hconjinj⟩ :=
    normalizing_model hU2 hUP hUn j3_centralizer_eq_bot
  refine ⟨hU2, hU1, hUP, hmap, j3_centralizer_eq_bot, hRmem, hinf, hnormal, ?_, φ, hφinj, hφ,
    himage, hconjinj⟩
  show Nat.card ↥(j3P ⊔ zpowers (tp 6156 j3OuterTbl)) = 100465920
  rw [hcard, card_j3P]

theorem ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial :
    j3S ≤ j3R ∧ Nat.card j3S = 256 ∧ (∃ T : Sylow 2 j3R, (T : Subgroup j3R) = j3S.subgroupOf j3R) ∧
      (∀ r ∈ j3Rows, tp 6156 r.rep ∈ j3R ∧ orderOf (tp 6156 r.rep) = 2 ∧
        (r.outer = true ↔ tp 6156 r.rep ∉ j3P) ∧
        j3C r = j3P ⊓ centralizer ({tp 6156 r.rep} : Set _) ∧
        Nat.card ↥(j3P ⊓ centralizer ({tp 6156 r.rep} : Set (Equiv.Perm (Fin 6156)))) =
          r.centOrder ∧
        (conjClass j3P (tp 6156 r.rep)).ncard = r.classSize) ∧
      (∀ t ∈ j3R, orderOf t = 2 → ∃ r ∈ j3Rows, ∃ g ∈ j3P, t = g * tp 6156 r.rep * g⁻¹) ∧
      (∀ i j : Fin j3Rows.length, (∃ g ∈ j3P,
        tp 6156 j3Rows[j].rep = g * tp 6156 j3Rows[i].rep * g⁻¹) → i = j) ∧
      j3Rows.map (fun r => (r.outer, r.classSize, r.centOrder)) =
        [(false, 26163, 1920), (true, 20520, 2448)] ∧
      (∀ t ∈ j3R, orderOf t = 2 →
        CFSG.oddCore ↥(j3P ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 6156)))) = ⊥) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, hRcard, hSR, hScard, hrows, hcover, hodd⟩ :=
    j3_centData
  have hRcard' : Nat.card j3R = 100465920 := hRcard
  have hS256 : Nat.card j3S = 256 := hScard
  have hSR' : j3S ≤ j3R := hSR
  refine ⟨hSR, hS256, ?_, fun r hr => ?_, hcover, ?_, rfl, hodd⟩
  · refine ⟨Sylow.ofCard (j3S.subgroupOf j3R) ?_, Sylow.coe_ofCard _ _⟩
    rw [Nat.card_congr (subgroupOfEquivOfLe hSR').toEquiv, hS256, hRcard',
      factorization_100465920]
    norm_num
  · obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hrows r hr
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  ·
    intro i j ⟨g, hg, hij⟩
    have hinv : ∀ r ∈ j3Rows, ∀ r' ∈ j3Rows, (∃ g ∈ j3P,
        tp 6156 r'.rep = g * tp 6156 r.rep * g⁻¹) →
          r.outer = r'.outer ∧ r.centOrder = r'.centOrder := by
      rintro r hr r' hr' ⟨g, hg, hgr⟩
      obtain ⟨-, -, hout, -, hcent, -, -⟩ := hrows r hr
      obtain ⟨-, -, hout', -, hcent', -, -⟩ := hrows r' hr'
      constructor
      · have hmem : tp 6156 r.rep ∈ j3P ↔ tp 6156 r'.rep ∈ j3P := by
          rw [hgr]
          constructor
          · intro h; exact j3P.mul_mem (j3P.mul_mem hg h) (j3P.inv_mem hg)
          · intro h
            have := j3P.mul_mem (j3P.mul_mem (j3P.inv_mem hg) h) hg
            rwa [show g⁻¹ * (g * tp 6156 r.rep * g⁻¹) * g = tp 6156 r.rep by group] at this
        cases hro : r.outer <;> cases hro' : r'.outer
        · rfl
        · rw [hro'] at hout'
          rw [hro, Bool.false_eq_true, false_iff, not_not] at hout
          exact absurd (hmem.1 hout) (hout'.1 rfl)
        · rw [hro] at hout
          rw [hro', Bool.false_eq_true, false_iff, not_not] at hout'
          exact absurd (hmem.2 hout') (hout.1 rfl)
        · rfl
      · rw [← hcent, ← hcent', hgr, inf_centralizer_conj j3P hg,
          Subgroup.card_map_of_injective (MulAut.conj g).injective]
    have h := hinv _ (List.getElem_mem _) _ (List.getElem_mem _) ⟨g, hg, hij⟩
    have hnodup : (j3Rows.map fun r => (r.outer, r.centOrder)).Nodup := by decide
    have hi : (i : ℕ) < (j3Rows.map fun r => (r.outer, r.centOrder)).length := by simp
    have hj : (j : ℕ) < (j3Rows.map fun r => (r.outer, r.centOrder)).length := by simp
    have hij' : (j3Rows.map fun r => (r.outer, r.centOrder))[(i : ℕ)] =
        (j3Rows.map fun r => (r.outer, r.centOrder))[(j : ℕ)] := by
      simp only [List.getElem_map]
      rw [h.1, h.2]
    exact Fin.ext (hnodup.getElem_inj_iff.mp hij')

end CFSG.Sporadic.SmallOddCore
