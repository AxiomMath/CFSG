
module

public import CFSG.Quasithin.Recognition.RuRank3TitsSyl
public import CFSG.Quasithin.Recognition.RuRank3PSL
public import CFSG.Sporadic.Schreier.TitsAction
public import CFSG.Sporadic.Schreier.TitsChain
public import CFSG.Sporadic.Schreier.RuChainSpec
public import CFSG.Sporadic.Schreier.RuConj
public meta import CFSG.Quasithin.Recognition.RuRank3TitsSyl
public meta import CFSG.Quasithin.Recognition.RuRank3PSL
public meta import CFSG.Sporadic.Schreier.TitsAction
public meta import CFSG.Sporadic.Schreier.TitsChain
public meta import CFSG.Sporadic.Schreier.RuChainSpec
public meta import CFSG.Sporadic.Schreier.RuCheckChains
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Schreier.TitsAbelCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsEnum
public meta import CFSG.Sporadic.Schreier.TitsCentralCheck
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import CFSG.Sporadic.Schreier.TitsActionCheckInputs
public import CFSG.Sporadic.Schreier.TitsCentralCheckInputs
public import CFSG.Sporadic.Schreier.TitsCertCheckInputs
public import CFSG.Sporadic.Schreier.TitsInvCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsAbelCheck
public import CFSG.Sporadic.Schreier.TitsLocalCheckInputs
public import CFSG.Quasithin.Recognition.RuRank3Tits13Inputs

@[expose] public section

namespace CFSG.Quasithin.RuRank3

open CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open scoped Pointwise

theorem mem_list_of_mem_genSubgroup {n : ℕ} {gens L : Array (Array ℕ)}
    {Gs : ℕ → Equiv.Perm (Fin n)} (hrep : ∀ k < gens.size, Rep n gens[k]! (Gs k))
    (hinv : ∀ k < gens.size, isInvA n gens[k]! (invCand n gens[k]!) = true)
    (hL : listClosedA n gens L = true) :
    ∀ g ∈ genSubgroup n gens.size Gs, ∃ i < L.size, Rep n L[i]! g := by
  simp only [listClosedA, Bool.and_eq_true] at hL
  obtain ⟨h1, hcl⟩ := hL
  have step : ∀ (a : Array ℕ) (A : Equiv.Perm (Fin n)), Rep n a A →
      (∀ i < L.size, (L.any fun e => eqA n e (compA n a L[i]!)) = true) →
      ∀ y, (∃ i < L.size, Rep n L[i]! y) → ∃ i < L.size, Rep n L[i]! (A * y) := by
    rintro a A ha hall y ⟨i, hi, hy⟩
    obtain ⟨j, hj, hje⟩ := Array.any_eq_true.1 (hall i hi)
    refine ⟨j, hj, ?_⟩
    rw [show L[j]! = L[j] from getElem!_pos L j hj]
    exact rep_of_eqA hje (rep_compA ha hy)
  intro g hg
  induction hg using Subgroup.closure_induction_left with
  | one =>
    obtain ⟨j, hj, hje⟩ := Array.any_eq_true.1 h1
    refine ⟨j, hj, ?_⟩
    rw [show L[j]! = L[j] from getElem!_pos L j hj]
    exact rep_of_eqA hje rep_idA
  | mul_left x hx y hy ih =>
    obtain ⟨k, hk, rfl⟩ := hx
    refine step _ _ (hrep k hk) (fun i hi => ?_) y ih
    have h' := allLt_spec (allLt_spec hcl hk) hi
    rw [Bool.and_eq_true] at h'
    exact h'.1
  | inv_mul_cancel x hx y hy ih =>
    obtain ⟨k, hk, rfl⟩ := hx
    refine step _ _ (rep_inv_of_isInvA (hrep k hk) (hinv k hk)) (fun i hi => ?_) y ih
    have h' := allLt_spec (allLt_spec hcl hk) hi
    rw [Bool.and_eq_true] at h'
    exact h'.2

theorem prime_dvd_card_fixedPoints_of_commute {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}
    [Fact p.Prime] {σ τ : Equiv.Perm α} (hσ : σ ^ p = 1) (hfree : ∀ a, σ a ≠ a)
    (hcomm : σ * τ = τ * σ) : p ∣ Fintype.card {a // τ a = a} := by
  have hinv : ∀ a, τ (σ a) = σ a ↔ τ a = a := by
    intro a
    have e : τ (σ a) = σ (τ a) := by
      rw [← Equiv.Perm.mul_apply, ← hcomm, Equiv.Perm.mul_apply]
    rw [e]
    exact ⟨fun h => σ.injective h, fun h => by rw [h]⟩
  let σ' : Equiv.Perm {a // τ a = a} := σ.subtypePerm hinv
  have hσ' : σ' ^ p ^ 1 = 1 := by
    rw [pow_one]
    ext a
    simp [σ', Equiv.Perm.subtypePerm_pow, hσ]
  have hmod := Equiv.Perm.card_compl_support_modEq hσ'
  have hempty : σ'.supportᶜ = ∅ := by
    ext a
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Finset.notMem_empty,
      iff_false]
    intro h
    exact hfree a (congrArg Subtype.val h)
  rw [hempty, Finset.card_empty] at hmod
  exact (Nat.modEq_zero_iff_dvd.1 hmod.symm)

theorem lineFixedA_iff {a : Array ℕ}
    {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g)
    (v : Fin 2925) : lineFixedA a v = true ↔ g • titsLine v = titsLine v := by
  have hpt : ∀ k < 3, (titsLinePt v k : ℕ) = titsLinePtArr[3 * (v : ℕ) + k]! :=
    fun k hk => titsLinePt_val v hk
  have hga : ∀ k < 3, a[titsLinePtArr[3 * (v : ℕ) + k]!]! = (g (titsLinePt v k) : ℕ) := by
    intro k hk
    rw [← hpt k hk]
    exact ha _
  have hmemL : ∀ y : Fin 1755, y ∈ titsLine v ↔ (y : ℕ) = titsLinePtArr[3 * (v : ℕ)]! ∨
      (y : ℕ) = titsLinePtArr[3 * (v : ℕ) + 1]! ∨ (y : ℕ) = titsLinePtArr[3 * (v : ℕ) + 2]! := by
    intro y
    have h0 := hpt 0 (by norm_num)
    rw [Nat.add_zero] at h0
    rw [titsLine_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton,
      ← h0, ← hpt 1 (by norm_num), ← hpt 2 (by norm_num), Fin.ext_iff, Fin.ext_iff, Fin.ext_iff]
  have hsub : g • titsLine v = titsLine v ↔ ∀ k < 3, g (titsLinePt v k) ∈ titsLine v := by
    constructor
    · intro h k hk
      rw [← h]
      refine Finset.smul_mem_smul_finset ?_
      rw [titsLine_eq]
      interval_cases k <;> simp
    · intro h
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        rw [Finset.mem_smul_finset] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        rw [titsLine_eq] at hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact h 0 (by norm_num)
        · exact h 1 (by norm_num)
        · exact h 2 (by norm_num)
      · rw [Finset.card_smul_finset]
  rw [hsub, lineFixedA, List.all_eq_true]
  constructor
  · intro h k hk
    have := h k (List.mem_range.2 hk)
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    rw [hmemL, ← hga k hk]
    rcases this with (h0 | h1) | h2
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h2)
  · intro h k hk
    have hk' := List.mem_range.1 hk
    have := h k hk'
    rw [hmemL, ← hga k hk'] at this
    simp only [Bool.or_eq_true, beq_iff_eq]
    rcases this with h0 | h1 | h2
    · exact Or.inl (Or.inl h0)
    · exact Or.inl (Or.inr h1)
    · exact Or.inr h2

theorem lineHom_fixed_iff
    (g : titsA) (v : Fin 2925) :
    titsLineHom g v = v ↔ (g : Equiv.Perm (Fin 1755)) • titsLine v = titsLine v := by
  rw [← titsLine_lineHom]
  exact titsLine_injective.eq_iff.symm

theorem card_fixedLines
    {g : titsA} {a : Array ℕ} (ha : Rep 1755 a g) :
    Fintype.card {v // titsLineHom g v = v} = lineFixCount a := by
  classical
  rw [Fintype.card_subtype, lineFixCount, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((List.nodup_range).filter _)]
  apply Finset.card_bij (fun (v : Fin 2925) _ => (v : ℕ))
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, v.2, true_and]
    exact (lineFixedA_iff ha v).2 ((lineHom_fixed_iff g v).1 hv)
  · intro a _ b _ h
    exact Fin.ext h
  · intro m hm
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range] at hm
    refine ⟨⟨m, hm.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (lineHom_fixed_iff g ⟨m, hm.1⟩).2 ((lineFixedA_iff ha ⟨m, hm.1⟩).1 hm.2)

theorem card_fixedPoints {g : Equiv.Perm (Fin 1755)} {a : Array ℕ} (ha : Rep 1755 a g) :
    Fintype.card {x // g x = x} = ptFixCount a := by
  classical
  rw [Fintype.card_subtype, ptFixCount, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((List.nodup_range).filter _)]
  apply Finset.card_bij (fun (x : Fin 1755) _ => (x : ℕ))
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, x.2, true_and, beq_iff_eq]
    rw [ha x, hx]
  · intro a _ b _ h
    exact Fin.ext h
  · intro m hm
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, beq_iff_eq] at hm
    refine ⟨⟨m, hm.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply Fin.ext
    rw [← ha ⟨m, hm.1⟩]
    exact hm.2

theorem card_fixedLines_conj
    (g y : titsA) :
    Fintype.card {v // titsLineHom (g * y * g⁻¹) v = v} =
      Fintype.card {v // titsLineHom y v = v} := by
  apply Fintype.card_congr
  refine Equiv.subtypeEquiv (titsLineHom g⁻¹) fun v => ?_
  rw [map_mul, map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  constructor
  · intro h
    have := congrArg (titsLineHom g).symm h
    rw [Equiv.symm_apply_apply] at this
    rw [Equiv.Perm.inv_def]
    exact this
  · intro h
    rw [h, ← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]

noncomputable def titsX13 : Equiv.Perm (Fin 1755) := permOfArr 1755 titsX13Arr

theorem mem_titsA_of_inTitsA {a : Array ℕ}
    {g : Equiv.Perm (Fin 1755)} (hg : Rep 1755 a g)
    (h : inTitsA a = true) : g ∈ titsA := by
  rw [← titsQA_original]
  exact (siftA_iff_mem_ofArrays (n := 1755) (hn := by norm_num) (hk := by
      rw [titsAmbientArrs_size]; norm_num) (hb := by decide) (chunks := 4)
    titsChains_check.2.2.2.2.2.1 (by norm_num) titsChains_check.2.2.2.2.2.2.2.2.1 hg).1 h

noncomputable def titsP3Chain : RawSchreierDatum 1755 :=
  RawSchreierDatum.ofArrays 1755 (by norm_num) titsP3Gens 3 (by simp [titsP3Gens])
    (ruFinList 1755 (by norm_num) [0]) (by decide) (ruWordsArr 3 3 [])

noncomputable def titsP5Chain : RawSchreierDatum 1755 :=
  RawSchreierDatum.ofArrays 1755 (by norm_num) titsP5Gens 2 (by simp [titsP5Gens])
    (ruFinList 1755 (by norm_num) [0]) (by decide) (ruWordsArr 2 2 [])

noncomputable def titsP3 : Subgroup (Equiv.Perm (Fin 1755)) :=
  genSubgroup 1755 titsP3Gens.size fun k => permOfArr 1755 titsP3Gens[k]!

noncomputable def titsP5 : Subgroup (Equiv.Perm (Fin 1755)) :=
  genSubgroup 1755 titsP5Gens.size fun k => permOfArr 1755 titsP5Gens[k]!

theorem titsP3Gens_size : titsP3Gens.size = 3 := by simp [titsP3Gens]

theorem titsP5Gens_size : titsP5Gens.size = 2 := by simp [titsP5Gens]

theorem chain_originalSubgroup_eq_gen {n : ℕ} {hn : 1 ≤ n} {S : Array (Array ℕ)} {k : ℕ}
    {hk : k ≤ S.size} {base : List (Fin n)} {hb : base.Nodup} {W : Array (List ℤ)}
    (hkS : k = S.size) :
    (RawSchreierDatum.ofArrays n hn S k hk base hb W).originalSubgroup =
      genSubgroup n S.size fun j => permOfArr n S[j]! := by
  rw [RawSchreierDatum.originalSubgroup, genSubgroup]
  congr 1
  ext g
  rw [Set.mem_ofPred_eq, RawSchreierDatum.mem_ofArrays_original, Set.mem_ofPred_eq, hkS]

theorem titsP3_eq : titsP3Chain.originalSubgroup = titsP3 :=
  chain_originalSubgroup_eq_gen titsP3Gens_size.symm

theorem titsP5_eq : titsP5Chain.originalSubgroup = titsP5 :=
  chain_originalSubgroup_eq_gen titsP5Gens_size.symm

theorem genSubgroup_le {n : ℕ} {k : ℕ} {Gs : ℕ → Equiv.Perm (Fin n)} {K : Subgroup _}
    (h : ∀ i < k, Gs i ∈ K) : genSubgroup n k Gs ≤ K := by
  rw [genSubgroup, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact h i hi

theorem exists_sylow_eq_of_card {p e : ℕ} [Fact p.Prime]
    {K : Subgroup titsA}
    (hK : Nat.card K = p ^ e) (hmax : ¬ p ^ (e + 1) ∣ 35942400) :
    ∃ Q : Sylow p titsA, (Q : Subgroup titsA) = K := by
  have hpK : IsPGroup p K := IsPGroup.of_card hK
  obtain ⟨Q, hKQ⟩ := hpK.exists_le_sylow
  refine ⟨Q, (Subgroup.eq_of_le_of_card_ge hKQ ?_).symm⟩
  obtain ⟨m, hm⟩ := (Q.2 : IsPGroup p Q).exists_card_eq
  rw [hm, hK]
  apply Nat.pow_le_pow_right (Fact.out : p.Prime).pos
  by_contra hlt
  push Not at hlt
  apply hmax
  have hdvd : p ^ m ∣ Nat.card titsA := by
    rw [← hm]
    exact Subgroup.card_subgroup_dvd_card _
  rw [card_titsA] at hdvd
  exact (Nat.pow_dvd_pow p hlt).trans hdvd

end CFSG.Quasithin.RuRank3
