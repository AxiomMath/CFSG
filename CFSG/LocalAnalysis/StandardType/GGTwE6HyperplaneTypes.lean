module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeModel
public import CFSG.Blueprint.ChevalleyRoots
public import CFSG.LieType.Steinberg.Adjoint.Pairs
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LocalAnalysis.StandardType.GGTwE6HyperplaneTypesK

public section

namespace CFSG.StandardType.TwE6HyperplaneTypes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.StandardType.TableBExc CFSG.StandardType.TableBExc.Three
  CFSG.StandardType.TableBExc.E6Three

local instance tableBE6HypNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] local instance tableBE6HypRootDecEq : DecidableEq (Fin Tag.E6.rank → ℤ) :=
  Fintype.decidablePiFintype

@[expose] def modelWordE6 (v : Fin 3 → ZMod 3) (j : ZMod 3) : List (Fin Tag.E6.rank) :=
  nfWordE6 (v 0).val (v 1).val (v 2).val ++ (List.replicate j.val wordE6C).flatten

theorem modelHomE6_eq_wordProd (y : Model piE7 piE7_pow_three) :
    modelHomE6 y = (coxeterSystem .E6).wordProd
      (modelWordE6 (Multiplicative.toAdd y.left) (Multiplicative.toAdd y.right)) := by
  change modelHom isModel_E6 y = _
  rw [modelHom_apply isModel_E6 y,
    show modelN isModel_E6 y.left = modelHomE6 (SemidirectProduct.inl y.left) from
      (modelHom_inl isModel_E6 y.left).symm, modelHomE6_inl, modelWordE6,
    CoxeterSystem.wordProd_append, wordProd_replicate, cE6]

@[expose] def conjTableE6 : List ((Fin 3 → ZMod 3) × ZMod 3 × List (Fin Tag.E6.rank)) := [
    (![0, 0, 0], 1, []),
    (![0, 0, 0], 2, [0, 2, 3, 4, 1, 3, 2, 0]),
    (![0, 1, 1], 0, [2, 3, 4, 5, 0, 2, 1, 3]),
    (![0, 1, 2], 0, [2, 3, 4, 5, 0, 2, 1, 3, 1]),
    (![0, 1, 2], 1, [4, 5]),
    (![0, 1, 2], 2, [5, 1, 3, 4, 0, 2, 3]),
    (![0, 2, 1], 0, [2, 3, 4, 0, 2, 1, 3]),
    (![0, 2, 1], 1, [5, 4]),
    (![0, 2, 1], 2, [5, 4, 3, 2, 1, 3, 0, 2]),
    (![0, 2, 2], 0, [2, 3, 4, 0, 2, 1, 3, 1]),
    (![1, 0, 1], 0, [4, 5, 3, 4, 2, 1, 3, 1]),
    (![1, 0, 2], 0, [4, 5, 3, 4, 2, 1, 3]),
    (![1, 0, 2], 1, [5, 1, 0]),
    (![1, 0, 2], 2, [0, 2, 3, 4, 1, 3, 0, 2]),
    (![1, 1, 0], 0, [5, 0, 2, 3, 4, 3, 2, 1, 3, 0]),
    (![1, 1, 1], 1, [5, 4, 2, 0]),
    (![1, 1, 1], 2, [0, 2, 1, 3, 4, 5, 1, 3]),
    (![1, 2, 0], 0, [0, 2, 3, 4, 5, 4, 3, 2, 1, 3, 0]),
    (![1, 2, 0], 1, [2, 0]),
    (![1, 2, 0], 2, [5, 4, 3, 2, 1, 3]),
    (![2, 0, 1], 0, [4, 5, 3, 4, 2, 1, 3, 1, 0]),
    (![2, 0, 1], 1, [5, 4, 0, 2]),
    (![2, 0, 1], 2, [0, 2, 3, 4, 1, 3]),
    (![2, 0, 2], 0, [4, 5, 3, 4, 2, 1, 3, 0]),
    (![2, 1, 0], 0, [5, 0, 2, 3, 4, 3, 2, 1, 3]),
    (![2, 1, 0], 1, [0, 2]),
    (![2, 1, 0], 2, [4, 5, 4, 3, 2, 1, 3, 4]),
    (![2, 2, 0], 0, [0, 2, 3, 4, 5, 4, 3, 2, 1, 3]),
    (![2, 2, 2], 1, [4, 5, 0, 2]),
    (![2, 2, 2], 2, [5, 4, 3, 2, 1, 3, 2, 0])
  ]

@[expose] def conjWordE6 (v : Fin 3 → ZMod 3) (j : ZMod 3) : List (Fin Tag.E6.rank) :=
  ((conjTableE6.find? fun e => decide (e.1 = v ∧ e.2.1 = j)).map fun e => e.2.2).getD []

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 100000 in
theorem modelElt_cases : ∀ v : Fin 3 → ZMod 3, ∀ j : ZMod 3,
    (j = 0 ∨ v 0 + v 1 + v 2 = 0) → ¬ (v = 0 ∧ j = 0) →
    (∀ i : Fin 3, ¬ (j = 0 ∧ (v = Pi.single i 1 ∨ v = Pi.single i 2))) →
    (j = 0 ∧ ∀ i, v i ≠ 0) ∨
    ∀ i : Fin Tag.E6.rank, wordAct .E6 (conjWordE6 v j ++ modelWordE6 v j) (Pi.single i 1) =
      wordAct .E6 (wordE6C ++ conjWordE6 v j) (Pi.single i 1) := by
  have H : ∀ v : Fin 3 → ZMod 3, ∀ j : ZMod 3,
      (j = 0 ∨ v 0 + v 1 + v 2 = 0) → ¬ (v = 0 ∧ j = 0) →
      (∀ i : Fin 3, ¬ (j = 0 ∧ (v = Pi.single i 1 ∨ v = Pi.single i 2))) →
      (j = 0 ∧ ∀ i, v i ≠ 0) ∨ ∀ i : Fin Tag.E6.rank,
        K.eqK (conjWordE6 v j ++ modelWordE6 v j) (wordE6C ++ conjWordE6 v j) i.val = true := by
    decide +kernel
  intro v j h1 h2 h3
  rcases H v j h1 h2 h3 with h | h
  · exact Or.inl h
  · exact Or.inr fun i => K.eqK_sound (h i)

set_option maxRecDepth 100000 in
theorem fpf_cubic : ∀ v : Fin 3 → ZMod 3, (∀ i, v i ≠ 0) → ∀ i : Fin Tag.E6.rank,
    (Pi.single i 1 : Fin Tag.E6.rank → ℤ) + wordAct .E6 (modelWordE6 v 0) (Pi.single i 1) +
      wordAct .E6 (modelWordE6 v 0) (wordAct .E6 (modelWordE6 v 0) (Pi.single i 1)) = 0 := by
  have H : ∀ v : Fin 3 → ZMod 3, (∀ i, v i ≠ 0) → ∀ i : Fin Tag.E6.rank,
      K.cubK (modelWordE6 v 0) i.val = true := by
    decide +kernel
  exact fun v hv i => K.cubK_sound (H v hv i)

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 100000 in
theorem modelElt_cube_ne : ∀ v : Fin 3 → ZMod 3, ∀ j : ZMod 3,
    ¬ (j = 0 ∨ v 0 + v 1 + v 2 = 0) → ∃ i : Fin Tag.E6.rank,
      wordAct .E6 (List.replicate 3 (modelWordE6 v j)).flatten (Pi.single i 1) ≠ Pi.single i 1 := by
  have H : ∀ v : Fin 3 → ZMod 3, ∀ j : ZMod 3,
      ¬ (j = 0 ∨ v 0 + v 1 + v 2 = 0) → ∃ i : Fin Tag.E6.rank,
        K.neK (List.replicate 3 (modelWordE6 v j)).flatten i.val = true := by
    decide +kernel
  intro v j hv
  obtain ⟨i, hi⟩ := H v j hv
  exact ⟨i, K.neK_sound hi⟩

@[expose] def basisC : Fin 3 → Fin Tag.E6.rank → ZMod 3 :=
  ![![0, 0, 0, 1, 0, 0], ![0, 1, 1, 0, 1, 0], ![1, 0, 0, 0, 0, 1]]

@[expose] def combC (x : Fin 3 → ZMod 3) : Fin Tag.E6.rank → ZMod 3 :=
  fun j => ∑ i, x i * basisC i j

@[expose] def dotZ3 (α : Fin Tag.E6.rank → ℤ) (v : Fin Tag.E6.rank → ZMod 3) : ZMod 3 :=
  ∑ j, ((α j : ℤ) : ZMod 3) * v j

@[expose] def cAct (v : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℤ := wordAct .E6 wordE6C v

theorem cE6_smul (v : Fin Tag.E6.rank → ℤ) : cE6 • v = cAct v := by
  rw [cE6, CFSG.StandardType.TableBExc.wordProd_smul, cAct]

theorem cE6_pow_ne_gE6 (m : ℕ) (i : Fin 3) : cE6 ^ m ≠ gE6 i := by
  have hdec : ∀ r i : Fin 3, ∃ j : Fin Tag.E6.rank,
      wordAct .E6 (List.replicate r.val wordE6C).flatten (Pi.single j 1) ≠
        wordAct .E6 (wordE6G i) (Pi.single j 1) := by
    decide +kernel
  intro h
  have hmod : cE6 ^ m = cE6 ^ (m % 3) :=
    pow_eq_pow_mod (a := cE6) (n := 3) m cE6_pow_three
  have h' : cE6 ^ (m % 3) = gE6 i := by rw [← hmod]; exact h
  obtain ⟨j, hj⟩ := hdec ⟨m % 3, Nat.mod_lt m (by decide)⟩ i
  apply hj
  have hv := congrArg
    (fun w : WeylGroup .E6 => w • (Pi.single j (1 : ℤ) : Fin Tag.E6.rank → ℤ)) h'
  have hc : cE6 ^ (m % 3) =
      (coxeterSystem .E6).wordProd (List.replicate (m % 3) wordE6C).flatten := by
    rw [cE6, wordProd_replicate]
  rw [hc, CFSG.StandardType.TableBExc.wordProd_smul, gE6, CFSG.StandardType.TableBExc.wordProd_smul] at hv
  exact hv

theorem cE6_zpow_ne_gE6 (m : ℤ) (i : Fin 3) : cE6 ^ m ≠ gE6 i := by
  rw [zpow_eq_zpow_emod' m cE6_pow_three,
    ← Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num : ((3 : ℕ) : ℤ) ≠ 0)), zpow_natCast]
  exact cE6_pow_ne_gE6 _ i

theorem cE6_ne_one : cE6 ≠ 1 := by
  intro h
  have h1 := congrArg (· • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ)) h
  simp only [cE6_smul, one_smul] at h1
  revert h1
  decide +kernel

theorem adWord_combC : ∀ x : Fin 3 → ZMod 3, adWord .E6 3 wordE6C (combC x) = combC x := by
  decide +kernel

theorem exists_combC_of_adWord : ∀ v : Fin Tag.E6.rank → ZMod 3,
    adWord .E6 3 wordE6C v = v → ∃ x : Fin 3 → ZMod 3, v = combC x := by
  decide +kernel

theorem combC_add (x x' : Fin 3 → ZMod 3) : combC (x + x') = combC x + combC x' := by
  funext j
  simp only [combC, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem exists_planeKey (H : AddSubgroup (Fin Tag.E6.rank → ZMod 3)) {y : Fin 3 → ZMod 3}
    (hu : combC y ∉ H)
    (hspan : ∀ v : Fin Tag.E6.rank → ZMod 3, adWord .E6 3 wordE6C v = v →
      ∃ j : ZMod 3, v - j • combC y ∈ H) :
    ∃ k : Fin 3 → ZMod 3, ∑ i, k i * y i = 1 ∧
      ∀ x : Fin 3 → ZMod 3, combC x ∈ H ↔ ∑ i, k i * x i = 0 := by
  let u := combC y
  have hu' : u ∉ H := hu
  choose k hk using fun i : Fin 3 =>
    hspan (combC (Pi.single i 1)) (adWord_combC (Pi.single i 1))
  have hsingle : ∀ (i : Fin 3) (j : Fin Tag.E6.rank),
      combC (Pi.single i (1 : ZMod 3)) j = basisC i j := by
    intro i j
    simp [combC, Pi.single_apply]
  have hcomb : ∀ x : Fin 3 → ZMod 3, combC x = ∑ i, x i • combC (Pi.single i 1) := by
    intro x
    funext j
    have hx : combC x j = ∑ i, x i * basisC i j := rfl
    rw [hx, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Pi.smul_apply, smul_eq_mul, hsingle]
  have hsmul : ∀ (a : ZMod 3) {w : Fin Tag.E6.rank → ZMod 3}, w ∈ H → a • w ∈ H := by
    intro a w hw
    rw [← ZMod.natCast_zmod_val a, Nat.cast_smul_eq_nsmul]
    exact AddSubgroup.nsmul_mem H hw a.val
  have hsum : ∀ x : Fin 3 → ZMod 3, combC x - (∑ i, k i * x i) • u ∈ H := by
    intro x
    have hmem : ∑ i, x i • (combC (Pi.single i 1) - k i • u) ∈ H := by
      refine AddSubgroup.sum_mem H (fun i _ => ?_)
      exact hsmul (x i) (hk i)
    have h1 : ∑ i, x i • (combC (Pi.single i 1) - k i • u)
        = ∑ i, (x i • combC (Pi.single i 1) - x i • (k i • u)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [smul_sub]
    have h2 : ∑ i, (x i • combC (Pi.single i 1) - x i • (k i • u))
        = (∑ i, x i • combC (Pi.single i 1)) - ∑ i, x i • (k i • u) :=
      Finset.sum_sub_distrib (fun i => x i • combC (Pi.single i 1))
        (fun i => x i • (k i • u))
    have h3 : ∑ i, (x i * k i) • u = (∑ i, k i * x i) • u := by
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [mul_comm]
    have h4 : ∑ i, x i • (k i • u) = ∑ i, (x i * k i) • u := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [smul_smul]
    have hcalc : ∑ i, x i • (combC (Pi.single i 1) - k i • u)
        = combC x - (∑ i, k i * x i) • u := by
      calc ∑ i, x i • (combC (Pi.single i 1) - k i • u)
          = ∑ i, (x i • combC (Pi.single i 1) - x i • (k i • u)) := h1
        _ = (∑ i, x i • combC (Pi.single i 1)) - ∑ i, x i • (k i • u) := h2
        _ = combC x - ∑ i, (x i * k i) • u := by rw [← hcomb x, h4]
        _ = combC x - (∑ i, k i * x i) • u := by rw [h3]
    rw [← hcalc]
    exact hmem
  have hkey : ∀ a : ZMod 3, a • u ∈ H ↔ a = 0 := by
    intro a
    constructor
    · intro ha
      by_contra hne
      have hgen : ∀ b : ZMod 3, b ≠ 0 → b = 1 ∨ b = 2 := by decide +kernel
      rcases hgen a hne with rfl | rfl
      · exact hu' (by simpa using ha)
      · have hcoef : (2 : ZMod 3) * 2 = 1 := by decide +kernel
        have h22 : (2 : ZMod 3) • ((2 : ZMod 3) • u) = u := by
          rw [smul_smul, hcoef, one_smul]
        have hmem : (2 : ZMod 3) • ((2 : ZMod 3) • u) ∈ H := hsmul 2 ha
        rw [h22] at hmem
        exact hu' hmem
    · intro ha
      rw [ha, zero_smul]
      exact H.zero_mem
  have hky : ∑ i, k i * y i = 1 := by
    have h1 : (1 - ∑ i, k i * y i) • u = u - (∑ i, k i * y i) • u := by
      funext j
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, sub_mul, one_mul]
    have h2 : (1 - ∑ i, k i * y i) • u ∈ H := by
      rw [h1]
      exact hsum y
    exact (sub_eq_zero.mp ((hkey _).mp h2)).symm
  refine ⟨k, hky, fun x => ?_⟩
  have hs : combC x - (∑ i, k i * x i) • u ∈ H := hsum x
  constructor
  · intro hx
    have htu : (∑ i, k i * x i) • u ∈ H := by
      have hEq : combC x - (combC x - (∑ i, k i * x i) • u) =
          (∑ i, k i * x i) • u := by abel
      exact hEq ▸ H.sub_mem hx hs
    exact (hkey _).mp htu
  · intro ht
    have htu : (∑ i, k i * x i) • u ∈ H := (hkey _).mpr ht
    simpa using H.add_mem hs htu

@[expose] def sigmaTest (k : Fin 3 → ZMod 3) (α : Fin Tag.E6.rank → ℤ) : Prop :=
  ∀ x : Fin 3 → ZMod 3, ∑ i, k i * x i = 0 → dotZ3 α (combC x) = 0

instance (k : Fin 3 → ZMod 3) (α : Fin Tag.E6.rank → ℤ) : Decidable (sigmaTest k α) := by
  unfold sigmaTest
  infer_instance

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 100000 in
theorem planeTypes_c : ∀ k : Fin 3 → ZMod 3, (∃ y : Fin 3 → ZMod 3,
      (∀ α ∈ rootFinset .E6, α + cAct α + cAct (cAct α) = 0 → dotZ3 α (combC y) = 0) ∧
        ∑ i, k i * y i = 1) →
    (∀ α ∈ rootFinset .E6, ¬ sigmaTest k α) ∨
    (∃ β ∈ (rootFinset .E6).filter (sigmaTest k),
      (∀ α ∈ rootFinset .E6, sigmaTest k α ↔ (α = β ∨ α = -β ∨ α = cAct β ∨ α = -cAct β ∨
        α = cAct (cAct β) ∨ α = -cAct (cAct β))) ∧
      iform β (cAct β) = 0 ∧ iform β (cAct (cAct β)) = 0 ∧ iform (cAct β) (cAct (cAct β)) = 0 ∧
      ∃ ℓ ∈ rootFinset .E6, ∑ i, ℓ i * (corootPair β (Pi.single i 1) +
        corootPair (cAct β) (Pi.single i 1) + corootPair (cAct (cAct β)) (Pi.single i 1)) = 1) ∨
    (k = ![1, 0, 0] ∨ k = ![2, 0, 0]) := by
  have H : ∀ k : Fin 3 → ZMod 3, (∃ y : Fin 3 → ZMod 3,
        (∀ n < 72, K.rootE6 n + K.rootE6 (K.sg n) + K.rootE6 (K.sg (K.sg n)) = 0 →
          dotZ3 (K.rootE6 n) (combC y) = 0) ∧ ∑ i, k i * y i = 1) →
      (∀ n < 72, ¬ sigmaTest k (K.rootE6 n)) ∨
      (∃ m < 72, sigmaTest k (K.rootE6 m) ∧
        (∀ n < 72, sigmaTest k (K.rootE6 n) ↔ (K.rootE6 n = K.rootE6 m ∨
          K.rootE6 n = -K.rootE6 m ∨ K.rootE6 n = K.rootE6 (K.sg m) ∨
          K.rootE6 n = -K.rootE6 (K.sg m) ∨ K.rootE6 n = K.rootE6 (K.sg (K.sg m)) ∨
          K.rootE6 n = -K.rootE6 (K.sg (K.sg m)))) ∧
        iform (K.rootE6 m) (K.rootE6 (K.sg m)) = 0 ∧
        iform (K.rootE6 m) (K.rootE6 (K.sg (K.sg m))) = 0 ∧
        iform (K.rootE6 (K.sg m)) (K.rootE6 (K.sg (K.sg m))) = 0 ∧
        ∃ p < 72, ∑ i, K.rootE6 p i * (corootPair (K.rootE6 m) (Pi.single i 1) +
          corootPair (K.rootE6 (K.sg m)) (Pi.single i 1) +
          corootPair (K.rootE6 (K.sg (K.sg m))) (Pi.single i 1)) = 1) ∨
      (k = ![1, 0, 0] ∨ k = ![2, 0, 0]) := by
    decide +kernel
  rintro k ⟨y, hy, hky⟩
  have hy' := K.root_c_of_forall (fun α a b => α + a + b = 0 → dotZ3 α (combC y) = 0) hy
  rcases H k ⟨y, hy', hky⟩ with h | ⟨m, hm, hs, hall, i1, i2, i3, p, hp, hsum⟩ | h
  · refine Or.inl fun α hα => ?_
    obtain ⟨n, hn, rfl⟩ := K.mem_rootFinset_E6.1 hα
    exact h n hn
  · refine Or.inr (Or.inl ?_)
    obtain ⟨h1, e1⟩ := K.cAct_rootE6 m hm
    have c1 : cAct (K.rootE6 m) = K.rootE6 (K.sg m) := e1
    have c2 : cAct (K.rootE6 (K.sg m)) = K.rootE6 (K.sg (K.sg m)) := (K.cAct_rootE6 _ h1).2
    refine ⟨K.rootE6 m, Finset.mem_filter.2 ⟨K.rootE6_mem hm, hs⟩, ?_, ?_⟩
    · intro α hα
      obtain ⟨n, hn, rfl⟩ := K.mem_rootFinset_E6.1 hα
      rw [c1, c2]
      exact hall n hn
    · rw [c1, c2]
      exact ⟨i1, i2, i3, K.rootE6 p, K.rootE6_mem hp, hsum⟩
  · exact Or.inr (Or.inr h)

@[expose] def fixedA2E6 : List (Fin Tag.E6.rank → ℤ) :=
  [![0, 0, 0, 1, 0, 0], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 2, 1, 0],
    ![0, 0, 0, -1, 0, 0], ![0, -1, -1, -1, -1, 0], ![0, -1, -1, -2, -1, 0]]

set_option maxRecDepth 100000 in
theorem sigmaTest_fixed : ∀ α ∈ rootFinset .E6,
    (sigmaTest ![1, 0, 0] α ↔ α ∈ fixedA2E6) ∧ (sigmaTest ![2, 0, 0] α ↔ α ∈ fixedA2E6) := by
  decide +kernel

theorem cAct_fixedA2E6 : ∀ α ∈ fixedA2E6, cAct α = α := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem sigmaTest_rotatingA2Two : ∀ α ∈ rootFinset .E6,
    (sigmaTest ![1, 2, 1] α ↔ α + cAct α + cAct (cAct α) = 0) ∧
    (sigmaTest ![2, 1, 2] α ↔ α + cAct α + cAct (cAct α) = 0) := by
  have H : ∀ n < 72,
      (sigmaTest ![1, 2, 1] (K.rootE6 n) ↔
        K.rootE6 n + K.rootE6 (K.sg n) + K.rootE6 (K.sg (K.sg n)) = 0) ∧
      (sigmaTest ![2, 1, 2] (K.rootE6 n) ↔
        K.rootE6 n + K.rootE6 (K.sg n) + K.rootE6 (K.sg (K.sg n)) = 0) := by
    decide +kernel
  exact K.forall_root_c (fun α a b => (sigmaTest ![1, 2, 1] α ↔ α + a + b = 0) ∧
    (sigmaTest ![2, 1, 2] α ↔ α + a + b = 0)) H

set_option maxRecDepth 100000 in
theorem planeTypes_c_all (k : Fin 3 → ZMod 3) (hk : k ≠ 0) :
    (∀ α ∈ rootFinset .E6, ¬ sigmaTest k α) ∨
    (∃ β ∈ (rootFinset .E6).filter (sigmaTest k),
      (∀ α ∈ rootFinset .E6, sigmaTest k α ↔ (α = β ∨ α = -β ∨ α = cAct β ∨ α = -cAct β ∨
        α = cAct (cAct β) ∨ α = -cAct (cAct β))) ∧
      iform β (cAct β) = 0 ∧ iform β (cAct (cAct β)) = 0 ∧ iform (cAct β) (cAct (cAct β)) = 0 ∧
      ∃ ℓ ∈ rootFinset .E6, ∑ i, ℓ i * (corootPair β (Pi.single i 1) +
        corootPair (cAct β) (Pi.single i 1) + corootPair (cAct (cAct β)) (Pi.single i 1)) = 1) ∨
    (k = ![1, 0, 0] ∨ k = ![2, 0, 0]) ∨
    ((k = ![1, 2, 1] ∨ k = ![2, 1, 2]) ∧
      ∀ α ∈ rootFinset .E6, sigmaTest k α ↔ α + cAct α + cAct (cAct α) = 0) := by
  by_cases he : k = ![1, 2, 1] ∨ k = ![2, 1, 2]
  · refine Or.inr (Or.inr (Or.inr ⟨he, ?_⟩))
    rcases he with rfl | rfl
    · exact fun α hα => (sigmaTest_rotatingA2Two α hα).1
    · exact fun α hα => (sigmaTest_rotatingA2Two α hα).2
  · have hguard : ∀ k : Fin 3 → ZMod 3, k ≠ 0 →
        ¬ (k = ![1, 2, 1] ∨ k = ![2, 1, 2]) →
        ∃ y : Fin 3 → ZMod 3,
          (∀ α ∈ rootFinset .E6, α + cAct α + cAct (cAct α) = 0 →
            dotZ3 α (combC y) = 0) ∧ ∑ i, k i * y i = 1 := by
      have H : ∀ k : Fin 3 → ZMod 3, k ≠ 0 → ¬ (k = ![1, 2, 1] ∨ k = ![2, 1, 2]) →
          ∃ y : Fin 3 → ZMod 3,
            (∀ n < 72, K.rootE6 n + K.rootE6 (K.sg n) + K.rootE6 (K.sg (K.sg n)) = 0 →
              dotZ3 (K.rootE6 n) (combC y) = 0) ∧ ∑ i, k i * y i = 1 := by
        decide +kernel
      intro k hk he
      obtain ⟨y, h1, h2⟩ := H k hk he
      exact ⟨y, K.forall_root_c (fun α a b => α + a + b = 0 → dotZ3 α (combC y) = 0) h1, h2⟩
    rcases planeTypes_c k (hguard k hk he) with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))

end CFSG.StandardType.TwE6HyperplaneTypes

end
