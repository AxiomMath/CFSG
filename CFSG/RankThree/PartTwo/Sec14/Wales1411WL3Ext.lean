module

public import CFSG.RankThree.PartTwo.Sec14.Wales1411WL3Tori
import CFSG.RankThree.PartTwo.Sec14.Wales1411WTori
import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypes

public section

namespace CFSG.RankThree.PartTwo.Sec14.Wales1411W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {M : Type} [Group M] [Finite M]

theorem map_pCoreOf_subgroupOf (p : ℕ) {N X : Subgroup M} (hX : X ≤ N) :
    (CFSG.Open.pCoreOf p (X.subgroupOf N)).map N.subtype = CFSG.Open.pCoreOf p X := by
  let e : ↥(X.subgroupOf N) ≃* ↥X := Subgroup.subgroupOfEquivOfLe hX
  have h1 := CFSG.pCore_map_iso p e
  unfold CFSG.Open.pCoreOf
  rw [Subgroup.map_map, ← h1, Subgroup.map_map]
  congr 1

theorem mem_normalizer_of_subgroupOf {N E : Subgroup M} [hN : N.Normal] (hEN : E ≤ N) {n : N}
    (hn : n ∈ Subgroup.normalizer ((E.subgroupOf N : Subgroup N) : Set N)) :
    (n : M) ∈ Subgroup.normalizer (E : Set M) := by
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have h := (Subgroup.mem_normalizer_iff.mp hn ⟨x, hEN hx⟩).mp (Subgroup.mem_subgroupOf.mpr hx)
  rw [Subgroup.mem_subgroupOf] at h
  simpa using h

theorem etrans2_of_normal_l3 (hKL : KL3HessTori) (N E : Subgroup M) [hN : N.Normal]
    (hEN : E ≤ N) {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hiso : Sec4.IsoLThreePi ↥N p f)
    (hEe : CFSG.Assembly.IsElemAbelian 3 (E.subgroupOf N))
    (hE9 : Nat.card (E.subgroupOf N) = 9)
    (htr : ∀ y₀ ∈ E.subgroupOf N, y₀ ≠ 1 → ∀ y₁ ∈ E.subgroupOf N, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer ((E.subgroupOf N : Subgroup N) : Set N), w * y₀ * w⁻¹ = y₁) :
    ETrans2 M E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1', h2'⟩ := hKL ↥N p f hp2 hf hiso (E.subgroupOf N) hEe hE9 htr
  have hE3 : IsPGroup 3 E := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    have := hEe.2 ⟨x, hEN x.2⟩ (Subgroup.mem_subgroupOf.mpr x.2)
    simpa using congrArg Subtype.val this
  have hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    have := hEe.1.is_comm.comm ⟨⟨x, hEN hx⟩, Subgroup.mem_subgroupOf.mpr hx⟩
      ⟨⟨y, hEN hy⟩, Subgroup.mem_subgroupOf.mpr hy⟩
    have h := congrArg (fun z : E.subgroupOf N => ((z : N) : M)) this
    simpa using h
  set U : M → Subgroup M := fun x =>
    CFSG.Open.pCoreOf 2 (N ⊓ Subgroup.centralizer ({x} : Set M)) with hU
  have hUmap : ∀ x (hx : x ∈ N), (CFSG.Open.pCoreOf 2
      (Subgroup.centralizer ({(⟨x, hx⟩ : N)} : Set N))).map N.subtype = U x := by
    intro x hx
    have h : Subgroup.centralizer ({(⟨x, hx⟩ : N)} : Set N) =
        (N ⊓ Subgroup.centralizer ({x} : Set M)).subgroupOf N := by
      rw [Subgroup.inf_subgroupOf_left]
      exact (Res5Types.centralizer_subgroupOf hx).symm
    rw [h, map_pCoreOf_subgroupOf 2 inf_le_left]
  have hUN : ∀ x, U x ≤ N := fun x =>
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
  have hback : ∀ W : Subgroup M, W ≤ N → W = (W.subgroupOf N).map N.subtype :=
    fun W hW => (Subgroup.map_subgroupOf_eq_of_le hW).symm
  have hnorm : ∀ W : Subgroup M, W ≤ N → E ≤ Subgroup.normalizer (W : Set M) →
      E.subgroupOf N ≤ Subgroup.normalizer ((W.subgroupOf N : Subgroup N) : Set N) := by
    intro W _ hEW ε hε
    rw [Subgroup.mem_normalizer_iff]
    intro w
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using Subgroup.mem_normalizer_iff.mp (hEW (Subgroup.mem_subgroupOf.mp hε)) w
  have hne : ∀ W : Subgroup M, W ≤ N → W ≠ ⊥ → W.subgroupOf N ≠ ⊥ := by
    intro W hW hW0 h
    apply hW0
    rw [hback W hW, h, Subgroup.map_bot]
  have h2grp : ∀ W : Subgroup M, W ≤ N → IsPGroup 2 W → IsPGroup 2 (W.subgroupOf N) :=
    fun W hW hW2 => hW2.of_equiv (Subgroup.subgroupOfEquivOfLe hW).symm
  refine etrans2_of_tori (N := N) U hE3 ?_ ?_ ?_ ?_ ?_ ?_
  · intro m ε hε
    rw [commutatorElement_def]
    exact mul_mem (hN.conj_mem ε (hEN hε) m) (inv_mem (hEN hε))
  · intro x _
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  · intro x hx
    refine le_trans ?_ (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
    refine le_inf hEN fun y hy => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hEab y hy x hx
  · intro x hx
    refine le_trans ?_ (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
    refine Late.le_normalizer_inf ?_ ?_
    · intro c _
      exact Subgroup.mem_normalizer_fintype fun n hn => hN.conj_mem n hn c
    · exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hx)).trans
        Subgroup.le_normalizer
  · intro W hWN hW2 hEW hW0
    obtain ⟨x, hx, hWx⟩ := h1' (W.subgroupOf N) (h2grp W hWN hW2) (hnorm W hWN hEW)
      (hne W hWN hW0)
    refine ⟨x, Subgroup.mem_subgroupOf.mp hx, ?_⟩
    rw [← hUmap x x.2, hback W hWN]
    exact Subgroup.map_mono hWx
  · intro x hx x' hx' W W' hW0 hW'0 hWx hW'x' hEW hEW'
    have hWN := hWx.trans (hUN x)
    have hW'N := hW'x'.trans (hUN x')
    have hWx₀ : W.subgroupOf N ≤ CFSG.Open.pCoreOf 2
        (Subgroup.centralizer ({(⟨x, hEN hx⟩ : N)} : Set N)) := by
      rw [← Subgroup.map_le_map_iff_of_injective N.subtype_injective, hUmap x (hEN hx),
        ← hback W hWN]
      exact hWx
    have hW'x₀ : W'.subgroupOf N ≤ CFSG.Open.pCoreOf 2
        (Subgroup.centralizer ({(⟨x', hEN hx'⟩ : N)} : Set N)) := by
      rw [← Subgroup.map_le_map_iff_of_injective N.subtype_injective, hUmap x' (hEN hx'),
        ← hback W' hW'N]
      exact hW'x'
    obtain ⟨n, hn, hnU⟩ := h2' ⟨x, hEN hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨x', hEN hx'⟩
      (Subgroup.mem_subgroupOf.mpr hx') (W.subgroupOf N) (W'.subgroupOf N) (hne W hWN hW0)
      (hne W' hW'N hW'0) hWx₀ hW'x₀ (hnorm W hWN hEW) (hnorm W' hW'N hEW')
    refine ⟨(n : M), Subgroup.mem_inf.mpr ⟨?_, mem_normalizer_of_subgroupOf hEN
      (Subgroup.mem_inf.mp hn).2⟩, ?_⟩
    · have h := Subgroup.mem_map_of_mem N.subtype (Subgroup.mem_inf.mp hn).1
      rwa [Subgroup.map_sup, ← hback W hWN, ← hback W' hW'N] at h
    · rw [← hUmap x (hEN hx), ← hUmap x' (hEN hx'), ← hnU, Subgroup.map_map, Subgroup.map_map]
      congr 1

end CFSG.RankThree.PartTwo.Sec14.Wales1411W
