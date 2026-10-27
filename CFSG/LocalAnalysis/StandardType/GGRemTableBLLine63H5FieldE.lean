module

public import CFSG.RankThree.PartOne.KC.PrimaryDecomposition
public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import Mathlib

public section

namespace CFSG.StandardType.Line63.H5

open Polynomial Module CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary

theorem card_le_nine_of_commute_pow_three_eq_one {K : Type*} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {l : K}
    (hirr : Irreducible (X ^ 3 - C l : K[X])) {x : Module.End K V}
    (hx : aeval x (X ^ 3 - C l : K[X]) = 0) (hdim : Module.finrank K V = 6)
    {ω : K} (hω : IsPrimitiveRoot ω 3) {ι : Type*} [Finite ι] (Y : ι → Module.End K V)
    (hinj : Function.Injective Y) (hcomm : ∀ i j, Commute (Y i) (Y j))
    (hcx : ∀ i, Commute (Y i) x) (hpow : ∀ i, Y i ^ 3 = 1) : Nat.card ι ≤ 9 := by
  classical
  set a : K[X] := X ^ 3 - C l with ha
  haveI : Fact (Irreducible a) := ⟨hirr⟩
  haveI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  have hdeg : a.natDegree = 3 := natDegree_X_pow_sub_C
  have htop : primaryComponent x a = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [mem_primaryComponent, hx]
    rfl
  have hfin : Module.finrank K (primaryComponent x a) = 6 := by
    rw [htop, finrank_top, hdim]
  have hm : Module.finrank (AdjoinRoot a) (primaryComponent x a) = 2 := by
    have h := finrank_primaryComponent x a
    rw [hfin, hdeg] at h
    omega
  set f : ι → Module.End (AdjoinRoot a) (primaryComponent x a) := fun i =>
    commutantRestrictHom a ⟨Y i, (mem_commutant x).2 (hcx i)⟩ with hf
  have hfcomm : ∀ i j, Commute (f i) (f j) := fun i j => by
    have h : Commute (⟨Y i, (mem_commutant x).2 (hcx i)⟩ : commutant x)
        ⟨Y j, (mem_commutant x).2 (hcx j)⟩ := Subtype.ext (hcomm i j).eq
    exact h.map (commutantRestrictHom a)
  have hfpow : ∀ i, f i ^ 3 = 1 := fun i => by
    have h : (⟨Y i, (mem_commutant x).2 (hcx i)⟩ : commutant x) ^ 3 = 1 :=
      Subtype.ext (by simpa using hpow i)
    simp only [hf]
    rw [← map_pow, h, map_one]
  have hfinj : Function.Injective f := by
    intro i j hij
    apply hinj
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ primaryComponent x a := htop ▸ Submodule.mem_top
    exact congrArg (fun g : Module.End (AdjoinRoot a) (primaryComponent x a) =>
      ((g ⟨v, hv⟩ : primaryComponent x a) : V)) hij
  have hζ : IsPrimitiveRoot (algebraMap K (AdjoinRoot a) ω) 3 :=
    hω.map_of_injective (algebraMap K (AdjoinRoot a)).injective
  obtain ⟨b, μ, hb⟩ := exists_basis_common_eigenvectors_of_pow_eq_one hζ f hfcomm hfpow
  have hμ3 : ∀ i j, μ i j ^ 3 = 1 := by
    intro i j
    have hev : (f i).HasEigenvector (μ i j) (b j) :=
      ⟨Module.End.mem_eigenspace_iff.2 (hb i j), b.ne_zero j⟩
    have h1 := hev.pow_apply 3
    rw [hfpow i, Module.End.one_apply] at h1
    have h2 : μ i j ^ 3 • b j = (1 : AdjoinRoot a) • b j := by rw [one_smul]; exact h1.symm
    exact smul_left_injective _ (b.ne_zero j) h2
  set R : Finset (AdjoinRoot a) := nthRootsFinset 3 (1 : AdjoinRoot a) with hR
  have hmemR : ∀ i j, μ i j ∈ R := fun i j => (mem_nthRootsFinset (by norm_num) 1).2 (hμ3 i j)
  have hRcard : Nat.card R = 3 := by
    rw [Nat.card_eq_finsetCard, hR, hζ.card_nthRootsFinset]
  let Φ : ι → (Fin (Module.finrank (AdjoinRoot a) (primaryComponent x a)) → R) :=
    fun i j => ⟨μ i j, hmemR i j⟩
  have hΦ : Function.Injective Φ := by
    intro i i' h
    apply hfinj
    refine b.ext fun j => ?_
    have h2 : μ i j = μ i' j := congrArg Subtype.val (congrFun h j)
    rw [hb i j, hb i' j, h2]
  calc Nat.card ι
      ≤ Nat.card (Fin (Module.finrank (AdjoinRoot a) (primaryComponent x a)) → R) :=
        Nat.card_le_card_of_injective Φ hΦ
    _ = 9 := by
      rw [Nat.card_fun, hRcard, Nat.card_eq_fintype_card, Fintype.card_fin, hm]
      norm_num

end CFSG.StandardType.Line63.H5

end
