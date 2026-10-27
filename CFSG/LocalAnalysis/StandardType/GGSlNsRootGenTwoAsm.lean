module

public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenAsm
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenCoverComp
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenTwistGen
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenCover

public section

namespace CFSG.StandardType.SlNsRootGen

open Matrix Polynomial CoordSL CFSG.RankThree.CALinearPlane CFSG.Assembly TableB
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private abbrev PairIndex (s : ℕ) : Type := {x : Fin s × Fin s // x.1 ≠ x.2}

private theorem cover_avoid_of_one_le
    {K : Type} [Field K] [Finite K] [Fintype K] [CharP K 2] {n s r : ℕ}
    {g : K[X]} [Fact (Irreducible g)] [Fact (Nat.Prime 3)]
    {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
    {hC : (rootMat g).det = 1} {hCp : rootMat g ^ 3 = 1}
    {hgd : g ∣ cyclotomic 3 K} {hpK : 3 ∣ Nat.card K + 1}
    {hζ : AdjoinRoot.root g ^ 3 = 1}
    {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin n) K →* L'}
    {A : Subgroup (MulAut L')}
    (hφs : Function.Surjective φ)
    (hφc : ∀ x, φ x ∈ Subgroup.center L' →
      x ∈ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (hkerp : ∀ z ∈ φ.ker, z ^ 3 = 1 → z = 1)
    (hM : SuSplitRootGen.IsCoverTorusModel φ (torusSL ε hC hCp) A)
    (hτc : ∀ t, φ (torusSL ε hC hCp t) ∈ Subgroup.center L' → t = 1)
    (hdim : 2 ≤ (rootPB g).dim) (hs3 : 3 ≤ s) (hr : 1 ≤ r) :
    GGTorusRootGenAvoid 3 A := by
  classical
  have hp2 : 3 ≠ 2 := by norm_num
  let w : PairIndex s ⊕ Fin s → SpecialLinearGroup (Fin n) K := fun i =>
    match i with
    | Sum.inl x => Classical.choose
        (exists_swap_mem_pairBlock (p := 3) (ε := ε) hC hCp x.1.1 x.1.2)
    | Sum.inr m => Classical.choose
        (exists_neg_mem_zeroBlock (p := 3) (ε := ε) hC hCp hζ hpK m)
  let f : PairIndex s ⊕ Fin s → (Fin s → ZMod 3) → Fin s → ZMod 3 := fun i =>
    match i with
    | Sum.inl x => fun t => swapMap x.1.1 x.1.2 t
    | Sum.inr m => negMap m
  let S : PairIndex s ⊕ Fin s → Subgroup (SpecialLinearGroup (Fin n) K) := fun i =>
    match i with
    | Sum.inl x => pairBlock g ε x.1.1 x.1.2
    | Sum.inr m => zeroBlock g ε m
  have hwS : ∀ i, w i ∈ S i := by
    intro i
    rcases i with x | m
    · dsimp only [w, S]
      exact (Classical.choose_spec
        (exists_swap_mem_pairBlock (p := 3) (ε := ε) hC hCp x.1.1 x.1.2)).1
    · dsimp only [w, S]
      exact (Classical.choose_spec
        (exists_neg_mem_zeroBlock (p := 3) (ε := ε) hC hCp hζ hpK m)).1
  have hw : ∀ i t, w i * torusSL ε hC hCp (Multiplicative.ofAdd t) * (w i)⁻¹ =
      torusSL ε hC hCp (Multiplicative.ofAdd (f i t)) := by
    intro i t
    rcases i with x | m
    · dsimp only [w, f]
      exact (Classical.choose_spec
        (exists_swap_mem_pairBlock (p := 3) (ε := ε) hC hCp x.1.1 x.1.2)).2 t
    · dsimp only [w, f]
      exact (Classical.choose_spec
        (exists_neg_mem_zeroBlock (p := 3) (ε := ε) hC hCp hζ hpK m)).2 t
  have hinv : ∀ i t, f i (f i t) = t := by
    intro i t
    rcases i with x | m
    · show swapMap (p := 3) x.1.1 x.1.2 (swapMap x.1.1 x.1.2 t) = t
      exact swapMap_swapMap x.1.1 x.1.2 t
    · show negMap (p := 3) m (negMap m t) = t
      exact negMap_negMap m t
  have hfix : ∀ i, Nat.card {t // f i t = t} * 3 = 3 ^ s := by
    intro i
    rcases i with x | m
    · show Nat.card {t // swapMap (p := 3) x.1.1 x.1.2 t = t} * 3 = 3 ^ s
      exact card_fixed_swapMap (p := 3) x.2
    · show Nat.card {t // negMap (p := 3) m t = t} * 3 = 3 ^ s
      exact card_fixed_negMap (p := 3) hp2 m
  have hcomp : ∀ i, IsComponentOf (S i) (Subgroup.centralizer
      (SuSplitRootGen.torusFix (torusSL ε hC hCp) (f i))) := by
    intro i
    rcases i with x | m
    · dsimp only [S, f]
      exact isComponentOf_pairBlock_centralizer (p := 3) hp2 hgd x.2
    · dsimp only [S, f]
      exact isComponentOf_zeroBlock_centralizer (p := 3) hp2 hpK hgd (Or.inr hr) m
  have hdvd : ∀ i, 3 ∣ Nat.card (S i) := by
    intro i
    rcases i with x | m
    · dsimp only [S]
      exact dvd_natCard_pairBlock (p := 3) hp2 hpK hgd x.2
    · dsimp only [S]
      exact dvd_natCard_zeroBlock (p := 3) hp2 hpK hgd m
  have hgen : ∀ j : PairIndex s ⊕ Fin s,
      (⨆ (i : PairIndex s ⊕ Fin s) (_ : f i ≠ f j), S i) = ⊤ := by
    intro j
    rcases j with x₀ | m₀
    · obtain ⟨⟨i₀, j₀⟩, hij₀⟩ := x₀
      apply le_antisymm le_top
      rw [← iSup_blocks_avoid_pair_eq_top (ε := ε) hdim hs3 i₀ j₀]
      refine sup_le ?_ ?_
      · refine iSup_le fun i => iSup_le fun j => iSup_le fun h => ?_
        have hne : f (Sum.inl ⟨(i, j), h.1⟩) ≠ f (Sum.inl ⟨(i₀, j₀), hij₀⟩) := by
          intro heq
          have heq' : swapMap (p := 3) i j = swapMap i₀ j₀ := heq
          exact h.2 (pair_eq_of_swapMap_eq h.1 hij₀ heq')
        exact le_iSup_of_le (Sum.inl ⟨(i, j), h.1⟩) (le_iSup_of_le hne le_rfl)
      · refine iSup_le fun m => ?_
        have hne : f (Sum.inr m) ≠ f (Sum.inl ⟨(i₀, j₀), hij₀⟩) := by
          intro heq
          exact swapMap_ne_negMap hij₀ m heq.symm
        exact le_iSup_of_le (Sum.inr m) (le_iSup_of_le hne le_rfl)
    · apply le_antisymm le_top
      rw [← iSup_blocks_avoid_zero_eq_top (ε := ε) hdim (by omega) m₀]
      refine sup_le ?_ ?_
      · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
        have hne : f (Sum.inl ⟨(i, j), hij⟩) ≠ f (Sum.inr m₀) := by
          intro heq
          exact swapMap_ne_negMap hij m₀ heq
        exact le_iSup_of_le (Sum.inl ⟨(i, j), hij⟩) (le_iSup_of_le hne le_rfl)
      · refine iSup_le fun m => iSup_le fun hm => ?_
        have hne : f (Sum.inr m) ≠ f (Sum.inr m₀) := by
          intro heq
          exact hm (eq_of_negMap_eq (p := 3) hp2 heq)
        exact le_iSup_of_le (Sum.inr m) (le_iSup_of_le hne le_rfl)
  have hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    exact hφc x (by rw [hx]; exact Subgroup.one_mem _)
  haveI : Nonempty (PairIndex s ⊕ Fin s) := ⟨Sum.inr ⟨0, by omega⟩⟩
  exact SuSplitRootGen.ggTorusRootGenAvoid_of_cover (p := 3)
    (H := SpecialLinearGroup (Fin n) K) (L' := L')
    (φ := φ) (τ := torusSL ε hC hCp) (A := A)
    (by norm_num) hφs hker hkerp hM hτc w f S hw hinv hfix hwS hcomp hdvd hgen

private theorem cover_avoid_of_eq_zero
    {K : Type} [Field K] [Finite K] [Fintype K] [CharP K 2] {n s r : ℕ}
    {g : K[X]} [Fact (Irreducible g)] [Fact (Nat.Prime 3)]
    {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
    {hC : (rootMat g).det = 1} {hCp : rootMat g ^ 3 = 1}
    {hgd : g ∣ cyclotomic 3 K} {hpK : 3 ∣ Nat.card K + 1}
    {hζ : AdjoinRoot.root g ^ 3 = 1}
    {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin n) K →* L'}
    {A : Subgroup (MulAut L')}
    (hφs : Function.Surjective φ)
    (hφc : ∀ x, φ x ∈ Subgroup.center L' →
      x ∈ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (hkerp : ∀ z ∈ φ.ker, z ^ 3 = 1 → z = 1)
    (hM : SuSplitRootGen.IsCoverTorusModel φ (torusSL ε hC hCp) A)
    (hτc : ∀ t, φ (torusSL ε hC hCp t) ∈ Subgroup.center L' → t = 1)
    (hs3 : 3 ≤ s) (hr : r = 0) :
    GGTorusRootGenAvoid 3 A := by
  classical
  subst r
  have hp2 : 3 ≠ 2 := by norm_num
  let w : PairIndex s ⊕ PairIndex s → SpecialLinearGroup (Fin n) K := fun i =>
    match i with
    | Sum.inl x => Classical.choose
        (exists_swap_mem_pairBlock (p := 3) (ε := ε) hC hCp x.1.1 x.1.2)
    | Sum.inr x => Classical.choose
        (exists_sswap_mem_twistPairBlock (p := 3) (ε := ε) hC hCp hζ hpK x.1.1 x.1.2)
  let f : PairIndex s ⊕ PairIndex s → (Fin s → ZMod 3) → Fin s → ZMod 3 := fun i =>
    match i with
    | Sum.inl x => fun t => swapMap x.1.1 x.1.2 t
    | Sum.inr x => fun t => sswapMap x.1.1 x.1.2 t
  let S : PairIndex s ⊕ PairIndex s → Subgroup (SpecialLinearGroup (Fin n) K) := fun i =>
    match i with
    | Sum.inl x => pairBlock g ε x.1.1 x.1.2
    | Sum.inr x => twistPairBlock g hζ hpK ε x.1.1 x.1.2
  have hwS : ∀ i, w i ∈ S i := by
    intro i
    rcases i with x | x
    · dsimp only [w, S]
      exact (Classical.choose_spec
        (exists_swap_mem_pairBlock (p := 3) (ε := ε) hC hCp x.1.1 x.1.2)).1
    · dsimp only [w, S]
      exact (Classical.choose_spec
        (exists_sswap_mem_twistPairBlock (p := 3) (ε := ε) hC hCp hζ hpK
          x.1.1 x.1.2)).1
  have hw : ∀ i t, w i * torusSL ε hC hCp (Multiplicative.ofAdd t) * (w i)⁻¹ =
      torusSL ε hC hCp (Multiplicative.ofAdd (f i t)) := by
    intro i t
    rcases i with x | x
    · dsimp only [w, f]
      exact (Classical.choose_spec
        (exists_swap_mem_pairBlock (p := 3) (ε := ε) hC hCp x.1.1 x.1.2)).2 t
    · dsimp only [w, f]
      exact (Classical.choose_spec
        (exists_sswap_mem_twistPairBlock (p := 3) (ε := ε) hC hCp hζ hpK
          x.1.1 x.1.2)).2 t
  have hinv : ∀ i t, f i (f i t) = t := by
    intro i t
    rcases i with x | x
    · show swapMap (p := 3) x.1.1 x.1.2 (swapMap x.1.1 x.1.2 t) = t
      exact swapMap_swapMap x.1.1 x.1.2 t
    · show sswapMap (p := 3) x.1.1 x.1.2 (sswapMap x.1.1 x.1.2 t) = t
      exact sswapMap_sswapMap x.1.1 x.1.2 t
  have hfix : ∀ i, Nat.card {t // f i t = t} * 3 = 3 ^ s := by
    intro i
    rcases i with x | x
    · show Nat.card {t // swapMap (p := 3) x.1.1 x.1.2 t = t} * 3 = 3 ^ s
      exact card_fixed_swapMap (p := 3) x.2
    · show Nat.card {t // sswapMap (p := 3) x.1.1 x.1.2 t = t} * 3 = 3 ^ s
      exact card_fixed_sswapMap (p := 3) x.2
  have hcomp : ∀ i, IsComponentOf (S i) (Subgroup.centralizer
      (SuSplitRootGen.torusFix (torusSL ε hC hCp) (f i))) := by
    intro i
    rcases i with x | x
    · dsimp only [S, f]
      exact isComponentOf_pairBlock_centralizer (p := 3) hp2 hgd x.2
    · dsimp only [S, f]
      exact isComponentOf_twistPairBlock_centralizer (p := 3) hp2 hpK hgd hζ x.2
  have hdvd : ∀ i, 3 ∣ Nat.card (S i) := by
    intro i
    rcases i with x | x
    · dsimp only [S]
      exact dvd_natCard_pairBlock (p := 3) hp2 hpK hgd x.2
    · dsimp only [S]
      exact dvd_natCard_twistPairBlock (p := 3) hp2 hpK hgd hζ x.2
  have hgen : ∀ j : PairIndex s ⊕ PairIndex s,
      (⨆ (i : PairIndex s ⊕ PairIndex s) (_ : f i ≠ f j), S i) = ⊤ := by
    intro j
    rcases j with x₀ | x₀
    · obtain ⟨⟨i₀, j₀⟩, hij₀⟩ := x₀
      apply le_antisymm le_top
      rw [← iSup_pairBlock_twistPairBlock_avoid_eq_top (p := 3) hp2 hpK hgd hζ
        ε hs3 i₀ j₀]
      refine iSup_le fun i => iSup_le fun j => iSup_le fun h => ?_
      refine sup_le ?_ ?_
      · have hne : f (Sum.inl ⟨(i, j), h.1⟩) ≠ f (Sum.inl ⟨(i₀, j₀), hij₀⟩) := by
          intro heq
          have heq' : swapMap (p := 3) i j = swapMap i₀ j₀ := heq
          exact h.2 (pair_eq_of_swapMap_eq h.1 hij₀ heq')
        exact le_iSup_of_le (Sum.inl ⟨(i, j), h.1⟩) (le_iSup_of_le hne le_rfl)
      · have hne : f (Sum.inr ⟨(i, j), h.1⟩) ≠ f (Sum.inl ⟨(i₀, j₀), hij₀⟩) := by
          intro heq
          have heq' : sswapMap (p := 3) i j = swapMap i₀ j₀ := heq
          exact sswapMap_ne_swapMap (p := 3) hp2 h.1 i₀ j₀ heq'
        exact le_iSup_of_le (Sum.inr ⟨(i, j), h.1⟩) (le_iSup_of_le hne le_rfl)
    · obtain ⟨⟨i₀, j₀⟩, hij₀⟩ := x₀
      apply le_antisymm le_top
      rw [← iSup_pairBlock_twistPairBlock_avoid_eq_top (p := 3) hp2 hpK hgd hζ
        ε hs3 i₀ j₀]
      refine iSup_le fun i => iSup_le fun j => iSup_le fun h => ?_
      refine sup_le ?_ ?_
      · have hne : f (Sum.inl ⟨(i, j), h.1⟩) ≠ f (Sum.inr ⟨(i₀, j₀), hij₀⟩) := by
          intro heq
          have heq' : swapMap (p := 3) i j = sswapMap i₀ j₀ := heq
          exact (sswapMap_ne_swapMap (p := 3) hp2 hij₀ i j).symm heq'
        exact le_iSup_of_le (Sum.inl ⟨(i, j), h.1⟩) (le_iSup_of_le hne le_rfl)
      · have hne : f (Sum.inr ⟨(i, j), h.1⟩) ≠ f (Sum.inr ⟨(i₀, j₀), hij₀⟩) := by
          intro heq
          have heq' : sswapMap (p := 3) i j = sswapMap i₀ j₀ := heq
          exact h.2 (pair_eq_of_sswapMap_eq h.1 hij₀ heq')
        exact le_iSup_of_le (Sum.inr ⟨(i, j), h.1⟩) (le_iSup_of_le hne le_rfl)
  have hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    exact hφc x (by rw [hx]; exact Subgroup.one_mem _)
  haveI : Nonempty (PairIndex s ⊕ PairIndex s) :=
    ⟨Sum.inl ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by
      intro h
      have hv := congrArg Fin.val h
      simp at hv⟩⟩
  exact SuSplitRootGen.ggTorusRootGenAvoid_of_cover (p := 3)
    (H := SpecialLinearGroup (Fin n) K) (L' := L')
    (φ := φ) (τ := torusSL ε hC hCp) (A := A)
    (by norm_num) hφs hker hkerp hM hτc w f S hw hinv hfix hwS hcomp hdvd hgen

theorem ggTorusRootGenAvoidKG_projectiveSL_two {K : Type} [Field K] [Finite K] [CharP K 2]
    {d : ℕ} (hK : Nat.card K = 2) (r : ℕ) :
    GGTorusRootGenAvoidKG 3 r (projectiveSL d K) (Set.range (conjAut d K)) := by
  classical
  have hp : Nat.Prime 3 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  haveI : NeZero 3 := ⟨hp.ne_zero⟩
  haveI : Nonempty K := ⟨0⟩
  intro L' _ _ ψ hψ hker hperf A hA hAI _ h3 hsc
  have hp2 : 3 ≠ 2 := by norm_num
  have hpK : 3 ∣ Nat.card K + 1 := ⟨1, by rw [hK]⟩
  have hpK' : ¬ 3 ∣ Nat.card K - 1 := by
    intro hK1
    have hdvd : 3 ∣ 2 := by
      have hsub : Nat.card K + 1 - (Nat.card K - 1) = 2 := by
        have := Nat.card_pos (α := K)
        omega
      rw [← hsub]
      exact Nat.dvd_sub hpK hK1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  have hpK0 : (3 : K) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  obtain ⟨g, hg, hgd⟩ := exists_irreducible_dvd_cyclotomic (K := K) hp
  haveI : Fact (Irreducible g) := ⟨hg⟩
  have hζ : AdjoinRoot.root g ^ 3 = 1 :=
    (CoordSL.root_isPrimitiveRoot hp hpK0 hgd).pow_eq_one
  have hC : (rootMat g).det = 1 := CoordSL.det_rootMat hp hpK' hpK0 hgd
  have hCp : rootMat g ^ 3 = 1 := CoordSL.rootMat_pow_eq_one hp hpK0 hgd
  have hunit : ∀ j : ℕ, ¬ 3 ∣ j → ∀ c : K, IsUnit (rootMat g ^ j - c • 1) :=
    CoordSL.isUnit_rootMat_pow_sub hp hpK' hpK0 hgd
  have hdim : 2 ≤ (rootPB g).dim :=
    LinTwoTv.two_le_rootPB_dim fun c => hunit 1 hp.not_dvd_one c
  obtain ⟨s, r', ε, φ, hφs, hφc, hs3, hMblk⟩ :=
    exists_isBlockTorusModel (g := g) hp hp2 hpK hgd hC hψ hker hperf hA hAI h3 hsc
  have hM : SuSplitRootGen.IsCoverTorusModel φ (torusSL ε hC hCp) A := by
    intro a
    rw [IsBlockTorusModel.mem_iff hMblk hCp]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨Multiplicative.ofAdd t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨Multiplicative.toAdd t, rfl⟩
  have hτc : ∀ t : Multiplicative (Fin s → ZMod 3),
      φ (torusSL ε hC hCp t) ∈ Subgroup.center L' → t = 1 := by
    have hinj := injective_conj_torusSL (ε := ε) (hC := hC) (hCp := hCp)
      (φ := φ) hφc hunit
    intro t ht
    apply hinj
    have h1 : MulAut.conj (φ (torusSL ε hC hCp t)) = 1 := by
      ext y
      rw [MulAut.conj_apply, MulAut.one_apply]
      have hc := Subgroup.mem_center_iff.mp ht y
      rw [← hc]
      group
    have h2 : MulAut.conj (φ (torusSL ε hC hCp 1)) = 1 := by simp
    exact h1.trans h2.symm
  haveI : Fintype K := Fintype.ofFinite K
  have hkerp : ∀ z ∈ φ.ker, z ^ 3 = 1 → z = 1 := by
    intro z hz _hz3
    have hzZ : z ∈ Subgroup.center (SpecialLinearGroup (Fin d) K) :=
      hφc z (by rw [MonoidHom.mem_ker] at hz; rw [hz]; exact Subgroup.one_mem _)
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst d
      refine Subtype.ext ?_
      ext i j
      exact i.elim0
    · obtain ⟨c, hc, hcz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hzZ
      have hc0 : c ≠ 0 := by
        intro h0
        rw [h0, Fintype.card_fin, zero_pow hd.ne'] at hc
        exact zero_ne_one hc
      have hmem : c ∈ ({0, 1} : Finset K) := by
        have hcard : Fintype.card K ≤ 2 := by
          rw [← Nat.card_eq_fintype_card]
          omega
        rw [← Finset.univ_of_card_le_two (R := K) hcard]
        exact Finset.mem_univ c
      have hc1 : c = 1 := by
        exact (by simpa using hmem : c = 0 ∨ c = 1).resolve_left hc0
      exact Subtype.ext (by rw [← hcz, hc1]; simp)
  rcases Nat.eq_zero_or_pos r' with hr | hr
  · exact cover_avoid_of_eq_zero (ε := ε) (hC := hC) (hCp := hCp)
      (hgd := hgd) (hpK := hpK) (hζ := hζ) hφs hφc hkerp hM hτc hs3 hr
  · exact cover_avoid_of_one_le (ε := ε) (hC := hC) (hCp := hCp)
      (hgd := hgd) (hpK := hpK) (hζ := hζ) hφs hφc hkerp hM hτc hdim hs3 hr

end CFSG.StandardType.SlNsRootGen

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggTorusRootGenAvoidKG_linearNs_two {K : Type} [Field K] {d : ℕ} (hK : Nat.card K = 2)
    (r : ℕ) :
    GGTorusRootGenAvoidKG 3 r (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  haveI : CharP K 2 := charP_two_of_card (m := 1) (by simpa using hK)
  exact ggTorusRootGenAvoidKG_of_mulEquiv (TypeA.recipeEquiv d K)
    (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
    (SlNsRootGen.ggTorusRootGenAvoidKG_projectiveSL_two hK r)

end CFSG.StandardType

end
