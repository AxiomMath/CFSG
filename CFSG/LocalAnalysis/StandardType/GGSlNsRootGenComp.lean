module

public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenTypeABlock
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3ZeroBlockCount
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusField
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLComp
public import CFSG.Sporadic.Th.Max3.Core

public section

namespace CFSG.StandardType.SlNsRootGen

open Matrix Polynomial CoordSL CFSG.RankThree.CALinearPlane CFSG.Assembly TableB Multiplicative
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] [Finite K] [CharP K 2] {g : K[X]} [Fact (Irreducible g)]
  {n s r p : ℕ} [Fact p.Prime] {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
  {hC : (rootMat g).det = 1} {hCp : rootMat g ^ p = 1} {L' : Type} [Group L'] [Finite L']
  {φ : SpecialLinearGroup (Fin n) K →* L'} {A : Subgroup (MulAut L')}

omit [Finite K] [CharP K 2] in
theorem ker_le_center_of {M : Type*} [Group M] (ψ : SpecialLinearGroup (Fin n) K →* M)
    (hψc : ∀ x, ψ x ∈ Subgroup.center M →
      x ∈ Subgroup.center (SpecialLinearGroup (Fin n) K)) :
    ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K) := by
  intro x hx
  exact hψc x (by rw [MonoidHom.mem_ker.mp hx]; exact Subgroup.one_mem _)

omit [Finite K] [CharP K 2] in
theorem frameHom_one_eq_torusSL {M : Type} [Group M]
    (ψ : SpecialLinearGroup (Fin n) K →* M) (t : Fin s → ZMod p) :
    frameHom ψ (1 : SpecialLinearGroup (Fin n) K) ε hC hCp (ofAdd t) =
      ψ (torusSL ε hC hCp (ofAdd t)) := by
  rw [frameHom_apply, torusSL_apply]
  simp

omit [Finite K] [CharP K 2] in
theorem ggFrame_one {M : Type} [Group M] (ψ : SpecialLinearGroup (Fin n) K →* M) :
    SLRep.ggFrame ψ (1 : SpecialLinearGroup (Fin n) K) = ψ := by
  refine MonoidHom.ext fun x => ?_
  rw [SLRep.ggFrame_apply]
  simp

theorem centralizer_torusSL_eq_map {M : Type} [Group M]
    (ψ : SpecialLinearGroup (Fin n) K →* M)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (hnsplit : ∀ c : K, c ^ p = 1 → c = 1) (hψs : Function.Surjective ψ)
    (β : Fin s → ZMod p) :
    Subgroup.centralizer {ψ (torusSL ε hC hCp (ofAdd β))} =
      (Subgroup.centralizer {SLNS.nsSL ε hC (fun i => (β i).val)}).map ψ := by
  have h := CoordSL.centralizer_eq_map (ψ := ψ) (A₀ := 1) (ε := ε) (hC := hC) (hCp := hCp)
    hker hnsplit β
  rwa [frameHom_one_eq_torusSL, ggFrame_one, MonoidHom.range_eq_top_of_surjective ψ hψs,
    top_inf_eq] at h

theorem pow_torusSL {M : Type} [Group M] (ψ : SpecialLinearGroup (Fin n) K →* M)
    (t : Fin s → ZMod p) :
    (ψ (torusSL ε hC hCp (ofAdd t))) ^ p = 1 := by
  have h := frameHom_pow_p (ψ := ψ) (A₀ := 1) (ε := ε) (hC := hC) hCp (ofAdd t)
  rwa [frameHom_one_eq_torusSL] at h

theorem map_torusSL_ne_one (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K + 1)
    (hgd : g ∣ cyclotomic p K) (hφc : ∀ x, φ x ∈ Subgroup.center L' →
      x ∈ Subgroup.center (SpecialLinearGroup (Fin n) K))
    {t : Fin s → ZMod p} (ht : t ≠ 0) :
    φ (torusSL ε hC hCp (ofAdd t)) ≠ 1 := by
  have hp : p.Prime := Fact.out
  have hK' : ¬ p ∣ Nat.card K - 1 := SpNS.not_dvd_card_sub_one hp hp2 hpK
  have hinj : Function.Injective
      (frameHom φ (1 : SpecialLinearGroup (Fin n) K) ε hC hCp) :=
    frameHom_injective φ 1 ε hC hCp (ker_le_center_of φ hφc) (rootPB_dim_pos g)
      fun j hj c => isUnit_rootMat_pow_sub hp hK'
        (OrdPNS.natCast_ne_zero_of_charTwo hp hp2) hgd j hj c
  intro h
  have h1 : frameHom φ (1 : SpecialLinearGroup (Fin n) K) ε hC hCp (ofAdd t) =
      frameHom φ (1 : SpecialLinearGroup (Fin n) K) ε hC hCp 1 := by
    rw [map_one, frameHom_one_eq_torusSL]
    exact h
  have h2 : ofAdd t = 1 := hinj h1
  exact ht (by simpa using congrArg Multiplicative.toAdd h2)

theorem aligned_blockVec {hζ : AdjoinRoot.root g ^ p = 1} (i : Fin s) :
    Aligned hζ (blockVec (p := p) i) :=
  aligned_of_eq_zero_or_one fun m => by
    by_cases h : m = i <;> simp [blockVec, h]

theorem aligned_pairVec {hζ : AdjoinRoot.root g ^ p = 1} (i j : Fin s) :
    Aligned hζ (pairVec (p := p) i j) :=
  aligned_of_eq_zero_or_one fun m => by
    by_cases h : m = i ∨ m = j <;> simp [pairVec, h]

theorem torusSL_single_mem_zeroBlock (i : Fin s) :
    torusSL ε hC hCp (ofAdd (Pi.single i (1 : ZMod p))) ∈ zeroBlock g ε i := by
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  have hz : zeroCoords ε (blockVec (p := p) i) = blockCoords ε i :=
    zeroCoords_blockVec ε i
  have hmem : SLNS.nsSL ε hC (fun m => ((Pi.single i (1 : ZMod p) : Fin s → ZMod p) m).val) ∈
      coordBlockSL K (zeroCoords ε (blockVec (p := p) i)) :=
    nsSL_mem_zeroBlock (ε := ε) (hC := hC) (β := blockVec (p := p) i)
      (k := fun m => ((Pi.single i (1 : ZMod p) : Fin s → ZMod p) m).val) (by
        intro m hm
        have hmi : m ≠ i := fun h => hm (blockVec_eq_zero_iff.mpr h)
        simp [Pi.single_eq_of_ne hmi, Ne.symm hmi])
  rwa [torusSL_apply, zeroBlock, ← hz]

theorem torusSL_sub_single_mem_pairBlock (hp2 : p ≠ 2) (hgd : g ∣ cyclotomic p K)
    {i j : Fin s} (hij : i ≠ j) :
    torusSL ε hC hCp (ofAdd (Pi.single i (1 : ZMod p) - Pi.single j (1 : ZMod p))) ∈
      pairBlock g ε i j := by
  have hp : p.Prime := Fact.out
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  have hprim : IsPrimitiveRoot (AdjoinRoot.root g) p :=
    root_isPrimitiveRoot hp (OrdPNS.natCast_ne_zero_of_charTwo hp hp2) hgd
  have hsupp : ∀ m : Fin s,
      pairVec (p := p) i j m ≠ 1 →
        (Pi.single i (1 : ZMod p) - Pi.single j (1 : ZMod p) : Fin s → ZMod p) m = 0 := by
    intro m hm
    have hmi : m ≠ i := fun h => hm (by subst h; simp [pairVec])
    have hmj : m ≠ j := fun h => hm (by subst h; simp [pairVec])
    simp [Pi.sub_apply, hmi, Ne.symm hmi, hmj, Ne.symm hmj]
  have hsum : ∑ m : Fin s,
      (Pi.single i (1 : ZMod p) - Pi.single j (1 : ZMod p) : Fin s → ZMod p) m = 0 := by
    have h1 : ∑ m : Fin s, (Pi.single i (1 : ZMod p) : Fin s → ZMod p) m = 1 := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb, Ne.symm hb]
      · intro h
        exact absurd (Finset.mem_univ i) h
    have h2 : ∑ m : Fin s, (Pi.single j (1 : ZMod p) : Fin s → ZMod p) m = 1 := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb, Ne.symm hb]
      · intro h
        exact absurd (Finset.mem_univ j) h
    have h3 : ∑ m : Fin s, (Pi.single i (1 : ZMod p) - Pi.single j (1 : ZMod p) :
        Fin s → ZMod p) m =
        (∑ m : Fin s, (Pi.single i (1 : ZMod p) : Fin s → ZMod p) m) -
          ∑ m : Fin s, (Pi.single j (1 : ZMod p) : Fin s → ZMod p) m :=
      Finset.sum_sub_distrib (s := Finset.univ)
        (f := fun m : Fin s => (Pi.single i (1 : ZMod p) : Fin s → ZMod p) m)
        (g := fun m : Fin s => (Pi.single j (1 : ZMod p) : Fin s → ZMod p) m)
    rw [h3, h1, h2, sub_self]
  obtain ⟨D, hD, hDθ⟩ := diag_mem_classBlock (g := g) (ε := ε) (hC := hC)
    (hζ := hprim.pow_eq_one) (β := pairVec (p := p) i j) (c := 1)
    (t := Pi.single i (1 : ZMod p) - Pi.single j (1 : ZMod p)) hsupp hsum
  rw [torusSL_apply, ← hDθ, pairBlock, ← classSet_pairVec (p := p) i j]
  exact Subgroup.mem_map_of_mem (theta g ε) hD

theorem isComponentOf_zeroBlock (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K + 1)
    (hgd : g ∣ cyclotomic p K) (hM : IsBlockTorusModel φ ε hC A) (hφs : Function.Surjective φ)
    (hφc : ∀ x, φ x ∈ Subgroup.center L' → x ∈ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (h4 : 4 ≤ Nat.card K) (hs : 2 ≤ s) {i : Fin s} {w : L'}
    (hwJ : w ∈ (zeroBlock g ε i).map φ)
    (hcomm : ∀ t : Fin s → ZMod p, MulAut.conj w * MulAut.conj (φ (torusSL ε hC hCp (ofAdd t))) =
      MulAut.conj (φ (torusSL ε hC hCp (ofAdd t))) * MulAut.conj w ↔ t i = 0) :
    IsComponentOf ((zeroBlock g ε i).map φ) (ggHypCent A w) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  have hpK' : (p : K) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  have hprim : IsPrimitiveRoot (AdjoinRoot.root g) p := root_isPrimitiveRoot hp hpK' hgd
  have hal : Aligned hprim.pow_eq_one (blockVec (p := p) i) := aligned_blockVec i
  have hz : zeroCoords ε (blockVec (p := p) i) = blockCoords ε i := zeroCoords_blockVec ε i
  have hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K) := ker_le_center_of φ hφc
  have hK' : ¬ p ∣ Nat.card K - 1 := SpNS.not_dvd_card_sub_one hp hp2 hpK
  have hnsplit : ∀ c : K, c ^ p = 1 → c = 1 := fun c hc =>
    OrdPNS.eq_one_of_pow_eq_one hp hK' hc
  obtain ⟨M, hMmem, rfl⟩ := Subgroup.mem_map.mp hwJ
  have hM' : M ∈ coordBlockSL K (zeroCoords ε (blockVec (p := p) i)) := by
    rw [zeroCoords_blockVec]
    exact hMmem
  have hJle : (zeroBlock g ε i).map φ ≤ ggHypCent A (φ M) := by
    intro x hx
    obtain ⟨N, hNmem, rfl⟩ := Subgroup.mem_map.mp hx
    unfold ggHypCent
    simp only [Subgroup.mem_iInf, mem_ggFix]
    intro a ha
    obtain ⟨haA, hcommA⟩ := ha
    obtain ⟨t, rfl⟩ := (hM.mem_iff hCp).mp haA
    have hti : t i = 0 := (hcomm t).mp hcommA
    have hNcoords : N ∈ coordBlockSL K (zeroCoords ε (blockVec (p := p) i)) := by
      rw [zeroCoords_blockVec]
      exact hNmem
    have hcommι : SLNS.nsSL ε hC (fun m => (t m).val) * N =
        N * SLNS.nsSL ε hC (fun m => (t m).val) := by
      refine comm_zeroBlock_of_torus (β := blockVec (p := p) i)
        (k := fun m => (t m).val) ?_ hNcoords
      intro m hm
      have hmi : m = i := blockVec_eq_zero_iff.mp hm
      rw [hmi]
      simpa using congrArg ZMod.val hti
    have hcommφ : φ (torusSL ε hC hCp (ofAdd t)) * φ N =
        φ N * φ (torusSL ε hC hCp (ofAdd t)) := by
      rw [torusSL_apply, ← map_mul, ← map_mul, hcommι]
    show MulAut.conj (φ (torusSL ε hC hCp (ofAdd t))) (φ N) = φ N
    rw [MulAut.conj_apply, hcommφ, mul_assoc, mul_inv_cancel, mul_one]
  have hβ : MulAut.conj (φ (torusSL ε hC hCp (ofAdd (blockVec (p := p) i)))) ∈ A :=
    (hM.mem_iff hCp).mpr ⟨blockVec (p := p) i, rfl⟩
  have hMβ : φ M * φ (torusSL ε hC hCp (ofAdd (blockVec (p := p) i))) =
      φ (torusSL ε hC hCp (ofAdd (blockVec (p := p) i))) * φ M := by
    rw [torusSL_apply, ← map_mul, ← map_mul]
    exact congrArg φ (comm_zeroBlock_of_torus (β := blockVec (p := p) i)
      (k := fun m => (blockVec (p := p) i m).val)
      (fun m hm => by rw [hm, ZMod.val_zero]) hM').symm
  have hβcomm : MulAut.conj (φ M) *
      MulAut.conj (φ (torusSL ε hC hCp (ofAdd (blockVec (p := p) i)))) =
      MulAut.conj (φ (torusSL ε hC hCp (ofAdd (blockVec (p := p) i)))) * MulAut.conj (φ M) := by
    calc MulAut.conj (φ M) *
          MulAut.conj (φ (torusSL ε hC hCp (ofAdd (blockVec (p := p) i))))
        = MulAut.conj (φ M * φ (torusSL ε hC hCp (ofAdd (blockVec (p := p) i)))) :=
          (map_mul MulAut.conj _ _).symm
      _ = MulAut.conj (φ (torusSL ε hC hCp (ofAdd (blockVec (p := p) i))) * φ M) := by
          rw [hMβ]
      _ = MulAut.conj (φ (torusSL ε hC hCp (ofAdd (blockVec (p := p) i)))) *
          MulAut.conj (φ M) := map_mul MulAut.conj _ _
  have hcent : ggHypCent A (φ M) ≤ Subgroup.centralizer
      {φ (torusSL ε hC hCp (ofAdd (blockVec (p := p) i)))} := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfix : MulAut.conj (φ (torusSL ε hC hCp (ofAdd (blockVec (p := p) i)))) x = x := by
      unfold ggHypCent at hx
      simp only [Subgroup.mem_iInf, mem_ggFix] at hx
      exact hx (MulAut.conj (φ (torusSL ε hC hCp (ofAdd (blockVec (p := p) i)))))
        ⟨hβ, hβcomm⟩
    rw [MulAut.conj_apply] at hfix
    calc x * φ (torusSL ε hC hCp (ofAdd (blockVec (p := p) i)))
        = (φ (torusSL ε hC hCp (ofAdd (blockVec (p := p) i))) * x *
            (φ (torusSL ε hC hCp (ofAdd (blockVec (p := p) i))))⁻¹) *
            φ (torusSL ε hC hCp (ofAdd (blockVec (p := p) i))) := by rw [hfix]
      _ = φ (torusSL ε hC hCp (ofAdd (blockVec (p := p) i))) * x := by group
  have hCen := centralizer_torusSL_eq_map (ψ := φ) (ε := ε) (hC := hC) (hCp := hCp)
    hker hnsplit hφs (blockVec (p := p) i)
  have hnorm : ggHypCent A (φ M) ≤
      Subgroup.normalizer ((zeroBlock g ε i).map φ : Set L') := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp (hCen ▸ hcent hx)
    obtain ⟨N, hNmem, rfl⟩ := Subgroup.mem_map.mp hy
    have hv' : v * SLNS.nsSL ε hC (fun m => (blockVec (p := p) i m).val) =
        SLNS.nsSL ε hC (fun m => (blockVec (p := p) i m).val) * v :=
      Subgroup.mem_centralizer_singleton_iff.mp hv
    have hN' : N ∈ coordBlockSL K (zeroCoords ε (blockVec (p := p) i)) := by
      rw [zeroCoords_blockVec]
      exact hNmem
    have hconj : v * N * v⁻¹ ∈ coordBlockSL K (zeroCoords ε (blockVec (p := p) i)) :=
      conj_mem_zeroBlock (hζ := hprim.pow_eq_one) hprim hal hv' hN'
    rw [← map_mul, ← map_inv, ← map_mul]
    exact Subgroup.mem_map_of_mem φ (by rw [zeroBlock, ← hz]; exact hconj)
  have hcard : 2 ≤ (blockCoords ε i).card := by
    rw [← hz, card_zeroCoords ε (blockVec (p := p) i)]
    have hdim : (rootPB g).dim = 2 := SpNS.rootPB_dim_eq_two hp hp2 hpK' hgd hpK
    have hf : (Finset.univ.filter fun m : Fin s => blockVec (p := p) i m = 0) = {i} := by
      ext m
      rw [Finset.mem_filter, Finset.mem_singleton]
      exact ⟨fun h => blockVec_eq_zero_iff.mp h.2,
        fun h => ⟨Finset.mem_univ _, blockVec_eq_zero_iff.mpr h⟩⟩
    rw [hf, Finset.card_singleton, hdim]
    omega
  have hq : CFSG.Assembly.IsQuasisimple ((zeroBlock g ε i).map φ) := by
    have hq₀ : CFSG.IsQuasisimple (zeroBlock g ε i) := by
      rw [zeroBlock]
      exact isQuasisimple_coordBlockSL hcard h4
    have hinj₀ : Function.Injective (φ.comp (zeroBlock g ε i).subtype) := by
      rw [injective_iff_map_eq_one]
      intro N h1
      have hscal : (N : SpecialLinearGroup (Fin n) K) ∈ scalars n K := by
        rw [scalars_eq_center]
        refine hφc (N : SpecialLinearGroup (Fin n) K) ?_
        have h1' : φ (N : SpecialLinearGroup (Fin n) K) = 1 := h1
        rw [h1']
        exact Subgroup.one_mem _
      have hN' : (N : SpecialLinearGroup (Fin n) K) ∈ coordBlockSL K (blockCoords ε i) := by
        simpa only [zeroBlock] using N.2
      obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin s)
        (by simpa using (show 1 < s by omega)) i
      let a0 : Fin (rootPB g).dim := ⟨0, rootPB_dim_pos g⟩
      let m : Fin n := ε.symm (Sum.inl (a0, j))
      have hm : m ∉ blockCoords ε i := by
        rw [mem_blockCoords_inl (ε := ε) (i := i) (x := m) (a := a0) (m := j) (by simp [m])]
        exact hji
      exact Subtype.ext (TypeA.eq_one_of_mem_coordBlockSL_of_mem_scalars hm hN' hscal)
    have hrange : (φ.comp (zeroBlock g ε i).subtype).range = (zeroBlock g ε i).map φ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hqmap : CFSG.IsQuasisimple ((zeroBlock g ε i).map φ) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        ((MonoidHom.ofInjective hinj₀).trans (MulEquiv.subgroupCongr hrange)) hq₀
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hqmap
  refine ⟨hJle, CFSG.Assembly.IsSubnormal.step hJle ?_ (CFSG.Assembly.IsSubnormal.refl _), hq⟩
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hJle).mpr hnorm

theorem theta_apply_col_eq {S : Finset (Fin s)}
    {M : SpecialLinearGroup (Fin s) (AdjoinRoot g)}
    (hM : M ∈ coordBlockSL (AdjoinRoot g) S) {m : Fin s} (hm : m ∉ S)
    (a : Fin (rootPB g).dim) (x : Fin n) :
    (theta g ε M : Matrix (Fin n) (Fin n) K) x (ε.symm (Sum.inl (a, m))) =
      if x = ε.symm (Sum.inl (a, m)) then 1 else 0 := by
  classical
  have hfix : (M : Matrix (Fin s) (Fin s) (AdjoinRoot g)) *ᵥ
      (Pi.single m ((rootPB g).basis a) : Fin s → AdjoinRoot g) =
      Pi.single m ((rootPB g).basis a) := by
    funext i
    rw [mulVec_single_apply', mem_coordBlockSL_iff.mp hM i m (Or.inr hm)]
    by_cases h : i = m <;> simp [h]
  have hx : frameCoords g ε ((Pi.single m ((rootPB g).basis a) : Fin s → AdjoinRoot g),
      (0 : Fin r → K)) = Pi.single (ε.symm (Sum.inl (a, m))) 1 :=
    frameCoords_single_basis (g := g) ε a m
  have h := frameCoords_frameForm (g := g) (ε := ε)
    (u := (theta g ε M : Matrix (Fin n) (Fin n) K))
    ((Pi.single m ((rootPB g).basis a) : Fin s → AdjoinRoot g), (0 : Fin r → K))
  rw [coe_theta, frameForm_thetaMat, blockAct_apply, hfix, hx] at h
  have h2 := congrFun h.symm x
  rw [Matrix.mulVec_single_one] at h2
  simpa [Matrix.col_apply, Pi.single_apply, coe_theta] using h2

theorem theta_diag_eq_one {S : Finset (Fin s)}
    {M : SpecialLinearGroup (Fin s) (AdjoinRoot g)}
    (hM : M ∈ coordBlockSL (AdjoinRoot g) S) {m : Fin s} (hm : m ∉ S)
    (a : Fin (rootPB g).dim) {x : Fin n} (hx : ε x = Sum.inl (a, m)) :
    (theta g ε M : Matrix (Fin n) (Fin n) K) x x = 1 := by
  have hx' : x = ε.symm (Sum.inl (a, m)) := by
    rw [← Equiv.symm_apply_apply ε x, hx]
  rw [hx']
  simpa using theta_apply_col_eq (ε := ε) hM hm a (ε.symm (Sum.inl (a, m)))

theorem isComponentOf_pairBlock (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K + 1)
    (hgd : g ∣ cyclotomic p K) (hM : IsBlockTorusModel φ ε hC A) (hφs : Function.Surjective φ)
    (hφc : ∀ x, φ x ∈ Subgroup.center L' → x ∈ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (hs : 3 ≤ s) {i j : Fin s} (hij : i ≠ j) {w : L'} (hwJ : w ∈ (pairBlock g ε i j).map φ)
    (hcomm : ∀ t : Fin s → ZMod p, MulAut.conj w * MulAut.conj (φ (torusSL ε hC hCp (ofAdd t))) =
      MulAut.conj (φ (torusSL ε hC hCp (ofAdd t))) * MulAut.conj w ↔ t i = t j) :
    IsComponentOf ((pairBlock g ε i j).map φ) (ggHypCent A w) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  haveI : Finite (AdjoinRoot g) := finite_adjoinRoot
  have hpK' : (p : K) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  have hprim : IsPrimitiveRoot (AdjoinRoot.root g) p := root_isPrimitiveRoot hp hpK' hgd
  have hal : Aligned hprim.pow_eq_one (pairVec (p := p) i j) := aligned_pairVec i j
  have hz : classSet (pairVec (p := p) i j) 1 = {i, j} := classSet_pairVec i j
  have hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K) := ker_le_center_of φ hφc
  have hK' : ¬ p ∣ Nat.card K - 1 := SpNS.not_dvd_card_sub_one hp hp2 hpK
  have hnsplit : ∀ c : K, c ^ p = 1 → c = 1 := fun c hc =>
    OrdPNS.eq_one_of_pow_eq_one hp hK' hc
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hwJ
  obtain ⟨M, hMmem, rfl⟩ := Subgroup.mem_map.mp hy
  have hM' : M ∈ coordBlockSL (AdjoinRoot g) (classSet (pairVec (p := p) i j) 1) := by
    rw [hz]
    exact hMmem
  have hcomm_pair : ∀ (t : Fin s → ZMod p), t i = t j →
      theta g ε M * SLNS.nsSL ε hC (fun m => (t m).val) =
        SLNS.nsSL ε hC (fun m => (t m).val) * theta g ε M := by
    intro t htij
    refine comm_classBlock_of_torus (β := pairVec (p := p) i j) (c := 1) ?_ hM'
    intro m n hm hn
    have hm' : m = i ∨ m = j := by
      have h1 : m ∈ classSet (pairVec (p := p) i j) 1 := mem_classSet.mpr hm
      rw [classSet_pairVec] at h1
      simpa using h1
    have hn' : n = i ∨ n = j := by
      have h1 : n ∈ classSet (pairVec (p := p) i j) 1 := mem_classSet.mpr hn
      rw [classSet_pairVec] at h1
      simpa using h1
    rcases hm' with rfl | rfl <;> rcases hn' with rfl | rfl <;> simp [htij]
  have hJle : (pairBlock g ε i j).map φ ≤ ggHypCent A (φ (theta g ε M)) := by
    intro x hx
    obtain ⟨z, hzJ, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨N, hNmem, rfl⟩ := Subgroup.mem_map.mp hzJ
    unfold ggHypCent
    simp only [Subgroup.mem_iInf, mem_ggFix]
    intro a ha
    obtain ⟨haA, hcommA⟩ := ha
    obtain ⟨t, rfl⟩ := (hM.mem_iff hCp).mp haA
    have htij : t i = t j := (hcomm t).mp hcommA
    have hcommι : theta g ε N * SLNS.nsSL ε hC (fun m => (t m).val) =
        SLNS.nsSL ε hC (fun m => (t m).val) * theta g ε N := by
      have hNclass : N ∈ coordBlockSL (AdjoinRoot g) (classSet (pairVec (p := p) i j) 1) := by
        rw [hz]
        exact hNmem
      refine comm_classBlock_of_torus (β := pairVec (p := p) i j) (c := 1) ?_ hNclass
      intro m n hm hn
      have hm' : m = i ∨ m = j := by
        have h1 : m ∈ classSet (pairVec (p := p) i j) 1 := mem_classSet.mpr hm
        rw [classSet_pairVec] at h1
        simpa using h1
      have hn' : n = i ∨ n = j := by
        have h1 : n ∈ classSet (pairVec (p := p) i j) 1 := mem_classSet.mpr hn
        rw [classSet_pairVec] at h1
        simpa using h1
      rcases hm' with rfl | rfl <;> rcases hn' with rfl | rfl <;> simp [htij]
    have hcommφ : φ (theta g ε N) * φ (torusSL ε hC hCp (ofAdd t)) =
        φ (torusSL ε hC hCp (ofAdd t)) * φ (theta g ε N) := by
      rw [torusSL_apply, ← map_mul, ← map_mul, hcommι]
    show MulAut.conj (φ (torusSL ε hC hCp (ofAdd t))) (φ (theta g ε N)) = φ (theta g ε N)
    rw [MulAut.conj_apply, hcommφ.symm, mul_assoc, mul_inv_cancel, mul_one]
  have hβ : MulAut.conj (φ (torusSL ε hC hCp (ofAdd (pairVec (p := p) i j)))) ∈ A :=
    (hM.mem_iff hCp).mpr ⟨pairVec (p := p) i j, rfl⟩
  have hMβ : φ (theta g ε M) * φ (torusSL ε hC hCp (ofAdd (pairVec (p := p) i j))) =
      φ (torusSL ε hC hCp (ofAdd (pairVec (p := p) i j))) * φ (theta g ε M) := by
    rw [torusSL_apply, ← map_mul, ← map_mul]
    exact congrArg φ (hcomm_pair (pairVec (p := p) i j) (by simp [pairVec]))
  have hβcomm : MulAut.conj (φ (theta g ε M)) *
      MulAut.conj (φ (torusSL ε hC hCp (ofAdd (pairVec (p := p) i j)))) =
      MulAut.conj (φ (torusSL ε hC hCp (ofAdd (pairVec (p := p) i j)))) *
        MulAut.conj (φ (theta g ε M)) := by
    calc MulAut.conj (φ (theta g ε M)) *
          MulAut.conj (φ (torusSL ε hC hCp (ofAdd (pairVec (p := p) i j))))
        = MulAut.conj (φ (theta g ε M) *
            φ (torusSL ε hC hCp (ofAdd (pairVec (p := p) i j)))) :=
          (map_mul MulAut.conj _ _).symm
      _ = MulAut.conj (φ (torusSL ε hC hCp (ofAdd (pairVec (p := p) i j))) *
            φ (theta g ε M)) := by rw [hMβ]
      _ = MulAut.conj (φ (torusSL ε hC hCp (ofAdd (pairVec (p := p) i j)))) *
          MulAut.conj (φ (theta g ε M)) := map_mul MulAut.conj _ _
  have hcent : ggHypCent A (φ (theta g ε M)) ≤ Subgroup.centralizer
      {φ (torusSL ε hC hCp (ofAdd (pairVec (p := p) i j)))} := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfix : MulAut.conj (φ (torusSL ε hC hCp (ofAdd (pairVec (p := p) i j)))) x = x := by
      unfold ggHypCent at hx
      simp only [Subgroup.mem_iInf, mem_ggFix] at hx
      exact hx (MulAut.conj (φ (torusSL ε hC hCp (ofAdd (pairVec (p := p) i j)))))
        ⟨hβ, hβcomm⟩
    rw [MulAut.conj_apply] at hfix
    calc x * φ (torusSL ε hC hCp (ofAdd (pairVec (p := p) i j)))
        = (φ (torusSL ε hC hCp (ofAdd (pairVec (p := p) i j))) * x *
            (φ (torusSL ε hC hCp (ofAdd (pairVec (p := p) i j))))⁻¹) *
            φ (torusSL ε hC hCp (ofAdd (pairVec (p := p) i j))) := by rw [hfix]
      _ = φ (torusSL ε hC hCp (ofAdd (pairVec (p := p) i j))) * x := by group
  have hCen := centralizer_torusSL_eq_map (ψ := φ) (ε := ε) (hC := hC) (hCp := hCp)
    hker hnsplit hφs (pairVec (p := p) i j)
  have hnorm : ggHypCent A (φ (theta g ε M)) ≤
      Subgroup.normalizer ((pairBlock g ε i j).map φ : Set L') := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp (hCen ▸ hcent hx)
    obtain ⟨z, hzJ, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨N, hNmem, rfl⟩ := Subgroup.mem_map.mp hzJ
    have hv' : v * SLNS.nsSL ε hC (fun m => (pairVec (p := p) i j m).val) =
        SLNS.nsSL ε hC (fun m => (pairVec (p := p) i j m).val) * v :=
      Subgroup.mem_centralizer_singleton_iff.mp hv
    have hNclass : N ∈ coordBlockSL (AdjoinRoot g) (classSet (pairVec (p := p) i j) 1) := by
      rw [hz]
      exact hNmem
    have hconj : v * theta g ε N * v⁻¹ ∈
        (coordBlockSL (AdjoinRoot g) (classSet (pairVec (p := p) i j) 1)).map (theta g ε) :=
      conj_mem_classBlock (hζ := hprim.pow_eq_one) hprim hal (one_ne_zero) hv' hNclass
    rw [← map_mul, ← map_inv, ← map_mul]
    have hpairEq : pairBlock g ε i j =
        (coordBlockSL (AdjoinRoot g) ({i, j} : Finset (Fin s))).map (theta g ε) := rfl
    rw [hpairEq]
    rw [hz] at hconj
    exact Subgroup.mem_map_of_mem φ hconj
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hL4 : 4 ≤ Nat.card (AdjoinRoot g) := four_le_natCard_adjoinRoot hprim hp3
  have hq : CFSG.Assembly.IsQuasisimple ((pairBlock g ε i j).map φ) := by
    have hcard : 2 ≤ ({i, j} : Finset (Fin s)).card := by rw [Finset.card_pair hij]
    have hq₀ : CFSG.IsQuasisimple
        (coordBlockSL (AdjoinRoot g) ({i, j} : Finset (Fin s))) :=
      isQuasisimple_coordBlockSL hcard hL4
    have hinj₀ : Function.Injective
        ((φ.comp (theta g ε)).comp (coordBlockSL (AdjoinRoot g) {i, j}).subtype) := by
      rw [injective_iff_map_eq_one]
      intro N h1
      have hscal : (theta g ε (N : SpecialLinearGroup (Fin s) (AdjoinRoot g)) :
          SpecialLinearGroup (Fin n) K) ∈ scalars n K := by
        rw [scalars_eq_center]
        refine hφc (theta g ε (N : SpecialLinearGroup (Fin s) (AdjoinRoot g))) ?_
        have h1' : φ (theta g ε (N : SpecialLinearGroup (Fin s) (AdjoinRoot g))) = 1 := h1
        rw [h1']
        exact Subgroup.one_mem _
      obtain ⟨m, -, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := ({i, j} : Finset (Fin s))) (t := Finset.univ) (by
          rw [Finset.card_univ, Fintype.card_fin, Finset.card_pair hij]
          omega)
      let a0 : Fin (rootPB g).dim := ⟨0, rootPB_dim_pos g⟩
      let x : Fin n := ε.symm (Sum.inl (a0, m))
      have hx : ε x = Sum.inl (a0, m) := by simp [x]
      have hdiag : (theta g ε (N : SpecialLinearGroup (Fin s) (AdjoinRoot g)) :
          Matrix (Fin n) (Fin n) K) x x = 1 :=
        theta_diag_eq_one N.2 hm a0 hx
      obtain ⟨c, -, hc⟩ := mem_scalars.mp hscal
      have hc1 : (c : K) = 1 := by
        have h1c : (scalar (Fin n) (c : K)) x x = 1 := by rw [← hc]; exact hdiag
        simpa [scalar_apply] using h1c
      have hθ1 : theta g ε (N : SpecialLinearGroup (Fin s) (AdjoinRoot g)) = 1 := by
        apply Subtype.ext
        rw [hc, hc1]
        simp
      have hN1 : (N : SpecialLinearGroup (Fin s) (AdjoinRoot g)) = 1 :=
        theta_injective (g := g) (ε := ε) (by simpa using hθ1)
      exact Subtype.ext hN1
    have hrange : ((φ.comp (theta g ε)).comp
        (coordBlockSL (AdjoinRoot g) {i, j}).subtype).range =
        (coordBlockSL (AdjoinRoot g) {i, j}).map (φ.comp (theta g ε)) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hqmap : CFSG.IsQuasisimple
        ((coordBlockSL (AdjoinRoot g) {i, j}).map (φ.comp (theta g ε))) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        ((MonoidHom.ofInjective hinj₀).trans (MulEquiv.subgroupCongr hrange)) hq₀
    have hmap : (pairBlock g ε i j).map φ =
        (coordBlockSL (AdjoinRoot g) ({i, j} : Finset (Fin s))).map (φ.comp (theta g ε)) := by
      rw [pairBlock]
      exact Subgroup.map_map _ _ _
    rw [hmap]
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hqmap
  refine ⟨hJle, CFSG.Assembly.IsSubnormal.step hJle ?_ (CFSG.Assembly.IsSubnormal.refl _), hq⟩
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hJle).mpr hnorm

theorem dvd_card_map_zeroBlock (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K + 1)
    (hgd : g ∣ cyclotomic p K)
    (hφc : ∀ x, φ x ∈ Subgroup.center L' → x ∈ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (hs : 2 ≤ s) (i : Fin s) : p ∣ Nat.card ((zeroBlock g ε i).map φ) := by
  have hp : p.Prime := Fact.out
  have hpK' : (p : K) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  have hC : (rootMat g).det = 1 :=
    det_rootMat hp (SpNS.not_dvd_card_sub_one (Fact.out : p.Prime) hp2 hpK) hpK' hgd
  have hCp : rootMat g ^ p = 1 := rootMat_pow_eq_one hp hpK' hgd
  let v : Fin s → ZMod p := Pi.single i 1
  have hti : v i = 1 := by simp [v]
  have ht0 : v ≠ 0 := by
    intro h
    exact one_ne_zero (by rw [← hti, h]; simp)
  have hmem : φ (torusSL ε hC hCp (ofAdd v)) ∈ (zeroBlock g ε i).map φ :=
    Subgroup.mem_map_of_mem φ (torusSL_single_mem_zeroBlock i)
  have hdvd := Subgroup.orderOf_dvd_natCard ((zeroBlock g ε i).map φ) hmem
  rwa [orderOf_eq_prime (pow_torusSL φ v)
    (map_torusSL_ne_one (φ := φ) hp2 hpK hgd hφc ht0)] at hdvd

theorem dvd_card_map_pairBlock (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K + 1)
    (hgd : g ∣ cyclotomic p K)
    (hφc : ∀ x, φ x ∈ Subgroup.center L' → x ∈ Subgroup.center (SpecialLinearGroup (Fin n) K))
    {i j : Fin s} (hij : i ≠ j) : p ∣ Nat.card ((pairBlock g ε i j).map φ) := by
  have hp : p.Prime := Fact.out
  have hpK' : (p : K) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  have hC : (rootMat g).det = 1 :=
    det_rootMat hp (SpNS.not_dvd_card_sub_one (Fact.out : p.Prime) hp2 hpK) hpK' hgd
  have hCp : rootMat g ^ p = 1 := rootMat_pow_eq_one hp hpK' hgd
  let v : Fin s → ZMod p := Pi.single i 1 - Pi.single j 1
  have hti : v i = 1 := by simp [v, Pi.sub_apply, hij, Ne.symm hij]
  have ht0 : v ≠ 0 := by
    intro h
    exact one_ne_zero (by rw [← hti, h]; simp)
  have hmem : φ (torusSL ε hC hCp (ofAdd v)) ∈ (pairBlock g ε i j).map φ :=
    Subgroup.mem_map_of_mem φ (torusSL_sub_single_mem_pairBlock hp2 hgd hij)
  have hdvd := Subgroup.orderOf_dvd_natCard ((pairBlock g ε i j).map φ) hmem
  rwa [orderOf_eq_prime (pow_torusSL φ v)
    (map_torusSL_ne_one (φ := φ) hp2 hpK hgd hφc ht0)] at hdvd

end CFSG.StandardType.SlNsRootGen

end
