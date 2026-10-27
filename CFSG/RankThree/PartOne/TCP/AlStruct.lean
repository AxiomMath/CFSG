module

public import CFSG.RankThree.PartOne.TCP.SurvStruct

public section

namespace CFSG.RankThree.PartOne.TCP

open Polynomial Module CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCSpIsotypic CFSG.RankThree.PartOne.KCSpComm CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped commutatorElement MatrixGroups

section Idx

variable {K : Type} [Field K] [Finite K] {f p : ℕ}

theorem sp4_idx_data {x : StatedSp 2 K} {ℓ : ℕ} (hD : SpData ℓ f 2 p K x)
    (hord : orderOf (Nat.card K : ZMod p) = 2) (blocks : SpPrimaryBlocks ℓ f p x (proj 2 K x)) :
    Subsingleton (SpBlockIdx x) ∧ ∀ b : SpBlockIdx x,
      primaryMultiplicity (spEnd x) (b.1 : K[X]) = 2 ∧
        ((b.1 : K[X]) ≠ X - 1 → (b.1 : K[X]).natDegree = 2) := by
  classical
  have hsq := hD.squarefree
  have hp := hD.prime
  have hxp := hD.pow_eq_one
  have hX : spEnd x ^ p = 1 := spEnd_pow hxp
  have hsum : ∑ a : primaryFactors (spEnd x),
      (a : K[X]).natDegree * primaryMultiplicity (spEnd x) (a : K[X]) = 4 := by
    rw [← finrank_eq_sum_degree_mul_multiplicity hsq]
    simp [Module.finrank_fintype_fun_eq_card]
  have hdeg : ∀ a : primaryFactors (spEnd x), (a : K[X]) ≠ X - 1 → 2 ≤ (a : K[X]).natDegree := by
    intro a ha1
    have h2 := two_dvd_natDegree_of_mem hp hX hord a.2 ha1
    have h0 : 0 < (a : K[X]).natDegree :=
      Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors a.2)
    omega
  have hfin : ∀ a : primaryFactors (spEnd x), finrank K (primaryComponent (spEnd x) (a : K[X])) =
      (a : K[X]).natDegree * primaryMultiplicity (spEnd x) (a : K[X]) := fun a => by
    have : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
    exact finrank_primaryComponent (spEnd x) (a : K[X])
  have hmpos : ∀ a : primaryFactors (spEnd x), 1 ≤ primaryMultiplicity (spEnd x) (a : K[X]) := by
    intro a
    have h1 : 1 ≤ finrank K (primaryComponent (spEnd x) (a : K[X])) :=
      Submodule.one_le_finrank_iff.mpr (primaryComponent_ne_bot hsq a.2)
    rw [hfin a] at h1
    rcases Nat.eq_zero_or_pos (primaryMultiplicity (spEnd x) (a : K[X])) with h0 | h0
    · rw [h0, mul_zero] at h1
      omega
    · exact h0
  obtain ⟨s, hs, -⟩ := blocks.rank
  have hfixed : ∀ a : primaryFactors (spEnd x), (a : K[X]) = X - 1 →
      2 ≤ primaryMultiplicity (spEnd x) (a : K[X]) := by
    intro a ha1
    have h1 : 1 ≤ finrank K (primaryComponent (spEnd x) (a : K[X])) :=
      Submodule.one_le_finrank_iff.mpr (primaryComponent_ne_bot hsq a.2)
    have h2 := hfin a
    have hV : primaryComponent (spEnd x) (a : K[X]) = primaryComponent (spEnd x) (X - 1) := by
      rw [ha1]
    have hd1 : (a : K[X]).natDegree = 1 := by
      rw [ha1]
      exact natDegree_X_sub_one
    rw [hV] at h1 h2
    rw [hd1, one_mul] at h2
    omega
  have hterm : ∀ a : SpBlockIdx x, 2 ≤ (a.1 : K[X]).natDegree *
      primaryMultiplicity (spEnd x) (a.1 : K[X]) ∧ ((a.1 : K[X]) ≠ X - 1 →
      4 ≤ (a.1 : K[X]).natDegree * primaryMultiplicity (spEnd x) (a.1 : K[X])) := by
    intro a
    have hm := a.2
    have hd1 : 1 ≤ (a.1 : K[X]).natDegree :=
      Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors a.1.2)
    refine ⟨by nlinarith, fun ha1 => ?_⟩
    have := hdeg a.1 ha1
    nlinarith
  have hsub : Subsingleton (SpBlockIdx x) := by
    refine ⟨fun a b => ?_⟩
    by_contra hab
    have hab' : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
    obtain ⟨ha2, ha4⟩ := hterm a
    obtain ⟨hb2, hb4⟩ := hterm b
    have hle : (a.1 : K[X]).natDegree * primaryMultiplicity (spEnd x) (a.1 : K[X]) +
        (b.1 : K[X]).natDegree * primaryMultiplicity (spEnd x) (b.1 : K[X]) ≤ 4 := by
      rw [← hsum, ← Finset.sum_pair hab' (f := fun c : primaryFactors (spEnd x) =>
        (c : K[X]).natDegree * primaryMultiplicity (spEnd x) (c : K[X]))]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    by_cases ha1 : (a.1 : K[X]) = X - 1
    · have hb1 : (b.1 : K[X]) ≠ X - 1 := fun h => hab' (Subtype.ext (ha1.trans h.symm))
      have := hb4 hb1
      linarith
    · have := ha4 ha1
      linarith
  refine ⟨hsub, fun b => ?_⟩
  obtain ⟨hb2, hb4⟩ := hterm b
  have hle : (b.1 : K[X]).natDegree * primaryMultiplicity (spEnd x) (b.1 : K[X]) ≤ 4 := by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun c : primaryFactors (spEnd x) =>
      (c : K[X]).natDegree * primaryMultiplicity (spEnd x) (c : K[X])) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ b.1)
  by_cases hb1 : (b.1 : K[X]) = X - 1
  · have hd1 : (b.1 : K[X]).natDegree = 1 := by
      rw [hb1]
      exact natDegree_X_sub_one
    have hm4 : primaryMultiplicity (spEnd x) (b.1 : K[X]) ≤ 4 := by
      rw [hd1, one_mul] at hle
      exact hle
    have hdimV : finrank K (primaryComponent (spEnd x) (X - 1)) = 2 * s := hs
    have hmeq : primaryMultiplicity (spEnd x) (b.1 : K[X]) =
        finrank K (primaryComponent (spEnd x) (X - 1)) := by
      have := hfin b.1
      rw [hd1, one_mul] at this
      rw [hb1] at this ⊢
      exact this.symm
    have hm4' : primaryMultiplicity (spEnd x) (b.1 : K[X]) ≠ 4 := by
      intro h4
      have htop : primaryComponent (spEnd x) (X - 1) = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        rw [← hmeq, h4]
        simp [Module.finrank_fintype_fun_eq_card]
      have hx1 : spEnd x = 1 := by
        refine LinearMap.ext fun v => ?_
        have hv : v ∈ primaryComponent (spEnd x) (X - 1) := htop ▸ Submodule.mem_top
        rw [blocks.fixed_eq] at hv
        exact sub_eq_zero.mp (by simpa using LinearMap.mem_ker.mp hv)
      have : x = 1 := spLin_injective (Units.ext (by rw [map_one, Units.val_one]; exact hx1))
      have h1 : orderOf x = 1 := by rw [this, orderOf_one]
      have := hD.order
      have := hp.one_lt
      omega
    have hm2 : primaryMultiplicity (spEnd x) (b.1 : K[X]) = 2 := by
      have := b.2
      have h3 : primaryMultiplicity (spEnd x) (b.1 : K[X]) ≠ 3 := by
        intro h3
        rw [h3] at hmeq
        omega
      omega
    exact ⟨hm2, fun h => absurd hb1 h⟩
  · have hdg := hdeg b.1 hb1
    have hm2 := b.2
    have hd2 : (b.1 : K[X]).natDegree = 2 := by nlinarith
    have hmm : primaryMultiplicity (spEnd x) (b.1 : K[X]) = 2 := by nlinarith
    exact ⟨hmm, fun _ => hd2⟩

omit [Finite K] in
theorem sp4_idx_empty_commute {x : StatedSp 2 K} {ℓ : ℕ} (hD : SpData ℓ f 2 p K x)
    (blocks : SpPrimaryBlocks ℓ f p x (proj 2 K x)) (hE : IsEmpty (SpBlockIdx x)) :
    ∀ g ∈ Subgroup.centralizer ({x} : Set (StatedSp 2 K)),
      ∀ h ∈ Subgroup.centralizer ({x} : Set (StatedSp 2 K)), g * h = h * g := by
  classical
  have facts := hD.blockFacts blocks
  have hCM : ∀ g ∈ Subgroup.centralizer ({x} : Set (StatedSp 2 K)),
      spLin 2 K g ∈ unitaryCentralizer (spForm 2 K) (spLin 2 K x) := fun g hg => by
    rw [unitaryCentralizer_spForm_eq_map]
    exact Subgroup.mem_map_of_mem _ hg
  intro g hg h hh
  have hcomm := Subgroup.commutator_mem_commutator (hCM g hg) (hCM h hh)
  rw [commutator_unitaryCentralizer_eq_iSup blocks facts, iSup_of_empty, Subgroup.mem_bot,
    ← map_commutatorElement, map_eq_one_iff _ spLin_injective] at hcomm
  exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm)

theorem sp4_component_of_idx {x : StatedSp 2 K} (hD : SpData 2 f 2 p K x)
    (hord : orderOf (Nat.card K : ZMod p) = 2) (blocks : SpPrimaryBlocks 2 f p x (proj 2 K x))
    (b : SpBlockIdx x) :
    CFSG.IsQuasisimple ↥(spPull x (b.1 : K[X])) ∧
      spPull x (b.1 : K[X]) ≤ Subgroup.centralizer ({x} : Set (StatedSp 2 K)) ∧
      (∀ g ∈ Subgroup.centralizer ({x} : Set (StatedSp 2 K)), ∀ d ∈ spPull x (b.1 : K[X]),
        g * d * g⁻¹ ∈ spPull x (b.1 : K[X])) ∧
      (∀ g ∈ Subgroup.centralizer ({x} : Set (StatedSp 2 K)),
        ∀ h ∈ Subgroup.centralizer ({x} : Set (StatedSp 2 K)), ⁅g, h⁆ ∈ spPull x (b.1 : K[X])) ∧
      (∀ g ∈ Subgroup.centralizer ({x} : Set (StatedSp 2 K)),
        (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ spPull x (b.1 : K[X])) := by
  classical
  obtain ⟨hsub, -⟩ := sp4_idx_data hD hord blocks
  have facts := hD.blockFacts blocks
  have hall : ∀ a : SpBlockIdx x, a = b := fun a => hsub.elim a b
  have hjoin : (⨆ a : SpBlockIdx x, specialBlock (spForm 2 K) (spLin 2 K x) (a.1 : K[X])) =
      specialBlock (spForm 2 K) (spLin 2 K x) (b.1 : K[X]) := by
    apply le_antisymm
    · exact iSup_le fun a => by rw [hall a]
    · exact le_iSup (fun a : SpBlockIdx x =>
        specialBlock (spForm 2 K) (spLin 2 K x) (a.1 : K[X])) b
  have hCM : ∀ g ∈ Subgroup.centralizer ({x} : Set (StatedSp 2 K)),
      spLin 2 K g ∈ unitaryCentralizer (spForm 2 K) (spLin 2 K x) := fun g hg => by
    rw [unitaryCentralizer_spForm_eq_map]
    exact Subgroup.mem_map_of_mem _ hg
  have hchar : CharP K 2 := hD.charP
  refine ⟨spPull_isQuasisimple (facts b.1) b.2, spPull_le_centralizer x _,
    spPull_normalized x _, ?_, ?_⟩
  · intro g hg h hh
    have hcomm := Subgroup.commutator_mem_commutator (hCM g hg) (hCM h hh)
    rw [commutator_unitaryCentralizer_eq_iSup blocks facts, hjoin] at hcomm
    change spLin 2 K ⁅g, h⁆ ∈ specialBlock (spForm 2 K) (spLin 2 K x) (b.1 : K[X])
    rw [map_commutatorElement]
    exact hcomm
  · intro g hg hk
    obtain ⟨k, hk⟩ := hk
    have hg2 : g ^ 2 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one g
    have hdet : ∀ a : primaryFactors (spEnd x), ∃ hgl : spLin 2 K g ∈
        gl_centralizer (spLin 2 K x),
        blockDetHom (spLin 2 K x) (a : K[X]) ⟨spLin 2 K g, hgl⟩ = 1 := by
      intro a
      refine ⟨(hCM g hg).2, ?_⟩
      have : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
      have : CharP (AdjoinRoot (a : K[X])) 2 :=
        charP_of_injective_algebraMap (algebraMap K (AdjoinRoot (a : K[X]))).injective 2
      refine units_eq_one_of_pow_two_pow (k := k) ?_
      rw [← map_pow]
      have h1 : (⟨spLin 2 K g, (hCM g hg).2⟩ : gl_centralizer (spLin 2 K x)) ^ 2 ^ k = 1 := by
        apply Subtype.ext
        change (spLin 2 K g) ^ 2 ^ k = 1
        rw [← map_pow, hg2, map_one]
      rw [h1, map_one]
    have hmem := mem_iSup_specialBlock_of_det_one hD blocks facts (hCM g hg) hdet
    rw [hjoin] at hmem
    exact hmem

end Idx

section BlockEquiv

universe u

variable {K : Type} [Field K] {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}
  {a : primaryFactors (x : Module.End K V)}

theorem nonempty_specialBlock_equiv_su {ℓ f' : ℕ}
    (hE : UnitaryFieldData ℓ f' (AdjoinRoot (a : K[X])))
    {Hf : primaryComponent (x : Module.End K V) (a : K[X]) →ₛₗ[hE.bar]
      primaryComponent (x : Module.End K V) (a : K[X]) →ₗ[AdjoinRoot (a : K[X])]
        AdjoinRoot (a : K[X])}
    (φ : orbitFactor B x (a : K[X]) ≃* sesqUnitaryGroup Hf)
    (hφ : ∀ (g : orbitFactor B x (a : K[X])) (v : V)
      (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
      blockApply (φ g : blockGL (x : Module.End K V) (a : K[X])) v hv =
        ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v) :
    Nonempty (specialBlock B x (a : K[X]) ≃* sesqSpecialUnitaryGroup Hf) := by
  let ι : sesqUnitaryGroup Hf →* blockGL (x : Module.End K V) (a : K[X]) :=
    (sesqUnitaryGroup Hf).subtype
  have hspec := specialBlock_eq_kerImage (B := B) φ ι hφ
  let D : sesqUnitaryGroup Hf →* (AdjoinRoot (a : K[X]))ˣ :=
    (blockGLDet (x : Module.End K V) (a : K[X])).comp ι
  have hker : D.ker = (sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf) := by
    ext δ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_sesqSpecialUnitaryGroup]
    constructor
    · intro h
      refine ⟨δ.2, ?_⟩
      have := congrArg Units.val h
      simpa [D, ι, blockGLDet] using this
    · rintro ⟨-, h⟩
      apply Units.ext
      simpa [D, ι, blockGLDet] using h
  obtain ⟨e⟩ := nonempty_kerImage_mulEquiv (orbitFactor B x (a : K[X])) φ D
  exact ⟨(((MulEquiv.subgroupCongr hspec).trans e).trans (MulEquiv.subgroupCongr hker)).trans
    (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf))⟩

end BlockEquiv

section Sp4Block

variable {K : Type} [Field K] [Finite K] {f p : ℕ}

theorem charP_two_of_natCard_eq {F : Type} [Field F] [Finite F] {m : ℕ}
    (h : Nat.card F = 2 ^ m) : CharP F 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card]; exact h)

omit [Finite K] in
theorem sp4_fixed_block_equiv {x : StatedSp 2 K} (hD : SpData 2 f 2 p K x)
    (blocks : SpPrimaryBlocks 2 f p x (proj 2 K x))
    (hmem : (X - 1 : K[X]) ∈ primaryFactors (spEnd x))
    (hm2 : primaryMultiplicity (spEnd x) (X - 1 : K[X]) = 2) :
    Nonempty (spPull x (X - 1 : K[X]) ≃* SL(2, K)) := by
  classical
  have hsq := hD.squarefree
  have hq4 : 4 ≤ Nat.card K := by have := hD.four_le; rw [hD.card]; omega
  obtain ⟨φ, hφ⟩ := blocks.fixedFactor hmem
  have hO : ({(X - 1 : K[X]), reciprocalPolynomial (X - 1 : K[X])} : Set K[X]) = {X - 1} := by
    rw [KCSpIsotypic.reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton]
  have hnd := blocks.fixed_nondegenerate
  have hBalt : ((spForm 2 K).restrict (primaryComponent (spEnd x) (X - 1))).IsAlt :=
    fun z => spForm_isAlt z.1
  have hfr : finrank K (primaryComponent (spEnd x) (X - 1)) = 2 := by
    have h1 := primaryMultiplicity_X_sub_C_eq (spEnd x) (1 : K)
    rw [C_1] at h1
    exact h1.symm.trans hm2
  let φ' : orbitFactor (spForm 2 K) (spLin 2 K x) (X - 1 : K[X]) ≃*
      sesqUnitaryGroup ((spForm 2 K).restrict (primaryComponent (spEnd x) (X - 1))) :=
    (spOrbitEquiv x hO).trans φ
  have hφ' : ∀ (g : orbitFactor (spForm 2 K) (spLin 2 K x) (X - 1 : K[X]))
      (v : primaryComponent (spEnd x) (X - 1)),
      ((((φ' g : sesqUnitaryGroup ((spForm 2 K).restrict
          (primaryComponent (spEnd x) (X - 1)))) : LinearMap.GeneralLinearGroup K
            (primaryComponent (spEnd x) (X - 1))) : Module.End K
              (primaryComponent (spEnd x) (X - 1))) v : Fin 2 ⊕ Fin 2 → K) =
        ((g : LinearMap.GeneralLinearGroup K (Fin 2 ⊕ Fin 2 → K)) :
          Module.End K (Fin 2 ⊕ Fin 2 → K)) (v : Fin 2 ⊕ Fin 2 → K) := fun g v => by
    rw [MulEquiv.trans_apply, hφ, spEnd_orbitEquiv]
  have hQS := isQuasisimple_sesqUnitaryGroup_of_alt hBalt hnd (by omega) (Or.inl hq4)
  have hperf : Group.IsPerfect (orbitFactor (spForm 2 K) (spLin 2 K x) (X - 1 : K[X])) :=
    @isPerfect_of_surjective _ _ _ _ φ'.symm.toMonoidHom φ'.symm.surjective hQS.1
  have hdet : ∀ (g : LinearMap.GeneralLinearGroup K (Fin 2 ⊕ Fin 2 → K))
      (hg : g ∈ orbitFactor (spForm 2 K) (spLin 2 K x) (X - 1 : K[X])),
      blockDetHom (spLin 2 K x) (X - 1 : K[X]) ⟨g, orbitFactor_le_gl_centralizer hg⟩ = 1 := by
    intro g hg
    exact eq_one_of_perfect_of_comm hperf (fun u v => mul_comm u v)
      ((blockDetHom (spLin 2 K x) (X - 1 : K[X])).comp
        (Subgroup.inclusion orbitFactor_le_gl_centralizer)) ⟨g, hg⟩
  have hspec : specialBlock (spForm 2 K) (spLin 2 K x) (X - 1 : K[X]) =
      orbitFactor (spForm 2 K) (spLin 2 K x) (X - 1 : K[X]) := by
    ext g
    rw [KCUnitary.mem_specialBlock]
    exact ⟨fun h => h.1, fun hg => ⟨hg, orbitFactor_le_gl_centralizer hg, hdet g hg⟩⟩
  obtain ⟨s, hs, ⟨e⟩⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp hBalt hnd
  have hs1 : s = 1 := by omega
  subst hs1
  let e1 : spPull x (X - 1 : K[X]) ≃*
      specialBlock (spForm 2 K) (spLin 2 K x) (X - 1 : K[X]) :=
    comapSpLinEquiv _ (fun _ hg => spLin_mem_sesq_of_mem_specialBlock hg)
  exact ⟨(((e1.trans (MulEquiv.subgroupCongr hspec)).trans φ').trans e).trans
    (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K).symm⟩

theorem sp4_selfdual_block_equiv {x : StatedSp 2 K} (hD : SpData 2 f 2 p K x)
    (hord : orderOf (Nat.card K : ZMod p) = 2) (blocks : SpPrimaryBlocks 2 f p x (proj 2 K x))
    (b : primaryFactors (spEnd x)) (hb1 : (b : K[X]) ≠ X - 1)
    (hdeg : (b : K[X]).natDegree = 2) (hm2 : primaryMultiplicity (spEnd x) (b : K[X]) = 2) :
    ∃ (F' : Type) (_ : Field F') (_ : Finite F') (_ : CharP F' 2), Nat.card F' = Nat.card K ∧
      Nonempty (spPull x (b : K[X]) ≃* SL(2, F')) := by
  classical
  have hp := hD.prime
  have hX : spEnd x ^ p = 1 := spEnd_pow hD.pow_eq_one
  have hself : reciprocalPolynomial (b : K[X]) = b :=
    reciprocalPolynomial_eq_of_mem hp hX hord b.2 hb1
  have hS := blocks.selfDual b hb1 hself
  obtain ⟨d, hdeg2d, hpd, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, hφ⟩ := hS.exists_half
  have hd1 : d = 1 := by omega
  subst hd1
  have hO : ({(b : K[X]), reciprocalPolynomial (b : K[X])} : Set K[X]) = {(b : K[X])} := by
    rw [hself, Set.pair_eq_singleton]
  let φ' : orbitFactor (spForm 2 K) (spLin 2 K x) (b : K[X]) ≃* sesqUnitaryGroup Hf :=
    (spOrbitEquiv x hO).trans φ
  have hφ' : ∀ (g : orbitFactor (spForm 2 K) (spLin 2 K x) (b : K[X])) (v : Fin 2 ⊕ Fin 2 → K)
      (hv : v ∈ primaryComponent (spEnd x) (b : K[X])),
      blockApply (φ' g : blockGL (spEnd x) (b : K[X])) v hv =
        ((g : LinearMap.GeneralLinearGroup K (Fin 2 ⊕ Fin 2 → K)) :
          Module.End K (Fin 2 ⊕ Fin 2 → K)) v := fun g v hv => by
    rw [MulEquiv.trans_apply]
    have := hφ (spOrbitEquiv x hO g) v hv
    rw [this, spEnd_orbitEquiv]
  obtain ⟨e₁⟩ := nonempty_specialBlock_equiv_su (B := spForm 2 K) (x := spLin 2 K x) (a := b) hE
    φ' hφ'
  have hfr : Module.finrank (AdjoinRoot (b : K[X]))
      (primaryComponent (spEnd x) (b : K[X])) = 2 := hm2
  obtain ⟨e₂⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf hHfl hfr
  have hcard : Nat.card hE.fixedField = Nat.card K := by
    rw [hE.card_fixedField, hD.card, mul_one]
  have hfin : Finite hE.fixedField := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact Nat.card_pos.ne')
  have hcharK : CharP K 2 := hD.charP
  have hcharF : CharP hE.fixedField 2 := by
    have h2 : Nat.card hE.fixedField = 2 ^ f := by rw [hcard, hD.card]
    exact charP_two_of_natCard_eq h2
  let e0 : spPull x (b : K[X]) ≃* specialBlock (spForm 2 K) (spLin 2 K x) (b : K[X]) :=
    comapSpLinEquiv _ (fun _ hg => spLin_mem_sesq_of_mem_specialBlock hg)
  exact ⟨hE.fixedField, inferInstance, hfin, hcharF, hcard, ⟨(e0.trans e₁).trans e₂⟩⟩

theorem sp4_block_equiv {x : StatedSp 2 K} (hD : SpData 2 f 2 p K x)
    (hord : orderOf (Nat.card K : ZMod p) = 2) (blocks : SpPrimaryBlocks 2 f p x (proj 2 K x))
    (b : SpBlockIdx x) :
    ∃ (F' : Type) (_ : Field F') (_ : Finite F') (_ : CharP F' 2), Nat.card F' = Nat.card K ∧
      Nonempty (spPull x (b.1 : K[X]) ≃* SL(2, F')) := by
  obtain ⟨-, hdata⟩ := sp4_idx_data hD hord blocks
  obtain ⟨hm2, hdeg⟩ := hdata b
  by_cases hb1 : (b.1 : K[X]) = X - 1
  · obtain ⟨⟨b0, hb0⟩, hbm⟩ := b
    change b0 = X - 1 at hb1
    subst hb1
    have hcharK : CharP K 2 := hD.charP
    have : Nat.card K = Nat.card K := rfl
    exact ⟨K, inferInstance, inferInstance, hcharK, rfl, sp4_fixed_block_equiv hD blocks hb0 hm2⟩
  · exact sp4_selfdual_block_equiv hD hord blocks b.1 hb1 (hdeg hb1) hm2

end Sp4Block

end CFSG.RankThree.PartOne.TCP
