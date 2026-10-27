module

public import CFSG.RankThree.PartOne.KC.SymplecticTorusDefs
public import CFSG.RankThree.PartOne.KC.SymplecticTorusDet
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicOrbits
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeAbstract
public import CFSG.RankThree.PartOne.KC.SymplecticDefiningCriterion

public section

namespace CFSG.RankThree.PartOne.KCSpComm

open Polynomial Module Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ClassicalInvolution.Models
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open scoped commutatorElement

variable {r : ℕ} {K : Type} [Field K]

structure SpData (ℓ f r p : ℕ) (K : Type) [Field K] (x : StatedSp r K) : Prop where
  prime_ell : ℓ.Prime
  one_le_f : 1 ≤ f
  card : Nat.card K = ℓ ^ f
  four_le : 3 < ℓ ^ f
  two_le_r : 2 ≤ r
  prime : p.Prime
  three_lt : 3 < p
  ne : p ≠ ℓ
  order : orderOf x = p

namespace SpData

variable {ℓ f p : ℕ} {x : StatedSp r K} (D : SpData ℓ f r p K x)
include D

theorem finite : Finite K := Nat.finite_of_card_ne_zero (by
  rw [D.card]
  exact (pow_pos D.prime_ell.pos f).ne')

theorem neZero : NeZero r := ⟨by have := D.two_le_r; omega⟩

theorem one_le_r : 1 ≤ r := by have := D.two_le_r; omega

theorem pow_eq_one : x ^ p = 1 := by
  rw [← D.order]
  exact pow_orderOf_eq_one x

theorem five_le : 5 ≤ p := by
  by_contra hlt
  have h3 := D.three_lt
  have h4 : p = 4 := by omega
  have := D.prime
  rw [h4] at this
  exact absurd this (by norm_num)

theorem odd : Odd p := D.prime.odd_of_ne_two (by have := D.three_lt; omega)

theorem charP : CharP K ℓ := by
  have : Finite K := D.finite
  have := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨D.prime_ell⟩
  exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, D.card])

theorem pK : (p : K) ≠ 0 := by
  have := D.charP
  intro h
  rw [CharP.cast_eq_zero_iff K ℓ] at h
  exact D.ne ((Nat.prime_dvd_prime_iff_eq D.prime_ell D.prime).mp h).symm

theorem primaryData : AltPrimaryData (spForm r K) (spLin r K x) :=
  altPrimaryData_spLin D.pK D.pow_eq_one

theorem squarefree : Squarefree (minpoly K (spEnd x)) := D.primaryData.squarefree

theorem blockFacts (blocks : SpPrimaryBlocks ℓ f p x (proj r K x)) :
    ∀ h : primaryFactors (spEnd x), SpBlockFacts (spForm r K) (spLin r K x) h :=
  fun h => spBlockFacts D.five_le D.four_le D.card D.squarefree blocks h

end SpData

section Elementary

variable [Finite K]

omit [Finite K] in
theorem spLin_eq_gspLin (s : StatedSp r K) : spLin r K s = gspLin r K (spXg s) := rfl

omit [Finite K] in
theorem spXg_mem_ker_multiplier [NeZero r] (s : StatedSp r K) : spXg s ∈ (multiplier r K).ker := by
  show multiplier r K (spXg s) = 1
  refine multiplier_eq (spXg s) (μ := 1) ?_
  rw [Units.val_one, one_smul]
  exact SymplecticTorusWeyl.mem_statedSp_iff.mp s.2

omit [Finite K] in
theorem sesqUnitaryGroup_le_range_gspLin :
    sesqUnitaryGroup (spForm r K) ≤ (gspLin r K).range := by
  intro g hg
  rw [← range_spLin] at hg
  obtain ⟨s, rfl⟩ := hg
  exact ⟨spXg s, rfl⟩

omit [Finite K] in
theorem mem_ker_multiplier_of_isometry [NeZero r] {A : gsp r K}
    (hA : gspLin r K A ∈ sesqUnitaryGroup (spForm r K)) : A ∈ (multiplier r K).ker := by
  rw [← range_spLin] at hA
  obtain ⟨s, hs⟩ := hA
  have : A = spXg s := gspLin_injective hs.symm
  subst this
  exact spXg_mem_ker_multiplier s

omit [Finite K] in
theorem spForm_gspLin [NeZero r] (A : gsp r K) (u v : Fin r ⊕ Fin r → K) :
    spForm r K (((gspLin r K A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) u)
      (((gspLin r K A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) v) =
      (multiplier r K A : K) * spForm r K u v := by
  change spForm r K ((A : GL (Fin r ⊕ Fin r) K) *ᵥ u) ((A : GL (Fin r ⊕ Fin r) K) *ᵥ v) = _
  rw [spForm_mulVec]
  have h : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ *
      SymplecticPairs.gram K r *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (multiplier r K A : K) • SymplecticPairs.gram K r := multiplier_spec A
  rw [h]
  change (Matrix.toBilin' ((multiplier r K A : K) • SymplecticPairs.gram K r)) u v = _
  rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
  rfl

omit [Finite K] in
theorem mem_gl_centralizer_of_mem_centralizer {x : StatedSp r K} {m : gsp r K}
    (hm : m ∈ Subgroup.centralizer ({spXg x} : Set (gsp r K))) :
    gspLin r K m ∈ gl_centralizer (spLin r K x) := by
  rw [mem_gl_centralizer]
  have h : m * spXg x = spXg x * m := Subgroup.mem_centralizer_singleton_iff.mp hm
  have h2 : gspLin r K (m * spXg x) = gspLin r K (spXg x * m) := by rw [h]
  rw [map_mul, map_mul] at h2
  have h3 : ((gspLin r K m : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
      Module.End K (Fin r ⊕ Fin r → K)) *
      ((spLin r K x : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) =
      ((spLin r K x : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) *
      ((gspLin r K m : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) := by
    rw [← Units.val_mul, ← Units.val_mul]
    exact congrArg Units.val h2
  exact h3

omit [Finite K] in
theorem mem_centralizer_of_mem_gl_centralizer {x : StatedSp r K} {m : gsp r K}
    (hm : gspLin r K m ∈ gl_centralizer (spLin r K x)) :
    m ∈ Subgroup.centralizer ({spXg x} : Set (gsp r K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  refine gspLin_injective ?_
  rw [map_mul, map_mul]
  exact Units.ext (mem_gl_centralizer.mp hm).eq

end Elementary

section Derived

variable {ℓ f p : ℕ} {x : StatedSp r K}

theorem specialBlock_le_range_gspLin (a : K[X]) :
    specialBlock (spForm r K) (spLin r K x) a ≤ (gspLin r K).range := fun _ hg =>
  sesqUnitaryGroup_le_range_gspLin (specialBlock_le_unitaryCentralizer hg).1

theorem mem_iSup_specialBlock_of_det_one (D : SpData ℓ f r p K x)
    (blocks : SpPrimaryBlocks ℓ f p x (proj r K x))
    (facts : ∀ h : primaryFactors (spEnd x), SpBlockFacts (spForm r K) (spLin r K x) h)
    {c : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)}
    (hc : c ∈ unitaryCentralizer (spForm r K) (spLin r K x))
    (hdet : ∀ a : primaryFactors (spEnd x), ∃ hg : c ∈ gl_centralizer (spLin r K x),
      blockDetHom (spLin r K x) (a : K[X]) ⟨c, hg⟩ = 1) :
    c ∈ ⨆ a : SpBlockIdx x, specialBlock (spForm r K) (spLin r K x) (a.1 : K[X]) := by
  classical
  obtain ⟨hcomm, hgen⟩ := directProduct_GL blocks
  have hH := D.primaryData
  have hfinι : Finite (reciprocalOrbits (spEnd x)) :=
    ((Finset.finite_toSet (primaryFactors (spEnd x))).image
      (fun h : K[X] => ({h, reciprocalPolynomial h} : Set K[X]))).to_subtype
  have : Fintype (reciprocalOrbits (spEnd x)) := Fintype.ofFinite _
  choose a ha hO using fun O : reciprocalOrbits (spEnd x) => (Set.mem_image _ _ _).mp O.2
  set C := gl_centralizer (spLin r K x) with hC
  let L : reciprocalOrbits (spEnd x) →
      Subgroup (LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) := fun O =>
    supportedUnitary (spForm r K) (spLin r K x) (O : Set K[X])
  have hLC : ∀ O, L O ≤ C := fun O => supportedUnitary_le_gl_centralizer _
  let L' : reciprocalOrbits (spEnd x) → Subgroup C := fun O => (L O).subgroupOf C
  let Dh : ∀ O : reciprocalOrbits (spEnd x), C →* (AdjoinRoot (a O))ˣ := fun O =>
    blockDetHom (spLin r K x) (a O)
  have hcomm' : Pairwise fun O O' : reciprocalOrbits (spEnd x) =>
      ∀ u v : C, u ∈ L' O → v ∈ L' O' → Commute u v := by
    intro O O' hne u v hu hv
    exact Subtype.ext (hcomm O O.2 O' O'.2 (fun h => hne (Subtype.ext h)) _ hu _ hv).eq
  have hD : ∀ O O' : reciprocalOrbits (spEnd x), O ≠ O' → ∀ g ∈ L' O', Dh O g = 1 := by
    intro O O' hne g hg
    have hdisj := hH.reciprocalOrbits_disjoint O.2 O'.2 (fun h => hne (Subtype.ext h))
    have haO : a O ∈ (O : Set K[X]) := by
      rw [← hO O]
      exact Or.inl rfl
    have hnot : a O ∉ (O' : Set K[X]) := fun h => Set.disjoint_left.mp hdisj haO h
    exact blockDetHom_eq_one_of_fix g.2 fun v hv => hg.2 (a O) (ha O) hnot v hv
  have hcC : c ∈ C := hc.2
  have hc' : (⟨c, hcC⟩ : C) ∈ ⨆ O, L' O := by
    have h1 : c ∈ ⨆ O, L O := by
      rw [hgen]
      exact hc
    have h2 : (⨆ O, L O).comap C.subtype = ⨆ O, (L O).comap C.subtype :=
      comap_iSup_of_le_range (Subgroup.subtype_injective C) fun O => by
        rw [Subgroup.range_subtype]
        exact hLC O
    have h3 : (⟨c, hcC⟩ : C) ∈ (⨆ O, L O).comap C.subtype := h1
    rw [h2] at h3
    exact h3
  have h1 : ∀ O, Dh O ⟨c, hcC⟩ = 1 := fun O => (hdet ⟨a O, ha O⟩).choose_spec
  have hmem := mem_iSup_inf_ker_of_comm L' hcomm' Dh hD hc' h1
  have hmem' : c ∈ (⨆ O, L' O ⊓ (Dh O).ker).map C.subtype := ⟨_, hmem, rfl⟩
  rw [Subgroup.map_iSup] at hmem'
  refine (iSup_le (fun O => ?_) : (⨆ O, (L' O ⊓ (Dh O).ker).map C.subtype) ≤ _) hmem'
  rintro _ ⟨g, ⟨hgL, hgD⟩, rfl⟩
  have hgOF : (g : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) ∈
      orbitFactor (spForm r K) (spLin r K x) (a O) := by
    rw [orbitFactor_spForm, hO O]
    exact hgL
  have hSB : (g : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) ∈
      specialBlock (spForm r K) (spLin r K x) (a O) :=
    mem_specialBlock.mpr ⟨hgOF, g.2, hgD⟩
  by_cases hm : 2 ≤ primaryMultiplicity (spEnd x) (a O)
  · exact le_iSup (fun b : SpBlockIdx x => specialBlock (spForm r K) (spLin r K x) (b.1 : K[X]))
      ⟨⟨a O, ha O⟩, hm⟩ hSB
  · have hbot := (facts ⟨a O, ha O⟩).special_bot (Nat.le_of_lt_succ (not_le.mp hm))
    rw [hbot] at hSB
    have h1 : (g : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) = 1 :=
      Subgroup.mem_bot.mp hSB
    show (g : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) ∈ _
    rw [h1]
    exact one_mem _

end Derived

section Blocks

variable {ℓ f p : ℕ} {x : StatedSp r K}

@[expose] noncomputable def spBlockGSp (x : StatedSp r K) (a : K[X]) : Subgroup (gsp r K) :=
  (specialBlock (spForm r K) (spLin r K x) a).comap (gspLin r K)

theorem mem_spBlockGSp {a : K[X]} {A : gsp r K} :
    A ∈ spBlockGSp x a ↔ gspLin r K A ∈ specialBlock (spForm r K) (spLin r K x) a := Iff.rfl

theorem map_spBlockGSp (a : K[X]) :
    (spBlockGSp x a).map (gspLin r K) = specialBlock (spForm r K) (spLin r K x) a :=
  Subgroup.map_comap_eq_self (specialBlock_le_range_gspLin a)

theorem spBlockGSp_le_centralizer (a : K[X]) :
    spBlockGSp x a ≤ Subgroup.centralizer ({spXg x} : Set (gsp r K)) := fun _ hA =>
  mem_centralizer_of_mem_gl_centralizer (specialBlock_le_unitaryCentralizer hA).2

theorem spBlockGSp_le_ker_multiplier [NeZero r] (a : K[X]) :
    spBlockGSp x a ≤ (multiplier r K).ker := fun _ hA =>
  mem_ker_multiplier_of_isometry (specialBlock_le_unitaryCentralizer hA).1

theorem conj_mem_spBlockGSp [NeZero r] {a : K[X]} {m g : gsp r K}
    (hm : m ∈ Subgroup.centralizer ({spXg x} : Set (gsp r K))) (hg : g ∈ spBlockGSp x a) :
    m * g * m⁻¹ ∈ spBlockGSp x a := by
  have h := conj_mem_specialBlock_of_similitude (B := spForm r K) (x := spLin r K x) (a := a)
    (m := gspLin r K m) (g := gspLin r K g) (mem_gl_centralizer_of_mem_centralizer hm)
    (μ := (multiplier r K m : K)) (fun u v => spForm_gspLin m u v) hg
  rw [mem_spBlockGSp, map_mul, map_mul, map_inv]
  exact h

theorem isQuasisimple_spBlockGSp
    (facts : ∀ h : primaryFactors (spEnd x), SpBlockFacts (spForm r K) (spLin r K x) h)
    (a : primaryFactors (spEnd x)) (hm : 2 ≤ primaryMultiplicity (spEnd x) (a : K[X])) :
    CFSG.IsQuasisimple (spBlockGSp x (a : K[X])) :=
  isQuasisimple_comap_of_le_range gspLin_injective (specialBlock_le_range_gspLin _)
    ((facts a).quasisimple hm)

theorem orbitFactor_le_range_gspLin (a : K[X]) :
    orbitFactor (spForm r K) (spLin r K x) a ≤ (gspLin r K).range := fun _ hg =>
  sesqUnitaryGroup_le_range_gspLin (orbitFactor_le_unitaryCentralizer hg).1

theorem commutator_centralizer_gsp [NeZero r] (D : SpData ℓ f r p K x)
    (blocks : SpPrimaryBlocks ℓ f p x (proj r K x))
    (facts : ∀ h : primaryFactors (spEnd x), SpBlockFacts (spForm r K) (spLin r K x) h) :
    ⁅Subgroup.centralizer ({spXg x} : Set (gsp r K)),
        Subgroup.centralizer ({spXg x} : Set (gsp r K))⁆ =
      ⨆ a : SpBlockIdx x, spBlockGSp x (a.1 : K[X]) := by
  have hcomap : (⨆ a : SpBlockIdx x, specialBlock (spForm r K) (spLin r K x) (a.1 : K[X])).comap
      (gspLin r K) = ⨆ a : SpBlockIdx x, spBlockGSp x (a.1 : K[X]) :=
    comap_iSup_of_le_range gspLin_injective fun a => specialBlock_le_range_gspLin _
  apply le_antisymm
  · refine Subgroup.commutator_le.mpr fun m hm m' hm' => ?_
    rw [← hcomap, Subgroup.mem_comap]
    have hmg := mem_gl_centralizer_of_mem_centralizer hm
    have hmg' := mem_gl_centralizer_of_mem_centralizer hm'
    have hcM : ⁅m, m'⁆ ∈ Subgroup.centralizer ({spXg x} : Set (gsp r K)) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hm hm') (inv_mem hm)) (inv_mem hm')
    have hcC := mem_gl_centralizer_of_mem_centralizer hcM
    have hmult : multiplier r K ⁅m, m'⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
    have hiso : gspLin r K ⁅m, m'⁆ ∈ sesqUnitaryGroup (spForm r K) := by
      rw [mem_sesqUnitaryGroup]
      intro u v
      rw [spForm_gspLin, hmult, Units.val_one, one_mul]
    refine mem_iSup_specialBlock_of_det_one D blocks facts (c := gspLin r K ⁅m, m'⁆)
      ⟨hiso, hcC⟩ (fun a => ⟨hcC, ?_⟩)
    have hcomm : (⟨gspLin r K ⁅m, m'⁆, hcC⟩ : gl_centralizer (spLin r K x)) =
        ⁅(⟨gspLin r K m, hmg⟩ : gl_centralizer (spLin r K x)), ⟨gspLin r K m', hmg'⟩⁆ := by
      apply Subtype.ext
      simp only [commutatorElement_def, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcomm, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  · refine iSup_le fun a => ?_
    obtain ⟨a, hm⟩ := a
    have h1 : spBlockGSp x (a : K[X]) =
        ⁅(orbitFactor (spForm r K) (spLin r K x) (a : K[X])).comap (gspLin r K),
          (orbitFactor (spForm r K) (spLin r K x) (a : K[X])).comap (gspLin r K)⁆ := by
      rw [← comap_commutator_of_le_range gspLin_injective (orbitFactor_le_range_gspLin _)
        (orbitFactor_le_range_gspLin _)]
      unfold spBlockGSp
      rw [(facts a).commutator_eq hm]
    show spBlockGSp x (a : K[X]) ≤ _
    rw [h1]
    exact Subgroup.commutator_mono
      (fun _ hA => mem_centralizer_of_mem_gl_centralizer (orbitFactor_le_gl_centralizer hA))
      (fun _ hA => mem_centralizer_of_mem_gl_centralizer (orbitFactor_le_gl_centralizer hA))

end Blocks

section Setting

variable {ℓ f p : ℕ} {x : StatedSp r K}

theorem spCenterUnits_le_centralizer (x : StatedSp r K) :
    spCenterUnits x ≤ Subgroup.centralizer ({spXg x} : Set (gsp r K)) := by
  intro A hA
  apply mem_centralizer_of_mem_gl_centralizer
  rw [mem_gl_centralizer]
  obtain ⟨hz, -⟩ := hA
  exact (mem_commutant _).mp hz

theorem spLinearAutGroup_eq_range : spLinearAutGroup r K = (conjAut r K).range := by
  rw [spLinearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]

theorem spDescent (D : SpData ℓ f r p K x) :
    (conjAut r K).range.Normal ∧
    (∀ α β : MulAut (StatedProj (StatedSp r K)), α * β * α⁻¹ * β⁻¹ ∈ (conjAut r K).range) ∧
    (spSemilinearAutGroup r K).index ∣ 2 := by
  obtain ⟨-, -, -, -, -, hDnorm, hcomm, hindex, -⟩ :=
    SteinbergBY.symplectic_prime_semilinear_field_descent D.prime_ell D.one_le_f D.two_le_r D.card
  rw [← spLinearAutGroup_eq_range]
  exact ⟨hDnorm, hcomm, hindex⟩

theorem exists_unique_lift {ℓ f r p : ℕ} {K : Type} [Field K] (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hr : 2 ≤ r) (hK : Nat.card K = ℓ ^ f) (hq : 3 < ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p)
    (hpℓ : p ≠ ℓ) (t : MulAut (StatedProj (StatedSp r K)))
    (ht : t ∈ (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))).range) (htp : orderOf t = p) :
    (∃! x : StatedSp r K, orderOf x = p ∧ MulAut.conj (proj r K x) = t) ∧
    ∀ x : StatedSp r K, orderOf x = p → MulAut.conj (proj r K x) = t →
      SpData ℓ f r p K x ∧ SpPrimaryBlocks ℓ f p x (proj r K x) := by
  have hinfin : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact (pow_pos hℓ.pos f).ne')
  have hr1 : 1 ≤ r := by omega
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact hq
  have hinj := KCSymplectic.conj_injective_statedProj_statedSp (r := r) (K := K) hr h4
  obtain ⟨τ, hτ⟩ := ht
  have hτp : orderOf τ = p := by
    rw [← htp, ← hτ]
    exact (orderOf_injective _ hinj τ).symm
  obtain ⟨hex, hblocks⟩ := symplectic_cross_prime_primary_centralizer_blocks hℓ hf hK hp
    (by omega) hpℓ hr1 τ hτp
  refine ⟨?_, ?_⟩
  · obtain ⟨x₀, ⟨hx₀a, hx₀o⟩, hx₀u⟩ := hex
    refine ⟨x₀, ⟨hx₀o, by rw [hx₀a, hτ]⟩, ?_⟩
    rintro y ⟨hyo, hyt⟩
    exact hx₀u y ⟨hinj (hyt.trans hτ.symm), hyo⟩
  · intro x hxo hxt
    have hxa : proj r K x = τ := hinj (hxt.trans hτ.symm)
    refine ⟨⟨hℓ, hf, hK, hq, hr, hp, hp3, hpℓ, hxo⟩, ?_⟩
    rw [hxa]
    exact hblocks x hxa hxo

theorem spProjSetting [NeZero r] (D : SpData ℓ f r p K x)
    (blocks : SpPrimaryBlocks ℓ f p x (proj r K x))
    (B : Subgroup (MulAut (StatedProj (StatedSp r K))))
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))).range ≤ B) :
    ProjSetting (conjAut r K) B (conjAut r K (spXg x)) (multiplier r K).ker
      (Subgroup.centralizer ({spXg x} : Set (gsp r K))) (spCenterUnits x)
      (fun a : SpBlockIdx x => spBlockGSp x (a.1 : K[X])) := by
  have : Finite K := D.finite
  have facts := D.blockFacts blocks
  have hN := conjAut_range_inf_centralizer_eq_map (K := K) D.one_le_r D.odd D.pow_eq_one
  refine
    { ker_central := fun u hu g => conjAut_ker_central D.one_le_r hu g
      D_normal := (spDescent D).1
      H_normal := ?_
      H_le_B := ?_
      N_eq := hN
      F_le_M := fun a => spBlockGSp_le_centralizer (x := x) (a.1 : K[X])
      F_le_Hs := fun a => spBlockGSp_le_ker_multiplier (x := x) (a.1 : K[X])
      F_normal := fun a m hm g hg => conj_mem_spBlockGSp (x := x) (a := (a.1 : K[X])) hm hg
      F_quasi := fun a => isQuasisimple_spBlockGSp (x := x) facts a.1 a.2
      M_derived := commutator_centralizer_gsp D blocks facts
      ZM_le_M := spCenterUnits_le_centralizer x
      ZM_central := ?_
      ker_le_ZM := ?_
      centralizes := ?_ }
  · rw [map_ker_multiplier]
    exact CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  · rw [map_ker_multiplier]
    exact hB
  · intro y hy m hm
    obtain ⟨hz, hc⟩ := hy
    have hm' : Commute ((gspLin r K m : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) (spLin r K x : Module.End K (Fin r ⊕ Fin r → K)) :=
      mem_gl_centralizer.mp (mem_gl_centralizer_of_mem_centralizer hm)
    have := commute_of_mem_centerSim (x := spLin r K x) ⟨hz, hc⟩ hm'
    exact gspLin_injective (by rw [map_mul, map_mul]; exact this.eq)
  · intro A hA
    obtain ⟨c, hc⟩ := (conjAut_eq_one_iff D.one_le_r A).mp hA
    refine smul_mem_centerSim (x := spLin r K x) (c : K) fun v => ?_
    rw [gspLin_apply, hc]
    ext i
    simp [Matrix.mulVec_diagonal, Matrix.scalar_apply, Matrix.GeneralLinearGroup.coe_scalar]
  · intro Y hY hcomm
    have hmem := mem_center_of_commute_specialBlocks (x := x) blocks facts
      (Y := gspLin r K Y) (mem_gl_centralizer_of_mem_centralizer hY) (fun a ha g hg => ?_)
    · exact mem_spCenterUnits.mpr hmem
    · rw [← map_spBlockGSp] at hg
      obtain ⟨g₀, hg₀, rfl⟩ := hg
      exact (commutatorElement_eq_one_iff_commute.mp (hcomm ⟨a, ha⟩ g₀ hg₀)).map (gspLin r K)

end Setting

end CFSG.RankThree.PartOne.KCSpComm
