module

public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitComp
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClFactors
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicBlocks
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLCompParts

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank Polynomial CFSG.RankThree.PartOne CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped commutatorElement

namespace SevSpNs

theorem exists_pow_mul_pow_eq_one {E : Type*} [Field E] {p : ℕ} (hp : p.Prime) {z₁ z₂ : Eˣ}
    (h₁ : z₁ ^ p = 1) (h₂ : z₂ ^ p = 1) :
    ∃ a b : ℕ, a < p ∧ b < p ∧ (a ≠ 0 ∨ b ≠ 0) ∧ z₁ ^ a * z₂ ^ b = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  by_cases hz : z₁ = 1
  · exact ⟨1, 0, hp.one_lt, hp.pos, Or.inl one_ne_zero, by rw [hz, one_pow, pow_zero, mul_one]⟩
  have hord : orderOf z₁ = p := orderOf_eq_prime h₁ hz
  have hprim : IsPrimitiveRoot (z₁ : E) p :=
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hord)
  obtain ⟨c, hc, hzc⟩ := hprim.eq_pow_of_pow_eq_one (ξ := (z₂ : E))
    (by rw [← Units.val_pow_eq_pow_val, h₂, Units.val_one])
  have hz2 : z₂ = z₁ ^ c := Units.ext (by rw [Units.val_pow_eq_pow_val, hzc])
  by_cases hc0 : c = 0
  · exact ⟨0, 1, hp.pos, hp.one_lt, Or.inr one_ne_zero, by
      rw [hz2, hc0]
      simp⟩
  · refine ⟨p - c, 1, by omega, hp.one_lt, Or.inr one_ne_zero, ?_⟩
    rw [pow_one, hz2, ← pow_add, Nat.sub_add_cancel hc.le, h₁]

variable {r : ℕ} {K : Type} [Field K]

theorem spSupported_le_centralizer (x : StatedSp r K) (O : Set K[X]) :
    spSupported x O ≤ Subgroup.centralizer ({x} : Set (StatedSp r K)) := fun _ hg =>
  Subgroup.mem_centralizer_singleton_iff.mpr (mem_spSupported.mp hg).1

theorem spSupported_normalized (x : StatedSp r K) (O : Set K[X]) :
    ∀ m ∈ Subgroup.centralizer ({x} : Set (StatedSp r K)), ∀ g ∈ spSupported x O,
      m * g * m⁻¹ ∈ spSupported x O := by
  intro m hm g hg
  have hm' : spLin r K m ∈ unitaryCentralizer (spForm r K) (spLin r K x) := by
    rw [unitaryCentralizer_spForm_eq_map]
    exact Subgroup.mem_map_of_mem _ hm
  have := conj_mem_supportedUnitary hm' (show spLin r K g ∈
    supportedUnitary (spForm r K) (spLin r K x) O from hg)
  change spLin r K (m * g * m⁻¹) ∈ supportedUnitary (spForm r K) (spLin r K x) O
  rwa [map_mul, map_mul, map_inv]

theorem normal_subgroupOf_of_normalized {x : StatedSp r K} {N : Subgroup (StatedSp r K)}
    (hN : N ≤ Subgroup.centralizer ({x} : Set (StatedSp r K)))
    (hn : ∀ m ∈ Subgroup.centralizer ({x} : Set (StatedSp r K)), ∀ g ∈ N, m * g * m⁻¹ ∈ N) :
    (N.subgroupOf (Subgroup.centralizer ({x} : Set (StatedSp r K)))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff hN]
  intro g m hg hm
  exact hn m hm g hg

theorem exists_le_spSupported [Finite K] {ℓ f p : ℕ} {x : StatedSp r K}
    (blocks : SpPrimaryBlocks ℓ f p x (proj r K x)) {L : Subgroup (StatedSp r K)}
    (hL : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer {x})) :
    ∃ h ∈ primaryFactors (spEnd x), L ≤ spSupported x {h, reciprocalPolynomial h} := by
  by_contra hno
  push Not at hno
  have hc : ∀ O : reciprocalOrbits (spEnd x),
      spSupported x (O : Set K[X]) ≤ Subgroup.centralizer (L : Set (StatedSp r K)) := by
    rintro ⟨O, hO⟩
    obtain ⟨h, hh, rfl⟩ := hO
    rcases CoordSL.le_or_commutator_eq_bot_of_normal hL (spSupported_le_centralizer x _)
      (normal_subgroupOf_of_normalized (spSupported_le_centralizer x _)
        (spSupported_normalized x _)) with h1 | h1
    · exact absurd h1 (hno h hh)
    · rw [Subgroup.commutator_comm] at h1
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
  have hall : Subgroup.centralizer ({x} : Set (StatedSp r K)) ≤
      Subgroup.centralizer (L : Set (StatedSp r K)) := by
    rw [← blocks.directProduct.2.2]
    exact iSup_le hc
  exact CFSG.LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple hL.2.2
    (hL.1.trans hall)

theorem spLin_mem_orbitFactor {x g : StatedSp r K} {h : K[X]}
    (hg : g ∈ spSupported x {h, reciprocalPolynomial h}) :
    spLin r K g ∈ orbitFactor (spForm r K) (spLin r K x) h := by
  rw [orbitFactor_spForm]
  exact hg

@[expose] noncomputable def factorDet (x : StatedSp r K) (h : K[X]) :
    spSupported x {h, reciprocalPolynomial h} →* (AdjoinRoot h)ˣ :=
  (blockDetHom (spLin r K x) h).comp
    { toFun := fun g => ⟨spLin r K (g : StatedSp r K),
        orbitFactor_le_gl_centralizer (spLin_mem_orbitFactor g.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g g' => Subtype.ext (by simp) }

theorem mem_spPull_of_factorDet {x g : StatedSp r K} {h : K[X]}
    (hg : g ∈ spSupported x {h, reciprocalPolynomial h}) (hd : factorDet x h ⟨g, hg⟩ = 1) :
    g ∈ spPull x h :=
  mem_specialBlock.mpr ⟨spLin_mem_orbitFactor hg,
    orbitFactor_le_gl_centralizer (spLin_mem_orbitFactor hg), hd⟩

theorem commutator_le_spPull (x : StatedSp r K) (h : K[X]) :
    ⁅spSupported x {h, reciprocalPolynomial h}, spSupported x {h, reciprocalPolynomial h}⁆ ≤
      spPull x h := by
  refine Subgroup.commutator_le.mpr fun g hg g' hg' => ?_
  have hmem : ⁅g, g'⁆ ∈ spSupported x {h, reciprocalPolynomial h} :=
    Subgroup.commutator_mem_commutator hg hg' |> fun hc =>
      (Subgroup.commutator_le_self _) hc
  refine mem_spPull_of_factorDet hmem ?_
  have he : (⟨⁅g, g'⁆, hmem⟩ : spSupported x {h, reciprocalPolynomial h}) =
      ⁅(⟨g, hg⟩ : spSupported x {h, reciprocalPolynomial h}), ⟨g', hg'⟩⁆ := rfl
  rw [he, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]

theorem exists_pow_mul_pow_mem_spPull {p : ℕ} (hp : p.Prime) {x u v : StatedSp r K} {h : K[X]}
    [Fact (Irreducible h)] (hu : u ∈ spSupported x {h, reciprocalPolynomial h})
    (hv : v ∈ spSupported x {h, reciprocalPolynomial h}) (hup : u ^ p = 1) (hvp : v ^ p = 1) :
    ∃ a b : ℕ, a < p ∧ b < p ∧ (a ≠ 0 ∨ b ≠ 0) ∧ u ^ a * v ^ b ∈ spPull x h := by
  set U : spSupported x {h, reciprocalPolynomial h} := ⟨u, hu⟩
  set V : spSupported x {h, reciprocalPolynomial h} := ⟨v, hv⟩
  have hU : U ^ p = 1 := Subtype.ext (by simpa [U] using hup)
  have hV : V ^ p = 1 := Subtype.ext (by simpa [V] using hvp)
  obtain ⟨a, b, ha, hb, hab, h1⟩ := exists_pow_mul_pow_eq_one hp
    (z₁ := factorDet x h U) (z₂ := factorDet x h V) (by rw [← map_pow, hU, map_one])
    (by rw [← map_pow, hV, map_one])
  refine ⟨a, b, ha, hb, hab, mem_spPull_of_factorDet (U ^ a * V ^ b).2 ?_⟩
  have he : (⟨u ^ a * v ^ b, (U ^ a * V ^ b).2⟩ : spSupported x {h, reciprocalPolynomial h}) =
      U ^ a * V ^ b := rfl
  rw [he, map_mul, map_pow, map_pow, h1]

theorem eq_spPull_of_le [Finite K] {x : StatedSp r K} {h : K[X]} {L : Subgroup (StatedSp r K)}
    (hL : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer {x}))
    (hLO : L ≤ spSupported x {h, reciprocalPolynomial h})
    (hq : CFSG.IsQuasisimple ↥(spPull x h)) : L = spPull x h := by
  have hLq : CFSG.IsQuasisimple ↥L :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native L).1 hL.2.2
  have hLP : L ≤ spPull x h := by
    rw [← LayerFacts.ggCommutator_eq_of_isQuasisimple hLq]
    exact (Subgroup.commutator_mono hLO hLO).trans (commutator_le_spPull x h)
  have hPc := SpNonsplitComp.isComponentOf_of_normalizes (spPull_le_centralizer x h)
    (spPull_normalized x h) hq
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hL hPc with h1 | h1
  · exact h1
  · exfalso
    apply CFSG.LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple hL.2.2
    rw [Subgroup.commutator_comm] at h1
    exact hLP.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1)

theorem false_of_le_of_commute {G : Type*} [Group G] {L F : Subgroup G}
    (hLq : CFSG.Assembly.IsQuasisimple ↥L) (hLF : L ≤ F)
    (hF : ∀ g ∈ F, ∀ g' ∈ F, g * g' = g' * g) : False := by
  apply CFSG.LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple hLq
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  intro l' hl'
  exact hF l' (hLF hl') l (hLF hl)

theorem card_primeFactors_six : (6 : ℕ).primeFactors.card ≤ 2 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
  decide

theorem fixed_case [Finite K] [CharP K 2] {f p : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f)
    (hp : p.Prime) (hp2 : p ≠ 2) {x : StatedSp r K} (hxp : x ^ p = 1)
    (blocks : SpPrimaryBlocks 2 f p x (proj r K x))
    (hmem : (X - 1 : K[X]) ∈ primaryFactors (spEnd x)) {L : Subgroup (StatedSp r K)}
    (hL : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer {x}))
    (hLF : L ≤ spFixedFactor x) :
    (∀ m ∈ Subgroup.centralizer ({x} : Set (StatedSp r K)), ∀ g ∈ L, m * g * m⁻¹ ∈ L) ∧
      ∀ u ∈ spFixedFactor x, u ^ p = 1 → u ∈ L := by
  have hLq : CFSG.IsQuasisimple ↥L :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native L).1 hL.2.2
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K 2 p).mp h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this).symm
  have hsq : Squarefree (minpoly K (spEnd x)) := (altPrimaryData_spLin hpK hxp).squarefree
  have hdim : 2 ≤ spFixedDim x := by
    obtain ⟨s, hs, -⟩ := blocks.rank
    have hne := primaryComponent_ne_bot hsq hmem
    have hpos : 0 < spFixedDim x := by
      unfold spFixedDim
      exact Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hne)
    have hd : spFixedDim x = 2 * s := hs
    omega
  have key : ∀ P : Subgroup (StatedSp r K), L ≤ P → P ≤ Subgroup.centralizer {x} →
      (∀ m ∈ Subgroup.centralizer ({x} : Set (StatedSp r K)), ∀ g ∈ P, m * g * m⁻¹ ∈ P) →
      CFSG.IsQuasisimple ↥P → L = P := by
    intro P hLP hPC hPn hPq
    have hPc := SpNonsplitComp.isComponentOf_of_normalizes hPC hPn hPq
    rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hL hPc with h1 | h1
    · exact h1
    · exfalso
      apply CFSG.LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple hL.2.2
      rw [Subgroup.commutator_comm] at h1
      exact hLP.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1)
  by_cases h42 : spFixedDim x = 4 ∧ Nat.card K = 2
  ·
    obtain ⟨hq, hodd⟩ := spFixed_four_two h42.2 blocks h42.1
    have hLP : L ≤ ⁅spFixedFactor x, spFixedFactor x⁆ := by
      rw [← LayerFacts.ggCommutator_eq_of_isQuasisimple hLq]
      exact Subgroup.commutator_mono hLF hLF
    have hn := SpNonsplitComp.normalized_commutator (spFixedFactor_normalized x)
    have hLeq := key _ hLP ((commutator_le_self _).trans (spFixedFactor_le_centralizer x)) hn hq
    refine ⟨fun m hm g hg => ?_, fun u hu hup => ?_⟩
    · rw [hLeq] at hg ⊢
      exact hn m hm g hg
    · rw [hLeq]
      exact hodd hp hp2 u hu hup
  · by_cases h22 : spFixedDim x = 2 ∧ Nat.card K = 2
    ·
      exfalso
      have hcard := card_spFixedFactor_of_dim_two blocks h22.1
      rw [h22.2] at hcard
      have hsolv : Group.IsSolvable ↥(spFixedFactor x) :=
        CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
          (by rw [hcard]; exact card_primeFactors_six)
      exact ClNonsplit.not_isQuasisimple_of_le hsolv hLF hLq
    · have hlist : SpFixedListed x := by
        refine ⟨hdim, fun ⟨hd, hk⟩ => ?_⟩
        rcases hk with hk | hk
        · exact h22 ⟨hd, hk⟩
        · rw [hK] at hk
          have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
          rw [hk] at h2
          omega
      have hq := spFixedFactor_isQuasisimple hK Nat.prime_two hf blocks hlist h42
      have hLeq := key _ hLF (spFixedFactor_le_centralizer x) (spFixedFactor_normalized x) hq
      refine ⟨fun m hm g hg => ?_, fun u hu _ => hLeq ▸ hu⟩
      rw [hLeq] at hg ⊢
      exact spFixedFactor_normalized x m hm g hg

open CFSG.LocalAnalysis.ComponentInitial in
theorem isQuasisimple_spPull_selfDual {f d : ℕ} {x : StatedSp r K} {h : primaryFactors (spEnd x)}
    (hself : reciprocalPolynomial (h : K[X]) = h)
    (hE : UnitaryFieldData 2 (f * d) (AdjoinRoot (h : K[X])))
    {Hf : primaryComponent (spEnd x) (h : K[X]) →ₛₗ[hE.bar]
      primaryComponent (spEnd x) (h : K[X]) →ₗ[AdjoinRoot (h : K[X])] AdjoinRoot (h : K[X])}
    (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft)
    (φ : spSupported x {(h : K[X])} ≃* sesqUnitaryGroup Hf)
    (hφ : ∀ (g : spSupported x {(h : K[X])}) (v : Fin r ⊕ Fin r → K)
      (hv : v ∈ primaryComponent (spEnd x) (h : K[X])),
      blockApply (φ g : blockGL (spEnd x) (h : K[X])) v hv = spEnd (g : StatedSp r K) v)
    (hm : 2 ≤ primaryMultiplicity (spEnd x) (h : K[X]))
    (hq : (primaryMultiplicity (spEnd x) (h : K[X]) = 2 → 4 ≤ 2 ^ (f * d)) ∧
      (primaryMultiplicity (spEnd x) (h : K[X]) = 3 → 3 ≤ 2 ^ (f * d))) :
    CFSG.IsQuasisimple ↥(spPull x (h : K[X])) := by
  have hO : ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) = {(h : K[X])} := by
    rw [hself, Set.pair_eq_singleton]
  set φ' : orbitFactor (spForm r K) (spLin r K x) (h : K[X]) ≃* sesqUnitaryGroup Hf :=
    (spOrbitEquiv x hO).trans φ with hφ'def
  have hφ' : ∀ (g : orbitFactor (spForm r K) (spLin r K x) (h : K[X]))
      (v : Fin r ⊕ Fin r → K) (hv : v ∈ primaryComponent (spEnd x) (h : K[X])),
      blockApply (φ' g : blockGL (spEnd x) (h : K[X])) v hv =
        ((g : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
          Module.End K (Fin r ⊕ Fin r → K)) v := by
    intro g v hv
    rw [hφ'def, MulEquiv.trans_apply, hφ (spOrbitEquiv x hO g) v hv, spEnd_orbitEquiv]
  let ι : sesqUnitaryGroup Hf →* blockGL (spEnd x) (h : K[X]) := (sesqUnitaryGroup Hf).subtype
  have hspec := specialBlock_eq_kerImage (B := spForm r K) (a := h) φ' ι hφ'
  let D : sesqUnitaryGroup Hf →* (AdjoinRoot (h : K[X]))ˣ :=
    (blockGLDet (spEnd x) (h : K[X])).comp ι
  have hker : D.ker = (sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf) := by
    ext δ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_sesqSpecialUnitaryGroup]
    constructor
    · intro h1
      refine ⟨δ.2, ?_⟩
      have := congrArg Units.val h1
      simpa [D, ι, blockGLDet] using this
    · rintro ⟨-, h1⟩
      apply Units.ext
      simpa [D, ι, blockGLDet] using h1
  have hquasi : CFSG.IsQuasisimple D.ker := by
    rw [hker]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)).symm
      (isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE hHf hHfl hm hq)
  obtain ⟨e⟩ := nonempty_kerImage_mulEquiv (orbitFactor (spForm r K) (spLin r K x) (h : K[X])) φ' D
  have hSB : CFSG.IsQuasisimple ↥(specialBlock (spForm r K) (spLin r K x) (h : K[X])) := by
    rw [hspec]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hquasi
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (comapSpLinEquiv _ (fun _ hg => spLin_mem_sesq_of_mem_specialBlock hg)).symm hSB

theorem card_primeFactors_unitary_two {n : ℕ} (hn : n = 18 ∨ n = 648) :
    n.primeFactors.card ≤ 2 :=
  LayerCores.card_primeFactors_small hn

open CFSG.LocalAnalysis.ComponentInitial in
theorem isSolvable_spSupported_selfDual [Finite K] {f d : ℕ} {x : StatedSp r K}
    {h : primaryFactors (spEnd x)} (hE : UnitaryFieldData 2 (f * d) (AdjoinRoot (h : K[X])))
    {Hf : primaryComponent (spEnd x) (h : K[X]) →ₛₗ[hE.bar]
      primaryComponent (spEnd x) (h : K[X]) →ₗ[AdjoinRoot (h : K[X])] AdjoinRoot (h : K[X])}
    (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft)
    (φ : spSupported x {(h : K[X])} ≃* sesqUnitaryGroup Hf) (hfd : f * d = 1)
    (hm2 : 2 ≤ primaryMultiplicity (spEnd x) (h : K[X]))
    (hm3 : primaryMultiplicity (spEnd x) (h : K[X]) ≤ 3) :
    Group.IsSolvable ↥(spSupported x {(h : K[X])}) := by
  have h2 : 2 ^ (f * d) = 2 := by rw [hfd, pow_one]
  have hcardU : Nat.card (sesqUnitaryGroup Hf) = 18 ∨ Nat.card (sesqUnitaryGroup Hf) = 648 := by
    rcases (show primaryMultiplicity (spEnd x) (h : K[X]) = 2 ∨
        primaryMultiplicity (spEnd x) (h : K[X]) = 3 by omega) with hm | hm
    · left
      have h1 := (CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl hm (by norm_num)).1
      rw [h2] at h1
      have e : ((2 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
          ∏ i ∈ Finset.Icc 1 2, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 18 := by decide +kernel
      exact_mod_cast h1.trans e
    · right
      have h1 := (CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl hm (by norm_num)).1
      rw [h2] at h1
      have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
          ∏ i ∈ Finset.Icc 1 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 648 := by decide +kernel
      exact_mod_cast h1.trans e
  have hcard : Nat.card ↥(spSupported x {(h : K[X])}) = Nat.card (sesqUnitaryGroup Hf) :=
    Nat.card_congr φ.toEquiv
  exact CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
    (hcard ▸ card_primeFactors_unitary_two hcardU)

theorem isQuasisimple_spPull_of_le [Finite K] {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {x : StatedSp r K} (blocks : SpPrimaryBlocks 2 f p x (proj r K x))
    {h : primaryFactors (spEnd x)} (hX1 : (h : K[X]) ≠ X - 1) {L : Subgroup (StatedSp r K)}
    (hL : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer {x}))
    (hLO : L ≤ spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}) :
    CFSG.IsQuasisimple ↥(spPull x (h : K[X])) := by
  have hLq : CFSG.IsQuasisimple ↥L :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native L).1 hL.2.2
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  by_cases hself : reciprocalPolynomial (h : K[X]) = h
  ·
    have hS := blocks.selfDual h hX1 hself
    obtain ⟨d, -, -, -, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, hφ⟩ := hS.exists_half
    have hO : ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) = {(h : K[X])} := by
      rw [hself, Set.pair_eq_singleton]
    rw [hO] at hLO
    by_cases hm : 2 ≤ primaryMultiplicity (spEnd x) (h : K[X])
    · by_cases hsm : f * d = 1 ∧ primaryMultiplicity (spEnd x) (h : K[X]) ≤ 3
      · exfalso
        exact ClNonsplit.not_isQuasisimple_of_le
          (isSolvable_spSupported_selfDual hE hHf hHfl φ hsm.1 hm hsm.2) hLO hLq
      · have h4 : primaryMultiplicity (spEnd x) (h : K[X]) ≤ 3 → 4 ≤ 2 ^ (f * d) := by
          intro h3
          have hfd : 2 ≤ f * d := by
            have := hE.one_le
            by_contra hc
            exact hsm ⟨by omega, h3⟩
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (f * d) := Nat.pow_le_pow_right (by norm_num) hfd
        exact isQuasisimple_spPull_selfDual hself hE hHf hHfl φ hφ hm
          ⟨fun h2 => h4 (by omega), fun h3 => le_trans (by norm_num) (h4 (by omega))⟩
    ·
      exfalso
      refine false_of_le_of_commute hL.2.2 hLO fun g hg g' hg' => ?_
      have h1 : φ ⟨g, hg⟩ * φ ⟨g', hg'⟩ = φ ⟨g', hg'⟩ * φ ⟨g, hg⟩ := by
        apply Subtype.ext
        apply Units.ext
        exact (End_commute_of_finrank_le_one (Nat.lt_succ_iff.mp (not_le.mp hm)) _ _).eq
      have h2 : (⟨g, hg⟩ : spSupported x {(h : K[X])}) * ⟨g', hg'⟩ = ⟨g', hg'⟩ * ⟨g, hg⟩ := by
        apply φ.injective
        rw [map_mul, map_mul, h1]
      exact congrArg Subtype.val h2
  ·
    have hne : (h : K[X]) ≠ reciprocalPolynomial (h : K[X]) := fun e => hself e.symm
    have hP := blocks.paired h hne
    obtain ⟨φ, hφ, -⟩ := hP.factor
    have hdeg : 1 ≤ (h : K[X]).natDegree :=
      Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
    have hN : 2 ^ f ≤ (2 ^ f) ^ (h : K[X]).natDegree := Nat.le_self_pow (by omega) _
    have hle := Nat.le_of_dvd (by omega) hP.dvd
    have hcard4 : 4 ≤ Nat.card (AdjoinRoot (h : K[X])) := by
      rw [hP.card_field]
      omega
    have : Finite (AdjoinRoot (h : K[X])) := Nat.finite_of_card_ne_zero (by omega)
    have facts := spBlockFacts_of_paired ((spOrbitEquiv x rfl).trans φ) (fun g v hv => by
      rw [MulEquiv.trans_apply, hφ, spEnd_orbitEquiv]) (exists_finset_card_four_of_card hcard4)
    by_cases hm : 2 ≤ primaryMultiplicity (spEnd x) (h : K[X])
    · exact spPull_isQuasisimple facts hm
    · exfalso
      refine false_of_le_of_commute hL.2.2 hLO fun g hg g' hg' => ?_
      have := facts.abelian (Nat.lt_succ_iff.mp (not_le.mp hm)) _ (spLin_mem_orbitFactor hg) _
        (spLin_mem_orbitFactor hg')
      exact spLin_injective (by rw [map_mul, map_mul]; exact this.eq)

theorem exists_spSupported_of_isComponentOf [Finite K] [CharP K 2] {f p : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2) {x : StatedSp r K}
    (hxp : x ^ p = 1) (blocks : SpPrimaryBlocks 2 f p x (proj r K x))
    {L : Subgroup (StatedSp r K)}
    (hL : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer {x})) :
    (∀ m ∈ Subgroup.centralizer ({x} : Set (StatedSp r K)), ∀ g ∈ L, m * g * m⁻¹ ∈ L) ∧
      ∃ O : Set K[X], L ≤ spSupported x O ∧
        ∀ u ∈ spSupported x O, ∀ v ∈ spSupported x O, u ^ p = 1 → v ^ p = 1 →
          ∃ a b : ℕ, a < p ∧ b < p ∧ (a ≠ 0 ∨ b ≠ 0) ∧ u ^ a * v ^ b ∈ L := by
  obtain ⟨h, hh, hLO⟩ := exists_le_spSupported blocks hL
  by_cases hX1 : h = X - 1
  · subst hX1
    have hO : ({X - 1, reciprocalPolynomial (X - 1)} : Set K[X]) = {X - 1} := by
      rw [KCSpIsotypic.reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton]
    rw [hO] at hLO
    obtain ⟨hn, hin⟩ := fixed_case hK hf hp hp2 hxp blocks hh hL hLO
    refine ⟨hn, {X - 1}, hLO, fun u hu v _ hup _ =>
      ⟨1, 0, hp.one_lt, hp.pos, Or.inl one_ne_zero, ?_⟩⟩
    rw [pow_one, pow_zero, mul_one]
    exact hin u hu hup
  · have hq := isQuasisimple_spPull_of_le (h := ⟨h, hh⟩) hp hp2 hf blocks hX1 hL hLO
    have hLeq := eq_spPull_of_le hL hLO hq
    have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    refine ⟨fun m hm g hg => ?_, {h, reciprocalPolynomial h}, hLO, fun u hu v hv hup hvp => ?_⟩
    · rw [hLeq] at hg ⊢
      exact spPull_normalized x h m hm g hg
    · rw [hLeq]
      exact exists_pow_mul_pow_mem_spPull hp hu hv hup hvp

end SevSpNs

end CFSG.StandardType
