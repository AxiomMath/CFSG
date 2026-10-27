module

public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneBlocks
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped commutatorElement

section Normalizes

variable {S : Type*} [Group S]

def Normalizes (M P : Subgroup S) : Prop := ∀ m ∈ M, ∀ g ∈ P, m * g * m⁻¹ ∈ P

theorem Normalizes.bot {M : Subgroup S} : Normalizes M (⊥ : Subgroup S) := by
  intro m _ g hg
  rw [Subgroup.mem_bot] at hg ⊢
  rw [hg]
  simp

theorem Normalizes.iSup {ι : Sort*} {M : Subgroup S} {P : ι → Subgroup S}
    (h : ∀ i, Normalizes M (P i)) : Normalizes M (⨆ i, P i) := by
  intro m hm g hg
  refine Subgroup.iSup_induction P (C := fun g => m * g * m⁻¹ ∈ ⨆ i, P i) hg ?_ ?_ ?_
  · intro i g hg
    exact Subgroup.mem_iSup_of_mem i (h i m hm g hg)
  · simp
  · intro a b ha hb
    have : m * (a * b) * m⁻¹ = (m * a * m⁻¹) * (m * b * m⁻¹) := by group
    rw [this]
    exact mul_mem ha hb

theorem Normalizes.sup {M P Q : Subgroup S} (hP : Normalizes M P) (hQ : Normalizes M Q) :
    Normalizes M (P ⊔ Q) := by
  have := Normalizes.iSup (M := M) (P := fun b : Bool => if b then P else Q)
    (fun b => by cases b <;> simp [hP, hQ])
  rwa [iSup_bool_eq] at this

theorem Normalizes.commutator {M F : Subgroup S} (h : Normalizes M F) : Normalizes M ⁅F, F⁆ := by
  intro m hm g hg
  have hle : F.map (MulAut.conj m).toMonoidHom ≤ F := by
    rintro _ ⟨y, hy, rfl⟩
    exact h m hm y hy
  have : (MulAut.conj m) g ∈ (⁅F, F⁆).map (MulAut.conj m).toMonoidHom := ⟨g, hg, rfl⟩
  rw [Subgroup.map_commutator] at this
  exact Subgroup.commutator_mono hle hle this

end Normalizes

section Layer

variable {r : ℕ} {K : Type} [Field K]

@[expose] noncomputable def spPullAll (x : StatedSp r K) : Subgroup (StatedSp r K) :=
  ⨆ h : primaryFactors (spEnd x), ⨆ (_ : (h : K[X]) ≠ X - 1 ∧
    2 ≤ primaryMultiplicity (spEnd x) (h : K[X])), spPull x (h : K[X])

open scoped _root_.Classical in
@[expose] noncomputable def spFixedLayerS (x : StatedSp r K) : Subgroup (StatedSp r K) :=
  if SpFixedListed x then
    (if spFixedDim x = 4 ∧ Nat.card K = 2 then ⁅spFixedFactor x, spFixedFactor x⁆
      else spFixedFactor x)
  else ⊥

theorem spFixedLayerImage_eq (x : StatedSp r K) :
    spFixedLayerImage x = (spFixedLayerS x).map (proj r K) := by
  unfold spFixedLayerImage spFixedLayerS
  split_ifs <;> simp

theorem spListedProduct_eq (x : StatedSp r K) :
    spListedProduct x = (spPullAll x ⊔ spFixedLayerS x).map (proj r K) := by
  rw [Subgroup.map_sup, ← spFixedLayerImage_eq]
  unfold spListedProduct spPullAll
  rw [Subgroup.map_iSup]
  congr 2
  funext h
  rw [Subgroup.map_iSup]
  rfl

theorem spPullAll_le (x : StatedSp r K) :
    spPullAll x ≤ Subgroup.centralizer ({x} : Set (StatedSp r K)) :=
  iSup_le fun _ => iSup_le fun _ => spPull_le_centralizer x _

theorem spPullAll_normalizes (x : StatedSp r K) :
    Normalizes (Subgroup.centralizer ({x} : Set (StatedSp r K))) (spPullAll x) :=
  Normalizes.iSup fun _ => Normalizes.iSup fun _ => spPull_normalized x _

theorem commutator_le_self {S : Type*} [Group S] (F : Subgroup S) : ⁅F, F⁆ ≤ F :=
  Subgroup.commutator_le.mpr fun _ hg _ hh =>
    F.mul_mem (F.mul_mem (F.mul_mem hg hh) (F.inv_mem hg)) (F.inv_mem hh)

theorem spFixedLayerS_le (x : StatedSp r K) :
    spFixedLayerS x ≤ Subgroup.centralizer ({x} : Set (StatedSp r K)) := by
  unfold spFixedLayerS
  split_ifs
  · exact (commutator_le_self _).trans (spFixedFactor_le_centralizer x)
  · exact spFixedFactor_le_centralizer x
  · exact bot_le

theorem spFixedLayerS_normalizes (x : StatedSp r K) :
    Normalizes (Subgroup.centralizer ({x} : Set (StatedSp r K))) (spFixedLayerS x) := by
  unfold spFixedLayerS
  split_ifs
  · exact Normalizes.commutator (spFixedFactor_normalized x)
  · exact spFixedFactor_normalized x
  · exact Normalizes.bot

end Layer

section Kernel

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem sq_eq_one_of_proj_eq_one (hr : 1 ≤ r) {u : StatedSp r K} (hu : proj r K u = 1) :
    u ^ 2 = 1 := by
  have hmem : u ∈ SymplecticHigher.spScalars r K := by
    rw [← SymplecticHigher.ker_proj]
    exact hu
  have hcard : Nat.card (SymplecticHigher.spScalars r K) ∣ 2 := by
    rw [card_spScalars_eq_gcd K hr]
    exact Nat.gcd_dvd_left _ _
  have h1 := (orderOf_dvd_natCard (⟨u, hmem⟩ : SymplecticHigher.spScalars r K)).trans hcard
  have h2 := orderOf_dvd_iff_pow_eq_one.mp h1
  exact congrArg Subtype.val h2

end Kernel

section Rank

variable {r : ℕ} {K : Type} [Field K]

theorem primaryMultiplicity_le {ℓ f p : ℕ} {x : StatedSp r K} (hp : p.Prime) (hp2 : p ≠ 2)
    (blocks : SpPrimaryBlocks ℓ f p x (proj r K x)) (h : primaryFactors (spEnd x))
    (hh : (h : K[X]) ≠ X - 1) : primaryMultiplicity (spEnd x) (h : K[X]) ≤ r := by
  classical
  obtain ⟨s, -, ⟨P, hP⟩, hrk⟩ := blocks.rank
  have hr := hrk P hP
  have hdeg : 1 ≤ (h : K[X]).natDegree :=
    (irreducible_of_mem_primaryFactors h.2).natDegree_pos
  by_cases hself : reciprocalPolynomial (h : K[X]) = h
  · obtain ⟨d, hd, hpd, -⟩ := (blocks.selfDual h hh hself).exists_half
    have hd1 : 1 ≤ d := by
      by_contra hd0
      have hd0' : d = 0 := by omega
      subst hd0'
      have : p ∣ 2 := by simpa using hpd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
    have hmemf : (h : K[X]) ∈ (primaryFactors (spEnd x)).filter
        (fun h => reciprocalPolynomial h = h ∧ h ≠ X - 1) :=
      Finset.mem_filter.mpr ⟨h.2, hself, hh⟩
    have h1 : (h : K[X]).natDegree / 2 * primaryMultiplicity (spEnd x) (h : K[X]) ≤
        ∑ h ∈ (primaryFactors (spEnd x)).filter
          (fun h => reciprocalPolynomial h = h ∧ h ≠ X - 1),
            h.natDegree / 2 * primaryMultiplicity (spEnd x) h :=
      Finset.single_le_sum (f := fun h => h.natDegree / 2 * primaryMultiplicity (spEnd x) h)
        (fun _ _ => Nat.zero_le _) hmemf
    have h2 : 1 ≤ (h : K[X]).natDegree / 2 := by omega
    have h3 : primaryMultiplicity (spEnd x) (h : K[X]) ≤
        (h : K[X]).natDegree / 2 * primaryMultiplicity (spEnd x) (h : K[X]) :=
      Nat.le_mul_of_pos_left _ h2
    omega
  · have hP' := blocks.paired h (Ne.symm hself)
    rcases hP.2.1 (h : K[X]) h.2 (Ne.symm hself) with hmP | hmP
    · have h1 : (h : K[X]).natDegree * primaryMultiplicity (spEnd x) (h : K[X]) ≤
          ∑ h ∈ P, h.natDegree * primaryMultiplicity (spEnd x) h :=
        Finset.single_le_sum (f := fun h => h.natDegree * primaryMultiplicity (spEnd x) h)
          (fun _ _ => Nat.zero_le _) hmP
      have h3 : primaryMultiplicity (spEnd x) (h : K[X]) ≤
          (h : K[X]).natDegree * primaryMultiplicity (spEnd x) (h : K[X]) :=
        Nat.le_mul_of_pos_left _ hdeg
      omega
    · have h1 : (reciprocalPolynomial (h : K[X])).natDegree *
          primaryMultiplicity (spEnd x) (reciprocalPolynomial (h : K[X])) ≤
            ∑ h ∈ P, h.natDegree * primaryMultiplicity (spEnd x) h :=
        Finset.single_le_sum (f := fun h => h.natDegree * primaryMultiplicity (spEnd x) h)
          (fun _ _ => Nat.zero_le _) hmP
      rw [← hP'.natDegree_eq, ← hP'.multiplicity_eq] at h1
      have h3 : primaryMultiplicity (spEnd x) (h : K[X]) ≤
          (h : K[X]).natDegree * primaryMultiplicity (spEnd x) (h : K[X]) :=
        Nat.le_mul_of_pos_left _ hdeg
      omega

end Rank


section Facts

variable {r : ℕ} {K : Type} [Field K]

@[expose] def SpListedFacts (p : ℕ) (B : Subgroup (MulAut (StatedProj (StatedSp r K))))
    (a : StatedProj (StatedSp r K)) (J : Subgroup (StatedProj (StatedSp r K))) : Prop :=
  J ≤ Subgroup.centralizer ({a} : Set (StatedProj (StatedSp r K))) ∧ CFSG.IsQuasisimple ↥J ∧
    (J.subgroupOf (Subgroup.centralizer ({a} : Set (StatedProj (StatedSp r K))))).Normal ∧
    CFSG.IsComponent ((J.map (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K)))).subgroupOf
        (B ⊓ Subgroup.centralizer ({MulAut.conj a} :
          Set (MulAut (StatedProj (StatedSp r K)))))) ∧
    ∀ s ∈ spLocalCore p B a, ∀ j ∈ J, s * MulAut.conj j = MulAut.conj j * s

theorem mem_spPullAll {x : StatedSp r K} {h : primaryFactors (spEnd x)}
    (hh : (h : K[X]) ≠ X - 1) (facts : SpBlockFacts (spForm r K) (spLin r K x) h)
    {k : StatedSp r K} (hk : k ∈ spPull x (h : K[X])) : k ∈ spPullAll x := by
  by_cases hm : 2 ≤ primaryMultiplicity (spEnd x) (h : K[X])
  · exact Subgroup.mem_iSup_of_mem h (Subgroup.mem_iSup_of_mem ⟨hh, hm⟩ hk)
  · have hbot := facts.special_bot (show primaryMultiplicity (spEnd x) (h : K[X]) ≤ 1 by omega)
    have h1 : spLin r K k ∈ specialBlock (spForm r K) (spLin r K x) (h : K[X]) := hk
    rw [hbot, Subgroup.mem_bot] at h1
    have : k = 1 := spLin_injective (h1.trans (map_one _).symm)
    rw [this]
    exact one_mem _

theorem spBlockFacts_nontrivial {ℓ f p : ℕ} {x : StatedSp r K} (hp5 : 5 ≤ p) (hq2 : 2 ≤ ℓ ^ f)
    (blocks : SpPrimaryBlocks ℓ f p x (proj r K x)) (h : primaryFactors (spEnd x))
    (hh : (h : K[X]) ≠ X - 1) : SpBlockFacts (spForm r K) (spLin r K x) h := by
  by_cases hself : reciprocalPolynomial (h : K[X]) = h
  · exact spBlockFacts_of_spSelfDual hp5 hq2 hself (blocks.selfDual h hh hself)
  · exact spBlockFacts_of_spPaired hp5 hq2 (blocks.paired h (Ne.symm hself))

theorem exists_local_nonfixed {ℓ f p : ℕ} {x : StatedSp r K} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hq2 : 2 ≤ ℓ ^ f) (blocks : SpPrimaryBlocks ℓ f p x (proj r K x))
    (hpm : ∀ h : primaryFactors (spEnd x), (h : K[X]) ≠ X - 1 →
      ¬ p ∣ primaryMultiplicity (spEnd x) (h : K[X]))
    (h : primaryFactors (spEnd x)) (hh : (h : K[X]) ≠ X - 1) {t : StatedSp r K}
    (ht : t ∈ spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}) (htp : t ^ p = 1) :
    ∃ s k : StatedSp r K, s ∈ spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])} ∧
      k ∈ spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])} ∧ k ∈ spPullAll x ∧
      t = s * k ∧
      (∀ g ∈ spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}, s * g = g * s) ∧
      s ^ p = 1 ∧ k ^ p = 1 := by
  have key : ∃ s k : StatedSp r K,
      s ∈ spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])} ∧
      k ∈ spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])} ∧
      k ∈ spPull x (h : K[X]) ∧ t = s * k ∧
      (∀ g ∈ spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}, s * g = g * s) ∧
      s ^ p = 1 ∧ k ^ p = 1 := by
    by_cases hself : reciprocalPolynomial (h : K[X]) = h
    · exact KCSymplectic.exists_local_selfDual (blocks.selfDual h hh hself) hself hp (hpm h hh)
        ht htp
    · exact KCSymplectic.exists_local_paired (blocks.paired h (Ne.symm hself)) hp (hpm h hh)
        ht htp
  obtain ⟨s, k, hs, hk, hkP, hts, hsc, hsp, hkp⟩ := key
  exact ⟨s, k, hs, hk, mem_spPullAll hh (spBlockFacts_nontrivial hp5 hq2 blocks h hh) hkP, hts,
    hsc, hsp, hkp⟩

end Facts

section Factorization

variable {r : ℕ} {K : Type} [Field K]

theorem spFactorization {ℓ f p : ℕ} {x : StatedSp r K} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hq2 : 2 ≤ ℓ ^ f) (blocks : SpPrimaryBlocks ℓ f p x (proj r K x))
    (hpm : ∀ h : primaryFactors (spEnd x), (h : K[X]) ≠ X - 1 →
      ¬ p ∣ primaryMultiplicity (spEnd x) (h : K[X]))
    {v : StatedSp r K} (hv : v ∈ Subgroup.centralizer ({x} : Set (StatedSp r K)))
    (hvp : v ^ p = 1) :
    ∃ z k w : StatedSp r K, v = z * k * w ∧
      z ∈ Subgroup.centralizer ({x} : Set (StatedSp r K)) ∧
      (∀ g ∈ Subgroup.centralizer ({x} : Set (StatedSp r K)), z * g = g * z) ∧ z ^ p = 1 ∧
      k ∈ spPullAll x ∧ w ∈ spFixedFactor x ∧ w ^ p = 1 := by
  classical
  obtain ⟨hcomm, hindep, hgen⟩ := blocks.directProduct
  have hfin : Finite ↥(reciprocalOrbits (spEnd x)) := by
    have : (reciprocalOrbits (spEnd x)).Finite := (Finset.finite_toSet _).image _
    exact this.to_subtype
  let H : ↥(reciprocalOrbits (spEnd x)) → Subgroup (StatedSp r K) :=
    fun O => spSupported x (O : Set K[X])
  have hv' : v ∈ ⨆ O, H O := by
    rw [hgen]
    exact hv
  have hcomm' : Pairwise fun i j => ∀ a b : StatedSp r K, a ∈ H i → b ∈ H j → Commute a b :=
    fun i j hij a b ha hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb
  have hloc : ∀ O : ↥(reciprocalOrbits (spEnd x)), ∀ t ∈ H O, t ^ p = 1 →
      ∃ s k w : StatedSp r K, s ∈ H O ∧ k ∈ H O ∧ w ∈ H O ∧ k ∈ spPullAll x ∧
        w ∈ spFixedFactor x ∧ t = s * k * w ∧ (∀ g ∈ H O, s * g = g * s) ∧ s ^ p = 1 ∧
        k ^ p = 1 ∧ w ^ p = 1 := by
    intro O t ht htp
    obtain ⟨a, ha, hO0⟩ := O.2
    have hO : ({a, reciprocalPolynomial a} : Set K[X]) = (O : Set K[X]) := hO0
    by_cases hX : a = X - 1
    · have hOset : (O : Set K[X]) = {X - 1} := by
        rw [← hO, hX, KCSpIsotypic.reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton]
      have htF : t ∈ spFixedFactor x := by
        unfold spFixedFactor
        rw [← hOset]
        exact ht
      exact ⟨1, 1, t, one_mem _, one_mem _, ht, one_mem _, htF, by simp, fun g _ => by simp,
        one_pow _, one_pow _, htp⟩
    · have ha' : (⟨a, ha⟩ : primaryFactors (spEnd x)) = ⟨a, ha⟩ := rfl
      have ht' : t ∈ spSupported x {((⟨a, ha⟩ : primaryFactors (spEnd x)) : K[X]),
          reciprocalPolynomial ((⟨a, ha⟩ : primaryFactors (spEnd x)) : K[X])} := by
        show t ∈ spSupported x {a, reciprocalPolynomial a}
        rw [hO]
        exact ht
      obtain ⟨s, k, hs, hk, hkK, hts, hsc, hsp, hkp⟩ := exists_local_nonfixed hp hp5 hq2 blocks hpm
        ⟨a, ha⟩ hX ht' htp
      have hs' : ∀ y, y ∈ spSupported x {a, reciprocalPolynomial a} → y ∈ H O := fun y hy => by
        change y ∈ spSupported x (O : Set K[X])
        rw [← hO]
        exact hy
      refine ⟨s, k, 1, hs' s hs, hs' k hk, one_mem _, hkK, one_mem _, by simpa using hts,
        fun g hg => hsc g ?_, hsp, hkp, one_pow _⟩
      change g ∈ spSupported x {a, reciprocalPolynomial a}
      rw [hO]
      exact hg
  obtain ⟨z, k, w, hvzkw, hzmem, hzc, hzp, hkK, hkmem, hkp, hwW, hwmem, hwp⟩ :=
    KCSymplectic.exists_factorization_of_family H hcomm' hindep (p := p) (spPullAll x)
      (spFixedFactor x) hloc hv' hvp
  exact ⟨z, k, w, hvzkw, hgen ▸ hzmem, fun g hg => hzc g (hgen ▸ hg), hzp, hkK, hwW, hwp⟩

end Factorization


section Equation

variable {r : ℕ} {K : Type} [Field K]

theorem spFixedLayerImage_eq_spBlockImage {ℓ f p : ℕ} (hK : Nat.card K = ℓ ^ f) (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) {x : StatedSp r K} (hsq : Squarefree (minpoly K (spEnd x)))
    (blocks : SpPrimaryBlocks ℓ f p x (proj r K x)) (hl : SpFixedListed x)
    (h42 : ¬ (spFixedDim x = 4 ∧ Nat.card K = 2)) :
    spFixedLayerImage x = spBlockImage x (X - 1) := by
  have hq2 : 2 ≤ Nat.card K := by
    rw [hK]
    exact hℓ.two_le.trans (Nat.le_self_pow (by omega) ℓ)
  have hmem := X_sub_one_mem_primaryFactors x (by have := hl.1; omega)
  have facts := spBlockFacts_of_spFixed hsq blocks hmem (spFixed_hq blocks hl h42 hq2)
  have hm : 2 ≤ primaryMultiplicity (spEnd x) (X - 1) := by
    rw [show (X - 1 : K[X]) = X - C 1 by rw [C_1], primaryMultiplicity_X_sub_C_eq]
    exact hl.1
  have hcomm := facts.commutator_eq hm
  have hqF := spFixedFactor_isQuasisimple hK hℓ hf blocks hl h42
  have hFperf : ⁅spFixedFactor x, spFixedFactor x⁆ = spFixedFactor x :=
    commutator_eq_of_isPerfect hqF.1
  have horb : orbitFactor (spForm r K) (spLin r K x) (X - 1) =
      (spFixedFactor x).map (spLin r K) := by
    rw [orbitFactor_spForm, KCSpIsotypic.reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton]
    exact (map_spSupported x {X - 1}).symm
  have hspec : specialBlock (spForm r K) (spLin r K x) (X - 1) =
      (spFixedFactor x).map (spLin r K) := by
    rw [← hcomm, horb, ← Subgroup.map_commutator, hFperf]
  have hcomap : (specialBlock (spForm r K) (spLin r K x) (X - 1)).comap (spLin r K) =
      spFixedFactor x := by
    rw [hspec, Subgroup.comap_map_eq_self_of_injective spLin_injective]
  unfold spFixedLayerImage spBlockImage
  simp only [hl, h42, ↓reduceIte, hcomap]

end Equation

theorem symplectic_inner_plane_below_prime_local_core_centralization
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = ℓ ^ f)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) {r : ℕ} (hr : 2 ≤ r)
    (hrq : ¬ (r = 2 ∧ ℓ ^ f = 2)) (B : Subgroup (MulAut (StatedProj (StatedSp r K))))
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))).range ≤ B)
    (A : Subgroup (StatedProj (StatedSp r K))) (hA : IsElemAbelian p A)
    (_hAcard : Nat.card A = p ^ 2) (a : StatedProj (StatedSp r K)) (haA : a ∈ A) (ha1 : a ≠ 1)
    (x : StatedSp r K) (hxa : proj r K x = a) (hxp : orderOf x = p) :
    (∀ h : primaryFactors (spEnd x), (h : K[X]) ≠ X - 1 →
      2 ≤ primaryMultiplicity (spEnd x) (h : K[X]) →
        SpListedFacts p B a (spBlockImage x (h : K[X]))) ∧
    (SpFixedListed x → SpListedFacts p B a (spFixedLayerImage x)) ∧
    (SpFixedListed x →
      (¬ (spFixedDim x = 4 ∧ Nat.card K = 2) → spFixedLayerImage x = spBlockImage x (X - 1)) ∧
      (spFixedDim x = 4 ∧ Nat.card K = 2 →
        spFixedLayerImage x = (⁅spFixedFactor x, spFixedFactor x⁆).map (proj r K))) ∧
    (¬ SpFixedListed x → spFixedLayerImage x = ⊥) ∧
    ((spFixedDim x = 2 → Nat.card K = 2 → Nat.card ↥(spFixedFactor x) = 6) ∧
      (spFixedDim x = 2 → Nat.card K = 3 → Nat.card ↥(spFixedFactor x) = 24) ∧
      (spFixedDim x = 4 → Nat.card K = 2 →
        Nonempty (↥⁅spFixedFactor x, spFixedFactor x⁆ ≃* alternatingGroup (Fin 6)) ∧
          ⁅spFixedFactor x, spFixedFactor x⁆.relIndex (spFixedFactor x) = 2)) ∧
    (((spListedProduct x).subgroupOf
        (Subgroup.centralizer ({a} : Set (StatedProj (StatedSp r K))))).Normal ∧
      ⁅spLocalCore p B a, (spListedProduct x).map (MulAut.conj : StatedProj (StatedSp r K) →*
        MulAut (StatedProj (StatedSp r K)))⁆ = ⊥) ∧
    ((∀ h : primaryFactors (spEnd x), (h : K[X]) ≠ X - 1 →
        ¬ p ∣ primaryMultiplicity (spEnd x) (h : K[X])) →
      (∀ y ∈ Subgroup.centralizer ({a} : Set (StatedProj (StatedSp r K))), orderOf y = p →
        ∃ z k : StatedProj (StatedSp r K), y = z * k ∧
          z ∈ Subgroup.centralizer ({a} : Set (StatedProj (StatedSp r K))) ∧
          (∀ n ∈ Subgroup.centralizer ({a} : Set (StatedProj (StatedSp r K))), z * n = n * z) ∧
          z ^ p = 1 ∧ k ∈ spListedProduct x) ∧
      (∀ y ∈ Subgroup.centralizer ({a} : Set (StatedProj (StatedSp r K))), orderOf y = p →
        ∀ s ∈ spLocalCore p B a, s * MulAut.conj y = MulAut.conj y * s) ∧
      ∀ g ∈ A, ∀ s ∈ spLocalCore p B a, s * MulAut.conj g = MulAut.conj g * s) ∧
    (r < p → ∀ g ∈ A, ∀ s ∈ spLocalCore p B a, s * MulAut.conj g = MulAut.conj g * s) := by
  classical
  subst hxa
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero f hℓ.ne_zero
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact hq0)
  have hp2 : p ≠ 2 := by omega
  have hp5 : 5 ≤ p := by
    rcases Nat.lt_or_ge p 5 with h4 | h4
    · have : p = 4 := by omega
      subst this
      exact absurd hp (by norm_num)
    · exact h4
  have hq2 : 2 ≤ ℓ ^ f := hℓ.two_le.trans (Nat.le_self_pow (by omega) ℓ)
  have : Finite (StatedProj (StatedSp r K)) :=
    CFSG.ClassicalGroups.Symplectic.finite_statedProj_statedSp r K
  obtain ⟨-, -, hinj⟩ := spProj_facts hℓ hf hK hr hrq
  have ha : orderOf (proj r K x) = p := orderOf_eq_prime (hA.2 _ haA) ha1
  obtain ⟨-, hblocks⟩ := symplectic_cross_prime_primary_centralizer_blocks hℓ hf hK hp hp2 hpℓ
    (by omega) (proj r K x) ha
  have blocks := hblocks x rfl hxp
  have hcent := blocks.centralizer_eq
  have hcharK : CharP K ℓ := by
    have := Fintype.ofFinite K
    have : Fact ℓ.Prime := ⟨hℓ⟩
    exact charP_of_card_eq_prime_pow (f := f) (by rw [Fintype.card_eq_nat_card, hK])
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K ℓ] at h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h).symm
  have hxpow : x ^ p = 1 := by
    rw [← hxp]
    exact pow_orderOf_eq_one x
  have hsq : Squarefree (minpoly K (spEnd x)) := (altPrimaryData_spLin hpK hxpow).squarefree
  have hblock : ∀ h : primaryFactors (spEnd x), (h : K[X]) ≠ X - 1 →
      2 ≤ primaryMultiplicity (spEnd x) (h : K[X]) →
        SpListedFacts p B (proj r K x) (spBlockImage x (h : K[X])) := fun h hh hm =>
    spListed_facts hp hB hinj hcent (spPull_le_centralizer x _) (spPull_normalized x _)
      (spPull_isQuasisimple (spBlockFacts_nontrivial hp5 hq2 blocks h hh) hm)
  have hfixed : SpFixedListed x → SpListedFacts p B (proj r K x) (spFixedLayerImage x) := by
    intro hl
    by_cases h42 : spFixedDim x = 4 ∧ Nat.card K = 2
    · obtain ⟨hq, -⟩ := spFixed_four_two h42.2 blocks h42.1
      have himg : spFixedLayerImage x = (⁅spFixedFactor x, spFixedFactor x⁆).map (proj r K) := by
        unfold spFixedLayerImage
        simp only [hl, h42.1, h42.2, and_self, ↓reduceIte]
      rw [himg]
      exact spListed_facts hp hB hinj hcent
        ((commutator_le_self _).trans (spFixedFactor_le_centralizer x))
        (Normalizes.commutator (spFixedFactor_normalized x)) hq
    · have himg : spFixedLayerImage x = (spFixedFactor x).map (proj r K) := by
        unfold spFixedLayerImage
        simp only [hl, h42, ↓reduceIte]
      rw [himg]
      exact spListed_facts hp hB hinj hcent (spFixedFactor_le_centralizer x)
        (spFixedFactor_normalized x) (spFixedFactor_isQuasisimple hK hℓ hf blocks hl h42)
  have hfixed_bot : ¬ SpFixedListed x → spFixedLayerImage x = ⊥ := by
    intro hl
    unfold spFixedLayerImage
    simp only [hl, ↓reduceIte]
  have hZ : ∀ s ∈ spLocalCore p B (proj r K x), ∀ j ∈ spListedProduct x,
      s * MulAut.conj j = MulAut.conj j * s := by
    intro s hs j hj
    let Zc : Subgroup (StatedProj (StatedSp r K)) :=
      (Subgroup.centralizer (spLocalCore p B (proj r K x) :
        Set (MulAut (StatedProj (StatedSp r K))))).comap
          (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K)))
    have hle : spListedProduct x ≤ Zc := by
      unfold spListedProduct
      refine sup_le (iSup_le fun h => iSup_le fun hh => ?_) ?_
      · intro j hj
        exact Subgroup.mem_centralizer_iff.mpr fun s hs => ((hblock h hh.1 hh.2).2.2.2.2 s hs j hj)
      · by_cases hl : SpFixedListed x
        · intro j hj
          exact Subgroup.mem_centralizer_iff.mpr fun s hs => ((hfixed hl).2.2.2.2 s hs j hj)
        · rw [hfixed_bot hl]
          exact bot_le
    exact Subgroup.mem_centralizer_iff.mp (hle hj) s hs
  have hdecomp : (∀ h : primaryFactors (spEnd x), (h : K[X]) ≠ X - 1 →
        ¬ p ∣ primaryMultiplicity (spEnd x) (h : K[X])) →
      ∀ y ∈ Subgroup.centralizer ({proj r K x} : Set (StatedProj (StatedSp r K))),
        orderOf y = p → ∃ z k : StatedProj (StatedSp r K), y = z * k ∧
          z ∈ Subgroup.centralizer ({proj r K x} : Set (StatedProj (StatedSp r K))) ∧
          (∀ n ∈ Subgroup.centralizer ({proj r K x} : Set (StatedProj (StatedSp r K))),
            z * n = n * z) ∧ z ^ p = 1 ∧ k ∈ spListedProduct x := by
    intro hpm y hy hyp
    rw [hcent] at hy
    obtain ⟨v₀, hv₀, hv₀y⟩ := hy
    have hyp' : y ^ p = 1 := by
      rw [← hyp]
      exact pow_orderOf_eq_one y
    have hv₀p : proj r K (v₀ ^ p) = 1 := by rw [map_pow, hv₀y, hyp']
    have hsq2 := sq_eq_one_of_proj_eq_one (by omega) hv₀p
    obtain ⟨c, hc⟩ : Even (p + 1) := (hp.odd_of_ne_two hp2).add_one
    have hvp : (v₀ ^ (p + 1)) ^ p = 1 := by
      have hexp : (p + 1) * p = p * 2 * c := by
        have : p + 1 = 2 * c := by omega
        rw [this]
        ring
      calc (v₀ ^ (p + 1)) ^ p = v₀ ^ ((p + 1) * p) := by rw [pow_mul]
        _ = v₀ ^ (p * 2 * c) := by rw [hexp]
        _ = ((v₀ ^ p) ^ 2) ^ c := by rw [pow_mul, pow_mul]
        _ = 1 := by rw [hsq2, one_pow]
    have hvy : proj r K (v₀ ^ (p + 1)) = y := by
      rw [map_pow, hv₀y, pow_succ, hyp', one_mul]
    obtain ⟨z, k, w, hvzkw, hzC, hzc, hzp, hkK, hwF, hwp⟩ := spFactorization hp hp5 hq2 blocks hpm
      (pow_mem hv₀ _) hvp
    have hwL : w ∈ spFixedLayerS x := by
      unfold spFixedLayerS
      by_cases hl : SpFixedListed x
      · by_cases h42 : spFixedDim x = 4 ∧ Nat.card K = 2
        · simp only [hl, h42, ↓reduceIte]
          exact (spFixed_four_two h42.2 blocks h42.1).2 hp hp2 w hwF hwp
        · simp only [hl, h42, ↓reduceIte]
          exact hwF
      · simp only [hl, ↓reduceIte]
        rw [eq_one_of_not_listed hp hp5 blocks hl hwF hwp]
        exact one_mem _
    refine ⟨proj r K z, proj r K (k * w), ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hvy, hvzkw, mul_assoc, map_mul]
    · rw [hcent]
      exact Subgroup.mem_map_of_mem _ hzC
    · intro n hn
      rw [hcent] at hn
      obtain ⟨m, hm, rfl⟩ := hn
      rw [← map_mul, ← map_mul, hzc m hm]
    · rw [← map_pow, hzp, map_one]
    · rw [spListedProduct_eq]
      exact Subgroup.mem_map_of_mem _
        (mul_mem (Subgroup.mem_sup_left hkK) (Subgroup.mem_sup_right hwL))
  have hcommute : (∀ h : primaryFactors (spEnd x), (h : K[X]) ≠ X - 1 →
        ¬ p ∣ primaryMultiplicity (spEnd x) (h : K[X])) →
      ∀ y ∈ Subgroup.centralizer ({proj r K x} : Set (StatedProj (StatedSp r K))), orderOf y = p →
        ∀ s ∈ spLocalCore p B (proj r K x), s * MulAut.conj y = MulAut.conj y * s := by
    intro hpm y hy hyp s hs
    obtain ⟨z, k, hyzk, hzN, hzc, hzp, hkD⟩ := hdecomp hpm y hy hyp
    have h1 := KCOrthogonal.commute_core_conj_of_central hp hB (proj r K x) hinj hzN hzc hzp s hs
    have h2 := hZ s hs k hkD
    rw [hyzk, map_mul]
    calc s * (MulAut.conj z * MulAut.conj k) = (s * MulAut.conj z) * MulAut.conj k := by
          rw [mul_assoc]
      _ = MulAut.conj z * (s * MulAut.conj k) := by rw [h1, mul_assoc]
      _ = MulAut.conj z * (MulAut.conj k * s) := by rw [h2]
      _ = MulAut.conj z * MulAut.conj k * s := by rw [mul_assoc]
  have hAcomm : ∀ g ∈ A, g ≠ 1 →
      g ∈ Subgroup.centralizer ({proj r K x} : Set (StatedProj (StatedSp r K))) ∧
        orderOf g = p := by
    intro g hg hg1
    refine ⟨?_, orderOf_eq_prime (hA.2 g hg) hg1⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hA.1
    have := mul_comm' (⟨g, hg⟩ : ↥A) ⟨proj r K x, haA⟩
    exact congrArg Subtype.val this
  have hAcent : (∀ h : primaryFactors (spEnd x), (h : K[X]) ≠ X - 1 →
        ¬ p ∣ primaryMultiplicity (spEnd x) (h : K[X])) →
      ∀ g ∈ A, ∀ s ∈ spLocalCore p B (proj r K x), s * MulAut.conj g = MulAut.conj g * s := by
    intro hpm g hg s hs
    by_cases hg1 : g = 1
    · rw [hg1, map_one, mul_one, one_mul]
    · obtain ⟨hgN, hgp⟩ := hAcomm g hg hg1
      exact hcommute hpm g hgN hgp s hs
  refine ⟨fun h hh hm => hblock h hh hm, hfixed, ?_, hfixed_bot, ?_, ?_, ?_, ?_⟩
  · intro hl
    exact ⟨fun h42 => spFixedLayerImage_eq_spBlockImage hK hℓ hf hsq blocks hl h42,
      fun h42 => by
        unfold spFixedLayerImage
        simp only [hl, h42.1, h42.2, and_self, ↓reduceIte]⟩
  · refine ⟨fun hd hq2 => ?_, fun hd hq3 => ?_, fun hd hq2 => spFixed_four_two_alt hq2 blocks hd⟩
    · rw [card_spFixedFactor_of_dim_two blocks hd, hq2]
      norm_num
    · rw [card_spFixedFactor_of_dim_two blocks hd, hq3]
      norm_num
  · refine ⟨?_, ?_⟩
    · rw [spListedProduct_eq, hcent]
      exact normal_subgroupOf_map (proj r K)
        ((spPullAll_normalizes x).sup (spFixedLayerS_normalizes x))
    · refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun s hs => ?_
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨j, hj, rfl⟩
      exact (hZ s hs j hj).symm
  · intro hpm
    exact ⟨hdecomp hpm, hcommute hpm, hAcent hpm⟩
  · intro hrp
    have hpm : ∀ h : primaryFactors (spEnd x), (h : K[X]) ≠ X - 1 →
        ¬ p ∣ primaryMultiplicity (spEnd x) (h : K[X]) := by
      intro h hh hd
      have hne := KCPrimary.primaryComponent_ne_bot hsq h.2
      have : Nontrivial (primaryComponent (spEnd x) (h : K[X])) :=
        Submodule.nontrivial_iff_ne_bot.mpr hne
      have hpos : 0 < primaryMultiplicity (spEnd x) (h : K[X]) := Module.finrank_pos
      have := Nat.le_of_dvd hpos hd
      have := primaryMultiplicity_le hp hp2 blocks h hh
      omega
    exact hAcent hpm

end CFSG.RankThree.PartOne
