module

public import CFSG.LocalAnalysis.StandardType.ExcPos.RootPairStabilizer
public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.LieType.AlgebraicGroups.CocharCurveConnected
public import CFSG.LieType.AlgebraicGroups.RootSpanConnected
public import CFSG.RankThree.PartOne.KE6.E8T3E6
public import CFSG.LieType.Chevalley.SignKernelComponentPerfect
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import Certificates.Certificate1952

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KE6
open CFSG.ClassicalInvolution.ModelFacts.Levi (thetaDiag)
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b (weylAct rootChar_weylAct)
open WithConv
open scoped CFSG.ConvolutionPoints

set_option linter.unusedSectionVars false


theorem isConnectedAlgebraicSubgroup_closure_iUnion {τ : Tag} {k : Type} [Field k]
    [IsAlgClosed k] {I : Type} (C : I → Set (ModGL τ k))
    (hC : ∀ i, SeminaireExp3.IsDomainImage k
      (SeminaireExp3.ZariskiGL.pt '' (modGLZariski τ k '' C i)))
    (h1 : ∀ i, (1 : ModGL τ k) ∈ C i) :
    IsConnectedAlgebraicSubgroup k
      ((Subgroup.closure (⋃ i, C i)).map (modGLPoint τ k).toMonoidHom) := by
  let W : I → Set (SeminaireExp3.ZariskiGL (Label τ) k) := fun i => modGLZariski τ k '' C i
  have h1' : ∀ i, (1 : SeminaireExp3.ZariskiGL (Label τ) k) ∈ W i :=
    fun i => ⟨1, h1 i, map_one _⟩
  obtain ⟨-, -, a, ha⟩ := SeminaireExp3.ZariskiGL.closure_eq_wordSet W hC h1'
  have hS : (modGLZariski τ k).toMonoidHom '' (⋃ i, C i) = ⋃ i, W i := Set.image_iUnion
  have himg : modGLZariski τ k '' (Subgroup.closure (⋃ i, C i) : Set (ModGL τ k)) =
      SeminaireExp3.ZariskiGL.wordSet W a := by
    rw [← ha, ← hS]
    change (modGLZariski τ k).toMonoidHom '' (Subgroup.closure (⋃ i, C i) : Set (ModGL τ k)) =
      ↑(Subgroup.closure ((modGLZariski τ k).toMonoidHom '' (⋃ i, C i)))
    rw [← MonoidHom.map_closure, Subgroup.coe_map]
  have hdom : SeminaireExp3.IsDomainImage k
      (transportPoints (modGLPoint τ k) (Subgroup.closure (⋃ i, C i) : Set (ModGL τ k))) := by
    rw [transportPoints_eq_image_modGLZariski, himg]
    exact SeminaireExp3.ZariskiGL.isDomainImage_wordSet W hC a
  exact (isConnectedAlgebraicSubgroup_map (modGLPoint τ k) (Subgroup.closure (⋃ i, C i))
    hdom.isPointConstructible hdom.isPointIrreducible).2.1

private theorem E7_cartan_eq_iform (i j : Fin Tag.E7.rank) :
    Tag.E7.cartan i j = iform (Pi.single i 1 : Fin Tag.E7.rank → ℤ) (Pi.single j 1) := by
  rw [iform_single_left]
  simp [Pi.single_apply, Tag.symmetrizer]

private theorem E7_root_coeff_six : ∀ β ∈ rootFinset .E7,
    β ⟨6, by decide⟩ = -1 ∨ β ⟨6, by decide⟩ = 0 ∨ β ⟨6, by decide⟩ = 1 := by
  decide +kernel

theorem rootSpan_e6_inf_torusGroup_eq (K : Type) [Field K] (w : WeylGroup .E7) :
    rootSpan .E7 K ((fun alpha => w • alpha) '' parabolicRoots .E7 (e6Nodes .E7)) ⊓
        torusGroup .E7 K =
      Subgroup.closure {g : ModGL .E7 K | ∃ j ∈ e6Nodes .E7, ∃ c : Kˣ,
        g = rootDiagUnit .E7 fun i =>
          c ^ iform (w • (Pi.single j 1 : Fin Tag.E7.rank → ℤ)) (Pi.single i 1)} := by
  obtain ⟨hQ, hQT, hHJ, -⟩ := E7_supported_Bruhat_and_exact_native_torus_kernel K (e6Nodes .E7)
  obtain ⟨hRS, -, hN⟩ := canonical_weyl_root_transport .E7 K
  have hinj : Function.Injective
      (MulAut.conj (canonicalRep (coxeterSystem .E7) K w)).toMonoidHom :=
    (MulAut.conj (canonicalRep (coxeterSystem .E7) K w)).injective
  have hspan : rootSpan .E7 K ((fun alpha => w • alpha) '' parabolicRoots .E7 (e6Nodes .E7)) =
      (subsystemGroup .E7 K (e6Nodes .E7)).map
        (MulAut.conj (canonicalRep (coxeterSystem .E7) K w)).toMonoidHom := by
    rw [hQ, hRS w _ fun α hα => hα.1]
  have htor : (torusGroup .E7 K).map
      (MulAut.conj (canonicalRep (coxeterSystem .E7) K w)).toMonoidHom = torusGroup .E7 K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 (hN w) y).1 hy
    · intro hx
      have h := (Subgroup.mem_normalizer_iff.1 (inv_mem (hN w)) x).1 hx
      rw [inv_inv] at h
      refine ⟨_, h, ?_⟩
      show canonicalRep (coxeterSystem .E7) K w * ((canonicalRep (coxeterSystem .E7) K w)⁻¹ * x *
        canonicalRep (coxeterSystem .E7) K w) * (canonicalRep (coxeterSystem .E7) K w)⁻¹ = x
      group
  have hkey : ∀ (j : Fin Tag.E7.rank) (c : Kˣ),
      (MulAut.conj (canonicalRep (coxeterSystem .E7) K w)).toMonoidHom (torusElt .E7 K j c) =
        rootDiagUnit .E7 fun i =>
          c ^ iform (w • (Pi.single j 1 : Fin Tag.E7.rank → ℤ)) (Pi.single i 1) := by
    intro j c
    have hd : torusElt .E7 K j c = rootDiagUnit .E7 (thetaDiag (Pi.single j 1) c) := by
      rw [torusElt_eq_rootDiagUnit]
      congr 1
      funext i
      show c ^ Tag.E7.cartan j i = c ^ iform (Pi.single j 1 : Fin Tag.E7.rank → ℤ) (Pi.single i 1)
      rw [E7_cartan_eq_iform j i]
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hd,
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit,
      weylAct_thetaDiag]
    rfl
  rw [hspan, ← htor, ← Subgroup.map_inf_eq _ _ _ hinj, hQT, hHJ]
  show (Subgroup.closure {g | ∃ i ∈ e6Nodes .E7, ∃ t : Kˣ, g = torusElt .E7 K i t}).map _ = _
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨j, hj, c, rfl⟩, rfl⟩
    exact ⟨j, hj, c, hkey j c⟩
  · rintro ⟨j, hj, c, rfl⟩
    exact ⟨torusElt .E7 K j c, ⟨j, hj, c, rfl⟩, hkey j c⟩

theorem e6_root_pair_stabilizer_eq {K : Type} [Field K] [IsAlgClosed K] [CharP K 2]
    (w : WeylGroup .E7) (Psi : Set (Fin Tag.E7.rank → ℤ))
    (hPsi : Psi = (fun alpha => w • alpha) '' parabolicRoots .E7 (e6Nodes .E7))
    {gamma : Fin Tag.E7.rank → ℤ} (hgamma : IsRoot .E7 gamma) :
    rootSpan .E7 K Psi ⊓
        Subgroup.normalizer (rootSubgroup .E7 K gamma : Set (ModGL .E7 K)) ⊓
        Subgroup.normalizer (rootSubgroup .E7 K (-gamma) : Set (ModGL .E7 K)) =
      (rootSpan .E7 K Psi ⊓ torusGroup .E7 K) ⊔
        rootSpan .E7 K {delta | delta ∈ Psi ∧ iform delta gamma = 0} := by
  have hτ : Tag.E7 = .D4 ∨ Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 :=
    Or.inr (Or.inr (Or.inl rfl))
  have hroot : ∀ p : ℕ, p.Prime → p ≠ 2 → ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := by
    intro p hp hp2
    have hpK : (p : K) ≠ 0 := fun h =>
      hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
        ((CharP.cast_eq_zero_iff K 2 p).1 h)).symm
    have : NeZero (p : K) := ⟨hpK⟩
    obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K p
    exact ⟨(hζ₀.isUnit hp.ne_zero).unit, IsPrimitiveRoot.coe_units_iff.mp (by
      rw [IsUnit.unit_spec]
      exact hζ₀)⟩
  obtain ⟨s, hs⟩ := hroot 3 Nat.prime_three (by decide)
  obtain ⟨t, ht5⟩ := hroot 5 (by norm_num) (by decide)
  obtain ⟨i6, hi6⟩ : ∃ i : Fin Tag.E7.rank, i = ⟨6, by decide⟩ := ⟨_, rfl⟩
  have hnot : ∀ i : Fin Tag.E7.rank, i ∉ e6Nodes .E7 ↔ i = i6 := by
    intro i
    have hlt : i.val < 7 := i.isLt
    rw [hi6]
    constructor
    · intro hi
      have hi' : ¬ i.val ≤ 5 := hi
      exact Fin.ext (by simp only; omega)
    · rintro rfl
      show ¬ (6 ≤ 5)
      omega
  have hb : ∀ v : Fin Tag.E7.rank → ℤ, rootChar (Pi.mulSingle i6 s) v = s ^ v i6 := by
    intro v
    rw [rootChar, Finset.prod_eq_single i6
      (fun i _ hi => by rw [Pi.mulSingle_eq_of_ne hi, one_zpow])
      (fun h => absurd (Finset.mem_univ i6) h), Pi.mulSingle_eq_same]
  have ha : ∀ v, rootChar (weylAct w (Pi.mulSingle i6 s)) v = s ^ (w⁻¹ • v) i6 := fun v => by
    rw [rootChar_weylAct, hb]
  have hcoef : ∀ β : Fin Tag.E7.rank → ℤ, IsRoot .E7 β → β i6 = -1 ∨ β i6 = 0 ∨ β i6 = 1 := by
    intro β hβ
    rw [hi6]
    exact E7_root_coeff_six β (mem_rootFinset.2 hβ)
  have hker : kernelRoots (rootCharHom (weylAct w (Pi.mulSingle i6 s))) = Psi := by
    rw [kernelRoots_rootCharHom, hPsi]
    ext α
    constructor
    · rintro ⟨hα, h1⟩
      have hβ : IsRoot .E7 (w⁻¹ • α) := IsRoot.smul hα w⁻¹
      have h0 : (w⁻¹ • α) i6 = 0 := by
        rw [ha] at h1
        have hdvd := (hs.zpow_eq_one_iff_dvd _).1 h1
        rcases hcoef _ hβ with h | h | h <;> rw [h] at hdvd ⊢ <;> omega
      refine ⟨w⁻¹ • α, ⟨hβ, fun i hi => ?_⟩, smul_inv_smul w α⟩
      rw [(hnot i).1 hi]
      exact h0
    · rintro ⟨β, ⟨hβ, hβJ⟩, rfl⟩
      refine ⟨IsRoot.smul hβ w, ?_⟩
      rw [ha, inv_smul_smul, hβJ i6 ((hnot i6).2 rfl), zpow_zero]
  have ht : ∀ n : ℕ, 0 < n → n ≤ 4 → t ^ n ≠ 1 := fun n h0 h4 =>
    ht5.pow_ne_one_of_pos_of_lt (by omega) (by omega)
  have hind : ∀ (v : Fin Tag.E7.rank → ℤ) (n : ℤ),
      rootChar (weylAct w (Pi.mulSingle i6 s)) v * t ^ n = 1 → t ^ n = 1 := by
    intro v n h
    rw [ha] at h
    have hs3 : s ^ (3 : ℤ) = 1 := (hs.zpow_eq_one_iff_dvd 3).2 (by norm_num)
    have h3 : t ^ (n * 3) = 1 := by
      have h' : (s ^ ((w⁻¹ • v) i6) * t ^ n) ^ (3 : ℤ) = 1 := by rw [h, one_zpow]
      rwa [mul_zpow, ← zpow_mul, ← zpow_mul, mul_comm ((w⁻¹ • v) i6) 3, zpow_mul, hs3, one_zpow,
        one_mul] at h'
    have hdvd := (ht5.zpow_eq_one_iff_dvd _).1 h3
    exact (ht5.zpow_eq_one_iff_dvd _).2 (by push_cast at hdvd ⊢; omega)
  have hEq := torusGroup_sup_rootSpan_kernelRoots_inf_normalizer_eq (τ := .E7) (K := K) hτ
    (weylAct w (Pi.mulSingle i6 s)) hgamma t ht hind
  rw [kernelRoots_rootCharHom_mul_thetaDiag hτ _ hgamma t ht hind, hker] at hEq
  have hRoots : ∀ δ ∈ Psi, IsRoot .E7 δ := by
    rw [← hker]
    exact fun δ hδ => hδ.1
  have hPR : ∀ δ ∈ {delta | delta ∈ Psi ∧ iform delta gamma = 0}, IsRoot .E7 δ :=
    fun δ hδ => hRoots δ hδ.1
  have hPle : rootSpan .E7 K {delta | delta ∈ Psi ∧ iform delta gamma = 0} ≤
      rootSpan .E7 K Psi :=
    biSup_mono fun δ hδ => hδ.1
  refine le_antisymm ?_ ?_
  · intro g hg
    have hg' : g ∈ (torusGroup .E7 K ⊔ rootSpan .E7 K Psi) ⊓
        Subgroup.normalizer (rootSubgroup .E7 K gamma : Set (ModGL .E7 K)) ⊓
        Subgroup.normalizer (rootSubgroup .E7 K (-gamma) : Set (ModGL .E7 K)) :=
      ⟨⟨Subgroup.mem_sup_right hg.1.1, hg.1.2⟩, hg.2⟩
    rw [hEq] at hg'
    have hsplit : g ∈ ((torusGroup .E7 K ⊔
        rootSpan .E7 K {delta | delta ∈ Psi ∧ iform delta gamma = 0} : Subgroup (ModGL .E7 K)) :
          Set (ModGL .E7 K)) := hg'
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (torusGroup_le_normalizer_rootSpan hPR)] at hsplit
    obtain ⟨h, hh, x, hx, rfl⟩ := hsplit
    have hhH : h ∈ rootSpan .E7 K Psi := by
      have e : h = (h * x) * x⁻¹ := by group
      rw [e]
      exact mul_mem hg.1.1 (inv_mem (hPle hx))
    exact mul_mem (Subgroup.mem_sup_left ⟨hhH, hh⟩) (Subgroup.mem_sup_right hx)
  · have hN : torusGroup .E7 K ⊔ rootSpan .E7 K {delta | delta ∈ Psi ∧ iform delta gamma = 0} ≤
        Subgroup.normalizer (rootSubgroup .E7 K gamma : Set (ModGL .E7 K)) ⊓
          Subgroup.normalizer (rootSubgroup .E7 K (-gamma) : Set (ModGL .E7 K)) := by
      rw [← hEq]
      exact fun g hg => ⟨hg.1.2, hg.2⟩
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · have h := hN (Subgroup.mem_sup_left hg.2)
      exact ⟨⟨hg.1, h.1⟩, h.2⟩
    · have h := hN (Subgroup.mem_sup_right hg)
      exact ⟨⟨hPle hg, h.1⟩, h.2⟩

theorem isConnectedAlgebraicSubgroup_e6_root_pair_stabilizer
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (w : WeylGroup .E7) (Psi : Set (Fin Tag.E7.rank → ℤ))
    (hPsi : Psi = (fun alpha => w • alpha) '' parabolicRoots .E7 (e6Nodes .E7))
    (gamma : Fin Tag.E7.rank → ℤ) (hgamma : IsRoot .E7 gamma) (_hgPsi : gamma ∈ Psi) :
    IsConnectedAlgebraicSubgroup Omega
      ((rootSpan .E7 Omega Psi ⊓
        Subgroup.normalizer (rootSubgroup .E7 Omega gamma : Set (ModGL .E7 Omega)) ⊓
        Subgroup.normalizer (rootSubgroup .E7 Omega (-gamma) : Set (ModGL .E7 Omega))).map
          (modGLPoint .E7 Omega).toMonoidHom) := by
  let lam : ↥(e6Nodes .E7) → Fin Tag.E7.rank → ℤ := fun j i =>
    iform (w • (Pi.single (j : Fin Tag.E7.rank) 1 : Fin Tag.E7.rank → ℤ)) (Pi.single i 1)
  obtain ⟨C, hCl, hCr⟩ : ∃ C : ↥(e6Nodes .E7) ⊕ ↥{delta | delta ∈ Psi ∧ iform delta gamma = 0} →
      Set (ModGL .E7 Omega),
      (∀ j, C (Sum.inl j) = Set.range fun c : Omegaˣ => rootDiagUnit .E7 fun i => c ^ lam j i) ∧
        ∀ δ, C (Sum.inr δ) = Set.range (pinnedX .E7 Omega δ.1) :=
    ⟨Sum.elim (fun j => Set.range fun c : Omegaˣ => rootDiagUnit .E7 fun i => c ^ lam j i)
      (fun δ => Set.range (pinnedX .E7 Omega δ.1)), fun _ => rfl, fun _ => rfl⟩
  have hT : rootSpan .E7 Omega Psi ⊓ torusGroup .E7 Omega =
      Subgroup.closure (⋃ j, C (Sum.inl j)) := by
    have hT0 := rootSpan_e6_inf_torusGroup_eq Omega w
    rw [← hPsi] at hT0
    rw [hT0]
    congr 1
    ext g
    simp only [hCl, Set.mem_iUnion, Set.mem_range, Set.mem_setOf_eq, Subtype.exists]
    constructor
    · rintro ⟨j, hj, c, rfl⟩
      exact ⟨j, hj, c, rfl⟩
    · rintro ⟨j, hj, c, rfl⟩
      exact ⟨j, hj, c, rfl⟩
  have hR : rootSpan .E7 Omega {delta | delta ∈ Psi ∧ iform delta gamma = 0} =
      Subgroup.closure (⋃ δ, C (Sum.inr δ)) := by
    rw [rootSpan, iSup_subtype']
    simp only [rootSubgroup, Subgroup.closure_iUnion, hCr]
  have hgen : (rootSpan .E7 Omega Psi ⊓ torusGroup .E7 Omega) ⊔
      rootSpan .E7 Omega {delta | delta ∈ Psi ∧ iform delta gamma = 0} =
        Subgroup.closure (⋃ x, C x) := by
    rw [Set.iUnion_sum, Subgroup.closure_union, hT, hR]
  rw [e6_root_pair_stabilizer_eq w Psi hPsi hgamma, hgen]
  refine isConnectedAlgebraicSubgroup_closure_iUnion C ?_ ?_
  · rintro (j | δ)
    · rw [hCl]
      exact isDomainImage_cocharCurve (lam j)
    · rw [hCr]
      exact isDomainImage_pinnedXCurve δ.1
  · rintro (j | δ)
    · rw [hCl]
      refine ⟨1, ?_⟩
      simp only [one_zpow]
      exact rootDiagUnit_one
    · rw [hCr]
      exact ⟨0, pinnedX_zero .E7 Omega δ.1⟩

private def e6WordTable : List (List ℤ × List ℕ) := [
  ([1, 0, 0, 0, 0, 0, 0], []),
  ([-1, 0, 0, 0, 0, 0, 0], [0]),
  ([1, 0, 1, 0, 0, 0, 0], [2]),
  ([-1, 0, -1, 0, 0, 0, 0], [2, 0]),
  ([0, 0, 1, 0, 0, 0, 0], [0, 2]),
  ([1, 0, 1, 1, 0, 0, 0], [3, 2]),
  ([-1, 0, -1, -1, 0, 0, 0], [3, 2, 0]),
  ([0, 0, -1, 0, 0, 0, 0], [0, 2, 0]),
  ([0, 0, 1, 1, 0, 0, 0], [3, 0, 2]),
  ([1, 0, 1, 1, 1, 0, 0], [4, 3, 2]),
  ([1, 1, 1, 1, 0, 0, 0], [1, 3, 2]),
  ([-1, -1, -1, -1, 0, 0, 0], [1, 3, 2, 0]),
  ([-1, 0, -1, -1, -1, 0, 0], [4, 3, 2, 0]),
  ([0, 0, -1, -1, 0, 0, 0], [3, 0, 2, 0]),
  ([0, 0, 0, 1, 0, 0, 0], [2, 3, 0, 2]),
  ([0, 0, 1, 1, 1, 0, 0], [4, 3, 0, 2]),
  ([0, 1, 1, 1, 0, 0, 0], [1, 3, 0, 2]),
  ([1, 0, 1, 1, 1, 1, 0], [5, 4, 3, 2]),
  ([1, 1, 1, 1, 1, 0, 0], [4, 1, 3, 2]),
  ([-1, -1, -1, -1, -1, 0, 0], [4, 1, 3, 2, 0]),
  ([-1, 0, -1, -1, -1, -1, 0], [5, 4, 3, 2, 0]),
  ([0, -1, -1, -1, 0, 0, 0], [1, 3, 0, 2, 0]),
  ([0, 0, -1, -1, -1, 0, 0], [4, 3, 0, 2, 0]),
  ([0, 0, 0, -1, 0, 0, 0], [2, 3, 0, 2, 0]),
  ([0, 0, 0, 1, 1, 0, 0], [4, 2, 3, 0, 2]),
  ([0, 0, 1, 1, 1, 1, 0], [5, 4, 3, 0, 2]),
  ([0, 1, 0, 1, 0, 0, 0], [2, 1, 3, 0, 2]),
  ([0, 1, 1, 1, 1, 0, 0], [4, 1, 3, 0, 2]),
  ([1, 1, 1, 1, 1, 1, 0], [5, 4, 1, 3, 2]),
  ([1, 1, 1, 2, 1, 0, 0], [3, 4, 1, 3, 2]),
  ([-1, -1, -1, -2, -1, 0, 0], [3, 4, 1, 3, 2, 0]),
  ([-1, -1, -1, -1, -1, -1, 0], [5, 4, 1, 3, 2, 0]),
  ([0, -1, -1, -1, -1, 0, 0], [4, 1, 3, 0, 2, 0]),
  ([0, -1, 0, -1, 0, 0, 0], [2, 1, 3, 0, 2, 0]),
  ([0, 0, -1, -1, -1, -1, 0], [5, 4, 3, 0, 2, 0]),
  ([0, 0, 0, -1, -1, 0, 0], [4, 2, 3, 0, 2, 0]),
  ([0, 0, 0, 0, 1, 0, 0], [3, 4, 2, 3, 0, 2]),
  ([0, 0, 0, 1, 1, 1, 0], [5, 4, 2, 3, 0, 2]),
  ([0, 1, 0, 0, 0, 0, 0], [3, 2, 1, 3, 0, 2]),
  ([0, 1, 0, 1, 1, 0, 0], [4, 2, 1, 3, 0, 2]),
  ([0, 1, 1, 1, 1, 1, 0], [5, 4, 1, 3, 0, 2]),
  ([0, 1, 1, 2, 1, 0, 0], [3, 4, 1, 3, 0, 2]),
  ([1, 1, 1, 2, 1, 1, 0], [5, 3, 4, 1, 3, 2]),
  ([1, 1, 2, 2, 1, 0, 0], [2, 3, 4, 1, 3, 2]),
  ([-1, -1, -2, -2, -1, 0, 0], [2, 3, 4, 1, 3, 2, 0]),
  ([-1, -1, -1, -2, -1, -1, 0], [5, 3, 4, 1, 3, 2, 0]),
  ([0, -1, -1, -2, -1, 0, 0], [3, 4, 1, 3, 0, 2, 0]),
  ([0, -1, -1, -1, -1, -1, 0], [5, 4, 1, 3, 0, 2, 0]),
  ([0, -1, 0, -1, -1, 0, 0], [4, 2, 1, 3, 0, 2, 0]),
  ([0, -1, 0, 0, 0, 0, 0], [3, 2, 1, 3, 0, 2, 0]),
  ([0, 0, 0, -1, -1, -1, 0], [5, 4, 2, 3, 0, 2, 0]),
  ([0, 0, 0, 0, -1, 0, 0], [3, 4, 2, 3, 0, 2, 0]),
  ([0, 0, 0, 0, 1, 1, 0], [5, 3, 4, 2, 3, 0, 2]),
  ([0, 1, 0, 1, 1, 1, 0], [5, 4, 2, 1, 3, 0, 2]),
  ([0, 1, 1, 2, 1, 1, 0], [5, 3, 4, 1, 3, 0, 2]),
  ([1, 1, 1, 2, 2, 1, 0], [4, 5, 3, 4, 1, 3, 2]),
  ([1, 1, 2, 2, 1, 1, 0], [5, 2, 3, 4, 1, 3, 2]),
  ([-1, -1, -2, -2, -1, -1, 0], [5, 2, 3, 4, 1, 3, 2, 0]),
  ([-1, -1, -1, -2, -2, -1, 0], [4, 5, 3, 4, 1, 3, 2, 0]),
  ([0, -1, -1, -2, -1, -1, 0], [5, 3, 4, 1, 3, 0, 2, 0]),
  ([0, -1, 0, -1, -1, -1, 0], [5, 4, 2, 1, 3, 0, 2, 0]),
  ([0, 0, 0, 0, -1, -1, 0], [5, 3, 4, 2, 3, 0, 2, 0]),
  ([0, 0, 0, 0, 0, 1, 0], [4, 5, 3, 4, 2, 3, 0, 2]),
  ([0, 1, 1, 2, 2, 1, 0], [4, 5, 3, 4, 1, 3, 0, 2]),
  ([1, 1, 2, 2, 2, 1, 0], [4, 5, 2, 3, 4, 1, 3, 2]),
  ([-1, -1, -2, -2, -2, -1, 0], [4, 5, 2, 3, 4, 1, 3, 2, 0]),
  ([0, -1, -1, -2, -2, -1, 0], [4, 5, 3, 4, 1, 3, 0, 2, 0]),
  ([0, 0, 0, 0, 0, -1, 0], [4, 5, 3, 4, 2, 3, 0, 2, 0]),
  ([1, 1, 2, 3, 2, 1, 0], [3, 4, 5, 2, 3, 4, 1, 3, 2]),
  ([-1, -1, -2, -3, -2, -1, 0], [3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
  ([1, 2, 2, 3, 2, 1, 0], [1, 3, 4, 5, 2, 3, 4, 1, 3, 2]),
  ([-1, -2, -2, -3, -2, -1, 0], [1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0])
]

private def e6Word (β : Fin Tag.E7.rank → ℤ) : List (Fin Tag.E7.rank) :=
  (((e6WordTable.find? fun p => p.1 == List.ofFn β).map Prod.snd).getD []).map
    fun n => ⟨n % 7, Nat.mod_lt _ (by decide)⟩

private theorem e6Word_spec : ∀ β ∈ rootFinset .E7, β ⟨6, by decide⟩ = 0 →
    List.ofFn ((e6Word β).foldr (fun i v => reflect .E7 i v) (Pi.single ⟨0, by decide⟩ 1)) =
      List.ofFn β ∧ ∀ i ∈ e6Word β, i.val ≤ 5 := by
  decide +kernel

theorem exists_mem_parabolicWeylGroup_e6_smul_eq {β : Fin Tag.E7.rank → ℤ}
    (hβ : β ∈ parabolicRoots .E7 (e6Nodes .E7)) :
    ∃ u ∈ parabolicWeylGroup .E7 (e6Nodes .E7),
      u • (Pi.single ⟨0, by decide⟩ 1 : Fin Tag.E7.rank → ℤ) = β := by
  have h6 : β ⟨6, by decide⟩ = 0 := hβ.2 _ (by show ¬ (6 ≤ 5); omega)
  obtain ⟨h1, h2⟩ := e6Word_spec β (mem_rootFinset.2 hβ.1) h6
  refine ⟨(coxeterSystem .E7).wordProd (e6Word β), ?_, ?_⟩
  · rw [CoxeterSystem.wordProd]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact simple_mem_parabolicWeylGroup_iff.2 (h2 i hi)
  · rw [wordProd_smul_eq_foldr_reflect]
    exact List.ofFn_injective h1

theorem exists_conj_e6_rootSpan_pair
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (w : WeylGroup .E7) (Psi : Set (Fin Tag.E7.rank → ℤ))
    (hPsi : Psi = (fun alpha => w • alpha) '' parabolicRoots .E7 (e6Nodes .E7))
    {beta gamma : Fin Tag.E7.rank → ℤ} (hbeta : beta ∈ Psi) (hgamma : gamma ∈ Psi) :
    ∃ g ∈ rootSpan .E7 Omega Psi,
      (rootSpan .E7 Omega {beta, -beta}).map (MulAut.conj g).toMonoidHom =
        rootSpan .E7 Omega {gamma, -gamma} := by
  subst hPsi
  obtain ⟨β, hβ, rfl⟩ := hbeta
  obtain ⟨γ, hγ, rfl⟩ := hgamma
  obtain ⟨uβ, huβ, hβe⟩ := exists_mem_parabolicWeylGroup_e6_smul_eq hβ
  obtain ⟨uγ, huγ, hγe⟩ := exists_mem_parabolicWeylGroup_e6_smul_eq hγ
  have huJ : uγ * uβ⁻¹ ∈ parabolicWeylGroup .E7 (e6Nodes .E7) := mul_mem huγ (inv_mem huβ)
  have hu : (uγ * uβ⁻¹) • β = γ := by rw [mul_smul, ← hβe, inv_smul_smul, hγe]
  obtain ⟨hQ, -⟩ := E7_supported_Bruhat_and_exact_native_torus_kernel Omega (e6Nodes .E7)
  obtain ⟨hRS, -, -⟩ := canonical_weyl_root_transport .E7 Omega
  have hpairR : ∀ δ : Fin Tag.E7.rank → ℤ, IsRoot .E7 δ →
      ∀ α ∈ ({δ, -δ} : Set (Fin Tag.E7.rank → ℤ)), IsRoot .E7 α := by
    rintro δ hδ α (rfl | rfl)
    · exact hδ
    · exact IsRoot.neg hδ
  have hpair : ∀ (v : WeylGroup .E7) (δ : Fin Tag.E7.rank → ℤ), IsRoot .E7 δ →
      (rootSpan .E7 Omega {δ, -δ}).map
          (MulAut.conj (canonicalRep (coxeterSystem .E7) Omega v)).toMonoidHom =
        rootSpan .E7 Omega {v • δ, -(v • δ)} := by
    intro v δ hδ
    rw [hRS v _ (hpairR δ hδ), Set.image_pair, smul_neg]
  refine ⟨canonicalRep (coxeterSystem .E7) Omega w *
      canonicalRep (coxeterSystem .E7) Omega (uγ * uβ⁻¹) *
      (canonicalRep (coxeterSystem .E7) Omega w)⁻¹, ?_, ?_⟩
  · rw [← hRS w _ fun α hα => hα.1, ← hQ]
    exact ⟨_, canonicalRep_mem_subsystemGroup huJ, rfl⟩
  · rw [← hpair w β hβ.1, ← map_conj_mul, ← hpair w γ hγ.1, ← hu, ← hpair _ β hβ.1,
      ← map_conj_mul]
    congr 3
    group

end CFSG.StandardType.LieKnownR2.ExcPos

end
