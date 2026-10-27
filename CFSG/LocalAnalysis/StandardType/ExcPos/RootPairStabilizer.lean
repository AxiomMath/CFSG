module

public import CFSG.LieType.Chevalley.KernelWeylStabilizer
public import CFSG.LieType.Chevalley.ToralCentralizerBruhat
public import CFSG.LieType.AlgebraicGroups.KernelRootBruhat
public import CFSG.LieType.AlgebraicGroups.KernelRootGroup
public import CFSG.LieType.AlgebraicGroups.ToralRootCover
public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart2
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcConn
import CFSG.LocalAnalysis.SeitzReduction.EPilotRoots
import CFSG.RankThree.PartOne.D4RC.Descent
import CFSG.RankThree.PartOne.KE.ConjRootSpan
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8KilledPlaneBlocksGeo
import CFSG.LieType.Chevalley.SimplyLacedCommutation
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct
import CFSG.LieType.Chevalley.FixedRootCentralizerGeneration
import CFSG.RankThree.PartOne.TCX.ParabolicConj
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi
import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore
open CFSG.ClassicalInvolution.ModelFacts.Levi (thetaDiag rootChar_thetaDiag rootChar_mul
  iform_eq_sum_single)

variable {τ : Tag} {K : Type} [Field K]

theorem zpow_ne_one_of_pow_ne_one {G : Type*} [Group G] {t : G}
    (ht : ∀ k : ℕ, 0 < k → k ≤ 4 → t ^ k ≠ 1) {n : ℤ} (hn : n ≠ 0)
    (h : |n| ≤ 4) : t ^ n ≠ 1 := by
  intro hpow
  have hle : n.natAbs ≤ 4 := by
    rw [Int.abs_eq_natAbs] at h
    exact_mod_cast h
  exact ht n.natAbs (Int.natAbs_pos.mpr hn) hle (pow_natAbs_eq_one.mpr hpow)

theorem eq_of_zpow_eq_zpow_of_abs_le {G : Type*} [Group G] {t : G} {m n : ℤ}
    (hm : |m| ≤ 2) (hn : |n| ≤ 2)
    (ht : ∀ k : ℕ, 0 < k → k ≤ 4 → t ^ k ≠ 1) (h : t ^ m = t ^ n) : m = n := by
  by_contra hmn
  have hmn' : m - n ≠ 0 := sub_ne_zero.mpr hmn
  have hle : |m - n| ≤ 4 := by
    have hm' : -2 ≤ m ∧ m ≤ 2 := by rwa [abs_le] at hm
    have hn' : -2 ≤ n ∧ n ≤ 2 := by rwa [abs_le] at hn
    rw [abs_le]
    omega
  have hpow : t ^ (m - n) = 1 := by
    rw [zpow_sub, h, mul_inv_cancel]
  exact (zpow_ne_one_of_pow_ne_one ht hmn' hle) hpow

theorem kernelRoots_rootCharHom_mul_thetaDiag
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (a : Fin τ.rank → Kˣ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (t : Kˣ)
    (ht : ∀ n : ℕ, 0 < n → n ≤ 4 → t ^ n ≠ 1)
    (hind : ∀ (v : Fin τ.rank → ℤ) (n : ℤ), rootChar a v * t ^ n = 1 → t ^ n = 1) :
    kernelRoots (rootCharHom (a * thetaDiag γ t)) =
      {δ | δ ∈ kernelRoots (rootCharHom a) ∧ iform δ γ = 0} := by
  ext δ
  constructor
  · intro hδ
    rw [kernelRoots_rootCharHom] at hδ ⊢
    obtain ⟨hδroot, hχ⟩ := hδ
    rw [rootChar_mul, rootChar_thetaDiag] at hχ
    have ht0 : t ^ iform γ δ = 1 := hind δ (iform γ δ) hχ
    have hbound : |iform γ δ| ≤ 2 :=
      abs_iform_le_two_of_isRoot_simplyLaced hτ hγ hδroot
    have hzero : iform γ δ = 0 := by
      by_contra hne
      exact zpow_ne_one_of_pow_ne_one ht hne (le_trans hbound (by norm_num)) ht0
    have hroot : rootChar a δ = 1 := by simpa [ht0] using hχ
    exact ⟨⟨hδroot, hroot⟩, (iform_comm δ γ).trans hzero⟩
  · rintro ⟨hδ, hzero⟩
    rw [kernelRoots_rootCharHom] at hδ ⊢
    refine ⟨hδ.1, ?_⟩
    rw [rootChar_mul, rootChar_thetaDiag, ← iform_comm, hzero, zpow_zero, mul_one]
    exact hδ.2

theorem rootSubgroup_le_normalizer_rootSubgroup_of_iform_eq_zero
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (horth : iform δ γ = 0) :
    rootSubgroup τ K δ ≤
      Subgroup.normalizer (rootSubgroup τ K γ : Set (ModGL τ K)) := by
  have hdot : δ ⬝ᵥ (Matrix.mulVec τ.symmetrizedCartan γ) = 0 := by
    rw [dotProduct_mulVec_eq_iform]
    exact horth
  have hcomm := (simply_laced_orthogonal_root_commutation τ hτ).2 K δ γ hδ hγ hdot
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (hcomm x hx y hy).symm

theorem rootSpan_le_normalizer_rootSubgroup_of_forall_iform_eq_zero
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ δ ∈ S, IsRoot τ δ ∧ iform δ γ = 0) :
    rootSpan τ K S ≤ Subgroup.normalizer (rootSubgroup τ K γ : Set (ModGL τ K)) :=
  iSup₂_le fun δ hδ =>
    rootSubgroup_le_normalizer_rootSubgroup_of_iform_eq_zero hτ (hS δ hδ).1 hγ (hS δ hδ).2

theorem mem_rootCharStabilizer_of_mem_closure_rootReflection
    {a : Fin τ.rank → Kˣ}
    {w : WeylGroup τ}
    (hw : w ∈ Subgroup.closure (rootReflection '' kernelRoots (rootCharHom a))) :
    w ∈ rootCharStabilizer a := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨δ, hδ, rfl⟩ := hx
    rw [kernelRoots_rootCharHom] at hδ
    intro v
    rw [rootReflection_smul hδ.1 v, rootChar_sub, rootChar_zsmul, hδ.2]
    simp
  | one => intro v; rw [one_smul]
  | mul x y _ _ ihx ihy =>
    intro v
    rw [mul_smul, ihx (y • v), ihy v]
  | inv x _ ih =>
    intro v
    have h := ih (x⁻¹ • v)
    simpa using h.symm

section

open CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
  (Uθ Uneg Lθ Jθ iθ iform_highRoot_single iform_highRoot_apply)
open CFSG.StandardType.F4ExplicitPos.PairStabilizer

theorem weylAct_thetaDiag
    (w : WeylGroup τ) (θ : Fin τ.rank → ℤ) (c : Kˣ) :
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct w (thetaDiag θ c) =
      thetaDiag (w • θ) c := by
  refine CFSG.HardMathSupport.Timmesfeld.Tables.T1b.eq_of_rootChar_eq fun v => ?_
  rw [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.rootChar_weylAct, rootChar_thetaDiag,
    rootChar_thetaDiag, ← iform_smul w θ (w⁻¹ • v), smul_inv_smul]

theorem adjointGroup_inf_normalizer_le_centralizer_thetaDiag_of_smul
    {τ : Tag} {K : Type} [Field K] {γ : Fin τ.rank → ℤ}
    (x : WeylGroup τ) (hx : x • highRoot τ = γ) (t : Kˣ) :
    adjointGroup τ K ⊓ Subgroup.normalizer (rootSubgroup τ K γ : Set (ModGL τ K)) ⊓
        Subgroup.normalizer (rootSubgroup τ K (-γ) : Set (ModGL τ K)) ≤
      Subgroup.centralizer {rootDiagUnit τ (thetaDiag γ t)} := by
  intro g hg
  let n := canonicalRep (coxeterSystem τ) K x
  have hn : n ∈ adjointGroup τ K :=
    canonicalRep_mem_adjointGroup (coxeterSystem τ) K x
  have hmap : (rootSubgroup τ K (highRoot τ)).map (MulAut.conj n).toMonoidHom =
      rootSubgroup τ K γ := by
    have h := CFSG.RankThree.PartOne.KE.map_conj_rootSubgroup x (isRoot_highRoot τ)
      (L := K)
    simpa [n, hx] using h
  have hmap_neg : (rootSubgroup τ K (-highRoot τ)).map
      (MulAut.conj n).toMonoidHom = rootSubgroup τ K (-γ) := by
    have h := CFSG.RankThree.PartOne.KE.map_conj_rootSubgroup x
      (IsRoot.neg (isRoot_highRoot τ)) (L := K)
    have hx_neg : x • (-highRoot τ) = -γ := by rw [smul_neg, hx]
    simpa [n, hx_neg] using h
  have hmap_inv : (rootSubgroup τ K γ).map (MulAut.conj n⁻¹).toMonoidHom =
      rootSubgroup τ K (highRoot τ) := by
    rw [← hmap]
    exact CFSG.LieType.Chevalley.map_conj_inv_map_conj
      (rootSubgroup τ K (highRoot τ)) n
  have hmap_neg_inv : (rootSubgroup τ K (-γ)).map
      (MulAut.conj n⁻¹).toMonoidHom = rootSubgroup τ K (-highRoot τ) := by
    rw [← hmap_neg]
    exact CFSG.LieType.Chevalley.map_conj_inv_map_conj
      (rootSubgroup τ K (-highRoot τ)) n
  obtain ⟨hgP, hgNneg⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨hgA, hgNγ⟩ := Subgroup.mem_inf.1 hgP
  have hgA' : n⁻¹ * g * n ∈ adjointGroup τ K :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hn) hgA) hn
  have hgNθ : n⁻¹ * g * n ∈ Subgroup.normalizer
      (rootSubgroup τ K (highRoot τ) : Set (ModGL τ K)) := by
    have hg_eq : n * (n⁻¹ * g * n) * n⁻¹ = g := by group
    have h := CFSG.LieType.Chevalley.mem_normalizer_map_conj_inv
      (H := rootSubgroup τ K γ) (n := n) (m := n⁻¹ * g * n)
      (by simpa [hg_eq] using hgNγ)
    rwa [hmap_inv] at h
  have hgNneg' : n⁻¹ * g * n ∈ Subgroup.normalizer
      (rootSubgroup τ K (-highRoot τ) : Set (ModGL τ K)) := by
    have hg_neg_eq : n * (n⁻¹ * g * n) * n⁻¹ = g := by group
    have h := CFSG.LieType.Chevalley.mem_normalizer_map_conj_inv
      (H := rootSubgroup τ K (-γ)) (n := n) (m := n⁻¹ * g * n)
      (by simpa [hg_neg_eq] using hgNneg)
    rwa [hmap_neg_inv] at h
  have hLθ : n⁻¹ * g * n ∈ Lθ τ K := by
    rw [← adjointGroup_inf_normalizer_Uθ_inf_normalizer_Uneg_eq_Lθ τ K]
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hgA', hgNθ⟩, hgNneg'⟩
  have hcommθ : (n⁻¹ * g * n) * rootDiagUnit τ (thetaDiag (highRoot τ) t) =
      rootDiagUnit τ (thetaDiag (highRoot τ) t) * (n⁻¹ * g * n) := by
    refine CFSG.RankThree.PartOne.TCX.rootDiagUnit_commute_parabolicLevi
      (thetaDiag (highRoot τ) t) ?_ hLθ
    intro j hj
    have hj' : j ≠ iθ τ := by simpa [Jθ] using hj
    simp [thetaDiag, iform_highRoot_apply, hj']
  have hconj : n * rootDiagUnit τ (thetaDiag (highRoot τ) t) * n⁻¹ =
      rootDiagUnit τ (thetaDiag γ t) := by
    rw [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit,
      weylAct_thetaDiag, hx]
  have hgcomm : g * rootDiagUnit τ (thetaDiag γ t) =
      rootDiagUnit τ (thetaDiag γ t) * g := by
    calc g * rootDiagUnit τ (thetaDiag γ t)
        = g * (n * rootDiagUnit τ (thetaDiag (highRoot τ) t) * n⁻¹) := by rw [hconj]
      _ = n * (n⁻¹ * g * n) * rootDiagUnit τ (thetaDiag (highRoot τ) t) * n⁻¹ := by
            group
      _ = n * ((n⁻¹ * g * n) * rootDiagUnit τ (thetaDiag (highRoot τ) t)) * n⁻¹ := by
            group
      _ = n * (rootDiagUnit τ (thetaDiag (highRoot τ) t) * (n⁻¹ * g * n)) * n⁻¹ := by
            rw [hcommθ]
      _ = n * rootDiagUnit τ (thetaDiag (highRoot τ) t) * (n⁻¹ * g * n) * n⁻¹ := by
            group
      _ = n * rootDiagUnit τ (thetaDiag (highRoot τ) t) * n⁻¹ * g := by
            group
      _ = rootDiagUnit τ (thetaDiag γ t) * g := by rw [hconj]
  exact Subgroup.mem_centralizer_singleton_iff.2 hgcomm

theorem adjointGroup_inf_normalizer_le_centralizer_thetaDiag
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (t : Kˣ) :
    adjointGroup τ K ⊓ Subgroup.normalizer (rootSubgroup τ K γ : Set (ModGL τ K)) ⊓
        Subgroup.normalizer (rootSubgroup τ K (-γ) : Set (ModGL τ K)) ≤
      Subgroup.centralizer {rootDiagUnit τ (thetaDiag γ t)} := by
  rcases hτ with rfl | rfl | rfl | rfl
  · obtain ⟨x, hx⟩ := CFSG.RankThree.PartOne.D4RC.rcd_exists_smul_highRoot hγ
    exact adjointGroup_inf_normalizer_le_centralizer_thetaDiag_of_smul x hx t
  · obtain ⟨x, hx⟩ := CFSG.SeitzReduction.EPilot.exists_smul_highRoot_eq
      (Or.inl rfl) hγ
    exact adjointGroup_inf_normalizer_le_centralizer_thetaDiag_of_smul x hx t
  · obtain ⟨x, hx⟩ := CFSG.SeitzReduction.EPilot.exists_smul_highRoot_eq
      (Or.inr (Or.inl rfl)) hγ
    exact adjointGroup_inf_normalizer_le_centralizer_thetaDiag_of_smul x hx t
  · obtain ⟨x, hx⟩ := CFSG.SeitzReduction.EPilot.exists_smul_highRoot_eq
      (Or.inr (Or.inr rfl)) hγ
    exact adjointGroup_inf_normalizer_le_centralizer_thetaDiag_of_smul x hx t

end

theorem torusGroup_sup_rootSpan_kernelRoots_mul_thetaDiag_le_inf_normalizer
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (a : Fin τ.rank → Kˣ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (t : Kˣ)
    (ht : ∀ n : ℕ, 0 < n → n ≤ 4 → t ^ n ≠ 1)
    (hind : ∀ (v : Fin τ.rank → ℤ) (n : ℤ), rootChar a v * t ^ n = 1 → t ^ n = 1) :
    torusGroup τ K ⊔ rootSpan τ K (kernelRoots (rootCharHom (a * thetaDiag γ t))) ≤
      (torusGroup τ K ⊔ rootSpan τ K (kernelRoots (rootCharHom a))) ⊓
        Subgroup.normalizer (rootSubgroup τ K γ : Set (ModGL τ K)) ⊓
        Subgroup.normalizer (rootSubgroup τ K (-γ) : Set (ModGL τ K)) := by
  have hker := kernelRoots_rootCharHom_mul_thetaDiag hτ a hγ t ht hind
  have hsubset : kernelRoots (rootCharHom (a * thetaDiag γ t)) ⊆
      kernelRoots (rootCharHom a) := by
    intro δ hδ
    rw [hker] at hδ
    exact hδ.1
  have hTγ : torusGroup τ K ≤
      Subgroup.normalizer (rootSubgroup τ K γ : Set (ModGL τ K)) := by
    have h := torusGroup_le_normalizer_rootSpan (K := K) (S := {γ})
      (fun α hα => by
        rw [Set.mem_singleton_iff] at hα
        rwa [hα])
    rwa [rootSpan, iSup_singleton] at h
  have hTneg : torusGroup τ K ≤
      Subgroup.normalizer (rootSubgroup τ K (-γ) : Set (ModGL τ K)) := by
    have h := torusGroup_le_normalizer_rootSpan (K := K) (S := {-γ})
      (fun α hα => by
        rw [Set.mem_singleton_iff] at hα
        rw [hα]
        exact IsRoot.neg hγ)
    rwa [rootSpan, iSup_singleton] at h
  have hSorth : ∀ δ ∈ kernelRoots (rootCharHom (a * thetaDiag γ t)),
      IsRoot τ δ ∧ iform δ γ = 0 := by
    intro δ hδ
    rw [hker] at hδ
    exact ⟨hδ.1.1, hδ.2⟩
  have hSorth_neg : ∀ δ ∈ kernelRoots (rootCharHom (a * thetaDiag γ t)),
      IsRoot τ δ ∧ iform δ (-γ) = 0 := by
    intro δ hδ
    obtain ⟨hroot, hzero⟩ := hSorth δ hδ
    refine ⟨hroot, ?_⟩
    rw [show -γ = (-1 : ℤ) • γ by simp, iform_smul_right, hzero, mul_zero]
  have hR : rootSpan τ K (kernelRoots (rootCharHom (a * thetaDiag γ t))) ≤
      rootSpan τ K (kernelRoots (rootCharHom a)) := by
    refine iSup₂_le fun δ hδ => ?_
    exact le_iSup₂_of_le δ (hsubset hδ) le_rfl
  have hleA : torusGroup τ K ⊔
        rootSpan τ K (kernelRoots (rootCharHom (a * thetaDiag γ t))) ≤
      torusGroup τ K ⊔ rootSpan τ K (kernelRoots (rootCharHom a)) :=
    sup_le le_sup_left (hR.trans le_sup_right)
  have hleB : torusGroup τ K ⊔
        rootSpan τ K (kernelRoots (rootCharHom (a * thetaDiag γ t))) ≤
      Subgroup.normalizer (rootSubgroup τ K γ : Set (ModGL τ K)) :=
    sup_le hTγ (rootSpan_le_normalizer_rootSubgroup_of_forall_iform_eq_zero
      (K := K) hτ hγ hSorth)
  have hleC : torusGroup τ K ⊔
        rootSpan τ K (kernelRoots (rootCharHom (a * thetaDiag γ t))) ≤
      Subgroup.normalizer (rootSubgroup τ K (-γ) : Set (ModGL τ K)) :=
    sup_le hTneg (rootSpan_le_normalizer_rootSubgroup_of_forall_iform_eq_zero
      (K := K) hτ (IsRoot.neg hγ) hSorth_neg)
  exact le_inf (le_inf hleA hleB) hleC

theorem smul_eq_self_of_mem_rootCharStabilizer_mul_thetaDiag
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {a : Fin τ.rank → Kˣ}
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {t : Kˣ}
    (ht : ∀ n : ℕ, 0 < n → n ≤ 4 → t ^ n ≠ 1) {w : WeylGroup τ}
    (hw : w ∈ rootCharStabilizer a)
    (hwb : w ∈ rootCharStabilizer (a * thetaDiag γ t)) :
    w • γ = γ := by
  have hfix : ∀ x : Fin τ.rank → ℤ, t ^ iform γ (w • x) = t ^ iform γ x := by
    intro x
    have ha := hw x
    have hb := hwb x
    simp only [rootChar_mul, rootChar_thetaDiag] at hb
    rw [ha] at hb
    exact mul_left_cancel hb
  have hsingle : ∀ j : Fin τ.rank,
      iform (w • γ) (Pi.single j 1) = iform γ (Pi.single j 1) := by
    intro j
    have h1 := hfix (w⁻¹ • (Pi.single j 1 : Fin τ.rank → ℤ))
    rw [smul_inv_smul] at h1
    have hA : |iform γ (Pi.single j 1)| ≤ 2 :=
      abs_iform_le_two_of_isRoot_simplyLaced hτ hγ (isRoot_single τ j)
    have hB : |iform γ (w⁻¹ • Pi.single j 1)| ≤ 2 :=
      abs_iform_le_two_of_isRoot_simplyLaced hτ hγ
        (IsRoot.smul (isRoot_single τ j) w⁻¹)
    have hEq2 := eq_of_zpow_eq_zpow_of_abs_le hA hB ht h1
    have h2 := iform_smul w γ (w⁻¹ • Pi.single j 1)
    rw [smul_inv_smul] at h2
    exact h2.trans hEq2.symm
  by_contra hne
  have hx : w • γ - γ ≠ 0 := sub_ne_zero.mpr hne
  have hpos := iform_self_pos hx
  have hz : iform (w • γ - γ) (w • γ - γ) = 0 := by
    rw [CFSG.ClassicalInvolution.ModelFacts.Levi.iform_eq_sum_single]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [iform_sub_left, hsingle j, sub_self, mul_zero]
  exact (ne_of_gt hpos) hz

theorem mem_torusGroup_sup_rootSpan_kernelRoots_mul_thetaDiag_of_mem_toralCentralizer
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (a : Fin τ.rank → Kˣ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (t : Kˣ)
    (ht : ∀ n : ℕ, 0 < n → n ≤ 4 → t ^ n ≠ 1)
    (hind : ∀ (v : Fin τ.rank → ℤ) (n : ℤ), rootChar a v * t ^ n = 1 → t ^ n = 1)
    {g : ModGL τ K}
    (hgC : g ∈ torusGroup τ K ⊔ rootSpan τ K (kernelRoots (rootCharHom a)))
    (hgT : g ∈ toralCentralizer τ K (a * thetaDiag γ t)) :
    g ∈ torusGroup τ K ⊔ rootSpan τ K (kernelRoots (rootCharHom (a * thetaDiag γ t))) := by
  have hker := kernelRoots_rootCharHom_mul_thetaDiag hτ a hγ t ht hind
  obtain ⟨w', hw'stab, h', hh'T, u', hu'ker, v', hv'ker, hg'⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors τ K (a * thetaDiag γ t)).1 g hgT
  have hsplit : g ∈ ((torusGroup τ K ⊔
      rootSpan τ K (kernelRoots (rootCharHom a)) : Subgroup (ModGL τ K)) :
        Set (ModGL τ K)) := hgC
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (torusGroup τ K)
    (rootSpan τ K (kernelRoots (rootCharHom a)))
    (torusGroup_le_normalizer_rootSpan (K := K) (S := kernelRoots (rootCharHom a))
      (fun α hα => hα.1))] at hsplit
  obtain ⟨h₀, hh₀, s, hs, hgs⟩ := hsplit
  obtain ⟨w, hw, h, hh, u, hu, v, hv, hs_eq⟩ :=
    exists_kernelRoots_bruhat_factor (rootCharHom a) hs
  have hu_pos : u ∈ posUnipotent τ K :=
    rootSpan_mono (S := posRoots (kernelRoots (rootCharHom a)))
      (T := {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α})
      (fun α hα => ⟨hα.1.1, hα.2⟩) hu
  have hvI : v ∈ rootSpan τ K (inversionSet w) :=
    rootSpan_mono (S := {α : Fin τ.rank → ℤ |
        α ∈ posRoots (kernelRoots (rootCharHom a)) ∧ height (w • α) < 0})
      (T := inversionSet w)
      (fun α hα => ⟨hα.1.1.1, hα.1.2, IsRoot.smul hα.1.1.1 w, hα.2⟩) hv
  have hu'pos : u' ∈ posUnipotent τ K :=
    rootSpan_mono (S := rootCharKernel (a * thetaDiag γ t) ∩
        {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α})
      (T := {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α})
      (fun α hα => ⟨hα.1.1, hα.2.2⟩) hu'ker
  have hv'I : v' ∈ rootSpan τ K (inversionSet w') :=
    rootSpan_mono (S := rootCharKernel (a * thetaDiag γ t) ∩ inversionSet w')
      (T := inversionSet w') (fun α hα => hα.2) hv'ker
  have hEq : (h₀ * h) * u * canonicalRep (coxeterSystem τ) K w * v =
      h' * u' * canonicalRep (coxeterSystem τ) K w' * v' := by
    have h1 : (h₀ * h) * u * canonicalRep (coxeterSystem τ) K w * v = h₀ * s := by
      rw [hs_eq]
      group
    exact h1.trans (hgs.trans hg')
  obtain ⟨hww, -, -, -⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors τ K (a * thetaDiag γ t)).2.1
      w w' (h₀ * h) h' u u' v v' (mul_mem hh₀ hh) hh'T hu_pos hu'pos hvI hv'I hEq
  have hwstab_b : w ∈ rootCharStabilizer (a * thetaDiag γ t) := by
    rw [hww]
    exact hw'stab
  rw [← hww] at hg'
  have hwstab : w ∈ rootCharStabilizer a :=
    mem_rootCharStabilizer_of_mem_closure_rootReflection hw
  have hwγ : w • γ = γ :=
    smul_eq_self_of_mem_rootCharStabilizer_mul_thetaDiag hτ hγ ht hwstab hwstab_b
  have hwK2 : w ∈ Subgroup.closure (rootReflection '' {δ | δ ∈ kernelRoots (rootCharHom a)
      ∧ iform δ γ = 0}) :=
    mem_closure_rootReflection_orthogonal_of_smul_eq (rootCharHom a) hw hwγ
  rw [← hker] at hwK2
  have hn : canonicalRep (coxeterSystem τ) K w ∈
      torusGroup τ K ⊔ rootSpan τ K (kernelRoots (rootCharHom (a * thetaDiag γ t))) :=
    canonicalRep_mem_torus_sup_rootSpan_kernelRoots
      (χ := rootCharHom (a * thetaDiag γ t)) hwK2
  have hu'C : u' ∈ torusGroup τ K ⊔
      rootSpan τ K (kernelRoots (rootCharHom (a * thetaDiag γ t))) := by
    rw [kernelRoots_rootCharHom]
    exact Subgroup.mem_sup_right (rootSpan_mono (fun α hα => hα.1) hu'ker)
  have hv'C : v' ∈ torusGroup τ K ⊔
      rootSpan τ K (kernelRoots (rootCharHom (a * thetaDiag γ t))) := by
    rw [kernelRoots_rootCharHom]
    exact Subgroup.mem_sup_right (rootSpan_mono (fun α hα => hα.1) hv'ker)
  have h'C : h' ∈ torusGroup τ K ⊔
      rootSpan τ K (kernelRoots (rootCharHom (a * thetaDiag γ t))) :=
    Subgroup.mem_sup_left hh'T
  rw [hg']
  exact mul_mem (mul_mem (mul_mem h'C hu'C) hn) hv'C

theorem torusGroup_sup_rootSpan_kernelRoots_inf_normalizer_eq
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (a : Fin τ.rank → Kˣ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (t : Kˣ)
    (ht : ∀ n : ℕ, 0 < n → n ≤ 4 → t ^ n ≠ 1)
    (hind : ∀ (v : Fin τ.rank → ℤ) (n : ℤ), rootChar a v * t ^ n = 1 → t ^ n = 1) :
    (torusGroup τ K ⊔ rootSpan τ K (kernelRoots (rootCharHom a))) ⊓
        Subgroup.normalizer (rootSubgroup τ K γ : Set (ModGL τ K)) ⊓
        Subgroup.normalizer (rootSubgroup τ K (-γ) : Set (ModGL τ K)) =
      torusGroup τ K ⊔ rootSpan τ K (kernelRoots (rootCharHom (a * thetaDiag γ t))) := by
  refine le_antisymm ?_ (torusGroup_sup_rootSpan_kernelRoots_mul_thetaDiag_le_inf_normalizer
    hτ a hγ t ht hind)
  intro g hg
  have hgC : g ∈ torusGroup τ K ⊔ rootSpan τ K (kernelRoots (rootCharHom a)) := hg.1.1
  have hgNγ : g ∈ Subgroup.normalizer (rootSubgroup τ K γ : Set (ModGL τ K)) := hg.1.2
  have hgNneg : g ∈ Subgroup.normalizer (rootSubgroup τ K (-γ) : Set (ModGL τ K)) := hg.2
  have hgAdj : g ∈ adjointGroup τ K :=
    torus_sup_rootSpan_le_adjointGroup (kernelRoots (rootCharHom a)) hgC
  have hgTa : g ∈ toralCentralizer τ K a := by
    have h := hgC
    rw [kernelRoots_rootCharHom] at h
    exact toralRootGroup_le a h
  have hconja := (mem_toralCentralizer.1 hgTa).2
  have hKA := adjointGroup_inf_normalizer_le_centralizer_thetaDiag hτ hγ t
    ⟨⟨hgAdj, hgNγ⟩, hgNneg⟩
  have hconjθ : rootDiagUnit τ (thetaDiag γ t) * g * (rootDiagUnit τ (thetaDiag γ t))⁻¹ = g :=
    (conj_eq_iff_mem_centralizer (a := thetaDiag γ t) (g := g)).2 hKA
  have hcommb : g ∈ toralCentralizer τ K (a * thetaDiag γ t) := by
    rw [mem_toralCentralizer]
    refine ⟨hgAdj, ?_⟩
    rw [rootDiagUnit_mul]
    calc
      (rootDiagUnit τ a * rootDiagUnit τ (thetaDiag γ t)) * g *
          (rootDiagUnit τ a * rootDiagUnit τ (thetaDiag γ t))⁻¹
          = rootDiagUnit τ a *
              (rootDiagUnit τ (thetaDiag γ t) * g *
                (rootDiagUnit τ (thetaDiag γ t))⁻¹) *
              (rootDiagUnit τ a)⁻¹ := by group
      _ = rootDiagUnit τ a * g * (rootDiagUnit τ a)⁻¹ := by rw [hconjθ]
      _ = g := hconja
  exact mem_torusGroup_sup_rootSpan_kernelRoots_mul_thetaDiag_of_mem_toralCentralizer
    hτ a hγ t ht hind hgC hcommb

end CFSG.StandardType.LieKnownR2.ExcPos

end
