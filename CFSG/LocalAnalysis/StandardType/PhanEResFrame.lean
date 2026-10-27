module

public import CFSG.LocalAnalysis.StandardType.PhanEResLevi
public import CFSG.LocalAnalysis.StandardType.PhanEStdBuildingData
public import CFSG.LocalAnalysis.StandardType.PhanEGateType
public import CFSG.LocalAnalysis.StandardType.PhanEGateMax
public import CFSG.LocalAnalysis.StandardType.PhanEChevConj

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Res

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan.PhanE
  CFSG.AGLEmbeddingD2.ParabLevi
open scoped Pointwise

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
  {w₀ : W} (F : FrobData D n H w₀)
  (hw₀ : IsLongest (coxeterMatrix D.isFiniteType).toCoxeterSystem Set.univ w₀)
  (hsq : ∀ i, n i * n i = 1)

private theorem hmbRF_flipType_eq_op_image (J : Set (Fin D.rank)) :
    Gate.flipType (cs) w₀ J = F.op '' J := by
  ext k
  constructor
  · rintro ⟨j, hj, hjk⟩
    refine ⟨j, hj, CoxeterSystem.simple_injective (cs) ?_⟩
    rw [← hjk, F.hop j]
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, F.hop j⟩

include hct hext in
private theorem hmbRF_smul_residue (k : K) (J : Set (Fin D.rank))
    (x : K ⧸ borel D H) :
    k • residue (cs) (stdδ hct) J x = residue (cs) (stdδ hct) J (k • x) := by
  have hB := stdBuilding hct hext
  ext z
  constructor
  · rintro ⟨z', hz', rfl⟩
    rw [mem_residue_iff_mem_parabolic hB] at hz' ⊢
    rwa [stdδ_smul hct hext k x z']
  · intro hz
    refine ⟨k⁻¹ • z, ?_, smul_inv_smul k z⟩
    rw [mem_residue_iff_mem_parabolic hB] at hz ⊢
    have h := stdδ_smul hct hext k x (k⁻¹ • z)
    rw [smul_inv_smul] at h
    rwa [← h]

private theorem hmbRF_weylAction_of_conj_simple {J : Set (Fin D.rank)} {v : W} {k m : Fin D.rank}
    (hmin : (cs).IsMinimalDoubleCosetRep J (Gate.flipType (cs) w₀ J) v)
    (hmJ : m ∈ J) (hconj : v * (cs).simple k * v⁻¹ = (cs).simple m) :
    weylAction D.isFiniteType v (Pi.single k 1) = Pi.single m 1 := by
  have hneg : weylAction D.isFiniteType ((cs).simple m)
      (weylAction D.isFiniteType v (Pi.single k 1)) =
      -weylAction D.isFiniteType v (Pi.single k 1) := by
    conv_lhs => rw [← hconj]
    rw [weylAction_mul_apply, weylAction_mul_apply,
      weylAction_inv_apply_apply D.isFiniteType v (Pi.single k 1),
      weylAction_simple_single, map_neg (weylAction D.isFiniteType v)]
  have hsupp : ∀ l ∉ ({m} : Set (Fin D.rank)),
      weylAction D.isFiniteType v (Pi.single k 1) l = 0 := by
    intro l hl
    have hpoint : reflection D.cartan m (weylAction D.isFiniteType v (Pi.single k 1)) =
        -weylAction D.isFiniteType v (Pi.single k 1) := by
      rw [← weylAction_simple D.isFiniteType m]
      exact hneg
    have hkl := congrFun hpoint l
    rw [reflection_apply_coroot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_of_ne (show l ≠ m by simpa using hl), mul_zero, sub_zero, Pi.neg_apply] at hkl
    omega
  have hleft : ∀ m' ∈ ({m} : Set (Fin D.rank)), ¬ (cs).IsLeftDescent v m' := by
    intro m' hm'
    rw [Set.mem_singleton_iff] at hm'
    rw [hm']
    exact ((CoxeterSystem.isMinimalDoubleCosetRep_iff cs).mp hmin).2 m hmJ
  obtain ⟨m', hm', hspec⟩ :=
    (isCTRootSystem D.isFiniteType D.divisible).eq_single ({m} : Set (Fin D.rank)) v k hleft hsupp
  rw [Set.mem_singleton_iff] at hm'
  rw [hm'] at hspec
  exact hspec

private theorem hmbRF_map_leviM (hφL : ∀ i, (rankOne D.rootGroup i).map F.φ ≤
    rankOne D.rootGroup (F.op i)) (I : Set (Fin D.rank)) :
    (leviM D I).map F.φ ≤ leviM D (F.op '' I) := by
  rw [leviM]
  simp only [Subgroup.map_iSup]
  refine iSup₂_le fun i hi => ?_
  exact (hφL i).trans (rankOne_le_leviM ⟨i, hi, rfl⟩)

include hext hw₀ hsq in
theorem exists_frame (hred : D.divisible = ∅)
    (hφL : ∀ i, (rankOne D.rootGroup i).map F.φ ≤ rankOne D.rootGroup (F.op i))
    (J : Set (Fin D.rank)) (a : K ⧸ borel D H) :
    ∃ (g : K) (v : W) (I : Set (Fin D.rank)) (π : Fin D.rank → Fin D.rank) (t₀ l₀ : K),
      I ⊆ J ∧
      residue (cs) (stdδ hct) J a = residue (cs) (stdδ hct) J ((g : K) : K ⧸ borel D H) ∧
      Gate.flipCore (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) J a =
        residue (cs) (stdδ hct) I ((g : K) : K ⧸ borel D H) ∧
      (∀ i ∈ I, π i ∈ I ∧ π (π i) = i ∧
        weylAction D.isFiniteType v (Pi.single (F.op i) 1) = Pi.single (π i) 1) ∧
      t₀ ∈ ⨆ k, H k ∧ l₀ ∈ leviM D I ∧
      ∀ l ∈ leviM D I,
        Gate.flipPsi (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) J a
            ((g * l : K) : K ⧸ borel D H) =
          ((g * t₀ * l₀ * (nrep hct v * F.φ l * (nrep hct v)⁻¹) : K) : K ⧸ borel D H) := by
  classical
  have hB : IsWeylDistanceBuilding (cs) (stdδ hct) := stdBuilding hct hext
  have hw : ∀ w : W, (cs).length (w * w₀) + (cs).length w = (cs).length w₀ :=
    fun w => hw₀.length_mul_left (q2nPE_mem_parabolic_univ w)
  have hn₀ : ∀ g : K, g⁻¹ * (nrep hct w₀ * F.φ (nrep hct w₀)) * g ∈ borel D H := by
    intro g
    rw [nrep_mul_phi_self hct F hext hw₀ hsq]
    simp
  have ht : Gate.IsFlipInvolution (cs) (stdδ hct) w₀ (stdFlip F (nrep hct w₀)) :=
    ⟨stdFlip_invol F hext hw₀ (nrep hct w₀) hn₀,
      stdFlip_δ hct F hext hw₀ (nrep hct w₀)⟩
  let t : K ⧸ borel D H → K ⧸ borel D H := stdFlip F (nrep hct w₀)
  let x₁ : K ⧸ borel D H := resProj (cs) (stdδ hct) J a (t a)
  have hx₁_core : x₁ ∈ Gate.flipCore (cs) (stdδ hct) t J a := by
    rw [Gate.flipCore, Gate.projSet]
    exact ⟨t a, ⟨a, self_mem_residue J a, rfl⟩, rfl⟩
  let x : K ⧸ borel D H := Gate.flipPsi (cs) (stdδ hct) t J a x₁
  set y : K ⧸ borel D H := t x₁ with hy_def
  have hcp : Gate.IsClosestPair (cs) (stdδ hct) J (Gate.flipType (cs) w₀ J) a (t a) x y :=
    Gate.isClosestPair_flipPsi hB hw ht hx₁_core
  have hmin : (cs).IsMinimalDoubleCosetRep J (Gate.flipType (cs) w₀ J) (stdδ hct x y) :=
    Gate.IsClosestPair.isMinimalDoubleCosetRep hB hcp
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective x
  obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective y
  have hcell : g₀⁻¹ * h ∈ bruhatCell hct (stdδ hct x y) := by
    rw [← stdδ_mk_eq_iff hct hext g₀ h (stdδ hct x y)]
    rw [hg₀, hh]
  obtain ⟨b, hb, u, hu, hbu⟩ := exists_eq_mul_nrep_mul hct hext hcell
  have huB : u ∈ borel D H :=
    posUnipotent_le_borel (inversionUnipotent_le_posUnipotent (stdδ hct x y) hu)
  set g : K := g₀ * b with hg_def
  have hgb : ((g₀ * b : K) : K ⧸ borel D H) = (g₀ : K ⧸ borel D H) := by
    rw [QuotientGroup.eq]
    rw [show (g₀ * b)⁻¹ * g₀ = b⁻¹ by group]
    exact inv_mem hb
  have hgx : ((g : K) : K ⧸ borel D H) = x := by
    rw [hg_def]
    rw [hgb]
    exact hg₀
  have hh_eq : h = g * nrep hct (stdδ hct x y) * u := by
    have h1 := congrArg (fun z => g₀ * z) hbu
    rw [mul_inv_cancel_left] at h1
    rw [h1, hg_def]; group
  have hh_quot : ((h : K) : K ⧸ borel D H) =
      ((g * nrep hct (stdδ hct x y) : K) : K ⧸ borel D H) := by
    rw [hh_eq]
    rw [QuotientGroup.eq]
    rw [show (g * nrep hct (stdδ hct x y) * u : K)⁻¹ *
        (g * nrep hct (stdδ hct x y)) = u⁻¹ by group]
    exact inv_mem huB
  have hh_gv : y = ((g * nrep hct (stdδ hct x y) : K) : K ⧸ borel D H) :=
    hh.symm.trans hh_quot
  set I : Set (Fin D.rank) := Gate.flipCoreType (cs) J (stdδ hct x y * w₀) with hI_def
  set π : Fin D.rank → Fin D.rank :=
    Gate.flipTypeMap (cs) (stdδ hct) w₀ t J a x₁ with hπ_def
  have hpi : Gate.flipPi (cs) (stdδ hct) w₀ t J a x₁ = stdδ hct x y * w₀ := rfl
  have hIfc : Gate.flipCore (cs) (stdδ hct) t J a = residue (cs) (stdδ hct) I x₁ := by
    have hcore := Gate.flipCore_eq_residue_flipCoreType hB hw ht hx₁_core
    rw [hpi] at hcore
    exact hcore
  have hxI : x ∈ residue (cs) (stdδ hct) I x₁ := by
    rw [← hIfc]
    exact Gate.flipPsi_mem hB hw ht hx₁_core
  have hIJ : I ⊆ J := Gate.flipCoreType_subset (cs) J (stdδ hct x y * w₀)
  set p₀ : K := (g * nrep hct (stdδ hct x y))⁻¹ * (nrep hct w₀ * F.φ g) with hp₀_def
  have hp₀_eq : ((p₀ : K) : K ⧸ borel D H) =
      (g * nrep hct (stdδ hct x y))⁻¹ • t ((g : K) : K ⧸ borel D H) := by
    rw [show t ((g : K) : K ⧸ borel D H) =
        stdFlip F (nrep hct w₀) ((g : K) : K ⧸ borel D H) from rfl, stdFlip_mk]
    rw [show nrep hct w₀ * F.φ g = (g * nrep hct (stdδ hct x y)) * p₀ by
      rw [hp₀_def]; group]
    rw [MulAction.Quotient.smul_coe, smul_eq_mul,
      show (g * nrep hct (stdδ hct x y))⁻¹ *
        ((g * nrep hct (stdδ hct x y)) * p₀) = p₀ by group]
  have htx_op : t x ∈ residue (cs) (stdδ hct) (F.op '' I) (t x₁) := by
    have h1 : t x ∈ residue (cs) (stdδ hct) (Gate.flipType (cs) w₀ I) (t x₁) := by
      rw [← Gate.image_residue_flip hw ht I x₁]
      exact ⟨x, hxI, rfl⟩
    rwa [hmbRF_flipType_eq_op_image F I] at h1
  have hone : (g * nrep hct (stdδ hct x y))⁻¹ • t x₁ = ((1 : K) : K ⧸ borel D H) := by
    have hy_gv : t x₁ = ((g * nrep hct (stdδ hct x y) : K) : K ⧸ borel D H) := by
      rw [← hy_def]; exact hh_gv
    rw [hy_gv, MulAction.Quotient.smul_coe, smul_eq_mul,
      show (g * nrep hct (stdδ hct x y))⁻¹ * (g * nrep hct (stdδ hct x y)) = 1 by group]
  have hp₀ : ((p₀ : K) : K ⧸ borel D H) ∈
      residue (cs) (stdδ hct) (F.op '' I) ((1 : K) : K ⧸ borel D H) := by
    rw [hp₀_eq]
    have h1 : t ((g : K) : K ⧸ borel D H) = t x := by rw [hgx]
    rw [h1, ← hone]
    rw [← hmbRF_smul_residue (hct := hct) (hext := hext) (g * nrep hct (stdδ hct x y))⁻¹
      (F.op '' I) (t x₁)]
    exact ⟨t x, htx_op, rfl⟩
  obtain ⟨t₁, ht₁, m₁, hm₁, hlevi⟩ := exists_parabolic_levi hct hext (F.op '' I) hp₀
  have hspec : ∀ i ∈ I, π i ∈ I ∧
      Gate.flipPi (cs) (stdδ hct) w₀ t J a x₁ * (cs).simple i *
        (Gate.flipPi (cs) (stdδ hct) w₀ t J a x₁)⁻¹ = (cs).simple (π i) := by
    intro i hi
    exact Gate.flipTypeMap_spec hB hw ht hIfc hi
  have hπinv : ∀ i ∈ I, π (π i) = i := by
    intro i hi
    exact Gate.flipTypeMap_flipTypeMap hB hw ht hIfc hi
  have hpi : Gate.flipPi (cs) (stdδ hct) w₀ t J a x₁ = stdδ hct x y * w₀ := rfl
  have hroot : ∀ i ∈ I, weylAction D.isFiniteType (stdδ hct x y) (Pi.single (F.op i) 1) =
      Pi.single (π i) 1 := by
    intro i hi
    have hconj := (hspec i hi).2
    rw [hpi] at hconj
    have hconj' : (stdδ hct x y) * (cs).simple (F.op i) * (stdδ hct x y)⁻¹ =
        (cs).simple (π i) := by
      have hw0 : w₀⁻¹ = w₀ := hw₀.inv_eq
      calc (stdδ hct x y) * (cs).simple (F.op i) * (stdδ hct x y)⁻¹
          = (stdδ hct x y) * (w₀ * (cs).simple i * w₀) * (stdδ hct x y)⁻¹ := by
            rw [F.hop i]
        _ = ((stdδ hct x y) * w₀) * (cs).simple i * ((stdδ hct x y) * w₀)⁻¹ := by
            rw [mul_inv_rev, hw0]; group
        _ = (cs).simple (π i) := hconj
    exact hmbRF_weylAction_of_conj_simple hmin (hIJ (hspec i hi).1) hconj'
  set t₀ : K := nrep hct (stdδ hct x y) * t₁ * (nrep hct (stdδ hct x y))⁻¹ with ht₀_def
  set l₀ : K := nrep hct (stdδ hct x y) * m₁ * (nrep hct (stdδ hct x y))⁻¹ with hl₀_def
  have ht₀ : t₀ ∈ ⨆ k, H k := by
    rw [ht₀_def]
    exact conj_mem_iSup_of_mem_weylN hct (nrep_mem_weylN hct (stdδ hct x y)) ht₁
  have hvI : ∀ i ∈ F.op '' I, ∃ j ∈ I,
      weylAction D.isFiniteType (stdδ hct x y) (Pi.single i 1) = Pi.single j 1 := by
    rintro i ⟨i', hi', rfl⟩
    exact ⟨π i', (hspec i' hi').1, hroot i' hi'⟩
  have hl₀ : l₀ ∈ leviM D I := by
    rw [hl₀_def]
    exact nrep_conj_mem_leviM hct hvI hm₁
  refine ⟨g, stdδ hct x y, I, π, t₀, l₀, hIJ, ?_, ?_, ?_, ht₀, hl₀, ?_⟩
  ·
    rw [hgx]
    exact (residue_eq_of_mem hB hcp.1).symm
  ·
    rw [hIfc, hgx]
    exact (residue_eq_of_mem hB hxI).symm
  ·
    intro i hi
    exact ⟨(hspec i hi).1, hπinv i hi, hroot i hi⟩
  ·
    intro l hl
    have hφl : F.φ l ∈ leviM D (F.op '' I) :=
      hmbRF_map_leviM F hφL I (Subgroup.mem_map_of_mem F.φ hl)
    set lam : K := t₁ * m₁ * F.φ l with hlam_def
    have hlevi_l : ((p₀ * F.φ l : K) : K ⧸ borel D H) = ((lam : K) : K ⧸ borel D H) := by
      rw [hlam_def]; exact hlevi (F.φ l) hφl
    have htgl : t ((g * l : K) : K ⧸ borel D H) =
        ((g * nrep hct (stdδ hct x y) * lam : K) : K ⧸ borel D H) := by
      rw [show t = stdFlip F (nrep hct w₀) from rfl, stdFlip_mk, map_mul]
      rw [QuotientGroup.eq]
      have hkey : (nrep hct w₀ * (F.φ g * F.φ l))⁻¹ *
          (g * nrep hct (stdδ hct x y) * lam) = (p₀ * F.φ l)⁻¹ * lam := by
        have h2 : nrep hct w₀ * (F.φ g * F.φ l) =
            (g * nrep hct (stdδ hct x y)) * (p₀ * F.φ l) := by
          rw [← mul_assoc, show nrep hct w₀ * F.φ g =
            (g * nrep hct (stdδ hct x y)) * p₀ by rw [hp₀_def]; group]
          group
        rw [h2]; group
      rw [hkey]
      exact QuotientGroup.eq.mp hlevi_l
    have hm₀ : nrep hct (stdδ hct x y) * F.φ l * (nrep hct (stdδ hct x y))⁻¹ ∈
        leviM D I := nrep_conj_mem_leviM hct hvI hφl
    set k : K := g * (nrep hct (stdδ hct x y) * lam * (nrep hct (stdδ hct x y))⁻¹) * g⁻¹
      with hk_def
    have hky : k • y = ((g * nrep hct (stdδ hct x y) * lam : K) : K ⧸ borel D H) := by
      conv_lhs => rw [hh_gv]
      rw [MulAction.Quotient.smul_coe, smul_eq_mul]
      congr 1
      rw [hk_def]; group
    have hkx : k • ((g : K) : K ⧸ borel D H) =
        ((g * (nrep hct (stdδ hct x y) * lam * (nrep hct (stdδ hct x y))⁻¹) : K) :
          K ⧸ borel D H) := by
      rw [MulAction.Quotient.smul_coe, smul_eq_mul]
      congr 1
      rw [hk_def]; group
    have hres0 : residue (cs) (stdδ hct) J ((g : K) : K ⧸ borel D H) =
        residue (cs) (stdδ hct) J a := by
      rw [hgx]
      exact residue_eq_of_mem hB hcp.1
    have ht₀B : t₀ ∈ borel D H := iSup_le_borel ht₀
    have hm' : t₀ * (l₀ * (nrep hct (stdδ hct x y) * F.φ l *
        (nrep hct (stdδ hct x y))⁻¹)) * t₀⁻¹ ∈ leviM D I :=
      ((Subgroup.mem_normalizer_iff.mp (torus_le_normalizer_leviM hct ht₀)
        (l₀ * (nrep hct (stdδ hct x y) * F.φ l *
          (nrep hct (stdδ hct x y))⁻¹))).mp (mul_mem hl₀ hm₀))
    have hk_eq : k • ((g : K) : K ⧸ borel D H) =
        ((g * (t₀ * (l₀ * (nrep hct (stdδ hct x y) * F.φ l *
          (nrep hct (stdδ hct x y))⁻¹)) * t₀⁻¹) : K) : K ⧸ borel D H) := by
      rw [hkx]
      rw [show g * (nrep hct (stdδ hct x y) * lam * (nrep hct (stdδ hct x y))⁻¹) =
          g * (t₀ * (l₀ * (nrep hct (stdδ hct x y) * F.φ l *
            (nrep hct (stdδ hct x y))⁻¹))) by
        rw [hlam_def, ht₀_def, hl₀_def]; group]
      rw [show g * (t₀ * (l₀ * (nrep hct (stdδ hct x y) * F.φ l *
            (nrep hct (stdδ hct x y))⁻¹))) =
          (g * (t₀ * (l₀ * (nrep hct (stdδ hct x y) * F.φ l *
            (nrep hct (stdδ hct x y))⁻¹)) * t₀⁻¹)) * t₀ by group, QuotientGroup.eq]
      rw [show ((g * (t₀ * (l₀ * (nrep hct (stdδ hct x y) * F.φ l *
            (nrep hct (stdδ hct x y))⁻¹)) * t₀⁻¹)) * t₀)⁻¹ *
          (g * (t₀ * (l₀ * (nrep hct (stdδ hct x y) * F.φ l *
            (nrep hct (stdδ hct x y))⁻¹)) * t₀⁻¹)) = t₀⁻¹ by group]
      exact inv_mem ht₀B
    have hleviM_mono : leviM D I ≤ leviM D J :=
      iSup₂_le fun i hi => rankOne_le_leviM (hIJ hi)
    have hmm : k • ((g : K) : K ⧸ borel D H) ∈ residue (cs) (stdδ hct) J a := by
      rw [hk_eq]
      exact hres0 ▸ mk_mul_mem_residue_of_mem_leviM hct hext g (hleviM_mono hm')
    have hresJ : residue (cs) (stdδ hct) J (k • ((g : K) : K ⧸ borel D H)) =
        residue (cs) (stdδ hct) J a := residue_eq_of_mem hB hmm
    have hresproj_k : resProj (cs) (stdδ hct) J a (k • y) =
        resProj (cs) (stdδ hct) J (k • ((g : K) : K ⧸ borel D H)) (k • y) := by
      have hp := isProjection_resProj hB J a (k • y)
      rw [← hresJ] at hp
      exact (resProj_eq hB hp).symm
    have hresproj_g : resProj (cs) (stdδ hct) J ((g : K) : K ⧸ borel D H) y = x := by
      have hp := isProjection_resProj hB J a y
      rw [← hres0] at hp
      rw [resProj_eq hB hp, Gate.IsClosestPair.eq_resProj_left hB hcp]
    calc Gate.flipPsi (cs) (stdδ hct) t J a ((g * l : K) : K ⧸ borel D H)
        = resProj (cs) (stdδ hct) J a (t ((g * l : K) : K ⧸ borel D H)) := rfl
      _ = resProj (cs) (stdδ hct) J a (k • y) := by rw [htgl, hky]
      _ = resProj (cs) (stdδ hct) J (k • ((g : K) : K ⧸ borel D H)) (k • y) :=
            hresproj_k
      _ = k • resProj (cs) (stdδ hct) J ((g : K) : K ⧸ borel D H) y :=
            resProj_smul hct hext J k ((g : K) : K ⧸ borel D H) y
      _ = k • x := by rw [hresproj_g]
      _ = ((g * t₀ * l₀ * (nrep hct (stdδ hct x y) * F.φ l *
            (nrep hct (stdδ hct x y))⁻¹) : K) : K ⧸ borel D H) := by
            conv_lhs => rw [← hgx]
            rw [hkx]
            congr 1
            rw [hlam_def, ht₀_def, hl₀_def]; group


variable {Fld : Type} [Field Fld] (M : ChevModel2 D n H Fld) {θ : Fld →+* Fld}
  (PC : M.PhiCompat F θ)

include PC in
theorem phi_rankOne_le (i : Fin D.rank) :
    (rankOne D.rootGroup i).map F.φ ≤ rankOne D.rootGroup (F.op i) := by
  have hΦ := isCTRootSystem D.isFiniteType D.divisible
  have hpos : Pi.single i 1 ∈ D.roots := hΦ.single_mem i
  have hneg : -Pi.single i 1 ∈ D.roots := by
    have h := hΦ.smul_mem ((cs).simple i) _ hpos
    rwa [hΦ.simple_single] at h
  have hpos' : Pi.single (F.op i) 1 ∈ D.roots := hΦ.single_mem (F.op i)
  have hneg' : -Pi.single (F.op i) 1 ∈ D.roots := by
    have h := hΦ.smul_mem ((cs).simple (F.op i)) _ hpos'
    rwa [hΦ.simple_single] at h
  rw [show rankOne D.rootGroup i =
      D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1) from rfl, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := (M.x_mem (Pi.single i 1) hpos x).mp hx
    rw [PC.phi_x (Pi.single i 1) hpos c, PC.ρ_single i]
    exact Subgroup.mem_sup_left ((M.x_mem (Pi.single (F.op i) 1) hpos' _).mpr ⟨θ c, rfl⟩)
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := (M.x_mem (-Pi.single i 1) hneg x).mp hx
    have hconj : M.x (-Pi.single i 1) c = n i * M.x (Pi.single i 1) c * (n i)⁻¹ := by
      rw [M.nm_conj i (Pi.single i 1) hpos c, hΦ.simple_single]
    rw [hconj, map_mul, map_mul, map_inv, F.n_map i, PC.phi_x (Pi.single i 1) hpos c,
      PC.ρ_single i, M.nm_conj (F.op i) (Pi.single (F.op i) 1) hpos' (θ c), hΦ.simple_single]
    exact Subgroup.mem_sup_right ((M.x_mem (-Pi.single (F.op i) 1) hneg' _).mpr ⟨θ c, rfl⟩)

include PC in
theorem kappa_single {v : W} {i j : Fin D.rank}
    (hv : weylAction D.isFiniteType v (Pi.single (F.op i) 1) = Pi.single j 1) (c : Fld) :
    nrep hct v * F.φ (M.x (Pi.single i 1) c) * (nrep hct v)⁻¹ = M.x (Pi.single j 1) (θ c) := by
  have hΦ := isCTRootSystem D.isFiniteType D.divisible
  rw [PC.phi_x (Pi.single i 1) (hΦ.single_mem i) c, PC.ρ_single i,
    M.nrep_conj hct v (hΦ.single_mem (F.op i)) (θ c), hv]

include PC in
theorem kappa_neg_single {v : W} {i j : Fin D.rank}
    (hv : weylAction D.isFiniteType v (Pi.single (F.op i) 1) = Pi.single j 1) (c : Fld) :
    nrep hct v * F.φ (M.x (-Pi.single i 1) c) * (nrep hct v)⁻¹ = M.x (-Pi.single j 1) (θ c) := by
  have hΦ := isCTRootSystem D.isFiniteType D.divisible
  have hpos : Pi.single i 1 ∈ D.roots := hΦ.single_mem i
  have hpos' : Pi.single (F.op i) 1 ∈ D.roots := hΦ.single_mem (F.op i)
  have hneg' : -Pi.single (F.op i) 1 ∈ D.roots := by
    have h := hΦ.smul_mem ((cs).simple (F.op i)) _ hpos'
    rwa [hΦ.simple_single] at h
  have hconj : M.x (-Pi.single i 1) c = n i * M.x (Pi.single i 1) c * (n i)⁻¹ := by
    rw [M.nm_conj i (Pi.single i 1) hpos c, hΦ.simple_single]
  rw [hconj, map_mul, map_mul, map_inv, F.n_map i, PC.phi_x (Pi.single i 1) hpos c,
    PC.ρ_single i, M.nm_conj (F.op i) (Pi.single (F.op i) 1) hpos' (θ c), hΦ.simple_single,
    M.nrep_conj hct v hneg' (θ c), map_neg, hv]

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
