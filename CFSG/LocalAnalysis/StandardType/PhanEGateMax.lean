module

public import CFSG.LocalAnalysis.StandardType.PhanEGateFormula
public import CFSG.LocalAnalysis.StandardType.PhanEReduction

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Gate

open CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type} {M : CoxeterMatrix ι} {W : Type} [Group W] {cs : CoxeterSystem M W}
  {C : Type} {δ : C → C → W} {w₀ : W} {t : C → C} {J I : Set ι} {a x₁ c x : C}

theorem isFlipInvolution_of_isSphericalFlip (ht : IsSphericalFlip cs δ w₀ t) :
    IsFlipInvolution cs δ w₀ t :=
  ⟨ht.invol, ht.dist⟩

@[expose] def IsFar (cs : CoxeterSystem M W) (δ : C → C → W) (I J : Set ι) (x₁ c : C) : Prop :=
  δ (resProj cs δ I x₁ c) c = longest cs I * longest cs J

private lemma p9uGX_finite_parabolic_of_subset {I J : Set ι} (hIJ : I ⊆ J)
    [Finite (cs.parabolic J)] : Finite (cs.parabolic I) :=
  Finite.of_injective (Subgroup.inclusion (cs.parabolic_mono hIJ))
    (Subgroup.inclusion_injective (cs.parabolic_mono hIJ))

private lemma p9uGX_length_longest_mul_add {I J : Set ι} (hIJ : I ⊆ J)
    [Finite (cs.parabolic J)] :
    cs.length (longest cs I * longest cs J) + cs.length (longest cs I) =
      cs.length (longest cs J) := by
  haveI : Finite (cs.parabolic I) := p9uGX_finite_parabolic_of_subset hIJ
  have hI := isLongest_longest (cs := cs) I
  have hJ := isLongest_longest (cs := cs) J
  have hmem : longest cs I ∈ cs.parabolic J := cs.parabolic_mono hIJ hI.1
  have h := hJ.length_inv_mul hmem
  rwa [hI.inv_eq] at h

private lemma p9uGX_length_simple_mul_longest_mul_add {I J : Set ι} (hIJ : I ⊆ J)
    [Finite (cs.parabolic J)] {i : ι} (hi : i ∈ I) :
    cs.length (cs.simple i * (longest cs I * longest cs J)) =
      cs.length (longest cs I * longest cs J) + 1 := by
  haveI : Finite (cs.parabolic I) := p9uGX_finite_parabolic_of_subset hIJ
  have hI := isLongest_longest (cs := cs) I
  have hJ := isLongest_longest (cs := cs) J
  have hmem : longest cs I * cs.simple i ∈ cs.parabolic J :=
    mul_mem (cs.parabolic_mono hIJ hI.1) (cs.simple_mem_parabolic (hIJ hi))
  have h := hJ.length_inv_mul (x := longest cs I * cs.simple i) hmem
  have hxinv : (longest cs I * cs.simple i)⁻¹ * longest cs J =
      cs.simple i * (longest cs I * longest cs J) := by
    rw [mul_inv_rev, cs.inv_simple, hI.inv_eq, mul_assoc]
  rw [hxinv] at h
  have hdesc : cs.length (longest cs I * cs.simple i) + 1 = cs.length (longest cs I) :=
    (cs.isRightDescent_iff).mp (hI.isRightDescent hi)
  have hU := p9uGX_length_longest_mul_add (cs := cs) (I := I) (J := J) hIJ
  omega

private lemma p9uGX_exists_mem_residue_dist_eq_longest {I : Set ι} {x₁ x : C}
    [Finite (cs.parabolic I)] (hB : IsWeylDistanceBuilding cs δ)
    (hx : x ∈ residue cs δ I x₁) :
    ∃ z ∈ residue cs δ I x₁, δ x z = longest cs I := by
  obtain ⟨z, hz, hdist⟩ := exists_mem_residue_dist_eq_mul hB x x (isLongest_longest I).1
  refine ⟨z, ?_, ?_⟩
  · rwa [residue_eq_of_mem hB hx] at hz
  · rw [hdist, hB.eq_one_self, one_mul]

theorem length_dist_resProj_add_le [Finite (cs.parabolic J)] (hB : IsWeylDistanceBuilding cs δ)
    (hIJ : I ⊆ J) (hx₁ : x₁ ∈ residue cs δ J a) (hc : c ∈ residue cs δ J a) :
    cs.length (δ c (resProj cs δ I x₁ c)) + cs.length (longest cs I) ≤
      cs.length (longest cs J) := by
  haveI : Finite (cs.parabolic I) := p9uGX_finite_parabolic_of_subset hIJ
  obtain ⟨z, hzI, hzdist⟩ :=
    p9uGX_exists_mem_residue_dist_eq_longest (cs := cs) (I := I) (x₁ := x₁)
      hB (resProj_mem hB I x₁ c)
  have hzJ : z ∈ residue cs δ J a := by
    have h : z ∈ residue cs δ J x₁ := residue_mono hIJ x₁ hzI
    rwa [residue_eq_of_mem hB hx₁] at h
  have hgate := IsProjection.gate hB (isProjection_resProj hB I x₁ c) hzI
  have hpar : δ c z ∈ cs.parabolic J := mem_parabolic_of_mem_residue hB hc hzJ
  have hle : cs.length (δ c z) ≤ cs.length (longest cs J) :=
    (isLongest_longest J).2 _ hpar
  rw [hgate.2, hzdist] at hle
  exact hle

theorem exists_isFar [Finite (cs.parabolic J)] (hB : IsWeylDistanceBuilding cs δ)
    (hIJ : I ⊆ J) (hx₁ : x₁ ∈ residue cs δ J a) (hx : x ∈ residue cs δ I x₁) :
    ∃ c ∈ residue cs δ J a, resProj cs δ I x₁ c = x ∧ IsFar cs δ I J x₁ c := by
  haveI : Finite (cs.parabolic I) := p9uGX_finite_parabolic_of_subset hIJ
  have hxJ : x ∈ residue cs δ J a := by
    have h := residue_mono hIJ x₁ hx
    rwa [residue_eq_of_mem hB hx₁] at h
  have hu : longest cs I * longest cs J ∈ cs.parabolic J :=
    mul_mem (cs.parabolic_mono hIJ (isLongest_longest I).1) (isLongest_longest J).1
  obtain ⟨c, hc, hcdist⟩ := exists_mem_residue_dist_eq_mul hB x x hu
  have hcR : c ∈ residue cs δ J a := by
    rw [← residue_eq_of_mem hB hxJ]
    exact hc
  have hxc : δ x c = longest cs I * longest cs J := by
    rw [hcdist, hB.eq_one_self, one_mul]
  have hpcore : resProj cs δ I x₁ c ∈ residue cs δ I x₁ := resProj_mem hB I x₁ c
  have hgate := IsProjection.gate hB (isProjection_resProj hB I x₁ c) hx
  set v : W := δ x (resProj cs δ I x₁ c) with hv
  have hvc : δ x c = v * δ (resProj cs δ I x₁ c) c := by
    rw [hv]
    rw [dist_inv hB c x, hgate.1, mul_inv_rev,
      ← dist_inv hB (resProj cs δ I x₁ c) x, ← dist_inv hB c (resProj cs δ I x₁ c)]
  have hvc_len : cs.length (δ x c) =
      cs.length v + cs.length (δ (resProj cs δ I x₁ c) c) := by
    rw [dist_inv hB c x, cs.length_inv, hgate.2, hv,
      dist_inv hB (resProj cs δ I x₁ c) x, cs.length_inv,
      dist_inv hB c (resProj cs δ I x₁ c), cs.length_inv]
    omega
  have hv1 : v = 1 := by
    by_contra hvne
    have hvpar : v ∈ cs.parabolic I := by
      rw [hv]
      exact mem_parabolic_of_mem_residue hB hx hpcore
    obtain ⟨i, hiI, hdesc⟩ :=
      cs.exists_rightDescent_mem_of_mem_parabolic_of_ne_one (inv_mem hvpar) (inv_ne_one.mpr hvne)
    have hleft : cs.IsLeftDescent v i := (cs.isRightDescent_inv_iff).mp hdesc
    have hleftlen : cs.length (cs.simple i * v) + 1 = cs.length v :=
      (cs.isLeftDescent_iff).mp hleft
    have hstep := p9uGX_length_simple_mul_longest_mul_add (cs := cs) (I := I) (J := J) hIJ hiI
    have hlen2 : cs.length (longest cs I * longest cs J) =
        cs.length v + cs.length (δ (resProj cs δ I x₁ c) c) := by
      rw [← hxc, hvc_len]
    have heq : (cs.simple i * v) * δ (resProj cs δ I x₁ c) c =
        cs.simple i * (longest cs I * longest cs J) := by
      rw [mul_assoc, ← hvc, hxc]
    have hle : cs.length (cs.simple i * (longest cs I * longest cs J)) ≤
        cs.length (cs.simple i * v) + cs.length (δ (resProj cs δ I x₁ c) c) := by
      rw [← heq]
      exact cs.length_mul_le (cs.simple i * v) (δ (resProj cs δ I x₁ c) c)
    omega
  have hpc : resProj cs δ I x₁ c = x := by
    have hxone : δ x (resProj cs δ I x₁ c) = 1 := by
      rw [← hv]
      exact hv1
    exact ((hB.eq_one_iff x (resProj cs δ I x₁ c)).mp hxone).symm
  refine ⟨c, hcR, hpc, ?_⟩
  unfold IsFar
  rw [hpc, hxc]

theorem isFar_iff_length_add_eq [Finite (cs.parabolic J)] (hB : IsWeylDistanceBuilding cs δ)
    (hIJ : I ⊆ J) (hx₁ : x₁ ∈ residue cs δ J a) (hc : c ∈ residue cs δ J a) :
    IsFar cs δ I J x₁ c ↔
      cs.length (δ c (resProj cs δ I x₁ c)) + cs.length (longest cs I) =
        cs.length (longest cs J) := by
  haveI : Finite (cs.parabolic I) := p9uGX_finite_parabolic_of_subset hIJ
  obtain ⟨z, hzI, hzdist⟩ :=
    p9uGX_exists_mem_residue_dist_eq_longest (cs := cs) (I := I) (x₁ := x₁)
      hB (resProj_mem hB I x₁ c)
  have hzJ : z ∈ residue cs δ J a := by
    have h : z ∈ residue cs δ J x₁ := residue_mono hIJ x₁ hzI
    rwa [residue_eq_of_mem hB hx₁] at h
  have hgate := IsProjection.gate hB (isProjection_resProj hB I x₁ c) hzI
  have hlen : cs.length (δ c (resProj cs δ I x₁ c)) + cs.length (longest cs I) =
      cs.length (δ c z) := by rw [hgate.2, hzdist]
  constructor
  · intro hfar
    unfold IsFar at hfar
    have h1 : cs.length (δ c (resProj cs δ I x₁ c)) =
        cs.length (longest cs I * longest cs J) := by
      rw [dist_inv hB (resProj cs δ I x₁ c) c, hfar, cs.length_inv]
    rw [h1]
    exact p9uGX_length_longest_mul_add hIJ
  · intro hlen_eq
    have hlenz : cs.length (δ c z) = cs.length (longest cs J) := by
      rw [← hlen, hlen_eq]
    have hcz : δ c z = longest cs J :=
      (IsLongest.unique ⟨mem_parabolic_of_mem_residue hB hc hzJ,
        fun v hv => by rw [hlenz]; exact (isLongest_longest J).2 v hv⟩
        (isLongest_longest J))
    have hmul : δ c (resProj cs δ I x₁ c) * longest cs I = longest cs J := by
      rw [← hzdist, ← hgate.1, hcz]
    have hIself : longest cs I * longest cs I = 1 := (isLongest_longest I).mul_self
    have hcp : δ c (resProj cs δ I x₁ c) = longest cs J * longest cs I := by
      have h2 := congrArg (· * longest cs I) hmul
      rwa [mul_assoc, hIself, mul_one] at h2
    unfold IsFar
    rw [dist_inv hB c (resProj cs δ I x₁ c), hcp, mul_inv_rev,
      (isLongest_longest I).inv_eq, (isLongest_longest J).inv_eq]

theorem flipMaxSet_eq [Finite (cs.parabolic J)] (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsFlipInvolution cs δ w₀ t) (hI : flipCore cs δ t J a = residue cs δ I x₁)
    (hIJ : I ⊆ J) :
    flipMaxSet cs δ t J a =
      {c | c ∈ residue cs δ J a ∧ IsFar cs δ I J x₁ c ∧
        resProj cs δ I x₁ c ∈ flipPsiMax cs δ t J a} := by
  haveI hIfin : Finite (cs.parabolic I) := p9uGX_finite_parabolic_of_subset hIJ
  have hx₁R : x₁ ∈ residue cs δ J a := by
    have hmem : x₁ ∈ flipCore cs δ t J a := by rw [hI]; exact self_mem_residue I x₁
    simp only [flipCore, projSet, Set.mem_image] at hmem
    rcases hmem with ⟨y, -, hy⟩
    rw [← hy]
    exact resProj_mem hB J a y
  ext c
  simp only [flipMaxSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hcR, hcmax⟩
    set xg : C := resProj cs δ I x₁ c with hxg
    have hxgcore : xg ∈ flipCore cs δ t J a := by
      rw [hxg, hI]
      exact resProj_mem hB I x₁ c
    obtain ⟨y₀, hy₀max⟩ := flipPsiMax_nonempty (cs := cs) (δ := δ) (t := t) (J := J)
      (a := a) hB hw ht
    have hy₀core : y₀ ∈ flipCore cs δ t J a := hy₀max.1
    obtain ⟨c', hc'R, hc'gate, hc'far⟩ :=
      exists_isFar (cs := cs) (δ := δ) (J := J) (I := I) (a := a) (x₁ := x₁) (x := y₀)
        hB hIJ hx₁R (by rw [← hI]; exact hy₀core)
    have hform_c := length_dist_flip hB hw ht hI hcR (isProjection_resProj hB I x₁ c)
    rw [← hxg] at hform_c
    have hform_c' := length_dist_flip hB hw ht hI hc'R (isProjection_resProj hB I x₁ c')
    rw [hc'gate] at hform_c'
    have hA : cs.length (δ (flipPsi cs δ t J a xg) (t xg)) =
        cs.length (δ (flipPsi cs δ t J a y₀) (t y₀)) := by
      rw [dist_flipPsi_const hB hw ht hxgcore hy₀core]
    have hle1 : cs.length (δ c xg) + cs.length (longest cs I) ≤
        cs.length (longest cs J) := by
      have h := length_dist_resProj_add_le (cs := cs) (δ := δ) (J := J) (I := I)
        (a := a) (x₁ := x₁) (c := c) hB hIJ hx₁R hcR
      rwa [← hxg] at h
    have hfar' : cs.length (δ c' y₀) + cs.length (longest cs I) =
        cs.length (longest cs J) := by
      have h := (isFar_iff_length_add_eq (cs := cs) (δ := δ) (J := J) (I := I) (a := a)
        (x₁ := x₁) (c := c') hB hIJ hx₁R hc'R).mp hc'far
      rwa [hc'gate] at h
    have hEmax : cs.length (δ xg (flipPsi cs δ t J a xg)) ≤
        cs.length (δ y₀ (flipPsi cs δ t J a y₀)) := hy₀max.2 xg hxgcore
    have hmax' : cs.length (δ c' (t c')) ≤ cs.length (δ c (t c)) := hcmax c' hc'R
    have hlx : cs.length (δ c xg) = cs.length (δ c' y₀) := by omega
    have hlxx : cs.length (δ xg (flipPsi cs δ t J a xg)) =
        cs.length (δ y₀ (flipPsi cs δ t J a y₀)) := by omega
    have hlen_eq : cs.length (δ c xg) + cs.length (longest cs I) =
        cs.length (longest cs J) := by omega
    refine ⟨hcR, (isFar_iff_length_add_eq (cs := cs) (δ := δ) (J := J) (I := I) (a := a)
      (x₁ := x₁) (c := c) hB hIJ hx₁R hcR).mpr hlen_eq, ?_⟩
    exact ⟨hxgcore, fun y hy => by rw [hlxx]; exact hy₀max.2 y hy⟩
  · rintro ⟨hcR, hfar, hxmax⟩
    refine ⟨hcR, fun z hz => ?_⟩
    set xg : C := resProj cs δ I x₁ c with hxg
    set xz : C := resProj cs δ I x₁ z with hxz
    have hxgcore : xg ∈ flipCore cs δ t J a := by rw [hxg]; exact hxmax.1
    have hxzcore : xz ∈ flipCore cs δ t J a := by
      rw [hxz, hI]
      exact resProj_mem hB I x₁ z
    have hform_c := length_dist_flip hB hw ht hI hcR (isProjection_resProj hB I x₁ c)
    rw [← hxg] at hform_c
    have hform_z := length_dist_flip hB hw ht hI hz (isProjection_resProj hB I x₁ z)
    rw [← hxz] at hform_z
    have hlx_eq : cs.length (δ c xg) + cs.length (longest cs I) =
        cs.length (longest cs J) := by
      have h := (isFar_iff_length_add_eq (cs := cs) (δ := δ) (J := J) (I := I) (a := a)
        (x₁ := x₁) (c := c) hB hIJ hx₁R hcR).mp hfar
      rwa [← hxg] at h
    have hle_z : cs.length (δ z xz) + cs.length (longest cs I) ≤
        cs.length (longest cs J) := by
      have h := length_dist_resProj_add_le (cs := cs) (δ := δ) (J := J) (I := I)
        (a := a) (x₁ := x₁) (c := z) hB hIJ hx₁R hz
      rwa [← hxz] at h
    have hA : cs.length (δ (flipPsi cs δ t J a xz) (t xz)) =
        cs.length (δ (flipPsi cs δ t J a xg) (t xg)) := by
      rw [dist_flipPsi_const hB hw ht hxzcore hxgcore]
    have hEmax : cs.length (δ xz (flipPsi cs δ t J a xz)) ≤
        cs.length (δ xg (flipPsi cs δ t J a xg)) := by
      simpa only [← hxg] using hxmax.2 xz hxzcore
    omega

end CFSG.ClassicalInvolution.Phan.PhanE.Gate

end
