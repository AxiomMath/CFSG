module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagDist
public import CFSG.LocalAnalysis.StandardType.PhanEGateMax

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE

variable {ι : Type} {M : CoxeterMatrix ι} {W : Type} [Group W] {cs : CoxeterSystem M W}
  {C : Type} {δ : C → C → W} {w₀ : W} {t : C → C} {J I : Set ι} {a x₁ : C}

private lemma p9uFA_finite_parabolic_of_subset {I J : Set ι} (hIJ : I ⊆ J)
    [Finite (cs.parabolic J)] : Finite (cs.parabolic I) :=
  Finite.of_injective (Subgroup.inclusion (cs.parabolic_mono hIJ))
    (Subgroup.inclusion_injective (cs.parabolic_mono hIJ))

private lemma p9uFA_cdist_restrict_eq (hB : IsWeylDistanceBuilding cs δ) (J : Set ι) (a : C)
    (y z : ↥(residue cs δ J a)) :
    cdist ((buildingOver cs δ J).restrict (residue cs δ J a)) y z =
      cs.length (δ (y : C) (z : C)) := by
  simpa using (length_dist_eq_cdist hB J a y.2 z.2).symm

private lemma p9uFA_mem_image_subtype_val_iff {α : Type*} {P : α → Prop} {S : Set (Subtype P)}
    {x : α} (hx : P x) :
    x ∈ Subtype.val '' S ↔ (⟨x, hx⟩ : Subtype P) ∈ S := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hy' : y ∈ S := hy
    have h : y = ⟨x, hx⟩ := Subtype.ext hxy
    rwa [h] at hy'
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem length_dist_le_length_longest [Finite (cs.parabolic I)]
    (hB : IsWeylDistanceBuilding cs δ) {x y z : C} (hy : y ∈ residue cs δ I x)
    (hz : z ∈ residue cs δ I x) :
    cs.length (δ y z) ≤ cs.length (longest cs I) := by
  exact (isLongest_longest (cs := cs) I).2 _ (mem_parabolic_of_mem_residue hB hy hz)

theorem exists_mem_residue_dist_eq_longest [Finite (cs.parabolic I)]
    (hB : IsWeylDistanceBuilding cs δ) (x : C) :
    ∃ z ∈ residue cs δ I x, δ x z = longest cs I := by
  obtain ⟨z, hz, hdist⟩ :=
    Gate.exists_mem_residue_dist_eq_mul (cs := cs) (δ := δ) hB x x (K := I)
      (isLongest_longest (cs := cs) I).1
  refine ⟨z, hz, ?_⟩
  rw [hdist, hB.eq_one_self, one_mul]

theorem isGateAt_restrict_iff (hB : IsWeylDistanceBuilding cs δ) (hIJ : I ⊆ J)
    (hx₁ : x₁ ∈ residue cs δ J a) (y g : ↥(residue cs δ J a)) :
    IsGateAt ((buildingOver cs δ J).restrict (residue cs δ J a))
        {c | (c : C) ∈ residue cs δ I x₁} y g ↔
      (g : C) = resProj cs δ I x₁ y := by
  constructor
  · intro h
    have hproj : IsProjection cs δ (residue cs δ I x₁) (y : C) (g : C) := by
      refine isProjection_of_gate hB h.1 (fun q hq => ?_)
      have hqJ : q ∈ residue cs δ J a := by
        have h' : q ∈ residue cs δ J x₁ := residue_mono hIJ x₁ hq
        rwa [residue_eq_of_mem hB hx₁] at h'
      have hh := h.2 ⟨q, hqJ⟩ hq
      rw [p9uFA_cdist_restrict_eq hB J a y ⟨q, hqJ⟩,
        p9uFA_cdist_restrict_eq hB J a y g,
        p9uFA_cdist_restrict_eq hB J a g ⟨q, hqJ⟩] at hh
      exact hh
    exact (resProj_eq hB hproj).symm
  · intro hg
    refine ⟨?_, ?_⟩
    · rw [Set.mem_setOf_eq, hg]
      exact resProj_mem hB I x₁ (y : C)
    · intro z hz
      rw [p9uFA_cdist_restrict_eq hB J a y z, p9uFA_cdist_restrict_eq hB J a y g,
        p9uFA_cdist_restrict_eq hB J a g z]
      have hgate := (IsProjection.gate hB (isProjection_resProj hB I x₁ (y : C))
        (q := (z : C)) hz).2
      rw [← hg] at hgate
      exact hgate

theorem mem_intrSet_restrict_iff (hB : IsWeylDistanceBuilding cs δ) (hIJ : I ⊆ J)
    (hx₁ : x₁ ∈ residue cs δ J a) (ψ' : ↥(residue cs δ J a) → ↥(residue cs δ J a)) (D : ℕ)
    (y : ↥(residue cs δ J a)) :
    y ∈ IntrSet ((buildingOver cs δ J).restrict (residue cs δ J a))
        {c | (c : C) ∈ residue cs δ I x₁} ψ' D ↔
      ∃ g : ↥(residue cs δ J a), (g : C) = resProj cs δ I x₁ y ∧
        cs.length (δ y (ψ' g)) = D := by
  rw [IntrSet]
  constructor
  · rintro ⟨g, hg, hgate, hdist⟩
    refine ⟨g, (isGateAt_restrict_iff hB hIJ hx₁ y g).mp hgate, ?_⟩
    rw [p9uFA_cdist_restrict_eq hB J a y (ψ' g)] at hdist
    exact hdist
  · rintro ⟨g, hg, hdist⟩
    refine ⟨g, ?_, (isGateAt_restrict_iff hB hIJ hx₁ y g).mpr hg, ?_⟩
    · rw [Set.mem_setOf_eq, hg]
      exact resProj_mem hB I x₁ (y : C)
    · rw [p9uFA_cdist_restrict_eq hB J a y (ψ' g)]
      exact hdist

private lemma p9uFA_isFar_and_max_iff [Finite (cs.parabolic J)]
    (hB : IsWeylDistanceBuilding cs δ) (hIJ : I ⊆ J) (hx₁ : x₁ ∈ residue cs δ J a)
    {ψ : C → C} (hψ : ∀ x ∈ residue cs δ I x₁, ψ x ∈ residue cs δ I x₁)
    (hex : ∃ x ∈ residue cs δ I x₁, cs.length (δ x (ψ x)) = cs.length (longest cs I))
    {c : C} (hc : c ∈ residue cs δ J a) :
    (Gate.IsFar cs δ I J x₁ c ∧
      resProj cs δ I x₁ c ∈ {x | x ∈ residue cs δ I x₁ ∧
        ∀ y ∈ residue cs δ I x₁, cs.length (δ y (ψ y)) ≤ cs.length (δ x (ψ x))}) ↔
      cs.length (δ c (ψ (resProj cs δ I x₁ c))) = cs.length (longest cs J) := by
  haveI : Finite (cs.parabolic I) := p9uFA_finite_parabolic_of_subset hIJ
  have hxgm : resProj cs δ I x₁ c ∈ residue cs δ I x₁ := resProj_mem hB I x₁ c
  have hψm : ψ (resProj cs δ I x₁ c) ∈ residue cs δ I (resProj cs δ I x₁ c) := by
    rw [residue_eq_of_mem hB hxgm]
    exact hψ _ hxgm
  have hb_le : cs.length (δ (resProj cs δ I x₁ c) (ψ (resProj cs δ I x₁ c))) ≤
      cs.length (longest cs I) :=
    length_dist_le_length_longest (cs := cs) (δ := δ) (I := I)
      (x := resProj cs δ I x₁ c) hB (self_mem_residue I _) hψm
  have hle : cs.length (δ c (resProj cs δ I x₁ c)) + cs.length (longest cs I) ≤
      cs.length (longest cs J) :=
    Gate.length_dist_resProj_add_le (cs := cs) (δ := δ) (J := J) (I := I)
      (a := a) (x₁ := x₁) (c := c) hB hIJ hx₁ hc
  have hgate : cs.length (δ c (ψ (resProj cs δ I x₁ c))) =
      cs.length (δ c (resProj cs δ I x₁ c)) +
        cs.length (δ (resProj cs δ I x₁ c) (ψ (resProj cs δ I x₁ c))) :=
    (IsProjection.gate hB (isProjection_resProj hB I x₁ c) (hψ _ hxgm)).2
  have hisFar : Gate.IsFar cs δ I J x₁ c ↔
      cs.length (δ c (resProj cs δ I x₁ c)) + cs.length (longest cs I) =
        cs.length (longest cs J) :=
    Gate.isFar_iff_length_add_eq (cs := cs) (δ := δ) (J := J) (I := I) (a := a)
      (x₁ := x₁) (c := c) hB hIJ hx₁ hc
  constructor
  · rintro ⟨hfar, hxmax⟩
    simp only [Set.mem_setOf_eq] at hxmax
    have hbA : cs.length (δ (resProj cs δ I x₁ c) (ψ (resProj cs δ I x₁ c))) =
        cs.length (longest cs I) := by
      obtain ⟨x₀, hx₀, hx₀eq⟩ := hex
      have := hxmax.2 x₀ hx₀
      omega
    have haA : cs.length (δ c (resProj cs δ I x₁ c)) + cs.length (longest cs I) =
        cs.length (longest cs J) := hisFar.mp hfar
    rw [hgate]
    omega
  · intro heq
    rw [hgate] at heq
    have hbA : cs.length (δ (resProj cs δ I x₁ c) (ψ (resProj cs δ I x₁ c))) =
        cs.length (longest cs I) := by omega
    have haA : cs.length (δ c (resProj cs δ I x₁ c)) + cs.length (longest cs I) =
        cs.length (longest cs J) := by omega
    refine ⟨hisFar.mpr haA, ?_⟩
    show resProj cs δ I x₁ c ∈ residue cs δ I x₁ ∧
      ∀ y ∈ residue cs δ I x₁,
        cs.length (δ y (ψ y)) ≤ cs.length (δ (resProj cs δ I x₁ c) (ψ (resProj cs δ I x₁ c)))
    refine ⟨hxgm, fun y hy => ?_⟩
    have hψy : ψ y ∈ residue cs δ I y := by
      rw [residue_eq_of_mem hB hy]
      exact hψ y hy
    have := length_dist_le_length_longest (cs := cs) (δ := δ) (I := I) (x := y)
      hB (self_mem_residue I y) hψy
    omega

theorem setOf_isFar_eq_image_intrSet [Finite (cs.parabolic J)]
    (hB : IsWeylDistanceBuilding cs δ) (hIJ : I ⊆ J) (hx₁ : x₁ ∈ residue cs δ J a)
    {ψ : C → C} (hψ : ∀ x ∈ residue cs δ I x₁, ψ x ∈ residue cs δ I x₁)
    (hex : ∃ x ∈ residue cs δ I x₁, cs.length (δ x (ψ x)) = cs.length (longest cs I))
    {ψ' : ↥(residue cs δ J a) → ↥(residue cs δ J a)}
    (hψ' : ∀ c : ↥(residue cs δ J a), (c : C) ∈ residue cs δ I x₁ → (ψ' c : C) = ψ c) :
    {c | c ∈ residue cs δ J a ∧ Gate.IsFar cs δ I J x₁ c ∧
        resProj cs δ I x₁ c ∈ {x | x ∈ residue cs δ I x₁ ∧
          ∀ y ∈ residue cs δ I x₁, cs.length (δ y (ψ y)) ≤ cs.length (δ x (ψ x))}} =
      Subtype.val '' IntrSet ((buildingOver cs δ J).restrict (residue cs δ J a))
        {c | (c : C) ∈ residue cs δ I x₁} ψ' (cs.length (longest cs J)) := by
  haveI : Finite (cs.parabolic I) := p9uFA_finite_parabolic_of_subset hIJ
  ext c
  by_cases hcR : c ∈ residue cs δ J a
  · have hxR : resProj cs δ I x₁ c ∈ residue cs δ J a := by
      have h : resProj cs δ I x₁ c ∈ residue cs δ J x₁ :=
        residue_mono hIJ x₁ (resProj_mem hB I x₁ c)
      rwa [residue_eq_of_mem hB hx₁] at h
    have hLHS : c ∈ {c | c ∈ residue cs δ J a ∧ Gate.IsFar cs δ I J x₁ c ∧
        resProj cs δ I x₁ c ∈ {x | x ∈ residue cs δ I x₁ ∧
          ∀ y ∈ residue cs δ I x₁, cs.length (δ y (ψ y)) ≤
            cs.length (δ x (ψ x))}} ↔
        (Gate.IsFar cs δ I J x₁ c ∧
          resProj cs δ I x₁ c ∈ {x | x ∈ residue cs δ I x₁ ∧
            ∀ y ∈ residue cs δ I x₁, cs.length (δ y (ψ y)) ≤
              cs.length (δ x (ψ x))}) := by
      simp only [Set.mem_setOf_eq, hcR, true_and]
    have hexists :
        (∃ g : ↥(residue cs δ J a), (g : C) = resProj cs δ I x₁ c ∧
          cs.length (δ c (ψ' g)) = cs.length (longest cs J)) ↔
        cs.length (δ c (ψ (resProj cs δ I x₁ c))) = cs.length (longest cs J) := by
      constructor
      · rintro ⟨g, hg, hgd⟩
        have hgI : (g : C) ∈ residue cs δ I x₁ := by
          rw [hg]
          exact resProj_mem hB I x₁ c
        rw [← hg, ← hψ' g hgI]
        exact hgd
      · intro hd
        refine ⟨⟨resProj cs δ I x₁ c, hxR⟩, rfl, ?_⟩
        rw [hψ' ⟨resProj cs δ I x₁ c, hxR⟩ (resProj_mem hB I x₁ c)]
        exact hd
    rw [hLHS, p9uFA_mem_image_subtype_val_iff hcR,
      mem_intrSet_restrict_iff hB hIJ hx₁ ψ' (cs.length (longest cs J)) ⟨c, hcR⟩]
    exact (p9uFA_isFar_and_max_iff (cs := cs) (δ := δ) (J := J) (I := I) (a := a)
      (x₁ := x₁) hB hIJ hx₁ hψ hex hcR).trans hexists.symm
  · constructor
    · intro hc
      exfalso
      simp only [Set.mem_setOf_eq] at hc
      exact hcR hc.1
    · intro hc
      exfalso
      rw [Set.mem_image] at hc
      obtain ⟨d, -, hd⟩ := hc
      exact hcR (hd ▸ d.2)

theorem flipMaxSet_eq_image_intrSet [Finite (cs.parabolic J)] (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : Gate.IsFlipInvolution cs δ w₀ t) (hI : Gate.flipCore cs δ t J a = residue cs δ I x₁)
    (hIJ : I ⊆ J)
    (hex : ∃ x ∈ residue cs δ I x₁,
      cs.length (δ x (Gate.flipPsi cs δ t J a x)) = cs.length (longest cs I))
    {ψ' : ↥(residue cs δ J a) → ↥(residue cs δ J a)}
    (hψ' : ∀ c : ↥(residue cs δ J a), (c : C) ∈ residue cs δ I x₁ →
      (ψ' c : C) = Gate.flipPsi cs δ t J a c) :
    flipMaxSet cs δ t J a =
      Subtype.val '' IntrSet ((buildingOver cs δ J).restrict (residue cs δ J a))
        {c | (c : C) ∈ residue cs δ I x₁} ψ' (cs.length (longest cs J)) := by
  haveI : Finite (cs.parabolic I) := p9uFA_finite_parabolic_of_subset hIJ
  have hx₁R : x₁ ∈ residue cs δ J a := by
    have hmem : x₁ ∈ Gate.flipCore cs δ t J a := by
      rw [hI]
      exact self_mem_residue I x₁
    simp only [Gate.flipCore, Gate.projSet, Set.mem_image] at hmem
    rcases hmem with ⟨y, -, hy⟩
    rw [← hy]
    exact resProj_mem hB J a y
  have hψ : ∀ x ∈ residue cs δ I x₁, Gate.flipPsi cs δ t J a x ∈ residue cs δ I x₁ := by
    intro x hx
    have h := Gate.flipPsi_mem (cs := cs) (δ := δ) (t := t) (w₀ := w₀) (J := J) (a := a)
      hB hw ht (by rwa [hI])
    rwa [hI] at h
  rw [Gate.flipMaxSet_eq (cs := cs) (δ := δ) (t := t) (w₀ := w₀) (J := J) (I := I) (a := a)
    (x₁ := x₁) hB hw ht hI hIJ]
  simpa only [Gate.flipPsiMax, hI] using
    setOf_isFar_eq_image_intrSet (cs := cs) (δ := δ) (J := J) (I := I) (a := a) (x₁ := x₁)
      hB hIJ hx₁R hψ hex hψ'

section Chart

variable {ι' C' : Type} {Y : ChamberSystem ι' C'}
  (Θ : ChamberIso ((buildingOver cs δ J).restrict (residue cs δ J a)) Y) {R₀' : Set C'}
  {ψ' : C' → C'}

theorem mem_flipMaxSet_iff_of_chamberIso [Finite (cs.parabolic J)]
    (hB : IsWeylDistanceBuilding cs δ) (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : Gate.IsFlipInvolution cs δ w₀ t) (hI : Gate.flipCore cs δ t J a = residue cs δ I x₁)
    (hIJ : I ⊆ J)
    (hex : ∃ x ∈ residue cs δ I x₁,
      cs.length (δ x (Gate.flipPsi cs δ t J a x)) = cs.length (longest cs I))
    (hR₀ : ∀ c : ↥(residue cs δ J a), (c : C) ∈ residue cs δ I x₁ ↔ Θ.Φ c ∈ R₀')
    (hψ : ∀ c c' : ↥(residue cs δ J a), (c : C) ∈ residue cs δ I x₁ →
      (c' : C) = Gate.flipPsi cs δ t J a c → Θ.Φ c' = ψ' (Θ.Φ c))
    (c : ↥(residue cs δ J a)) :
    (c : C) ∈ flipMaxSet cs δ t J a ↔ Θ.Φ c ∈ IntrSet Y R₀' ψ' (cs.length (longest cs J)) := by
  haveI : Finite (cs.parabolic I) := p9uFA_finite_parabolic_of_subset hIJ
  let ψR : ↥(residue cs δ J a) → ↥(residue cs δ J a) :=
    fun x => ⟨Gate.flipPsi cs δ t J a x, resProj_mem hB J a (t x)⟩
  have hψR : ∀ x : ↥(residue cs δ J a), (x : C) ∈ residue cs δ I x₁ →
      (ψR x : C) = Gate.flipPsi cs δ t J a x := fun _ _ => rfl
  have hmax := flipMaxSet_eq_image_intrSet (cs := cs) (δ := δ) (t := t) (w₀ := w₀) (J := J)
    (I := I) (a := a) (x₁ := x₁) hB hw ht hI hIJ hex (ψ' := ψR) hψR
  have hthis : (c : C) ∈ flipMaxSet cs δ t J a ↔
      c ∈ IntrSet ((buildingOver cs δ J).restrict (residue cs δ J a))
        {x | (x : C) ∈ residue cs δ I x₁} ψR (cs.length (longest cs J)) := by
    constructor
    · intro hc
      have hc' : (c : C) ∈ Subtype.val '' IntrSet
          ((buildingOver cs δ J).restrict (residue cs δ J a))
          {x | (x : C) ∈ residue cs δ I x₁} ψR (cs.length (longest cs J)) := by
        rwa [← hmax]
      exact (p9uFA_mem_image_subtype_val_iff c.2).mp hc'
    · intro hc
      have hc' : (c : C) ∈ Subtype.val '' IntrSet
          ((buildingOver cs δ J).restrict (residue cs δ J a))
          {x | (x : C) ∈ residue cs δ I x₁} ψR (cs.length (longest cs J)) :=
        (p9uFA_mem_image_subtype_val_iff c.2).mpr hc
      rwa [hmax]
  have himg : Θ.Φ '' {x : ↥(residue cs δ J a) | (x : C) ∈ residue cs δ I x₁} = R₀' := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (hR₀ g).mp hg
    · intro hx
      refine ⟨Θ.Φ.symm x, ?_, Θ.Φ.apply_symm_apply x⟩
      have : Θ.Φ (Θ.Φ.symm x) ∈ R₀' := by rwa [Θ.Φ.apply_symm_apply]
      exact (hR₀ (Θ.Φ.symm x)).mpr this
  have hpsi : ∀ g ∈ {x : ↥(residue cs δ J a) | (x : C) ∈ residue cs δ I x₁},
      Θ.Φ (ψR g) = ψ' (Θ.Φ g) := by
    intro g hg
    exact hψ g (ψR g) hg rfl
  have hiso := IntrSet_chamberIso Θ (hψ := hpsi) (cs.length (longest cs J)) c
  rw [himg] at hiso
  exact hthis.trans hiso.symm

theorem exists_length_flipPsi_eq_longest_of_chamberIso [Finite (cs.parabolic J)]
    (hB : IsWeylDistanceBuilding cs δ) (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : Gate.IsFlipInvolution cs δ w₀ t) (hI : Gate.flipCore cs δ t J a = residue cs δ I x₁)
    (hIJ : I ⊆ J)
    (hR₀ : ∀ c : ↥(residue cs δ J a), (c : C) ∈ residue cs δ I x₁ ↔ Θ.Φ c ∈ R₀')
    (hψ : ∀ c c' : ↥(residue cs δ J a), (c : C) ∈ residue cs δ I x₁ →
      (c' : C) = Gate.flipPsi cs δ t J a c → Θ.Φ c' = ψ' (Θ.Φ c))
    (hY : ∃ x ∈ R₀', ∀ y ∈ R₀', ∀ z ∈ R₀', cdist Y y z ≤ cdist Y x (ψ' x)) :
    ∃ x ∈ residue cs δ I x₁,
      cs.length (δ x (Gate.flipPsi cs δ t J a x)) = cs.length (longest cs I) := by
  haveI : Finite (cs.parabolic I) := p9uFA_finite_parabolic_of_subset hIJ
  obtain ⟨x', hx'R₀, hx'max⟩ := hY
  let c : ↥(residue cs δ J a) := Θ.Φ.symm x'
  have hcΦ : Θ.Φ c = x' := Θ.Φ.apply_symm_apply x'
  have hcI : (c : C) ∈ residue cs δ I x₁ := (hR₀ c).mpr (by rw [hcΦ]; exact hx'R₀)
  let ψR : ↥(residue cs δ J a) → ↥(residue cs δ J a) :=
    fun x => ⟨Gate.flipPsi cs δ t J a x, resProj_mem hB J a (t x)⟩
  have hΦψ : Θ.Φ (ψR c) = ψ' x' := by
    have h := hψ c (ψR c) hcI rfl
    rwa [hcΦ] at h
  have hdist : cdist Y x' (ψ' x') =
      cs.length (δ c (Gate.flipPsi cs δ t J a c)) := by
    calc cdist Y x' (ψ' x') = cdist Y (Θ.Φ c) (Θ.Φ (ψR c)) := by rw [hcΦ, hΦψ]
      _ = cdist ((buildingOver cs δ J).restrict (residue cs δ J a)) c (ψR c) :=
            cdist_chamberIso Θ c (ψR c)
      _ = cs.length (δ c (Gate.flipPsi cs δ t J a c)) := by
            rw [p9uFA_cdist_restrict_eq hB J a c (ψR c)]
  have hx₁I : x₁ ∈ residue cs δ I x₁ := self_mem_residue I x₁
  have hx₁R : x₁ ∈ residue cs δ J a := by
    have hmem : x₁ ∈ Gate.flipCore cs δ t J a := by
      rw [hI]
      exact hx₁I
    simp only [Gate.flipCore, Gate.projSet, Set.mem_image] at hmem
    rcases hmem with ⟨y, -, hy⟩
    rw [← hy]
    exact resProj_mem hB J a y
  obtain ⟨z, hzI, hzdist⟩ :=
    exists_mem_residue_dist_eq_longest (cs := cs) (δ := δ) (I := I) hB x₁
  have hzR : z ∈ residue cs δ J a := by
    have h : z ∈ residue cs δ J x₁ := residue_mono hIJ x₁ hzI
    rwa [residue_eq_of_mem hB hx₁R] at h
  have hle := hx'max (Θ.Φ ⟨x₁, hx₁R⟩) ((hR₀ ⟨x₁, hx₁R⟩).mp hx₁I)
    (Θ.Φ ⟨z, hzR⟩) ((hR₀ ⟨z, hzR⟩).mp hzI)
  have hcdist : cdist Y (Θ.Φ ⟨x₁, hx₁R⟩) (Θ.Φ ⟨z, hzR⟩) =
      cs.length (longest cs I) := by
    rw [cdist_chamberIso Θ ⟨x₁, hx₁R⟩ ⟨z, hzR⟩,
      p9uFA_cdist_restrict_eq hB J a ⟨x₁, hx₁R⟩ ⟨z, hzR⟩, hzdist]
  have hlow : cs.length (longest cs I) ≤
      cs.length (δ c (Gate.flipPsi cs δ t J a c)) := by
    rw [← hcdist, ← hdist]
    exact hle
  have hflipI : Gate.flipPsi cs δ t J a c ∈ residue cs δ I x₁ := by
    have hcore : (c : C) ∈ Gate.flipCore cs δ t J a := by rwa [hI]
    have h := Gate.flipPsi_mem (cs := cs) (δ := δ) (t := t) (w₀ := w₀) (J := J) (a := a)
      hB hw ht hcore
    rwa [hI] at h
  have hup : cs.length (δ c (Gate.flipPsi cs δ t J a c)) ≤ cs.length (longest cs I) :=
    length_dist_le_length_longest (cs := cs) (δ := δ) (I := I) (x := x₁) hB hcI hflipI
  exact ⟨c, hcI, le_antisymm hup hlow⟩

include Θ in
theorem length_longest_eq_of_chamberIso [Finite (cs.parabolic J)]
    (hB : IsWeylDistanceBuilding cs δ) {d : ℕ} (hle : ∀ x y : C', cdist Y x y ≤ d)
    (hd : ∃ x y : C', cdist Y x y = d) :
    cs.length (longest cs J) = d := by
  have hXle : ∀ u v : ↥(residue cs δ J a),
      cdist ((buildingOver cs δ J).restrict (residue cs δ J a)) u v ≤
        cs.length (longest cs J) := by
    intro u v
    rw [p9uFA_cdist_restrict_eq hB J a u v]
    exact length_dist_le_length_longest (cs := cs) (δ := δ) (I := J) (x := a) hB u.2 v.2
  obtain ⟨z, hz, hzdist⟩ :=
    exists_mem_residue_dist_eq_longest (cs := cs) (δ := δ) (I := J) hB a
  have hXeq : cdist ((buildingOver cs δ J).restrict (residue cs δ J a))
      ⟨a, self_mem_residue J a⟩ ⟨z, hz⟩ = cs.length (longest cs J) := by
    rw [p9uFA_cdist_restrict_eq hB J a ⟨a, self_mem_residue J a⟩ ⟨z, hz⟩, hzdist]
  have h1 : cs.length (longest cs J) ≤ d := by
    calc cs.length (longest cs J) =
          cdist ((buildingOver cs δ J).restrict (residue cs δ J a))
            ⟨a, self_mem_residue J a⟩ ⟨z, hz⟩ := hXeq.symm
      _ = cdist Y (Θ.Φ ⟨a, self_mem_residue J a⟩) (Θ.Φ ⟨z, hz⟩) :=
            (cdist_chamberIso Θ ⟨a, self_mem_residue J a⟩ ⟨z, hz⟩).symm
      _ ≤ d := hle _ _
  have h2 : d ≤ cs.length (longest cs J) := by
    obtain ⟨x, y, hxy⟩ := hd
    have h := hXle (Θ.Φ.symm x) (Θ.Φ.symm y)
    have heq : cdist ((buildingOver cs δ J).restrict (residue cs δ J a))
        (Θ.Φ.symm x) (Θ.Φ.symm y) = d := by
      rw [← cdist_chamberIso Θ (Θ.Φ.symm x) (Θ.Φ.symm y), Θ.Φ.apply_symm_apply,
        Θ.Φ.apply_symm_apply, hxy]
    exact heq ▸ h
  exact le_antisymm h1 h2

end Chart

end CFSG.ClassicalInvolution.Phan.PhanE.Flag

end
