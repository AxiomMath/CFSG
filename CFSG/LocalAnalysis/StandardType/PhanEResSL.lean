module

public import CFSG.LocalAnalysis.StandardType.PhanEResSLWeyl

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Res

open Matrix CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Phan.PhanE.Flag
  CFSG.LieType.Steinberg.CentralExt.SLClosed CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {Fld : Type} [Field Fld]

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
  {M : ChevModel2 D n H Fld} {m : ℕ}

private noncomputable def hmbSL_slType {M : ChevModel2 D n H Fld} {m : ℕ} (L : SLPath M m)
    {J : Set (Fin D.rank)} (hJ : Set.range L.e = J) : ↥J ≃ Fin m where
  toFun j := (Equiv.ofInjective L.e L.inj).symm ⟨j.1, hJ.symm ▸ j.2⟩
  invFun k := ⟨L.e k, hJ ▸ Set.mem_range.mpr ⟨k, rfl⟩⟩
  left_inv j := by
    apply Subtype.ext
    exact Equiv.apply_ofInjective_symm L.inj ⟨j.1, hJ.symm ▸ j.2⟩
  right_inv k := by
    have h1 : (⟨L.e k, hJ.symm ▸ (hJ ▸ Set.mem_range.mpr ⟨k, rfl⟩)⟩ :
        ↥(Set.range L.e)) = ⟨L.e k, (⟨k, rfl⟩ : ∃ y, L.e y = L.e k)⟩ := Subtype.ext rfl
    show (Equiv.ofInjective L.e L.inj).symm
        ⟨L.e k, hJ.symm ▸ (hJ ▸ Set.mem_range.mpr ⟨k, rfl⟩)⟩ = k
    rw [h1]
    exact Equiv.ofInjective_symm_apply L.inj k

private lemma hmbSL_slType_apply {M : ChevModel2 D n H Fld} {m : ℕ} (L : SLPath M m)
    {J : Set (Fin D.rank)} (hJ : Set.range L.e = J) (k : Fin m) (hk : L.e k ∈ J) :
    hmbSL_slType L hJ ⟨L.e k, hk⟩ = k := by
  have h1 : (⟨L.e k, hJ.symm ▸ hk⟩ : ↥(Set.range L.e)) =
      ⟨L.e k, (⟨k, rfl⟩ : ∃ y, L.e y = L.e k)⟩ := Subtype.ext rfl
  show (Equiv.ofInjective L.e L.inj).symm ⟨L.e k, hJ.symm ▸ hk⟩ = k
  rw [h1]
  exact Equiv.ofInjective_symm_apply L.inj k

private lemma hmbSL_slType_val {M : ChevModel2 D n H Fld} {m : ℕ} (L : SLPath M m)
    {J : Set (Fin D.rank)} (hJ : Set.range L.e = J) (j : ↥J) :
    L.e (hmbSL_slType L hJ j) = j.1 :=
  Equiv.apply_ofInjective_symm L.inj ⟨j.1, hJ.symm ▸ j.2⟩

private noncomputable def hmbSL_Psi {M : ChevModel2 D n H Fld} {m : ℕ} (L : SLPath M m)
    (g : K) : FlagK Fld (m + 1) → K ⧸ borel D H := fun E =>
  ((g * L.ε (Classical.choose (exists_flagAct_stdFlag E)) : K) : K ⧸ borel D H)

private lemma hmbSL_Psi_apply {M : ChevModel2 D n H Fld} {m : ℕ} (L : SLPath M m) (g : K)
    (A : SpecialLinearGroup (Fin (m + 1)) Fld) {E : FlagK Fld (m + 1)}
    (hE : flagAct (SpecialLinearGroup.toGL A) (stdFlag Fld (m + 1)) = E) :
    hmbSL_Psi L g E = ((g * L.ε A : K) : K ⧸ borel D H) := by
  classical
  set A' : SpecialLinearGroup (Fin (m + 1)) Fld :=
    Classical.choose (exists_flagAct_stdFlag E) with hA'
  have hspec : flagAct (SpecialLinearGroup.toGL A') (stdFlag Fld (m + 1)) = E := by
    rw [hA']
    exact Classical.choose_spec (exists_flagAct_stdFlag E)
  have hfix : flagAct (SpecialLinearGroup.toGL (A⁻¹ * A')) (stdFlag Fld (m + 1)) =
      stdFlag Fld (m + 1) := by
    rw [map_mul, map_inv, flagAct_mul, hspec, ← hE]
    rw [← flagAct_mul, ← map_inv, ← map_mul, inv_mul_cancel, map_one, flagAct_one]
  have hU : A⁻¹ * A' ∈ LinearFlag.upperTriangular (m + 1) Fld :=
    (flagAct_stdFlag_eq_iff (A⁻¹ * A')).mp hfix
  have hB : L.ε (A⁻¹ * A') ∈ borel D H := ε_mem_borel L hU
  unfold hmbSL_Psi
  rw [← hA', QuotientGroup.eq]
  have hval : (g * L.ε A')⁻¹ * (g * L.ε A) = (L.ε (A⁻¹ * A'))⁻¹ := by
    have hA'e : L.ε A' = L.ε A * L.ε (A⁻¹ * A') := by
      conv_lhs => rw [show A' = A * (A⁻¹ * A') from by group]
      exact map_mul L.ε A (A⁻¹ * A')
    rw [hA'e]
    group
  rw [hval]
  exact inv_mem hB

private theorem hmbSL_ε_n {M : ChevModel2 D n H Fld} {m : ℕ} [CharP Fld 2] (L : SLPath M m)
    (k : Fin m) :
    L.ε (tv Fld k.castSucc k.succ 1 * tv Fld k.succ k.castSucc 1 * tv Fld k.castSucc k.succ 1) =
      n (L.e k) := by
  rw [map_mul, map_mul, L.tv_eq k.castSucc k.succ (hmbSL_castSucc_ne_succ k) 1,
    L.tv_eq k.succ k.castSucc (hmbSL_castSucc_ne_succ k).symm 1,
    hmbSL_pathRoot_castSucc_succ, hmbSL_pathRoot_succ_castSucc, M.nm_def,
    CharTwo.neg_eq (1 : Fld)]

include hct hext in
private theorem hmbSL_hinj {M : ChevModel2 D n H Fld} {m : ℕ} [CharP Fld 2] (L : SLPath M m)
    {J : Set (Fin D.rank)} (hJ : Set.range L.e = J) (g : K) :
    Function.Injective (hmbSL_Psi L g) := by
  intro E E' h
  obtain ⟨A, hA⟩ := exists_flagAct_stdFlag E
  obtain ⟨A', hA'⟩ := exists_flagAct_stdFlag E'
  rw [hmbSL_Psi_apply L g A hA, hmbSL_Psi_apply L g A' hA'] at h
  have hδ1 : stdδ hct ((g * L.ε A : K) : K ⧸ borel D H)
      ((g * L.ε A' : K) : K ⧸ borel D H) = 1 := by
    rw [h]
    exact (stdBuilding hct hext).eq_one_self _
  rw [stdδ_mk_mul_ε hct hext L g A A'] at hδ1
  have hflag : flagδ m (flagAct (SpecialLinearGroup.toGL A) (stdFlag Fld (m + 1)))
      (flagAct (SpecialLinearGroup.toGL A') (stdFlag Fld (m + 1))) = 1 :=
    pathWeyl_injective L (by rw [hδ1, map_one])
  rw [flagδ_eq_one_iff] at hflag
  rw [← hA, ← hA']
  exact hflag

include hext in
private theorem hmbSL_hmem {M : ChevModel2 D n H Fld} {m : ℕ} [CharP Fld 2] (L : SLPath M m)
    {J : Set (Fin D.rank)} (hJ : Set.range L.e = J) (g : K) :
    ∀ ω, hmbSL_Psi L g ω ∈ residue (cs) (stdδ hct) J ((g : K) : K ⧸ borel D H) := by
  intro ω
  obtain ⟨A, hA⟩ := exists_flagAct_stdFlag ω
  rw [hmbSL_Psi_apply L g A hA]
  exact mk_mul_ε_mem_residue hct hext L hJ g A

include hext in
private theorem hmbSL_hadj {M : ChevModel2 D n H Fld} {m : ℕ} [CharP Fld 2] (L : SLPath M m)
    {J : Set (Fin D.rank)} (hJ : Set.range L.e = J) (g : K) :
    ∀ (j : ↥J) (ω ω' : FlagK Fld (m + 1)),
      (flagSys Fld m).adj (hmbSL_slType L hJ j) ω ω' ↔
        stdδ hct (hmbSL_Psi L g ω) (hmbSL_Psi L g ω') = 1 ∨
          stdδ hct (hmbSL_Psi L g ω) (hmbSL_Psi L g ω') = (cs).simple j := by
  intro j ω ω'
  obtain ⟨A, hA⟩ := exists_flagAct_stdFlag ω
  obtain ⟨A', hA'⟩ := exists_flagAct_stdFlag ω'
  have hsimple : (cs).simple j = pathWeyl L ((symCox m).simple (hmbSL_slType L hJ j)) := by
    rw [← hmbSL_slType_val L hJ j]
    exact (pathWeyl_simple L (hmbSL_slType L hJ j)).symm
  rw [flagSys_adj_iff, hmbSL_Psi_apply L g A hA, hmbSL_Psi_apply L g A' hA',
    stdδ_mk_mul_ε hct hext L g A A', ← hA, ← hA']
  constructor
  · rintro (h | h)
    · left
      rw [h, map_one]
    · right
      rw [h, hsimple]
  · rintro (h | h)
    · left
      exact pathWeyl_injective L (by rw [h, map_one])
    · right
      exact pathWeyl_injective L (h.trans hsimple)

include hext in
private theorem hmbSL_hpanel {M : ChevModel2 D n H Fld} {m : ℕ} [CharP Fld 2] (L : SLPath M m)
    {J : Set (Fin D.rank)} (hJ : Set.range L.e = J) (g : K) :
    ∀ (ω : FlagK Fld (m + 1)) (j : ↥J) (c : K ⧸ borel D H),
      stdδ hct (hmbSL_Psi L g ω) c = (cs).simple j → c ∈ Set.range (hmbSL_Psi L g) := by
  intro ω j c hδ
  obtain ⟨A, hA⟩ := exists_flagAct_stdFlag ω
  rw [hmbSL_Psi_apply L g A hA] at hδ
  have hjmem : (j : Fin D.rank) ∈ Set.range L.e := by rw [hJ]; exact j.2
  obtain ⟨k, hk⟩ := hjmem
  have hj : j = ⟨L.e k, by rw [hk]; exact j.2⟩ := Subtype.ext hk.symm
  rw [hj] at hδ
  obtain ⟨x, hx, hxeq⟩ := exists_eq_of_stdδ_eq_simple hct hext (i := L.e k)
    (g := g * L.ε A) hδ
  rw [← hmbSL_pathRoot_castSucc_succ L.e k] at hx
  obtain ⟨c', hc'⟩ := (M.x_mem (pathRoot L.e k.castSucc k.succ)
    (pathRoot_mem_roots L (hmbSL_castSucc_ne_succ k)) x).mp hx
  refine ⟨flagAct (SpecialLinearGroup.toGL
    (A * tv Fld k.castSucc k.succ c' *
      (tv Fld k.castSucc k.succ 1 * tv Fld k.succ k.castSucc 1 * tv Fld k.castSucc k.succ 1)))
    (stdFlag Fld (m + 1)), ?_⟩
  have hAUP : L.ε (A * tv Fld k.castSucc k.succ c' *
      (tv Fld k.castSucc k.succ 1 * tv Fld k.succ k.castSucc 1 * tv Fld k.castSucc k.succ 1)) =
      L.ε A * L.ε (tv Fld k.castSucc k.succ c') * n (L.e k) := by
    rw [map_mul, hmbSL_ε_n L k, map_mul]
  rw [hmbSL_Psi_apply L g _ rfl, hAUP,
    L.tv_eq k.castSucc k.succ (hmbSL_castSucc_ne_succ k) c', hc', hxeq]
  congr 1
  group

private theorem hmbSL_hbase {M : ChevModel2 D n H Fld} {m : ℕ} (L : SLPath M m)
    {J : Set (Fin D.rank)} (hJ : Set.range L.e = J) (g : K) :
    (g : K ⧸ borel D H) ∈ Set.range (hmbSL_Psi L g) := by
  refine ⟨stdFlag Fld (m + 1), ?_⟩
  rw [hmbSL_Psi_apply L g 1 (by rw [map_one, flagAct_one]), map_one, mul_one]

noncomputable def slChart [CharP Fld 2] (hext : SteinbergExtras D n H) (L : SLPath M m)
    {J : Set (Fin D.rank)} (hJ : Set.range L.e = J) (g : K) :
    ChamberIso ((buildingOver (cs) (stdδ hct) J).restrict
      (residue (cs) (stdδ hct) J ((g : K) : K ⧸ borel D H))) (flagSys Fld m) :=
  chartOfMap (stdBuilding hct hext) (flagSys Fld m) (hmbSL_slType L hJ) (hmbSL_Psi L g)
    (hmbSL_hinj hct hext L hJ g) (hmbSL_hadj hct hext L hJ g) (hmbSL_hmem hct hext L hJ g)
    (hmbSL_hbase L hJ g) (hmbSL_hpanel hct hext L hJ g)

theorem slChart_symm_apply [CharP Fld 2] (L : SLPath M m) {J : Set (Fin D.rank)}
    (hJ : Set.range L.e = J) (g : K) (A : SpecialLinearGroup (Fin (m + 1)) Fld) :
    (((slChart hct hext L hJ g).Φ.symm
        (flagAct (SpecialLinearGroup.toGL A) (stdFlag Fld (m + 1))) :
      ↥(residue (cs) (stdδ hct) J ((g : K) : K ⧸ borel D H))) : K ⧸ borel D H) =
      ((g * L.ε A : K) : K ⧸ borel D H) := by
  exact (chartOfMap_symm_apply (hB := stdBuilding hct hext) (Y := flagSys Fld m)
    (e := hmbSL_slType L hJ) (Ψ := hmbSL_Psi L g) (hinj := hmbSL_hinj hct hext L hJ g)
    (hadj := hmbSL_hadj hct hext L hJ g) (hmem := hmbSL_hmem hct hext L hJ g)
    (hbase := hmbSL_hbase L hJ g) (hpanel := hmbSL_hpanel hct hext L hJ g)
    (ω := flagAct (SpecialLinearGroup.toGL A) (stdFlag Fld (m + 1)))).trans
    (hmbSL_Psi_apply L g A rfl)

theorem slChart_apply [CharP Fld 2] (L : SLPath M m) {J : Set (Fin D.rank)}
    (hJ : Set.range L.e = J) (g : K)
    (A : SpecialLinearGroup (Fin (m + 1)) Fld) :
    (slChart hct hext L hJ g).Φ ⟨_, mk_mul_ε_mem_residue hct hext L hJ g A⟩ =
      flagAct (SpecialLinearGroup.toGL A) (stdFlag Fld (m + 1)) := by
  have hsub : (⟨((g * L.ε A : K) : K ⧸ borel D H),
        mk_mul_ε_mem_residue hct hext L hJ g A⟩ :
      ↥(residue (cs) (stdδ hct) J ((g : K) : K ⧸ borel D H))) =
      ⟨hmbSL_Psi L g (flagAct (SpecialLinearGroup.toGL A) (stdFlag Fld (m + 1))),
        hmbSL_hmem hct hext L hJ g _⟩ := by
    apply Subtype.ext
    exact (hmbSL_Psi_apply L g A rfl).symm
  rw [hsub]
  exact chartOfMap_apply (hB := stdBuilding hct hext) (Y := flagSys Fld m)
    (e := hmbSL_slType L hJ) (Ψ := hmbSL_Psi L g) (hinj := hmbSL_hinj hct hext L hJ g)
    (hadj := hmbSL_hadj hct hext L hJ g) (hmem := hmbSL_hmem hct hext L hJ g)
    (hbase := hmbSL_hbase L hJ g) (hpanel := hmbSL_hpanel hct hext L hJ g)
    (ω := flagAct (SpecialLinearGroup.toGL A) (stdFlag Fld (m + 1)))

theorem slChart_e_apply [CharP Fld 2] (L : SLPath M m) {J : Set (Fin D.rank)}
    (hJ : Set.range L.e = J)
    (g : K) (k : Fin m) (hk : L.e k ∈ J) :
    (slChart hct hext L hJ g).e ⟨L.e k, hk⟩ = k := by
  rw [slChart, chartOfMap_e]
  exact hmbSL_slType_apply L hJ k hk

private noncomputable def hmbSL_conjGL {m : ℕ} (Dt : GL (Fin (m + 1)) Fld) :
    SpecialLinearGroup (Fin (m + 1)) Fld →* SpecialLinearGroup (Fin (m + 1)) Fld :=
  (SpecialLinearGroup.toGLKerEquiv (n := Fin (m + 1)) (R := Fld)).symm.toMonoidHom.comp
    (((MulAut.conj Dt).toMonoidHom.comp SpecialLinearGroup.toGL).codRestrict
      (GeneralLinearGroup.det.ker) (fun A => by
        change GeneralLinearGroup.det (Dt * SpecialLinearGroup.toGL A * Dt⁻¹) = 1
        rw [map_mul, map_mul, map_inv, SpecialLinearGroup.coeToGL_det, mul_one,
          mul_inv_cancel]))

private lemma hmbSL_conjGL_coe {m : ℕ} (Dt : GL (Fin (m + 1)) Fld)
    (A : SpecialLinearGroup (Fin (m + 1)) Fld) :
    ((hmbSL_conjGL Dt A : SpecialLinearGroup (Fin (m + 1)) Fld) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) =
      (Dt : Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) *
        (A : Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) *
        ((Dt⁻¹ : GL (Fin (m + 1)) Fld) : Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) := by
  rfl

private lemma hmbSL_toGL_conjGL {m : ℕ} (Dt : GL (Fin (m + 1)) Fld)
    (A : SpecialLinearGroup (Fin (m + 1)) Fld) :
    SpecialLinearGroup.toGL (hmbSL_conjGL Dt A) =
      Dt * SpecialLinearGroup.toGL A * Dt⁻¹ := by
  apply Units.ext
  rw [SpecialLinearGroup.coe_GL_coe_matrix, hmbSL_conjGL_coe,
    Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  rfl

private lemma hmbSL_conjGL_mul {m : ℕ} (Dx Dy : GL (Fin (m + 1)) Fld) :
    hmbSL_conjGL (Dx * Dy) = (hmbSL_conjGL Dx).comp (hmbSL_conjGL Dy) := by
  apply MonoidHom.ext
  intro A
  apply SpecialLinearGroup.toGL_injective
  rw [hmbSL_toGL_conjGL, MonoidHom.comp_apply, hmbSL_toGL_conjGL, hmbSL_toGL_conjGL]
  group

private lemma hmbSL_conjGL_one {m : ℕ} :
    hmbSL_conjGL (1 : GL (Fin (m + 1)) Fld) = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro A
  apply SpecialLinearGroup.toGL_injective
  rw [hmbSL_toGL_conjGL, MonoidHom.id_apply]
  group

private theorem hmbSL_hom_ext_tv {N : Type*} [Group N] {m : ℕ}
    (f g : SpecialLinearGroup (Fin (m + 1)) Fld →* N)
    (h : ∀ (p q : Fin (m + 1)) (hpq : p ≠ q) (c : Fld),
      f (tv Fld p q c) = g (tv Fld p q c)) : f = g := by
  apply MonoidHom.ext
  intro A
  have htop : Subgroup.closure (Set.range (TransvectionStruct.toSpecialLinearGroup :
      TransvectionStruct (Fin (m + 1)) Fld → SpecialLinearGroup (Fin (m + 1)) Fld)) = ⊤ :=
    SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
  have hmem : A ∈ Subgroup.closure (Set.range (TransvectionStruct.toSpecialLinearGroup :
      TransvectionStruct (Fin (m + 1)) Fld → SpecialLinearGroup (Fin (m + 1)) Fld)) := by
    rw [htop]; exact Subgroup.mem_top A
  induction hmem using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    rw [TransvectionStruct.toSpecialLinearGroup_def, ← tv_of_ne t.hij t.c]
    exact h t.i t.j t.hij t.c
  | one => rw [map_one, map_one]
  | mul x y hx hy ihx ihy => rw [map_mul, map_mul, ihx, ihy]
  | inv x hx ih => rw [map_inv, map_inv, ih]

private lemma hmbSL_coe_tv {m : ℕ} {p q : Fin (m + 1)} (hpq : p ≠ q) (c : Fld) :
    ((tv Fld p q c : SpecialLinearGroup (Fin (m + 1)) Fld) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) = Matrix.transvection p q c := by
  rw [tv_of_ne hpq]
  exact Matrix.SpecialLinearGroup.transvection_coe hpq c

private lemma hmbSL_diagGL_inv_coe {m : ℕ} (χ : Fin (m + 1) → Fldˣ) :
    (((TauCeti.diagGL χ : GL (Fin (m + 1)) Fld)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) Fld)⁻¹ =
      Matrix.diagonal (fun i => ((χ i : Fld))⁻¹) := by
  rw [TauCeti.diagGL_coe]
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal]
  exact Matrix.diagonal_eq_one.mpr (funext (fun i => mul_inv_cancel₀ (Units.ne_zero (χ i))))

private lemma hmbSL_diagGL_conj_tv {m : ℕ} (χ : Fin (m + 1) → Fldˣ)
    {p q : Fin (m + 1)} (hpq : p ≠ q) (c : Fld) :
    hmbSL_conjGL (TauCeti.diagGL χ) (tv Fld p q c) =
      tv Fld p q ((χ p : Fld) * c * ((χ q : Fld))⁻¹) := by
  apply Subtype.ext
  rw [hmbSL_conjGL_coe, hmbSL_coe_tv hpq c, hmbSL_coe_tv hpq _,
    Matrix.GeneralLinearGroup.coe_inv, hmbSL_diagGL_inv_coe, TauCeti.diagGL_coe,
    TauCeti.diagonal_mul_transvection_mul_diagonal (fun a =>
      mul_inv_cancel₀ (Units.ne_zero (χ a)))]

private lemma hmbSL_pathRoot_sub {r m : ℕ} (e : Fin m → Fin r) (p q : Fin (m + 1)) :
    pathRoot e p q = pathRoot e 0 q - pathRoot e 0 p := by
  rcases lt_or_ge p q with hpq | hqp
  · have h := hmbSL_pathRoot_split e (Fin.zero_le p) hpq.le
    rw [h]; abel
  · by_cases hpq' : p = q
    · subst hpq'
      rw [hmbSL_pathRoot_self, sub_self]
    · have hlt : q < p := lt_of_le_of_ne hqp (Ne.symm hpq')
      have h := hmbSL_pathRoot_split e (Fin.zero_le q) hlt.le
      have hneg : pathRoot e p q = -pathRoot e q p := by
        unfold pathRoot
        rw [if_neg (not_lt.mpr hlt.le), if_pos hlt]
      rw [hneg, h]; abel

private theorem hmbSL_torus_gen {M : ChevModel2 D n H Fld} {m : ℕ} (L : SLPath M m)
    (i : Fin D.rank) (u : Fldˣ) :
    ∃ Dt : GL (Fin (m + 1)) Fld,
      (∀ p q, p ≠ q → (Dt : Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) p q = 0) ∧
      ∀ A, M.hh i u * L.ε A * (M.hh i u)⁻¹ = L.ε (hmbSL_conjGL Dt A) := by
  classical
  let E : Fin (m + 1) → ℤ := fun p => coroot D.cartan i (pathRoot L.e 0 p)
  let χ : Fin (m + 1) → Fldˣ := fun p => u ^ (-(E p))
  let Dt : GL (Fin (m + 1)) Fld := TauCeti.diagGL χ
  refine ⟨Dt, ?_, ?_⟩
  · intro p q hpq
    rw [show (Dt : Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) =
      Matrix.diagonal (fun i => (χ i : Fld)) from TauCeti.diagGL_coe χ]
    exact Matrix.diagonal_apply_ne _ hpq
  · intro A
    let F : SpecialLinearGroup (Fin (m + 1)) Fld →* K :=
      (MulAut.conj (M.hh i u)).toMonoidHom.comp L.ε
    let G : SpecialLinearGroup (Fin (m + 1)) Fld →* K :=
      L.ε.comp (hmbSL_conjGL Dt)
    have hFG : F = G := by
      apply hmbSL_hom_ext_tv
      intro p q hpq c
      show M.hh i u * L.ε (tv Fld p q c) * (M.hh i u)⁻¹ =
        L.ε (hmbSL_conjGL Dt (tv Fld p q c))
      have hγ : pathRoot L.e p q ∈ D.roots := pathRoot_mem_roots L hpq
      have hE : E q - E p = coroot D.cartan i (pathRoot L.e p q) := by
        show coroot D.cartan i (pathRoot L.e 0 q) - coroot D.cartan i (pathRoot L.e 0 p) = _
        rw [hmbSL_pathRoot_sub L.e p q, map_sub]
      have hchar : ((χ p : Fld) * ((χ q : Fld))⁻¹) =
          ↑(u ^ coroot D.cartan i (pathRoot L.e p q)) := by
        have hpow : χ p * (χ q)⁻¹ = u ^ coroot D.cartan i (pathRoot L.e p q) := by
          have h0 : χ p * (χ q)⁻¹ = u ^ (E q - E p) := by
            show u ^ (-(E p)) * (u ^ (-(E q)))⁻¹ = u ^ (E q - E p)
            have h : (u ^ (-(E q)))⁻¹ = u ^ (E q) := by
              rw [_root_.zpow_neg, _root_.inv_inv]
            rw [h, ← _root_.zpow_add]
            ring_nf
          rw [hE] at h0
          exact h0
        have h1 : ((χ p : Fld) * ((χ q : Fld))⁻¹) = ((χ p * (χ q)⁻¹ : Fldˣ) : Fld) := by
          rw [Units.val_mul, Units.val_inv_eq_inv_val]
        rw [h1]
        exact congrArg (fun z : Fldˣ => (z : Fld)) hpow
      simp only [coroot_apply] at hchar ⊢
      rw [L.tv_eq p q hpq c, M.hh_conj i u (pathRoot L.e p q) hγ c,
        hmbSL_diagGL_conj_tv χ hpq c, L.tv_eq p q hpq _, ← hchar]
      ring_nf
    exact congrArg (fun f : SpecialLinearGroup (Fin (m + 1)) Fld →* K => f A) hFG

private theorem hmbSL_torus_conj {M : ChevModel2 D n H Fld} {m : ℕ} (L : SLPath M m)
    {t : K} (ht : t ∈ ⨆ k, H k) :
    ∃ Dt : GL (Fin (m + 1)) Fld,
      (∀ p q, p ≠ q → (Dt : Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) p q = 0) ∧
      ∀ A, t * L.ε A * t⁻¹ = L.ε (hmbSL_conjGL Dt A) := by
  classical
  let C : K → Prop := fun t => ∃ Dt : GL (Fin (m + 1)) Fld,
      (∀ p q, p ≠ q → (Dt : Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) p q = 0) ∧
      ∀ A, t * L.ε A * t⁻¹ = L.ε (hmbSL_conjGL Dt A)
  change C t
  refine Subgroup.iSup_induction (C := C) (fun k => H k) ht ?_ ?_ ?_
  · intro k hk hkH
    rw [← M.hh_range k] at hkH
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hkH
    exact hmbSL_torus_gen L k u
  · refine ⟨1, ?_, ?_⟩
    · intro p q hpq
      rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply_ne hpq]
    · intro A
      rw [one_mul, inv_one, mul_one, hmbSL_conjGL_one, MonoidHom.id_apply]
  · intro x y hx hy
    obtain ⟨Dx, hDx, hxconj⟩ := hx
    obtain ⟨Dy, hDy, hyconj⟩ := hy
    refine ⟨Dx * Dy, ?_, ?_⟩
    · intro p q hpq
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hkp : k = p
      · rw [hkp, hDy p q hpq, mul_zero]
      · rw [hDx p k (Ne.symm hkp), zero_mul]
    · intro A
      rw [hmbSL_conjGL_mul, MonoidHom.comp_apply, ← hxconj (hmbSL_conjGL Dy A),
        ← hyconj A]
      group

private lemma hmbSL_conjGL_mul_diag {m : ℕ} (Dt : GL (Fin (m + 1)) Fld)
    (A : SpecialLinearGroup (Fin (m + 1)) Fld) :
    SpecialLinearGroup.toGL (hmbSL_conjGL Dt A) * Dt = Dt * SpecialLinearGroup.toGL A := by
  rw [hmbSL_toGL_conjGL]
  group

theorem slChart_coord_torus [CharP Fld 2] (L : SLPath M m) {J : Set (Fin D.rank)}
    (hJ : Set.range L.e = J)
    (g : K) {t : K} (ht : t ∈ ⨆ k, H k) :
    ∃ Dt : GL (Fin (m + 1)) Fld,
      (∀ i j, i ≠ j → (Dt : Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) i j = 0) ∧
      ∀ (A : SpecialLinearGroup (Fin (m + 1)) Fld)
        (c : ↥(residue (cs) (stdδ hct) J ((g : K) : K ⧸ borel D H))),
        (c : K ⧸ borel D H) = ((g * t * L.ε A : K) : K ⧸ borel D H) →
          (slChart hct hext L hJ g).Φ c =
            flagAct Dt (flagAct (SpecialLinearGroup.toGL A) (stdFlag Fld (m + 1))) := by
  obtain ⟨Dt, hdiag, hconj⟩ := hmbSL_torus_conj L ht
  refine ⟨Dt, hdiag, ?_⟩
  intro A c hc
  have hflag : flagAct Dt (flagAct (SpecialLinearGroup.toGL A) (stdFlag Fld (m + 1))) =
      flagAct (SpecialLinearGroup.toGL (hmbSL_conjGL Dt A)) (stdFlag Fld (m + 1)) := by
    rw [← flagAct_mul, ← hmbSL_conjGL_mul_diag, flagAct_mul,
      show flagAct Dt (stdFlag Fld (m + 1)) = stdFlag Fld (m + 1) from
        flagAct_stdFlag Dt (fun i j hij => hdiag i j hij.ne')]
  rw [hflag]
  have hB : t ∈ borel D H := Subgroup.mem_sup_left ht
  have hchamber : (c : K ⧸ borel D H) =
      ((g * L.ε (hmbSL_conjGL Dt A) : K) : K ⧸ borel D H) := by
    rw [hc, QuotientGroup.eq]
    have hKeq : g * t * L.ε A = g * L.ε (hmbSL_conjGL Dt A) * t := by
      rw [← hconj A]; group
    rw [hKeq]
    have hthis : (g * L.ε (hmbSL_conjGL Dt A) * t)⁻¹ *
        (g * L.ε (hmbSL_conjGL Dt A)) = t⁻¹ := by group
    rw [hthis]
    exact inv_mem hB
  have hsymm := slChart_symm_apply hct hext L hJ g (hmbSL_conjGL Dt A)
  have hsub : c = (slChart hct hext L hJ g).Φ.symm
      (flagAct (SpecialLinearGroup.toGL (hmbSL_conjGL Dt A)) (stdFlag Fld (m + 1))) := by
    apply Subtype.ext
    rw [hchamber, hsymm]
  rw [hsub]
  exact (slChart hct hext L hJ g).Φ.apply_symm_apply _

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
