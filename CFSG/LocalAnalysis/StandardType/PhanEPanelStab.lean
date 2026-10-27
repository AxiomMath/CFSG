module

public import CFSG.LocalAnalysis.StandardType.PhanEFixedTrans

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry
open scoped Matrix MatrixGroups

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H)
  {w₀ : W} (F : FrobData D n H w₀) (hext : SteinbergExtras D n H)
  (hw₀ : IsLongest (coxeterMatrix D.isFiniteType).toCoxeterSystem Set.univ w₀)
  (hsq : ∀ i, n i * n i = 1)

private theorem hmbPan_mem_closure_simple (i : Fin D.rank) (w : W) :
    w ∈ Subgroup.closure ({(cs).simple i} : Set W) ↔ w = 1 ∨ w = (cs).simple i := by
  constructor
  · intro hw
    rw [Subgroup.mem_closure_singleton] at hw
    obtain ⟨m, hm⟩ := hw
    have h2 : (cs).simple i ^ (2 : ℕ) = 1 := (cs).simple_sq i
    have hm2 : (cs).simple i ^ m = (cs).simple i ^ (m % (2 : ℤ)) := zpow_eq_zpow_emod' m h2
    rw [← hm, hm2]
    rcases Int.emod_two_eq_zero_or_one m with h | h <;> rw [h]
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)

private theorem hmbPan_w2_coe (L : StdLevi F (nrep hct w₀)) :
    (((sl2Upper (1 : L.Fld) * sl2Lower (-1) * sl2Upper 1 : SL(2, L.Fld))) :
      Matrix (Fin 2) (Fin 2) L.Fld) = !![0, 1; -1, 0] := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Lower, Matrix.mul_apply,
      Fin.sum_univ_two]

private theorem hmbPan_w2_inv_coe (L : StdLevi F (nrep hct w₀)) :
    ((((sl2Upper (1 : L.Fld) * sl2Lower (-1) * sl2Upper 1 : SL(2, L.Fld)))⁻¹ :
      SL(2, L.Fld)) : Matrix (Fin 2) (Fin 2) L.Fld) = !![0, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, hmbPan_w2_coe (hct := hct) (F := F) L,
    Matrix.adjugate_fin_two_of]
  simp

private theorem hmbPan_sl2Borel_mem (L : StdLevi F (nrep hct w₀)) (i : Fin D.rank)
    {A : SL(2, L.Fld)} (hA : A ∈ sl2Borel L.Fld) : L.ε i A ∈ borel D H := by
  have h10 : (A : Matrix (Fin 2) (Fin 2) L.Fld) 1 0 = 0 := hA
  have hdet : (A : Matrix (Fin 2) (Fin 2) L.Fld) 0 0 *
      (A : Matrix (Fin 2) (Fin 2) L.Fld) 1 1 = 1 := by
    have h := A.2
    rw [Matrix.det_fin_two, h10] at h
    simpa using h
  let u : L.Fldˣ := Units.mk ((A : Matrix (Fin 2) (Fin 2) L.Fld) 0 0)
    ((A : Matrix (Fin 2) (Fin 2) L.Fld) 1 1) hdet (by rw [mul_comm]; exact hdet)
  have hfac : A = WeakCT.torusHom L.Fld u *
      sl2Upper ((A : Matrix (Fin 2) (Fin 2) L.Fld) 1 1 *
        (A : Matrix (Fin 2) (Fin 2) L.Fld) 0 1) := by
    refine Subtype.ext ?_
    ext p q
    fin_cases p <;> fin_cases q <;>
      simp [WeakCT.coe_torusHom, coe_sl2Upper, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.mul_apply, Fin.sum_univ_two, h10, Units.val_mk, u]
    rw [← mul_assoc, hdet, one_mul]
  rw [hfac, map_mul]
  refine mul_mem ?_ ?_
  · exact iSup_le_borel (le_iSup H i (L.ε_torusHom_mem i u))
  · refine rootGroup_le_borel
      ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i) (ht_single_pos i) ?_
    have hx : L.ε i (sl2Upper ((A : Matrix (Fin 2) (Fin 2) L.Fld) 1 1 *
        (A : Matrix (Fin 2) (Fin 2) L.Fld) 0 1)) ∈
        (D.rootGroup (Pi.single i 1) : Set K) :=
      L.upper i ▸ Set.mem_range_self ((A : Matrix (Fin 2) (Fin 2) L.Fld) 1 1 *
        (A : Matrix (Fin 2) (Fin 2) L.Fld) 0 1)
    exact hx

private theorem hmbPan_range_le (L : StdLevi F (nrep hct w₀)) (i : Fin D.rank)
    {P : Subgroup K} (hBP : borel D H ≤ P) (hnP : n i ∈ P) : (L.ε i).range ≤ P := by
  have hα : Pi.single i 1 ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hneg : -Pi.single i 1 ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hα
  have hxP : D.rootGroup (Pi.single i 1) ≤ P := fun y hy =>
    hBP (rootGroup_le_borel hα (ht_single_pos i) hy)
  have hUpper : ∀ c, L.ε i (sl2Upper c) ∈ P := by
    intro c
    refine hxP ?_
    have hx : L.ε i (sl2Upper c) ∈ (D.rootGroup (Pi.single i 1) : Set K) :=
      L.upper i ▸ Set.mem_range_self c
    exact hx
  have hLower : ∀ c, L.ε i (sl2Lower c) ∈ P := by
    intro c
    have hz : L.ε i (sl2Lower c) ∈ (D.rootGroup (-Pi.single i 1) : Set K) :=
      L.lower i ▸ Set.mem_range_self c
    have hconjz : n i * L.ε i (sl2Lower c) * (n i)⁻¹ ∈ D.rootGroup (Pi.single i 1) := by
      have h := hct.conj_mem i (-Pi.single i 1) hneg (L.ε i (sl2Lower c)) hz
      rwa [map_neg, weylAction_simple_single D.isFiniteType i, neg_neg] at h
    have heq : L.ε i (sl2Lower c) =
        (n i)⁻¹ * (n i * L.ε i (sl2Lower c) * (n i)⁻¹) * n i := by group
    rw [heq]
    exact mul_mem (mul_mem (inv_mem hnP) (hxP hconjz)) hnP
  rintro x ⟨A, rfl⟩
  have hA : A ∈ Subgroup.closure (Set.range (sl2Upper (k := L.Fld)) ∪
      Set.range (sl2Lower (k := L.Fld))) := by
    have h2 : A ∈ Subgroup.closure
        (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper L.Fld) ∪
          Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower L.Fld)) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := L.Fld)]
      exact Subgroup.mem_top A
    exact h2
  have hcomap : Subgroup.closure (Set.range (sl2Upper (k := L.Fld)) ∪
      Set.range (sl2Lower (k := L.Fld))) ≤ Subgroup.comap (L.ε i) P := by
    refine (Subgroup.closure_le (Subgroup.comap (L.ε i) P)).2 ?_
    rintro y (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact hUpper c
    · exact hLower c
  exact hcomap hA

include hct in
private theorem hmbPan_inv_conj_n_mem_posUnipotentExcept (i : Fin D.rank) {u : K}
    (hu : u ∈ posUnipotentExcept D i) : (n i)⁻¹ * u * (n i) ∈ posUnipotentExcept D i := by
  have hsq : (n i * n i)⁻¹ ∈ ⨆ j, H j :=
    inv_mem (by rw [← pow_two]; exact le_iSup H i (hct.sq_mem i))
  have hTnorm : (⨆ j, H j) ≤ Subgroup.normalizer (posUnipotentExcept D i : Set K) :=
    CFSG.LieType.Steinberg.le_normalizer_iSup₂ fun h hh γ hγ y hy =>
      Subgroup.mem_iSup_of_mem γ (Subgroup.mem_iSup_of_mem hγ
        ((Subgroup.mem_normalizer_iff.mp
          (iSup_le_normalizer_rootGroup hct hγ.1.1 hh) y).mp hy))
  have e : (n i)⁻¹ * u * (n i) =
      (n i * n i)⁻¹ * (n i * u * (n i)⁻¹) * ((n i * n i)⁻¹)⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hTnorm hsq)
    (n i * u * (n i)⁻¹)).mp (conj_n_mem_posUnipotentExcept hct i hu)

include hext in
private theorem hmbPan_cell_simple_eq (i : Fin D.rank) {g : K}
    (hg : g ∈ bruhatCell hct ((cs).simple i)) :
    ∃ x ∈ D.rootGroup (Pi.single i 1), ∃ b ∈ borel D H, g = x * n i * b := by
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hg
  rw [nrep_simple hct i] at *
  obtain ⟨t, ht, u, hu, x, hx, hb₁eq⟩ := exists_eq_mul_mul_of_mem_borel hct hext i hb₁
  have hα : Pi.single i 1 ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hneg : -Pi.single i 1 ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hα
  set u' : K := x⁻¹ * u * x with hu'_def
  have hu'mem : u' ∈ posUnipotentExcept D i := by
    rw [hu'_def]
    exact (Subgroup.mem_normalizer_iff''.mp (rootGroup_single_le_normalizer hext i hx) u).mp hu
  set u'' : K := (n i)⁻¹ * u' * (n i) with hu''_def
  have hu''mem : u'' ∈ posUnipotentExcept D i := by
    rw [hu''_def]
    exact hmbPan_inv_conj_n_mem_posUnipotentExcept (hct := hct) (H := H) i hu'mem
  set y : K := (n i)⁻¹ * x * (n i) with hy_def
  have hymem : y ∈ D.rootGroup (-Pi.single i 1) := by
    rw [hy_def]
    have h := (actsAs_n hct i).inv_conj_mem hα hx
    rwa [(cs).inv_simple, weylAction_simple_single D.isFiniteType i] at h
  set t' : K := (n i)⁻¹ * t * (n i) with ht'_def
  have ht'mem : t' ∈ ⨆ k, H k := by
    rw [ht'_def]
    exact inv_conj_n_mem_iSup (hct := hct) i ht
  set y' : K := t' * y * t'⁻¹ with hy'_def
  have hy'mem : y' ∈ D.rootGroup (-Pi.single i 1) := by
    rw [hy'_def]
    exact (Subgroup.mem_normalizer_iff.mp
      (iSup_le_normalizer_rootGroup (hct := hct) hneg ht'mem) y).mp hymem
  set x'' : K := n i * y' * (n i)⁻¹ with hx''_def
  have hx''mem : x'' ∈ D.rootGroup (Pi.single i 1) := by
    rw [hx''_def]
    have h := hct.conj_mem i (-Pi.single i 1) hneg y' hy'mem
    rwa [map_neg, weylAction_simple_single D.isFiniteType i, neg_neg] at h
  set b : K := t' * u'' * b₂ with hb_def
  have hbmem : b ∈ borel D H := by
    rw [hb_def]
    exact mul_mem (mul_mem (iSup_le_borel ht'mem) (posUnipotent_le_borel
      (posUnipotentExcept_le_posUnipotent i hu''mem))) hb₂
  have hu'x : u * x = x * u' := by rw [hu'_def]; group
  have hu''n : u' * n i = n i * u'' := by rw [hu''_def]; group
  have hyn : x * n i = n i * y := by rw [hy_def]; group
  have ht'n : t * n i = n i * t' := by rw [ht'_def]; group
  have hy't : t' * y = y' * t' := by rw [hy'_def]; group
  refine ⟨x'', hx''mem, b, hbmem, ?_⟩
  rw [hb₁eq]
  calc t * u * x * n i * b₂
      = t * (u * x) * n i * b₂ := by group
    _ = t * (x * u') * n i * b₂ := by rw [hu'x]
    _ = t * x * (u' * n i) * b₂ := by group
    _ = t * x * (n i * u'') * b₂ := by rw [hu''n]
    _ = t * (x * n i) * u'' * b₂ := by group
    _ = t * (n i * y) * u'' * b₂ := by rw [hyn]
    _ = (t * n i) * y * u'' * b₂ := by group
    _ = (n i * t') * y * u'' * b₂ := by rw [ht'n]
    _ = n i * (t' * y) * u'' * b₂ := by group
    _ = n i * (y' * t') * u'' * b₂ := by rw [hy't]
    _ = n i * y' * t' * u'' * b₂ := by group
    _ = (n i * y' * (n i)⁻¹) * n i * (t' * u'' * b₂) := by group
    _ = x'' * n i * b := by rw [← hx''_def, ← hb_def]

include hext hw₀ hsq in
theorem stdFix_mem_cell_iff (hBU : BruhatExtras D H) (L : StdLevi F (nrep hct w₀))
    (i : Fin D.rank) {g : K} (hg : g ∈ stdFix F (nrep hct w₀)) :
    (g ∈ bruhatCell hct 1 ∨ g ∈ bruhatCell hct ((cs).simple i)) ↔
      g ∈ (borel D H ⊓ stdFix F (nrep hct w₀)) ⊔ (slSU L.θ 2).map (L.ε i) := by
  classical
  constructor
  · rintro (hgB | hgcell)
    · have hgB' : g ∈ (borel D H : Set K) := bruhatCell_one hct ▸ hgB
      exact Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hgB', hg⟩)
    · obtain ⟨x', hx', b', hb', hg_eq⟩ :=
        hmbPan_cell_simple_eq (hct := hct) (hext := hext) i hgcell
      obtain ⟨c, hc⟩ : ∃ c, L.ε i (sl2Upper c) = x' := by
        have : x' ∈ Set.range (fun c => L.ε i (sl2Upper c)) := by
          rw [L.upper i]
          exact hx'
        exact this
      let w2 : SL(2, L.Fld) := sl2Upper (1 : L.Fld) * sl2Lower (-1) * sl2Upper 1
      let C : SL(2, L.Fld) := sl2Upper c * w2
      have hC : L.ε i C = x' * n i := by
        show L.ε i (sl2Upper c * w2) = x' * n i
        rw [map_mul, hc]
        congr 1
        exact L.weyl i
      have hg_eq' : g = L.ε i C * b' := by rw [hg_eq, hC]
      have hM : (((C⁻¹ * slSigma L.θ 2 C : SL(2, L.Fld))) :
          Matrix (Fin 2) (Fin 2) L.Fld) 1 1 ≠ 0 := by
        intro hM0
        set M : SL(2, L.Fld) := C⁻¹ * slSigma L.θ 2 C with hM_def
        have hM0' : (M : Matrix (Fin 2) (Fin 2) L.Fld) 1 1 = 0 := by
          simpa only [hM_def] using hM0
        have hτg : stdTau F (nrep hct w₀) g = g := hg
        have h1 : L.ε i (slSigma L.θ 2 C) * stdTau F (nrep hct w₀) b' = L.ε i C * b' := by
          rw [hg_eq'] at hτg
          rwa [map_mul, L.stdTau_ε i C] at hτg
        have hzτ : L.ε i M = b' * (stdTau F (nrep hct w₀) b')⁻¹ := by
          rw [hM_def, map_mul, map_inv]
          calc (L.ε i C)⁻¹ * L.ε i (slSigma L.θ 2 C)
              = (L.ε i C)⁻¹ * (L.ε i (slSigma L.θ 2 C) * stdTau F (nrep hct w₀) b') *
                  (stdTau F (nrep hct w₀) b')⁻¹ := by group
            _ = (L.ε i C)⁻¹ * (L.ε i C * b') * (stdTau F (nrep hct w₀) b')⁻¹ := by rw [h1]
            _ = b' * (stdTau F (nrep hct w₀) b')⁻¹ := by group
        let β : SL(2, L.Fld) := M * w2⁻¹
        have hβ : β ∈ sl2Borel L.Fld := by
          show (β : Matrix (Fin 2) (Fin 2) L.Fld) 1 0 = 0
          have hcoe : (β : Matrix (Fin 2) (Fin 2) L.Fld) =
              (M : Matrix (Fin 2) (Fin 2) L.Fld) * !![0, -1; 1, 0] := by
            rw [show β = M * w2⁻¹ from rfl, Matrix.SpecialLinearGroup.coe_mul,
              hmbPan_w2_inv_coe (hct := hct) (F := F) L]
          rw [hcoe, Matrix.mul_apply, Fin.sum_univ_two]
          simp [hM0']
        have hMβ : M = β * w2 := by
          rw [show β = M * w2⁻¹ from rfl]
          group
        have hzβ : L.ε i M = L.ε i β * n i := by
          rw [hMβ, map_mul, L.weyl i]
        have hτinv : (stdTau F (nrep hct w₀) b')⁻¹ =
            nrep hct w₀ * (F.φ b')⁻¹ * (nrep hct w₀)⁻¹ := by
          rw [stdTau_apply]
          group
        have hφb'B : F.φ b' ∈ borel D H := (F.mem_borel_iff b').2 hb'
        have hder : n i * nrep hct w₀ =
            (L.ε i β)⁻¹ * b' * nrep hct w₀ * (F.φ b')⁻¹ := by
          have heq : L.ε i β * n i =
              b' * nrep hct w₀ * (F.φ b')⁻¹ * (nrep hct w₀)⁻¹ := by
            rw [← hzβ, hzτ, hτinv]
            group
          calc n i * nrep hct w₀ =
                (L.ε i β)⁻¹ * (L.ε i β * n i) * nrep hct w₀ := by group
            _ = (L.ε i β)⁻¹ * (b' * nrep hct w₀ * (F.φ b')⁻¹ * (nrep hct w₀)⁻¹) *
                  nrep hct w₀ := by rw [heq]
            _ = (L.ε i β)⁻¹ * b' * nrep hct w₀ * (F.φ b')⁻¹ := by group
        have hcell : n i * nrep hct w₀ ∈ bruhatCell hct w₀ :=
          ⟨(L.ε i β)⁻¹ * b',
            mul_mem (inv_mem (hmbPan_sl2Borel_mem (hct := hct) (F := F) L i hβ)) hb',
            (F.φ b')⁻¹, inv_mem hφb'B, hder⟩
        have hdes : (cs).IsLeftDescent w₀ i := hw₀.isLeftDescent (Set.mem_univ i)
        have hlen : (cs).length ((cs).simple i * ((cs).simple i * w₀)) =
            (cs).length ((cs).simple i) + (cs).length ((cs).simple i * w₀) := by
          rw [(cs).length_simple i, (cs).simple_mul_simple_cancel_left i]
          have h := (cs).isLeftDescent_iff.mp hdes
          omega
        have hn₀ : nrep hct w₀ = n i * nrep hct ((cs).simple i * w₀) := by
          have h := nrep_mul hct hlen
          rw [(cs).simple_mul_simple_cancel_left i, nrep_simple hct i] at h
          exact h
        have hnrep : n i * nrep hct w₀ = nrep hct ((cs).simple i * w₀) := by
          rw [hn₀, ← mul_assoc, hsq i, one_mul]
        have hcell' : n i * nrep hct w₀ ∈ bruhatCell hct ((cs).simple i * w₀) := by
          rw [hnrep]
          exact nrep_mem_bruhatCell hct _
        have heq2 : w₀ = (cs).simple i * w₀ := eq_of_mem_bruhatCell hct hext hcell hcell'
        exact (cs).simple_ne_one i (mul_right_cancel (show (cs).simple i * w₀ = 1 * w₀ by
          rw [one_mul]
          exact heq2.symm))
      obtain ⟨b₂, hb₂, hfix⟩ := exists_mul_mem_slSU L.θ L.θ_invol L.norm_surj C hM
      have hb₂B : L.ε i b₂ ∈ borel D H :=
        hmbPan_sl2Borel_mem (hct := hct) (F := F) L i hb₂
      have hvfix : L.ε i (C * b₂) ∈ stdFix F (nrep hct w₀) :=
        (L.ε_mem_stdFix_iff i (C * b₂)).2 hfix
      have hv : L.ε i (C * b₂) ∈ (slSU L.θ 2).map (L.ε i) :=
        Subgroup.mem_map.2 ⟨C * b₂, hfix, rfl⟩
      have hvinv : (L.ε i (C * b₂))⁻¹ * g ∈
          borel D H ⊓ stdFix F (nrep hct w₀) := by
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · have h : (L.ε i (C * b₂))⁻¹ * g = (L.ε i b₂)⁻¹ * b' := by
            rw [hg_eq', map_mul]
            group
          rw [h]
          exact mul_mem (inv_mem hb₂B) hb'
        · exact mul_mem (inv_mem hvfix) hg
      have hgdecomp : g = L.ε i (C * b₂) * ((L.ε i (C * b₂))⁻¹ * g) := by group
      rw [hgdecomp, sup_comm]
      exact Subgroup.mul_mem_sup hv hvinv
  · intro hg'
    obtain ⟨P, hP, _⟩ := std_residue_mk hct hext ({i} : Set (Fin D.rank))
    have himage : (cs).simple '' ({i} : Set (Fin D.rank)) = ({(cs).simple i} : Set W) := by
      ext w
      simp
    have hBP : borel D H ≤ P := by
      intro b hb
      show b ∈ (P : Set K)
      rw [hP, himage]
      exact Set.mem_iUnion.2 ⟨1, Set.mem_iUnion.2 ⟨Subgroup.one_mem _,
        by rw [bruhatCell_one hct]; exact hb⟩⟩
    have hnP : n i ∈ P := by
      show n i ∈ (P : Set K)
      rw [hP, himage]
      refine Set.mem_iUnion.2 ⟨(cs).simple i, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
      · exact Subgroup.subset_closure (by simp)
      · rw [← nrep_simple hct i]
        exact nrep_mem_bruhatCell hct _
    have hRangeP : (L.ε i).range ≤ P :=
      hmbPan_range_le (hct := hct) (F := F) L i hBP hnP
    have hle : (borel D H ⊓ stdFix F (nrep hct w₀)) ⊔ (slSU L.θ 2).map (L.ε i) ≤ P :=
      sup_le (inf_le_left.trans hBP) ((Subgroup.map_le_range (f := L.ε i) (slSU L.θ 2)).trans
        hRangeP)
    have hgP : g ∈ P := hle hg'
    have hgP' : g ∈ (P : Set K) := hgP
    rw [hP, himage] at hgP'
    obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hgP'
    obtain ⟨hwcl, hgw⟩ := Set.mem_iUnion.1 hw
    rw [hmbPan_mem_closure_simple (D := D) i w] at hwcl
    rcases hwcl with rfl | rfl
    · exact Or.inl hgw
    · exact Or.inr hgw

end CFSG.ClassicalInvolution.Phan.PhanE
