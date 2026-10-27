module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12Objects
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalSection
public import CFSG.CharacterTheory.Semidihedral.CentralizerAlternatives
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels


@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Sporadic.J2.Module12
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Blueprint
private noncomputable def addHomOfAut (x : MulAut W12) : V12 →+ V12 where
  toFun v := Multiplicative.toAdd (x (Multiplicative.ofAdd v))
  map_zero' := by simp
  map_add' a b := by
    show Multiplicative.toAdd (x (Multiplicative.ofAdd (a + b))) =
      Multiplicative.toAdd (x (Multiplicative.ofAdd a)) +
        Multiplicative.toAdd (x (Multiplicative.ofAdd b))
    rw [show Multiplicative.ofAdd (a + b) =
      Multiplicative.ofAdd a * Multiplicative.ofAdd b from rfl, map_mul]
    rfl
private noncomputable def hjLinOfAut (x : MulAut W12) : V12 →ₗ[ZMod 2] V12 where
  toFun v := Multiplicative.toAdd (x (Multiplicative.ofAdd v))
  map_add' := (addHomOfAut x).map_add
  map_smul' := by
    intro c v
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) c with rfl | rfl <;> simp
private lemma hjLinOfAut_apply (x : MulAut W12) (v : V12) :
    hjLinOfAut x v = Multiplicative.toAdd (x (Multiplicative.ofAdd v)) := rfl
private lemma exists_scalar_of_mem_centralizer {x : MulAut W12}
    (hx : x ∈ Subgroup.centralizer (hjL0 : Set (MulAut W12))) :
    ∃ α : F4, α ≠ 0 ∧ ∀ v : V12, hjLinOfAut x v = α • v := by
  classical
  letI : AddCommGroup V12 := CFSG.Sporadic.J2.Module12.instAddCommGroupV12
  letI : Module F4 V12 := CFSG.Sporadic.J2.Module12.instModuleF4
  let F : V12 →ₗ[ZMod 2] V12 := hjLinOfAut x
  let X : Matrix (Fin 12) (Fin 12) (ZMod 2) := LinearMap.toMatrix' F
  have hxcomm : ∀ y ∈ hjL0, y * x = x * y := fun y hy =>
    Subgroup.mem_centralizer_iff.mp hx y hy
  have hxA : F.comp (Matrix.mulVecLin (A12 : Matrix (Fin 12) (Fin 12) (ZMod 2))) =
      (Matrix.mulVecLin (A12 : Matrix (Fin 12) (Fin 12) (ZMod 2))).comp F := by
    apply LinearMap.ext
    intro v
    change hjLinOfAut x ((Matrix.mulVecLin (A12 : Matrix (Fin 12) (Fin 12) (ZMod 2))) v) =
      (Matrix.mulVecLin (A12 : Matrix (Fin 12) (Fin 12) (ZMod 2))) (hjLinOfAut x v)
    have h := congrArg (fun φ : MulAut W12 => φ (Multiplicative.ofAdd v))
      (hxcomm (hjAct A12) hjAct_A12_mem)
    have h' : Multiplicative.toAdd (hjAct A12 (x (Multiplicative.ofAdd v))) =
        Multiplicative.toAdd (x (hjAct A12 (Multiplicative.ofAdd v))) :=
      congrArg Multiplicative.toAdd h
    have h2 : (A12 : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
          (Multiplicative.toAdd (x (Multiplicative.ofAdd v))) =
        Multiplicative.toAdd (hjAct A12 (x (Multiplicative.ofAdd v))) := by
      rw [show x (Multiplicative.ofAdd v) = Multiplicative.ofAdd
        (Multiplicative.toAdd (x (Multiplicative.ofAdd v))) from rfl]
      rw [hjAct_apply]
      simp
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hjLinOfAut_apply,
      hjLinOfAut_apply, h2]
    exact h'.symm
  have hxB : F.comp (Matrix.mulVecLin (B12 : Matrix (Fin 12) (Fin 12) (ZMod 2))) =
      (Matrix.mulVecLin (B12 : Matrix (Fin 12) (Fin 12) (ZMod 2))).comp F := by
    apply LinearMap.ext
    intro v
    change hjLinOfAut x ((Matrix.mulVecLin (B12 : Matrix (Fin 12) (Fin 12) (ZMod 2))) v) =
      (Matrix.mulVecLin (B12 : Matrix (Fin 12) (Fin 12) (ZMod 2))) (hjLinOfAut x v)
    have h := congrArg (fun φ : MulAut W12 => φ (Multiplicative.ofAdd v))
      (hxcomm (hjAct B12) hjAct_B12_mem)
    have h' : Multiplicative.toAdd (hjAct B12 (x (Multiplicative.ofAdd v))) =
        Multiplicative.toAdd (x (hjAct B12 (Multiplicative.ofAdd v))) :=
      congrArg Multiplicative.toAdd h
    have h2 : (B12 : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
          (Multiplicative.toAdd (x (Multiplicative.ofAdd v))) =
        Multiplicative.toAdd (hjAct B12 (x (Multiplicative.ofAdd v))) := by
      rw [show x (Multiplicative.ofAdd v) = Multiplicative.ofAdd
        (Multiplicative.toAdd (x (Multiplicative.ofAdd v))) from rfl]
      rw [hjAct_apply]
      simp
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hjLinOfAut_apply,
      hjLinOfAut_apply, h2]
    exact h'.symm
  have hAmat : LinearMap.toMatrix'
      (Matrix.mulVecLin (A12 : Matrix (Fin 12) (Fin 12) (ZMod 2))) = A12 := by
    change LinearMap.toMatrix' (Matrix.toLin'
      (A12 : Matrix (Fin 12) (Fin 12) (ZMod 2))) = A12
    exact LinearMap.toMatrix'_toLin' _
  have hBmat : LinearMap.toMatrix'
      (Matrix.mulVecLin (B12 : Matrix (Fin 12) (Fin 12) (ZMod 2))) = B12 := by
    change LinearMap.toMatrix' (Matrix.toLin'
      (B12 : Matrix (Fin 12) (Fin 12) (ZMod 2))) = B12
    exact LinearMap.toMatrix'_toLin' _
  have hXA : X * (A12 : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      (A12 : Matrix (Fin 12) (Fin 12) (ZMod 2)) * X := by
    have h := congrArg (fun f : V12 →ₗ[ZMod 2] V12 => LinearMap.toMatrix' f) hxA
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, hAmat] at h
    simpa [X] using h
  have hXB : X * (B12 : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      (B12 : Matrix (Fin 12) (Fin 12) (ZMod 2)) * X := by
    have h := congrArg (fun f : V12 →ₗ[ZMod 2] V12 => LinearMap.toMatrix' f) hxB
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, hBmat] at h
    simpa [X] using h
  have hAalg : Aalg ≤ Subalgebra.centralizer (ZMod 2)
      ({X} : Set (Matrix (Fin 12) (Fin 12) (ZMod 2))) := by
    rw [Aalg]
    refine Algebra.adjoin_le ?_
    rintro Y (rfl | rfl)
    · change Amat ∈ Subalgebra.centralizer (ZMod 2)
        ({X} : Set (Matrix (Fin 12) (Fin 12) (ZMod 2)))
      rw [Subalgebra.mem_centralizer_iff]
      intro Z hZ
      rw [Set.mem_singleton_iff] at hZ
      subst hZ
      rw [Amat_eq]
      exact hXA
    · change Bmat ∈ Subalgebra.centralizer (ZMod 2)
        ({X} : Set (Matrix (Fin 12) (Fin 12) (ZMod 2)))
      rw [Subalgebra.mem_centralizer_iff]
      intro Z hZ
      rw [Set.mem_singleton_iff] at hZ
      subst hZ
      rw [Bmat_eq]
      exact hXB
  have hCX : ∀ Y ∈ CJ, Y * X = X * Y := by
    intro Y hY
    have hYA : Y ∈ (Aalg : Set (Matrix (Fin 12) (Fin 12) (ZMod 2))) := by
      rw [Aalg_eq_CJ]
      exact hY
    have hmem : Y ∈ Subalgebra.centralizer (ZMod 2)
        ({X} : Set (Matrix (Fin 12) (Fin 12) (ZMod 2))) := hAalg hYA
    rw [Subalgebra.mem_centralizer_iff] at hmem
    exact (hmem X (Set.mem_singleton X)).symm
  have hJmX : X * Jm = Jm * X := by
    have hmem : Jm ∈ Subalgebra.centralizer (ZMod 2)
        ({X} : Set (Matrix (Fin 12) (Fin 12) (ZMod 2))) := hAalg Jm_mem_Aalg
    rw [Subalgebra.mem_centralizer_iff] at hmem
    exact hmem X (Set.mem_singleton X)
  have hJ : ∀ v : V12, F (Jlin v) = Jlin (F v) := by
    intro v
    rw [Jlin_apply, Jlin_apply]
    calc F (Matrix.mulVec Jm v)
        = Matrix.mulVec X (Matrix.mulVec Jm v) :=
          (LinearMap.toMatrix'_mulVec F (Matrix.mulVec Jm v)).symm
      _ = Matrix.mulVec (X * Jm) v := Matrix.mulVec_mulVec v X Jm
      _ = Matrix.mulVec (Jm * X) v := by rw [hJmX]
      _ = Matrix.mulVec Jm (Matrix.mulVec X v) := (Matrix.mulVec_mulVec v Jm X).symm
      _ = Matrix.mulVec Jm (F v) := by rw [LinearMap.toMatrix'_mulVec]
  let f₄ : V12 →ₗ[F4] V12 :=
    { toFun := F
      map_add' := F.map_add
      map_smul' := by
        intro c v
        rw [smul_F4_def, smul_F4_def, F.map_add, F.map_smul, F.map_smul, hJ v]
        simp }
  have hF : ∀ v : V12, f₄ v = Matrix.mulVec X v := fun v =>
    (LinearMap.toMatrix'_mulVec F v).symm
  have hcenter : f₄ ∈ Set.center (Module.End F4 V12) := by
    rw [Semigroup.mem_center_iff]
    intro g
    apply LinearMap.ext
    intro v
    obtain ⟨Y, hY, hYg⟩ := exists_mem_CJ_of_linearMap g
    calc (g * f₄) v = g (f₄ v) := rfl
      _ = Matrix.mulVec Y (f₄ v) := (hYg (f₄ v)).symm
      _ = Matrix.mulVec Y (Matrix.mulVec X v) := by rw [hF v]
      _ = Matrix.mulVec (Y * X) v := Matrix.mulVec_mulVec v Y X
      _ = Matrix.mulVec (X * Y) v := by rw [hCX Y hY]
      _ = Matrix.mulVec X (Matrix.mulVec Y v) := (Matrix.mulVec_mulVec v X Y).symm
      _ = Matrix.mulVec X (g v) := by rw [hYg v]
      _ = f₄ (g v) := (hF (g v)).symm
      _ = (f₄ * g) v := rfl
  have : Module.Free F4 V12 := inferInstance
  obtain ⟨α, hα, hαf⟩ := Module.End.mem_center_iff.mp hcenter
  have hαapply : ∀ v : V12, f₄ v = α • v := by
    intro v
    rw [hαf]
    exact Module.End.smulLeft_apply α hα v
  have hinj : Function.Injective f₄ := by
    intro a b hab
    have h1 : x (Multiplicative.ofAdd a) = x (Multiplicative.ofAdd b) :=
      Multiplicative.ofAdd.injective hab
    exact Multiplicative.ofAdd.injective (x.injective h1)
  have hα0 : α ≠ 0 := by
    intro h0
    have h1 : f₄ (0 : V12) = f₄ (Pi.single (0 : Fin 12) (1 : ZMod 2)) := by
      rw [hαapply, hαapply, h0]
      exact (zero_smul F4
        (Pi.single (0 : Fin 12) (1 : ZMod 2) : V12)).symm
    have h2 : (0 : V12) = Pi.single (0 : Fin 12) (1 : ZMod 2) := hinj h1
    have h3 : (Pi.single (0 : Fin 12) (1 : ZMod 2) : V12) ≠ 0 := by
      intro h
      have := congrFun h (0 : Fin 12)
      simp at this
    exact h3 h2.symm
  exact ⟨α, hα0, hαapply⟩
theorem centralizer_hjL0 :
    Subgroup.centralizer (hjL0 : Set (MulAut W12)) = Subgroup.zpowers hjOmega := by
  classical
  let C : Subgroup (MulAut W12) := Subgroup.centralizer (hjL0 : Set (MulAut W12))
  have hmain : ∀ x : ↥C, ∃ α : F4, α ≠ 0 ∧
      ∀ v : V12, hjLinOfAut x.1 v = α • v := fun x =>
    exists_scalar_of_mem_centralizer x.2
  let α : ↥C → F4 := fun x => (hmain x).choose
  have hα0 : ∀ x, α x ≠ 0 := fun x => (hmain x).choose_spec.1
  have hαact : ∀ (x : ↥C) (v : V12), hjLinOfAut x.1 v = α x • v := fun x =>
    (hmain x).choose_spec.2
  let toUnit : ↥C → F4ˣ := fun x => Units.mk0 (α x) (hα0 x)
  have hinj : Function.Injective toUnit := by
    intro x y hxy
    have hαxy : α x = α y := by
      have := congrArg (fun u : F4ˣ => (u : F4)) hxy
      simpa [toUnit] using this
    apply Subtype.ext
    apply MulEquiv.ext
    intro w
    have hlin : hjLinOfAut x.1 = hjLinOfAut y.1 := by
      apply LinearMap.ext
      intro v
      rw [hαact x v, hαact y v, hαxy]
    have hpoint : ∀ v : V12,
        x.1 (Multiplicative.ofAdd v) = y.1 (Multiplicative.ofAdd v) := by
      intro v
      have := congrArg (fun f : V12 →ₗ[ZMod 2] V12 => f v) hlin
      exact Multiplicative.ofAdd.injective this
    simpa using hpoint (Multiplicative.toAdd w)
  have hcard : Nat.card ↥C ≤ Nat.card F4ˣ :=
    Nat.card_le_card_of_injective toUnit hinj
  have hunits : Nat.card F4ˣ = 3 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card, CFSG.F4.card]
  have hC3 : Nat.card ↥C ≤ 3 := by rwa [hunits] at hcard
  have hle : Subgroup.zpowers hjOmega ≤ C :=
    Subgroup.zpowers_le.2 hjOmega_mem_centralizer
  have hcard' : Nat.card ↥C ≤ Nat.card ↥(Subgroup.zpowers hjOmega) := by
    rw [Nat.card_zpowers, orderOf_hjOmega]
    exact hC3
  exact (Subgroup.eq_of_le_of_card_ge hle hcard').symm

private lemma map_ker_conjNormal_le_centralizer {Y : Subgroup (MulAut W12)}
    (hLY : hjL0 ≤ Y) [hN : (hjL0.subgroupOf Y).Normal] :
    Subgroup.map (Subgroup.subtype Y)
      (MonoidHom.ker (MulAut.conjNormal (H := hjL0.subgroupOf Y))) ≤
      Subgroup.centralizer (hjL0 : Set (MulAut W12)) := by
  classical
  rintro _ ⟨g, hg, rfl⟩
  rw [CFSG.Semidihedral.CentralizerAlternatives.conjNormal_ker
    (hjL0.subgroupOf Y)] at hg
  have hg' : ∀ h ∈ (hjL0.subgroupOf Y : Set ↥Y), h * g = g * h :=
    Subgroup.mem_centralizer_iff.mp hg
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  let h : hjL0.subgroupOf Y := ⟨⟨l, hLY hl⟩, hl⟩
  have hcomm := hg' h h.2
  have := congrArg (Subgroup.subtype Y) hcomm
  simpa [h] using this
theorem card_dvd_six_mul_of_normal
    {Y : Subgroup (MulAut W12)} (hLY : hjL0 ≤ Y)
    (hN : (hjL0.subgroupOf Y).Normal) : Nat.card Y ∣ 6 * Nat.card hjL0 := by
  classical
  have : (hjL0.subgroupOf Y).Normal := hN
  let H : Subgroup ↥Y := hjL0.subgroupOf Y
  let φ : ↥Y →* MulAut ↥H := MulAut.conjNormal
  have hker3 : Nat.card ↥(MonoidHom.ker φ) ∣ 3 := by
    have hle := map_ker_conjNormal_le_centralizer (Y := Y) hLY
    rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective Y)]
    calc Nat.card ↥(Subgroup.map (Subgroup.subtype Y) (MonoidHom.ker φ)) ∣
          Nat.card ↥(Subgroup.centralizer (hjL0 : Set (MulAut W12))) :=
          Subgroup.card_dvd_of_le hle
      _ = 3 := by rw [centralizer_hjL0, Nat.card_zpowers, orderOf_hjOmega]
  obtain ⟨eJ⟩ := hjL0_isSpor
  let eH : ↥H ≃* NativeSporadic.J2 := (Subgroup.subgroupOfEquivOfLe hLY).trans eJ
  have hHcard : Nat.card ↥H = Nat.card hjL0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLY).toEquiv
  have : Finite ↥H := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_congr eH.toEquiv, CFSG.Sporadic.J2.card_J2]
    norm_num)
  have hAutH : Nat.card (MulAut ↥H) = 2 * Nat.card hjL0 := by
    calc Nat.card (MulAut ↥H) = Nat.card (MulAut NativeSporadic.J2) :=
          Nat.card_congr (MulAut.congr eH).toEquiv
      _ = 2 * Nat.card NativeSporadic.J2 :=
          CFSG.ComponentClassification.J2Cover.j2_mulAut_card
      _ = 2 * Nat.card hjL0 := by rw [← Nat.card_congr eH.toEquiv, hHcard]
  have hrange : Nat.card ↥(MonoidHom.range φ) ∣ 2 * Nat.card hjL0 :=
    (Subgroup.card_subgroup_dvd_card (MonoidHom.range φ)).trans (by rw [hAutH])
  have hcard : Nat.card ↥Y = Nat.card ↥(MonoidHom.ker φ) *
      Nat.card ↥(MonoidHom.range φ) := (Subgroup.card_ker_mul_card_range φ).symm
  rw [hcard]
  calc Nat.card ↥(MonoidHom.ker φ) * Nat.card ↥(MonoidHom.range φ) ∣
        3 * (2 * Nat.card hjL0) := Nat.mul_dvd_mul hker3 hrange
    _ = 6 * Nat.card hjL0 := by ring
theorem sq_mem_of_normal
    {Y : Subgroup (MulAut W12)} (hLY : hjL0 ≤ Y)
    (hN : (hjL0.subgroupOf Y).Normal) {y : MulAut W12} (hy : y ∈ Y) :
    ∃ l ∈ hjL0, ∃ c ∈ Subgroup.zpowers hjOmega, y ^ 2 = l * c := by
  classical
  have : (hjL0.subgroupOf Y).Normal := hN
  let H : Subgroup ↥Y := hjL0.subgroupOf Y
  let φ : ↥Y →* MulAut ↥H := MulAut.conjNormal
  obtain ⟨eJ⟩ := hjL0_isSpor
  let eP : ↥H ≃* CFSG.ComponentClassification.J2Cover.P :=
    (Subgroup.subgroupOfEquivOfLe hLY).trans
      (eJ.trans CFSG.ComponentClassification.J2Cover.nativeEquivP)
  have : Finite ↥H := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_congr eP.toEquiv, CFSG.ComponentClassification.J2Cover.card_P]
    norm_num)
  have hAutH : Nat.card (MulAut ↥H) = 2 * Nat.card ↥H := by
    calc Nat.card (MulAut ↥H) =
          Nat.card (MulAut CFSG.ComponentClassification.J2Cover.P) :=
          Nat.card_congr (MulAut.congr eP).toEquiv
      _ = 2 * Nat.card CFSG.ComponentClassification.J2Cover.P := by
          rw [CFSG.ComponentClassification.J2Cover.card_mulAut_P,
            CFSG.ComponentClassification.J2Cover.card_P]
      _ = 2 * Nat.card ↥H := by rw [Nat.card_congr eP.toEquiv]
  have hcenter : Subgroup.center ↥H = ⊥ :=
    CFSG.ComponentClassification.J2Cover.External.center_eq_bot_of_mulEquiv eP
      CFSG.ComponentClassification.J2Cover.center_P
  let Inn : Subgroup (MulAut ↥H) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner ↥H
  have hinner : Nat.card ↥Inn = Nat.card ↥H := by
    simpa [Inn] using CFSG.Sporadic.Schreier.card_inner_of_center_eq_bot hcenter
  have hindex : Inn.index = 2 := by
    have h := Subgroup.index_mul_card (H := Inn)
    rw [hinner, hAutH] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  let gy : ↥Y := ⟨y, hy⟩
  have hsq : (φ gy) ^ 2 ∈ Inn := Subgroup.sq_mem_of_index_two hindex (φ gy)
  have hInn : Inn = (MulAut.conj : ↥H →* MulAut ↥H).range := rfl
  rw [hInn, MonoidHom.mem_range] at hsq
  obtain ⟨h, hh⟩ := hsq
  let l : MulAut W12 := h
  have hl : l ∈ hjL0 := h.2
  have hlY : l ∈ Y := hLY hl
  have hker : φ ((⟨l, hlY⟩ : ↥Y)⁻¹ * gy ^ 2) = 1 := by
    rw [map_mul, map_inv, map_pow]
    have h1 : φ (⟨l, hlY⟩ : ↥Y) = MulAut.conj h := by
      change MulAut.conjNormal (⟨l, hlY⟩ : ↥Y) = MulAut.conj h
      rw [show (⟨l, hlY⟩ : ↥Y) = (h : ↥Y) from Subtype.ext rfl]
      exact MulAut.conjNormal_val
    rw [h1, ← hh, inv_mul_cancel]
  let c : MulAut W12 := l⁻¹ * y ^ 2
  have hcKer : c ∈ Subgroup.map (Subgroup.subtype Y) (MonoidHom.ker φ) := by
    refine ⟨(⟨l, hlY⟩ : ↥Y)⁻¹ * gy ^ 2, ?_, ?_⟩
    · change φ ((⟨l, hlY⟩ : ↥Y)⁻¹ * gy ^ 2) = 1
      exact hker
    · simp [c, gy, l]
  have hcOmega : c ∈ Subgroup.zpowers hjOmega := by
    rw [← centralizer_hjL0]
    exact map_ker_conjNormal_le_centralizer (Y := Y) hLY hcKer
  exact ⟨l, hl, c, hcOmega, by
    rw [show c = l⁻¹ * y ^ 2 from rfl]
    group⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
