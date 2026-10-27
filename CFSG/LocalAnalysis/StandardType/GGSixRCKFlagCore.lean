module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKFlagDefs
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner
public import TauCeti.RepresentationTheory.Unipotent.PowerOrder
public import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.RCKFlag

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.StandardType.RCKC1 CFSG.Open

theorem trivial_on_of_irred {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] [CharP F 2] (j : U →* GL ι F) (C T : Subgroup U) (hTC : T ≤ C)
    (hTn : ∀ c ∈ C, ∀ t ∈ T, c * t * c⁻¹ ∈ T) (hT : IsPGroup 2 T) (W : Submodule F (ι → F))
    (hW : ∀ c ∈ C, ∀ x ∈ W, (j c : Matrix ι ι F).mulVec x ∈ W)
    (hirr : ∀ P : Submodule F (ι → F), P ≤ W →
      (∀ c ∈ C, ∀ x ∈ P, (j c : Matrix ι ι F).mulVec x ∈ P) → P = ⊥ ∨ P = W) :
    ∀ t ∈ T, ∀ w ∈ W, (j t : Matrix ι ι F).mulVec w = w := by
  intro t ht w hw
  by_cases hWbot : W = ⊥
  · have hw0 : w = 0 := by
      rw [hWbot] at hw
      simpa using hw
    rw [hw0, Matrix.mulVec_zero]
  · haveI : Nontrivial W := (Submodule.nontrivial_iff_ne_bot (p := W)).mpr hWbot
    haveI : ExpChar F 2 := expChar_prime F 2
    haveI : FiniteDimensional F W := FiniteDimensional.finiteDimensional_submodule W
    let ρ : Representation F T W :=
      { toFun := fun t =>
          { toFun := fun w =>
              ⟨(j (t : U) : Matrix ι ι F).mulVec w.1, hW (t : U) (hTC t.2) w.1 w.2⟩
            map_add' := by
              intro x y
              apply Subtype.ext
              simp [Matrix.mulVec_add]
            map_smul' := by
              intro a x
              apply Subtype.ext
              simp [Matrix.mulVec_smul] }
        map_one' := by
          ext w
          simp
        map_mul' := by
          intro s t
          ext w
          simp [Matrix.mulVec_mulVec, Module.End.mul_apply] }
    obtain ⟨v, hv0, hvfix⟩ :=
      Representation.exists_common_fixed_vector_of_isPGroup (k := F) (G := T) (V := W) 2 hT ρ
    let P : Submodule F (ι → F) :=
      { carrier := {x | x ∈ W ∧ ∀ t : T, (j (t : U) : Matrix ι ι F).mulVec x = x}
        zero_mem' := ⟨W.zero_mem, by intro t; simp⟩
        add_mem' := by
          intro x y hx hy
          refine ⟨W.add_mem hx.1 hy.1, fun t => ?_⟩
          rw [Matrix.mulVec_add, hx.2 t, hy.2 t]
        smul_mem' := by
          intro a x hx
          refine ⟨W.smul_mem a hx.1, fun t => ?_⟩
          rw [Matrix.mulVec_smul, hx.2 t] }
    have hPinv : ∀ c ∈ C, ∀ x ∈ P, (j c : Matrix ι ι F).mulVec x ∈ P := by
      intro c hc x hx
      refine ⟨hW c hc x hx.1, fun t => ?_⟩
      have hconj : c⁻¹ * (t : U) * c ∈ T := by
        simpa using hTn c⁻¹ (inv_mem hc) (t : U) t.2
      have hmul : (j (t : U) : Matrix ι ι F) * (j c : Matrix ι ι F)
          = (j c : Matrix ι ι F) * (j (c⁻¹ * (t : U) * c) : Matrix ι ι F) := by
        rw [← Matrix.GeneralLinearGroup.coe_mul, ← Matrix.GeneralLinearGroup.coe_mul,
          ← map_mul, ← map_mul,
          show (t : U) * c = c * (c⁻¹ * (t : U) * c) by group]
      calc (j (t : U) : Matrix ι ι F).mulVec ((j c : Matrix ι ι F).mulVec x)
          = ((j (t : U) : Matrix ι ι F) * (j c : Matrix ι ι F)).mulVec x := by
            rw [Matrix.mulVec_mulVec]
        _ = ((j c : Matrix ι ι F) * (j (c⁻¹ * (t : U) * c) : Matrix ι ι F)).mulVec x := by
            rw [hmul]
        _ = (j c : Matrix ι ι F).mulVec ((j (c⁻¹ * (t : U) * c) : Matrix ι ι F).mulVec x) := by
            rw [Matrix.mulVec_mulVec]
        _ = (j c : Matrix ι ι F).mulVec x := by
            rw [hx.2 ⟨c⁻¹ * (t : U) * c, hconj⟩]
    have hvP : v.1 ∈ P := by
      refine ⟨v.2, fun t => ?_⟩
      exact congrArg Subtype.val (hvfix t)
    have hPne : P ≠ ⊥ := by
      intro hbot
      apply hv0
      apply Subtype.ext
      have : v.1 ∈ (⊥ : Submodule F (ι → F)) := by rw [← hbot]; exact hvP
      simpa using this
    rcases hirr P (fun x hx => hx.1) hPinv with hP | hP
    · exact absurd hP hPne
    · have : w ∈ P := by rw [hP]; exact hw
      exact this.2 ⟨t, ht⟩

theorem flagCent_of_trivial {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι] [Field F]
    (j : U →* GL ι F) (hj : Function.Injective j) (R' : Subgroup U) (W H : Submodule F (ι → F))
    (hv : ∀ v ∈ R', v ≠ 1 →
      LinearMap.range (Matrix.toLin' ((j v : Matrix ι ι F) - 1)) = W ∧
      LinearMap.ker (Matrix.toLin' ((j v : Matrix ι ι F) - 1)) = H)
    (r : U) (hr : r ∈ R') (hr1 : r ≠ 1) (T : Subgroup U)
    (hT : T ≤ Subgroup.centralizer ({r} : Set U))
    (hW : ∀ t ∈ T, ∀ w ∈ W, (j t : Matrix ι ι F).mulVec w = w) :
    T ≤ Subgroup.centralizer (R' : Set U) := by
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro v hvR
  by_cases hv1 : v = 1
  · subst v
    simp
  · have htr : t * r = r * t := Subgroup.mem_centralizer_singleton_iff.mp (hT ht)
    have htrM : (j t : Matrix ι ι F) * (j r : Matrix ι ι F)
        = (j r : Matrix ι ι F) * (j t : Matrix ι ι F) := by
      rw [← Matrix.GeneralLinearGroup.coe_mul, ← Matrix.GeneralLinearGroup.coe_mul,
        ← map_mul, ← map_mul, htr]
    have hNt : (j t : Matrix ι ι F) * ((j r : Matrix ι ι F) - 1)
        = ((j r : Matrix ι ι F) - 1) * (j t : Matrix ι ι F) := by
      calc (j t : Matrix ι ι F) * ((j r : Matrix ι ι F) - 1)
          = (j t : Matrix ι ι F) * (j r : Matrix ι ι F) - (j t : Matrix ι ι F) := by
            rw [mul_sub, mul_one]
        _ = (j r : Matrix ι ι F) * (j t : Matrix ι ι F) - (j t : Matrix ι ι F) := by rw [htrM]
        _ = ((j r : Matrix ι ι F) - 1) * (j t : Matrix ι ι F) := by rw [sub_mul, one_mul]
    have hrangeN : (Matrix.toLin' ((j r : Matrix ι ι F) - 1)).range = W := (hv r hr hr1).1
    have hkerN : (Matrix.toLin' ((j r : Matrix ι ι F) - 1)).ker = H := (hv r hr hr1).2
    have step1 : ∀ m : ι → F, ((j t : Matrix ι ι F) - 1).mulVec m ∈ H := by
      intro m
      rw [← hkerN, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.mulVec_mulVec]
      have hNX : ((j r : Matrix ι ι F) - 1) * ((j t : Matrix ι ι F) - 1)
          = ((j t : Matrix ι ι F) - 1) * ((j r : Matrix ι ι F) - 1) := by
        calc ((j r : Matrix ι ι F) - 1) * ((j t : Matrix ι ι F) - 1)
            = ((j r : Matrix ι ι F) - 1) * (j t : Matrix ι ι F)
                - ((j r : Matrix ι ι F) - 1) := by rw [mul_sub, mul_one]
          _ = (j t : Matrix ι ι F) * ((j r : Matrix ι ι F) - 1)
                - ((j r : Matrix ι ι F) - 1) := by rw [← hNt]
          _ = ((j t : Matrix ι ι F) * (j r : Matrix ι ι F) - (j t : Matrix ι ι F))
                - ((j r : Matrix ι ι F) - 1) := by rw [mul_sub, mul_one]
          _ = ((j t : Matrix ι ι F) - 1) * ((j r : Matrix ι ι F) - 1) := by
                rw [sub_mul, one_mul, mul_sub, mul_one]
      rw [hNX, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
      have hNW : ((j r : Matrix ι ι F) - 1).mulVec m ∈ W := by
        rw [← hrangeN]
        exact LinearMap.mem_range.mpr ⟨m, by rw [Matrix.toLin'_apply]⟩
      rw [hW t ht (((j r : Matrix ι ι F) - 1).mulVec m) hNW, sub_self]
    have hNv_comm : (j t : Matrix ι ι F) * ((j v : Matrix ι ι F) - 1)
        = ((j v : Matrix ι ι F) - 1) * (j t : Matrix ι ι F) := by
      apply Matrix.mulVec_injective
      funext m
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have hrangev : (Matrix.toLin' ((j v : Matrix ι ι F) - 1)).range = W := (hv v hvR hv1).1
      have hkerv : (Matrix.toLin' ((j v : Matrix ι ι F) - 1)).ker = H := (hv v hvR hv1).2
      have hNm : ((j v : Matrix ι ι F) - 1).mulVec m ∈ W := by
        rw [← hrangev]
        exact LinearMap.mem_range.mpr ⟨m, by rw [Matrix.toLin'_apply]⟩
      have hfix : (j t : Matrix ι ι F).mulVec (((j v : Matrix ι ι F) - 1).mulVec m)
          = ((j v : Matrix ι ι F) - 1).mulVec m := hW t ht _ hNm
      have hstep : ((j v : Matrix ι ι F) - 1).mulVec ((j t : Matrix ι ι F).mulVec m - m) = 0 := by
        have hx : ((j t : Matrix ι ι F) - 1).mulVec m = (j t : Matrix ι ι F).mulVec m - m := by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec]
        rw [← hx, ← Matrix.toLin'_apply, ← LinearMap.mem_ker, hkerv]
        exact step1 m
      have hsplit : ((j v : Matrix ι ι F) - 1).mulVec ((j t : Matrix ι ι F).mulVec m)
          = ((j v : Matrix ι ι F) - 1).mulVec m := by
        conv_lhs => rw [← sub_add_cancel ((j t : Matrix ι ι F).mulVec m) m]
        rw [Matrix.mulVec_add, hstep, zero_add]
      rw [hfix, hsplit]
    have hAB : (j t : Matrix ι ι F) * (j v : Matrix ι ι F)
        = (j v : Matrix ι ι F) * (j t : Matrix ι ι F) := by
      have h := hNv_comm
      rw [mul_sub, sub_mul, mul_one, one_mul] at h
      have h2 := congrArg (fun x => x + (j t : Matrix ι ι F)) h
      simpa [sub_add_cancel] using h2
    have hcommGL : j t * j v = j v * j t := by
      apply Matrix.GeneralLinearGroup.ext
      intro i k
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
      exact congrFun (congrFun hAB i) k
    have htv : t * v = v * t := by
      have : j (t * v) = j (v * t) := by rw [map_mul, map_mul, hcommGL]
      exact hj this
    exact htv.symm

theorem flagCentU_of_irredW {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] [CharP F 2] (j : U →* GL ι F) (B : Option ((ι → F) → (ι → F) → F))
    (hj : Function.Injective j) (h : FlagIrredW j B) : FlagCentU j B := by
  intro R' W H hWH hv hB r hr hr1
  let C : Subgroup U := Subgroup.centralizer ({r} : Set U)
  let T : Subgroup U := pCoreOf 2 C
  have hTC : T ≤ C := GGRootNorm.pCoreOf_le C
  have hTn : ∀ c ∈ C, ∀ t ∈ T, c * t * c⁻¹ ∈ T := by
    intro c hc t ht
    exact (Subgroup.mem_normalizer_iff.mp (GGRootNorm.le_normalizer_pCoreOf C hc) t).mp ht
  have hT : IsPGroup 2 T := GGRootNorm.isPGroup_pCoreOf C
  have hWpres : ∀ c ∈ C, ∀ x ∈ W, (j c : Matrix ι ι F).mulVec x ∈ W := by
    intro c hc x hx
    have hcr : c * r = r * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hcN : (j c : Matrix ι ι F) * ((j r : Matrix ι ι F) - 1)
        = ((j r : Matrix ι ι F) - 1) * (j c : Matrix ι ι F) := by
      calc (j c : Matrix ι ι F) * ((j r : Matrix ι ι F) - 1)
          = (j c : Matrix ι ι F) * (j r : Matrix ι ι F) - (j c : Matrix ι ι F) := by
            rw [mul_sub, mul_one]
        _ = (j r : Matrix ι ι F) * (j c : Matrix ι ι F) - (j c : Matrix ι ι F) := by
            rw [← Matrix.GeneralLinearGroup.coe_mul, ← Matrix.GeneralLinearGroup.coe_mul,
              ← map_mul, ← map_mul, hcr]
        _ = ((j r : Matrix ι ι F) - 1) * (j c : Matrix ι ι F) := by rw [sub_mul, one_mul]
    have hrangeN : (Matrix.toLin' ((j r : Matrix ι ι F) - 1)).range = W := (hv r hr hr1).1
    have hx' : x ∈ (Matrix.toLin' ((j r : Matrix ι ι F) - 1)).range := by rw [hrangeN]; exact hx
    obtain ⟨m, hm⟩ := LinearMap.mem_range.mp hx'
    rw [← hm, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hcN, ← Matrix.mulVec_mulVec]
    rw [← hrangeN]
    exact LinearMap.mem_range.mpr
      ⟨(j c : Matrix ι ι F).mulVec m, by rw [Matrix.toLin'_apply]⟩
  have hirr := h R' W H hWH hv hB r hr hr1
  have htriv := trivial_on_of_irred j C T hTC hTn hT W hWpres hirr
  exact flagCent_of_trivial j hj R' W H hv r hr hr1 T hTC htriv

end CFSG.StandardType.RCKFlag
