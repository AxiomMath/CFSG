module

public import CFSG.ClassicalGroups.Symplectic.StandardForm
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.GL83PartI.I713.Chain
public import CFSG.RankThree.PartOne.KC.UnitaryRigidityOne
public import CFSG.Quasithin.Background.B1Transvection
public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.Quasithin.Background.RealizesFaithful
public import CFSG.RankThree.PartOne.S15K.CommonEigen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open

theorem exists_isElemAbelian_not_isCyclic_fixing_of_nat_realizes
    {M V : Type*} {K : Type} [Group M] [Finite M] [CommGroup V] [Finite V]
    [Field K] [Finite K]
    (hV : ∀ w : V, w ^ 2 = 1)
    (alpha : M →* MulAut V) (H : Subgroup (MulAut V))
    (hH : H ≤ alpha.range)
    (hreal : (FFModel.nat (StatedSp 2 K)).Realizes H ⊤ (fixV H))
    (hK : Nat.card K = 4 ∨ Nat.card K = 8)
    (p : ℕ) (hp : p = Nat.card K - 1)
    (P : Subgroup M) (hP : IsElemAbelian p P) (hPcard : Nat.card P = p ^ 3)
    (hPH : P.map alpha ≤ H) :
    ∀ w : V, ∃ B : Subgroup M,
      IsPGroup p B ∧ IsElemAbelian p B ∧ ¬ IsCyclic ↥B ∧
        ∀ b ∈ B, alpha b w = w := by
  classical
  have hp37 : p = 3 ∨ p = 7 := by
    rcases hK with hK | hK
    · left
      omega
    · right
      omega
  have hpprime : p.Prime := by
    rcases hp37 with rfl | rfl
    · norm_num
    · norm_num
  have hpodd : Odd p := by
    rcases hp37 with rfl | rfl
    · norm_num
    · norm_num
  have hp_pos : 0 < p := hpprime.pos
  obtain ⟨π, hπ⟩ := hreal
  have hπinj : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful_on (FFModel.nat_faithful (StatedSp 2 K)) hπ
  let e : StatedSp 2 K ≃* H := MulEquiv.ofBijective π ⟨hπinj, hπ.1⟩
  obtain ⟨β, hβsurj, hβker, hβeq⟩ :=
    FFModel.RealizesVia.coord (D := FFModel.nat (StatedSp 2 K)) rfl rfl hπ
  let fP : P →* H :=
    (alpha.comp P.subtype).codRestrict H
      (fun x => hPH (Subgroup.mem_map_of_mem alpha x.2))
  let γP : P →* StatedSp 2 K := e.symm.toMonoidHom.comp fP
  have hπγP : ∀ x : P, ((π (γP x) : H) : MulAut V) = alpha (x : M) := by
    intro x
    have h1 : π (γP x) = fP x := by
      change e (e.symm (fP x)) = fP x
      exact e.apply_symm_apply (fP x)
    rw [h1]
    rfl
  let ρ : P →* Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K :=
    (Subgroup.subtype (StatedSp 2 K)).comp γP
  let T : P →* Module.End K (Fin 2 ⊕ Fin 2 → K) :=
    { toFun := fun x => Matrix.mulVecLin
        ((ρ x : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      map_one' := by
        simp only [map_one, Units.val_one, Matrix.mulVecLin_one]
        rfl
      map_mul' := by
        intro x y
        simp only [map_mul, Units.val_mul, Matrix.mulVecLin_mul]
        rfl }
  have hcomm : ∀ x y : P, T x * T y = T y * T x := by
    intro x y
    rw [← map_mul, ← map_mul]
    exact congrArg T (hP.1.is_comm.comm x y)
  have hpow : ∀ x : P, T x ^ p = 1 := by
    intro x
    have hx : x ^ p = 1 := by
      apply Subtype.ext
      simpa using hP.2 (x : M) x.2
    calc T x ^ p = T (x ^ p) := (map_pow T x p).symm
      _ = T 1 := by rw [hx]
      _ = 1 := map_one T
  have hdvd : p ∣ Nat.card K - 1 := by
    rw [← hp]
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.S15K.exists_isPrimitiveRoot_of_dvd
    (K := K) hpprime hdvd
  have htop_ne_bot : (⊤ : Submodule K (Fin 2 ⊕ Fin 2 → K)) ≠ ⊥ := by
    intro hbot
    have hmem : (Pi.single (Sum.inl (0 : Fin 2)) (1 : K)) ∈
        (⊥ : Submodule K (Fin 2 ⊕ Fin 2 → K)) := by
      rw [← hbot]
      exact Submodule.mem_top
    rw [Submodule.mem_bot] at hmem
    have h1 := congrFun hmem (Sum.inl (0 : Fin 2))
    simp at h1
  obtain ⟨nvec, -, hnvec_ne, hscalar⟩ :=
    @CFSG.RankThree.PartOne.S15K.exists_common_eigenvector K (Fin 2 ⊕ Fin 2 → K)
      _ _ _ _ p hp_pos ζ hζ P T hcomm hpow
      (⊤ : Submodule K (Fin 2 ⊕ Fin 2 → K)) htop_ne_bot
      (by intro i w _; exact Submodule.mem_top)
  let nM : Multiplicative (Fin 2 ⊕ Fin 2 → K) := Multiplicative.ofAdd nvec
  let act : P →* LinearMap.GeneralLinearGroup K (Fin 2 ⊕ Fin 2 → K) :=
    (Matrix.GeneralLinearGroup.toLin (n := Fin 2 ⊕ Fin 2) (R := K)).toMonoidHom.comp ρ
  have hact_apply : ∀ x : P,
      (act x : Module.End K (Fin 2 ⊕ Fin 2 → K)) nvec =
        ((ρ x : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).mulVec nvec := by
    intro x
    simp [act, Matrix.GeneralLinearGroup.coe_toLin]
  have hev : ∀ x : P, ∃ c : K,
      (act x : Module.End K (Fin 2 ⊕ Fin 2 → K)) nvec = c • nvec := by
    intro x
    obtain ⟨c, hc⟩ := hscalar x
    exact ⟨c, by rw [hact_apply x]; simpa [T, Matrix.mulVecLin_apply] using hc⟩
  obtain ⟨χ, hχ⟩ :=
    CFSG.RankThree.PartOne.KCUnitaryOne.exists_charHom (ρ := act) hnvec_ne hev
  let Bp : Subgroup P := χ.ker
  have hBp_fix : ∀ x : P, x ∈ Bp ↔
      ((ρ x : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).mulVec nvec = nvec := by
    intro x
    constructor
    · intro hx
      have hx1 : χ x = 1 := MonoidHom.mem_ker.mp hx
      have h1 := hχ x
      rw [hx1, Units.val_one, one_smul, hact_apply x] at h1
      exact h1
    · intro hx
      apply Units.ext
      have h1 := hχ x
      rw [hact_apply x, hx] at h1
      exact smul_left_injective K hnvec_ne (by simpa using h1.symm)
  have hidx_dvd : Bp.index ∣ p := by
    rw [show Bp = χ.ker from rfl, Subgroup.index_ker]
    have h := Subgroup.card_subgroup_dvd_card χ.range
    rwa [Nat.card_units, ← hp] at h
  have hprod : Nat.card Bp * Bp.index = p ^ 3 := by
    calc Nat.card Bp * Bp.index = Nat.card P := Subgroup.card_mul_index Bp
      _ = p ^ 3 := hPcard
  have hidx_cases : Bp.index = 1 ∨ Bp.index = p :=
    hpprime.eq_one_or_self_of_dvd _ hidx_dvd
  have hBp_card : p ^ 2 ≤ Nat.card Bp := by
    rcases hidx_cases with h1 | h1
    · have hcard : Nat.card Bp = p ^ 3 := by
        rw [h1, mul_one] at hprod
        exact hprod
      rw [hcard]
      exact Nat.pow_le_pow_right hp_pos (by norm_num : 2 ≤ 3)
    · have hcard : Nat.card Bp = p ^ 2 := by
        have h2 : Nat.card Bp * p = p ^ 2 * p := by
          calc Nat.card Bp * p = p ^ 3 := by simpa [h1] using hprod
            _ = p ^ 2 * p := by ring
        exact Nat.eq_of_mul_eq_mul_right hp_pos h2
      rw [hcard]
  let B0 : Subgroup M := Bp.map P.subtype
  have hB0_le_P : B0 ≤ P := Subgroup.map_subtype_le Bp
  have hB0_el : IsElemAbelian p B0 := hP.mono hB0_le_P
  have hB0_card : Nat.card B0 = Nat.card Bp :=
    Subgroup.card_map_of_injective P.subtype_injective
  have hB0_card_ge : p ^ 2 ≤ Nat.card B0 := by
    rw [hB0_card]
    exact hBp_card
  have hB0_ncyc : ¬ IsCyclic ↥B0 := by
    intro hcyc
    have hle : Nat.card B0 ≤ p :=
      GL83.I713.card_le_of_isElemAbelian_of_isCyclic hpprime hB0_el hcyc
    have hle2 : p ^ 2 ≤ p := le_trans hB0_card_ge hle
    have hmul : p * p ≤ p * 1 := by simpa [pow_two] using hle2
    have hple1 : p ≤ 1 := Nat.le_of_mul_le_mul_left hmul hp_pos
    omega
  have hB0_fix_Z : ∀ w ∈ fixV H, ∀ b ∈ B0, alpha b w = w := by
    intro w hw b hb
    have hbP : (b : M) ∈ P := hB0_le_P hb
    have hbH : alpha b ∈ H := hPH (Subgroup.mem_map_of_mem alpha hbP)
    exact (mem_fixV.mp hw) (alpha b) hbH
  have hB0_fix_lift : ∀ b ∈ B0, ∀ w : V,
      β ⟨w, Subgroup.mem_top w⟩ = nM → alpha b w = w := by
    intro b hb w hwβ
    obtain ⟨x, hxBp, hxb⟩ := Subgroup.mem_map.mp hb
    have hbP : (b : M) ∈ P := hB0_le_P hb
    have hbH : alpha b ∈ H := hPH (Subgroup.mem_map_of_mem alpha hbP)
    have hxfix : ((ρ x : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).mulVec nvec = nvec :=
      (hBp_fix x).1 hxBp
    have hβx : β ⟨alpha (x : M) w, Subgroup.mem_top _⟩ = nM := by
      have h1 := hβeq (γP x) ⟨w, Subgroup.mem_top w⟩ (Subgroup.mem_top _)
      rw [hπγP x] at h1
      rw [hwβ] at h1
      have h2 : (FFModel.nat (StatedSp 2 K)).act (γP x) nM = nM := by
        change Multiplicative.ofAdd
          (Matrix.mulVec (((γP x : StatedSp 2 K) :
            Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) nvec) = nM
        rw [show (((γP x : StatedSp 2 K) :
            Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
            ((ρ x : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) from rfl, hxfix]
      rw [h2] at h1
      exact h1
    have hβb : β ⟨alpha b w, Subgroup.mem_top _⟩ = nM := by
      simpa [← hxb] using hβx
    have hβd : β (⟨alpha b w, Subgroup.mem_top _⟩ *
        ⟨w, Subgroup.mem_top w⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, hβb, hwβ]
      exact mul_inv_cancel nM
    have hdZ : alpha b w * w⁻¹ ∈ fixV H := by
      simpa using (hβker _).1 hβd
    have hd_fix : alpha b (alpha b w * w⁻¹) = alpha b w * w⁻¹ :=
      (mem_fixV.mp hdZ) (alpha b) hbH
    have hsq : ((alpha b) ^ 2) w = w := by
      set d : V := alpha b w * w⁻¹ with hd
      have hdisp : alpha b w = d * w := by
        rw [hd]
        group
      calc ((alpha b) ^ 2) w = (alpha b) ((alpha b) w) := rfl
        _ = (alpha b) (d * w) := by rw [hdisp]
        _ = (alpha b) d * (alpha b) w := by rw [map_mul]
        _ = d * (d * w) := by rw [show (alpha b) d = d from hd_fix, hdisp]
        _ = (d * d) * w := by group
        _ = w := by
          have hd2 : d * d = 1 := by simpa [pow_two] using hV d
          rw [hd2, one_mul]
    have hxpow : (alpha b) ^ p = 1 := by
      have hbp : (b : M) ^ p = 1 := hP.2 (b : M) hbP
      calc (alpha b) ^ p = alpha ((b : M) ^ p) := (map_pow alpha b p).symm
        _ = alpha 1 := by rw [hbp]
        _ = 1 := map_one alpha
    exact CFSG.Quasithin.B1.fix_of_sq_fix hpodd hxpow hsq
  intro w
  let wu : ↥(⊤ : Subgroup V) := ⟨w, Subgroup.mem_top w⟩
  by_cases hw : β wu = 1
  · refine ⟨B0, hB0_el.isPGroup, hB0_el, hB0_ncyc, ?_⟩
    intro b hb
    exact hB0_fix_Z w ((hβker wu).1 hw) b hb
  · let x : Fin 2 ⊕ Fin 2 → K := Multiplicative.toAdd (β wu)
    have hofx : Multiplicative.ofAdd x = β wu := ofAdd_toAdd (β wu)
    have hxne : x ≠ 0 := by
      intro hx0
      apply hw
      rw [← hofx, hx0]
      rfl
    obtain ⟨A, hA, hAvec⟩ := CFSG.ClassicalGroups.Symplectic.exists_statedSp_mulVec_eq
      (m := 2) (K := K) hxne hnvec_ne
    let A' : StatedSp 2 K := ⟨A, hA⟩
    let hAH : H := ⟨π A', (π A').2⟩
    have hAHrange : (hAH : MulAut V) ∈ alpha.range := hH hAH.2
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hAHrange
    have hmα : alpha m = ((π A' : H) : MulAut V) := by
      simpa [hAH] using hm
    have hβmw : β ⟨alpha m w, Subgroup.mem_top _⟩ = nM := by
      have h1 := hβeq A' wu (Subgroup.mem_top _)
      rw [← hmα] at h1
      have h2 : (FFModel.nat (StatedSp 2 K)).act A' (β wu) = nM := by
        change Multiplicative.ofAdd
          (Matrix.mulVec (((A' : StatedSp 2 K) :
            Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
            (Multiplicative.toAdd (β wu))) = nM
        have hA' : (((A' : StatedSp 2 K) :
            Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
            ((A : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := rfl
        rw [hA', ← hofx]
        simp only [toAdd_ofAdd]
        rw [show Matrix.mulVec ((A : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) x = nvec from hAvec]
      rw [h2] at h1
      exact h1
    have hfix_mw : ∀ b ∈ B0, alpha b (alpha m w) = alpha m w := by
      intro b hb
      exact hB0_fix_lift b hb (alpha m w) hβmw
    let f : M →* M := (MulAut.conj m⁻¹).toMonoidHom
    refine ⟨B0.map f, (hB0_el.map f).isPGroup, hB0_el.map f, ?_, ?_⟩
    · intro hcyc
      exact hB0_ncyc ((MulEquiv.isCyclic
        (B0.equivMapOfInjective f (MulAut.conj m⁻¹).injective)).mpr hcyc)
    · intro b hb
      obtain ⟨b0, hb0, rfl⟩ := Subgroup.mem_map.mp hb
      have hconj : alpha ((MulAut.conj m⁻¹) b0) w =
          (alpha m)⁻¹ (alpha b0 (alpha m w)) := by
        rw [MulAut.conj_apply]
        simp only [map_mul, map_inv]
        rfl
      rw [show f b0 = (MulAut.conj m⁻¹) b0 from rfl, hconj,
        hfix_mw b0 hb0]
      simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
