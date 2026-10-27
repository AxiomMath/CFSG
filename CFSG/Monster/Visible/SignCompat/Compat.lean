module

public import CFSG.Monster.Visible.SignCompat.Conj
public import CFSG.Monster.Visible.SignFixed
import Mathlib.Tactic.ReduceModChar

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Visible

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Lifts
  CFSG.Monster.ScalarKernel Matrix Subgroup

namespace SignCompat

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

private theorem mem_L_add {u v : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (hv : v ∈ codeLattice C) :
    u + v ∈ codeLattice C := (codeLatticeSubgroup allOnes_mem_C).add_mem hu hv

private theorem mem_L_sub {u v : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (hv : v ∈ codeLattice C) :
    u - v ∈ codeLattice C := (codeLatticeSubgroup allOnes_mem_C).sub_mem hu hv

private theorem mem_L_zsmul {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (n : ℤ) :
    n • u ∈ codeLattice C := (codeLatticeSubgroup allOnes_mem_C).zsmul_mem hu n

private theorem cls_eq_of_eq_add' {x u w : Fin 24 → ℤ} (hx : x ∈ codeLattice C)
    (hu : u ∈ codeLattice C) (hw : w ∈ codeLattice C) (h : x = u + (2 : ℤ) • w) :
    cls x hx = cls u hu := by
  have h2 : (2 : ℤ) • w ∈ codeLattice C := mem_L_zsmul hw 2
  rw [cls_congr hx h, ← cls_add hu h2, cls_two_smul hw h2, add_zero]

theorem cls_zero' (h : (0 : Fin 24 → ℤ) ∈ codeLattice C) : cls 0 h = 0 :=
  Submodule.Quotient.mk_zero _

theorem cls_bitLift_smul (t : ZMod 2) {v : Fin 24 → ℤ} (hv : v ∈ codeLattice C)
    (h : bitLift t • v ∈ codeLattice C) : cls (bitLift t • v) h = t • cls v hv := by
  rcases zmod2_cases t with rfl | rfl
  · have e : bitLift (0 : ZMod 2) • v = 0 := by
      rw [show bitLift (0 : ZMod 2) = 0 from rfl, zero_smul]
    rw [cls_congr h e, cls_zero', zero_smul]
  · have e : bitLift (1 : ZMod 2) • v = v := by
      rw [bitLift_one, one_smul]
    rw [cls_congr h e, one_smul]

theorem modTwoEnd_gO_cls_eq (a : C) {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) :
    modTwoEnd (gO a) (cls u hu) =
      cls u hu + cls ((2 : ℤ) • maskVec a u) (two_maskVec_mem a.2 hu) := by
  rw [modTwoEnd_gO_cls]
  have e : cls u hu = cls (signVec a u) (signVec_mem a.2 hu) +
      cls ((2 : ℤ) • maskVec a u) (two_maskVec_mem a.2 hu) := by
    rw [cls_add]
    exact cls_congr hu (sub_add_cancel u _).symm
  rw [e, add_assoc, ZModModule.add_self, add_zero]

theorem twoLift_mem' (a : C) : (fun k => 2 * bitLift ((a : Fin 24 → ZMod 2) k)) ∈ codeLattice C :=
  two_bitLift_mem weight_mod_four' a.2

theorem four_mem {v : Fin 24 → ZMod 2} (hv : Even (hammingNorm v)) :
    (fun k => 4 * bitLift (v k)) ∈ codeLattice C := by
  refine mem_of_even (y := fun k => 2 * bitLift (v k)) (fun k => by ring) ?_ ?_
  · have e : (fun k => ((2 * bitLift (v k) : ℤ) : ZMod 2)) = 0 := by
      funext k
      rw [Int.cast_mul, show ((2 : ℤ) : ZMod 2) = 0 from rfl, zero_mul]
      rfl
    rw [e]
    exact C.zero_mem
  · rw [← Finset.mul_sum, sum_bitLift]
    obtain ⟨m, hm⟩ := hv
    rw [hm]
    push_cast
    omega

theorem cls_four {v : Fin 24 → ZMod 2} (hv : Even (hammingNorm v)) :
    cls (fun k => 4 * bitLift (v k)) (four_mem hv) =
      lamVec v + ((hammingNorm v / 2 : ℕ) : ZMod 2) • twoΩCls := by
  set h := hammingNorm v / 2 with hdef
  have hh : hammingNorm v = 2 * h := by
    obtain ⟨m, hm⟩ := hv
    omega
  have hw : ((h / 2 : ℕ) : ℤ) • twoΩ - lamSum v ∈ codeLattice C :=
    mem_L_sub (mem_L_zsmul twoΩ_mem _) (lamSum_mem v)
  have hb : bitLift (h : ZMod 2) • twoΩ ∈ codeLattice C := mem_L_zsmul twoΩ_mem _
  have hx : lamSum v + bitLift (h : ZMod 2) • twoΩ ∈ codeLattice C := mem_L_add (lamSum_mem v) hb
  have hbit : bitLift (h : ZMod 2) = ((h % 2 : ℕ) : ℤ) := by
    rw [bitLift, ZMod.val_natCast]
  rw [cls_eq_of_eq_add' (four_mem hv) hx hw ?_, ← cls_add (lamSum_mem v) hb,
    cls_bitLift_smul _ twoΩ_mem hb]
  · rfl
  · funext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, lamSum, twoΩ_apply, hbit,
      hh]
    push_cast
    omega

theorem lamCode_Ω' : lamCode Ω = twoΩ := by
  funext k
  have hP : P Ω = 0 := by decide
  simp only [lamCode, Pint, hP, twoΩ_apply]
  rw [show Ω k = 1 from rfl, bitLift_one, show bitLift (0 : ZMod 2) = 0 from rfl]
  ring

theorem lamX_ΩC : lamX ΩC = twoΩCls := by
  rw [lamX, lamCodeCls, twoΩCls_eq]
  exact cls_congr _ lamCode_Ω'

theorem modTwoEnd_gO_lamX (a b : C) :
    modTwoEnd (gO a) (lamX b) = lamX b + lamVec ((a : Fin 24 → ZMod 2) * (b : Fin 24 → ZMod 2)) +
      K (a : Fin 24 → ZMod 2) b • twoΩCls := by
  rw [lamX, lamCodeCls, modTwoEnd_gO_cls_eq, add_assoc]
  congr 1
  have hev : Even (hammingNorm ((a : Fin 24 → ZMod 2) * (b : Fin 24 → ZMod 2))) :=
    even_iff_two_dvd.2 (two_dvd_hammingNorm_mul a.2 b.2)
  have hw : bitLift (P (b : Fin 24 → ZMod 2)) •
      ((fun k => 2 * bitLift ((a : Fin 24 → ZMod 2) k)) -
        (fun k => 4 * bitLift (((a : Fin 24 → ZMod 2) * (b : Fin 24 → ZMod 2)) k))) ∈
          codeLattice C :=
    mem_L_zsmul (mem_L_sub (twoLift_mem' a) (four_mem hev)) _
  rw [cls_eq_of_eq_add' _ (four_mem hev) hw ?_, cls_four hev, K_eq]
  funext k
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, maskVec_apply, lamCode, Pint,
    Pi.mul_apply, bitLift_mul]
  ring

theorem modTwoEnd_gO_lamVec_single (a : C) (i : Fin 24) :
    modTwoEnd (gO a) (lamVec (Pi.single i 1)) = lamVec (Pi.single i 1) +
      (lamX a + (P (a : Fin 24 → ZMod 2) + (a : Fin 24 → ZMod 2) i) • twoΩCls) := by
  rw [lamVec, modTwoEnd_gO_cls_eq]
  congr 1
  have h8 : (8 : ℤ) • (Pi.single i (1 : ℤ) : Fin 24 → ℤ) ∈ codeLattice C :=
    smul_eight_mem_codeLattice _
  have hw : bitLift (P (a : Fin 24 → ZMod 2)) •
      ((fun k => 2 * bitLift ((a : Fin 24 → ZMod 2) k)) - twoΩ) +
      bitLift ((a : Fin 24 → ZMod 2) i) •
        (-lamSum (Pi.single i 1) - (8 : ℤ) • (Pi.single i (1 : ℤ) : Fin 24 → ℤ)) +
      (bitLift (P (a : Fin 24 → ZMod 2)) * bitLift ((a : Fin 24 → ZMod 2) i)) • twoΩ ∈
        codeLattice C :=
    mem_L_add (mem_L_add (mem_L_zsmul (mem_L_sub (twoLift_mem' a) twoΩ_mem) _)
      (mem_L_zsmul (mem_L_sub ((codeLatticeSubgroup allOnes_mem_C).neg_mem (lamSum_mem _)) h8) _))
      (mem_L_zsmul twoΩ_mem _)
  have hb : bitLift (P (a : Fin 24 → ZMod 2) + (a : Fin 24 → ZMod 2) i) • twoΩ ∈ codeLattice C :=
    mem_L_zsmul twoΩ_mem _
  have hx : lamCode a + bitLift (P (a : Fin 24 → ZMod 2) + (a : Fin 24 → ZMod 2) i) • twoΩ ∈
      codeLattice C := mem_L_add (lamCode_mem a.2) hb
  rw [cls_eq_of_eq_add' _ hx hw ?_, ← cls_add (lamCode_mem a.2) hb,
    cls_bitLift_smul _ twoΩ_mem hb]
  · rfl
  · have hbl := bitLift_add' (P (a : Fin 24 → ZMod 2)) ((a : Fin 24 → ZMod 2) i)
    rw [bitLift_mul] at hbl
    funext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
      maskVec_apply, lamCode, Pint, lamSum_single, twoΩ_apply]
    rcases eq_or_ne k i with rfl | hk
    · simp only [Pi.single_eq_same]
      linear_combination (2 : ℤ) * hbl
    · simp only [Pi.single_eq_of_ne hk]
      linear_combination (2 : ℤ) * hbl

theorem modTwoEnd_gO_lamCocode (a : C) (δ : Cocode) :
    modTwoEnd (gO a) (lamCocode δ) = lamCocode δ + pair ΩC δ • lamX a +
      (pair ΩC δ * P (a : Fin 24 → ZMod 2) + pair a δ) • twoΩCls := by
  induction δ using Submodule.Quotient.induction_on with
  | H v =>
    have hsum : modTwoEnd (gO a) (lamVec v) = ∑ i, v i • (lamVec (Pi.single i 1) +
        (lamX a + (P (a : Fin 24 → ZMod 2) + (a : Fin 24 → ZMod 2) i) • twoΩCls)) := by
      rw [lamVec_eq_sum v, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, modTwoEnd_gO_lamVec_single]
    have h1 : (ΩC : Fin 24 → ZMod 2) ⬝ᵥ v = ∑ i, v i := by
      simp [dotProduct, Ω]
    have h2 : ∑ i, v i * (P (a : Fin 24 → ZMod 2) + (a : Fin 24 → ZMod 2) i) =
        (∑ i, v i) * P (a : Fin 24 → ZMod 2) + (a : Fin 24 → ZMod 2) ⬝ᵥ v := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul, dotProduct, mul_comm]
    rw [lamCocode_mk, hsum, pair_mk, pair_mk, h1]
    simp only [smul_add, Finset.sum_add_distrib, smul_smul, ← Finset.sum_smul]
    rw [h2, ← lamVec_eq_sum v, add_assoc]

theorem phi0_ΩC_zero : phi0 (ΩC, 0) = twoΩCls := by
  rw [phi0_apply, lamT, thetaD_ΩC, map_zero, add_zero, add_zero, lamX_ΩC]

theorem phi0_smul_combo (a : C) (ω t : ZMod 2) (δ : Cocode) :
    phi0 (ω • a + t • ΩC, ω • thetaD a + δ) = ω • lamX a + t • twoΩCls + lamCocode δ := by
  have e : ((ω • a + t • ΩC, ω • thetaD a + δ) : C × Cocode) =
      ω • (a, thetaD a) + t • (ΩC, 0) + (0, δ) := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [e, map_add, map_add, map_smul, map_smul, phi0_thetaD, phi0_ΩC_zero, phi0_zero_left]

theorem conjY_XQ_coords (e f : Parker) :
    ((conjY e ⟨f.sign, f.code, thetaD f.code⟩).a, (conjY e ⟨f.sign, f.code, thetaD f.code⟩).δ) =
      (f.code + K (e.code : Fin 24 → ZMod 2) f.code • ΩC,
        Acocode e.code f.code + thetaD f.code) := by
  have hev : pair ΩC (thetaD f.code) = 0 := pair_ΩC_thetaD _
  rw [conjY, conjD_of_even e hev]
  refine Prod.ext ?_ ?_
  · simp only [SpinCoord.mul_a, conjT, pair_thetaD, zero_add]
    rw [add_assoc, ← add_smul, θ_add_θ_swap]
  · simp only [SpinCoord.mul_δ, conjT, zero_add]

theorem conjY_DQ_coords (e : Parker) (δ : Cocode) :
    ((conjY e ⟨0, 0, δ⟩).a, (conjY e ⟨0, 0, δ⟩).δ) =
      (pair ΩC δ • e.code + (pair ΩC δ * P (e.code : Fin 24 → ZMod 2) + pair e.code δ) • ΩC,
        pair ΩC δ • thetaD e.code + δ) := by
  have h0 : Acocode e.code 0 = 0 := by
    rw [Acocode, ZeroMemClass.coe_zero, mul_zero]
    exact Submodule.Quotient.mk_zero _
  refine Prod.ext ?_ ?_
  · simp only [conjY, SpinCoord.mul_a, conjT, conjD, θ_zero_right, zero_smul, add_zero, zero_add]
  · simp only [conjY, SpinCoord.mul_δ, conjT, conjD, h0, zero_add]

private def phiConj (e : Parker) : Q →* Multiplicative L2 :=
  (phi.toMonoidHom.comp (QuotientGroup.mk' (center Q))).comp (conjYQ e).toMonoidHom

private def phiSign (e : Parker) : Q →* Multiplicative L2 :=
  (AddMonoidHom.toMultiplicative (modTwoEnd (gO e.code)).toAddMonoidHom).comp
    (phi.toMonoidHom.comp (QuotientGroup.mk' (center Q)))

private theorem phiConj_apply (e : Parker) (x : Q) :
    phiConj e x = phi (QuotientGroup.mk (conjYQ e x)) := rfl

private theorem phiSign_apply (e : Parker) (x : Q) :
    phiSign e x = Multiplicative.ofAdd
      (modTwoEnd (gO e.code) (Multiplicative.toAdd (phi (QuotientGroup.mk x)))) := rfl

private theorem phiConj_spinEquiv (e : Parker) (x : SpinCoord) :
    phiConj e (spinEquiv x) = Multiplicative.ofAdd (phi0 ((conjY e x).a, (conjY e x).δ)) :=
  (phiConj_apply e _).trans ((congrArg (fun t : Q => phi (QuotientGroup.mk t))
    (conjYQ_spinEquiv e x)).trans (phi_mk_spinEquiv _))

private theorem phiConj_eq_phiSign (e : Parker) : phiConj e = phiSign e := by
  refine MonoidHom.eq_of_eqOn_dense (closure_preimage_eq_top (Set.range XU ∪ Set.range DU)) ?_
  rintro g (⟨f, hf⟩ | ⟨δ, hδ⟩)
  · have hg : g = XQ f := Subtype.ext hf.symm
    rw [hg]
    have h1 : phiConj e (XQ f) = Multiplicative.ofAdd (lamX f.code +
        lamVec ((e.code : Fin 24 → ZMod 2) * (f.code : Fin 24 → ZMod 2)) +
          K (e.code : Fin 24 → ZMod 2) f.code • twoΩCls) := by
      rw [XQ_eq, phiConj_spinEquiv, conjY_XQ_coords]
      refine congrArg Multiplicative.ofAdd ?_
      have e1 : ((f.code + K (e.code : Fin 24 → ZMod 2) f.code • ΩC,
          Acocode e.code f.code + thetaD f.code) : C × Cocode) =
          (f.code, thetaD f.code) + K (e.code : Fin 24 → ZMod 2) f.code • (ΩC, 0) +
            (0, Acocode e.code f.code) := by
        refine Prod.ext ?_ ?_ <;> simp [add_comm]
      rw [e1, map_add, map_add, map_smul, phi0_thetaD, phi0_ΩC_zero, phi0_zero_left,
        lamCocode_Acocode]
      abel
    have h2 : phiSign e (XQ f) = Multiplicative.ofAdd (lamX f.code +
        lamVec ((e.code : Fin 24 → ZMod 2) * (f.code : Fin 24 → ZMod 2)) +
          K (e.code : Fin 24 → ZMod 2) f.code • twoΩCls) := by
      rw [phiSign_apply, phi_XQ, toAdd_ofAdd, modTwoEnd_gO_lamX]
    exact h1.trans h2.symm
  · have hg : g = DQ δ := Subtype.ext hδ.symm
    rw [hg]
    have h1 : phiConj e (DQ δ) = Multiplicative.ofAdd (pair ΩC δ • lamX e.code +
        (pair ΩC δ * P (e.code : Fin 24 → ZMod 2) + pair e.code δ) • twoΩCls +
          lamCocode δ) := by
      rw [DQ_eq, phiConj_spinEquiv, conjY_DQ_coords, phi0_smul_combo]
    have h2 : phiSign e (DQ δ) = Multiplicative.ofAdd (pair ΩC δ • lamX e.code +
        (pair ΩC δ * P (e.code : Fin 24 → ZMod 2) + pair e.code δ) • twoΩCls +
          lamCocode δ) := by
      rw [phiSign_apply, phi_DQ, toAdd_ofAdd, modTwoEnd_gO_lamCocode]
      refine congrArg Multiplicative.ofAdd ?_
      abel
    exact h1.trans h2.symm

theorem phi_conjYQ (e : Parker) (r : Q) :
    Multiplicative.toAdd (phi (QuotientGroup.mk (conjYQ e r))) =
      modTwoEnd (gO e.code) (Multiplicative.toAdd (phi (QuotientGroup.mk r))) :=
  congrArg Multiplicative.toAdd ((phiConj_apply e r).symm.trans
    ((DFunLike.congr_fun (phiConj_eq_phiSign e) r).trans (phiSign_apply e r)))

end SignCompat

open SignCompat

theorem isCompatible_YU_gO (e : Parker) : IsCompatible (YU e) (gO e.code) := by
  intro r r' h
  have hr : r' = conjYQ e r := Subtype.ext (h.trans (coe_conjYQ e r).symm)
  exact (congrArg (fun x : Q => Multiplicative.toAdd (phi (QuotientGroup.mk x))) hr).trans
    (phi_conjYQ e r)

theorem YU_gO_mem_Pvis (e : Parker) : (YU e, gO e.code) ∈ Pvis :=
  ⟨isDyadicSpinNormalizer_YU e, isCompatible_YU_gO e⟩

end CFSG.Monster.Visible
