module

public import CFSG.RankThree.CentralLiftU.HypRankOneOdd
public import CFSG.RankThree.CentralLiftU.UnitaryThreeLift
public import CFSG.RankThree.CentralLift.LinearTorusMonomial

public section

namespace CFSG.RankThree.CentralLiftU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.CentralLift (IsLargeCentralExt map_sl2Lift_large conj_sl2Lift_apply_large
  sl2Lift_comp_large commute_sl2Lift_large eq_sl2Lift_large)
open CFSG.LieType.CentralExt (sl2Lift)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (sl2Diag sl2W sl2ConjDiag
  coe_sl2Diag coe_sl2W coe_sl2ConjDiag sl2W_mul_sl2W sl2ConjDiag_inv_sl2W
  sl2ConjDiag_neg_one_sl2W)
open CFSG.RankThree.CentralLift.LinearRoots (swapSL sl2ConjDiag_sl2Diag swapSL_sl2Diag
  sl2ConjDiag_one)
open CFSG.LieType.Steinberg (perfectLift)
open scoped Matrix

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) {r ε : ℕ}

theorem gramJ3_herm : ((gramJ3 K).map h.bar)ᵀ = gramJ3 K := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [gramJ3]

theorem det_gramJ3 : (gramJ3 K).det ≠ 0 := by
  simp [gramJ3, det_fin_three]

theorem ne_succ_of_lt {i : Fin r} (hi : i.val + 1 < r) : i ≠ ⟨i.val + 1, hi⟩ := fun e => by
  have := congrArg Fin.val e
  simp at this

theorem sl2ConjDiag_sl2W {k : Type*} [Field k] (u : kˣ) :
    sl2ConjDiag u (sl2W : SpecialLinearGroup (Fin 2) k) = sl2Diag u⁻¹ * sl2W := by
  simpa only [inv_inv] using sl2ConjDiag_inv_sl2W (k := k) u⁻¹

@[expose] noncomputable def fcoe : h.fixedFieldˣ →* Kˣ :=
  Units.map h.fixedField.subtype.toMonoidHom

theorem coe_fcoe (b : h.fixedFieldˣ) : ((fcoe h b : Kˣ) : K) = ((b : h.fixedField) : K) :=
  rfl

section Defs

variable {R : Type*} [Group R] (π : R →* hypSU h r ε) {c : K} (hc : c ∈ h.traceZero)
  (hc0 : c ≠ 0)

@[expose] noncomputable def rhoLift {i j : Fin r} (hij : i ≠ j) :
    SpecialLinearGroup (Fin 2) K →* R :=
  sl2Lift π (rhoU h hij)

@[expose] noncomputable def iotaLift (k : Fin r) : SpecialLinearGroup (Fin 2) h.fixedField →* R :=
  sl2Lift π (iotaU h hc hc0 k)

@[expose] noncomputable def hRho {i j : Fin r} (hij : i ≠ j) : Kˣ →* R :=
  (rhoLift h π hij).comp sl2Diag

@[expose] noncomputable def hIota (k : Fin r) : h.fixedFieldˣ →* R :=
  (iotaLift h π hc hc0 k).comp sl2Diag

@[expose] noncomputable def vRho {i j : Fin r} (hij : i ≠ j) : R := rhoLift h π hij sl2W

@[expose] noncomputable def vIota (k : Fin r) : R := iotaLift h π hc hc0 k sl2W

@[expose] noncomputable def sLift (i : Fin r) : R :=
  if hi : i.val + 1 < r then vRho h π (ne_succ_of_lt hi) else vIota h π hc hc0 i

theorem sLift_of_lt {i : Fin r} (hi : i.val + 1 < r) :
    sLift h π hc hc0 i = vRho h π (ne_succ_of_lt hi) :=
  dite_eq_left hi

theorem sLift_of_not_lt {i : Fin r} (hi : ¬i.val + 1 < r) :
    sLift h π hc hc0 i = vIota h π hc hc0 i :=
  dite_eq_right hi

theorem rhoLift_congr {i j i' j' : Fin r} (hij : i ≠ j) (hij' : i' ≠ j') (hi : i = i')
    (hj : j = j') : rhoLift h π hij = rhoLift h π hij' := by
  subst hi hj
  rfl

theorem vRho_mul_self {i j : Fin r} (hij : i ≠ j) :
    vRho h π hij * vRho h π hij = hRho h π hij (-1) := by
  rw [vRho, ← map_mul, sl2W_mul_sl2W]
  rfl

theorem vIota_mul_self (k : Fin r) :
    vIota h π hc hc0 k * vIota h π hc hc0 k = hIota h π hc hc0 k (-1) := by
  rw [vIota, ← map_mul, sl2W_mul_sl2W]
  rfl

end Defs

section DefsOdd

variable {R : Type*} [Group R] (π : R →* hypSU h r 1)

@[expose] noncomputable def kappaLift (k : Fin r) : gramSU h (gramJ3 K) →* R :=
  perfectLift π (kappaU h k)

@[expose] noncomputable def hKappa (k : Fin r) : Kˣ →* R := (kappaLift h π k).comp (dkHom h)

end DefsOdd

structure UHyp {R : Type*} [Group R] (π : R →* hypSU h r ε) : Prop where
  odd : ℓ ≠ 2
  large : IsLargeCentralExt π

namespace UHyp

variable {h} {R : Type*} [Group R] {π : R →* hypSU h r ε} (hS : UHyp h π)
include hS

theorem charK : ringChar K ≠ 2 := by
  have := h.charP
  rw [ringChar.eq K ℓ]
  exact hS.odd

theorem charF : ringChar h.fixedField ≠ 2 := by
  intro h2
  have h3 : ((2 : ℕ) : h.fixedField) = 0 := (ringChar.spec h.fixedField 2).mpr (by rw [h2])
  have h4 : ((2 : ℕ) : K) = 0 := by
    rw [← map_natCast h.fixedField.subtype 2, h3, map_zero]
  exact Ring.two_ne_zero hS.charK (by exact_mod_cast h4)

end UHyp

section Basic

variable {R : Type*} [Group R] [Finite R] {π : R →* hypSU h r ε} (hS : UHyp h π)
  {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)
include hS

theorem pi_rhoLift {i j : Fin r} (hij : i ≠ j) (g : SpecialLinearGroup (Fin 2) K) :
    π (rhoLift h π hij g) = rhoU h hij g := by
  have := h.finite
  exact map_sl2Lift_large hS.charK hS.large _ g

theorem pi_iotaLift (k : Fin r) (g : SpecialLinearGroup (Fin 2) h.fixedField) :
    π (iotaLift h π hc hc0 k g) = iotaU h hc hc0 k g := by
  have := h.finite
  exact map_sl2Lift_large hS.charF hS.large _ g

theorem pi_vRho {i j : Fin r} (hij : i ≠ j) : π (vRho h π hij) = rhoU h hij sl2W :=
  pi_rhoLift h hS hij sl2W

theorem pi_vIota (k : Fin r) : π (vIota h π hc hc0 k) = iotaU h hc hc0 k sl2W :=
  pi_iotaLift h hS hc hc0 k sl2W

theorem coe_pi_hRho {i j : Fin r} (hij : i ≠ j) (t : Kˣ) :
    ((π (hRho h π hij t) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      diagonal (rhoDiag h i j t) := by
  rw [hRho, MonoidHom.comp_apply, pi_rhoLift h hS]
  exact coe_rhoU_sl2Diag h hij t

theorem coe_pi_hIota (k : Fin r) (b : h.fixedFieldˣ) :
    ((π (hIota h π hc hc0 k b) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal (iotaDiag h k b) := by
  rw [hIota, MonoidHom.comp_apply, pi_iotaLift h hS]
  exact coe_iotaU_sl2Diag h hc hc0 k b

theorem conj_rhoLift_of {e : R} {k l k' l' : Fin r} (hkl : k ≠ l) (hkl' : k' ≠ l')
    {γ : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 2) K}
    (hγ : (MulAut.conj (π e)).toMonoidHom.comp (rhoU h hkl) = (rhoU h hkl').comp γ)
    (g : SpecialLinearGroup (Fin 2) K) :
    e * rhoLift h π hkl g * e⁻¹ = rhoLift h π hkl' (γ g) := by
  have := h.finite
  rw [rhoLift, conj_sl2Lift_apply_large hS.charK hS.large, hγ,
    ← sl2Lift_comp_large hS.charK hS.charK hS.large]
  rfl

theorem conj_iotaLift_of {e : R} {k k' : Fin r}
    {γ : SpecialLinearGroup (Fin 2) h.fixedField →* SpecialLinearGroup (Fin 2) h.fixedField}
    (hγ : (MulAut.conj (π e)).toMonoidHom.comp (iotaU h hc hc0 k) =
      (iotaU h hc hc0 k').comp γ) (g : SpecialLinearGroup (Fin 2) h.fixedField) :
    e * iotaLift h π hc hc0 k g * e⁻¹ = iotaLift h π hc hc0 k' (γ g) := by
  have := h.finite
  rw [iotaLift, conj_sl2Lift_apply_large hS.charF hS.large, hγ,
    ← sl2Lift_comp_large hS.charF hS.charF hS.large]
  rfl

theorem commute_rhoLift_rhoLift {i j k l : Fin r} (hij : i ≠ j) (hkl : k ≠ l)
    (hcomm : ∀ g g', Commute (rhoU (ε := ε) h hij g) (rhoU h hkl g'))
    (g g' : SpecialLinearGroup (Fin 2) K) :
    Commute (rhoLift h π hij g) (rhoLift h π hkl g') := by
  have := h.finite
  exact commute_sl2Lift_large hS.charK hS.charK hS.large _ _ hcomm g g'

theorem commute_rhoLift_iotaLift {i j : Fin r} (hij : i ≠ j) (k : Fin r)
    (hcomm : ∀ g g', Commute (rhoU (ε := ε) h hij g) (iotaU h hc hc0 k g'))
    (g : SpecialLinearGroup (Fin 2) K) (g' : SpecialLinearGroup (Fin 2) h.fixedField) :
    Commute (rhoLift h π hij g) (iotaLift h π hc hc0 k g') := by
  have := h.finite
  exact commute_sl2Lift_large hS.charK hS.charF hS.large _ _ hcomm g g'

theorem commute_iotaLift_iotaLift (k l : Fin r)
    (hcomm : ∀ g g', Commute (iotaU (ε := ε) h hc hc0 k g) (iotaU h hc hc0 l g'))
    (g g' : SpecialLinearGroup (Fin 2) h.fixedField) :
    Commute (iotaLift h π hc hc0 k g) (iotaLift h π hc hc0 l g') := by
  have := h.finite
  exact commute_sl2Lift_large hS.charF hS.charF hS.large _ _ hcomm g g'

theorem rhoLift_swap {i j : Fin r} (hij : i ≠ j) :
    rhoLift h π hij.symm = (rhoLift h π hij).comp swapSL := by
  have := h.finite
  rw [rhoLift, rhoLift, rhoU_swap, sl2Lift_comp_large hS.charK hS.charK hS.large]

theorem hRho_swap {i j : Fin r} (hij : i ≠ j) (t : Kˣ) :
    hRho h π hij.symm t = hRho h π hij t⁻¹ := by
  rw [hRho, hRho, MonoidHom.comp_apply, MonoidHom.comp_apply, rhoLift_swap h hS hij,
    MonoidHom.comp_apply, swapSL_sl2Diag]

end Basic

section Diag

variable {R : Type*} [Group R] [Finite R] {π : R →* hypSU h r ε} (hS : UHyp h π)
  {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)
include hS

theorem conj_rhoLift_of_diag {x : R} {q : HypIndex r ε → K}
    (hx : ((π x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q)
    {i j : Fin r} (hij : i ≠ j) (g : SpecialLinearGroup (Fin 2) K) :
    x * rhoLift h π hij g * x⁻¹ = rhoLift h π hij (sl2ConjDiag (Units.mk0 (q (.inl j) / q (.inl i))
      (div_ne_zero (diag_entry_ne_zero h hx _) (diag_entry_ne_zero h hx _))) g) := by
  refine conj_rhoLift_of h hS hij hij ?_ g
  refine MonoidHom.ext fun g' => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact conj_diag_rhoU h hx hij g'

theorem conj_iotaLift_of_diag {x : R} {q : HypIndex r ε → K}
    (hx : ((π x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q)
    (k : Fin r) (g : SpecialLinearGroup (Fin 2) h.fixedField) :
    x * iotaLift h π hc hc0 k g * x⁻¹ =
      iotaLift h π hc hc0 k (sl2ConjDiag (diagRatio h hx k) g) := by
  refine conj_iotaLift_of h hS hc hc0 ?_ g
  refine MonoidHom.ext fun g' => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact conj_diag_iotaU h hc hc0 hx k g'

theorem conj_hRho_of_diag {x : R} {q : HypIndex r ε → K}
    (hx : ((π x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q)
    {i j : Fin r} (hij : i ≠ j) (t : Kˣ) : x * hRho h π hij t * x⁻¹ = hRho h π hij t := by
  rw [hRho, MonoidHom.comp_apply, conj_rhoLift_of_diag h hS hx hij, sl2ConjDiag_sl2Diag]

theorem conj_hIota_of_diag {x : R} {q : HypIndex r ε → K}
    (hx : ((π x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q)
    (k : Fin r) (b : h.fixedFieldˣ) :
    x * hIota h π hc hc0 k b * x⁻¹ = hIota h π hc hc0 k b := by
  rw [hIota, MonoidHom.comp_apply, conj_iotaLift_of_diag h hS hc hc0 hx, sl2ConjDiag_sl2Diag]

theorem vRho_conj_of_diag {x : R} {q : HypIndex r ε → K}
    (hx : ((π x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q)
    {i j : Fin r} (hij : i ≠ j) :
    vRho h π hij * x * (vRho h π hij)⁻¹ = hRho h π hij (Units.mk0 (q (.inl j) / q (.inl i))
      (div_ne_zero (diag_entry_ne_zero h hx _) (diag_entry_ne_zero h hx _))) * x := by
  set u : Kˣ := Units.mk0 (q (.inl j) / q (.inl i))
    (div_ne_zero (diag_entry_ne_zero h hx _) (diag_entry_ne_zero h hx _))
  have E : x * vRho h π hij * x⁻¹ = hRho h π hij u⁻¹ * vRho h π hij := by
    rw [vRho, conj_rhoLift_of_diag h hS hx hij, sl2ConjDiag_sl2W, map_mul]
    rfl
  calc vRho h π hij * x * (vRho h π hij)⁻¹
      = (hRho h π hij u⁻¹)⁻¹ * (hRho h π hij u⁻¹ * vRho h π hij) * x * (vRho h π hij)⁻¹ := by
        group
    _ = (hRho h π hij u⁻¹)⁻¹ * (x * vRho h π hij * x⁻¹) * x * (vRho h π hij)⁻¹ := by rw [E]
    _ = hRho h π hij u * x := by rw [map_inv, inv_inv]; group

theorem vIota_conj_of_diag {x : R} {q : HypIndex r ε → K}
    (hx : ((π x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q)
    (k : Fin r) :
    vIota h π hc hc0 k * x * (vIota h π hc hc0 k)⁻¹ =
      hIota h π hc hc0 k (diagRatio h hx k) * x := by
  set u := diagRatio h hx k
  have E : x * vIota h π hc hc0 k * x⁻¹ = hIota h π hc hc0 k u⁻¹ * vIota h π hc hc0 k := by
    rw [vIota, conj_iotaLift_of_diag h hS hc hc0 hx, sl2ConjDiag_sl2W, map_mul]
    rfl
  calc vIota h π hc hc0 k * x * (vIota h π hc hc0 k)⁻¹
      = (hIota h π hc hc0 k u⁻¹)⁻¹ * (hIota h π hc hc0 k u⁻¹ * vIota h π hc hc0 k) * x *
          (vIota h π hc hc0 k)⁻¹ := by group
    _ = (hIota h π hc hc0 k u⁻¹)⁻¹ * (x * vIota h π hc hc0 k * x⁻¹) * x *
          (vIota h π hc hc0 k)⁻¹ := by rw [E]
    _ = hIota h π hc hc0 k u * x := by rw [map_inv, inv_inv]; group

end Diag

section Weyl

variable {R : Type*} [Group R] [Finite R] {π : R →* hypSU h r ε} (hS : UHyp h π)
  {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)
include hS

theorem vRho_conj_rhoLift {i j : Fin r} (hij : i ≠ j) {k l : Fin r} (hkl : k ≠ l)
    (g : SpecialLinearGroup (Fin 2) K) :
    vRho h π hij * rhoLift h π hkl g * (vRho h π hij)⁻¹ =
      rhoLift h π ((Equiv.swap i j).injective.ne hkl)
        (sl2ConjDiag (Units.mk0 (lineSign j l / lineSign j k)
          (div_ne_zero (lineSign_ne_zero j l) (lineSign_ne_zero j k))) g) := by
  refine conj_rhoLift_of h hS hkl _ (MonoidHom.ext fun g' => ?_) g
  rw [pi_vRho h hS hij]
  exact conj_rhoU_sl2W_rhoU h hij hkl g'

theorem vRho_conj_iotaLift {i j : Fin r} (hij : i ≠ j) (k : Fin r)
    (g : SpecialLinearGroup (Fin 2) h.fixedField) :
    vRho h π hij * iotaLift h π hc hc0 k g * (vRho h π hij)⁻¹ =
      iotaLift h π hc hc0 (Equiv.swap i j k) g := by
  refine conj_iotaLift_of h hS hc hc0 (γ := MonoidHom.id _) (MonoidHom.ext fun g' => ?_) g
  rw [pi_vRho h hS hij]
  exact conj_rhoU_sl2W_iotaU h hij hc hc0 k g'

theorem vRho_conj_vIota {i j : Fin r} (hij : i ≠ j) :
    vRho h π hij * vIota h π hc hc0 j * (vRho h π hij)⁻¹ = vIota h π hc hc0 i := by
  have e := vRho_conj_iotaLift h hS hc hc0 hij j sl2W
  rwa [Equiv.swap_apply_right] at e

theorem hRho_trans {i j k : Fin r} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (t : Kˣ) :
    hRho h π hik t = hRho h π hij t * hRho h π hjk t := by
  have e1 := vRho_conj_of_diag h hS (coe_pi_hRho h hS hjk t) hij
  have e2 := vRho_conj_rhoLift h hS hij hjk (sl2Diag t)
  rw [sl2ConjDiag_sl2Diag, rhoLift_congr h π _ hik (Equiv.swap_apply_right i j)
    (Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm)] at e2
  have hu : Units.mk0 (rhoDiag h j k t (.inl j) / rhoDiag h j k t (.inl i))
      (div_ne_zero (diag_entry_ne_zero h (coe_pi_hRho h hS hjk t) _)
        (diag_entry_ne_zero h (coe_pi_hRho h hS hjk t) _)) = t := by
    ext
    simp [rhoDiag, hij, hik]
  rw [hu] at e1
  change vRho h π hij * hRho h π hjk t * (vRho h π hij)⁻¹ = hRho h π hik t at e2
  rw [← e2, e1]

theorem hIota_eq_hRho_mul {i j : Fin r} (hij : i ≠ j) (b : h.fixedFieldˣ) :
    hIota h π hc hc0 i b = hRho h π hij (fcoe h b) * hIota h π hc hc0 j b := by
  have e1 := vRho_conj_of_diag h hS (coe_pi_hIota h hS hc hc0 j b) hij
  have e2 := vRho_conj_iotaLift h hS hc hc0 hij j (sl2Diag b)
  rw [Equiv.swap_apply_right] at e2
  have hu : Units.mk0 (iotaDiag h j b (.inl j) / iotaDiag h j b (.inl i))
      (div_ne_zero (diag_entry_ne_zero h (coe_pi_hIota h hS hc hc0 j b) _)
        (diag_entry_ne_zero h (coe_pi_hIota h hS hc hc0 j b) _)) = fcoe h b := by
    ext
    simp [iotaDiag, hij, coe_fcoe]
  rw [hu] at e1
  change vRho h π hij * hIota h π hc hc0 j b * (vRho h π hij)⁻¹ = hIota h π hc hc0 i b at e2
  rw [← e2, e1]

theorem vRho_conj_vRho_left {i j l : Fin r} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    vRho h π hij * vRho h π hjl * (vRho h π hij)⁻¹ = (vRho h π hil)⁻¹ := by
  have e := vRho_conj_rhoLift h hS hij hjl sl2W
  have hu : Units.mk0 (lineSign (K := K) j l / lineSign j j)
      (div_ne_zero (lineSign_ne_zero j l) (lineSign_ne_zero j j)) = -1 := by
    ext
    simp [lineSign, hjl.symm]
  rw [hu, sl2ConjDiag_neg_one_sl2W, map_inv, rhoLift_congr h π _ hil
    (Equiv.swap_apply_right i j) (Equiv.swap_apply_of_ne_of_ne hil.symm hjl.symm)] at e
  exact e

theorem vRho_conj_vRho_right {i j l : Fin r} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    vRho h π hjl * vRho h π hij * (vRho h π hjl)⁻¹ = vRho h π hil := by
  have e := vRho_conj_rhoLift h hS hjl hij sl2W
  have hu : Units.mk0 (lineSign (K := K) l j / lineSign l i)
      (div_ne_zero (lineSign_ne_zero l j) (lineSign_ne_zero l i)) = 1 := by
    ext
    simp [lineSign, hjl, hil]
  rw [hu, sl2ConjDiag_one, rhoLift_congr h π _ hil (Equiv.swap_apply_of_ne_of_ne hij hil)
    (Equiv.swap_apply_left j l)] at e
  exact e

theorem commute_vRho_vRho {i j k l : Fin r} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) : Commute (vRho h π hij) (vRho h π hkl) :=
  commute_rhoLift_rhoLift h hS hij hkl (commute_rhoU_rhoU h hij hkl hik hil hjk hjl) sl2W sl2W

theorem commute_vRho_vIota {i j k : Fin r} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Commute (vRho h π hij) (vIota h π hc hc0 k) :=
  commute_rhoLift_iotaLift h hS hc hc0 hij k (commute_rhoU_iotaU h hij hc hc0 hik hjk) sl2W sl2W

theorem commute_vIota_vIota {k l : Fin r} (hkl : k ≠ l) :
    Commute (vIota h π hc hc0 k) (vIota h π hc hc0 l) :=
  commute_iotaLift_iotaLift h hS hc hc0 k l (commute_iotaU_iotaU h hc hc0 hkl) sl2W sl2W

end Weyl

section Iota3

variable {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)

theorem iota3_sl2Diag (b : h.fixedFieldˣ) :
    iota3 h hc hc0 (sl2Diag b) = dkHom h (fcoe h b) := by
  have hb : h.bar ((b : h.fixedField) : K) = (b : h.fixedField) :=
    (h.mem_fixedField).1 (b : h.fixedField).2
  have hb0 : ((b : h.fixedField) : K) ≠ 0 := by
    intro h0
    exact b.ne_zero (Subtype.ext h0)
  apply Subtype.ext
  apply Units.ext
  rw [coe_iota3, coe_dkHom]
  ext x y
  fin_cases x <;> fin_cases y <;> simp [iota3Mat, dkVec, coe_fcoe, hb, hb0]

end Iota3

section Odd

variable {R : Type*} [Group R] [Finite R] {π : R →* hypSU h r 1} (hS : UHyp h π)
  {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)
include hS

theorem pi_kappaLift (k : Fin r) (X : gramSU h (gramJ3 K)) :
    π (kappaLift h π k X) = kappaU h k X :=
  map_su3Lift_large h hS.odd (gramJ3_herm h) det_gramJ3 hS.large _ X

theorem coe_pi_hKappa (k : Fin r) (a : Kˣ) :
    ((π (hKappa h π k a) : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) =
      diagonal (kappaDiag h k a) := by
  rw [hKappa, MonoidHom.comp_apply, pi_kappaLift h hS]
  exact coe_kappaU_dkHom h k a

theorem kappaLift_comp (k : Fin r) (γ : gramSU h (gramJ3 K) →* gramSU h (gramJ3 K)) :
    (kappaLift h π k).comp γ = su3Lift h π ((kappaU h k).comp γ) := by
  refine eq_su3Lift_large h hS.odd (gramJ3_herm h) det_gramJ3 hS.large ?_
  rw [← MonoidHom.comp_assoc]
  exact congrArg (fun α => α.comp γ)
    (comp_su3Lift_large h hS.odd (gramJ3_herm h) det_gramJ3 hS.large (kappaU h k))

theorem conj_kappaLift_of {e : R} {k k' : Fin r}
    {γ : gramSU h (gramJ3 K) →* gramSU h (gramJ3 K)}
    (hγ : (MulAut.conj (π e)).toMonoidHom.comp (kappaU h k) = (kappaU h k').comp γ)
    (X : gramSU h (gramJ3 K)) :
    e * kappaLift h π k X * e⁻¹ = kappaLift h π k' (γ X) := by
  have h1 := conj_su3Lift_apply_large h hS.odd (gramJ3_herm h) det_gramJ3 hS.large
    (kappaU h k) e X
  rw [hγ, ← kappaLift_comp h hS] at h1
  exact h1

theorem conj_kappaLift_of_diag {x : R} {q : HypIndex r 1 → K}
    (hx : ((π x : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) = diagonal q)
    (k : Fin r) (X : gramSU h (gramJ3 K)) :
    x * kappaLift h π k X * x⁻¹ = kappaLift h π k (conjDiagJ3 h (diag_trip_ne_zero h hx k)
      (diag_trip_02 h hx k) (diag_trip_11 h hx k) X) := by
  refine conj_kappaLift_of h hS ?_ X
  refine MonoidHom.ext fun X' => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact conj_diag_kappaU h hx k X'

theorem conj_hKappa_of_diag {x : R} {q : HypIndex r 1 → K}
    (hx : ((π x : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) = diagonal q)
    (k : Fin r) (a : Kˣ) : x * hKappa h π k a * x⁻¹ = hKappa h π k a := by
  rw [hKappa, MonoidHom.comp_apply, conj_kappaLift_of_diag h hS hx, conjDiagJ3_dkHom]

theorem vRho_conj_hKappa {i j : Fin r} (hij : i ≠ j) (k : Fin r) (a : Kˣ) :
    vRho h π hij * hKappa h π k a * (vRho h π hij)⁻¹ = hKappa h π (Equiv.swap i j k) a := by
  have e := conj_kappaLift_of h hS (e := vRho h π hij) (k := k) (k' := Equiv.swap i j k)
    (γ := conjDiagJ3 h (u := ![lineSign j k, 1, lineSign j k])
      (fun x => by fin_cases x <;> simp [lineSign_ne_zero])
      (lineSign_isometry_J3 h j k).1 (lineSign_isometry_J3 h j k).2)
    (MonoidHom.ext fun X' => by
      rw [pi_vRho h hS hij]
      exact conj_rhoU_sl2W_kappaU h hij k X') (dkHom h a)
  rw [conjDiagJ3_dkHom] at e
  exact e

theorem hKappa_eq_hRho_mul {i j : Fin r} (hij : i ≠ j) (a : Kˣ) :
    hKappa h π i a = hRho h π hij a * hKappa h π j a := by
  have e1 := vRho_conj_of_diag h hS (coe_pi_hKappa h hS j a) hij
  have e2 := vRho_conj_hKappa h hS hij j a
  rw [Equiv.swap_apply_right] at e2
  have hu : Units.mk0 (kappaDiag h j a (.inl j) / kappaDiag h j a (.inl i))
      (div_ne_zero (diag_entry_ne_zero h (coe_pi_hKappa h hS j a) _)
        (diag_entry_ne_zero h (coe_pi_hKappa h hS j a) _)) = a := by
    ext
    simp [kappaDiag, hij]
  rw [hu] at e1
  rw [← e2, e1]

theorem iotaLift_eq_kappaLift_comp (k : Fin r) :
    iotaLift h π hc hc0 k = (kappaLift h π k).comp (iota3 h hc hc0) := by
  have := h.finite
  symm
  refine eq_sl2Lift_large hS.charF hS.large ?_
  rw [← MonoidHom.comp_assoc, iotaU_eq_kappaU_comp h hc hc0 k]
  exact congrArg (fun α => α.comp (iota3 h hc hc0))
    (comp_su3Lift_large h hS.odd (gramJ3_herm h) det_gramJ3 hS.large (kappaU h k))

theorem hIota_eq_hKappa (k : Fin r) (b : h.fixedFieldˣ) :
    hIota h π hc hc0 k b = hKappa h π k (fcoe h b) := by
  rw [hIota, MonoidHom.comp_apply, iotaLift_eq_kappaLift_comp h hS hc hc0, MonoidHom.comp_apply,
    iota3_sl2Diag h hc hc0]
  rfl

end Odd

end CFSG.RankThree.CentralLiftU
