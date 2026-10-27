module

public import CFSG.Quasithin.H13.AS91Sec8V1Cocycle
public import CFSG.Quasithin.H13.AS91Sec8V1Gens
public import CFSG.Quasithin.H13.AS91Sec8V1Map
public import Certificates.Certificate664013

public section

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Monster.Code
open scoped Pointwise symmDiff

@[expose] def gA : ↥sextStab := ⟨sxA, sxA_mem⟩

@[expose] def gB : ↥sextStab := ⟨sxB, sxB_mem⟩

theorem gA_pow_five : gA ^ 5 = 1 := by
  refine Subtype.ext ?_
  show (sxA : Equiv.Perm (Fin 24)) ^ 5 = 1
  decide +kernel

theorem closure_gA_gB (hgen : sextStab = Subgroup.closure ({sxA, sxB} : Set S24)) :
    Subgroup.closure ({gA, gB} : Set ↥sextStab) = ⊤ := by
  set K : Subgroup ↥sextStab := Subgroup.closure {gA, gB} with hK
  have hle : Subgroup.closure ({sxA, sxB} : Set S24) ≤ K.map sextStab.subtype := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨gA, Subgroup.subset_closure (by simp), rfl⟩
    · exact ⟨gB, Subgroup.subset_closure (by simp), rfl⟩
  refine Subgroup.ext fun s => ⟨fun _ => Subgroup.mem_top s, fun _ => ?_⟩
  have hs : (s : S24) ∈ Subgroup.closure ({sxA, sxB} : Set S24) := by
    rw [← hgen]
    exact s.2
  obtain ⟨k, hk, hke⟩ := hle hs
  have hks : k = s := Subtype.ext hke
  rwa [hks] at hk

theorem chi_gA_eq_one (χ : ↥sextStab →* Multiplicative (ZMod 2)) : χ gA = 1 := by
  have h2 : ∀ u : Multiplicative (ZMod 2), u ^ 2 = 1 := by decide
  have h5 : χ gA ^ 5 = 1 := by
    rw [← MonoidHom.map_pow, gA_pow_five, MonoidHom.map_one]
  have h4 : χ gA ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2]
  rw [show (5 : ℕ) = 4 + 1 from rfl, pow_add, h4, one_mul, pow_one] at h5
  exact h5

theorem chi_gB_ne_one (hgen : sextStab = Subgroup.closure ({sxA, sxB} : Set S24))
    (χ : ↥sextStab →* Multiplicative (ZMod 2)) (hχ : χ ≠ 1) : χ gB ≠ 1 := by
  intro hb
  apply hχ
  have hker : Subgroup.closure ({gA, gB} : Set ↥sextStab) ≤ MonoidHom.ker χ := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · show χ gA = 1
      exact chi_gA_eq_one χ
    · show χ gB = 1
      exact hb
  ext s
  exact MonoidHom.mem_ker.1 (hker (closure_gA_gB hgen ▸ Subgroup.mem_top s))

@[expose] def cocPerm : CocL → ↥sextStab
  | .a => gA
  | .ai => gA⁻¹
  | .b => gB
  | .bi => gB⁻¹

@[expose] def cocEvalW : List CocL → ↥sextStab
  | [] => 1
  | l :: ls => cocPerm l * cocEvalW ls

theorem hasArr_cocPerm (l : CocL) : HasArr (↑(cocPerm l) : S24) (cocImg l) := by
  cases l
  · show HasArr (sxA : S24) cocArrA
    unfold HasArr
    decide +kernel
  · show HasArr (sxA⁻¹ : S24) cocArrAi
    unfold HasArr
    decide +kernel
  · show HasArr (sxB : S24) cocArrB
    unfold HasArr
    decide +kernel
  · show HasArr (sxB⁻¹ : S24) cocArrBi
    unfold HasArr
    decide +kernel

theorem hasArr_cocPerm_inv (l : CocL) : HasArr ((↑(cocPerm l) : S24))⁻¹ (cocInvImg l) := by
  cases l
  · show HasArr (sxA⁻¹ : S24) cocArrAi
    unfold HasArr
    decide +kernel
  · show HasArr (sxA : S24) cocArrA
    unfold HasArr
    decide +kernel
  · show HasArr (sxB⁻¹ : S24) cocArrBi
    unfold HasArr
    decide +kernel
  · show HasArr (sxB : S24) cocArrB
    unfold HasArr
    decide +kernel

theorem hasArr_cocInvArrOf (x y : ℕ) : ∀ w : List CocL,
    HasArr ((cocEvalW w : ↥sextStab) : S24)⁻¹ (cocInvArrOf x y w)
  | [] => hasArr_one
  | l :: ls => by
    show HasArr ((↑(cocPerm l) * ↑(cocEvalW ls) : S24))⁻¹
      (cArr (cocInvArrOf x y ls) (cocInvImg l))
    rw [mul_inv_rev]
    exact hasArr_mul (hasArr_cocInvArrOf x y ls) (hasArr_cocPerm_inv l)

theorem cocMaskVal_nil (x y : ℕ) : cocMaskVal x y [] = 0 := rfl

theorem cocMaskVal_cons (x y : ℕ) (l : CocL) (ls : List CocL) :
    cocMaskVal x y (l :: ls) =
      act11 (cocInvArrOf x y ls) (cocVal x y l) ^^^ cocMaskVal x y ls := rfl

theorem cocMaskVal_lt (x y : ℕ) : ∀ w : List CocL, cocMaskVal x y w < 2 ^ 11
  | [] => Nat.two_pow_pos 11
  | l :: ls => by
    rw [cocMaskVal_cons]
    exact Nat.xor_lt_two_pow (act11_lt _ _) (cocMaskVal_lt x y ls)

theorem cocPerm_spec (D : ↥sextStab → W11) (hD : IsRightCocycle sextStab sextStab_le D)
    (x y : ℕ) (hx : D gA = toW 11 x) (hy : D gB = toW 11 y) (l : CocL) :
    D (cocPerm l) = toW 11 (cocVal x y l) := by
  cases l
  · exact hx
  · show D gA⁻¹ = toW 11 (act11 cocArrA x)
    rw [hD.map_inv, hx, rho11_toW sextStab sextStab_le gA (hasArr_cocPerm .a) x]
    rfl
  · exact hy
  · show D gB⁻¹ = toW 11 (act11 cocArrB y)
    rw [hD.map_inv, hy, rho11_toW sextStab sextStab_le gB (hasArr_cocPerm .b) y]
    rfl

theorem cocFold_spec (D : ↥sextStab → W11) (hD : IsRightCocycle sextStab sextStab_le D)
    (x y : ℕ) (hx : D gA = toW 11 x) (hy : D gB = toW 11 y) :
    ∀ w : List CocL, D (cocEvalW w) = toW 11 (cocMaskVal x y w)
  | [] => by
    rw [cocEvalW, cocMaskVal_nil, hD.map_one, toW_zero]
  | l :: ls => by
    have hletter : D (cocPerm l) = toW 11 (cocVal x y l) :=
      cocPerm_spec D hD x y hx hy l
    have hrec : D (cocEvalW ls) = toW 11 (cocMaskVal x y ls) :=
      cocFold_spec D hD x y hx hy ls
    have hstep : D (cocEvalW (l :: ls)) =
        (rho11 sextStab sextStab_le (cocEvalW ls))⁻¹ (toW 11 (cocVal x y l)) *
          toW 11 (cocMaskVal x y ls) := by
      rw [show cocEvalW (l :: ls) = cocPerm l * cocEvalW ls from rfl]
      rw [hD (cocPerm l) (cocEvalW ls), hletter, hrec]
    rw [hstep, cocMaskVal_cons, toW_xor]
    rw [show (rho11 sextStab sextStab_le (cocEvalW ls))⁻¹
        = rho11 sextStab sextStab_le (cocEvalW ls)⁻¹ from
      _root_.map_inv (rho11 sextStab sextStab_le) (cocEvalW ls)]
    exact congrArg (fun u => u * toW 11 (cocMaskVal x y ls))
      (rho11_toW sextStab sextStab_le (cocEvalW ls)⁻¹
        (hasArr_cocInvArrOf x y ls) (cocVal x y l))

theorem cocRelArr_eq_idArr {w : List CocL} (hw : w ∈ cocRelWords) : cocRelArr w = idArr := by
  have h := Certificates.certificate664013
  simp only [cert664013Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨-, -⟩, h1⟩, -⟩, -⟩ := h
  rw [cocRelCheck, List.all_eq_true] at h1
  simpa using h1 w hw

theorem hasArr_cocEvalW : ∀ w : List CocL,
    HasArr ((cocEvalW w : ↥sextStab) : S24) (cocRelArr w)
  | [] => hasArr_one
  | l :: ls => by
    show HasArr ((↑(cocPerm l) * ↑(cocEvalW ls) : S24)) (cArr (cocImg l) (cocRelArr ls))
    exact hasArr_mul (hasArr_cocPerm l) (hasArr_cocEvalW ls)

theorem cocEvalW_relWords {w : List CocL} (hw : w ∈ cocRelWords) : cocEvalW w = 1 := by
  have h1 : HasArr ((cocEvalW w : ↥sextStab) : S24) (cocRelArr w) := hasArr_cocEvalW w
  rw [cocRelArr_eq_idArr hw] at h1
  exact Subtype.ext (perm_eq_of_hasArr h1 hasArr_one)

theorem cocCertA_spec {x : ℕ} (hx : x < 2048) (hN : cocMaskVal x 0 cocAFive = 0) :
    cocCobMask cocArrAi (cocTabA.getD x 0) = x := by
  have h := Certificates.certificate664013
  simp only [cert664013Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨-, -⟩, -⟩, h1⟩, -⟩ := h
  rw [cocCertA, List.all_eq_true] at h1
  have h2 := h1 x (List.mem_range.2 hx)
  rw [Bool.or_eq_true] at h2
  rcases h2 with h2 | h2
  · rw [Bool.not_eq_true'] at h2
    exact absurd hN (by
      intro hc
      rw [hc] at h2
      simpa using h2)
  · simpa using h2

theorem cocCertB_spec {y : ℕ} (hy : y < 2048)
    (hc : cocRelWords.all (fun w => cocMaskVal 0 y w == 0) = true) :
    cocCobMask cocArrAi (cocWitW y) ^^^ (if cocWitBeta y then cocDBetaA else 0) = 0 ∧
      cocCobMask cocArrBi (cocWitW y) ^^^ (if cocWitAlpha y then cocZeta else 0) ^^^
        (if cocWitBeta y then cocDBetaB else 0) = y := by
  have h := Certificates.certificate664013
  simp only [cert664013Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h1⟩ := h
  rw [cocCertB, List.all_eq_true] at h1
  have h2 := h1 y (List.mem_range.2 hy)
  rw [Bool.or_eq_true] at h2
  rcases h2 with h2 | h2
  · rw [Bool.not_eq_true'] at h2
    exact absurd hc (by rw [h2]; simp)
  · simpa only [Bool.and_eq_true, beq_iff_eq] using h2

theorem hasArr_gA_inv : HasArr ((↑(gA) : S24))⁻¹ cocArrAi := hasArr_cocPerm_inv .a

theorem hasArr_gB_inv : HasArr ((↑(gB) : S24))⁻¹ cocArrBi := hasArr_cocPerm_inv .b

theorem dBeta_gA : dBeta sextStab gA = toW 11 cocDBetaA := by
  have hp : (((gA : ↥sextStab) : S24))⁻¹ 0 = 18 := by
    show (sxA⁻¹ : Equiv.Perm (Fin 24)) 0 = 18
    decide +kernel
  have hset : ({0} : Finset (Fin 24)) ∆ {18} = maskFin (2 ^ 0 + 2 ^ 18) := by decide +kernel
  unfold dBeta
  rw [hp, hset, setClass_maskFin,
    show actM ccECols (2 ^ 0 + 2 ^ 18) = cocDBetaA from by decide +kernel]

theorem dBeta_gB : dBeta sextStab gB = toW 11 cocDBetaB := by
  have hp : (((gB : ↥sextStab) : S24))⁻¹ 0 = 23 := by
    show (sxB⁻¹ : Equiv.Perm (Fin 24)) 0 = 23
    decide +kernel
  have hset : ({0} : Finset (Fin 24)) ∆ {23} = maskFin (2 ^ 0 + 2 ^ 23) := by decide +kernel
  unfold dBeta
  rw [hp, hset, setClass_maskFin,
    show actM ccECols (2 ^ 0 + 2 ^ 23) = cocDBetaB from by decide +kernel]

theorem sextClass_zero_eq : sextClass (sextFin 0) = toW 11 cocZeta :=
  sextClass_sextFin_zero

theorem rho11_sextClass_zero (s : ↥sextStab) :
    rho11 sextStab sextStab_le s (sextClass (sextFin 0)) = sextClass (sextFin 0) := by
  have hsext : IsSextet (sextFin 0) := isSextet_sextFin (by norm_num)
  have hstab : (s : S24) • sextFin 0 = sextFin 0 :=
    MulAction.mem_stabilizer_iff.1 s.2.2
  have h := sextClass_smul (σ := (s : S24)) s.2.1 hsext
  rw [hstab] at h
  rw [CFSG.Quasithin.H13.AS91.Loc49.rho11_sextStab_apply]
  exact h.symm

theorem isRightCocycle_one : IsRightCocycle sextStab sextStab_le (fun _ => (1 : W11)) := by
  intro s t
  simp

@[expose] noncomputable def cocChar (χ : ↥sextStab →* Multiplicative (ZMod 2)) (α : Bool) :
    ↥sextStab → W11 :=
  fun s => if α then (if χ s = 1 then 1 else sextClass (sextFin 0)) else 1

@[expose] noncomputable def cocBeta (β : Bool) : ↥sextStab → W11 :=
  fun s => if β then dBeta sextStab s else 1

@[expose] noncomputable def cocFamily (χ : ↥sextStab →* Multiplicative (ZMod 2)) (w : W11)
    (α β : Bool) : ↥sextStab → W11 :=
  fun s => coboundary sextStab sextStab_le w s * cocChar χ α s * cocBeta β s

theorem isRightCocycle_cocChar (χ : ↥sextStab →* Multiplicative (ZMod 2)) (α : Bool) :
    IsRightCocycle sextStab sextStab_le (cocChar χ α) := by
  cases α
  · exact isRightCocycle_one
  · exact isRightCocycle_char χ rho11_sextClass_zero

theorem isRightCocycle_cocBeta (β : Bool) :
    IsRightCocycle sextStab sextStab_le (cocBeta β) := by
  cases β
  · exact isRightCocycle_one
  · exact isRightCocycle_dBeta

theorem isRightCocycle_cocFamily (χ : ↥sextStab →* Multiplicative (ZMod 2)) (w : W11)
    (α β : Bool) : IsRightCocycle sextStab sextStab_le (cocFamily χ w α β) :=
  ((isRightCocycle_coboundary w).mul (isRightCocycle_cocChar χ α)).mul
    (isRightCocycle_cocBeta β)

theorem cocChar_gA (χ : ↥sextStab →* Multiplicative (ZMod 2)) (α : Bool) :
    cocChar χ α gA = 1 := by
  cases α
  · rfl
  · simp [cocChar, chi_gA_eq_one χ]

theorem cocChar_gB (hgen : sextStab = Subgroup.closure ({sxA, sxB} : Set S24))
    (χ : ↥sextStab →* Multiplicative (ZMod 2)) (hχ : χ ≠ 1) (α : Bool) :
    cocChar χ α gB = if α then sextClass (sextFin 0) else 1 := by
  cases α
  · rfl
  · simp [cocChar, chi_gB_ne_one hgen χ hχ]

theorem cocFamily_gA (χ : ↥sextStab →* Multiplicative (ZMod 2)) (w : W11) (α β : Bool) :
    cocFamily χ w α β gA = coboundary sextStab sextStab_le w gA *
      (if β then toW 11 cocDBetaA else 1) := by
  unfold cocFamily
  rw [cocChar_gA]
  cases β
  · simp [cocBeta]
  · simp [cocBeta, dBeta_gA]

theorem cocFamily_gB (hgen : sextStab = Subgroup.closure ({sxA, sxB} : Set S24))
    (χ : ↥sextStab →* Multiplicative (ZMod 2)) (hχ : χ ≠ 1) (w : W11) (α β : Bool) :
    cocFamily χ w α β gB = coboundary sextStab sextStab_le w gB *
      (if α then sextClass (sextFin 0) else 1) * (if β then toW 11 cocDBetaB else 1) := by
  unfold cocFamily
  rw [cocChar_gB hgen χ hχ]
  cases β
  · simp [cocBeta]
  · simp [cocBeta, dBeta_gB]

theorem coboundary_gA (w : ℕ) :
    coboundary sextStab sextStab_le (toW 11 w) gA = toW 11 (cocCobMask cocArrAi w) := by
  unfold coboundary
  rw [show (rho11 sextStab sextStab_le gA)⁻¹ = rho11 sextStab sextStab_le gA⁻¹ from
    (_root_.map_inv (rho11 sextStab sextStab_le) gA).symm]
  rw [rho11_toW sextStab sextStab_le gA⁻¹ hasArr_gA_inv w, W11_inv, ← toW_xor]
  rfl

theorem coboundary_gB (w : ℕ) :
    coboundary sextStab sextStab_le (toW 11 w) gB = toW 11 (cocCobMask cocArrBi w) := by
  unfold coboundary
  rw [show (rho11 sextStab sextStab_le gB)⁻¹ = rho11 sextStab sextStab_le gB⁻¹ from
    (_root_.map_inv (rho11 sextStab sextStab_le) gB).symm]
  rw [rho11_toW sextStab sextStab_le gB⁻¹ hasArr_gB_inv w, W11_inv, ← toW_xor]
  rfl

theorem mulAut_cobMul {M : Type*} [CommGroup M] (f : M ≃* M) (w v : M) :
    (f w * w⁻¹) * (f v * v⁻¹) = f (w * v) * (w * v)⁻¹ := by
  rw [map_mul, mul_inv]
  ac_rfl

theorem mulAut_cobMul_reorder {M : Type*} [CommGroup M] (f : M ≃* M) (w v a b : M) :
    (f w * w⁻¹) * a * b * (f v * v⁻¹) = (f (w * v) * (w * v)⁻¹) * a * b := by
  calc (f w * w⁻¹) * a * b * (f v * v⁻¹)
      = ((f w * w⁻¹) * (f v * v⁻¹)) * a * b := by ac_rfl
    _ = (f (w * v) * (w * v)⁻¹) * a * b := by rw [mulAut_cobMul]

theorem mul_coboundary_comm (w v a b : W11) (s : ↥sextStab) :
    coboundary sextStab sextStab_le w s * a * b * coboundary sextStab sextStab_le v s =
      coboundary sextStab sextStab_le (w * v) s * a * b := by
  unfold coboundary
  exact mulAut_cobMul_reorder (rho11 sextStab sextStab_le s)⁻¹ w v a b

theorem toW_mul_if (a b : ℕ) (β : Bool) :
    toW 11 a * (if β then toW 11 b else 1) = toW 11 (a ^^^ (if β then b else 0)) := by
  cases β <;> simp [toW_xor, toW_zero]

theorem sextStabCocycle_of_closure
    (hgen : sextStab = Subgroup.closure ({sxA, sxB} : Set S24)) : SextStabCocycle := by
  intro D hD χ hχ
  have htop : Subgroup.closure ({gA, gB} : Set ↥sextStab) = ⊤ := closure_gA_gB hgen
  have hχB : χ gB ≠ 1 := chi_gB_ne_one hgen χ hχ
  obtain ⟨xm, hxm_lt, hxm⟩ := toW_surj 11 (D gA)
  obtain ⟨ym, hym_lt, hym⟩ := toW_surj 11 (D gB)
  have hxm_lt : xm < 2048 := by simpa using hxm_lt
  have hym_lt : ym < 2048 := by simpa using hym_lt
  have hconstr : ∀ w ∈ cocRelWords, cocMaskVal xm ym w = 0 := by
    intro w hw
    have h1 : D (cocEvalW w) = 1 := by rw [cocEvalW_relWords hw, hD.map_one]
    have h2 := cocFold_spec D hD xm ym hxm.symm hym.symm w
    rw [h1] at h2
    have h3 : toW 11 0 = toW 11 (cocMaskVal xm ym w) := by
      rw [toW_zero]
      exact h2
    exact (toW_inj (Nat.two_pow_pos 11) (cocMaskVal_lt xm ym w) h3).symm
  have hA5 : cocMaskVal xm 0 cocAFive = 0 := hconstr cocAFive (by decide +kernel)
  have hwA := cocCertA_spec hxm_lt hA5
  set w0 : W11 := toW 11 (cocTabA.getD xm 0) with hw0
  have hcobA : coboundary sextStab sextStab_le w0 gA = toW 11 xm := by
    rw [hw0, coboundary_gA]
    exact congrArg (toW 11) hwA
  set D' : ↥sextStab → W11 := fun s => D s * coboundary sextStab sextStab_le w0 s with hD'
  have hD'coc : IsRightCocycle sextStab sextStab_le D' := by
    rw [hD']
    exact hD.mul (isRightCocycle_coboundary w0)
  have hD'A : D' gA = 1 := by
    rw [hD']
    show D gA * coboundary sextStab sextStab_le w0 gA = 1
    rw [← hxm, hcobA, W11_mul_self]
  obtain ⟨ym', hym'_lt, hym'⟩ := toW_surj 11 (D' gB)
  have hym'_lt : ym' < 2048 := by simpa using hym'_lt
  have hconstr' : cocRelWords.all (fun w => cocMaskVal 0 ym' w == 0) = true := by
    rw [List.all_eq_true]
    intro w hw
    have h1 : D' (cocEvalW w) = 1 := by rw [cocEvalW_relWords hw, hD'coc.map_one]
    have h2 := cocFold_spec D' hD'coc 0 ym' (by rw [hD'A, toW_zero]) hym'.symm w
    rw [h1] at h2
    have h3 : toW 11 0 = toW 11 (cocMaskVal 0 ym' w) := by
      rw [toW_zero]
      exact h2
    have h4 : cocMaskVal 0 ym' w = 0 :=
      (toW_inj (Nat.two_pow_pos 11) (cocMaskVal_lt 0 ym' w) h3).symm
    rw [h4]
    rfl
  obtain ⟨hcB1, hcB2⟩ := cocCertB_spec hym'_lt hconstr'
  refine ⟨toW 11 (cocWitW ym') * w0, cocWitAlpha ym', cocWitBeta ym', fun s => ?_⟩
  have hFcoc : IsRightCocycle sextStab sextStab_le
      (cocFamily χ (toW 11 (cocWitW ym')) (cocWitAlpha ym') (cocWitBeta ym')) :=
    isRightCocycle_cocFamily χ _ _ _
  have hFA : cocFamily χ (toW 11 (cocWitW ym')) (cocWitAlpha ym') (cocWitBeta ym') gA =
      D' gA := by
    rw [hD'A, cocFamily_gA, coboundary_gA, toW_mul_if, hcB1, toW_zero]
  have hFB : cocFamily χ (toW 11 (cocWitW ym')) (cocWitAlpha ym') (cocWitBeta ym') gB =
      D' gB := by
    rw [← hym', cocFamily_gB hgen χ hχ, coboundary_gB, sextClass_zero_eq, toW_mul_if,
      toW_mul_if, hcB2]
  have hFD' : ∀ s, cocFamily χ (toW 11 (cocWitW ym')) (cocWitAlpha ym') (cocWitBeta ym') s =
      D' s :=
    IsRightCocycle.eq_of_eqOn hFcoc hD'coc htop (by
      intro s hs
      rcases hs with h | h
      · rw [h]; exact hFA
      · rw [h]; exact hFB)
  have hDs : D s = D' s * coboundary sextStab sextStab_le w0 s := by
    rw [hD']
    rw [mul_assoc, W11_mul_self, mul_one]
  rw [hDs, ← hFD' s]
  exact mul_coboundary_comm (toW 11 (cocWitW ym')) w0 (cocChar χ (cocWitAlpha ym') s)
    (cocBeta (cocWitBeta ym') s) s

end CFSG.Quasithin.H13.AS91.M24G
