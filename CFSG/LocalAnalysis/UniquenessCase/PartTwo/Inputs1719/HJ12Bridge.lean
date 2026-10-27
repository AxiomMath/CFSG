module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12Check
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJModel
public import CFSG.GF2Type.Smith1979.GammaU.PairCensus
public import CFSG.GF2Type.Smith1979.GammaU.SigmaBase

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Sporadic.J2.Module12 (A12 B12 toM12 a12 b12)

namespace HJBridge

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Enum (enumGrp_sound card_genGrp)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12 (hjAc hjBc hjJc hjTauc wordR)

noncomputable def ofLin : (V12 ≃ₗ[ZMod 2] V12) →* MulAut W12 where
  toFun u := AddEquiv.toMultiplicative u.toAddEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

theorem ofLin_apply (u : V12 ≃ₗ[ZMod 2] V12) (v : V12) :
    ofLin u (Multiplicative.ofAdd v) = Multiplicative.ofAdd (u v) := rfl

theorem ofLin_injective : Function.Injective ofLin := by
  intro u u' h
  refine LinearEquiv.ext fun v => ?_
  have := congrArg (fun φ : MulAut W12 => Multiplicative.toAdd (φ (Multiplicative.ofAdd v))) h
  exact this




theorem linOfRows_hjAc (v : V12) :
    linOfRows hjAc v = (A12 : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec v := by
  have hf : linOfRows hjAc = Matrix.mulVecLin (A12 : Matrix (Fin 12) (Fin 12) (ZMod 2)) :=
    linMap_ext fun j => by
      rw [linOfRows_unit, Matrix.mulVecLin_apply]
      show vecOf hjAc[(j : ℕ)]! = (toM12 a12).mulVec (vecOf (2 ^ (j : ℕ)))
      revert j
      decide +kernel
  exact LinearMap.congr_fun hf v

theorem linOfRows_hjBc (v : V12) :
    linOfRows hjBc v = (B12 : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec v := by
  have hf : linOfRows hjBc = Matrix.mulVecLin (B12 : Matrix (Fin 12) (Fin 12) (ZMod 2)) :=
    linMap_ext fun j => by
      rw [linOfRows_unit, Matrix.mulVecLin_apply]
      show vecOf hjBc[(j : ℕ)]! = (toM12 b12).mulVec (vecOf (2 ^ (j : ℕ)))
      revert j
      decide +kernel
  exact LinearMap.congr_fun hf v

def hjJx : List (List ℕ) := [
  [1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1],
  [0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1],
  [1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1],
  [0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0],
  [0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1],
  [1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0],
  [1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0],
  [1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1],
  [0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1],
  [0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1],
  [0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1],
  [1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]]

def hjJxi : List (List ℕ) := [
  [0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1],
  [0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1],
  [1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1],
  [0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0],
  [0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1],
  [1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0],
  [1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0],
  [1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1],
  [0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1],
  [0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1],
  [0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1],
  [1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]]

theorem hjJx_mul : toM12 hjJx * toM12 hjJxi = 1 := by decide +kernel
theorem hjJxi_mul : toM12 hjJxi * toM12 hjJx = 1 := by decide +kernel

noncomputable def J12x : GL (Fin 12) (ZMod 2) :=
  ⟨toM12 hjJx, toM12 hjJxi, hjJx_mul, hjJxi_mul⟩

theorem J12x_comm_A12 : J12x * A12 = A12 * J12x := Units.ext (by decide +kernel)
theorem J12x_comm_B12 : J12x * B12 = B12 * J12x := Units.ext (by decide +kernel)

theorem linOfRows_hjJc (v : V12) :
    linOfRows hjJc v = (J12x : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec v := by
  have hf : linOfRows hjJc = Matrix.mulVecLin (J12x : Matrix (Fin 12) (Fin 12) (ZMod 2)) :=
    linMap_ext fun j => by
      rw [linOfRows_unit, Matrix.mulVecLin_apply]
      show vecOf hjJc[(j : ℕ)]! = (toM12 hjJx).mulVec (vecOf (2 ^ (j : ℕ)))
      revert j
      decide +kernel
  exact LinearMap.congr_fun hf v

def hjTauR : List (List ℕ) := [
  [0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1],
  [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1],
  [0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 1],
  [0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0],
  [1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0],
  [0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0],
  [1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0],
  [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1],
  [0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1],
  [1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1],
  [0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1],
  [1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]]

def hjTauRi : List (List ℕ) := [
  [0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1],
  [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1],
  [0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 1],
  [0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0],
  [1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0],
  [0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0],
  [1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0],
  [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1],
  [0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1],
  [1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1],
  [0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1],
  [1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]]

theorem hjTauR_mul : toM12 hjTauR * toM12 hjTauRi = 1 := by decide +kernel
theorem hjTauRi_mul : toM12 hjTauRi * toM12 hjTauR = 1 := by decide +kernel

noncomputable def hjTauM : GL (Fin 12) (ZMod 2) :=
  ⟨toM12 hjTauR, toM12 hjTauRi, hjTauR_mul, hjTauRi_mul⟩

theorem linOfRows_hjTauc (v : V12) :
    linOfRows hjTauc v = (hjTauM : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec v := by
  have hf : linOfRows hjTauc = Matrix.mulVecLin (hjTauM : Matrix (Fin 12) (Fin 12) (ZMod 2)) :=
    linMap_ext fun j => by
      rw [linOfRows_unit, Matrix.mulVecLin_apply]
      show vecOf hjTauc[(j : ℕ)]! = (toM12 hjTauR).mulVec (vecOf (2 ^ (j : ℕ)))
      revert j
      decide +kernel
  exact LinearMap.congr_fun hf v

theorem J12x_pow_three : J12x ^ 3 = 1 := Units.ext (by
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  show toM12 hjJx ^ 3 = 1
  decide +kernel)

theorem J12x_ne_one : J12x ≠ 1 := fun h => by
  have h1 : toM12 hjJx = 1 := congrArg Units.val h
  revert h1
  decide +kernel

noncomputable def linOfGL (g : GL (Fin 12) (ZMod 2)) : V12 ≃ₗ[ZMod 2] V12 :=
  LinearEquiv.ofLinear (Matrix.mulVecLin (g : Matrix (Fin 12) (Fin 12) (ZMod 2)))
    (Matrix.mulVecLin ((g⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)))
    (by rw [← Matrix.mulVecLin_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.mulVecLin_one])

theorem hjAct_eq_ofLin (g : GL (Fin 12) (ZMod 2)) : hjAct g = ofLin (linOfGL g) := by
  ext w
  rfl

def RowsOf (x : MulAut W12) (r : Array ℕ) : Prop :=
  ∀ v : V12, x (Multiplicative.ofAdd v) = Multiplicative.ofAdd (linOfRows r v)


theorem rowsOf_one : RowsOf 1 idR := fun v => by rw [linOfRows_idR]; rfl

theorem rowsOf_mul {x y : MulAut W12} {r s : Array ℕ} (hx : RowsOf x r) (hy : RowsOf y s) :
    RowsOf (x * y) (mulR r s) := fun v => by
  rw [MulAut.mul_apply, hy v, hx, linOfRows_mulR]

theorem rowsOf_gen (l : ℕ) :
    RowsOf (if l = 0 then hjAct A12 else hjAct B12) (if l = 0 then hjAc else hjBc) := fun v => by
  split_ifs
  · rw [linOfRows_hjAc]; rfl
  · rw [linOfRows_hjBc]; rfl

theorem rowsOf_foldl (w : List ℕ) : ∀ (x : MulAut W12) (acc : Array ℕ), RowsOf x acc →
    RowsOf (x * hjWord w)
      (w.foldl (fun acc l => mulR acc (if l = 0 then hjAc else hjBc)) acc) := by
  induction w with
  | nil => intro x acc h; simpa [hjWord] using h
  | cons l w ih =>
    intro x acc h
    have e : x * hjWord (l :: w) = (x * (if l = 0 then hjAct A12 else hjAct B12)) * hjWord w := by
      simp only [hjWord, List.map_cons, List.prod_cons, mul_assoc]
    rw [e, List.foldl_cons]
    exact ih _ _ (rowsOf_mul h (rowsOf_gen l))

theorem rowsOf_hjWord (w : List ℕ) : RowsOf (hjWord w) (wordR w) := by
  have h := rowsOf_foldl w 1 idR rowsOf_one
  rw [one_mul] at h
  simpa only [HJ12.wordR, native_mulR, native_idR] using h

theorem rowsOf_unique {x y : MulAut W12} {r : Array ℕ} (hx : RowsOf x r) (hy : RowsOf y r) :
    x = y :=
  MulEquiv.ext fun w => by
    have h1 := hx (Multiplicative.toAdd w)
    have h2 := hy (Multiplicative.toAdd w)
    rw [ofAdd_toAdd] at h1 h2
    rw [h1, h2]

theorem rowsOf_inv {x : MulAut W12} {r : Array ℕ} (hx : RowsOf x r)
    (h1 : mulR r (Viol.invR r) = idR) : RowsOf x⁻¹ (Viol.invR r) := by
  intro v
  have h2 : x (Multiplicative.ofAdd (linOfRows (Viol.invR r) v)) = Multiplicative.ofAdd v := by
    rw [hx, ← linOfRows_mulR, h1, linOfRows_idR]
  show x⁻¹ (Multiplicative.ofAdd v) = Multiplicative.ofAdd (linOfRows (Viol.invR r) v)
  rw [← h2, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

theorem rowsOf_conj {x y : MulAut W12} {r s : Array ℕ} (hx : RowsOf x r) (hy : RowsOf y s)
    (hr : mulR r (Viol.invR r) = idR) :
    RowsOf (x * y * x⁻¹) (mulR (mulR r s) (Viol.invR r)) :=
  rowsOf_mul (rowsOf_mul hx hy) (rowsOf_inv hx hr)

theorem genSet_eq : Viol.GenSet [hjAc, hjBc] = {linOfGL A12, linOfGL B12} := by
  ext l
  simp only [Viol.GenSet, List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨r, hr, hl⟩
    rcases hr with rfl | rfl
    · left; exact LinearEquiv.ext fun x => by rw [hl, linOfRows_hjAc]; rfl
    · right; exact LinearEquiv.ext fun x => by rw [hl, linOfRows_hjBc]; rfl
  · rintro (rfl | rfl)
    · exact ⟨hjAc, Or.inl rfl, fun x => by rw [linOfRows_hjAc]; rfl⟩
    · exact ⟨hjBc, Or.inr rfl, fun x => by rw [linOfRows_hjBc]; rfl⟩

theorem hjL0_eq_map_genGrp : hjL0 = (Viol.genGrp [hjAc, hjBc]).map ofLin := by
  rw [Viol.genGrp, MonoidHom.map_closure, genSet_eq, Set.image_pair, ← hjAct_eq_ofLin,
    ← hjAct_eq_ofLin]
  rfl

noncomputable def grpOf (gs : List (Array ℕ)) : Subgroup (MulAut W12) :=
  (Viol.genGrp gs).map ofLin

theorem card_grpOf (gs : List (Array ℕ)) : Nat.card (grpOf gs) = Nat.card (Viol.genGrp gs) :=
  Subgroup.card_map_of_injective ofLin_injective

theorem grpOf_append_eq_sup (l₁ l₂ : List (Array ℕ)) :
    grpOf (l₁ ++ l₂) = grpOf l₁ ⊔ grpOf l₂ := by
  have hset : Viol.GenSet (l₁ ++ l₂) = Viol.GenSet l₁ ∪ Viol.GenSet l₂ := by
    ext u
    simp only [Viol.GenSet, List.mem_append, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro ⟨r, hr | hr, hu⟩
      · exact Or.inl ⟨r, hr, hu⟩
      · exact Or.inr ⟨r, hr, hu⟩
    · rintro (⟨r, hr, hu⟩ | ⟨r, hr, hu⟩)
      · exact ⟨r, Or.inl hr, hu⟩
      · exact ⟨r, Or.inr hr, hu⟩
  unfold grpOf Viol.genGrp
  rw [hset, Subgroup.closure_union, Subgroup.map_sup]

theorem card_grpOf_eq {gs : List (Array ℕ)} (hgs : SigmaP.gensOK gs = true)
    (hc : Enum.closedCheck gs (Enum.enumGrp gs) = true) :
    Nat.card (grpOf gs) = (Enum.enumGrp gs).dedup.length := by
  rw [card_grpOf]
  exact Enum.card_genGrp (Enum.enumGrp_sound (SigmaP.gensOK_spec hgs)) (idR_mem_enumGrp gs) hc

theorem mem_grpOf_iff {gs : List (Array ℕ)} (hgs : SigmaP.gensOK gs = true)
    (hc : Enum.closedCheck gs (Enum.enumGrp gs) = true) (x : MulAut W12) :
    x ∈ grpOf gs ↔ ∃ r ∈ Enum.enumGrp gs, RowsOf x r := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨r, hr, hur⟩ := (mem_genGrp_iff (SigmaP.gensOK_spec hgs) hc u).1 hu
    exact ⟨r, hr, fun v => by rw [ofLin_apply, hur]⟩
  · rintro ⟨r, hr, hxr⟩
    obtain ⟨-, u, hu, hur⟩ := Enum.enumGrp_sound (SigmaP.gensOK_spec hgs) r hr
    refine ⟨u, hu, MulEquiv.ext fun w => ?_⟩
    show ofLin u (Multiplicative.ofAdd (Multiplicative.toAdd w)) =
      x (Multiplicative.ofAdd (Multiplicative.toAdd w))
    rw [ofLin_apply, hxr, hur]

noncomputable def linWord (w : List ℕ) : V12 ≃ₗ[ZMod 2] V12 :=
  (w.map fun l => if l = 0 then linOfGL A12 else linOfGL B12).prod

theorem ofLin_linWord (w : List ℕ) : ofLin (linWord w) = hjWord w := by
  rw [linWord, map_list_prod, List.map_map, hjWord]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  simp only [Function.comp_apply]
  split_ifs <;> exact (hjAct_eq_ofLin _).symm

theorem grpOf_words (ws : List (List ℕ)) :
    grpOf (ws.map wordR) = Subgroup.closure {x | ∃ w ∈ ws, x = hjWord w} := by
  have hset : ofLin '' Viol.GenSet (ws.map wordR) = {x | ∃ w ∈ ws, x = hjWord w} := by
    ext x
    simp only [Viol.GenSet, List.mem_map, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, ⟨r, ⟨w, hw, rfl⟩, hu⟩, rfl⟩
      refine ⟨w, hw, MulEquiv.ext fun y => ?_⟩
      show ofLin u (Multiplicative.ofAdd (Multiplicative.toAdd y)) =
        hjWord w (Multiplicative.ofAdd (Multiplicative.toAdd y))
      rw [ofLin_apply, hu, rowsOf_hjWord]
    · rintro ⟨w, hw, rfl⟩
      refine ⟨linWord w, ⟨wordR w, ⟨w, hw, rfl⟩, fun v => ?_⟩, ofLin_linWord w⟩
      have h := rowsOf_hjWord w v
      rw [← ofLin_linWord, ofLin_apply] at h
      exact Multiplicative.ofAdd.injective h
  rw [grpOf, Viol.genGrp, MonoidHom.map_closure, hset]

theorem mem_orbit_iff {p : ℕ} (hp : p < 4096)
    (hcl : ∀ x ∈ orbitOf [hjAc, hjBc] p, ∀ g ∈ [hjAc, hjBc],
      appN g x ∈ orbitOf [hjAc, hjBc] p) (v : V12) :
    (∃ l ∈ hjL0, l (Multiplicative.ofAdd v) = Multiplicative.ofAdd (vecOf p)) ↔
      ∃ x ∈ orbitOf [hjAc, hjBc] p, v = vecOf x := by
  have hreal : ∀ g ∈ [hjAc, hjBc], Realizable g := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact ⟨⟨rfl, by decide⟩, linOfGL A12, fun y => by rw [linOfRows_hjAc]; rfl⟩
    · exact ⟨⟨rfl, by decide⟩, linOfGL B12, fun y => by rw [linOfRows_hjBc]; rfl⟩
  have horb := orbit_eq hreal hp hcl
  constructor
  · rintro ⟨l, hl, hlv⟩
    rw [hjL0_eq_map_genGrp] at hl
    obtain ⟨u, hu, rfl⟩ := hl
    have h1 : u v = vecOf p := Multiplicative.ofAdd.injective hlv
    have hv : v ∈ MulAction.orbit (Viol.genGrp [hjAc, hjBc]) (vecOf p) :=
      ⟨⟨u⁻¹, inv_mem hu⟩, by
        show u.symm (vecOf p) = v
        rw [← h1, LinearEquiv.symm_apply_apply]⟩
    rw [horb] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    have hv : vecOf x ∈ MulAction.orbit (Viol.genGrp [hjAc, hjBc]) (vecOf p) := by
      rw [horb]
      exact ⟨x, hx, rfl⟩
    obtain ⟨⟨u, hu⟩, hux⟩ := hv
    have hux' : u (vecOf p) = vecOf x := hux
    refine ⟨ofLin u⁻¹, ?_, ?_⟩
    · rw [hjL0_eq_map_genGrp]
      exact ⟨u⁻¹, inv_mem hu, rfl⟩
    · show Multiplicative.ofAdd (u.symm (vecOf x)) = _
      rw [← hux', LinearEquiv.symm_apply_apply]

theorem grpOf_eq_closure {gs : List (Array ℕ)} {S : Set (MulAut W12)}
    (h1 : ∀ g ∈ gs, ∃ x ∈ S, RowsOf x g) (h2 : ∀ x ∈ S, ∃ g ∈ gs, RowsOf x g)
    (hok : ∀ g ∈ gs, Realizable g) :
    grpOf gs = Subgroup.closure S := by
  have hset : ofLin '' Viol.GenSet gs = S := by
    ext x
    constructor
    · rintro ⟨u, ⟨r, hr, hu⟩, rfl⟩
      obtain ⟨y, hy, hyr⟩ := h1 r hr
      have : ofLin u = y := MulEquiv.ext fun w => by
        show ofLin u (Multiplicative.ofAdd (Multiplicative.toAdd w)) =
          y (Multiplicative.ofAdd (Multiplicative.toAdd w))
        rw [ofLin_apply, hu, hyr]
      rw [this]
      exact hy
    · intro hx
      obtain ⟨g, hg, hxg⟩ := h2 x hx
      obtain ⟨-, u, hu⟩ := hok g hg
      refine ⟨u, ⟨g, hg, hu⟩, MulEquiv.ext fun w => ?_⟩
      show ofLin u (Multiplicative.ofAdd (Multiplicative.toAdd w)) =
        x (Multiplicative.ofAdd (Multiplicative.toAdd w))
      rw [ofLin_apply, hu, hxg]
  rw [grpOf, Viol.genGrp, MonoidHom.map_closure, hset]

theorem exists_of_mem_orbitOf {p x : ℕ} (hp : p < 4096) (hx : x ∈ orbitOf [hjAc, hjBc] p) :
    ∃ l ∈ hjL0, l (Multiplicative.ofAdd (vecOf p)) = Multiplicative.ofAdd (vecOf x) := by
  have hin : ∀ g ∈ [hjAc, hjBc], InSub (Viol.genGrp [hjAc, hjBc]) g := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact ⟨⟨rfl, by decide⟩, linOfGL A12, Subgroup.subset_closure (by rw [genSet_eq]; simp),
        fun y => by rw [linOfRows_hjAc]; rfl⟩
    · exact ⟨⟨rfl, by decide⟩, linOfGL B12, Subgroup.subset_closure (by rw [genSet_eq]; simp),
        fun y => by rw [linOfRows_hjBc]; rfl⟩
  obtain ⟨-, u, hu, hux⟩ := orbitOf_inv hin hp x hx
  refine ⟨ofLin u, ?_, ?_⟩
  · rw [hjL0_eq_map_genGrp]
    exact ⟨u, hu, rfl⟩
  · rw [ofLin_apply, ← hux]

theorem mem_fixV_zpowers_iff (x : MulAut W12) (w : W12) :
    w ∈ fixV (Subgroup.zpowers x) ↔ x w = w :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

def fixCodesR (r : Array ℕ) : List ℕ := (List.range 4096).filter fun v => appN r v == v

theorem card_fixV_zpowers {x : MulAut W12} {r : Array ℕ} (hx : RowsOf x r)
    (hr : ∀ y ∈ r, y < 4096) :
    Nat.card (fixV (Subgroup.zpowers x)) = (fixCodesR r).length := by
  classical
  have hnd : (fixCodesR r).Nodup := List.Nodup.filter _ List.nodup_range
  let f : fixV (Subgroup.zpowers x) → (fixCodesR r).toFinset := fun w =>
    ⟨codeOf (Multiplicative.toAdd (w : W12)), by
      rw [List.mem_toFinset, fixCodesR, List.mem_filter, List.mem_range]
      refine ⟨codeOf_lt _, ?_⟩
      have hw := (mem_fixV_zpowers_iff x w).1 w.2
      have h1 : linOfRows r (Multiplicative.toAdd (w : W12)) = Multiplicative.toAdd (w : W12) := by
        have := hx (Multiplicative.toAdd (w : W12))
        rw [ofAdd_toAdd, hw] at this
        exact (congrArg Multiplicative.toAdd this).symm
      rw [beq_iff_eq]
      apply vecOf_inj (appN_lt hr _) (codeOf_lt _)
      rw [vecOf_appN, vecOf_codeOf, h1]⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro a b hab
      have h := congrArg (fun z : (fixCodesR r).toFinset => vecOf (z : ℕ)) hab
      simp only [f, vecOf_codeOf] at h
      exact Subtype.ext (Multiplicative.toAdd.injective h)
    · rintro ⟨n, hn⟩
      rw [List.mem_toFinset, fixCodesR, List.mem_filter, List.mem_range, beq_iff_eq] at hn
      refine ⟨⟨Multiplicative.ofAdd (vecOf n), (mem_fixV_zpowers_iff x _).2 ?_⟩, ?_⟩
      · rw [hx, ← vecOf_appN, hn.2]
      · exact Subtype.ext (by simp [f, codeOf_vecOf hn.1])
  rw [Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup hnd]

theorem wordR_canon (w : List ℕ) : (wordR w).size = 12 ∧ ∀ y ∈ wordR w, y < 4096 := by
  have hgen : ∀ l : ℕ, ∀ y ∈ (if l = 0 then hjAc else hjBc), y < 4096 := by
    intro l y hy
    split_ifs at hy <;> revert y <;> decide
  have key : ∀ (acc : Array ℕ), acc.size = 12 → (∀ y ∈ acc, y < 4096) →
      (w.foldl (fun acc l => CFSG.GammaU.Native.mulR acc (if l = 0 then hjAc else hjBc)) acc).size
        = 12 ∧ ∀ y ∈ w.foldl (fun acc l => CFSG.GammaU.Native.mulR acc
          (if l = 0 then hjAc else hjBc)) acc, y < 4096 := by
    induction w with
    | nil => intro acc h1 h2; exact ⟨h1, h2⟩
    | cons l w ih =>
      intro acc h1 h2
      rw [List.foldl_cons]
      refine ih _ ?_ ?_
      · show (Array.map _ _).size = 12
        rw [Array.size_map]
        split_ifs <;> rfl
      · intro y hy
        obtain ⟨z, -, rfl⟩ := Array.mem_map.1 hy
        rw [native_appN]
        exact appN_lt h2 z
  exact key idR rfl (by decide)

theorem inSub_gens : ∀ g ∈ [hjAc, hjBc], InSub (Viol.genGrp [hjAc, hjBc]) g := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact ⟨⟨rfl, by decide⟩, linOfGL A12, Subgroup.subset_closure (by rw [genSet_eq]; simp),
      fun y => by rw [linOfRows_hjAc]; rfl⟩
  · exact ⟨⟨rfl, by decide⟩, linOfGL B12, Subgroup.subset_closure (by rw [genSet_eq]; simp),
      fun y => by rw [linOfRows_hjBc]; rfl⟩

theorem lt_of_mem_orbitOf {p x : ℕ} (hp : p < 4096) (hx : x ∈ orbitOf [hjAc, hjBc] p) :
    x < 4096 :=
  (orbitOf_inv inSub_gens hp x hx).1

theorem ncard_orbit_hjL0 {p : ℕ} (hp : p < 4096)
    (hcl : ∀ x ∈ orbitOf [hjAc, hjBc] p, ∀ g ∈ [hjAc, hjBc],
      appN g x ∈ orbitOf [hjAc, hjBc] p) :
    (MulAction.orbit ↥hjL0 (Multiplicative.ofAdd (vecOf p) : W12)).ncard =
      (orbitOf [hjAc, hjBc] p).eraseDups.length := by
  classical
  have horb : MulAction.orbit ↥hjL0 (Multiplicative.ofAdd (vecOf p) : W12) =
      (fun x => (Multiplicative.ofAdd (vecOf x) : W12)) '' {x | x ∈ orbitOf [hjAc, hjBc] p} := by
    ext w
    constructor
    · rintro ⟨⟨l, hl⟩, rfl⟩
      obtain ⟨x, hx, hxe⟩ := (mem_orbit_iff hp hcl
        (Multiplicative.toAdd (l (Multiplicative.ofAdd (vecOf p))))).1
        ⟨l⁻¹, inv_mem hl, by rw [ofAdd_toAdd, ← MulAut.mul_apply, inv_mul_cancel,
          MulAut.one_apply]⟩
      refine ⟨x, hx, ?_⟩
      show Multiplicative.ofAdd (vecOf x) = l (Multiplicative.ofAdd (vecOf p))
      rw [← hxe, ofAdd_toAdd]
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨l, hl, hlx⟩ := (mem_orbit_iff hp hcl (vecOf x)).2 ⟨x, hx, rfl⟩
      refine ⟨⟨l⁻¹, inv_mem hl⟩, ?_⟩
      show l⁻¹ (Multiplicative.ofAdd (vecOf p)) = Multiplicative.ofAdd (vecOf x)
      rw [← hlx, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hinj : Set.InjOn (fun x => (Multiplicative.ofAdd (vecOf x) : W12))
      {x | x ∈ orbitOf [hjAc, hjBc] p} := fun a ha b hb h =>
    vecOf_inj (lt_of_mem_orbitOf hp ha) (lt_of_mem_orbitOf hp hb)
      (Multiplicative.ofAdd.injective h)
  rw [horb, hinj.ncard_image, ← card_toFinset_eraseDups,
    show {x | x ∈ orbitOf [hjAc, hjBc] p} = ↑(orbitOf [hjAc, hjBc] p).toFinset by ext; simp,
    Set.ncard_coe_finset]

end HJBridge

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
