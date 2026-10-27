module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4Torus
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
public import CFSG.LieType.Ree.LargeReeA1Pair
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix

namespace TableBF4Two

section SL2

variable {K : Type} [Field K]

theorem neg_one_eq_one_of_two (h2 : (2 : K) = 0) : (-1 : K) = 1 := by
  rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h2]

theorem coe_S0 (h2 : (2 : K) = 0) :
    ((uSL 1 * vSL 1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two, h2]

theorem coe_S0_sq (h2 : (2 : K) = 0) :
    (((uSL 1 * vSL 1) ^ 2 : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 1, 0] := by
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, coe_S0 h2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two, h2]

theorem S0_pow_three (h2 : (2 : K) = 0) : (uSL 1 * vSL 1 : SL2 K) ^ 3 = 1 := by
  ext i j
  rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, coe_S0_sq h2, coe_S0 h2]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two, h2]

theorem W_S0_W (h2 : (2 : K) = 0) :
    (WSL : SL2 K) * (uSL 1 * vSL 1) * WSL⁻¹ = (uSL 1 * vSL 1)⁻¹ := by
  have hS := coe_S0 h2
  obtain ⟨S, hSdef⟩ : ∃ S : SL2 K, S = uSL 1 * vSL 1 := ⟨_, rfl⟩
  rw [← hSdef] at hS ⊢
  rw [mul_inv_eq_iff_eq_mul, eq_inv_mul_iff_mul_eq]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hS, coe_WSL]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, neg_one_eq_one_of_two h2, one_add_one_eq_two, h2]

theorem S0_pow_mul_uSL_ne (h2 : (2 : K) = 0) {k : ℕ} (hk : k < 3) (hk0 : k ≠ 0) :
    (uSL 1 * vSL 1 : SL2 K) ^ k * uSL 1 ≠ uSL 1 * (uSL 1 * vSL 1) ^ k := by
  intro h
  have h' := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h'
  obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
  · rw [pow_one, coe_S0 h2, coe_uSL] at h'
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h'
  · rw [coe_S0_sq h2, coe_uSL] at h'
    simp [Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two, h2] at h'

theorem S0_ne_one (h2 : (2 : K) = 0) : (uSL 1 * vSL 1 : SL2 K) ≠ 1 := by
  intro h
  apply S0_pow_mul_uSL_ne h2 (k := 1) (by norm_num) one_ne_zero
  rw [pow_one, h, one_mul, mul_one]

theorem uSL_one_sq (h2 : (2 : K) = 0) : (uSL 1 : SL2 K) ^ 2 = 1 := by
  ext i j
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, coe_uSL]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two, h2]

theorem uSL_one_ne_one : (uSL 1 : SL2 K) ≠ 1 := by
  intro h
  have h' := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simp [coe_uSL] at h'

end SL2

section Roots

@[expose] def orthRoot : Fin 4 → (Fin Tag.F4.rank → ℤ) :=
  ![![0, 1, 0, 0], ![0, 1, 2, 0], ![0, 1, 2, 2], ![2, 3, 4, 2]]

theorem form_neg_neg (v w : Fin Tag.F4.rank → ℤ) :
    (-v) ⬝ᵥ (Tag.F4.symmetrizedCartan *ᵥ (-w)) = v ⬝ᵥ (Tag.F4.symmetrizedCartan *ᵥ w) := by
  rw [Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]

theorem form_neg_left (v w : Fin Tag.F4.rank → ℤ) :
    (-v) ⬝ᵥ (Tag.F4.symmetrizedCartan *ᵥ w) = -(v ⬝ᵥ (Tag.F4.symmetrizedCartan *ᵥ w)) :=
  neg_dotProduct _ _

theorem form_neg_right (v w : Fin Tag.F4.rank → ℤ) :
    v ⬝ᵥ (Tag.F4.symmetrizedCartan *ᵥ (-w)) = -(v ⬝ᵥ (Tag.F4.symmetrizedCartan *ᵥ w)) := by
  rw [Matrix.mulVec_neg, dotProduct_neg]


theorem orthRoot_mem : ∀ i, orthRoot i ∈ rootFinset .F4 := by decide +kernel

theorem isRoot_orthRoot (i : Fin 4) : IsRoot .F4 (orthRoot i) :=
  mem_rootFinset.1 (orthRoot_mem i)

theorem orthRoot_norm :
    ∀ i, orthRoot i ⬝ᵥ (Tag.F4.symmetrizedCartan *ᵥ orthRoot i) = 4 := by decide +kernel

theorem orthRoot_orth :
    ∀ i j, i ≠ j → orthRoot i ⬝ᵥ (Tag.F4.symmetrizedCartan *ᵥ orthRoot j) = 0 := by
  decide +kernel

theorem rootFinset_norm_le :
    ∀ v ∈ rootFinset .F4, v ⬝ᵥ (Tag.F4.symmetrizedCartan *ᵥ v) ≤ 4 := by decide +kernel

theorem norm_le_four_of_isRoot {v : Fin Tag.F4.rank → ℤ} (hv : IsRoot .F4 v) :
    v ⬝ᵥ (Tag.F4.symmetrizedCartan *ᵥ v) ≤ 4 :=
  rootFinset_norm_le v (mem_rootFinset.2 hv)

theorem not_isRoot_nsmul_add_nsmul {v w : Fin Tag.F4.rank → ℤ}
    (hv : v ⬝ᵥ (Tag.F4.symmetrizedCartan *ᵥ v) = 4)
    (hw : w ⬝ᵥ (Tag.F4.symmetrizedCartan *ᵥ w) = 4)
    (hvw : v ⬝ᵥ (Tag.F4.symmetrizedCartan *ᵥ w) = 0)
    (hwv : w ⬝ᵥ (Tag.F4.symmetrizedCartan *ᵥ v) = 0) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ¬ IsRoot .F4 (a • v + b • w) := by
  intro h
  have h1 := norm_le_four_of_isRoot h
  rw [← natCast_zsmul v a, ← natCast_zsmul w b] at h1
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, hv, hw, hvw, hwv, smul_eq_mul] at h1
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith

end Roots


section RankOne


theorem commute_pinnedX_of_orth (R : Type) [CommRing R] {v w : Fin Tag.F4.rank → ℤ}
    (hv : IsRoot .F4 v) (hw : IsRoot .F4 w)
    (hvv : v ⬝ᵥ (Tag.F4.symmetrizedCartan *ᵥ v) = 4)
    (hww : w ⬝ᵥ (Tag.F4.symmetrizedCartan *ᵥ w) = 4)
    (hvw : v ⬝ᵥ (Tag.F4.symmetrizedCartan *ᵥ w) = 0)
    (hwv : w ⬝ᵥ (Tag.F4.symmetrizedCartan *ᵥ v) = 0) (c d : R) :
    Commute (pinnedX .F4 R v c) (pinnedX .F4 R w d) := by
  have hne : v ≠ w := by
    rintro rfl
    rw [hvv] at hvw
    norm_num at hvw
  have hne' : v ≠ -w := by
    rintro rfl
    rw [neg_dotProduct, hww] at hvw
    norm_num at hvw
  exact CFSG.LieType.Ree.commute_pinnedX_of_forall_not_isRoot R hv hw hne hne'
    (fun a b ha hb => not_isRoot_nsmul_add_nsmul hvv hww hvw hwv ha hb) c d

variable {K : Type} [Field K]

abbrev orthGen (K : Type) [Field K] (i : Fin 4) : Set (ModGL .F4 K) :=
  Set.range (pinnedX .F4 K (orthRoot i)) ∪ Set.range (pinnedX .F4 K (-orthRoot i))

theorem commute_orthGen {i j : Fin 4} (hij : i ≠ j) {x y : ModGL .F4 K} (hx : x ∈ orthGen K i)
    (hy : y ∈ orthGen K j) : Commute x y := by
  have hi := isRoot_orthRoot i
  have hj := isRoot_orthRoot j
  have hni := orthRoot_norm i
  have hnj := orthRoot_norm j
  have hij' := orthRoot_orth i j hij
  have hji' := orthRoot_orth j i hij.symm
  rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩ <;> rcases hy with ⟨d, rfl⟩ | ⟨d, rfl⟩
  · exact commute_pinnedX_of_orth K hi hj hni hnj hij' hji' c d
  · exact commute_pinnedX_of_orth K hi (IsRoot.neg hj) hni (by rw [form_neg_neg, hnj])
      (by rw [form_neg_right, hij', neg_zero]) (by rw [form_neg_left, hji', neg_zero]) c d
  · exact commute_pinnedX_of_orth K (IsRoot.neg hi) hj (by rw [form_neg_neg, hni]) hnj
      (by rw [form_neg_left, hij', neg_zero]) (by rw [form_neg_right, hji', neg_zero]) c d
  · exact commute_pinnedX_of_orth K (IsRoot.neg hi) (IsRoot.neg hj) (by rw [form_neg_neg, hni])
      (by rw [form_neg_neg, hnj]) (by rw [form_neg_neg, hij']) (by rw [form_neg_neg, hji']) c d

theorem range_rootSL2_orthRoot (i : Fin 4) :
    (rootSL2 .F4 K (orthRoot i)).range = Subgroup.closure (orthGen K i) := by
  rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot (isRoot_orthRoot i), rootSubgroup,
    rootSubgroup, ← Subgroup.closure_union]

theorem commute_rootSL2 {i j : Fin 4} (hij : i ≠ j) (A B : SL2 K) :
    Commute (rootSL2 .F4 K (orthRoot i) A) (rootSL2 .F4 K (orthRoot j) B) := by
  have h1 : Subgroup.closure (orthGen K i) ≤ Subgroup.centralizer (orthGen K j) := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    exact (commute_orthGen hij hx hy).symm
  have h2 : Subgroup.closure (orthGen K j) ≤
      Subgroup.centralizer (Subgroup.closure (orthGen K i) : Set (ModGL .F4 K)) := by
    rw [Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (h1 hx) y hy).symm
  have hA : rootSL2 .F4 K (orthRoot i) A ∈ Subgroup.closure (orthGen K i) := by
    rw [← range_rootSL2_orthRoot]
    exact ⟨A, rfl⟩
  have hB : rootSL2 .F4 K (orthRoot j) B ∈ Subgroup.closure (orthGen K j) := by
    rw [← range_rootSL2_orthRoot]
    exact ⟨B, rfl⟩
  exact Subgroup.mem_centralizer_iff.mp (h2 hB) _ hA

@[expose] noncomputable def rho (K : Type) [Field K] (i : Fin 4) : SL2 K →* adjointGroup .F4 K :=
  (rootSL2 .F4 K (orthRoot i)).codRestrict _ fun A =>
    (exceptional_Lang_root_rank_one_data .F4 K (orthRoot i)).2.2.2.2.1 A

theorem coe_rho (i : Fin 4) (A : SL2 K) :
    ((rho K i A : adjointGroup .F4 K) : ModGL .F4 K) = rootSL2 .F4 K (orthRoot i) A :=
  rfl

theorem rho_injective (i : Fin 4) : Function.Injective (rho K i) := fun _ _ h =>
  CFSG.RankThree.Chevalley.rootSL2_injective_of_field (orthRoot i) (congrArg Subtype.val h)

theorem commute_rho {i j : Fin 4} (hij : i ≠ j) (A B : SL2 K) :
    Commute (rho K i A) (rho K j B) :=
  Subtype.ext (commute_rootSL2 hij A B)

end RankOne

section Reflections

theorem castSucc_ne_castSucc {i j : Fin 3} (h : i ≠ j) : i.castSucc ≠ j.castSucc := fun e =>
  h (Fin.castSucc_injective _ e)

theorem castSucc_ne_three (i : Fin 3) : i.castSucc ≠ (3 : Fin 4) := by
  have h := Fin.castSucc_lt_last i
  intro e
  rw [e] at h
  exact absurd h (lt_irrefl _)

@[expose] def reflHom (i : Fin 3) :
    (Fin 3 → Multiplicative (ZMod 3)) →* (Fin 3 → Multiplicative (ZMod 3)) where
  toFun f j := if j = i then (f j)⁻¹ else f j
  map_one' := by
    funext j
    simp only [Pi.one_apply]
    split_ifs
    · exact inv_one
    · rfl
  map_mul' f g := by
    funext j
    simp only [Pi.mul_apply]
    split_ifs
    · exact mul_inv (f j) (g j)
    · rfl

theorem reflHom_apply (i : Fin 3) (f : Fin 3 → Multiplicative (ZMod 3)) (j : Fin 3) :
    reflHom i f j = if j = i then (f j)⁻¹ else f j :=
  rfl

theorem reflHom_mulSingle (i j : Fin 3) (a : Multiplicative (ZMod 3)) :
    reflHom i (Pi.mulSingle j a) = Pi.mulSingle j (if j = i then a⁻¹ else a) := by
  funext k
  rw [reflHom_apply]
  by_cases hkj : k = j
  · subst hkj
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne hkj, Pi.mulSingle_eq_of_ne hkj]
    split_ifs
    · exact inv_one
    · rfl

@[expose] noncomputable def reflCoeff (i : Fin 3) : (Fin 3 → ZMod 3) →ₗ[ZMod 3] ZMod 3 :=
  (2 : ZMod 3) • LinearMap.proj i

theorem reflCoeff_apply (i : Fin 3) (v : Fin 3 → ZMod 3) : reflCoeff i v = 2 * v i := by
  simp [reflCoeff]

theorem reflCoeff_single (i : Fin 3) : reflCoeff i (Pi.single i 1) = 2 := by
  rw [reflCoeff_apply, Pi.single_eq_same, mul_one]

theorem sub_two_mul_eq_neg (x : ZMod 3) : x - 2 * x = -x := by
  revert x
  decide

theorem reflVec_apply_self (i : Fin 3) (v : Fin 3 → ZMod 3) :
    (v - reflCoeff i v • Pi.single i 1 : Fin 3 → ZMod 3) i = -v i := by
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, reflCoeff_apply, mul_one]
  exact sub_two_mul_eq_neg (v i)

theorem reflVec_apply_of_ne {i j : Fin 3} (hji : j ≠ i) (v : Fin 3 → ZMod 3) :
    (v - reflCoeff i v • Pi.single i 1 : Fin 3 → ZMod 3) j = v j := by
  simp [Pi.single_eq_of_ne hji]

theorem reflHom_ofAdd (i : Fin 3) (v : Fin 3 → ZMod 3) :
    reflHom i (fun j => Multiplicative.ofAdd (v j)) =
      fun j => Multiplicative.ofAdd ((v - reflCoeff i v • Pi.single i 1 : Fin 3 → ZMod 3) j) := by
  funext j
  rw [reflHom_apply]
  split_ifs with hji
  · subst hji
    rw [reflVec_apply_self]
    exact (ofAdd_neg (v j)).symm
  · rw [reflVec_apply_of_ne hji]

end Reflections

section Torus

variable
  {K : Type} [Field K] [CharP K 2]

variable (K) in
@[expose] noncomputable def torusGen (i : Fin 3) : adjointGroup .F4 K :=
  rho K i.castSucc (uSL 1 * vSL 1)

variable (K) in
@[expose] noncomputable def reflGen (i : Fin 3) : adjointGroup .F4 K :=
  rho K i.castSucc WSL

theorem torusGen_pow_three (i : Fin 3) : torusGen K i ^ 3 = 1 := by
  rw [torusGen, ← map_pow, S0_pow_three CharTwo.two_eq_zero, map_one]

theorem torusGen_ne_one (i : Fin 3) : torusGen K i ≠ 1 := fun h =>
  S0_ne_one (K := K) CharTwo.two_eq_zero (rho_injective _ (h.trans (map_one _).symm))

variable (K) in
@[expose] noncomputable def torusCoord (i : Fin 3) :
    Multiplicative (ZMod 3) →* adjointGroup .F4 K :=
  TableBSymp.zmodPowHom (torusGen_pow_three (K := K) i)

theorem torusCoord_apply (i : Fin 3) (a : Multiplicative (ZMod 3)) :
    torusCoord K i a = rho K i.castSucc ((uSL 1 * vSL 1) ^ (Multiplicative.toAdd a).val) := by
  rw [torusCoord, TableBSymp.zmodPowHom_apply, torusGen, map_pow]

theorem torusCoord_injective (i : Fin 3) : Function.Injective (torusCoord K i) := by
  have := Fact.mk Nat.prime_three
  rw [injective_iff_map_eq_one]
  intro a ha
  rw [torusCoord, TableBSymp.zmodPowHom_apply] at ha
  have hd := orderOf_dvd_of_pow_eq_one ha
  rw [orderOf_eq_prime (torusGen_pow_three i) (torusGen_ne_one i)] at hd
  have hlt := ZMod.val_lt (Multiplicative.toAdd a)
  have h0 : (Multiplicative.toAdd a).val = 0 := by omega
  rw [ZMod.val_eq_zero] at h0
  rw [← ofAdd_toAdd a, h0, ofAdd_zero]

variable (K) in
@[expose] noncomputable def rootInv : adjointGroup .F4 K :=
  rho K 3 (uSL 1)

theorem rootInv_sq : rootInv K ^ 2 = 1 := by
  rw [rootInv, ← map_pow, uSL_one_sq CharTwo.two_eq_zero, map_one]

omit [CharP K 2] in
theorem rootInv_ne_one : rootInv K ≠ 1 := fun h =>
  uSL_one_ne_one (K := K) (rho_injective _ (h.trans (map_one _).symm))


theorem torusCoord_commute :
    Pairwise fun i j : Fin 3 => ∀ a b, Commute (torusCoord K i a) (torusCoord K j b) := by
  intro i j hij a b
  rw [torusCoord_apply, torusCoord_apply]
  exact commute_rho (castSucc_ne_castSucc hij) _ _

variable (K) in
@[expose] noncomputable def torus3 : (Fin 3 → Multiplicative (ZMod 3)) →* adjointGroup .F4 K :=
  MonoidHom.noncommPiCoprod (torusCoord K) torusCoord_commute

theorem torusCoord_iSupIndep : iSupIndep fun i => (torusCoord K i).range := by
  rw [iSupIndep_def]
  intro i
  rw [Subgroup.disjoint_def]
  intro x hx hx'
  obtain ⟨a, rfl⟩ := hx
  have hle : (⨆ (j) (_ : j ≠ i), (torusCoord K j).range) ≤
      Subgroup.centralizer {rho K i.castSucc (uSL 1)} := by
    refine iSup₂_le fun j hj => ?_
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, torusCoord_apply]
    exact (commute_rho (castSucc_ne_castSucc hj) _ _).eq
  have hc := Subgroup.mem_centralizer_singleton_iff.mp (hle hx')
  rw [torusCoord_apply, ← map_mul, ← map_mul] at hc
  have hc' := rho_injective _ hc
  by_contra hne
  have hval : (Multiplicative.toAdd a).val ≠ 0 := by
    intro h0
    apply hne
    rw [torusCoord_apply, h0, pow_zero, map_one]
  exact S0_pow_mul_uSL_ne CharTwo.two_eq_zero (ZMod.val_lt _) hval hc'

theorem torus3_injective : Function.Injective (torus3 K) :=
  MonoidHom.injective_noncommPiCoprod_of_iSupIndep (torusCoord K) torusCoord_iSupIndep
    torusCoord_injective

theorem reflGen_conj_torusCoord (i j : Fin 3) (a : Multiplicative (ZMod 3)) :
    reflGen K i * torusCoord K j a * (reflGen K i)⁻¹ =
      torusCoord K j (if j = i then a⁻¹ else a) := by
  split_ifs with hji
  · subst hji
    rw [show torusCoord K j a⁻¹ = (torusCoord K j a)⁻¹ from map_inv _ a, torusCoord_apply,
      reflGen, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    rw [← conj_pow, W_S0_W CharTwo.two_eq_zero, inv_pow]
  · rw [torusCoord_apply, reflGen,
      (commute_rho (castSucc_ne_castSucc (Ne.symm hji)) WSL _).eq, mul_inv_cancel_right]

theorem reflGen_conj_torus3 (i : Fin 3) (f : Fin 3 → Multiplicative (ZMod 3)) :
    reflGen K i * torus3 K f * (reflGen K i)⁻¹ = torus3 K (reflHom i f) := by
  have h : (MulAut.conj (reflGen K i)).toMonoidHom.comp (torus3 K) =
      (torus3 K).comp (reflHom i) := MonoidHom.pi_ext fun j a => by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, torus3,
      MonoidHom.noncommPiCoprod_mulSingle, reflHom_mulSingle]
    exact reflGen_conj_torusCoord i j a
  have h1 := congrArg (fun φ => φ f) h
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h1

variable (K) in
@[expose] noncomputable def torusE : Multiplicative (Fin 3 → ZMod 3) →* adjointGroup .F4 K :=
  (torus3 K).comp (MulEquiv.piMultiplicative fun _ : Fin 3 => ZMod 3).toMonoidHom

theorem torusE_apply (v : Fin 3 → ZMod 3) :
    torusE K (Multiplicative.ofAdd v) = torus3 K fun j => Multiplicative.ofAdd (v j) :=
  rfl

theorem torusE_injective : Function.Injective (torusE K) := fun _ _ h =>
  (MulEquiv.piMultiplicative fun _ : Fin 3 => ZMod 3).injective (torus3_injective (K := K) h)

theorem reflGen_conj_torusE (i : Fin 3) (v : Fin 3 → ZMod 3) :
    reflGen K i * torusE K (Multiplicative.ofAdd v) * (reflGen K i)⁻¹ =
      torusE K (Multiplicative.ofAdd (v - reflCoeff i v • Pi.single i 1)) := by
  rw [torusE_apply, torusE_apply, reflGen_conj_torus3, reflHom_ofAdd]

theorem torusE_commute_rootInv (v : Multiplicative (Fin 3 → ZMod 3)) :
    Commute (torusE K v) (rootInv K) := by
  have hmem : torusE K v ∈ (torus3 K).range := ⟨_, rfl⟩
  have hle : (torus3 K).range ≤ Subgroup.centralizer {rootInv K} := by
    rw [torus3, MonoidHom.noncommPiCoprod_range]
    refine iSup_le fun i => ?_
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, torusCoord_apply, rootInv]
    exact (commute_rho (castSucc_ne_three i) _ _).eq
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hmem))

theorem ggTorusLift_adjointF4Two : GGTorusLift 3 3 (adjointGroup .F4 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : Subgroup.zpowers (rootInv K) ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact rootInv_ne_one
  have hU2 : IsPGroup 2 (Subgroup.zpowers (rootInv K)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime rootInv_sq rootInv_ne_one, pow_one]
  refine TableBF4.ggTorusLift_of_reflections (d := 3) Nat.prime_three (by norm_num) (torusE K)
    torusE_injective reflCoeff reflCoeff_single (reflGen K) reflGen_conj_torusE hU hU2 ?_
  intro v x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [((torusE_commute_rootInv v).zpow_right k).eq, mul_inv_cancel_right]
  exact Subgroup.zpow_mem_zpowers _ _

theorem ggTorusLift_F4Two [Finite K] : GGTorusLift 3 3 (TableBF4.RecipeGroup K) :=
  TableBF4.ggTorusLift_of_mulEquiv (TableBF4.recipeEquiv K) ggTorusLift_adjointF4Two

end Torus

end TableBF4Two

end CFSG.StandardType
