module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LieType.Steinberg.Adjoint.Pairs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open CFSG.LieType.Steinberg.Adjoint (iform iform_nsmul_add_nsmul iform_self_of_isRoot iform_comm
  iform_smul_left iform_smul_right)

namespace TableBExcTwo

section Roots

variable {τ : Tag}

theorem iform_self_eq_two_of_isRoot (hsym : ∀ i, τ.symmetrizer i i = 1)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) : iform γ γ = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hγ
  rw [hj, hsym j, mul_one]

theorem iform_neg_left' (x y : Fin τ.rank → ℤ) : iform (-x) y = -iform x y := by
  rw [← neg_one_zsmul x, iform_smul_left, neg_one_mul]

theorem iform_neg_right' (x y : Fin τ.rank → ℤ) : iform x (-y) = -iform x y := by
  rw [← neg_one_zsmul y, iform_smul_right, neg_one_mul]

theorem not_isRoot_nsmul_add_nsmul_of_orth (hsym : ∀ i, τ.symmetrizer i i = 1)
    {v w : Fin τ.rank → ℤ} (hv : IsRoot τ v) (hw : IsRoot τ w) (hvw : iform v w = 0) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) : ¬ IsRoot τ (a • v + b • w) := by
  intro h
  have h1 := iform_self_eq_two_of_isRoot hsym h
  rw [iform_nsmul_add_nsmul, hvw, iform_self_eq_two_of_isRoot hsym hv,
    iform_self_eq_two_of_isRoot hsym hw] at h1
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith

theorem ne_and_ne_neg_of_orth (hsym : ∀ i, τ.symmetrizer i i = 1) {v w : Fin τ.rank → ℤ}
    (hw : IsRoot τ w) (hvw : iform v w = 0) : v ≠ w ∧ v ≠ -w := by
  have h2 := iform_self_eq_two_of_isRoot hsym hw
  refine ⟨?_, ?_⟩
  · rintro rfl
    rw [h2] at hvw
    exact absurd hvw (by norm_num)
  · rintro rfl
    rw [iform_neg_left', h2] at hvw
    exact absurd hvw (by norm_num)

end Roots

structure OrthFrame (τ : Tag)
    (d : ℕ) where
  root : Fin (d + 1) → (Fin τ.rank → ℤ)
  symm_one : ∀ i, τ.symmetrizer i i = 1
  isRoot : ∀ i, IsRoot τ (root i)
  orth : ∀ i j, i ≠ j → iform (root i) (root j) = 0

section RankOne

variable
  {τ : Tag} {d : ℕ}

theorem commute_pinnedX_of_iform_eq_zero (R : Type) [CommRing R]
    (hsym : ∀ i, τ.symmetrizer i i = 1) {v w : Fin τ.rank → ℤ} (hv : IsRoot τ v)
    (hw : IsRoot τ w) (hvw : iform v w = 0) (c d : R) :
    Commute (pinnedX τ R v c) (pinnedX τ R w d) := by
  obtain ⟨hne, hne'⟩ := ne_and_ne_neg_of_orth hsym hw hvw
  exact CFSG.LieType.Ree.commute_pinnedX_of_forall_not_isRoot R hv hw hne hne'
    (fun a b ha hb => not_isRoot_nsmul_add_nsmul_of_orth hsym hv hw hvw ha hb) c d

variable {K : Type} [Field K]

abbrev orthGen (K : Type) [Field K] (F : OrthFrame τ d) (i : Fin (d + 1)) : Set (ModGL τ K) :=
  Set.range (pinnedX τ K (F.root i)) ∪ Set.range (pinnedX τ K (-F.root i))

theorem commute_orthGen (F : OrthFrame τ d) {i j : Fin (d + 1)} (hij : i ≠ j)
    {x y : ModGL τ K} (hx : x ∈ orthGen K F i) (hy : y ∈ orthGen K F j) : Commute x y := by
  have hi := F.isRoot i
  have hj := F.isRoot j
  have h0 := F.orth i j hij
  rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩ <;> rcases hy with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · exact commute_pinnedX_of_iform_eq_zero K F.symm_one hi hj h0 c e
  · exact commute_pinnedX_of_iform_eq_zero K F.symm_one hi (IsRoot.neg hj)
      (by rw [iform_neg_right', h0, neg_zero]) c e
  · exact commute_pinnedX_of_iform_eq_zero K F.symm_one (IsRoot.neg hi) hj
      (by rw [iform_neg_left', h0, neg_zero]) c e
  · exact commute_pinnedX_of_iform_eq_zero K F.symm_one (IsRoot.neg hi) (IsRoot.neg hj)
      (by rw [iform_neg_left', iform_neg_right', h0, neg_zero, neg_zero]) c e

theorem range_rootSL2_frame (F : OrthFrame τ d) (i : Fin (d + 1)) :
    (rootSL2 τ K (F.root i)).range = Subgroup.closure (orthGen K F i) := by
  rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot (F.isRoot i), rootSubgroup,
    rootSubgroup, ← Subgroup.closure_union]

theorem commute_rootSL2 (F : OrthFrame τ d) {i j : Fin (d + 1)} (hij : i ≠ j) (A B : SL2 K) :
    Commute (rootSL2 τ K (F.root i) A) (rootSL2 τ K (F.root j) B) := by
  have h1 : Subgroup.closure (orthGen K F i) ≤ Subgroup.centralizer (orthGen K F j) := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    exact (commute_orthGen F hij hx hy).symm
  have h2 : Subgroup.closure (orthGen K F j) ≤
      Subgroup.centralizer (Subgroup.closure (orthGen K F i) : Set (ModGL τ K)) := by
    rw [Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (h1 hx) y hy).symm
  have hA : rootSL2 τ K (F.root i) A ∈ Subgroup.closure (orthGen K F i) := by
    rw [← range_rootSL2_frame]
    exact ⟨A, rfl⟩
  have hB : rootSL2 τ K (F.root j) B ∈ Subgroup.closure (orthGen K F j) := by
    rw [← range_rootSL2_frame]
    exact ⟨B, rfl⟩
  exact Subgroup.mem_centralizer_iff.mp (h2 hB) _ hA

@[expose] noncomputable def rho (K : Type) [Field K] (F : OrthFrame τ d) (i : Fin (d + 1)) :
    SL2 K →* adjointGroup τ K :=
  (rootSL2 τ K (F.root i)).codRestrict _ fun A =>
    (exceptional_Lang_root_rank_one_data τ K (F.root i)).2.2.2.2.1 A

theorem coe_rho (F : OrthFrame τ d) (i : Fin (d + 1)) (A : SL2 K) :
    ((rho K F i A : adjointGroup τ K) : ModGL τ K) = rootSL2 τ K (F.root i) A :=
  rfl

theorem rho_injective (F : OrthFrame τ d) (i : Fin (d + 1)) : Function.Injective (rho K F i) :=
  fun _ _ h =>
    CFSG.RankThree.Chevalley.rootSL2_injective_of_field (F.root i) (congrArg Subtype.val h)

theorem commute_rho (F : OrthFrame τ d) {i j : Fin (d + 1)} (hij : i ≠ j) (A B : SL2 K) :
    Commute (rho K F i A) (rho K F j B) :=
  Subtype.ext (commute_rootSL2 F hij A B)

end RankOne

section Reflections

variable {d : ℕ}

@[expose] def reflHom (i : Fin d) :
    (Fin d → Multiplicative (ZMod 3)) →* (Fin d → Multiplicative (ZMod 3)) where
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

theorem reflHom_apply (i : Fin d) (f : Fin d → Multiplicative (ZMod 3)) (j : Fin d) :
    reflHom i f j = if j = i then (f j)⁻¹ else f j :=
  rfl

theorem reflHom_mulSingle (i j : Fin d) (a : Multiplicative (ZMod 3)) :
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

@[expose] noncomputable def reflCoeff (i : Fin d) : (Fin d → ZMod 3) →ₗ[ZMod 3] ZMod 3 :=
  (2 : ZMod 3) • LinearMap.proj i

theorem reflCoeff_apply (i : Fin d) (v : Fin d → ZMod 3) : reflCoeff i v = 2 * v i := by
  simp [reflCoeff]

theorem reflCoeff_single (i : Fin d) : reflCoeff i (Pi.single i 1) = 2 := by
  rw [reflCoeff_apply, Pi.single_eq_same, mul_one]

theorem reflVec_apply_self (i : Fin d) (v : Fin d → ZMod 3) :
    (v - reflCoeff i v • Pi.single i 1 : Fin d → ZMod 3) i = -v i := by
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, reflCoeff_apply, mul_one]
  exact TableBF4Two.sub_two_mul_eq_neg (v i)

theorem reflVec_apply_of_ne {i j : Fin d} (hji : j ≠ i) (v : Fin d → ZMod 3) :
    (v - reflCoeff i v • Pi.single i 1 : Fin d → ZMod 3) j = v j := by
  simp [Pi.single_eq_of_ne hji]

theorem reflHom_ofAdd (i : Fin d) (v : Fin d → ZMod 3) :
    reflHom i (fun j => Multiplicative.ofAdd (v j)) =
      fun j => Multiplicative.ofAdd ((v - reflCoeff i v • Pi.single i 1 : Fin d → ZMod 3) j) := by
  funext j
  rw [reflHom_apply]
  split_ifs with hji
  · subst hji
    rw [reflVec_apply_self]
    exact (ofAdd_neg (v j)).symm
  · rw [reflVec_apply_of_ne hji]

theorem castSucc_ne_castSucc' {i j : Fin d} (h : i ≠ j) : i.castSucc ≠ j.castSucc := fun e =>
  h (Fin.castSucc_injective _ e)

end Reflections

section Torus

variable
  {τ : Tag} {d : ℕ} {K : Type} [Field K] [CharP K 2]

variable (K) in
@[expose] noncomputable def torusGen (F : OrthFrame τ d) (i : Fin d) : adjointGroup τ K :=
  rho K F i.castSucc (uSL 1 * vSL 1)

variable (K) in
@[expose] noncomputable def reflGen (F : OrthFrame τ d) (i : Fin d) : adjointGroup τ K :=
  rho K F i.castSucc WSL

theorem torusGen_pow_three (F : OrthFrame τ d) (i : Fin d) : torusGen K F i ^ 3 = 1 := by
  rw [torusGen, ← map_pow, TableBF4Two.S0_pow_three CharTwo.two_eq_zero, map_one]

theorem torusGen_ne_one (F : OrthFrame τ d) (i : Fin d) : torusGen K F i ≠ 1 := fun h =>
  TableBF4Two.S0_ne_one (K := K) CharTwo.two_eq_zero
    (rho_injective F _ (h.trans (map_one _).symm))

variable (K) in
@[expose] noncomputable def torusCoord (F : OrthFrame τ d) (i : Fin d) :
    Multiplicative (ZMod 3) →* adjointGroup τ K :=
  TableBSymp.zmodPowHom (torusGen_pow_three (K := K) F i)

theorem torusCoord_apply (F : OrthFrame τ d) (i : Fin d) (a : Multiplicative (ZMod 3)) :
    torusCoord K F i a =
      rho K F i.castSucc ((uSL 1 * vSL 1) ^ (Multiplicative.toAdd a).val) := by
  rw [torusCoord, TableBSymp.zmodPowHom_apply, torusGen, map_pow]

theorem torusCoord_injective (F : OrthFrame τ d) (i : Fin d) :
    Function.Injective (torusCoord K F i) := by
  have := Fact.mk Nat.prime_three
  rw [injective_iff_map_eq_one]
  intro a ha
  rw [torusCoord, TableBSymp.zmodPowHom_apply] at ha
  have hd := orderOf_dvd_of_pow_eq_one ha
  rw [orderOf_eq_prime (torusGen_pow_three F i) (torusGen_ne_one F i)] at hd
  have hlt := ZMod.val_lt (Multiplicative.toAdd a)
  have h0 : (Multiplicative.toAdd a).val = 0 := by omega
  rw [ZMod.val_eq_zero] at h0
  rw [← ofAdd_toAdd a, h0, ofAdd_zero]

variable (K) in
@[expose] noncomputable def rootInv (F : OrthFrame τ d) : adjointGroup τ K :=
  rho K F (Fin.last d) (uSL 1)

theorem rootInv_sq (F : OrthFrame τ d) : rootInv K F ^ 2 = 1 := by
  rw [rootInv, ← map_pow, TableBF4Two.uSL_one_sq CharTwo.two_eq_zero, map_one]

omit [CharP K 2] in
theorem rootInv_ne_one (F : OrthFrame τ d) : rootInv K F ≠ 1 := fun h =>
  TableBF4Two.uSL_one_ne_one (K := K) (rho_injective F _ (h.trans (map_one _).symm))


theorem torusCoord_commute (F : OrthFrame τ d) :
    Pairwise fun i j : Fin d => ∀ a b, Commute (torusCoord K F i a) (torusCoord K F j b) := by
  intro i j hij a b
  rw [torusCoord_apply, torusCoord_apply]
  exact commute_rho F (castSucc_ne_castSucc' hij) _ _

variable (K) in
@[expose] noncomputable def torusD (F : OrthFrame τ d) :
    (Fin d → Multiplicative (ZMod 3)) →* adjointGroup τ K :=
  MonoidHom.noncommPiCoprod (torusCoord K F) (torusCoord_commute F)

theorem torusCoord_iSupIndep (F : OrthFrame τ d) : iSupIndep fun i => (torusCoord K F i).range := by
  rw [iSupIndep_def]
  intro i
  rw [Subgroup.disjoint_def]
  intro x hx hx'
  obtain ⟨a, rfl⟩ := hx
  have hle : (⨆ (j) (_ : j ≠ i), (torusCoord K F j).range) ≤
      Subgroup.centralizer {rho K F i.castSucc (uSL 1)} := by
    refine iSup₂_le fun j hj => ?_
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, torusCoord_apply]
    exact (commute_rho F (castSucc_ne_castSucc' hj) _ _).eq
  have hc := Subgroup.mem_centralizer_singleton_iff.mp (hle hx')
  rw [torusCoord_apply, ← map_mul, ← map_mul] at hc
  have hc' := rho_injective F _ hc
  by_contra hne
  have hval : (Multiplicative.toAdd a).val ≠ 0 := by
    intro h0
    apply hne
    rw [torusCoord_apply, h0, pow_zero, map_one]
  exact TableBF4Two.S0_pow_mul_uSL_ne CharTwo.two_eq_zero (ZMod.val_lt _) hval hc'

theorem torusD_injective (F : OrthFrame τ d) : Function.Injective (torusD K F) :=
  MonoidHom.injective_noncommPiCoprod_of_iSupIndep (torusCoord K F) (torusCoord_iSupIndep F)
    (torusCoord_injective F)

theorem reflGen_conj_torusCoord (F : OrthFrame τ d) (i j : Fin d) (a : Multiplicative (ZMod 3)) :
    reflGen K F i * torusCoord K F j a * (reflGen K F i)⁻¹ =
      torusCoord K F j (if j = i then a⁻¹ else a) := by
  split_ifs with hji
  · subst hji
    rw [show torusCoord K F j a⁻¹ = (torusCoord K F j a)⁻¹ from map_inv _ a, torusCoord_apply,
      reflGen, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    rw [← conj_pow, TableBF4Two.W_S0_W CharTwo.two_eq_zero, inv_pow]
  · rw [torusCoord_apply, reflGen,
      (commute_rho F (castSucc_ne_castSucc' (Ne.symm hji)) WSL _).eq, mul_inv_cancel_right]

theorem reflGen_conj_torusD (F : OrthFrame τ d) (i : Fin d) (f : Fin d → Multiplicative (ZMod 3)) :
    reflGen K F i * torusD K F f * (reflGen K F i)⁻¹ = torusD K F (reflHom i f) := by
  have h : (MulAut.conj (reflGen K F i)).toMonoidHom.comp (torusD K F) =
      (torusD K F).comp (reflHom i) := MonoidHom.pi_ext fun j a => by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, torusD,
      MonoidHom.noncommPiCoprod_mulSingle, reflHom_mulSingle]
    exact reflGen_conj_torusCoord F i j a
  have h1 := congrArg (fun φ => φ f) h
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h1

variable (K) in
@[expose] noncomputable def torusE (F : OrthFrame τ d) :
    Multiplicative (Fin d → ZMod 3) →* adjointGroup τ K :=
  (torusD K F).comp (MulEquiv.piMultiplicative fun _ : Fin d => ZMod 3).toMonoidHom

theorem torusE_apply (F : OrthFrame τ d) (v : Fin d → ZMod 3) :
    torusE K F (Multiplicative.ofAdd v) = torusD K F fun j => Multiplicative.ofAdd (v j) :=
  rfl

theorem torusE_injective (F : OrthFrame τ d) : Function.Injective (torusE K F) := fun _ _ h =>
  (MulEquiv.piMultiplicative fun _ : Fin d => ZMod 3).injective (torusD_injective (K := K) F h)

theorem reflGen_conj_torusE (F : OrthFrame τ d) (i : Fin d) (v : Fin d → ZMod 3) :
    reflGen K F i * torusE K F (Multiplicative.ofAdd v) * (reflGen K F i)⁻¹ =
      torusE K F (Multiplicative.ofAdd (v - reflCoeff i v • Pi.single i 1)) := by
  rw [torusE_apply, torusE_apply, reflGen_conj_torusD, reflHom_ofAdd]

theorem torusE_commute_rootInv (F : OrthFrame τ d) (v : Multiplicative (Fin d → ZMod 3)) :
    Commute (torusE K F v) (rootInv K F) := by
  have hmem : torusE K F v ∈ (torusD K F).range := ⟨_, rfl⟩
  have hle : (torusD K F).range ≤ Subgroup.centralizer {rootInv K F} := by
    rw [torusD, MonoidHom.noncommPiCoprod_range]
    refine iSup_le fun i => ?_
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, torusCoord_apply, rootInv]
    exact (commute_rho F (Fin.castSucc_lt_last i).ne _ _).eq
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hmem))

theorem ggTorusLift_of_frame (F : OrthFrame τ d) : GGTorusLift 3 d (adjointGroup τ K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : Subgroup.zpowers (rootInv K F) ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact rootInv_ne_one F
  have hU2 : IsPGroup 2 (Subgroup.zpowers (rootInv K F)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime (rootInv_sq F) (rootInv_ne_one F), pow_one]
  refine TableBF4.ggTorusLift_of_reflections (d := d) Nat.prime_three (by norm_num) (torusE K F)
    (torusE_injective F) reflCoeff reflCoeff_single (reflGen K F) (reflGen_conj_torusE F) hU hU2
    ?_
  intro v x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [((torusE_commute_rootInv F v).zpow_right k).eq, mul_inv_cancel_right]
  exact Subgroup.zpow_mem_zpowers _ _

end Torus

section Frames

@[expose] def frameE7Root : Fin 7 → (Fin Tag.E7.rank → ℤ) :=
  ![![2, 2, 3, 4, 3, 2, 1], ![0, 1, 1, 2, 2, 2, 1], ![0, 1, 1, 2, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0]]

@[expose] def frameE8Root : Fin 8 → (Fin Tag.E8.rank → ℤ) :=
  ![![2, 3, 4, 6, 5, 4, 3, 2], ![2, 2, 3, 4, 3, 2, 1, 0], ![0, 1, 1, 2, 2, 2, 1, 0],
    ![0, 1, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0]]

theorem frameE7Root_mem : ∀ i, frameE7Root i ∈ rootFinset .E7 := by decide +kernel

theorem frameE8Root_mem : ∀ i, frameE8Root i ∈ rootFinset .E8 := by decide +kernel


theorem frameE7Root_orth : ∀ i j, i ≠ j → iform (frameE7Root i) (frameE7Root j) = 0 := by
  decide +kernel

theorem frameE8Root_orth : ∀ i j, i ≠ j → iform (frameE8Root i) (frameE8Root j) = 0 := by
  decide +kernel

@[expose] def frameE7 : OrthFrame .E7 6 where
  root := frameE7Root
  symm_one := fun i => by simp [Tag.symmetrizer]
  isRoot := fun i => mem_rootFinset.1 (frameE7Root_mem i)
  orth := frameE7Root_orth

@[expose] def frameE8 : OrthFrame .E8 7 where
  root := frameE8Root
  symm_one := fun i => by simp [Tag.symmetrizer]
  isRoot := fun i => mem_rootFinset.1 (frameE8Root_mem i)
  orth := frameE8Root_orth

end Frames

section Recipe

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggTorusLift_E7Two : GGTorusLift 3 6 (TableBExc.RecipeGroup .E7 K) :=
  TableBF4.ggTorusLift_of_mulEquiv (TableBExc.recipeEquiv .E7 K) (ggTorusLift_of_frame frameE7)

theorem ggTorusLift_E8Two : GGTorusLift 3 7 (TableBExc.RecipeGroup .E8 K) :=
  TableBF4.ggTorusLift_of_mulEquiv (TableBExc.recipeEquiv .E8 K) (ggTorusLift_of_frame frameE8)

end Recipe

end TableBExcTwo

end CFSG.StandardType
