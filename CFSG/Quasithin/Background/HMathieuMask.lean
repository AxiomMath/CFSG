module

public import CFSG.Quasithin.Background.HMathieuBits
public import CFSG.Quasithin.Background.HMathieuArr
public import CFSG.Quasithin.Background.HMathieuStd

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code

@[expose] def permCols (a : Array ℕ) : List ℕ := (List.range 24).map fun j => 2 ^ a[j]!

@[expose] def permM (a : Array ℕ) (x : ℕ) : ℕ := actM (permCols a) x

@[expose] def permWordHom (σ : Equiv.Perm (Fin 24)) :
    (Fin 24 → ZMod 2) →+ (Fin 24 → ZMod 2) where
  toFun := permWord σ
  map_zero' := rfl
  map_add' _ _ := rfl

@[expose] def HasArr (σ : Equiv.Perm (Fin 24)) (a : Array ℕ) : Prop :=
  ∀ i : Fin 24, (σ i : ℕ) = a[(i : ℕ)]!

theorem permWord_bvec {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (ha : HasArr σ a) (x : ℕ) :
    permWord σ (bvec 24 x) = bvec 24 (permM a x) := by
  refine addHom_bvec (permWordHom σ) (permCols a) (by simp [permCols]) ?_ x
  intro j hj
  rw [List.getD_eq_getElem _ _ (by simpa [permCols] using hj)]
  simp only [permCols, List.getElem_map, List.getElem_range]
  funext i
  have hj' : a[j]! = (σ ⟨j, hj⟩ : ℕ) := (ha ⟨j, hj⟩).symm
  rw [hj']
  change bvec 24 (2 ^ j) (σ⁻¹ i) = bvec 24 (2 ^ (σ ⟨j, hj⟩ : ℕ)) i
  simp only [bvec_apply, Nat.testBit_two_pow]
  have : (j = ((σ⁻¹ i : Fin 24) : ℕ)) ↔ ((σ ⟨j, hj⟩ : Fin 24) : ℕ) = i := by
    constructor
    · intro h
      have : (⟨j, hj⟩ : Fin 24) = σ⁻¹ i := Fin.ext h
      rw [this]
      simp
    · intro h
      have : σ ⟨j, hj⟩ = i := Fin.ext h
      rw [← this]
      simp
  by_cases h : j = ((σ⁻¹ i : Fin 24) : ℕ)
  · rw [decide_eq_true h, decide_eq_true (this.1 h)]
  · rw [decide_eq_false h, decide_eq_false (fun h' => h (this.2 h'))]

theorem hasArr_permOfArr {a b : Array ℕ} (h : InvPairOK 24 a b = true) :
    HasArr (permOfArr 24 a b h) a :=
  permOfArr_val h

theorem hasArr_permOfArr_inv {a b : Array ℕ} (h : InvPairOK 24 a b = true) :
    HasArr (permOfArr 24 a b h)⁻¹ b := by
  intro i
  have hba : InvPairOK 24 b a = true := by
    unfold InvPairOK at h ⊢
    rw [List.all_eq_true] at h ⊢
    intro i hi
    have := h i hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this ⊢
    exact ⟨⟨⟨this.1.1.2, this.1.1.1⟩, this.2⟩, this.1.2⟩
  exact arrFun_val hba i

@[expose] def syndCols : List ℕ :=
  [62, 129, 65, 193, 61, 514, 258, 770, 59, 2052, 1028, 3076, 55, 2696, 1352, 4040, 47, 2896,
    1744, 3472, 31, 2528, 1952, 3680]

theorem synd_cols : ∀ j < 24, synd (bvec 24 (2 ^ j)) = bvec 12 (syndCols.getD j 0) := by
  decide +kernel

@[expose] def syndM (x : ℕ) : ℕ := actM syndCols x

theorem synd_bvec (x : ℕ) : synd (bvec 24 x) = bvec 12 (syndM x) :=
  addHom_bvec synd.toAddMonoidHom syndCols rfl synd_cols x

theorem syndCols_lt : ∀ c ∈ syndCols, c < 2 ^ 12 := by decide

theorem bvec_mem_C_iff (x : ℕ) : bvec 24 x ∈ C ↔ syndM x = 0 := by
  rw [← synd_eq_zero_iff, synd_bvec]
  constructor
  · intro h
    exact bvec_inj (actM_lt syndCols_lt x) (Nat.two_pow_pos 12) (h.trans (bvec_zero 12).symm)
  · intro h
    rw [h, bvec_zero]

@[expose] def autArrOK (a b : Array ℕ) : Bool :=
  (List.range 12).all fun i => syndM (permM a (Bmask i)) == 0 && syndM (permM b (Bmask i)) == 0

theorem mem_AutPerm_of_arr {a b : Array ℕ} (h : InvPairOK 24 a b = true)
    (hok : autArrOK a b = true) : permOfArr 24 a b h ∈ AutPerm := by
  have hspec : ∀ i : Fin 12, syndM (permM a (Bmask i)) = 0 ∧ syndM (permM b (Bmask i)) = 0 := by
    intro i
    have := List.all_eq_true.1 hok i (List.mem_range.2 i.2)
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this
  set p := permOfArr 24 a b h
  refine mem_AutPerm_of_basis (fun i => ?_) (fun i => ?_)
  · have : B i ∘ ⇑p = permWord p⁻¹ (B i) := by
      funext k
      simp [permWord]
    rw [this, B_eq_bvec, permWord_bvec (hasArr_permOfArr_inv h), bvec_mem_C_iff]
    exact (hspec i).2
  · have : B i ∘ ⇑p⁻¹ = permWord p (B i) := rfl
    rw [this, B_eq_bvec, permWord_bvec (hasArr_permOfArr h), bvec_mem_C_iff]
    exact (hspec i).1

@[expose] def ccECols : List ℕ :=
  [30, 65, 33, 97, 29, 258, 130, 386, 27, 1028, 516, 1540, 23, 1352, 680, 2024, 15, 1456, 880,
    1744, 31, 1248, 960, 1824]

theorem ccE_cols : ∀ j < 24, ccE (bvec 24 (2 ^ j)) = bvec 11 (ccECols.getD j 0) := by
  decide +kernel

@[expose] def liftECols : List ℕ :=
  [0x100001, 0x100010, 0x100100, 0x101000, 0x110000, 0x6ca000, 0xa6c000, 0xc6a000, 0x6ac000,
    0xaaa000, 0xccc000]

theorem liftE_cols : ∀ j < 11, liftE (bvec 11 (2 ^ j)) = bvec 24 (liftECols.getD j 0) := by
  decide +kernel

@[expose] def cc10Cols : List ℕ :=
  [15, 15, 63, 31, 33, 129, 65, 193, 34, 514, 258, 770, 36, 676, 340, 1012, 40, 728, 440, 872,
    32, 624, 480, 912]

theorem cc10_cols : ∀ j < 24, cc10 (bvec 24 (2 ^ j)) = bvec 10 (cc10Cols.getD j 0) := by
  decide +kernel

@[expose] def lift10Cols : List ℕ :=
  [0x100010, 0x100100, 0x101000, 0x110000, 0x6ca000, 0xa6c000, 0xc6a000, 0x6ac000, 0xaaa000,
    0xccc000]

theorem lift10_cols : ∀ j < 10, lift10 (bvec 10 (2 ^ j)) = bvec 24 (lift10Cols.getD j 0) := by
  decide +kernel

theorem ccE_bvec (x : ℕ) : ccE (bvec 24 x) = bvec 11 (actM ccECols x) :=
  addHom_bvec ccE.toAddMonoidHom ccECols rfl ccE_cols x

theorem liftE_bvec (x : ℕ) : liftE (bvec 11 x) = bvec 24 (actM liftECols x) :=
  addHom_bvec liftE.toAddMonoidHom liftECols rfl liftE_cols x

theorem cc10_bvec (x : ℕ) : cc10 (bvec 24 x) = bvec 10 (actM cc10Cols x) :=
  addHom_bvec cc10.toAddMonoidHom cc10Cols rfl cc10_cols x

theorem lift10_bvec (x : ℕ) : lift10 (bvec 10 x) = bvec 24 (actM lift10Cols x) :=
  addHom_bvec lift10.toAddMonoidHom lift10Cols rfl lift10_cols x

theorem ccECols_lt : ∀ c ∈ ccECols, c < 2 ^ 11 := by decide

theorem cc10Cols_lt : ∀ c ∈ cc10Cols, c < 2 ^ 10 := by decide

@[expose] def act11 (a : Array ℕ) (m : ℕ) : ℕ := actM ccECols (permM a (actM liftECols m))

@[expose] def act10 (a : Array ℕ) (m : ℕ) : ℕ := actM cc10Cols (permM a (actM lift10Cols m))

theorem xorLin_act11 (a : Array ℕ) : XorLin (act11 a) :=
  ((actM_xor _).comp (actM_xor _)).comp (actM_xor _)

theorem xorLin_act10 (a : Array ℕ) : XorLin (act10 a) :=
  ((actM_xor _).comp (actM_xor _)).comp (actM_xor _)

theorem act11_lt (a : Array ℕ) (m : ℕ) : act11 a m < 2 ^ 11 := actM_lt ccECols_lt _

theorem act10_lt (a : Array ℕ) (m : ℕ) : act10 a m < 2 ^ 10 := actM_lt cc10Cols_lt _

theorem rho11_toW (Γ : Subgroup (Equiv.Perm (Fin 24))) (hΓ : Γ ≤ AutPerm) (σ : ↥Γ)
    {a : Array ℕ} (ha : HasArr (σ : Equiv.Perm (Fin 24)) a) (m : ℕ) :
    rho11 Γ hΓ σ (toW 11 m) = toW 11 (act11 a m) := by
  have h1 : rho11 Γ hΓ σ (toW 11 m) =
      cocodeCoords.κ (G6.permAct 24 σ (cocodeCoords.lift (toW 11 m))) := rfl
  have h2 : Multiplicative.toAdd (cocodeCoords.lift (toW 11 m)) = liftE (bvec 11 m) := rfl
  have h3 : ∀ x, cocodeCoords.κ x = Multiplicative.ofAdd (ccE (Multiplicative.toAdd x)) :=
    fun _ => rfl
  rw [h1, h3, toAdd_permAct, h2, liftE_bvec, permWord_bvec ha, ccE_bvec]
  rfl

theorem rho10_toW (Γ : Subgroup (Equiv.Perm (Fin 24))) (hΓ : Γ ≤ mog22plus) (σ : ↥Γ)
    {a : Array ℕ} (ha : HasArr (σ : Equiv.Perm (Fin 24)) a) (m : ℕ) :
    rho10 Γ hΓ σ (toW 10 m) = toW 10 (act10 a m) := by
  have h1 : rho10 Γ hΓ σ (toW 10 m) =
      cocode22Coords.κ (G6.permAct 24 σ (cocode22Coords.lift (toW 10 m))) := rfl
  have h2 : Multiplicative.toAdd (cocode22Coords.lift (toW 10 m)) = lift10 (bvec 10 m) := rfl
  have h3 : ∀ x, cocode22Coords.κ x = Multiplicative.ofAdd (cc10 (Multiplicative.toAdd x)) :=
    fun _ => rfl
  rw [h1, h3, toAdd_permAct, h2, lift10_bvec, permWord_bvec ha, cc10_bvec]
  rfl

@[expose] def pairMask (i j : ℕ) : ℕ := 2 ^ i ^^^ 2 ^ j

theorem toAdd_pairVec (i j : Fin 24) (hij : i ≠ j) :
    Multiplicative.toAdd (pairVec i j) = bvec 24 (pairMask i j) := by
  rw [pairMask, bvec_xor]
  funext k
  simp only [pairVec, unitVec, toAdd_mul, toAdd_ofAdd, Pi.add_apply, Pi.single_apply, bvec_apply,
    Nat.testBit_two_pow]
  have hi : (decide ((i : ℕ) = k) = true) ↔ k = i := by
    rw [decide_eq_true_iff]
    exact ⟨fun h => (Fin.ext h).symm, fun h => by rw [h]⟩
  have hj : (decide ((j : ℕ) = k) = true) ↔ k = j := by
    rw [decide_eq_true_iff]
    exact ⟨fun h => (Fin.ext h).symm, fun h => by rw [h]⟩
  by_cases h1 : k = i <;> by_cases h2 : k = j <;> simp_all

@[expose] def o2Masks22 : List ℕ :=
  ((List.range 24).filter (2 ≤ ·)).map fun j => actM cc10Cols (pairMask 0 j)

@[expose] def o2Masks23 : List ℕ :=
  ((List.range 24).filter (1 ≤ ·)).map fun j => actM ccECols (pairMask 0 j)

@[expose] def o2Masks24 : List ℕ :=
  (List.range 24).flatMap fun i =>
    ((List.range 24).filter (i < ·)).map fun j => actM ccECols (pairMask i j)

theorem toW_o2_22 {o : ℕ} (ho : o ∈ o2Masks22) :
    ∃ j : Fin 24, j ≠ 0 ∧ j ≠ 1 ∧ toW 10 o = cocode22Coords.κ (pairVec 0 j) := by
  simp only [o2Masks22, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at ho
  obtain ⟨j, ⟨hj, h2⟩, rfl⟩ := ho
  refine ⟨⟨j, hj⟩, fun h => by simp [Fin.ext_iff] at h; omega,
    fun h => by simp [Fin.ext_iff] at h; omega, ?_⟩
  change _ = Multiplicative.ofAdd (cc10 (Multiplicative.toAdd (pairVec 0 ⟨j, hj⟩)))
  rw [toAdd_pairVec 0 ⟨j, hj⟩ (fun h => by simp [Fin.ext_iff] at h; omega), cc10_bvec]
  rfl

theorem toW_o2_23 {o : ℕ} (ho : o ∈ o2Masks23) :
    ∃ j : Fin 24, j ≠ 0 ∧ toW 11 o = cocodeCoords.κ (pairVec 0 j) := by
  simp only [o2Masks23, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at ho
  obtain ⟨j, ⟨hj, h1⟩, rfl⟩ := ho
  refine ⟨⟨j, hj⟩, fun h => by simp [Fin.ext_iff] at h; omega, ?_⟩
  change _ = Multiplicative.ofAdd (ccE (Multiplicative.toAdd (pairVec 0 ⟨j, hj⟩)))
  rw [toAdd_pairVec 0 ⟨j, hj⟩ (fun h => by simp [Fin.ext_iff] at h; omega), ccE_bvec]
  rfl

theorem toW_o2_24 {o : ℕ} (ho : o ∈ o2Masks24) :
    ∃ i j : Fin 24, i ≠ j ∧ toW 11 o = cocodeCoords.κ (pairVec i j) := by
  simp only [o2Masks24, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq] at ho
  obtain ⟨i, hi, j, ⟨hj, hij⟩, rfl⟩ := ho
  refine ⟨⟨i, hi⟩, ⟨j, hj⟩, fun h => by simp [Fin.ext_iff] at h; omega, ?_⟩
  change _ = Multiplicative.ofAdd (ccE (Multiplicative.toAdd (pairVec ⟨i, hi⟩ ⟨j, hj⟩)))
  rw [toAdd_pairVec ⟨i, hi⟩ ⟨j, hj⟩ (fun h => by simp [Fin.ext_iff] at h; omega), ccE_bvec]
  rfl

end CFSG.Quasithin.H.Mathieu
