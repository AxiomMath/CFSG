module

public import CFSG.Monster.B.Gen.EbarPairing
public import CFSG.Monster.B.Max2.Tower
public import CFSG.Monster.B.Co2.MatrixWBase

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.VisQuot

theorem eq_top_of_le_card_closure_map {K L : Type*} [Group K] [Group L] [Finite K]
    (φ : K →* L) (hφ : Function.Injective φ) (H : Subgroup K) {a b : K} (ha : a ∈ H)
    (hb : b ∈ H) (hcard : Nat.card K ≤ Nat.card (Subgroup.closure ({φ a, φ b} : Set L))) :
    H = ⊤ := by
  have hle : Subgroup.closure ({φ a, φ b} : Set L) ≤ H.map φ := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨a, ha, rfl⟩
    · exact ⟨b, hb, rfl⟩
  have : Finite (H.map φ) := Finite.of_surjective _ (φ.subgroupMap_surjective H)
  refine Subgroup.eq_top_of_le_card H ?_
  calc Nat.card K ≤ _ := hcard
    _ ≤ Nat.card (H.map φ) := Subgroup.card_le_of_le hle
    _ = Nat.card H := Subgroup.card_map_of_injective hφ

theorem wAct_mul_rev {v : L2} (k k' : Kstab v) : wAct v (k * k') = wAct v k' * wAct v k := by
  have h := (KvAct v).map_mul k k'
  change MulOpposite.op (wAct v (k * k')) =
    MulOpposite.op (wAct v k) * MulOpposite.op (wAct v k') at h
  rw [← MulOpposite.op_mul] at h
  exact MulOpposite.op_injective h

theorem wAct_one_eq {v : L2} : wAct v 1 = 1 := by
  have h := (KvAct v).map_one
  change MulOpposite.op (wAct v 1) = 1 at h
  exact MulOpposite.op_injective (h.trans MulOpposite.op_one.symm)

@[expose] noncomputable def kvMat {v : L2} (β : Module.Basis (Fin 22) (ZMod 2) (Wv v))
    (k : Kstab v) : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  Matrix.of fun i j => β.repr (wAct v k (β i)) j

theorem kvMat_apply {v : L2} (β : Module.Basis (Fin 22) (ZMod 2) (Wv v)) (k : Kstab v)
    (i j : Fin 22) : kvMat β k i j = β.repr (wAct v k (β i)) j := rfl

theorem kvMat_one {v : L2} (β : Module.Basis (Fin 22) (ZMod 2) (Wv v)) : kvMat β 1 = 1 := by
  ext i j
  rw [kvMat_apply, wAct_one_eq, Module.End.one_apply, Module.Basis.repr_self, Matrix.one_apply,
    Finsupp.single_apply]

theorem kvMat_mul
    {v : L2} (β : Module.Basis (Fin 22) (ZMod 2) (Wv v)) (k k' : Kstab v) :
    kvMat β (k * k') = kvMat β k * kvMat β k' := by
  ext i j
  rw [kvMat_apply, wAct_mul_rev, Module.End.mul_apply, Matrix.mul_apply]
  conv_lhs => rw [← β.sum_repr (wAct v k (β i))]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply, smul_eq_mul, kvMat_apply]

@[expose] noncomputable def kvGL
    {v : L2} (β : Module.Basis (Fin 22) (ZMod 2) (Wv v)) :
    Kstab v →* GL (Fin 22) (ZMod 2) :=
  MonoidHom.toHomUnits
    { toFun := kvMat β
      map_one' := kvMat_one β
      map_mul' := kvMat_mul β }

theorem coe_kvGL
    {v : L2} (β : Module.Basis (Fin 22) (ZMod 2) (Wv v)) (k : Kstab v) :
    ((kvGL β k : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) = kvMat β k := rfl

theorem kvGL_injective
    {v : L2} (hv : Function.Injective (KvAct v))
    (β : Module.Basis (Fin 22) (ZMod 2) (Wv v)) : Function.Injective (kvGL β) := by
  intro k k' h
  have hm : kvMat β k = kvMat β k' := by rw [← coe_kvGL, ← coe_kvGL, h]
  apply hv
  change MulOpposite.op (wAct v k) = MulOpposite.op (wAct v k')
  congr 1
  refine β.ext fun i => β.repr.injective (Finsupp.ext fun j => ?_)
  exact congrFun (congrFun hm i) j

theorem phi0_coordOf_rStar_ne_zero : phi0 (coordOf rStar) ≠ 0 := by
  rw [phi0_coordOf_rStar]
  exact Co2.v0_ne_zero

theorem finrank_Wv_rStar : Module.finrank (ZMod 2) (Wv (phi0 (coordOf rStar))) = 22 :=
  finrank_Wv phi0_coordOf_rStar_ne_zero

@[expose] noncomputable def psiBasis (e : Fin 22 → Cbar) (he : ∀ i, e i ∈ Ebar)
    (hind : LinearIndependent (ZMod 2) fun i => Multiplicative.toAdd (psiBar ⟨e i, he i⟩)) :
    Module.Basis (Fin 22) (ZMod 2) (Wv (phi0 (coordOf rStar))) :=
  basisOfLinearIndependentOfCardEqFinrank hind (by rw [Fintype.card_fin, finrank_Wv_rStar])

theorem psiBasis_apply (e : Fin 22 → Cbar) (he : ∀ i, e i ∈ Ebar)
    (hind : LinearIndependent (ZMod 2) fun i => Multiplicative.toAdd (psiBar ⟨e i, he i⟩))
    (i : Fin 22) : psiBasis e he hind i = Multiplicative.toAdd (psiBar ⟨e i, he i⟩) := by
  rw [psiBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

theorem kvMat_of_conj (e : Fin 22 → Cbar) (he : ∀ i, e i ∈ Ebar)
    (hind : LinearIndependent (ZMod 2) fun i => Multiplicative.toAdd (psiBar ⟨e i, he i⟩))
    {g : Cbar} (hg : g ∈ Jbar) (R : Matrix (Fin 22) (Fin 22) (ZMod 2))
    (hR : ∀ i, psiBar ⟨g⁻¹ * e i * g, conj_mem_Ebar hg (he i)⟩ =
      Multiplicative.ofAdd (∑ j, R i j • Multiplicative.toAdd (psiBar ⟨e j, he j⟩))) :
    kvMat (psiBasis e he hind) (jbarToKv ⟨g, hg⟩) = R := by
  ext i j
  rw [kvMat_apply, psiBasis_apply]
  have h := psiBar_conj hg (he i)
  rw [hR i] at h
  have h' := congrArg Multiplicative.toAdd h
  simp only [toAdd_ofAdd] at h'
  rw [← h']
  have hs : (∑ j, R i j • Multiplicative.toAdd (psiBar ⟨e j, he j⟩)) =
      ∑ j, R i j • psiBasis e he hind j := by
    simp only [psiBasis_apply]
  rw [hs, Module.Basis.repr_sum_self]

theorem natCard_Kstab_rStar :
    Nat.card (Kstab (phi0 (coordOf rStar))) = 42305421312000 :=
  natCard_Kstab_of_short (phi0_mem_shortSet' isShortCoord_rStar)

theorem finite_Kstab_rStar :
    Finite (Kstab (phi0 (coordOf rStar))) :=
  Nat.finite_of_card_ne_zero (by rw [natCard_Kstab_rStar]; norm_num)

theorem jbarToKv_onto_of_max2
    (G : Subgroup Cbar) {a b : Cbar} (haG : a ∈ G) (hbG : b ∈ G)
    (haJ : a ∈ Jbar) (hbJ : b ∈ Jbar) (e : Fin 22 → Cbar) (he : ∀ i, e i ∈ Ebar)
    (hind : LinearIndependent (ZMod 2) fun i => Multiplicative.toAdd (psiBar ⟨e i, he i⟩))
    (hR1 : ∀ i, psiBar ⟨a⁻¹ * e i * a, conj_mem_Ebar haJ (he i)⟩ =
      Multiplicative.ofAdd (∑ j, ((Max2.R1u : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) i j •
        Multiplicative.toAdd (psiBar ⟨e j, he j⟩)))
    (hR2 : ∀ i, psiBar ⟨b⁻¹ * e i * b, conj_mem_Ebar hbJ (he i)⟩ =
      Multiplicative.ofAdd (∑ j, ((Max2.R2u : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) i j •
        Multiplicative.toAdd (psiBar ⟨e j, he j⟩))) :
    ∀ k : Kstab (phi0 (coordOf rStar)), ∃ g : Jbar, (g : Cbar) ∈ G ∧ jbarToKv g = k := by
  have := finite_Kstab_rStar
  set β := psiBasis e he hind
  have ha1 : kvGL β (jbarToKv ⟨a, haJ⟩) = Max2.R1u :=
    Units.ext (by rw [coe_kvGL, kvMat_of_conj e he hind haJ _ hR1])
  have hb1 : kvGL β (jbarToKv ⟨b, hbJ⟩) = Max2.R2u :=
    Units.ext (by rw [coe_kvGL, kvMat_of_conj e he hind hbJ _ hR2])
  have htop := eq_top_of_le_card_closure_map (kvGL β) (kvGL_injective KvAct_injective_rStar β)
    ((G.subgroupOf Jbar).map jbarToKv) (a := jbarToKv ⟨a, haJ⟩) (b := jbarToKv ⟨b, hbJ⟩)
    ⟨⟨a, haJ⟩, Subgroup.mem_subgroupOf.2 haG, rfl⟩ ⟨⟨b, hbJ⟩, Subgroup.mem_subgroupOf.2 hbG, rfl⟩
    (by rw [ha1, hb1, natCard_Kstab_rStar]; exact Max2.card_closure_R12_ge)
  intro k
  have hk : k ∈ (G.subgroupOf Jbar).map jbarToKv := htop ▸ Subgroup.mem_top k
  obtain ⟨g, hg, rfl⟩ := hk
  exact ⟨g, Subgroup.mem_subgroupOf.1 hg, rfl⟩

@[expose] def letterIn {M : Type*} [Group M] (x y : M) (t : Bool × Bool) : M :=
  if t.2 then (if t.1 then x else y)⁻¹ else if t.1 then x else y

@[expose] def wordIn {M : Type*} [Group M] (x y : M) (w : List (Bool × Bool)) : M :=
  (w.map (letterIn x y)).prod

theorem map_letterIn {M N : Type*} [Group M] [Group N] (f : M →* N) (x y : M) (t : Bool × Bool) :
    f (letterIn x y t) = letterIn (f x) (f y) t := by
  obtain ⟨s, i⟩ := t
  cases s <;> cases i <;> simp [letterIn]

theorem map_wordIn {M N : Type*} [Group M] [Group N] (f : M →* N) (x y : M)
    (w : List (Bool × Bool)) : f (wordIn x y w) = wordIn (f x) (f y) w := by
  rw [wordIn, wordIn, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun t _ => map_letterIn f x y t

theorem wordIn_mem {M : Type*} [Group M] (H : Subgroup M) {x y : M} (hx : x ∈ H) (hy : y ∈ H)
    (w : List (Bool × Bool)) : wordIn x y w ∈ H := by
  rw [wordIn]
  refine Subgroup.list_prod_mem H fun z hz => ?_
  obtain ⟨⟨s, i⟩, -, rfl⟩ := List.mem_map.1 hz
  cases s <;> cases i <;> simp [letterIn, hx, hy, H.inv_mem]

@[expose] def mulRows (A B : Array ℕ) : Array ℕ :=
  ((List.range 22).map fun i => Max2.Native.act22 B A[i]!).toArray

@[expose] def idRows : Array ℕ := ((List.range 22).map fun i => 1 <<< i).toArray

theorem getElem!_listRange_map {f : ℕ → ℕ} {i : ℕ} (hi : i < 22) :
    ((List.range 22).map f).toArray[i]! = f i := by
  rw [getElem!_pos ((List.range 22).map f).toArray i (by simpa using hi)]
  simp

theorem decMat_mulRows (A B : Array ℕ) :
    Max2.decMat (mulRows A B) = Max2.decMat A * Max2.decMat B := by
  ext i j
  rw [Max2.decMat, Matrix.of_apply, mulRows, getElem!_listRange_map i.isLt, Max2.bvec_act22,
    Matrix.mul_apply]
  simp only [Matrix.vecMul, dotProduct, Max2.decMat, Matrix.of_apply]

theorem decMat_idRows : Max2.decMat idRows = 1 := by
  ext i j
  rw [Max2.decMat, Matrix.of_apply, idRows, getElem!_listRange_map i.isLt, bvec_apply,
    Matrix.one_apply, Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : i = j
  · subst h
    simp
  · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
    simp [h, h']

@[expose] def r2InvRows : Array ℕ :=
  #[1127759, 4185780, 1092240, 3349584, 2446896, 1588250, 3008677, 2381804, 3694636, 2173409,
    1840875, 2418042, 776914, 3494035, 4183051, 845183, 3826102, 1306480, 1104742, 1299143,
    2278585, 1103961]

theorem r1_mul_r1_check : mulRows Max2.Native.r1Rows Max2.Native.r1Rows = idRows := by
  decide +kernel

theorem r2_mul_r2Inv_check : mulRows Max2.Native.r2Rows r2InvRows = idRows := by
  decide +kernel

theorem R1u_inv :
    (Max2.R1u⁻¹ : GL (Fin 22) (ZMod 2)) = Max2.R1u := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  have h := congrArg Max2.decMat r1_mul_r1_check
  rw [decMat_mulRows, decMat_idRows, ← Max2.coe_R1u] at h
  rw [Units.val_mul, h, Units.val_one]

theorem coe_R2u_inv :
    ((Max2.R2u⁻¹ : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) =
    Max2.decMat r2InvRows := by
  have h := congrArg Max2.decMat r2_mul_r2Inv_check
  rw [decMat_mulRows, decMat_idRows, ← Max2.coe_R2u] at h
  calc ((Max2.R2u⁻¹ : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2))
      = ((Max2.R2u⁻¹ : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) *
          ((Max2.R2u : Matrix (Fin 22) (Fin 22) (ZMod 2)) * Max2.decMat r2InvRows) := by
        rw [h, mul_one]
    _ = Max2.decMat r2InvRows := by rw [← mul_assoc, Units.inv_mul, one_mul]

@[expose] def letterRows (t : Bool × Bool) : Array ℕ :=
  if t.1 then Max2.Native.r1Rows else if t.2 then r2InvRows else Max2.Native.r2Rows

theorem decMat_letterRows (t : Bool × Bool) :
    Max2.decMat (letterRows t) =
      ((letterIn Max2.R1u Max2.R2u t : GL (Fin 22) (ZMod 2)) :
        Matrix (Fin 22) (Fin 22) (ZMod 2)) := by
  obtain ⟨s, i⟩ := t
  cases s <;> cases i
  · simp only [letterRows, letterIn, Bool.false_eq_true, ite_false, Max2.coe_R2u]
  · simp only [letterRows, letterIn, Bool.false_eq_true, ite_false, ite_true, coe_R2u_inv]
  · simp only [letterRows, letterIn, Bool.false_eq_true, ite_false, ite_true, Max2.coe_R1u]
  · simp only [letterRows, letterIn, ite_true, R1u_inv, Max2.coe_R1u]

theorem decMat_foldl_letterRows
    (w : List (Bool × Bool)) (acc : Array ℕ) :
    Max2.decMat (w.foldl (fun acc t => mulRows acc (letterRows t)) acc) =
      Max2.decMat acc * ((wordIn Max2.R1u Max2.R2u w : GL (Fin 22) (ZMod 2)) :
        Matrix (Fin 22) (Fin 22) (ZMod 2)) := by
  induction w generalizing acc with
  | nil => rw [List.foldl_nil, wordIn, List.map_nil, List.prod_nil, Units.val_one, mul_one]
  | cons t w ih =>
    rw [List.foldl_cons, ih, decMat_mulRows, decMat_letterRows]
    simp only [wordIn, List.map_cons, List.prod_cons, Units.val_mul, mul_assoc]

@[expose] def kernelWord : List (Bool × Bool) :=
  (List.replicate 14 [(true, false), (false, true), (false, true), (true, false), (true, false),
    (false, true)]).flatten

theorem kernelWord_check :
    kernelWord.foldl (fun acc t => mulRows acc (letterRows t)) idRows = idRows := by
  decide +kernel

theorem wordIn_R_kernelWord :
    wordIn Max2.R1u Max2.R2u kernelWord = 1 := by
  apply Units.ext
  have h := congrArg Max2.decMat kernelWord_check
  rw [decMat_foldl_letterRows, decMat_idRows, one_mul] at h
  rw [h, Units.val_one]

theorem wordIn_mem_Ebar
    {a b : Cbar} (haJ : a ∈ Jbar) (hbJ : b ∈ Jbar) (e : Fin 22 → Cbar)
    (he : ∀ i, e i ∈ Ebar)
    (hind : LinearIndependent (ZMod 2) fun i => Multiplicative.toAdd (psiBar ⟨e i, he i⟩))
    (hR1 : ∀ i, psiBar ⟨a⁻¹ * e i * a, conj_mem_Ebar haJ (he i)⟩ =
      Multiplicative.ofAdd (∑ j, ((Max2.R1u : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) i j •
        Multiplicative.toAdd (psiBar ⟨e j, he j⟩)))
    (hR2 : ∀ i, psiBar ⟨b⁻¹ * e i * b, conj_mem_Ebar hbJ (he i)⟩ =
      Multiplicative.ofAdd (∑ j, ((Max2.R2u : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) i j •
        Multiplicative.toAdd (psiBar ⟨e j, he j⟩)))
    (w : List (Bool × Bool)) (hw : wordIn Max2.R1u Max2.R2u w = 1) : wordIn a b w ∈ Ebar := by
  set β := psiBasis e he hind
  have ha1 : kvGL β (jbarToKv ⟨a, haJ⟩) = Max2.R1u :=
    Units.ext (by rw [coe_kvGL, kvMat_of_conj e he hind haJ _ hR1])
  have hb1 : kvGL β (jbarToKv ⟨b, hbJ⟩) = Max2.R2u :=
    Units.ext (by rw [coe_kvGL, kvMat_of_conj e he hind hbJ _ hR2])
  set g : Jbar := wordIn ⟨a, haJ⟩ ⟨b, hbJ⟩ w
  have hg : (g : Cbar) = wordIn a b w := map_wordIn Jbar.subtype _ _ w
  have h1 : kvGL β (jbarToKv g) = 1 := by
    rw [map_wordIn, map_wordIn, ha1, hb1, hw]
  have h := kvGL_injective KvAct_injective_rStar β (h1.trans (map_one _).symm)
  have hker : g ∈ jbarToKv.ker := h
  rw [ker_jbarToKv, Subgroup.mem_subgroupOf, hg] at hker
  exact hker

@[expose] def gramRows : Array ℕ :=
  #[1949072, 4152928, 2289248, 1275280, 4091849, 4175814, 3657014, 1569337, 1739897, 3879094,
    1388927, 459095, 3655339, 3376829, 233694, 3961317, 2916075, 2915326, 1285363, 230195,
    2406395, 1290870]

@[expose] def gramInvRows : Array ℕ :=
  #[723488, 225572, 2697498, 4027892, 1072748, 2326747, 397624, 2109992, 478798, 2717073,
    3552024, 69909, 3968730, 3688078, 2728730, 4083744, 3558191, 1410403, 1283400, 1110541,
    1029144, 128684]

theorem gram_mul_inv_check : mulRows gramRows gramInvRows = idRows := by
  decide +kernel

theorem gram_symm_nat : ∀ i < 22, ∀ j < 22, gramRows[i]!.testBit j = gramRows[j]!.testBit i := by
  decide +kernel

theorem gram_diag_nat : ∀ i < 22, gramRows[i]!.testBit i = false := by
  decide +kernel

theorem gram_symm (i j : Fin 22) : Max2.decMat gramRows i j = Max2.decMat gramRows j i := by
  simp only [Max2.decMat, Matrix.of_apply, bvec_apply, gram_symm_nat i i.isLt j j.isLt]

theorem gram_diag (i : Fin 22) : Max2.decMat gramRows i i = 0 := by
  simp only [Max2.decMat, Matrix.of_apply, bvec_apply, gram_diag_nat i i.isLt]
  rfl

theorem linearIndependent_psi_of_cert (e : Fin 22 → Cbar) (he : ∀ i, e i ∈ Ebar)
    (hG : ∀ i j : Fin 22, i < j → e i * e j = e j * e i * xbar ^ (Max2.decMat gramRows i j).val) :
    LinearIndependent (ZMod 2) fun i => Multiplicative.toAdd (psiBar ⟨e i, he i⟩) :=
  linearIndependent_psi_of_gram e he (Max2.decMat gramRows) (Max2.decMat gramInvRows)
    (by rw [← decMat_mulRows, gram_mul_inv_check, decMat_idRows])
    (gram_rel_of_lt (Max2.decMat gramRows) gram_symm gram_diag hG)

theorem hom_eq_sum_of_eq_prod {G A : Type*} [Group G] [AddCommGroup A] [Module (ZMod 2) A]
    {H : Subgroup G} (φ : H →* Multiplicative A) {n : ℕ} (f : Fin n → G) (hf : ∀ j, f j ∈ H)
    {x y : G} (hx : x ∈ H) (hφx : φ ⟨x, hx⟩ = 1) (hy : y ∈ H) (c : Fin n → ZMod 2) (ε : ℕ)
    (h : y = ((List.finRange n).map fun j => f j ^ (c j).val).prod * x ^ ε) :
    φ ⟨y, hy⟩ = Multiplicative.ofAdd (∑ j, c j • Multiplicative.toAdd (φ ⟨f j, hf j⟩)) := by
  have key : (⟨y, hy⟩ : H) =
      ((List.finRange n).map fun j => (⟨f j, hf j⟩ : H) ^ (c j).val).prod * (⟨x, hx⟩ : H) ^ ε := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_pow, SubmonoidClass.coe_list_prod, List.map_map]
    exact h
  rw [key, map_mul, map_pow, hφx, one_pow, mul_one, map_list_prod, List.map_map,
    ← Fin.prod_univ_def]
  apply Multiplicative.toAdd.injective
  rw [toAdd_prod, toAdd_ofAdd]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Function.comp_apply, map_pow, toAdd_pow, ← Nat.cast_smul_eq_nsmul (ZMod 2),
    ZMod.natCast_zmod_val]

theorem psiBar_eq_sum_of_eq_prod {e : Fin 22 → Cbar} (he : ∀ i, e i ∈ Ebar) {y : Cbar}
    (hy : y ∈ Ebar) (c : Fin 22 → ZMod 2) (ε : ℕ)
    (h : y = ((List.finRange 22).map fun j => e j ^ (c j).val).prod * xbar ^ ε) :
    psiBar ⟨y, hy⟩ = Multiplicative.ofAdd (∑ j, c j • Multiplicative.toAdd (psiBar ⟨e j, he j⟩)) :=
  hom_eq_sum_of_eq_prod psiBar e he xbar_mem_Ebar ((psiBar_eq_one_iff _).2 (Or.inr rfl)) hy c ε h

end CFSG.Monster.B
