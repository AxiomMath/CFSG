module

public import CFSG.Quasithin.H13.L32NS8Plane
public import CFSG.Quasithin.EmptyFaithful.SzN28S8Mod
public import CFSG.Quasithin.H13.L32NLem14411a

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.S8Tr

open Matrix Mat8Cert S8Cert CFSG.Quasithin.H13.L1442M CFSG.Quasithin.H13.L14411 CFSG.Open

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

structure Frame (B : LinearMap.BilinForm (ZMod 2) V) (I I' : Submodule (ZMod 2) V) : Prop where
  alt : ∀ v, B v v = 0
  nd : ∀ v, (∀ w, B v w = 0) → v = 0
  compl : IsCompl I I'
  iso : ∀ v ∈ I, ∀ w ∈ I, B v w = 0
  iso' : ∀ v ∈ I', ∀ w ∈ I', B v w = 0
  rank : Module.finrank (ZMod 2) I = 4
  rank' : Module.finrank (ZMod 2) I' = 4

abbrev e8 : Fin 4 ⊕ Fin 4 ≃ Fin 8 := finSumFinEquiv

section Defs

variable (B : LinearMap.BilinForm (ZMod 2) V) {I : Submodule (ZMod 2) V}
  (b : Module.Basis (Fin 4) (ZMod 2) I) (d : Fin 4 → V)

@[expose] noncomputable def cS (v : V) : Fin 4 ⊕ Fin 4 → ZMod 2 :=
  Sum.elim (fun k => B v (d k)) (fun k => B (b k) v)

@[expose] noncomputable def coordL : V →ₗ[ZMod 2] (Fin 8 → ZMod 2) :=
  (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) e8.symm).toLinearMap ∘ₗ
    LinearMap.pi (Sum.elim (fun k => B.flip (d k)) (fun k => B (b k)))

theorem coordL_apply (v : V) : coordL B b d v = cS B b d v ∘ e8.symm := by
  funext i
  simp only [coordL, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, LinearMap.pi_apply, cS]
  rcases e8.symm i with k | k <;> rfl

@[expose] noncomputable def mI (γ : V ≃ₗ[ZMod 2] V) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fun k l => B (γ (b l)) (d k)

@[expose] noncomputable def nI (γ : V ≃ₗ[ZMod 2] V) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fun k m => B (b k) (γ (d m))

@[expose] noncomputable def qI (x : V ≃ₗ[ZMod 2] V) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fun k m => B (x (d m)) (d k)

@[expose] noncomputable def pI (x : V ≃ₗ[ZMod 2] V) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fun k l => B (b k) (x (b l))

end Defs

theorem reindex_mulVec (A : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2))
    (c : Fin 4 ⊕ Fin 4 → ZMod 2) :
    (Matrix.reindex e8 e8 A).mulVec (c ∘ e8.symm) = (A.mulVec c) ∘ e8.symm := by
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  congr 2
  funext s
  simp

namespace Frame

variable {B : LinearMap.BilinForm (ZMod 2) V} {I I' : Submodule (ZMod 2) V} (F : Frame B I I')
include F

theorem symm (v w : V) : B v w = B w v := by
  have h := F.alt (v + w)
  simp only [map_add, LinearMap.add_apply, F.alt v, F.alt w, zero_add, add_zero] at h
  have key : ∀ a c : ZMod 2, a + c = 0 → c = a := by decide
  exact key _ _ h

theorem eq_zero_of_orth {w : V} (h1 : ∀ i ∈ I, B w i = 0) (h2 : ∀ i ∈ I', B w i = 0) : w = 0 := by
  refine F.nd w fun u => ?_
  have hu : u ∈ I ⊔ I' := by rw [F.compl.sup_eq_top]; trivial
  obtain ⟨i, hi, i', hi', rfl⟩ := Submodule.mem_sup.mp hu
  rw [map_add, h1 i hi, h2 i' hi', add_zero]

variable [Finite V]

theorem exists_dual (b : Module.Basis (Fin 4) (ZMod 2) I) :
    ∃ d : Fin 4 → V, (∀ k, d k ∈ I') ∧ ∀ l k, B (b l) (d k) = if l = k then 1 else 0 := by
  classical
  let φ : I' →ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
    { toFun := fun j l => B (b l) j
      map_add' := fun j j' => funext fun l => by simp
      map_smul' := fun c j => funext fun l => by simp }
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro j hj
    rw [LinearMap.mem_ker] at hj
    have hjl : ∀ l, B (b l) j = 0 := fun l => congrFun hj l
    rw [Submodule.mem_bot]
    apply Subtype.ext
    refine F.eq_zero_of_orth (fun i hi => ?_) (fun i hi => F.iso' _ j.2 _ hi)
    rw [F.symm]
    have hi' : (⟨i, hi⟩ : I) = ∑ l, b.repr ⟨i, hi⟩ l • b l := (b.sum_repr _).symm
    have : i = ∑ l, b.repr ⟨i, hi⟩ l • (b l : V) := by
      have := congrArg Subtype.val hi'
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this
    rw [this, map_sum, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun l _ => by rw [map_smul, LinearMap.smul_apply, hjl l, smul_zero]
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [F.rank', Module.finrank_fin_fun])).mp hinj
  choose d hd using fun k => hsurj (Pi.single k 1)
  refine ⟨fun k => d k, fun k => (d k).2, fun l k => ?_⟩
  have := congrFun (hd k) l
  simp only [φ, LinearMap.coe_mk, AddHom.coe_mk] at this
  rw [this, Pi.single_apply]

omit F [Finite V] in
theorem expand_I (b : Module.Basis (Fin 4) (ZMod 2) I) {d : Fin 4 → V}
    (hbd : ∀ l k, B (b l) (d k) = if l = k then 1 else 0) {i : V} (hi : i ∈ I) :
    i = ∑ l, B i (d l) • (b l : V) := by
  classical
  have hi' : (⟨i, hi⟩ : I) = ∑ l, b.repr ⟨i, hi⟩ l • b l := (b.sum_repr _).symm
  have h1 : i = ∑ l, b.repr ⟨i, hi⟩ l • (b l : V) := by
    have := congrArg Subtype.val hi'
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this
  have h2 : ∀ l, B i (d l) = b.repr ⟨i, hi⟩ l := by
    intro l
    conv_lhs => rw [h1]
    rw [map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply, hbd, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  conv_lhs => rw [h1]
  simp only [h2]

omit [Finite V] in
theorem expand_I' (b : Module.Basis (Fin 4) (ZMod 2) I) {d : Fin 4 → V} (hd : ∀ k, d k ∈ I')
    (hbd : ∀ l k, B (b l) (d k) = if l = k then 1 else 0) {j : V} (hj : j ∈ I') :
    j = ∑ m, B (b m) j • d m := by
  classical
  set w := j - ∑ m, B (b m) j • d m with hw
  have hwI' : w ∈ I' := I'.sub_mem hj (I'.sum_mem fun m _ => I'.smul_mem _ (hd m))
  have hw0 : w = 0 := by
    refine F.eq_zero_of_orth (fun i hi => ?_) (fun i hi => F.iso' _ hwI' _ hi)
    rw [F.symm, expand_I b hbd hi, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [map_smul, LinearMap.smul_apply, hw, map_sub, map_sum]
    simp only [map_smul, hbd, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, sub_self]
  rw [hw, sub_eq_zero] at hw0
  exact hw0

omit [Finite V] in
theorem expand (b : Module.Basis (Fin 4) (ZMod 2) I) {d : Fin 4 → V} (hd : ∀ k, d k ∈ I')
    (hbd : ∀ l k, B (b l) (d k) = if l = k then 1 else 0) (v : V) :
    v = ∑ l, B v (d l) • (b l : V) + ∑ m, B (b m) v • d m := by
  have hv : v ∈ I ⊔ I' := by rw [F.compl.sup_eq_top]; trivial
  obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.mp hv
  have h1 : ∀ l, B (i + j) (d l) = B i (d l) := fun l => by
    rw [map_add, LinearMap.add_apply, F.iso' _ hj _ (hd l), add_zero]
  have h2 : ∀ m, B (b m) (i + j) = B (b m) j := fun m => by
    rw [map_add, F.iso _ (b m).2 _ hi, zero_add]
  simp only [h1, h2]
  rw [← expand_I b hbd hi, ← F.expand_I' b hd hbd hj]

omit [Finite V] in
theorem coordL_injective (b : Module.Basis (Fin 4) (ZMod 2) I) {d : Fin 4 → V}
    (hd : ∀ k, d k ∈ I') (hbd : ∀ l k, B (b l) (d k) = if l = k then 1 else 0) :
    Function.Injective (coordL B b d) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker, coordL_apply] at hv
  have h1 : ∀ s, cS B b d v s = 0 := fun s => by
    have := congrFun hv (e8 s)
    simpa using this
  rw [Submodule.mem_bot, F.expand b hd hbd v]
  have h2 : ∀ l, B v (d l) = 0 := fun l => h1 (Sum.inl l)
  have h3 : ∀ m, B (b m) v = 0 := fun m => h1 (Sum.inr m)
  simp [h2, h3]

theorem finrank_V : Module.finrank (ZMod 2) V = 8 := by
  rw [← Submodule.finrank_add_eq_of_isCompl F.compl, F.rank, F.rank']

@[expose] noncomputable def coord (b : Module.Basis (Fin 4) (ZMod 2) I) {d : Fin 4 → V}
    (hd : ∀ k, d k ∈ I') (hbd : ∀ l k, B (b l) (d k) = if l = k then 1 else 0) :
    V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2) :=
  LinearEquiv.ofBijective (coordL B b d) ⟨F.coordL_injective b hd hbd,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [F.finrank_V, Module.finrank_fin_fun])).mp (F.coordL_injective b hd hbd)⟩

theorem coord_apply (b : Module.Basis (Fin 4) (ZMod 2) I) {d : Fin 4 → V}
    (hd : ∀ k, d k ∈ I') (hbd : ∀ l k, B (b l) (d k) = if l = k then 1 else 0) (v : V) :
    F.coord b hd hbd v = cS B b d v ∘ e8.symm :=
  coordL_apply B b d v

theorem mat_eq_of_coord (b : Module.Basis (Fin 4) (ZMod 2) I) {d : Fin 4 → V}
    (hd : ∀ k, d k ∈ I') (hbd : ∀ l k, B (b l) (d k) = if l = k then 1 else 0)
    {A A' : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (h : ∀ v, A.mulVec (F.coord b hd hbd v) = A'.mulVec (F.coord b hd hbd v)) : A = A' := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := (F.coord b hd hbd).surjective x
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h]

omit [Finite V] in
theorem cS_pres (b : Module.Basis (Fin 4) (ZMod 2) I) {d : Fin 4 → V}
    (hd : ∀ k, d k ∈ I') (hbd : ∀ l k, B (b l) (d k) = if l = k then 1 else 0)
    {γ : V ≃ₗ[ZMod 2] V} (hγI : ∀ i ∈ I, γ i ∈ I) (hγI' : ∀ j ∈ I', γ j ∈ I') (v : V) :
    cS B b d (γ v) = (Matrix.fromBlocks (mI B b d γ) 0 0 (nI B b d γ)).mulVec (cS B b d v) := by
  rw [Matrix.fromBlocks_mulVec]
  funext s
  conv_lhs => rw [F.expand b hd hbd v]
  rcases s with k | k
  · simp only [cS, Sum.elim_inl, map_add, map_sum, map_smul, LinearMap.add_apply,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Matrix.zero_mulVec, add_zero]
    rw [show (∑ m, B (b m) v * B (γ (d m)) (d k)) = 0 from Finset.sum_eq_zero fun m _ => by
      rw [F.iso' _ (hγI' _ (hd m)) _ (hd k), mul_zero], add_zero]
    simp only [Matrix.mulVec, dotProduct, mI, Function.comp_apply, Sum.elim_inl]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  · simp only [cS, Sum.elim_inr, map_add, map_sum, map_smul, smul_eq_mul, Matrix.zero_mulVec,
      zero_add]
    rw [show (∑ l, B v (d l) * B (b k) (γ (b l))) = 0 from Finset.sum_eq_zero fun l _ => by
      rw [F.iso _ (b k).2 _ (hγI _ (b l).2), mul_zero], zero_add]
    simp only [Matrix.mulVec, dotProduct, nI, Function.comp_apply, Sum.elim_inr]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _

omit F [Finite V] in
theorem mI_transpose_mul (b : Module.Basis (Fin 4) (ZMod 2) I) {d : Fin 4 → V}
    (hbd : ∀ l k, B (b l) (d k) = if l = k then 1 else 0)
    {γ : V ≃ₗ[ZMod 2] V} (hiso : ∀ v w, B (γ v) (γ w) = B v w) (hγI : ∀ i ∈ I, γ i ∈ I) :
    (mI B b d γ)ᵀ * nI B b d γ = 1 := by
  ext l m
  have h1 := expand_I b hbd (hγI _ (b l).2)
  have h2 : B (γ (b l)) (γ (d m)) =
      Finset.univ.sum fun k => B (γ (b l)) (d k) * B (b k) (γ (d m)) := by
    conv_lhs => rw [h1]
    rw [map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hiso, hbd] at h2
  simp only [Matrix.mul_apply, Matrix.transpose_apply, mI, nI, Matrix.one_apply]
  rw [← h2]

theorem matOf_eq_blk (b : Module.Basis (Fin 4) (ZMod 2) I) {d : Fin 4 → V}
    (hd : ∀ k, d k ∈ I') (hbd : ∀ l k, B (b l) (d k) = if l = k then 1 else 0)
    {γ : V ≃ₗ[ZMod 2] V} (hiso : ∀ v w, B (γ v) (γ w) = B v w) (hγI : ∀ i ∈ I, γ i ∈ I)
    (hγI' : ∀ j ∈ I', γ j ∈ I') :
    (mI B b d γ).det ≠ 0 ∧ ((matOf (F.coord b hd hbd) γ : GL (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2)) = blk (mI B b d γ) ((mI B b d γ)⁻¹)ᵀ := by
  have hMN := mI_transpose_mul b hbd hiso hγI
  have hdet : (mI B b d γ).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hMN
    rw [Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hN : nI B b d γ = ((mI B b d γ)⁻¹)ᵀ := by
    rw [Matrix.transpose_nonsing_inv, Matrix.inv_eq_right_inv hMN]
  refine ⟨hdet, F.mat_eq_of_coord b hd hbd fun v => ?_⟩
  rw [matOf_mulVec, ← hN, blk, F.coord_apply, F.coord_apply, reindex_mulVec,
    F.cS_pres b hd hbd hγI hγI' v]

omit [Finite V] in
theorem cS_swap (b : Module.Basis (Fin 4) (ZMod 2) I) {d : Fin 4 → V}
    (hd : ∀ k, d k ∈ I') (hbd : ∀ l k, B (b l) (d k) = if l = k then 1 else 0)
    {x : V ≃ₗ[ZMod 2] V} (hxI : ∀ i ∈ I, x i ∈ I') (hxI' : ∀ j ∈ I', x j ∈ I) (v : V) :
    cS B b d (x v) = (Matrix.fromBlocks 0 (qI B d x) (pI B b x) 0).mulVec (cS B b d v) := by
  rw [Matrix.fromBlocks_mulVec]
  funext s
  conv_lhs => rw [F.expand b hd hbd v]
  rcases s with k | k
  · simp only [cS, Sum.elim_inl, map_add, map_sum, map_smul, LinearMap.add_apply,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Matrix.zero_mulVec, zero_add]
    rw [show (∑ l, B v (d l) * B (x (b l)) (d k)) = 0 from Finset.sum_eq_zero fun l _ => by
      rw [F.iso' _ (hxI _ (b l).2) _ (hd k), mul_zero], zero_add]
    simp only [Matrix.mulVec, dotProduct, qI, Function.comp_apply, Sum.elim_inr]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  · simp only [cS, Sum.elim_inr, map_add, map_sum, map_smul, smul_eq_mul, Matrix.zero_mulVec,
      add_zero]
    rw [show (∑ m, B (b m) v * B (b k) (x (d m))) = 0 from Finset.sum_eq_zero fun m _ => by
      rw [F.iso _ (b k).2 _ (hxI' _ (hd m)), mul_zero], add_zero]
    simp only [Matrix.mulVec, dotProduct, pI, Function.comp_apply, Sum.elim_inl]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _

omit [Finite V] in
theorem qI_transpose_mul (b : Module.Basis (Fin 4) (ZMod 2) I) {d : Fin 4 → V}
    (hd : ∀ k, d k ∈ I') (hbd : ∀ l k, B (b l) (d k) = if l = k then 1 else 0)
    {x : V ≃ₗ[ZMod 2] V} (hiso : ∀ v w, B (x v) (x w) = B v w) (hxI : ∀ i ∈ I, x i ∈ I') :
    (qI B d x)ᵀ * pI B b x = 1 := by
  ext m l
  have h1 := F.expand_I' b hd hbd (hxI _ (b l).2)
  have h2 : B (x (d m)) (x (b l)) =
      Finset.univ.sum fun k => B (x (d m)) (d k) * B (b k) (x (b l)) := by
    conv_lhs => rw [h1]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hiso, F.symm (d m) (b l), hbd] at h2
  simp only [Matrix.mul_apply, Matrix.transpose_apply, qI, pI, Matrix.one_apply]
  rw [← h2]
  simp only [eq_comm]

theorem matOf_eq_blk_tau (b : Module.Basis (Fin 4) (ZMod 2) I) {d : Fin 4 → V}
    (hd : ∀ k, d k ∈ I') (hbd : ∀ l k, B (b l) (d k) = if l = k then 1 else 0)
    {x : V ≃ₗ[ZMod 2] V} (hiso : ∀ v w, B (x v) (x w) = B v w) (hxI : ∀ i ∈ I, x i ∈ I')
    (hxI' : ∀ j ∈ I', x j ∈ I) :
    (qI B d x).det ≠ 0 ∧ ((matOf (F.coord b hd hbd) x : GL (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2)) =
        blk (qI B d x) ((qI B d x)⁻¹)ᵀ * (s8g4 : Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
  have hQP := F.qI_transpose_mul b hd hbd hiso hxI
  have hdet : (qI B d x).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hQP
    rw [Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hP : pI B b x = ((qI B d x)⁻¹)ᵀ := by
    rw [Matrix.transpose_nonsing_inv, Matrix.inv_eq_right_inv hQP]
  refine ⟨hdet, F.mat_eq_of_coord b hd hbd fun v => ?_⟩
  rw [matOf_mulVec, blk_mul_tau, ← hP, F.coord_apply, F.coord_apply, reindex_mulVec,
    F.cS_swap b hd hbd hxI hxI' v]

theorem exists_coord_le_s8 {Γ A : Subgroup (V ≃ₗ[ZMod 2] V)}
    {x : V ≃ₗ[ZMod 2] V}
    (d8 : SzN28.S8Data Γ A I I' x) (hiso : ∀ γ ∈ Γ, ∀ v w, B (γ v) (γ w) = B v w) :
    ∃ e : V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2), ∀ γ ∈ Γ, matOf e γ ∈ s8 := by
  let b : Module.Basis (Fin 4) (ZMod 2) I := Module.finBasisOfFinrankEq (ZMod 2) I F.rank
  obtain ⟨d, hd, hbd⟩ := F.exists_dual b
  refine ⟨F.coord b hd hbd, fun γ hγ => ?_⟩
  have hA : ∀ a ∈ A, matOf (F.coord b hd hbd) a ∈ s8 := by
    intro a ha
    obtain ⟨hdet, hmat⟩ := F.matOf_eq_blk b hd hbd (hiso a (d8.A_le ha)) (d8.A_inv_I a ha)
      (d8.A_inv_I' a ha)
    obtain ⟨u, hu, hu'⟩ := blk_mem_s8 _ hdet
    have : matOf (F.coord b hd hbd) a = u := Units.ext (hmat.trans hu'.symm)
    rw [this]
    exact hu
  have hxI : ∀ i ∈ I, x i ∈ I' := fun i hi => by
    rw [d8.I'_eq]
    exact ⟨i, hi, rfl⟩
  have hxI' : ∀ j ∈ I', x j ∈ I := fun j hj => by
    rw [d8.I'_eq] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    have hxx : x ((x : V →ₗ[ZMod 2] V) i) = i := d8.xx_apply i
    rw [hxx]
    exact hi
  have hx : matOf (F.coord b hd hbd) x ∈ s8 := by
    obtain ⟨hdet, hmat⟩ := F.matOf_eq_blk_tau b hd hbd (hiso x d8.x_mem) hxI hxI'
    obtain ⟨u, hu, hu'⟩ := blk_mem_s8 _ hdet
    have : matOf (F.coord b hd hbd) x = u * s8g4 :=
      Units.ext (by rw [hmat, Units.val_mul, hu'])
    rw [this]
    exact mul_mem hu s8g4_mem
  by_cases hγA : γ ∈ A
  · exact hA γ hγA
  · obtain ⟨a, ha, rfl⟩ := d8.outer γ hγ hγA
    rw [map_mul]
    exact mul_mem (hA a ha) hx

end Frame

theorem add_self8 (u : Fin 8 → ZMod 2) : u + u = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize u i = c
  revert c
  decide

theorem false_of_sylow_plane
    {T' : Subgroup (GL (Fin 8) (ZMod 2))} (hT's8 : T' ≤ s8) (hT' : Nat.card T' = 128)
    {w p : Fin 8 → ZMod 2} (hw0 : w ≠ 0) (hp0 : p ≠ 0) (hpw : p ≠ w)
    (hTw : ∀ t ∈ T', (t : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w = w)
    (hTp : ∀ t ∈ T', (t : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec p = p ∨
      (t : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec p = p + w)
    {y : GL (Fin 8) (ZMod 2)} (hy : y ∈ s8)
    (hyw : (y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w = p ∨
      (y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w = p + w) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs8 : Nat.card s8 = 40320 := card_s8
  have hsyl : ∀ K : Subgroup (GL (Fin 8) (ZMod 2)), K ≤ s8 → Nat.card K = 128 →
      IsPGroup 2 (K.subgroupOf s8) ∧ ¬ 2 ∣ (K.subgroupOf s8).index := by
    intro K hK hK128
    have hc : Nat.card (K.subgroupOf s8) = 128 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv]
      exact hK128
    refine ⟨IsPGroup.of_card (n := 7) (by rw [hc]; norm_num), ?_⟩
    have h1 := (K.subgroupOf s8).card_mul_index
    rw [hc, hs8] at h1
    have h2 : (K.subgroupOf s8).index = 315 := by omega
    rw [h2]
    decide
  obtain ⟨h1p, h1i⟩ := hsyl T' hT's8 hT'
  obtain ⟨h2p, h2i⟩ := hsyl T1 T1_le_s8 card_T1
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥s8) (h1p.toSylow h1i) (h2p.toSylow h2i)
  have hg' : ∀ t ∈ T1, ∃ t' ∈ T',
      t = (g : GL (Fin 8) (ZMod 2)) * t' * (g : GL (Fin 8) (ZMod 2))⁻¹ := by
    intro t ht
    have ht' : (⟨t, T1_le_s8 ht⟩ : ↥s8) ∈ ((h2p.toSylow h2i : Sylow 2 ↥s8) : Subgroup ↥s8) := ht
    rw [← hg, Sylow.coe_subgroup_smul] at ht'
    obtain ⟨t₀, ht₀, he⟩ := ht'
    refine ⟨(t₀ : GL (Fin 8) (ZMod 2)), ht₀, ?_⟩
    have := congrArg Subtype.val he
    simpa [MulAut.conj_apply] using this.symm
  set G8 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
    ((g : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) with hG8
  have hconj : ∀ t' : GL (Fin 8) (ZMod 2), ∀ v,
      (((g : GL (Fin 8) (ZMod 2)) * t' * (g : GL (Fin 8) (ZMod 2))⁻¹ : GL (Fin 8) (ZMod 2)) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (G8.mulVec v) =
        G8.mulVec ((t' : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) := by
    intro t' v
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hG8,
      Matrix.mulVec_mulVec (v := v), ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hinj : Function.Injective G8.mulVec := by
    intro u v huv
    have := congrArg (((g : GL (Fin 8) (ZMod 2))⁻¹ : GL (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec huv
    rwa [hG8, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mulVec, Matrix.one_mulVec] at this
  have hw1 : G8.mulVec w = vec8 vR := by
    refine eq_vR_of_fix (fun t ht => ?_) fun h => hw0 (hinj (h.trans (Matrix.mulVec_zero _).symm))
    obtain ⟨t', ht', rfl⟩ := hg' t ht
    rw [hconj, hTw t' ht']
  have hplane : ∀ q : Fin 8 → ZMod 2, q ≠ 0 → q ≠ w →
      (∀ t ∈ T', (t : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec q = q ∨
        (t : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec q = q + w) →
      inII (code8 (G8.mulVec q)) = true := by
    intro q hq0 hqw hTq
    refine inII_of_plane (fun h => hq0 (hinj (h.trans (Matrix.mulVec_zero _).symm)))
      (fun h => hqw (hinj (h.trans hw1.symm))) fun t ht => ?_
    obtain ⟨t', ht', rfl⟩ := hg' t ht
    rw [hconj, ← hw1, ← Matrix.mulVec_add]
    rcases hTq t' ht' with h | h
    · left; rw [h]
    · right; rw [h]
  have hpw' : p + w ≠ 0 := fun h => hpw (by
    have := congrArg (· + w) h
    simpa [add_assoc, add_self8] using this)
  have hpw'' : p + w ≠ w := fun h => hp0 (by simpa using h)
  have hTp' : ∀ t ∈ T', (t : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (p + w) = p + w ∨
      (t : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (p + w) = (p + w) + w := by
    intro t ht
    rw [Matrix.mulVec_add, hTw t ht]
    rcases hTp t ht with h | h
    · left; rw [h]
    · right
      rw [h]
  set y₁ : GL (Fin 8) (ZMod 2) := (g : GL (Fin 8) (ZMod 2)) * y * (g : GL (Fin 8) (ZMod 2))⁻¹
  have hy₁ : y₁ ∈ s8 := mul_mem (mul_mem g.2 hy) (inv_mem g.2)
  have hII := inII_s8 hy₁ (vec8 vR)
  rw [← hw1, hconj] at hII
  have hvR : inII (code8 (vec8 vR)) = false := by
    rw [code8_vec8 (by decide)]
    decide
  rw [hw1, hvR] at hII
  rcases hyw with h | h
  · rw [h, hplane p hp0 hpw hTp] at hII
    exact absurd hII (by decide)
  · rw [h, hplane (p + w) hpw' hpw'' hTp'] at hII
    exact absurd hII (by decide)

end CFSG.Quasithin.H13.S8Tr
