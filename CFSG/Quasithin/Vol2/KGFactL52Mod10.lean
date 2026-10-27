module

public import CFSG.Quasithin.Vol2.KGFactC31EBasis
public import CFSG.RankThree.SteinbergR3EHigherLinearOuterOrder
public import CFSG.RankThree.PartOne.S11b.Sec109SylowTransport
public import CFSG.LieType.SteinbergBROddSylowCore
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.Ch4

open Matrix
open CFSG.Open CFSG.Quasithin CFSG.Quasithin.KGC31
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def singerMat : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 0, 0, 0, 1; 1, 0, 0, 0, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0]

@[expose] def singerInvMat : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 1, 0, 0, 0; 1, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1; 1, 0, 0, 0, 0]

theorem singerMat_mul_singerInvMat : singerMat * singerInvMat = 1 := by decide +kernel

theorem det_singerMat : singerMat.det = 1 := by
  have h := congrArg Matrix.det singerMat_mul_singerInvMat
  rw [Matrix.det_mul, Matrix.det_one] at h
  generalize singerMat.det = a at h
  generalize singerInvMat.det = b at h
  revert a b
  decide

@[expose] def singer5 : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) := ⟨singerMat, det_singerMat⟩

@[expose] def sg2 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 0, 0, 1, 0; 0, 0, 0, 0, 1; 1, 0, 0, 1, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0]

@[expose] def sg4 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 1, 0, 1, 1; 0, 0, 1, 0, 1; 1, 0, 0, 1, 0]

@[expose] def sg8 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 1, 1, 0; 0, 1, 0, 1, 1; 1, 0, 0, 1, 1; 1, 1, 0, 0, 1; 0, 1, 1, 0, 0]

@[expose] def sg16 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 1, 1, 0, 0; 1, 1, 1, 1, 0; 0, 0, 0, 1, 1; 1, 0, 0, 0, 1; 1, 1, 0, 0, 0]

theorem singerMat_sq : singerMat * singerMat = sg2 := by decide +kernel

theorem sg2_sq : sg2 * sg2 = sg4 := by decide +kernel

theorem sg4_sq : sg4 * sg4 = sg8 := by decide +kernel

theorem sg8_sq : sg8 * sg8 = sg16 := by decide +kernel

theorem sg_31 : sg16 * sg8 * sg4 * sg2 * singerMat = 1 := by decide +kernel

theorem singerMat_ne_one : singerMat ≠ 1 := by decide +kernel

theorem singerMat_pow_31 : singerMat ^ 31 = 1 := by
  have h2 : singerMat ^ 2 = sg2 := by rw [pow_two, singerMat_sq]
  have h4 : singerMat ^ 4 = sg4 := by rw [show 4 = 2 * 2 from rfl, pow_mul, h2, pow_two, sg2_sq]
  have h8 : singerMat ^ 8 = sg8 := by rw [show 8 = 4 * 2 from rfl, pow_mul, h4, pow_two, sg4_sq]
  have h16 : singerMat ^ 16 = sg16 := by
    rw [show 16 = 8 * 2 from rfl, pow_mul, h8, pow_two, sg8_sq]
  rw [show 31 = 16 + 8 + 4 + 2 + 1 from rfl, pow_add, pow_add, pow_add, pow_add, pow_one, h16, h8,
    h4, h2, sg_31]

theorem orderOf_singer5 : orderOf singer5 = 31 := by
  have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  refine orderOf_eq_prime (Subtype.ext ?_) fun h => singerMat_ne_one ?_
  · rw [Matrix.SpecialLinearGroup.coe_pow]
    exact singerMat_pow_31
  · exact congrArg Subtype.val h

theorem coe_singer5 : (singer5 : Matrix (Fin 5) (Fin 5) (ZMod 2)) = singerMat := rfl

theorem coe_singer5_inv : ((singer5⁻¹ : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    Matrix (Fin 5) (Fin 5) (ZMod 2)) = singerInvMat := by
  have h1 : ((singer5⁻¹ : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) * singerMat = 1 := by
    rw [← coe_singer5, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  calc ((singer5⁻¹ : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))
      = ((singer5⁻¹ : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
          Matrix (Fin 5) (Fin 5) (ZMod 2)) * (singerMat * singerInvMat) := by
        rw [singerMat_mul_singerInvMat, Matrix.mul_one]
    _ = singerInvMat := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

@[expose] def pSinger (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  A ^ 5 + A ^ 2 + 1

theorem pSinger_singerMat : pSinger singerMat = 0 := by
  have h2' : singerMat ^ 2 = sg2 := by rw [pow_two, singerMat_sq]
  have h4 : singerMat ^ 4 = sg4 := by rw [show 4 = 2 * 2 from rfl, pow_mul, h2', pow_two, sg2_sq]
  have h5 : singerMat ^ 5 = sg4 * singerMat := by rw [pow_succ, h4]
  have h2 : singerMat ^ 2 = sg2 := by rw [pow_two, singerMat_sq]
  rw [pSinger, h5, h2]
  decide +kernel

theorem pSinger_singerInvMat_ne : pSinger singerInvMat ≠ 0 := by
  have h4 : singerInvMat ^ 4 = (singerInvMat * singerInvMat) * (singerInvMat * singerInvMat) := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, pow_two, pow_two]
  have h5 : singerInvMat ^ 5 = (singerInvMat * singerInvMat) * (singerInvMat * singerInvMat) *
      singerInvMat := by
    rw [pow_succ, h4]
  rw [pSinger, h5, pow_two]
  decide +kernel

theorem pSinger_conj (k A : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    pSinger ((k * A * k⁻¹ : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      (k : Matrix (Fin 5) (Fin 5) (ZMod 2)) * pSinger (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
        ((k⁻¹ : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) := by
  have hpow : ∀ m : ℕ, ((k * A * k⁻¹ : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) ^ m = (k : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
        (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) ^ m *
        ((k⁻¹ : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) := by
    intro m
    rw [← Matrix.SpecialLinearGroup.coe_pow, conj_pow, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow]
  have hk : (k : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
      ((k⁻¹ : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [pSinger, pSinger, hpow, hpow, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul,
    Matrix.mul_one, hk]

theorem pSinger_transpose (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) :
    pSinger Aᵀ = (pSinger A)ᵀ := by
  rw [pSinger, pSinger, Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_pow,
    Matrix.transpose_pow, Matrix.transpose_one]

theorem transpose_transpose_sl (A : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    A.transpose.transpose = A :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_transpose,
      Matrix.transpose_transpose])

theorem inv_transpose_sl (A : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    (A.transpose)⁻¹ = (A⁻¹).transpose := by
  symm
  apply eq_inv_of_mul_eq_one_left
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose,
    Matrix.SpecialLinearGroup.coe_transpose, ← Matrix.transpose_mul,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
    Matrix.transpose_one]

@[expose] def gammaSL : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) ≃*
    Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) where
  toFun A := (A⁻¹).transpose
  invFun A := (A⁻¹).transpose
  left_inv A := by
    show ((A⁻¹).transpose⁻¹).transpose = A
    rw [inv_transpose_sl, inv_inv, transpose_transpose_sl]
  right_inv A := by
    show ((A⁻¹).transpose⁻¹).transpose = A
    rw [inv_transpose_sl, inv_inv, transpose_transpose_sl]
  map_mul' A B := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_transpose, _root_.mul_inv_rev,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]

theorem coe_gammaSL (A : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    ((gammaSL A : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ :=
  Matrix.SpecialLinearGroup.coe_transpose _

theorem gammaSL_not_inner (k : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    ¬ ∀ A, gammaSL A = k * A * k⁻¹ := by
  intro hk
  apply pSinger_singerInvMat_ne
  have h1 : pSinger ((gammaSL singer5 : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) = 0 := by
    rw [hk, pSinger_conj, coe_singer5, pSinger_singerMat, Matrix.mul_zero, Matrix.zero_mul]
  rw [coe_gammaSL, coe_singer5_inv, pSinger_transpose] at h1
  exact Matrix.transpose_eq_zero.mp h1

@[expose] def k0Mat : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 0, 0, 0, 1; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 1; 1, 0, 0, 1, 0]

@[expose] def k0InvMat : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 1, 0, 0, 1; 1, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 1, 0, 0, 0, 0]

theorem k0Mat_mul_k0InvMat : k0Mat * k0InvMat = 1 := by decide +kernel

theorem k0Mat_conj : k0Mat * singerInvMat = singerInvMatᵀ * k0Mat := by decide +kernel

theorem det_k0Mat : k0Mat.det = 1 := by
  have h := congrArg Matrix.det k0Mat_mul_k0InvMat
  rw [Matrix.det_mul, Matrix.det_one] at h
  generalize k0Mat.det = a at h
  generalize k0InvMat.det = b at h
  revert a b
  decide

@[expose] def k0 : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) := ⟨k0Mat, det_k0Mat⟩

theorem gammaSL_singer5 : gammaSL singer5 = k0 * singer5⁻¹ * k0⁻¹ := by
  apply Subtype.ext
  rw [coe_gammaSL, coe_singer5_inv, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, coe_singer5_inv]
  have hk : (k0 : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
      ((k0⁻¹ : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  calc singerInvMatᵀ = singerInvMatᵀ * ((k0 : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
        ((k0⁻¹ : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
          Matrix (Fin 5) (Fin 5) (ZMod 2))) := by rw [hk, Matrix.mul_one]
    _ = (singerInvMatᵀ * k0Mat) * ((k0⁻¹ : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
          Matrix (Fin 5) (Fin 5) (ZMod 2)) := by rw [Matrix.mul_assoc]; rfl
    _ = k0Mat * singerInvMat * ((k0⁻¹ : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
          Matrix (Fin 5) (Fin 5) (ZMod 2)) := by rw [k0Mat_conj]
    _ = _ := rfl

section Basis

variable {G : Type} [Group G]

theorem eElt_single_ofAdd {n : ℕ} (c : Fin n → ZMod 2) :
    eElt (fun i => Multiplicative.ofAdd (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2)) c =
      Multiplicative.ofAdd c := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_ofAdd, eElt, toAdd_list_sum, List.map_ofFn, List.sum_ofFn]
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j (fun b _ hbj => by
      simp [Function.comp_apply, Ne.symm hbj]) (by simp)]
  simp [Function.comp_apply]

theorem exists_eBasis_of_isE2 {n : ℕ} {V : Subgroup G} (hV : IsE2 n ↥V) :
    ∃ (v : Fin n → G) (hv : EBasis v), eSub hv = V := by
  obtain ⟨e⟩ := hV
  set f : Multiplicative (Fin n → ZMod 2) →* G := V.subtype.comp e.symm.toMonoidHom with hfdef
  have hf : Function.Injective f := V.subtype_injective.comp e.symm.injective
  set u : Fin n → Multiplicative (Fin n → ZMod 2) :=
    fun i => Multiplicative.ofAdd (Pi.single i 1) with hudef
  have hu : EBasis u := by
    refine ⟨fun i => ?_, fun i j => Commute.all _ _, fun c hc => ?_⟩
    · show Multiplicative.ofAdd (Pi.single i (1 : ZMod 2) + Pi.single i 1 : Fin n → ZMod 2) = 1
      rw [← Pi.single_add, show (1 : ZMod 2) + 1 = 0 from rfl, Pi.single_zero, ofAdd_zero]
    · rw [hudef, eElt_single_ofAdd] at hc
      exact Multiplicative.ofAdd.injective hc
  refine ⟨fun i => f (u i), hu.map hf, ?_⟩
  rw [← eSub_map hu hf]
  have htop : eSub hu = ⊤ := eq_top_iff.mpr fun x _ =>
    (mem_eSub_iff hu x).mpr ⟨Multiplicative.toAdd x, by rw [hudef, eElt_single_ofAdd]; rfl⟩
  rw [htop]
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    exact (e.symm y).2
  · intro hx
    exact ⟨e ⟨x, hx⟩, Subgroup.mem_top _, by simp [hfdef]⟩

end Basis

theorem mul_inv_mem_of_card_dvd_two {Γ : Type*} [Group Γ] {N : Subgroup Γ} [N.Normal]
    (h : Nat.card (Γ ⧸ N) ∣ 2) {a b : Γ} (ha : a ∉ N) (hb : b ∉ N) : a * b⁻¹ ∈ N := by
  by_contra hab
  have hne : Nat.card (Γ ⧸ N) ≠ 0 := fun h0 => by rw [h0] at h; norm_num at h
  have : Finite (Γ ⧸ N) := Nat.finite_of_card_ne_zero hne
  have h1 : (a : Γ ⧸ N) ≠ 1 := fun h' => ha ((QuotientGroup.eq_one_iff a).mp h')
  have h2 : (b : Γ ⧸ N) ≠ 1 := fun h' => hb ((QuotientGroup.eq_one_iff b).mp h')
  have h3 : (a : Γ ⧸ N) ≠ (b : Γ ⧸ N) := fun h' => hab ((QuotientGroup.eq_one_iff _).mp (by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h', mul_inv_cancel]))
  have hinj : Function.Injective (![1, (a : Γ ⧸ N), (b : Γ ⧸ N)] : Fin 3 → Γ ⧸ N) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have h4 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_fin] at h4
  have h5 := Nat.le_of_dvd (by norm_num) h
  omega

@[expose] def SingerNoConj (G : Type) [Group G] (L V : Subgroup G) : Prop :=
  ∀ (v : Fin 10 → G) (hv : EBasis v), eSub hv = V → ∀ (hLE : L ≤ eNorm hv)
    (e : ModO2 L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) (y : ↥L),
    (y : ModO2 L) = e.symm singer5 → ∀ U : GL (Fin 10) (ZMod 2),
      eGL hv (Subgroup.inclusion hLE y) ≠ U * eGL hv (Subgroup.inclusion hLE y⁻¹) * U⁻¹

section Main

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_pCore_iff_mem_pCoreOf {L : Subgroup G} (x : ↥L) :
    x ∈ CFSG.pCore 2 ↥L ↔ (x : G) ∈ pCoreOf 2 L := (CFSG.mem_openPCoreOf_iff x).symm

@[expose] noncomputable def conjL {L : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (L : Set G)) : ↥L ≃* ↥L where
  toFun x := ⟨t * x * t⁻¹, (Subgroup.mem_normalizer_iff.mp ht x).mp x.2⟩
  invFun x := ⟨t⁻¹ * x * t, by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht) x).mp x.2
    simpa using this⟩
  left_inv x := Subtype.ext (by simp only; group)
  right_inv x := Subtype.ext (by simp only; group)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

omit [Finite G] in
theorem coe_conjL {L : Subgroup G} {t : G} (ht : t ∈ Subgroup.normalizer (L : Set G)) (x : ↥L) :
    ((conjL ht x : ↥L) : G) = t * x * t⁻¹ := rfl

omit [Finite G] in
theorem j4L5BlockInner_of_noConj {L V : Subgroup G} (hPSL : IsPSL 5 2 1 (ModO2 L))
    (hVE : IsE2 10 ↥V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hC : L ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 L) (hNC : SingerNoConj G L V)
    {t : G} (htL : t ∈ Subgroup.normalizer (L : Set G))
    (htV : t ∈ Subgroup.normalizer (V : Set G)) :
    ∃ l ∈ L, ∀ y ∈ L, t * l * y * (t * l)⁻¹ * y⁻¹ ∈ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hv, hvV⟩ := exists_eBasis_of_isE2 hVE
  have hNV : Subgroup.normalizer (V : Set G) = eNorm hv := by rw [← hvV]
  have hLE : L ≤ eNorm hv := hNV ▸ hLV
  have htE : t ∈ eNorm hv := hNV ▸ htV
  set ρL : ↥L →* GL (Fin 10) (ZMod 2) := (eGL hv).comp (Subgroup.inclusion hLE) with hρL
  have hρL_coe : ∀ x : ↥L, ((ρL x : GL (Fin 10) (ZMod 2)) : Matrix (Fin 10) (Fin 10) (ZMod 2)) =
      eMat hv (Subgroup.inclusion hLE x) := fun x => rfl
  have hρL_one : ∀ x : ↥L, ρL x = 1 ↔ (x : G) ∈ pCoreOf 2 L := by
    intro x
    rw [← Units.val_eq_one, hρL_coe, eMat_eq_one_iff, hvV, ← hC]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hker : CFSG.pCore 2 ↥L ≤ ρL.ker := fun x hx =>
    (hρL_one x).mpr ((mem_pCore_iff_mem_pCoreOf x).mp hx)
  set ρbar : ModO2 L →* GL (Fin 10) (ZMod 2) := QuotientGroup.lift (CFSG.pCore 2 ↥L) ρL hker
    with hρbar
  have hρbar_mk : ∀ x : ↥L, ρbar (x : ModO2 L) = ρL x := fun x => QuotientGroup.lift_mk _ _ _
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.Sec109.exists_mulEquiv_sl_two hPSL
  set ρ : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) →* GL (Fin 10) (ZMod 2) :=
    ρbar.comp e.symm.toMonoidHom with hρ
  have hρ_apply : ∀ x, ρ x = ρbar (e.symm x) := fun x => rfl
  have hchar : (CFSG.pCore 2 ↥L).map (conjL htL).toMonoidHom = CFSG.pCore 2 ↥L :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance (conjL htL)
  set α : ModO2 L ≃* ModO2 L :=
    QuotientGroup.congr (CFSG.pCore 2 ↥L) (CFSG.pCore 2 ↥L) (conjL htL) hchar with hαdef
  have hα_mk : ∀ x : ↥L, α (x : ModO2 L) = ((conjL htL x : ↥L) : ModO2 L) := fun x =>
    QuotientGroup.congr_mk _ _ _ _ x
  set T : GL (Fin 10) (ZMod 2) := eGL hv ⟨t, htE⟩ with hT
  have hρα : ∀ y : ModO2 L, ρbar (α y) = T * ρbar y * T⁻¹ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hα_mk, hρbar_mk, hρbar_mk, hT]
    show eGL hv (Subgroup.inclusion hLE (conjL htL x)) =
      eGL hv ⟨t, htE⟩ * eGL hv (Subgroup.inclusion hLE x) * (eGL hv ⟨t, htE⟩)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hOut : Nat.card (Outer (ModO2 L)) ∣ 2 := by
    have hK : Nat.card (ZMod 2) = 2 := by simp
    have h1 := CFSG.RankThree.Automorphisms.higher_linear_outer_order_divides_field_scalar_bound
      (K := ZMod 2) (ℓ := 2) (f := 1) (n := 5) Nat.prime_two le_rfl (by norm_num)
      (by rw [hK, pow_one])
    norm_num at h1
    rw [CFSG.LieType.SteinbergBR.OddSylow.card_outer_congr
      (e.trans (CFSG.RankThree.PartOne.Sec109.projectiveSLEquivSL_two hK (by norm_num)))]
    exact h1
  set γ' : MulAut (ModO2 L) := MulAut.congr e.symm gammaSL with hγ'
  have hγ'_apply : ∀ y, γ' y = e.symm (gammaSL (e y)) := fun y => rfl
  have hγ'_out : γ' ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (ModO2 L) := by
    rintro ⟨h, hh⟩
    apply gammaSL_not_inner (e h)
    intro A
    have h1 := congrArg (fun φ : MulAut (ModO2 L) => e (φ (e.symm A))) hh
    simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply, hγ'_apply] at h1
    exact h1.symm
  have hα_in : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (ModO2 L) := by
    by_contra hα_out
    have hαγ := mul_inv_mem_of_card_dvd_two hOut hα_out hγ'_out
    obtain ⟨h, hh⟩ := hαγ
    have hαeq : ∀ y, α y = h * γ' y * h⁻¹ := by
      intro y
      have h1 := congrArg (fun φ : MulAut (ModO2 L) => φ (γ' y)) hh
      simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply] at h1
      rw [MulEquiv.symm_apply_apply] at h1
      exact h1.symm
    have h1 := hρα (e.symm singer5)
    rw [hαeq, hγ'_apply, MulEquiv.apply_symm_apply, gammaSL_singer5] at h1
    simp only [map_mul, map_inv] at h1
    set U : GL (Fin 10) (ZMod 2) := T⁻¹ * ρbar h * ρ k0 with hU
    have h2 : ρ singer5 = U * ρ singer5⁻¹ * U⁻¹ := by
      rw [hρ_apply, hρ_apply, hU, hρ_apply]
      simp only [map_inv]
      calc ρbar (e.symm singer5) = T⁻¹ * (T * ρbar (e.symm singer5) * T⁻¹) * T := by group
        _ = _ := by rw [← h1]; group
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (e.symm singer5)
    apply hNC v hv hvV hLE e y hy U
    have hy1 : ρ singer5 = eGL hv (Subgroup.inclusion hLE y) := by
      rw [hρ_apply, ← hy, hρbar_mk]; rfl
    have hy2 : ρ singer5⁻¹ = eGL hv (Subgroup.inclusion hLE y⁻¹) := by
      rw [hρ_apply, map_inv, ← hy, ← QuotientGroup.mk_inv, hρbar_mk]; rfl
    rw [← hy1, ← hy2]
    exact h2
  obtain ⟨lbar, hlbar⟩ := hα_in
  obtain ⟨l₀, rfl⟩ := QuotientGroup.mk_surjective lbar
  refine ⟨((l₀⁻¹ : ↥L) : G), (l₀⁻¹).2, fun y hy => ?_⟩
  set y' : ↥L := l₀⁻¹ * ⟨y, hy⟩ * l₀ with hy'
  have h1 : α (y' : ModO2 L) = ((⟨y, hy⟩ : ↥L) : ModO2 L) := by
    rw [← hlbar, MulAut.conj_apply, hy', QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv]
    group
  rw [hα_mk] at h1
  have h2 : (conjL htL y' * (⟨y, hy⟩ : ↥L)⁻¹ : ↥L) ∈ CFSG.pCore 2 ↥L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, h1, QuotientGroup.mk_inv,
      mul_inv_cancel]
  rw [mem_pCore_iff_mem_pCoreOf] at h2
  convert h2 using 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjL, hy']
  group

end Main

end CFSG.Quasithin.H13.Ch4
