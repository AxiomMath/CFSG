module

public import CFSG.Quasithin.EmptyFaithful.R3c18D
import CFSG.RankThree.PartTwo.KFacts.AutPSUScalar
public import CFSG.RankThree.PartTwo.KFacts.AutPSUOrderThree

public section

namespace CFSG.Quasithin

namespace R3c18

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedSU StatedProj StatedScalars)
open scoped MatrixGroups

variable {f : ℕ} {K : Type} [Field K]

@[expose] def normOneGp (_h : UnitaryFieldData 2 f K) : Subgroup Kˣ :=
  (powMonoidHom (2 ^ f + 1) : Kˣ →* Kˣ).ker

theorem mem_normOneGp {h : UnitaryFieldData 2 f K} {x : Kˣ} :
    x ∈ normOneGp h ↔ x ^ (2 ^ f + 1) = 1 := Iff.rfl

theorem norm_eq_pow {h : UnitaryFieldData 2 f K} (c : K) : h.norm c = c ^ (2 ^ f + 1) := by
  rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, pow_succ']

theorem mem_normOneGp_iff_norm {h : UnitaryFieldData 2 f K} {x : Kˣ} :
    x ∈ normOneGp h ↔ h.norm (x : K) = 1 := by
  rw [mem_normOneGp, norm_eq_pow, ← Units.val_pow_eq_pow_val, ← Units.val_one (α := K),
    Units.val_inj]

theorem det_mem_normOneGp {h : UnitaryFieldData 2 f K} (A : unitaryIsom3 h) :
    GeneralLinearGroup.det (A : GL (Fin 3) K) ∈ normOneGp h := by
  rw [mem_normOneGp_iff_norm, GeneralLinearGroup.val_det_apply]
  have hdet := congrArg Matrix.det (mem_unitaryIsom3.mp A.2)
  rw [Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    Matrix.det_one] at hdet
  rw [UnitaryFieldData.norm, mul_comm]
  exact hdet

theorem scalar_mem_unitaryIsom3 {h : UnitaryFieldData 2 f K} {w : Kˣ} (hw : w ∈ normOneGp h) :
    GeneralLinearGroup.scalar (Fin 3) w ∈ unitaryIsom3 h :=
  CFSG.RankThree.PartTwo.KFacts.scalar_mem_unitaryIsom3_of_norm (mem_normOneGp_iff_norm.1 hw)

section Norm

variable {h : UnitaryFieldData 2 f K}

@[expose] noncomputable def normU (σ : K ≃+* K) (A : unitaryIsom3 h) : ℕ → unitaryIsom3 h
  | 0 => 1
  | n + 1 => normU σ A n * ⟨glAut (σ ^ n) (A : GL (Fin 3) K), glAut_mem_unitaryIsom3 (σ ^ n) A.2⟩

theorem pow_psuConj_mul_psuField (σ : K ≃+* K) (A : unitaryIsom3 h) (n : ℕ) :
    (psuConj h A * psuField h σ) ^ n = psuConj h (normU σ A n) * psuField h (σ ^ n) := by
  induction n with
  | zero => simp [normU]
  | succ m ih => rw [pow_succ, ih, normU, psuConj_mul_psuField_mul, ← pow_succ]

theorem det_glAut (σ : K ≃+* K) (g : GL (Fin 3) K) :
    GeneralLinearGroup.det (glAut σ g) =
      Units.map (σ : K →* K) (GeneralLinearGroup.det g) := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, coe_glAut, Units.coe_map, GeneralLinearGroup.val_det_apply]
  exact (RingHom.map_det σ.toRingHom _).symm

theorem det_normU (σ : K ≃+* K) (A : unitaryIsom3 h) (n : ℕ) :
    GeneralLinearGroup.det ((normU σ A n : unitaryIsom3 h) : GL (Fin 3) K) =
      ∏ i ∈ Finset.range n, Units.map ((σ ^ i : K ≃+* K).toRingHom : K →* K)
        (GeneralLinearGroup.det (A : GL (Fin 3) K)) := by
  induction n with
  | zero => simp [normU]
  | succ m ih =>
    rw [normU, Subgroup.coe_mul, map_mul, ih, Finset.prod_range_succ]
    congr 1
    exact det_glAut (σ ^ m) _

theorem psuConj_mem_inner_of_det (C : unitaryIsom3 h) {y : Kˣ} (hy : y ∈ normOneGp h)
    (hC : GeneralLinearGroup.det (C : GL (Fin 3) K) = y ^ 3) :
    psuConj h C ∈ inner (unitaryPSU h 3) := by
  have hyI := scalar_mem_unitaryIsom3 hy
  obtain ⟨Y, hY⟩ : ∃ Y : unitaryIsom3 h, (Y : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) y :=
    ⟨⟨_, hyI⟩, rfl⟩
  obtain ⟨C', hC'⟩ : ∃ C' : unitaryIsom3 h, C' = Y⁻¹ * C := ⟨_, rfl⟩
  have hdet : ((C' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, hC', Subgroup.coe_mul, Subgroup.coe_inv, map_mul,
      map_inv, hY, GeneralLinearGroup.det_scalar, Fintype.card_fin, hC, inv_mul_cancel,
      Units.val_one]
  have hC'SU : (C' : GL (Fin 3) K) ∈ unitarySU 2 f K 3 := (mem_unitarySU_iff h).mpr ⟨hdet, C'.2⟩
  have hY1 : psuConj h Y = 1 := by
    have hYe : Y = ⟨_, hyI⟩ := Subtype.ext hY
    rw [hYe]
    exact psuConj_scalar hyI
  have hCY : C = Y * C' := by rw [hC', mul_inv_cancel_left]
  refine ⟨((⟨C', hC'SU⟩ : unitarySU 2 f K 3) : unitaryPSU h 3), ?_⟩
  calc MulAut.conj ((⟨C', hC'SU⟩ : unitarySU 2 f K 3) : unitaryPSU h 3) = psuConj h C' := by
        rw [conj_mk_eq_psuConj]
    _ = psuConj h C := by rw [hCY, map_mul, hY1, one_mul]

end Norm

section Cube

variable [Finite K] [CharP K 2] {h : UnitaryFieldData 2 f K}

theorem psuConj_mem_inner_of_pow_eq_one {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {A : unitaryIsom3 h} {σ : K ≃+* K} (hpow : (psuConj h A * psuField h σ) ^ (p ^ k) = 1) :
    psuConj h A ∈ inner (unitaryPSU h 3) := by
  rw [pow_psuConj_mul_psuField] at hpow
  obtain ⟨hσ, c, hc, hcA⟩ := eq_one_of_psuConj_mul_psuField_eq_one _ _ hpow
  obtain ⟨j, hj⟩ := exists_frob_pow σ
  set t : ℕ := 2 ^ j with ht
  have ht3 : ¬ 3 ∣ t := fun h3 => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hn : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  have hn3 : ¬ 3 ∣ p ^ k := fun h3 => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 this).symm
  have hcN : c ∈ normOneGp h := mem_normOneGp_iff_norm.2 hc
  set a : normOneGp h := ⟨GeneralLinearGroup.det (A : GL (Fin 3) K), det_mem_normOneGp A⟩ with ha
  have hpowG : ∀ x : normOneGp h, x ^ (t ^ (p ^ k)) = x := fun x => Subtype.ext (Units.ext (by
    have h1 := pow_iter_frob σ hj (p ^ k) (x : Kˣ)
    rw [hσ] at h1
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    exact h1.symm))
  obtain ⟨b, hb⟩ := isCube_of_prod_pow hn hn3 ht3 hpowG a ⟨⟨c, hcN⟩, by
    apply Subtype.ext
    have hprod := map_prod (normOneGp h).subtype (fun i => a ^ t ^ i) (Finset.range (p ^ k))
    simp only [Subgroup.coe_subtype, Subgroup.coe_pow] at hprod
    rw [Subgroup.coe_pow, hprod]
    have h1 : ∀ i ∈ Finset.range (p ^ k), ((a : Kˣ) ^ (t ^ i)) =
        Units.map ((σ ^ i : K ≃+* K).toRingHom : K →* K)
          (GeneralLinearGroup.det (A : GL (Fin 3) K)) := fun i _ =>
      Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.coe_map]
        exact (pow_iter_frob σ hj i _).symm)
    rw [Finset.prod_congr rfl h1, ← det_normU, hcA, GeneralLinearGroup.det_scalar,
      Fintype.card_fin]⟩
  refine psuConj_mem_inner_of_det A b.2 ?_
  have := congrArg Subtype.val hb
  simpa [ha] using this.symm

end Cube

@[expose] def U3PRankShape : Prop :=
  ∀ (K : Type) [Field K] [Finite K] {p q : ℕ}, p.Prime → p ≠ 2 → Nat.card K = q ^ 2 → ¬ p ∣ q →
    3 / orderOf (-(q : ZMod p)) ≤ 1 → CFSG.pRank p ↥(StatedSU 3 q K) ≤ 1

section Sylow

variable [Finite K] {h : UnitaryFieldData 2 f K}

theorem dvd_succ_of_two_le_pRank_u3 (hshape : U3PRankShape) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h2 : 2 ≤ CFSG.pRank p (unitaryPSU h 3)) : p ∣ 2 ^ f + 1 := by
  classical
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hK : Nat.card K = (2 ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hpq : ¬ p ∣ 2 ^ f := fun hd => hp2
    ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  have hN : ¬ p ∣ Nat.card
      ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (2 ^ f) K)) := by
    rw [(CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (by norm_num)).2.2]
    intro hd
    have := Nat.le_of_dvd (by norm_num) (hd.trans (Nat.gcd_dvd_left 3 _))
    omega
  have h3 : 2 ≤ CFSG.pRank p ↥(StatedSU 3 (2 ^ f) K) := by
    rw [← CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp _ hN,
      ← pRank_congr hp.one_lt (unitaryPSUEquiv h (by norm_num : 1 ≤ 3))]
    exact h2
  by_contra hnd
  have hQ0 : (-((2 ^ f : ℕ) : ZMod p)) ≠ 0 := by
    rw [neg_ne_zero, Ne, ZMod.natCast_eq_zero_iff]
    exact hpq
  set e := orderOf (-((2 ^ f : ℕ) : ZMod p)) with he
  have he0 : 0 < e := orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
    ⟨p - 1, by have := hp.two_le; omega, by
      have := ZMod.pow_card_sub_one_eq_one hQ0
      exact this⟩)
  have he1 : e ≠ 1 := fun h1 => hnd (by
    have : (-((2 ^ f : ℕ) : ZMod p)) = 1 := orderOf_eq_one_iff.1 h1
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast at this ⊢
    linear_combination -this)
  have hcond : 3 / e ≤ 1 :=
    Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul he0).2 (by omega))
  have := hshape K hp hp2 hK hpq hcond
  omega

end Sylow

section Torus

variable {h : UnitaryFieldData 2 f K}

theorem bar_mul_self_of_mem {x : Kˣ} (hx : x ∈ normOneGp h) : h.bar (x : K) * (x : K) = 1 := by
  rw [mul_comm]
  exact mem_normOneGp_iff_norm.1 hx

theorem toGL_diagHom_mem {a b : Kˣ} (ha : a ∈ normOneGp h) (hb : b ∈ normOneGp h) :
    Matrix.SpecialLinearGroup.toGL (diagHom (a, b)) ∈ unitarySU 2 f K 3 := by
  rw [mem_unitarySU_iff h]
  refine ⟨(diagHom (a, b)).2, ?_⟩
  have hc : (a * b)⁻¹ ∈ normOneGp h := inv_mem (mul_mem ha hb)
  change ((diagSL (a, b) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
    (diagSL (a, b) : Matrix (Fin 3) (Fin 3) K) = 1
  rw [coe_diagSL, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i
  · exact bar_mul_self_of_mem ha
  · exact bar_mul_self_of_mem hb
  · exact bar_mul_self_of_mem hc

@[expose] noncomputable def diagU (h : UnitaryFieldData 2 f K) :
    normOneGp h × normOneGp h →* unitaryPSU h 3 :=
  (unitaryProj h 3).comp
    (((Matrix.SpecialLinearGroup.toGL : SL(3, K) →* GL (Fin 3) K).comp
      (diagHom.comp ((normOneGp h).subtype.prodMap (normOneGp h).subtype))).codRestrict
        (unitarySU 2 f K 3) fun x => toGL_diagHom_mem x.1.2 x.2.2)

theorem eq_of_diagU_eq_one (x : normOneGp h × normOneGp h) (hx : diagU h x = 1) :
    x.1 = x.2 ∧ x.1 ^ 3 = 1 := by
  have hmem := (QuotientGroup.eq_one_iff _).1 hx
  obtain ⟨c, -, hc3, hc⟩ := mem_unitaryScalars.1 hmem
  have h0 := congrFun (congrFun (congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K))
    hc) 0) 0
  have h1 := congrFun (congrFun (congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K))
    hc) 1) 1
  simp [diagHom, diagSL, Matrix.scalar_apply] at h0 h1
  have e0 : (x.1 : Kˣ) = c := Units.ext h0
  have e1 : (x.2 : Kˣ) = c := Units.ext h1
  refine ⟨Subtype.ext (e0.trans e1.symm), Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, e0, hc3]
  rfl

theorem psuField_diagU {σ : K ≃+* K} (x : normOneGp h × normOneGp h)
    (hx1 : Units.map (σ : K →* K) (x.1 : Kˣ) = x.1) (hx2 : Units.map (σ : K →* K) (x.2 : Kˣ) = x.2) :
    psuField h σ (diagU h x) = diagU h x := by
  change psuField h σ ((⟨_, _⟩ : unitarySU 2 f K 3) : unitaryPSU h 3) = _
  rw [psuField_mk]
  congr 1
  apply Subtype.ext
  rw [coe_suField]
  change glAut σ (Matrix.SpecialLinearGroup.toGL (diagHom ((x.1 : Kˣ), (x.2 : Kˣ)))) =
    Matrix.SpecialLinearGroup.toGL (diagHom ((x.1 : Kˣ), (x.2 : Kˣ)))
  apply Units.ext
  rw [coe_glAut]
  have := congrArg Subtype.val (map_diagHom σ ((x.1 : Kˣ), (x.2 : Kˣ)))
  rw [hx1, hx2] at this
  exact this

end Torus

section ElemAbelian

variable [Finite K] {h : UnitaryFieldData 2 f K}

omit [Finite K] in
theorem exists_sq_u3 (σ : K ≃+* K) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {ζ : normOneGp h}
    (hζ : orderOf ζ = p) (hfix : Units.map (σ : K →* K) (ζ : Kˣ) = ζ) :
    ∃ E : Subgroup (unitaryPSU h 3), Nat.card E = p ^ 2 ∧ CFSG.Open.IsElemAbelian p E ∧
      ∀ y ∈ E, psuField h σ y = y := by
  have hζp : ζ ^ p = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hfix1 : Units.map (σ : K →* K) (1 : Kˣ) = 1 := map_one _
  refine exists_sq_of_pair hp (psuField h σ) (u := diagU h (ζ, 1)) (v := diagU h (1, ζ))
    (psuField_diagU _ hfix (by exact hfix1)) (psuField_diagU _ (by exact hfix1) hfix) ?_ ?_ ?_ ?_
  · rw [← map_mul, ← map_mul]
    congr 1
    ext <;> simp [mul_comm]
  · rw [← map_pow]
    simp [hζp, Prod.mk_one_one]
  · rw [← map_pow]
    simp [hζp, Prod.mk_one_one]
  · intro i j hij
    rw [← map_pow, ← map_pow, ← map_mul] at hij
    obtain ⟨h1, h2⟩ := eq_of_diagU_eq_one _ hij
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.pow_fst, Prod.pow_snd, one_pow, mul_one,
      one_mul] at h1 h2
    have hi : p ∣ i := by
      have : ζ ^ (i * 3) = 1 := by rw [pow_mul, h2]
      have h3 := orderOf_dvd_of_pow_eq_one this
      rw [hζ] at h3
      rcases (Nat.Prime.dvd_mul hp).1 h3 with h | h
      · exact h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h) hp3
    refine ⟨hi, ?_⟩
    have hζi : ζ ^ i = 1 := by
      obtain ⟨m, rfl⟩ := hi
      rw [pow_mul, hζp, one_pow]
    have : ζ ^ j = 1 := by rw [← h1]; exact hζi
    rw [← hζ]
    exact orderOf_dvd_of_pow_eq_one this

end ElemAbelian

theorem dvd_succ_of_dvd_pow_succ {p q : ℕ} (hp : p.Prime) (h : p ∣ q ^ p + 1) : p ∣ q + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_zero_iff] at h ⊢
  push_cast at h ⊢
  rwa [ZMod.pow_card] at h

section Frame

@[expose] noncomputable def pFrameU3 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hshape : U3PRankShape)
    {f : ℕ} (hf : 2 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K) :
    PFrame p (unitaryPSU h 3) (K ≃+* K) where
  fld := psuField h
  fld_inter := fun c hc => psuField_mem_range_psuConj_iff.1 ((stdPinnedPSU3 h).inn_le hc)
  conj_mem := fun α k hα => by
    have hq : 2 < 2 ^ f := by
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    obtain ⟨A, σ, hAσ⟩ := exists_psuConj_mul_psuField hq α
    have hpow : (psuConj h A * psuField h σ) ^ (p ^ k) = 1 := by
      rw [← hAσ, ← hα]
      exact pow_orderOf_eq_one α
    exact ⟨1, psuConj h A, psuConj_mem_inner_of_pow_eq_one hp (by omega) (by omega) hpow, σ,
      by rw [hAσ]; simp⟩
  sq := fun h2 c hc => by
    have hdvd : p ∣ 2 ^ f + 1 := dvd_succ_of_two_le_pRank_u3 hshape hp hp5 h2
    obtain ⟨hpf2, k, hk, hkcard⟩ := exists_fixed_subfield (f := 2 * f) (by omega) h.card c hc
    have hpf : p ∣ f := by
      rcases (Nat.Prime.dvd_mul hp).1 hpf2 with h2' | h2'
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2') (by omega)
      · exact h2'
    obtain ⟨m, hm⟩ := hpf
    have hf0 : 0 < p := hp.pos
    have hkq : Nat.card k = (2 ^ m) ^ 2 := by
      rw [hkcard, ← pow_mul, hm, show 2 * (p * m) = p * (2 * m) by ring, Nat.mul_div_cancel_left _ hf0]
      ring_nf
    have hq : 2 ^ f = (2 ^ m) ^ p := by rw [hm, ← pow_mul, mul_comm]
    have hd1 : p ∣ 2 ^ m + 1 := by
      rw [hq] at hdvd
      exact dvd_succ_of_dvd_pow_succ hp hdvd
    have : Fact p.Prime := ⟨hp⟩
    have hcardU : p ∣ Nat.card kˣ := by
      rw [Nat.card_units, hkq]
      have : (2 ^ m) ^ 2 - 1 = (2 ^ m - 1) * (2 ^ m + 1) := by
        have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
        zify [h1, Nat.one_le_pow 2 (2 ^ m) (by norm_num)]
        ring
      rw [this]
      exact Dvd.dvd.mul_left hd1 _
    obtain ⟨ζ₀, hζ₀⟩ := exists_prime_orderOf_dvd_card' p hcardU
    have hinj : Function.Injective (Units.map (k.subtype : k →+* K).toMonoidHom) :=
      Units.map_injective k.subtype.injective
    set ζ : Kˣ := Units.map (k.subtype : k →+* K).toMonoidHom ζ₀ with hζdef
    have hζo : orderOf ζ = p := by rw [hζdef, orderOf_injective _ hinj ζ₀, hζ₀]
    have hζp : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
    have hζN : ζ ∈ normOneGp h := by
      rw [mem_normOneGp]
      obtain ⟨r, hr⟩ := hdvd
      rw [hr, pow_mul, hζp, one_pow]
    refine exists_sq_u3 c hp (by omega) (ζ := ⟨ζ, hζN⟩)
      ((Subgroup.orderOf_mk _ _).trans hζo) ?_
    apply Units.ext
    change c (ζ₀ : K) = (ζ₀ : K)
    exact hk _ ζ₀.1.2

theorem qLiePRankFam_u3 (hshape : U3PRankShape) :
    QLiePRankFam (fun S _ => ∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel S .PSU 3 2 f) := by
  intro p hp hp5 X _ _ S _ hC _ ⟨f, hf, hm⟩ hS2 hX
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hm
  have hKU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  have := hKU.finite
  have := hKU.charP
  have : Fact p.Prime := ⟨hp⟩
  let e' : ↥S ≃* unitaryPSU hKU 3 := e.trans (unitaryPSUEquiv hKU (by norm_num)).symm
  exact pframe_core hC ((pFrameU3 hp hp5 hshape hf K hKU).ofMulEquiv hp.one_lt e') hS2 hX

end Frame

end R3c18

end CFSG.Quasithin
