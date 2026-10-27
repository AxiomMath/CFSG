module

public import CFSG.Quasithin.Vol2.Ch10SecQ9G30
public import CFSG.Quasithin.Vol2.Ch10SecQ9G27
public import CFSG.Quasithin.Vol2.Ch10SecQ9G29

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I J : Subgroup G} {t w : G}

omit [Finite G] in
theorem conjAct_eq_of_mul_inv_mem {V : Subgroup G} {a b : ↥(Subgroup.normalizer (V : Set G))}
    (h : (a : G) * (b : G)⁻¹ ∈ Subgroup.centralizer (V : Set G)) : conjAct V a = conjAct V b := by
  have h1 : conjAct V (a * b⁻¹) = 1 := (conjAct_eq_one_iff' V (a * b⁻¹)).mpr h
  rw [map_mul, map_inv] at h1
  exact mul_inv_eq_one.mp h1

theorem Conf.false_of_L5_cv (c : Conf T L I t w J)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h1026 : Stmt10_2_6) (h1028 : Stmt10_2_8) (h318 : A318Facts)
    (h36' : A36ForSQTK) (hE : Ch11.SecA.FactA318ExclTwo) (hK7L5 : FactK7L5)
    (hL5I : FactL5Inv) (hVe : IsElemAbelian 2 (VI T L I J w))
    (hq : CFSG.Open.IsQuasisimple ↥(autI hVe J))
    (hCJ : J ⊓ Subgroup.centralizer (VI T L I J w : Set G) = pCoreOf 2 J)
    (eL : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (e : ↥(autI hVe J) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (hcv : fsuCVM T L I ≠ ⊥) : False := by
  have hyp := c.hyp
  have h3 := case3_of hyp h1012 ⟨eL⟩ hcv
  obtain ⟨y, hyLt, hy3, hyw⟩ := Conf.exists_y_of_case3 c h37 h38 h1011 h3
  have hJN : J ≤ Subgroup.normalizer (VI T L I J w : Set G) :=
    le_sup_left.trans (le_normalizer_VI T L I J w)
  obtain ⟨eJ⟩ := nonempty_quotient_equiv hVe hJN hCJ e
  have hyJ : y ∈ J := Conf.mem_J_of_orderOf_three' c h38 h318 h36' hE eJ
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e (isQuasisimple_of_open' hq))
    (center_SL_eq_bot 5) three_dvd_card_SL5 two_le_pRank_SL5 hK7L5 hyw hy3
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := conjugate_le_normalizer hyp c.ht hyLt
  have hyc : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
    intro l hl
    have h1 : ⁅y, l⁆ ∈ ⁅CFSG.conjugate L t, L⁆ := Subgroup.commutator_mem_commutator hyLt hl
    rw [Subgroup.commutator_comm] at h1
    exact (SecA.commutator_conjugate_le h37 hyp c.ht c.htn h1).1
  have hy3' : y ^ 3 = 1 := by have := pow_orderOf_eq_one y; rwa [hy3] at this
  set π := piJ eJ with hπ
  have hR : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({w} : Set G) ⊓ J) J :=
    A4.isSylowTwoOf_inf_normal c.sylow c.J_le
      ((Subgroup.normal_subgroupOf_iff_le_normalizer c.J_le).mp c.normal)
  have hRL : T ⊓ Subgroup.centralizer ({w} : Set G) ⊓ J ≤ Subgroup.normalizer (L : Set G) :=
    inf_le_left.trans ((c.Tw_le_T1 h37 h38).trans inf_le_right)
  have hyX : π ⟨y, hyJ⟩ ∈ Subgroup.normalizer ((piL π c.le).range : Set _) :=
    image_le_normalizer π c.le (R := Subgroup.zpowers y)
      ((Subgroup.zpowers_le (H := Subgroup.normalizer (L : Set G))).mpr hyN)
      ⟨⟨y, hyJ⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers y), rfl⟩
  have hyX3 : orderOf (π ⟨y, hyJ⟩) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ fun h => ?_
    · rw [← map_pow]
      convert map_one π
      exact Subtype.ext hy3'
    · obtain ⟨m, hm⟩ := piJ_ker eJ ⟨y, hyJ⟩ h
      have h1 : y = 1 := eq_one_of_two_pow hm hy3' (by decide)
      rw [h1, orderOf_one] at hy3
      omega
  have hycX : ∀ x ∈ (piL π c.le).range,
      π ⟨y, hyJ⟩ * x * (π ⟨y, hyJ⟩)⁻¹ * x⁻¹ ∈ pCoreOf 2 (piL π c.le).range := by
    rintro _ ⟨l, rfl⟩
    have h1 := image_pCoreOf_le π c.le (hyc l l.2)
    convert h1 using 1
    rw [piL_apply, piL_apply, ← map_inv, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
    rfl
  obtain ⟨_, ⟨r, hr, rfl⟩, k, hk⟩ := hL5I _ _ (image_isSylowTwoOf hR π (piJ_surjective eJ))
    (image_le_normalizer π c.le hRL) (image_perfect π c.le (SecA.perfect_L hyp.fsu.maximal.1))
    (image_quot_equiv π c.le (piJ_ker eJ) eL) _ hyX hyX3 hycX
  have hr' : (r : G) ∈ T ⊓ Subgroup.centralizer ({w} : Set G) ⊓ J := Subgroup.mem_subgroupOf.mp hr
  have hz : ∃ n : ℕ, ((r : G) * y * (r : G)⁻¹ * y) ^ 2 ^ n = 1 := by
    obtain ⟨m, hm⟩ := piJ_ker eJ ((r * ⟨y, hyJ⟩ * r⁻¹ * ⟨y, hyJ⟩) ^ 2 ^ k)
      (by rw [map_pow, map_mul, map_mul, map_mul, map_inv]; exact hk)
    refine ⟨k + m, ?_⟩
    rw [pow_add, pow_mul]
    simpa using hm
  obtain ⟨eA⟩ := Conf.exists_eA c h1011 h1012 h1026 h1028 ⟨eL⟩ hcv
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨-, -, hV2C, -⟩ := hdec t c.ht c.htn
  obtain ⟨θ, hθ, hθv⟩ := exists_thetaL h37 h38 h1011 hyp (w := ⟨w, c.w_mem_V⟩) (hV2C c.claim.1)
  have : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := SecA.isSimpleGroup_of_not_normal h37 h38
    hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.faithful hyp.not_normal
  have hQ : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 :=
    (Nat.card_congr eL.toEquiv).trans card_SL_three_two
  have hyNV : y ∈ Subgroup.normalizer (fsuVM T L I : Set G) :=
    ((SecA.conjugate_le_fsuL0 c.ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)) hyLt
  have hyL0 : y ∈ fsuL0 T L ⊔ T := Subgroup.mem_sup_left (SecA.conjugate_le_fsuL0 c.ht hyLt)
  have hyw' : y * ((⟨w, c.w_mem_V⟩ : ↥(fsuVM T L I)) : G) * y⁻¹ = w := by
    show y * w * y⁻¹ = w
    rw [Subgroup.mem_centralizer_singleton_iff.mp hyw, mul_inv_cancel_right]
  have hrT : (r : G) ∈ T := hr'.1.1
  have hrw' : (r : G) * ((⟨w, c.w_mem_V⟩ : ↥(fsuVM T L I)) : G) * (r : G)⁻¹ = w := by
    show (r : G) * w * (r : G)⁻¹ = w
    rw [Subgroup.mem_centralizer_singleton_iff.mp hr'.1.2, mul_inv_cancel_right]
  set yb := autW (w := ⟨w, c.w_mem_V⟩) y hyNV hyL0 hyw' with hyb
  set rb := autW (w := ⟨w, c.w_mem_V⟩) (r : G) (SecA.le_normalizer_fsuVM T L I hrT)
    (Subgroup.mem_sup_right hrT) hrw' with hrb
  refine false_of_A4xL32 hQ eA θ hθ (y := yb) (r := rb) ?_ ?_ ?_ ?_
  ·
    intro h
    rw [hyb, autW_eq_one_iff] at h
    have hty : t * y * t⁻¹ ∈ L := by
      rw [SecA.mem_conjugate_iff] at hyLt
      exact hyLt
    have htN := Subgroup.inv_mem _ (SecA.le_normalizer_fsuVM T L I c.ht)
    have htyC : t * y * t⁻¹ ∈ Subgroup.centralizer (fsuUL T L I : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hvV : v ∈ fsuVM T L I := commutator_le_left_of_le_normalizer
        ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)) hv
      have hv' : t⁻¹ * v * t ∈ fsuVM T L I := by
        have := (Subgroup.mem_normalizer_iff.mp htN v).mp hvV
        rwa [inv_inv] at this
      have h1 := Subgroup.mem_centralizer_iff.mp h _ hv'
      calc v * (t * y * t⁻¹) = t * ((t⁻¹ * v * t) * y) * t⁻¹ := by group
        _ = t * (y * (t⁻¹ * v * t)) * t⁻¹ := by rw [h1]
        _ = t * y * t⁻¹ * v := by group
    have h2 := eq_one_of_odd_of_centralizer h37 h38 h1011 hyp hty htyC (n := 3)
      (by rw [conj_pow, hy3', mul_one, mul_inv_cancel]) (by decide)
    have h3 : y = 1 := by
      calc y = t⁻¹ * (t * y * t⁻¹) * t := by group
        _ = 1 := by rw [h2]; group
    rw [h3, orderOf_one] at hy3
    omega
  ·
    apply Subtype.ext
    rw [Subgroup.coe_pow, hyb, autW_val, ← map_pow, Subgroup.coe_one]
    rw [show (⟨y, hyNV⟩ : ↥(Subgroup.normalizer (fsuVM T L I : Set G))) ^ 3 = 1 from
      Subtype.ext (by simpa using hy3'), map_one]
  ·
    intro q
    induction q using QuotientGroup.induction_on with
    | H l =>
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hθv, hyb, autW_val, ← map_mul, ← map_mul]
      apply conjAct_eq_of_mul_inv_mem
      show y * l * ((l : G) * y)⁻¹ ∈ Subgroup.centralizer (fsuVM T L I : Set G)
      rw [show y * l * ((l : G) * y)⁻¹ = y * l * y⁻¹ * (l : G)⁻¹ by group]
      exact pCoreOf_L_le_centralizer hyp h1011 (hyc l l.2)
  ·
    obtain ⟨n, hn⟩ := hz
    refine ⟨n, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      hyb, hrb, autW_val, autW_val, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_pow,
      Subgroup.coe_one]
    convert map_one (conjAct (fsuVM T L I))
    exact Subtype.ext (by simpa using hn)

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
