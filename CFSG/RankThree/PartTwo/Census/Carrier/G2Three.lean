module

public import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.Blueprint.Catalog
public import CFSG.Blueprint.ChevalleyWeyl
public import CFSG.RankThree.PartTwo.Census.Carrier.G2ThreeCert
public import CFSG.Quasithin.Background.G2UAdjoint
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Chevalley.NativeMonomial
import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryFourThree
import CFSG.LieType.Chevalley.ExactG2FiniteOrder
import CFSG.Adapters.TauCetiExceptional.BridgeG2
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate8150
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.RankThree.PartTwo.Census.Carrier.G2Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U CFSG.Assembly
  CFSG.Assembly.RankThreeEven

local notation "M14" => Matrix (Fin 14) (Fin 14) (ZMod 3)
local notation "GL14" => GL (Fin 14) (ZMod 3)

theorem XMat_zero_one_three : XMat (ZMod 3) (ix 0) 1 = dec14 x0c := by
  decide +kernel

theorem XMat_one_one_three : XMat (ZMod 3) (ix 1) 1 = dec14 x1c := by
  decide +kernel

theorem YMat_zero_one_three : YMat (ZMod 3) (ix 0) 1 = dec14 y0c := by
  decide +kernel

theorem YMat_one_one_three : YMat (ZMod 3) (ix 1) 1 = dec14 y1c := by
  decide +kernel

@[expose] noncomputable def R3 : Subgroup GL14 :=
  (adjointGroup .G2 (ZMod 3)).map (glHom (RingEquiv.refl (ZMod 3)))

noncomputable def adjointEquivR3 : adjointGroup .G2 (ZMod 3) ≃* R3 :=
  Subgroup.equivMapOfInjective _ (glHom (RingEquiv.refl (ZMod 3))) (glHom_injective _)

theorem card_R3 : Nat.card R3 = 4245696 :=
  (Nat.card_congr adjointEquivR3.toEquiv).symm.trans
    ((CFSG.LieType.Chevalley.exact_G2_finite_order (ZMod 3) (q := 3) (by simp)).2.1.trans
      (by norm_num))

@[expose] noncomputable def gX (i : Fin 2) : GL14 :=
  glHom (RingEquiv.refl (ZMod 3)) (xUnit .G2 (ZMod 3) (ix i) 1)

@[expose] noncomputable def gY (i : Fin 2) : GL14 :=
  glHom (RingEquiv.refl (ZMod 3)) (yUnit .G2 (ZMod 3) (ix i) 1)

theorem gX_mem (i : Fin 2) : gX i ∈ R3 :=
  ⟨_, xUnit_mem_adjointGroup _ _, rfl⟩

theorem gY_mem (i : Fin 2) : gY i ∈ R3 :=
  ⟨_, yUnit_mem_adjointGroup _ _, rfl⟩

theorem coe_gX (i : Fin 2) : (gX i : M14) = XMat (ZMod 3) (ix i) 1 := by
  rw [gX, glHom_apply, coe_glEquiv, coe_xUnit, endEquiv_xOp]
  rfl

theorem coe_gY (i : Fin 2) : (gY i : M14) = YMat (ZMod 3) (ix i) 1 := by
  rw [gY, glHom_apply, coe_glEquiv, coe_yUnit, endEquiv_yOp]
  rfl

theorem coe_gX0 : (gX 0 : M14) = dec14 x0c :=
  (coe_gX 0).trans XMat_zero_one_three

theorem coe_gX1 : (gX 1 : M14) = dec14 x1c :=
  (coe_gX 1).trans XMat_one_one_three

theorem coe_gY0 : (gY 0 : M14) = dec14 y0c :=
  (coe_gY 0).trans YMat_zero_one_three

theorem coe_gY1 : (gY 1 : M14) = dec14 y1c :=
  (coe_gY 1).trans YMat_one_one_three

@[expose] noncomputable def tU : GL14 :=
  gX 1 ^ 2 * gY 1 * gX 1 * gY 1 * gX 1 ^ 2

@[expose] noncomputable def n0U : GL14 :=
  gX 0 * gY 0 ^ 2 * gX 0

@[expose] noncomputable def n1U : GL14 :=
  gX 1 * gY 1 ^ 2 * gX 1

@[expose] noncomputable def n0iU : GL14 :=
  gX 0 ^ 2 * gY 0 * gX 0 ^ 2

@[expose] noncomputable def n1iU : GL14 :=
  gX 1 ^ 2 * gY 1 * gX 1 ^ 2

@[expose] noncomputable def wU : GL14 :=
  n0U * n1U

@[expose] noncomputable def wiU : GL14 :=
  n1iU * n0iU

@[expose] noncomputable def uU : GL14 :=
  wU * gX 0 * wiU

@[expose] noncomputable def vU : GL14 :=
  wU * gY 0 * wiU

@[expose] noncomputable def h0U : GL14 :=
  gX 0 ^ 2 * gY 0 * gX 0 * gY 0 * gX 0 ^ 2

@[expose] noncomputable def q2U : GL14 :=
  gX 1 * n1U * gX 1 ^ 2

@[expose] noncomputable def nbU : GL14 :=
  uU * vU ^ 2 * uU

@[expose] noncomputable def qb2U : GL14 :=
  uU * nbU * uU ^ 2

theorem coe_sq {g : GL14} {c : List ℕ} (h : (g : M14) = dec14 c) :
    ((g ^ 2 : GL14) : M14) = dec14 (sq14 c) := by
  rw [Units.val_pow_eq_pow_val, pow_two, h, sq14, dec14_mul14]

theorem coe_mul {g h : GL14} {c d : List ℕ} (hg : (g : M14) = dec14 c)
    (hh : (h : M14) = dec14 d) : ((g * h : GL14) : M14) = dec14 (mul14 c d) := by
  rw [Units.val_mul, hg, hh, dec14_mul14]

theorem coe_tU : (tU : M14) = dec14 tc :=
  coe_mul (coe_mul (coe_mul (coe_mul (coe_sq coe_gX1) coe_gY1) coe_gX1) coe_gY1) (coe_sq coe_gX1)

theorem coe_n0U : (n0U : M14) = dec14 n0c :=
  coe_mul (coe_mul coe_gX0 (coe_sq coe_gY0)) coe_gX0

theorem coe_n1U : (n1U : M14) = dec14 n1c :=
  coe_mul (coe_mul coe_gX1 (coe_sq coe_gY1)) coe_gX1

theorem coe_n0iU : (n0iU : M14) = dec14 n0ic :=
  coe_mul (coe_mul (coe_sq coe_gX0) coe_gY0) (coe_sq coe_gX0)

theorem coe_n1iU : (n1iU : M14) = dec14 n1ic :=
  coe_mul (coe_mul (coe_sq coe_gX1) coe_gY1) (coe_sq coe_gX1)

theorem coe_wU : (wU : M14) = dec14 wc :=
  coe_mul coe_n0U coe_n1U

theorem coe_wiU : (wiU : M14) = dec14 wic :=
  coe_mul coe_n1iU coe_n0iU

theorem coe_uU : (uU : M14) = dec14 uc :=
  coe_mul (coe_mul coe_wU coe_gX0) coe_wiU

theorem coe_vU : (vU : M14) = dec14 vc :=
  coe_mul (coe_mul coe_wU coe_gY0) coe_wiU

theorem coe_h0U : (h0U : M14) = dec14 h0c :=
  coe_mul (coe_mul (coe_mul (coe_mul (coe_sq coe_gX0) coe_gY0) coe_gX0) coe_gY0) (coe_sq coe_gX0)

theorem coe_q2U : (q2U : M14) = dec14 q2c :=
  coe_mul (coe_mul coe_gX1 coe_n1U) (coe_sq coe_gX1)

theorem coe_nbU : (nbU : M14) = dec14 nbc :=
  coe_mul (coe_mul coe_uU (coe_sq coe_vU)) coe_uU

theorem coe_qb2U : (qb2U : M14) = dec14 qb2c :=
  coe_mul (coe_mul coe_uU coe_nbU) (coe_sq coe_uU)

theorem tU_mem : tU ∈ R3 :=
  mul_mem (mul_mem (mul_mem (mul_mem (pow_mem (gX_mem 1) 2) (gY_mem 1)) (gX_mem 1)) (gY_mem 1))
    (pow_mem (gX_mem 1) 2)

theorem n0U_mem : n0U ∈ R3 :=
  mul_mem (mul_mem (gX_mem 0) (pow_mem (gY_mem 0) 2)) (gX_mem 0)

theorem n1U_mem : n1U ∈ R3 :=
  mul_mem (mul_mem (gX_mem 1) (pow_mem (gY_mem 1) 2)) (gX_mem 1)

theorem wU_mem : wU ∈ R3 :=
  mul_mem n0U_mem n1U_mem

theorem wiU_mem : wiU ∈ R3 :=
  mul_mem (mul_mem (mul_mem (pow_mem (gX_mem 1) 2) (gY_mem 1)) (pow_mem (gX_mem 1) 2))
    (mul_mem (mul_mem (pow_mem (gX_mem 0) 2) (gY_mem 0)) (pow_mem (gX_mem 0) 2))

theorem uU_mem : uU ∈ R3 :=
  mul_mem (mul_mem wU_mem (gX_mem 0)) wiU_mem

theorem vU_mem : vU ∈ R3 :=
  mul_mem (mul_mem wU_mem (gY_mem 0)) wiU_mem

theorem h0U_mem : h0U ∈ R3 :=
  mul_mem (mul_mem (mul_mem (mul_mem (pow_mem (gX_mem 0) 2) (gY_mem 0)) (gX_mem 0)) (gY_mem 0))
    (pow_mem (gX_mem 0) 2)

theorem q2U_mem : q2U ∈ R3 :=
  mul_mem (mul_mem (gX_mem 1) n1U_mem) (pow_mem (gX_mem 1) 2)

theorem nbU_mem : nbU ∈ R3 :=
  mul_mem (mul_mem uU_mem (pow_mem vU_mem 2)) uU_mem

theorem qb2U_mem : qb2U ∈ R3 :=
  mul_mem (mul_mem uU_mem nbU_mem) (pow_mem uU_mem 2)

@[expose] noncomputable def X0 : Subgroup GL14 :=
  Subgroup.closure {gX 1, gY 1, uU, vU, h0U}

@[expose] noncomputable def S2 : Subgroup GL14 :=
  Subgroup.closure {n1U, q2U, nbU, qb2U, h0U}

@[expose] noncomputable def P9 : Subgroup GL14 :=
  Subgroup.closure {gX 1, uU}

theorem image_gens_X0 : (Units.coeHom M14) '' {gX 1, gY 1, uU, vU, h0U} =
    {y | ∃ c ∈ gensX, dec14 c = y} := by
  ext y
  simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_ofPred_eq, gensX, List.mem_cons, List.not_mem_nil,
    or_false, exists_eq_or_imp, exists_eq_left, Units.coeHom_apply, coe_gX1, coe_gY1, coe_uU,
    coe_vU, coe_h0U, @eq_comm _ (dec14 _) y]

theorem image_gens_S2 : (Units.coeHom M14) '' {n1U, q2U, nbU, qb2U, h0U} =
    {y | ∃ c ∈ gensS, dec14 c = y} := by
  ext y
  simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_ofPred_eq, gensS, List.mem_cons, List.not_mem_nil,
    or_false, exists_eq_or_imp, exists_eq_left, Units.coeHom_apply, coe_n1U, coe_q2U, coe_nbU,
    coe_qb2U, coe_h0U, @eq_comm _ (dec14 _) y]

theorem image_gens_P9 : (Units.coeHom M14) '' {gX 1, uU} = {y | ∃ c ∈ gensP, dec14 c = y} := by
  ext y
  simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_ofPred_eq, gensP, List.mem_cons, List.not_mem_nil,
    or_false, exists_eq_or_imp, exists_eq_left, Units.coeHom_apply, coe_gX1, coe_uU,
    @eq_comm _ (dec14 _) y]

theorem card_X0 : Nat.card X0 = 576 := by
  obtain ⟨hsize, hclosed, hdist, hcanon, -⟩ := certX
  refine (card_closure_eq dec14 one14 mul14 gensX (Units.coeHom M14) Units.val_injective
    dec14_one14 dec14_mul14 _ image_gens_X0 parX hclosed hdist fun t ht t' ht' e => ?_).trans
      hsize
  exact dec14_injective (allCheck_spec hcanon ht) (allCheck_spec hcanon ht') e

theorem card_S2 : Nat.card S2 = 64 := by
  obtain ⟨hsize, hclosed, hdist, hcanon⟩ := certS
  refine (card_closure_eq dec14 one14 mul14 gensS (Units.coeHom M14) Units.val_injective
    dec14_one14 dec14_mul14 _ image_gens_S2 parS hclosed hdist fun t ht t' ht' e => ?_).trans
      hsize
  exact dec14_injective (allCheck_spec hcanon ht) (allCheck_spec hcanon ht') e

theorem card_P9 : Nat.card P9 = 9 := by
  obtain ⟨hsize, hclosed, hdist, hcanon⟩ := certP
  refine (card_closure_eq dec14 one14 mul14 gensP (Units.coeHom M14) Units.val_injective
    dec14_one14 dec14_mul14 _ image_gens_P9 parP hclosed hdist fun t ht t' ht' e => ?_).trans
      hsize
  exact dec14_injective (allCheck_spec hcanon ht) (allCheck_spec hcanon ht') e

theorem image_X0 : (Units.coeHom M14) '' (X0 : Set GL14) =
    {y | ∃ t < elemsX.size, dec14 (elemsX.getD t []) = y} :=
  image_closure_eq dec14 one14 mul14 gensX (Units.coeHom M14) dec14_one14 dec14_mul14 _
    image_gens_X0 parX certX.2.1

theorem image_S2 : (Units.coeHom M14) '' (S2 : Set GL14) =
    {y | ∃ t < elemsS.size, dec14 (elemsS.getD t []) = y} :=
  image_closure_eq dec14 one14 mul14 gensS (Units.coeHom M14) dec14_one14 dec14_mul14 _
    image_gens_S2 parS certS.2.1

theorem exists_code_X0 {g : GL14} (hg : g ∈ X0) :
    ∃ t < elemsX.size, dec14 (elemsX.getD t []) = (g : M14) := by
  have h : (Units.coeHom M14) g ∈ (Units.coeHom M14) '' (X0 : Set GL14) := ⟨g, hg, rfl⟩
  rw [image_X0] at h
  exact h

theorem exists_code_S2 {g : GL14} (hg : g ∈ S2) :
    ∃ t < elemsS.size, dec14 (elemsS.getD t []) = (g : M14) := by
  have h : (Units.coeHom M14) g ∈ (Units.coeHom M14) '' (S2 : Set GL14) := ⟨g, hg, rfl⟩
  rw [image_S2] at h
  exact h

theorem X0_le_R3 : X0 ≤ R3 := by
  rw [X0, Subgroup.closure_le]
  rintro g (rfl | rfl | rfl | rfl | rfl)
  exacts [gX_mem 1, gY_mem 1, uU_mem, vU_mem, h0U_mem]

theorem S2_le_R3 : S2 ≤ R3 := by
  rw [S2, Subgroup.closure_le]
  rintro g (rfl | rfl | rfl | rfl | rfl)
  exacts [n1U_mem, q2U_mem, nbU_mem, qb2U_mem, h0U_mem]

theorem P9_le_X0 : P9 ≤ X0 := by
  rw [P9, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

theorem commute_of_commutes {g h : GL14} {c d : List ℕ} (hg : (g : M14) = dec14 c)
    (hh : (h : M14) = dec14 d) (hc : commutes c d = true) : g * h = h * g := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hg, hh, ← dec14_mul14, ← dec14_mul14,
    beq_iff_eq.mp hc]

theorem X0_le_centralizer : X0 ≤ Subgroup.centralizer {tU} := by
  have hc := certX.2.2.2.2
  simp only [commuteCheck, gensX, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at hc
  obtain ⟨h1, h2, h3, h4, h5⟩ := hc
  rw [X0, Subgroup.closure_le]
  rintro g (rfl | rfl | rfl | rfl | rfl) <;>
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  · exact commute_of_commutes coe_gX1 coe_tU h1
  · exact commute_of_commutes coe_gY1 coe_tU h2
  · exact commute_of_commutes coe_uU coe_tU h3
  · exact commute_of_commutes coe_vU coe_tU h4
  · exact commute_of_commutes coe_h0U coe_tU h5

theorem pow_three_of_code {g : GL14} {c : List ℕ} (hg : (g : M14) = dec14 c)
    (h : mul14 c (sq14 c) = one14) : g ^ 3 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, pow_succ', pow_two, hg, Units.val_one, ← dec14_mul14,
    ← dec14_mul14, ← sq14, h, dec14_one14]

theorem gens_pow_three : gX 0 ^ 3 = 1 ∧ gX 1 ^ 3 = 1 ∧ gY 0 ^ 3 = 1 ∧ gY 1 ^ 3 = 1 := by
  have hc := certC.2
  simp only [cubeCheck, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq] at hc
  obtain ⟨h1, h2, h3, h4⟩ := hc
  exact ⟨pow_three_of_code coe_gX0 h1, pow_three_of_code coe_gX1 h2,
    pow_three_of_code coe_gY0 h3, pow_three_of_code coe_gY1 h4⟩

theorem inv_eq_sq {g : GL14} (h : g ^ 3 = 1) : g⁻¹ = g ^ 2 := by
  rw [inv_eq_iff_mul_eq_one, ← pow_succ']
  exact h

theorem gensO_spec : ∀ gp ∈ gensO, ∃ g ∈ R3, dec14 (gp.take 196) = (g : M14) ∧
    dec14 (gp.drop 196) = ((g⁻¹ : GL14) : M14) := by
  obtain ⟨h0, h1, h2, h3⟩ := gens_pow_three
  have key : ∀ (c : List ℕ) (g : GL14), g ∈ R3 → (g : M14) = dec14 c → c.length = 196 →
      g ^ 3 = 1 → ∃ g' ∈ R3, dec14 ((c ++ sq14 c).take 196) = (g' : M14) ∧
        dec14 ((c ++ sq14 c).drop 196) = ((g'⁻¹ : GL14) : M14) := by
    intro c g hgR hg hc h3
    refine ⟨g, hgR, ?_, ?_⟩
    · rw [List.take_left' hc, hg]
    · rw [List.drop_left' hc, inv_eq_sq h3, coe_sq hg]
  simp only [gensO, List.mem_cons, List.not_mem_nil, or_false]
  rintro gp (rfl | rfl | rfl | rfl)
  · exact key _ _ (gX_mem 0) coe_gX0 rfl h0
  · exact key _ _ (gX_mem 1) coe_gX1 rfl h1
  · exact key _ _ (gY_mem 0) coe_gY0 rfl h2
  · exact key _ _ (gY_mem 1) coe_gY1 rfl h3

theorem exists_conj_of_orbit {k : ℕ} (hk : k < elemsO.size) :
    ∃ g ∈ R3, dec14 (elemsO.getD k []) = (g : M14) * (tU : M14) * ((g⁻¹ : GL14) : M14) := by
  have hmem : elemsO.getD k [] ∈ orbitBuild tc gensO parO := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some]
    exact Array.getElem_mem hk
  rw [coe_tU]
  exact orbitBuild_spec R3 tc gensO gensO_spec parO _ hmem

section Abstract

variable {H : Type} [Group H] [Finite H]

theorem card_centralizer_mul_le {t : H} {n : ℕ} (f : Fin n → H) (hf : Function.Injective f)
    (hft : ∀ k, ∃ g, f k = g * t * g⁻¹) :
    Nat.card (Subgroup.centralizer {t}) * n ≤ Nat.card H := by
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (ConjAct H) t)
  rw [MulAction.index_stabilizer, ← Subgroup.nat_card_centralizer_nat_card_stabilizer,
    Nat.card_congr (ConjAct.toConjAct (G := H)).toEquiv.symm] at h1
  have hmem : ∀ k, f k ∈ MulAction.orbit (ConjAct H) t := fun k => by
    obtain ⟨g, hg⟩ := hft k
    exact ⟨ConjAct.toConjAct g, by
      change ConjAct.toConjAct g • t = f k
      rw [ConjAct.toConjAct_smul, hg]⟩
  have h2 : n ≤ (MulAction.orbit (ConjAct H) t).ncard := by
    calc n = (Set.range f).ncard := by rw [Set.ncard_range_of_injective hf, Nat.card_fin]
      _ ≤ _ := Set.ncard_le_ncard (Set.range_subset_iff.mpr hmem) (Set.toFinite _)
  calc Nat.card (Subgroup.centralizer {t}) * n ≤
        Nat.card (Subgroup.centralizer {t}) * (MulAction.orbit (ConjAct H) t).ncard :=
      Nat.mul_le_mul_left _ h2
    _ = Nat.card H := h1

omit [Finite H] in
theorem map_conj_le_centralizer {R : Subgroup H} {s g : H}
    (hR : R ≤ Subgroup.centralizer {g * s * g⁻¹}) :
    R.map (MulAut.conj g⁻¹).toMonoidHom ≤ Subgroup.centralizer {s} := by
  rintro _ ⟨r, hr, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := Subgroup.mem_centralizer_singleton_iff.mp (hR hr)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  calc g⁻¹ * r * g * s = g⁻¹ * (r * (g * s * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * s * g⁻¹) * r) * g := by rw [h]
    _ = s * (g⁻¹ * r * g) := by group

theorem exists_conj_of_sylow {t : H} {S : Subgroup H} (hcard : Nat.card H = 4245696)
    (hS : Nat.card S = 64) (hSinv : ∀ u ∈ S, orderOf u = 2 → ∃ g, u = g * t * g⁻¹) {s : H}
    (hs : orderOf s = 2) : ∃ g, s = g * t * g⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : IsPGroup 2 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  have hSp : IsPGroup 2 S := IsPGroup.of_card (n := 6) (hS.trans (by norm_num))
  have hSi : S.index = 66339 := by
    have h := Subgroup.card_mul_index S
    rw [hS, hcard] at h
    omega
  let SS : Sylow 2 H := hSp.toSylow (by rw [hSi]; decide)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H SS Q
  have hQeq : (Q : Subgroup H) = S.map (MulAut.conj g).toMonoidHom := by
    have h1 : ((g • SS : Sylow 2 H) : Subgroup H) = (Q : Subgroup H) := by rw [hg]
    rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h1
    exact h1.symm
  have hsQ : s ∈ (Q : Subgroup H) := hQ (Subgroup.mem_zpowers s)
  rw [hQeq] at hsQ
  obtain ⟨u, huS, rfl⟩ := hsQ
  have hu2 : orderOf u = 2 := by
    rw [← hs]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective u).symm
  obtain ⟨g', hg'⟩ := hSinv u huS hu2
  refine ⟨g * g', ?_⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hg']
  group

omit [Finite H] in
theorem card_le_two_of_forall {t : H} {Q : Subgroup H} (hQ : ∀ q ∈ Q, q = 1 ∨ q = t) :
    Nat.card Q ≤ 2 := by
  classical
  have hinj : Function.Injective fun q : Q => decide ((q : H) = 1) := by
    intro a b hab
    simp only at hab
    apply Subtype.ext
    rcases hQ a a.2 with ha | ha <;> rcases hQ b b.2 with hb | hb
    · rw [ha, hb]
    · rw [ha, hb] at hab ⊢
      simp at hab
      exact hab.symm
    · rw [ha, hb] at hab ⊢
      simp at hab
      exact hab
    · rw [ha, hb]
  have h := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h

omit [Finite H] in
theorem pow_sixtyfour_eq_one_of_mem {X : Subgroup H} (hX : Nat.card X = 576) {q : H}
    (hq : q ∈ X) {k : ℕ} (hk : q ^ 2 ^ k = 1) : q ^ 64 = 1 := by
  have h1 : orderOf q ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hjq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have h2 : orderOf q ∣ 576 := by
    rw [← hX, ← Subgroup.orderOf_mk q hq]
    exact orderOf_dvd_natCard _
  rw [hjq] at h2
  have hj6 : j ≤ 6 := by
    by_contra hlt
    have : 2 ^ 7 ∣ 576 := (pow_dvd_pow 2 (by omega)).trans h2
    norm_num at this
  rw [← orderOf_dvd_iff_pow_eq_one, hjq]
  exact pow_dvd_pow 2 hj6

theorem exists_conj_of_card_nine {X P P₁ : Subgroup H} (hX : Nat.card X = 576) (hPX : P ≤ X)
    (hP : Nat.card P = 9) (hP₁X : P₁ ≤ X) (hP₁ : Nat.card P₁ = 9) :
    ∃ y ∈ X, ∀ p ∈ P, y * p * y⁻¹ ∈ P₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsyl : ∀ P' : Subgroup H, P' ≤ X → Nat.card P' = 9 →
      IsPGroup 3 (P'.subgroupOf X) ∧ ¬ 3 ∣ (P'.subgroupOf X).index := by
    intro P' hP' hc
    have hc' : Nat.card (P'.subgroupOf X) = 9 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP').toEquiv, hc]
    refine ⟨IsPGroup.of_card (n := 2) (hc'.trans (by norm_num)), ?_⟩
    have h := Subgroup.card_mul_index (P'.subgroupOf X)
    rw [hc', hX] at h
    have h64 : (P'.subgroupOf X).index = 64 := by omega
    rw [h64]
    decide
  obtain ⟨h1a, h1b⟩ := hsyl P₁ hP₁X hP₁
  obtain ⟨h9a, h9b⟩ := hsyl P hPX hP
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X (h9a.toSylow h9b) (h1a.toSylow h1b)
  have hPeq : P₁.subgroupOf X = (P.subgroupOf X).map (MulAut.conj x).toMonoidHom := by
    have h1 : ((x • h9a.toSylow h9b : Sylow 3 X) : Subgroup X) =
        (h1a.toSylow h1b : Subgroup X) := by rw [hx]
    rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe, IsPGroup.toSylow_coe] at h1
    exact h1.symm
  refine ⟨x, x.2, fun p hp => ?_⟩
  have hmem : (MulAut.conj x).toMonoidHom ⟨p, hPX hp⟩ ∈ P₁.subgroupOf X := by
    rw [hPeq]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hp)
  exact Subgroup.mem_subgroupOf.mp hmem

theorem localRank_three_le_two_of_involution_data {t : H} {X S P : Subgroup H}
    (hcard : Nat.card H = 4245696) (hXt : X ≤ Subgroup.centralizer {t}) (hX : Nat.card X = 576)
    (f : Fin 7371 → H) (hf : Function.Injective f) (hft : ∀ k, ∃ g, f k = g * t * g⁻¹)
    (hS : Nat.card S = 64) (hSinv : ∀ u ∈ S, orderOf u = 2 → ∃ g, u = g * t * g⁻¹)
    (hPX : P ≤ X) (hP : Nat.card P = 9)
    (hPc : ∀ q ∈ X, (∀ p ∈ P, q * p = p * q) → q ^ 64 = 1 → q = 1 ∨ q = t) :
    localRank 3 H ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCX : Subgroup.centralizer {t} = X := by
    refine (Subgroup.eq_of_le_of_card_ge hXt ?_).symm
    have h := card_centralizer_mul_le f hf hft
    rw [hcard] at h
    rw [hX]
    by_contra hlt
    push Not at hlt
    have : 577 * 7371 ≤ Nat.card (Subgroup.centralizer {t}) * 7371 := Nat.mul_le_mul_right _ hlt
    omega
  have hconj := fun s (hs : orderOf s = 2) => exists_conj_of_sylow hcard hS hSinv hs
  refine UnitaryFourThree.localRank_three_le_two_of (fun s hs R hR h27 => ?_)
    (fun K hK Q hQ hQK => ?_)
  ·
    obtain ⟨g, rfl⟩ := hconj s hs
    have h1 := map_conj_le_centralizer hR
    have h2 : Nat.card (R.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card R :=
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    have h3 := Subgroup.card_dvd_of_le h1
    rw [h2, hCX, hX] at h3
    have := h27.trans h3
    norm_num at this
  ·
    by_cases hQ1 : Q = ⊥
    · rw [hQ1, Subgroup.card_bot]
      omega
    have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ1
    have hZ2 : 2 ∣ Nat.card (Subgroup.center Q) := by
      have hZp : IsPGroup 2 (Subgroup.center Q) := hQ.to_subgroup _
      have := hQ.center_nontrivial
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZp
      rcases k with _ | k
      · rw [pow_zero] at hk
        exact absurd hk Finite.one_lt_card.ne'
      · rw [hk, pow_succ]
        exact dvd_mul_left 2 _
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hZ2
    set s : H := (((z : Subgroup.center Q) : Q) : H)
    have hsQ : s ∈ Q := ((z : Subgroup.center Q) : Q).2
    have hs2 : orderOf s = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
    have hsc : ∀ q ∈ Q, q * s = s * q := fun q hq =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨q, hq⟩)
    obtain ⟨g, hg⟩ := hconj s hs2
    set c : H →* H := (MulAut.conj g⁻¹).toMonoidHom with hc_def
    have hcinj : Function.Injective c := (MulAut.conj g⁻¹).injective
    have hcs : c s = t := by
      rw [hg, hc_def, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hQ₁X : Q.map c ≤ X := by
      rw [← hCX]
      rintro _ ⟨q, hq, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hcs, ← map_mul, ← map_mul, hsc q hq]
    have hK₁X : K.map c ≤ X := by
      rw [← hCX]
      rintro _ ⟨k, hk, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hcs, ← map_mul, ← map_mul]
      exact congrArg c (Subgroup.mem_centralizer_iff.mp (hQK hsQ) k hk)
    have hQ₁K₁ : ∀ q ∈ Q.map c, ∀ k ∈ K.map c, q * k = k * q := by
      rintro _ ⟨q, hq, rfl⟩ _ ⟨k, hk, rfl⟩
      rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp (hQK hq) k hk)]
    have hK₁ : Nat.card (K.map c) = Nat.card K := Subgroup.card_map_of_injective hcinj
    obtain ⟨P₁', hP₁'⟩ := Sylow.exists_subgroup_card_pow_prime (G := K.map c) 3 (n := 2)
      (by rw [hK₁]; exact hK)
    have hP₁K : P₁'.map (K.map c).subtype ≤ K.map c := Subgroup.map_subtype_le _
    have hcardP₁ : Nat.card (P₁'.map (K.map c).subtype) = 9 := by
      rw [Subgroup.card_map_of_injective (K.map c).subtype_injective, hP₁']
      norm_num
    obtain ⟨y, hyX, hy⟩ := exists_conj_of_card_nine hX hPX hP (hP₁K.trans hK₁X) hcardP₁
    have hQ2 : ∀ q ∈ (Q.map c).map (MulAut.conj y⁻¹).toMonoidHom, q = 1 ∨ q = t := by
      rintro _ ⟨q, hq, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      have hqX : y⁻¹ * q * y ∈ X := mul_mem (mul_mem (inv_mem hyX) (hQ₁X hq)) hyX
      have hcomm : ∀ p ∈ P, (y⁻¹ * q * y) * p = p * (y⁻¹ * q * y) := by
        intro p hp
        have h := hQ₁K₁ q hq _ (hP₁K (hy p hp))
        calc (y⁻¹ * q * y) * p = y⁻¹ * (q * (y * p * y⁻¹)) * y := by group
          _ = y⁻¹ * ((y * p * y⁻¹) * q) * y := by rw [h]
          _ = p * (y⁻¹ * q * y) := by group
      obtain ⟨q₀, hq₀, rfl⟩ := hq
      obtain ⟨k, hk⟩ := hQ ⟨q₀, hq₀⟩
      have hk₀ : q₀ ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have hk' : (y⁻¹ * c q₀ * y) ^ 2 ^ k = 1 := by
        have e := map_pow (MulAut.conj y⁻¹) (c q₀) (2 ^ k)
        rw [MulAut.conj_apply, inv_inv, MulAut.conj_apply, inv_inv] at e
        rw [← e, ← map_pow, hk₀, map_one, mul_one, inv_mul_cancel]
      exact hPc _ hqX hcomm (pow_sixtyfour_eq_one_of_mem hX hqX hk')
    have hle := card_le_two_of_forall hQ2
    rwa [Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective,
      Subgroup.card_map_of_injective hcinj] at hle

end Abstract

abbrev H3 : Type :=
  ↥R3

@[expose] noncomputable def tH : H3 :=
  ⟨tU, tU_mem⟩

noncomputable def orbitConj (k : Fin 7371) : H3 :=
  if hk : (k : ℕ) < elemsO.size then
    ⟨(exists_conj_of_orbit hk).choose, (exists_conj_of_orbit hk).choose_spec.1⟩
  else 1

noncomputable def orbitElt (k : Fin 7371) : H3 :=
  orbitConj k * tH * (orbitConj k)⁻¹

theorem orbitElt_conj (k : Fin 7371) : ∃ g : H3, orbitElt k = g * tH * g⁻¹ :=
  ⟨orbitConj k, rfl⟩

theorem coe_tH : (tH : GL14) = tU :=
  rfl

theorem coe_orbitElt {k : Fin 7371} (hk : (k : ℕ) < elemsO.size) :
    (((orbitElt k : H3) : GL14) : M14) = dec14 (elemsO.getD k []) := by
  have hc : ((orbitConj k : H3) : GL14) = (exists_conj_of_orbit hk).choose := by
    rw [orbitConj, dite_eq_left hk]
  rw [(exists_conj_of_orbit hk).choose_spec.2, orbitElt, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, hc, coe_tH, Units.val_mul, Units.val_mul]

theorem orbitElt_injective : Function.Injective orbitElt := by
  obtain ⟨hsize, hdist, hcanon, -⟩ := certO
  intro k k' h
  have hk : (k : ℕ) < elemsO.size := by rw [hsize]; exact k.2
  have hk' : (k' : ℕ) < elemsO.size := by rw [hsize]; exact k'.2
  have e := congrArg (fun x : H3 => ((x : GL14) : M14)) h
  simp only [coe_orbitElt hk, coe_orbitElt hk'] at e
  exact Fin.ext (distinctCheck_spec hdist hk hk'
    (dec14_injective (allCheck_spec hcanon hk) (allCheck_spec hcanon hk') e))

@[expose] noncomputable def X0H : Subgroup H3 :=
  X0.subgroupOf R3

@[expose] noncomputable def S2H : Subgroup H3 :=
  S2.subgroupOf R3

@[expose] noncomputable def P9H : Subgroup H3 :=
  P9.subgroupOf R3

theorem card_X0H : Nat.card X0H = 576 := by
  rw [X0H, Nat.card_congr (Subgroup.subgroupOfEquivOfLe X0_le_R3).toEquiv, card_X0]

theorem card_S2H : Nat.card S2H = 64 := by
  rw [S2H, Nat.card_congr (Subgroup.subgroupOfEquivOfLe S2_le_R3).toEquiv, card_S2]

theorem card_P9H : Nat.card P9H = 9 := by
  rw [P9H, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (P9_le_X0.trans X0_le_R3)).toEquiv,
    card_P9]

theorem X0H_le_centralizer : X0H ≤ Subgroup.centralizer {tH} := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp
    (X0_le_centralizer (Subgroup.mem_subgroupOf.mp hx)))

theorem found_spec {es : Array (List ℕ)} {m : Std.HashMap (List ℕ) ℕ} {y : List ℕ}
    (h : found es m y = true) : ∃ t < es.size, es.getD t [] = y := by
  simp only [found] at h
  split at h
  · rename_i t _
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨t, h.1, h.2⟩
  · exact absurd h Bool.false_ne_true

theorem exists_conj_of_mem_S2H (u : H3) (hu : u ∈ S2H) (hu2 : orderOf u = 2) :
    ∃ g : H3, u = g * tH * g⁻¹ := by
  obtain ⟨k, hk, hcode⟩ := exists_code_S2 (Subgroup.mem_subgroupOf.mp hu)
  have hcheck := allCheck_spec certO.2.2.2 hk
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu2
    omega
  have hsq : u * u = 1 := by rw [← pow_two, ← hu2, pow_orderOf_eq_one]
  have hcsq : mul14 (elemsS.getD k []) (elemsS.getD k []) = one14 := by
    refine dec14_injective (canon14_mul14 _ _) canon14_one14 ?_
    rw [dec14_mul14, hcode, dec14_one14, ← Units.val_mul, ← Subgroup.coe_mul, hsq]
    rfl
  have hc1 : elemsS.getD k [] ≠ one14 := by
    intro h
    apply hu1
    refine Subtype.ext (Units.ext ?_)
    rw [← hcode, h, dec14_one14]
    rfl
  simp only [invP, hcsq, beq_self_eq_true, Bool.not_true, Bool.false_or] at hcheck
  rcases Bool.or_eq_true_iff.mp hcheck with h | h
  · exact absurd (beq_iff_eq.mp h) hc1
  obtain ⟨k', hk', hcode'⟩ := found_spec h
  obtain ⟨g, hg, hgc⟩ := exists_conj_of_orbit hk'
  refine ⟨⟨g, hg⟩, Subtype.ext (Units.ext ?_)⟩
  rw [← hcode, ← hcode', hgc]
  rfl

theorem dec14_sq14 (x : List ℕ) : dec14 (sq14 x) = dec14 x ^ 2 := by
  rw [sq14, dec14_mul14, pow_two]

theorem dec14_pow64 (x : List ℕ) : dec14 (pow64 x) = dec14 x ^ 64 := by
  simp only [pow64, dec14_sq14, ← pow_mul]

theorem eq_one_or_eq_tU {q : GL14} (hq : q ∈ X0) (h1 : q * gX 1 = gX 1 * q)
    (h2 : q * uU = uU * q) (h64 : q ^ 64 = 1) : q = 1 ∨ q = tU := by
  obtain ⟨k, hk, hcode⟩ := exists_code_X0 hq
  have hcheck := allCheck_spec certC.1 hk
  have hc1 : commutes (elemsX.getD k []) x1c = true := by
    rw [commutes, beq_iff_eq]
    refine dec14_injective (canon14_mul14 _ _) (canon14_mul14 _ _) ?_
    rw [dec14_mul14, dec14_mul14, hcode, ← coe_gX1, ← Units.val_mul, ← Units.val_mul, h1]
  have hc2 : commutes (elemsX.getD k []) uc = true := by
    rw [commutes, beq_iff_eq]
    refine dec14_injective (canon14_mul14 _ _) (canon14_mul14 _ _) ?_
    rw [dec14_mul14, dec14_mul14, hcode, ← coe_uU, ← Units.val_mul, ← Units.val_mul, h2]
  have hc3 : pow64 (elemsX.getD k []) = one14 := by
    refine dec14_injective ?_ canon14_one14 ?_
    · simp only [pow64, sq14]
      exact canon14_mul14 _ _
    · rw [dec14_pow64, hcode, dec14_one14, ← Units.val_pow_eq_pow_val, h64, Units.val_one]
  simp only [centralP, hc1, hc2, hc3, beq_self_eq_true, Bool.and_self, Bool.not_true,
    Bool.false_or] at hcheck
  rcases Bool.or_eq_true_iff.mp hcheck with h | h
  · left
    refine Units.ext ?_
    rw [← hcode, beq_iff_eq.mp h, dec14_one14, Units.val_one]
  · right
    refine Units.ext ?_
    rw [← hcode, beq_iff_eq.mp h, coe_tU]

theorem eq_one_or_eq_tH (q : H3) (hq : q ∈ X0H) (hc : ∀ p ∈ P9H, q * p = p * q)
    (h64 : q ^ 64 = 1) : q = 1 ∨ q = tH := by
  have hgX1 : gX 1 ∈ P9 := Subgroup.subset_closure (by simp)
  have huU : uU ∈ P9 := Subgroup.subset_closure (by simp)
  have hc1 := congrArg Subtype.val
    (hc ⟨gX 1, P9_le_X0.trans X0_le_R3 hgX1⟩ (Subgroup.mem_subgroupOf.mpr hgX1))
  have hc2 := congrArg Subtype.val
    (hc ⟨uU, P9_le_X0.trans X0_le_R3 huU⟩ (Subgroup.mem_subgroupOf.mpr huU))
  have h64' : (q : GL14) ^ 64 = 1 := by
    rw [← Subgroup.coe_pow, h64, Subgroup.coe_one]
  rcases eq_one_or_eq_tU (Subgroup.mem_subgroupOf.mp hq) hc1 hc2 h64' with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem localRank_three_R3 : localRank 3 H3 ≤ 2 :=
  localRank_three_le_two_of_involution_data (t := tH) card_R3 X0H_le_centralizer card_X0H
    orbitElt orbitElt_injective orbitElt_conj card_S2H exists_conj_of_mem_S2H
    (Subgroup.subgroupOf_mono _ P9_le_X0) card_P9H eq_one_or_eq_tH

noncomputable def adjointQuotientEquivR3 : AdjointQuotient .G2 (ZMod 3) ≃* H3 :=
  ((QuotientGroup.quotientMulEquivOfEq
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot).trans
    adjointEquivR3

theorem localRank_three_adjointQuotient : localRank 3 (AdjointQuotient .G2 (ZMod 3)) ≤ 2 :=
  (@localRank_eq_of_mulEquiv _ H3 _ R3.toGroup _ _ adjointQuotientEquivR3 3
    Nat.prime_three).trans_le localRank_three_R3

end CFSG.RankThree.PartTwo.Census.Carrier.G2Three

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven TauCeti

theorem excluded433_G2_three (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid) (hp : q.p = 3)
    (he : q.exponent = 1) : Excluded433 (.lie ⟨.G2 q, hv⟩) := by
  intro G _ _ hG e
  have hK : Nat.card (ZMod 3) = q.card := by
    rw [Nat.card_zmod, PrimePower.card_def, hp, he, pow_one]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q hv (by rw [hp]; decide) (ZMod 3) hK
  exact hG.false_of_localRank_three_le_two (e.trans b.symm)
    Carrier.G2Three.localRank_three_adjointQuotient

end CFSG.RankThree.PartTwo.Census
