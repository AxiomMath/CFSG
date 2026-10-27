module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddCoord
public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddNat
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs517Odd
public import CFSG.Quasithin.Vol2.Ch5ModulesFFOrd
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Odd

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL unipSL_mulVec)
open scoped IsMulCommutative commutatorElement Pointwise

section Coord

variable {G : Type} [Group G] {T L V : Subgroup G} {n : ℕ} (c : OddCoord T L V n)

theorem OddCoord.act_mul (g h : Subgroup.normalizer (V : Set G)) (w : Fin 2 → c.K) :
    c.act (g * h) w = c.act g (c.act h w) := by
  obtain ⟨v, rfl⟩ := c.ε_bij.2 w
  rw [c.act_ε, c.act_ε, c.act_ε, map_mul, MulAut.mul_apply]

theorem OddCoord.act_one (w : Fin 2 → c.K) : c.act 1 w = w := by
  obtain ⟨v, rfl⟩ := c.ε_bij.2 w
  rw [c.act_ε, map_one, MulAut.one_apply]

theorem OddCoord.act_add (g : Subgroup.normalizer (V : Set G)) (w w' : Fin 2 → c.K) :
    c.act g (w + w') = c.act g w + c.act g w' := by
  obtain ⟨v, rfl⟩ := c.ε_bij.2 w
  obtain ⟨v', rfl⟩ := c.ε_bij.2 w'
  rw [← c.ε_mul, c.act_ε, c.act_ε, c.act_ε, map_mul, c.ε_mul]

theorem OddCoord.conj_eq_iff (g : Subgroup.normalizer (V : Set G)) (v : ↥V) :
    (g : G) * v * (g : G)⁻¹ = v ↔ c.act g (c.ε v) = c.ε v := by
  rw [c.act_ε]
  constructor
  · intro h
    congr 1
    exact Subtype.ext (by rw [conjAct_apply_coe, h])
  · intro h
    rw [← conjAct_apply_coe, c.ε_bij.1 h]

theorem OddCoord.act_eq_of_conj_eq {g h : Subgroup.normalizer (V : Set G)}
    (hgh : ∀ v ∈ V, (g : G) * v * (g : G)⁻¹ = (h : G) * v * (h : G)⁻¹) (w : Fin 2 → c.K) :
    c.act g w = c.act h w := by
  obtain ⟨v, rfl⟩ := c.ε_bij.2 w
  rw [c.act_ε, c.act_ε]
  congr 1
  exact Subtype.ext (by rw [conjAct_apply_coe, conjAct_apply_coe, hgh v v.2])

theorem OddCoord.mem_centralizer_iff (g : Subgroup.normalizer (V : Set G)) :
    (g : G) ∈ Subgroup.centralizer (V : Set G) ↔ ∀ w, c.act g w = w := by
  constructor
  · intro hg w
    obtain ⟨v, rfl⟩ := c.ε_bij.2 w
    refine (c.conj_eq_iff g v).mp ?_
    rw [(Subgroup.mem_centralizer_iff.mp hg v v.2).symm, mul_assoc, mul_inv_cancel, mul_one]
  · intro hg
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have := (c.conj_eq_iff g ⟨v, hv⟩).mpr (hg _)
    calc v * (g : G) = ((g : G) * v * (g : G)⁻¹) * g := by rw [this]
      _ = g * v := by group

theorem mulVec_one_of_lower {K : Type} [Field K] (A : Matrix (Fin 2) (Fin 2) K) (h : A 1 0 = 0)
    (w : Fin 2 → K) : (A.mulVec w) 1 = A 1 1 * w 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h]

end Coord

namespace Setup5_1_17Odd

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}
variable (s : Setup5_1_17Odd G T M L V H B D n)
include s

theorem le_normalizer_V : L ⊔ T ≤ Subgroup.normalizer (V : Set G) :=
  s.hyp.module.isTwoReducedIn.2.1

theorem L_le_normalizer_V : L ≤ Subgroup.normalizer (V : Set G) :=
  le_sup_left.trans s.le_normalizer_V

theorem elemAbelian : IsElemAbelian 2 V := s.hyp.module.isTwoReducedIn.2.2.1

theorem one_le_n : 1 ≤ n := by
  obtain ⟨k, hk⟩ := s.odd
  omega

theorem isSylowTwoOf_inf : IsSylowTwoOf (T ⊓ L) L :=
  A4.isSylowTwoOf_inf_normal (s.hyp.hyp.toHyp5_0_1.isSylowTwoOf le_sup_right) le_sup_left
    s.hyp.hyp.toHyp5_0_1.sup_le_normalizer

theorem nonempty_coord : Nonempty (OddCoord T L V n) :=
  s.natural.nonempty_oddCoord s.one_le_n s.isSylowTwoOf_inf

theorem exists_inf_conj_eq (hI : L2OddInnerFact) {t : G} (ht : t ∈ T) :
    ∃ l ∈ T ⊓ L, ∀ v ∈ V, t * v * t⁻¹ = l * v * l⁻¹ := by
  have hh := s.hyp.hyp.toHyp5_0_1
  obtain ⟨l, hl, q, hq, rfl⟩ := hh.exists_eq_mul_of_odd hI s.odd ht
  have hqC : q ∈ Subgroup.centralizer (V : Set G) := by
    rw [← hh.centralizer_eq_pCoreOf s.hyp.module] at hq
    exact hq.2
  refine ⟨l, hl, fun v hv => ?_⟩
  have hvq : v * q = q * v := Subgroup.mem_centralizer_iff.mp hqC v hv
  calc l * q * v * (l * q)⁻¹ = l * (q * v * q⁻¹) * l⁻¹ := by group
    _ = l * v * l⁻¹ := by rw [← hvq, mul_inv_cancel_right]

omit s in
theorem normalizer_le_normalizer_Z :
    Subgroup.normalizer (T : Set G) ≤
      Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := by
  intro g hg
  apply mem_normalizer_of_forall_conj_mem'
  intro z hz
  obtain ⟨hzT, hzC, hz2⟩ := mem_quasithinOmegaOneCenter_iff.mp hz
  refine mem_quasithinOmegaOneCenter_iff.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hzT, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have ht' : g⁻¹ * t * g ∈ T := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) t).mp ht
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hzC _ ht'
    calc t * (g * z * g⁻¹) = g * ((g⁻¹ * t * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * t * g)) * g⁻¹ := by rw [hc]
      _ = g * z * g⁻¹ * t := by group
  · rw [conj_pow, hz2, mul_one, mul_inv_cancel]

omit [Finite G] s in
theorem T_le_centralizer_Z₁ :
    T ≤ Subgroup.centralizer ((quasithinOmegaOneCenter T ⊓ V : Subgroup G) : Set G) := by
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact ((mem_quasithinOmegaOneCenter_iff.mp hz.1).2.1 |> Subgroup.mem_centralizer_iff.mp) t ht
    |>.symm

theorem D_le_normalizer_Z₁ (hI : L2OddInnerFact) :
    D ≤ Subgroup.normalizer ((quasithinOmegaOneCenter T ⊓ V : Subgroup G) : Set G) := by
  have hh := s.hyp.hyp.toHyp5_0_1
  have hDT : D ≤ Subgroup.normalizer (T : Set G) :=
    s.hyp.notation59.2.1.1.trans (hh.borelL_le_normalizer_T_of_odd hI s.odd)
  have hDL : D ≤ L := s.hyp.notation59.2.1.1.trans inf_le_left
  intro d hd
  apply mem_normalizer_of_forall_conj_mem'
  intro z hz
  exact ⟨(Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_Z (hDT hd)) z).mp hz.1,
    (Subgroup.mem_normalizer_iff.mp (s.L_le_normalizer_V (hDL hd)) z).mp hz.2⟩

theorem mem_Z_iff (hI : L2OddInnerFact) (c : OddCoord T L V n) (v : ↥V) :
    (v : G) ∈ quasithinOmegaOneCenter T ↔ c.ε v 1 = 0 := by
  constructor
  · intro hv
    obtain ⟨g, hg, hgb⟩ := c.unip_surj 1
    have hgv : (g : G) * v * (g : G)⁻¹ = v := by
      have := Subgroup.mem_centralizer_iff.mp (mem_quasithinOmegaOneCenter_iff.mp hv).2.1 g hg.1
      rw [this, mul_inv_cancel_right]
    have h1 := (c.conj_eq_iff g v).mp hgv
    rw [hgb, coe_unipSL, unipSL_mulVec, one_mul] at h1
    have h2 := congrFun h1 0
    simp only [Matrix.cons_val_zero] at h2
    linear_combination h2
  · intro hv
    refine mem_quasithinOmegaOneCenter_iff.mpr ⟨s.le_T v.2, ?_, s.elemAbelian.2 v v.2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    obtain ⟨l, hl, hlt⟩ := s.exists_inf_conj_eq hI ht
    obtain ⟨b, hb⟩ := c.unip ⟨l, s.L_le_normalizer_V hl.2⟩ hl
    have hlv : l * v * l⁻¹ = v := by
      refine (c.conj_eq_iff ⟨l, s.L_le_normalizer_V hl.2⟩ v).mpr ?_
      rw [hb, coe_unipSL, unipSL_mulVec, hv, mul_zero, add_zero]
      funext i
      fin_cases i
      · rfl
      · exact hv.symm
    have htv : t * v * t⁻¹ = v := (hlt v v.2).trans hlv
    calc t * v = (t * v * t⁻¹) * t := by group
      _ = v * t := by rw [htv]

theorem exists_mat_of_normalizer (hI : L2OddInnerFact) (c : OddCoord T L V n)
    (g : Subgroup.normalizer (V : Set G)) (hgL : (g : G) ∈ L)
    (hgZ : (g : G) ∈ Subgroup.normalizer
      ((quasithinOmegaOneCenter T ⊓ V : Subgroup G) : Set G)) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) c.K, (A : Matrix (Fin 2) (Fin 2) c.K) 1 0 = 0 ∧
      ∀ w, c.act g w = (A : Matrix (Fin 2) (Fin 2) c.K).mulVec w := by
  obtain ⟨A, hA⟩ := c.mat g hgL
  refine ⟨A, ?_, hA⟩
  obtain ⟨v, hv⟩ := c.ε_bij.2 ![1, 0]
  have hvZ : (v : G) ∈ quasithinOmegaOneCenter T := (s.mem_Z_iff hI c v).mpr (by rw [hv]; rfl)
  have hgv : (g : G) * v * (g : G)⁻¹ ∈ quasithinOmegaOneCenter T :=
    ((Subgroup.mem_normalizer_iff.mp hgZ v).mp ⟨hvZ, v.2⟩).1
  have h1 : c.ε (conjAct V g v) 1 = 0 :=
    (s.mem_Z_iff hI c _).mp (by rw [conjAct_apply_coe]; exact hgv)
  rw [← c.act_ε, hv, hA] at h1
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h1

omit s in
theorem mul_eq_one_of_lower {K : Type} [Field K] (A : Matrix.SpecialLinearGroup (Fin 2) K)
    (h : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (A : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
  have hdet := A.2
  rw [Matrix.det_fin_two, h, mul_zero, sub_zero] at hdet
  exact hdet

omit s in
theorem eq_unipSL_of_lower {K : Type} [Field K] (A : Matrix.SpecialLinearGroup (Fin 2) K)
    (h : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (h1 : (A : Matrix (Fin 2) (Fin 2) K) 1 1 = 1) :
    A = unipSL ((A : Matrix (Fin 2) (Fin 2) K) 0 1) := by
  have h0 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have := mul_eq_one_of_lower A h
    rwa [h1, mul_one] at this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_unipSL, h, h0, h1]

theorem exists_D_act_eq (hI : L2OddInnerFact) (hF : L2TorusFact) (c : OddCoord T L V n)
    {μ : c.K} (hμ : μ ≠ 0) :
    ∃ d : Subgroup.normalizer (V : Set G), (d : G) ∈ D ∧ ∀ w, (c.act d w) 1 = μ * w 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  have hDL : D ≤ L := s.hyp.notation59.2.1.1.trans inf_le_left
  have hDZ := s.D_le_normalizer_Z₁ hI
  let nd : ↥D → Subgroup.normalizer (V : Set G) := fun d => ⟨d, s.L_le_normalizer_V (hDL d.2)⟩
  have hA : ∀ d : ↥D, ∃ A : Matrix.SpecialLinearGroup (Fin 2) c.K,
      (A : Matrix (Fin 2) (Fin 2) c.K) 1 0 = 0 ∧
        ∀ w, c.act (nd d) w = (A : Matrix (Fin 2) (Fin 2) c.K).mulVec w :=
    fun d => s.exists_mat_of_normalizer hI c (nd d) (hDL d.2) (hDZ d.2)
  choose A hA0 hAact using hA
  have hact1 : ∀ d : ↥D, ∀ w, (c.act (nd d) w) 1 = (A d : Matrix (Fin 2) (Fin 2) c.K) 1 1 * w 1 :=
    fun d w => by rw [hAact, mulVec_one_of_lower _ (hA0 d)]
  have hne : ∀ d : ↥D, (A d : Matrix (Fin 2) (Fin 2) c.K) 1 1 ≠ 0 := fun d h0 => by
    have := mul_eq_one_of_lower (A d) (hA0 d)
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have hmul : ∀ d d' : ↥D, (A (d * d') : Matrix (Fin 2) (Fin 2) c.K) 1 1 =
      (A d : Matrix (Fin 2) (Fin 2) c.K) 1 1 * (A d' : Matrix (Fin 2) (Fin 2) c.K) 1 1 := by
    intro d d'
    have h1 := hact1 (d * d') ![0, 1]
    have h2 : c.act (nd (d * d')) ![0, 1] = c.act (nd d) (c.act (nd d') ![0, 1]) := by
      rw [← c.act_mul]
      rfl
    rw [h2, hact1, hact1] at h1
    simpa using h1.symm
  let χ : ↥D → c.Kˣ := fun d => Units.mk0 _ (hne d)
  have hχi : Function.Injective χ := by
    intro d d' hdd
    have h11 : (A d : Matrix (Fin 2) (Fin 2) c.K) 1 1 = (A d' : Matrix (Fin 2) (Fin 2) c.K) 1 1 :=
      congrArg Units.val hdd
    set x := d⁻¹ * d' with hx
    have hone : (A 1 : Matrix (Fin 2) (Fin 2) c.K) 1 1 = 1 := by
      have h1 := hact1 1 ![0, 1]
      have h2 : c.act (nd 1) ![0, 1] = ![0, 1] := c.act_one _
      rw [h2] at h1
      simpa using h1.symm
    have hx11 : (A x : Matrix (Fin 2) (Fin 2) c.K) 1 1 = 1 := by
      have h1 := hmul d x
      rw [hx, mul_inv_cancel_left, ← h11] at h1
      have h2 : (A d : Matrix (Fin 2) (Fin 2) c.K) 1 1 * 1 =
          (A d : Matrix (Fin 2) (Fin 2) c.K) 1 1 * (A x : Matrix (Fin 2) (Fin 2) c.K) 1 1 := by
        rw [mul_one]; exact h1
      exact (mul_left_cancel₀ (hne d) h2).symm
    have hxu := eq_unipSL_of_lower (A x) (hA0 x) hx11
    have hx2C : ((x * x : ↥D) : G) ∈ Subgroup.centralizer (V : Set G) := by
      have hc := (c.mem_centralizer_iff (nd (x * x))).mpr fun w => by
        have h1 : c.act (nd (x * x)) w = c.act (nd x) (c.act (nd x) w) := by
          rw [← c.act_mul]
          rfl
        rw [h1, hAact, hAact, hxu, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
          Vol2.Ch10.SecA.unipSL_mul_self, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
      exact hc
    have hx2O : ((x * x : ↥D) : G) ∈ pCoreOf 2 L :=
      hh.inf_centralizer_le s.L_le_normalizer_V s.hyp.module.2.2 ⟨hDL (x * x).2, hx2C⟩
    have hxodd : Odd (orderOf x) := Odd.of_dvd_nat s.hyp.notation59.2.1.2.1 (orderOf_dvd_natCard x)
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 L) ⟨_, hx2O⟩
    have hk' : (x * x) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have hx1 : x = 1 := by
      have h1 : orderOf x ∣ 2 * 2 ^ k := by
        apply orderOf_dvd_of_pow_eq_one
        rw [pow_mul, sq, hk']
      have h2 : Nat.Coprime (orderOf x) (2 * 2 ^ k) :=
        Nat.Coprime.mul_right (Nat.coprime_two_right.mpr hxodd)
          (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hxodd))
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h2 h1)
    rw [hx] at hx1
    exact (inv_mul_eq_one.mp hx1)
  have hcardD : Nat.card D = 2 ^ n - 1 := (hh.isCyclic_card_of_isHall hF s.hyp.notation59.2.1).2
  have hcardK : Nat.card c.Kˣ = 2 ^ n - 1 := by rw [Nat.card_units, c.card]
  have hχb : Function.Bijective χ := hχi.bijective_of_nat_card_le (by rw [hcardD, hcardK])
  obtain ⟨d, hd⟩ := hχb.2 (Units.mk0 μ hμ)
  refine ⟨nd d, d.2, fun w => ?_⟩
  rw [hact1]
  congr 1
  exact congrArg Units.val hd

theorem Z₁_ne_bot : quasithinOmegaOneCenter T ⊓ V ≠ ⊥ := by
  have hh := s.hyp.hyp.toHyp5_0_1
  obtain ⟨z, hzV, hz1, hzT⟩ := exists_ne_one_mem_centralizer (hh.isSylowTwoOf le_top).2.1 s.le_T
    s.T_le_normalizer s.natural.ne_bot
  intro hb
  have hzZ : z ∈ quasithinOmegaOneCenter T ⊓ V :=
    ⟨mem_quasithinOmegaOneCenter_iff.mpr ⟨s.le_T hzV, hzT, s.elemAbelian.2 z hzV⟩, hzV⟩
  rw [hb, Subgroup.mem_bot] at hzZ
  exact hz1 hzZ

theorem not_three_dvd : ¬ 3 ∣ 2 ^ n - 1 := by
  obtain ⟨k, hk⟩ := s.odd
  rw [hk, pow_succ, pow_mul]
  have h4 : 4 ^ k % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have hpos : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  norm_num
  omega

theorem B_le_centralizer (h5114 : Stmt5_1_14_first) (hI : L2OddInnerFact) (hB3 : Nat.card B ∣ 3)
    (c : OddCoord T L V n) : B ≤ Subgroup.centralizer (V : Set G) := by
  have hh := s.hyp.hyp.toHyp5_0_1
  intro b hb
  have hbM : b ∈ M := (s.hyp.notation59.1.1 hb).1
  have hbH : b ∈ H := (s.hyp.notation59.1.1 hb).2
  have hZH := (h5114 G T M L V H B D n s.hyp.hyp s.hyp.notation59 s.hyp.module s.hyp.l34).2.1.1
  have hbZ : ∀ z ∈ quasithinOmegaOneCenter T, b * z * b⁻¹ = z := by
    intro z hz
    have hc : ⁅z, b⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator hz hbH
      rw [hZH, Subgroup.mem_bot] at this
      exact this
    rw [commutatorElement_eq_one_iff_mul_comm] at hc
    rw [← hc, mul_inv_cancel_right]
  have hbV : b ∈ Subgroup.normalizer (V : Set G) := by
    by_contra hbV
    have hti := s.ti b hbM hbV
    obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp s.Z₁_ne_bot
    have hzc : z ∈ CFSG.conjugate V b := by
      refine ⟨z, hzZ.2, ?_⟩
      show b⁻¹ * z * b⁻¹⁻¹ = z
      have := hbZ z hzZ.1
      calc b⁻¹ * z * b⁻¹⁻¹ = b⁻¹ * (b * z * b⁻¹) * b := by rw [inv_inv, this]
        _ = z := by group
    have hmem : z ∈ V ⊓ CFSG.conjugate V b := ⟨hzZ.2, hzc⟩
    rw [hti, Subgroup.mem_bot] at hmem
    exact hz1 (Subtype.ext hmem)
  have hbL : b ∈ Subgroup.normalizer (L : Set G) := hh.normal hbM
  set bn : Subgroup.normalizer (V : Set G) := ⟨b, hbV⟩ with hbn
  obtain ⟨σ, hσ⟩ := c.semi bn hbL
  have hfix : ∀ x : c.K, c.act bn ![x, 0] = ![x, 0] := by
    intro x
    obtain ⟨v, hv⟩ := c.ε_bij.2 ![x, 0]
    have hvZ := (s.mem_Z_iff hI c v).mpr (by rw [hv]; rfl)
    rw [← hv]
    exact (c.conj_eq_iff bn v).mp (hbZ v hvZ)
  have hσ1 : ∀ a : c.K, σ a = a := by
    intro a
    have h1 := hσ a ![1, 0]
    have e1 : a • (![1, 0] : Fin 2 → c.K) = ![a, 0] := by
      funext i
      fin_cases i <;> simp
    rw [e1, hfix, hfix] at h1
    have := congrFun h1 0
    simp at this
    exact this.symm
  set u := c.act bn ![0, 1] with hu
  have hlin : ∀ w : Fin 2 → c.K, c.act bn w = ![w 0 + w 1 * u 0, w 1 * u 1] := by
    intro w
    have hw : c.act bn w = c.act bn (w 0 • ![1, 0] + w 1 • ![0, 1]) := by
      congr 1
      funext i
      fin_cases i <;> simp
    rw [hw, c.act_add, hσ, hσ, hσ1, hσ1, hfix, ← hu]
    funext i
    fin_cases i <;> simp
  have hb3 : b ^ 3 = 1 := by
    have h1 : orderOf b ∣ 3 := by
      rw [← Subgroup.orderOf_mk b hb]
      exact (orderOf_dvd_natCard _).trans hB3
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hbn3 : bn * bn * bn = 1 := Subtype.ext (by
    show b * b * b = 1
    rw [← pow_three']
    exact hb3)
  have h3 : c.act bn (c.act bn (c.act bn ![0, 1])) = ![0, 1] := by
    rw [← c.act_mul, ← c.act_mul, hbn3, c.act_one]
  rw [hlin, hlin, hlin] at h3
  have hu1 : u 1 * u 1 * u 1 = 1 := by
    have := congrFun h3 1
    simpa using this
  have hu0 : u 0 + u 1 * u 0 + u 1 * u 1 * u 0 = 0 := by
    have := congrFun h3 0
    simp at this
    linear_combination this
  have hγ : u 1 = 1 := by
    have hne : u 1 ≠ 0 := fun h0 => by simp [h0] at hu1
    set γ := Units.mk0 (u 1) hne with hγdef
    have hγ3 : γ ^ 3 = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, hγdef, Units.val_mk0, Units.val_one, pow_three']
      exact hu1)
    have h1 : orderOf γ ∣ 3 := orderOf_dvd_of_pow_eq_one hγ3
    have h2 : orderOf γ ∣ 2 ^ n - 1 := by
      rw [← c.card, ← Nat.card_units]
      exact orderOf_dvd_natCard γ
    have h3' : orderOf γ = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
      · exact h
      · exact absurd (h ▸ h2) s.not_three_dvd
    have := congrArg Units.val (orderOf_eq_one_iff.mp h3')
    simpa [hγdef] using this
  have hu0' : u 0 = 0 := by
    rw [hγ] at hu0
    have h2 : (2 : c.K) = 0 := CharP.cast_eq_zero c.K 2
    linear_combination hu0 - u 0 * h2
  refine (c.mem_centralizer_iff bn).mpr fun w => ?_
  rw [hlin, hγ, hu0', mul_zero, add_zero, mul_one]
  funext i
  fin_cases i <;> rfl

theorem T_act_snd (hI : L2OddInnerFact) (c : OddCoord T L V n)
    (t : Subgroup.normalizer (V : Set G)) (ht : (t : G) ∈ T) (w : Fin 2 → c.K) :
    (c.act t w) 1 = w 1 := by
  obtain ⟨l, hl, hlt⟩ := s.exists_inf_conj_eq hI ht
  obtain ⟨b, hb⟩ := c.unip ⟨l, s.L_le_normalizer_V hl.2⟩ hl
  rw [c.act_eq_of_conj_eq (h := ⟨l, s.L_le_normalizer_V hl.2⟩) hlt, hb, coe_unipSL,
    unipSL_mulVec]
  rfl

theorem inf_normalizer_le (hI : L2OddInnerFact) (hF : L2TorusFact) (c : OddCoord T L V n) :
    L ⊓ Subgroup.normalizer ((quasithinOmegaOneCenter T ⊓ V : Subgroup G) : Set G) ≤ T ⊔ D := by
  have hh := s.hyp.hyp.toHyp5_0_1
  have hDL : D ≤ L := s.hyp.notation59.2.1.1.trans inf_le_left
  intro x hx
  set xn : Subgroup.normalizer (V : Set G) := ⟨x, s.L_le_normalizer_V hx.1⟩ with hxn
  obtain ⟨A, hA0, hA⟩ := s.exists_mat_of_normalizer hI c xn hx.1 hx.2
  have hA11 : (A : Matrix (Fin 2) (Fin 2) c.K) 1 1 ≠ 0 := fun h0 => by
    have := mul_eq_one_of_lower A hA0
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  obtain ⟨d, hdD, hd⟩ := s.exists_D_act_eq hI hF c (inv_ne_zero hA11)
  set yn := d * xn with hyn
  have hyL : (yn : G) ∈ L := L.mul_mem (hDL hdD) hx.1
  have hyZ : (yn : G) ∈ Subgroup.normalizer
      ((quasithinOmegaOneCenter T ⊓ V : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ (s.D_le_normalizer_Z₁ hI hdD) hx.2
  obtain ⟨B', hB0, hB⟩ := s.exists_mat_of_normalizer hI c yn hyL hyZ
  have hB11 : (B' : Matrix (Fin 2) (Fin 2) c.K) 1 1 = 1 := by
    have h1 : (c.act yn ![0, 1]) 1 = 1 := by
      rw [hyn, c.act_mul, hd, hA, mulVec_one_of_lower _ hA0]
      simp [inv_mul_cancel₀ hA11]
    rw [hB, mulVec_one_of_lower _ hB0] at h1
    simpa using h1
  have hBu := eq_unipSL_of_lower B' hB0 hB11
  obtain ⟨l, hl, hlb⟩ := c.unip_surj ((B' : Matrix (Fin 2) (Fin 2) c.K) 0 1)
  have hC : ((l⁻¹ * yn : Subgroup.normalizer (V : Set G)) : G) ∈
      Subgroup.centralizer (V : Set G) := by
    refine (c.mem_centralizer_iff _).mpr fun w => ?_
    have h1 : c.act yn w = c.act l w := by rw [hB, hlb, ← hBu]
    rw [c.act_mul, h1, ← c.act_mul, inv_mul_cancel, c.act_one]
  have hO : ((l⁻¹ * yn : Subgroup.normalizer (V : Set G)) : G) ∈ T := by
    have hmemL : ((l⁻¹ * yn : Subgroup.normalizer (V : Set G)) : G) ∈ L :=
      L.mul_mem (L.inv_mem hl.2) hyL
    have := hh.inf_centralizer_le s.L_le_normalizer_V s.hyp.module.2.2 ⟨hmemL, hC⟩
    exact (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf s.isSylowTwoOf_inf this).1
  have hx' : x = (d : G)⁻¹ * ((l : G) * ((l⁻¹ * yn : Subgroup.normalizer (V : Set G)) : G)) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hyn, hxn]
    group
  rw [hx']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (D.inv_mem hdD))
    (Subgroup.mem_sup_left (T.mul_mem hl.1 hO))

theorem D_eq_one_of_act (hI : L2OddInnerFact) (c : OddCoord T L V n)
    {d : Subgroup.normalizer (V : Set G)} (hd : (d : G) ∈ D) (h : ∀ w, (c.act d w) 1 = w 1) :
    (d : G) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  have hDL : D ≤ L := s.hyp.notation59.2.1.1.trans inf_le_left
  obtain ⟨A, hA0, hA⟩ := s.exists_mat_of_normalizer hI c d (hDL hd) (s.D_le_normalizer_Z₁ hI hd)
  have hA11 : (A : Matrix (Fin 2) (Fin 2) c.K) 1 1 = 1 := by
    have h1 := h ![0, 1]
    rw [hA, mulVec_one_of_lower _ hA0] at h1
    simpa using h1
  have hAu := eq_unipSL_of_lower A hA0 hA11
  have hC : ((d * d : Subgroup.normalizer (V : Set G)) : G) ∈ Subgroup.centralizer (V : Set G) := by
    refine (c.mem_centralizer_iff _).mpr fun w => ?_
    rw [c.act_mul, hA, hA, hAu, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
      Vol2.Ch10.SecA.unipSL_mul_self, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have hO : (d : G) * d ∈ pCoreOf 2 L :=
    hh.inf_centralizer_le s.L_le_normalizer_V s.hyp.module.2.2 ⟨L.mul_mem (hDL hd) (hDL hd), hC⟩
  have hdodd : Odd (orderOf (d : G)) := by
    have h1 : orderOf (d : G) ∣ Nat.card D := by
      rw [← Subgroup.orderOf_mk (d : G) hd]
      exact orderOf_dvd_natCard _
    exact Odd.of_dvd_nat s.hyp.notation59.2.1.2.1 h1
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 L) ⟨_, hO⟩
  have hk' : ((d : G) * d) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf (d : G) ∣ 2 * 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, sq, hk']
  have h2 : Nat.Coprime (orderOf (d : G)) (2 * 2 ^ k) :=
    Nat.Coprime.mul_right (Nat.coprime_two_right.mpr hdodd)
      (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hdodd))
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h2 h1)

theorem exists_mem_T_mem_B {x : G} (hx : x ∈ M ⊓ H) : ∃ t ∈ T, ∃ b ∈ B, x = t * b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  have hTMH : T ≤ M ⊓ H := le_inf hh.T_le s.hyp.hyp.hStar.1.1
  have hSylMH : IsSylowTwoOf T (M ⊓ H) := hh.isSylowTwoOf hTMH
  obtain ⟨hBle, hBodd, k, hk⟩ := s.hyp.notation59.1
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hSylMH.2.1
  have hcardMH : Nat.card ↥(M ⊓ H) = Nat.card T * Nat.card B := by
    have e1 := B.relIndex_mul_card (K := M ⊓ H)
    rw [inf_eq_left.mpr hBle, hk] at e1
    have e2 := T.relIndex_mul_card (K := M ⊓ H)
    rw [inf_eq_left.mpr hTMH, hm] at e2
    have hodd2 : Odd (T.relIndex (M ⊓ H)) :=
      Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hSylMH.2.2)
    obtain ⟨hkm, -⟩ := two_pow_mul_odd_inj (a := k) (b := m) hBodd hodd2
      (by rw [e1, ← e2, mul_comm])
    rw [← e1, hkm, hm]
  have hTB : T ⊓ B = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hm]
    exact Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hBodd)
  let f : ↥T × ↥B → ↥(M ⊓ H) := fun p => ⟨(p.1 : G) * p.2,
    (M ⊓ H).mul_mem (hTMH p.1.2) (hBle p.2.2)⟩
  have hfi : Function.Injective f := by
    rintro ⟨t, b⟩ ⟨t', b'⟩ h
    have h1 : (t : G) * b = t' * b' := congrArg Subtype.val h
    have h2 : (t' : G)⁻¹ * t = b' * (b : G)⁻¹ := by
      calc (t' : G)⁻¹ * t = (t' : G)⁻¹ * (t * b) * (b : G)⁻¹ := by group
        _ = (t' : G)⁻¹ * (t' * b') * (b : G)⁻¹ := by rw [h1]
        _ = b' * (b : G)⁻¹ := by group
    have hmem : (t' : G)⁻¹ * t ∈ T ⊓ B :=
      ⟨T.mul_mem (T.inv_mem t'.2) t.2, by rw [h2]; exact B.mul_mem b'.2 (B.inv_mem b.2)⟩
    rw [hTB, Subgroup.mem_bot] at hmem
    have ht : (t : G) = t' := by
      have : (t : G) = t' * ((t' : G)⁻¹ * t) := by group
      rw [this, hmem, mul_one]
    have hb : (b : G) = b' := by
      rw [ht] at h1
      exact mul_left_cancel h1
    exact Prod.ext (Subtype.ext ht) (Subtype.ext hb)
  have hfb : Function.Bijective f :=
    hfi.bijective_of_nat_card_le (by rw [Nat.card_prod, hcardMH])
  obtain ⟨⟨t, b⟩, hp⟩ := hfb.2 ⟨x, hx⟩
  exact ⟨t, t.2, b, b.2, (congrArg Subtype.val hp).symm⟩

theorem eq_M (h323 : Stmt3_2_3) {M' : Subgroup G} (hM' : quasithinIsMaxTwoLocal M')
    (hLT : L ⊔ T ≤ M') : M' = M := by
  have hh := s.hyp.hyp.toHyp5_0_1
  obtain ⟨-, ⟨-, huniq⟩, -⟩ := h323 G T L hh.simple hh.nonabelian hh.qtke hh.sylow hh.maximal
    hh.faithful hh.isQuasisimple
  rw [hh.conjClosure_eq] at huniq
  rw [huniq M' hM' hLT, huniq M hh.maxTwoLocal hh.sup_le_M]

theorem normalizer_V_le_M (h323 : Stmt3_2_3) : Subgroup.normalizer (V : Set G) ≤ M := by
  have hloc : IsTwoLocal (Subgroup.normalizer (V : Set G)) :=
    ⟨V, s.natural.ne_bot, isPGroup_of_isElemAbelian s.elemAbelian, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  rw [← s.eq_M h323 hM' (s.le_normalizer_V.trans hle)]
  exact hle

theorem hypF81
    (h5114 : Stmt5_1_14_first) (hI : L2OddInnerFact) (hF : L2TorusFact)
    (h323 : Stmt3_2_3) (hB3 : Nat.card B ∣ 3)
    (hTI : IsTISetUnder (quasithinOmegaOneCenter T ⊓ V) ⊤)
    (habel : ∀ H₁ : Subgroup G, H ⊔ D ≤ H₁ →
      H₁ ≤ Subgroup.normalizer ((quasithinOmegaOneCenter T ⊓ V : Subgroup G) : Set G) →
      IsElemAbelian 2 (conjClosure V H₁)) :
    HypF81 T V L (quasithinOmegaOneCenter T ⊓ V) (H ⊔ D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c⟩ := s.nonempty_coord
  have hh := s.hyp.hyp.toHyp5_0_1
  set Z := quasithinOmegaOneCenter T with hZdef
  set Z₁ := Z ⊓ V with hZ₁def
  set K := oTwoUpper H with hKdef
  have hDL : D ≤ L := s.hyp.notation59.2.1.1.trans inf_le_left
  have hTH : T ≤ H := s.hyp.hyp.hStar.1.1
  have hZH := (h5114 G T M L V H B D n s.hyp.hyp s.hyp.notation59 s.hyp.module s.hyp.l34).2.1.1
  have hHZ : H ≤ Subgroup.centralizer (Z : Set G) := by
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZH
    exact Subgroup.le_centralizer_iff.mp this
  have hHZ₁ : H ≤ Subgroup.normalizer (Z₁ : Set G) := by
    intro x hx
    apply mem_normalizer_of_forall_conj_mem'
    intro z hz
    have : x * z * x⁻¹ = z := by
      have := Subgroup.mem_centralizer_iff.mp (hHZ hx) z hz.1
      rw [← this, mul_inv_cancel_right]
    rw [this]
    exact hz
  have hH₁Z : H ⊔ D ≤ Subgroup.normalizer (Z₁ : Set G) := sup_le hHZ₁ (s.D_le_normalizer_Z₁ hI)
  have hVL : V ≤ L := by
    have h1 := s.natural.commutator_eq
    rw [← h1, Subgroup.commutator_le]
    intro v hv l hl
    rw [commutatorElement_def]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hh.T_le_normalizer (s.le_T hv)) l).mp hl)
      (L.inv_mem hl)
  have hV2 : IsPGroup 2 V := isPGroup_of_isElemAbelian s.elemAbelian
  have hVO : V ≤ pCoreOf 2 L := le_pCoreOf_of_le_normalizer 2 hVL s.L_le_normalizer_V hV2
  have hHM : ¬ H ≤ M := s.hyp.hyp.hStar.2.1
  have hmemZ₁ : ∀ v : ↥V, (v : G) ∈ Z₁ ↔ c.ε v 1 = 0 := fun v =>
    ⟨fun h => (s.mem_Z_iff hI c v).mp h.1, fun h => ⟨(s.mem_Z_iff hI c v).mpr h, v.2⟩⟩
  have hεinv : ∀ v w : ↥V, c.ε (v * w⁻¹) = c.ε v - c.ε w := fun v w => by
    have := c.ε_mul (v * w⁻¹) w
    rw [inv_mul_cancel_right] at this
    rw [this]
    abel
  refine
    { sylow := hh.isSylowTwoOf le_top
      elemAbelian := s.elemAbelian
      normalizes_L := hh.T_le_normalizer
      oTwoRes_eq := ?_
      charTwo_L := ?_
      reduced := s.hyp.module.isTwoReducedIn
      cT := hh.centralizer_eq_pCoreOf s.hyp.module
      V₁_ne_bot := s.Z₁_ne_bot
      V₁_le_V := inf_le_right
      T_normalizes_V₁ := T_le_centralizer_Z₁.trans (Subgroup.centralizer_le_normalizer _)
      weak_a := ?_
      V₁_lt_V := ?_
      irred := ?_
      H_normalizes_V₁ := hH₁Z
      L₁T_le_H := ?_
      charTwo_H := ?_
      ker_le := ?_
      o2_trivial := ?_ }
  ·
    rw [oTwoRes_eq_oTwoUpper]
    exact hh.faithful.2.1 _ (oTwoUpper_le L)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le L)).mpr
        (le_normalizer_oTwoUpper L)) fun x hx => exists_pow_mem_oTwoUpper L hx
  ·
    intro x hx
    exact hh.inf_centralizer_le s.L_le_normalizer_V s.hyp.module.2.2
      ⟨hx.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVO) hx.2⟩
  ·
    intro g hg
    obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hg
    have hy1' : y ≠ 1 := fun e => hy1 (Subtype.ext e)
    obtain ⟨hyZ, hyV⟩ := Subgroup.mem_inf.mp hy
    rw [mem_conjSub, inv_inv] at hyV
    have hw1 : g * y * g⁻¹ ≠ 1 := by
      intro hw
      apply hy1'
      have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
      rw [this, hw]; group
    obtain ⟨l, hl, hlw⟩ := s.natural.exists_conj_eq hyV hyZ.2 hw1 hy1'
    set x := l * g with hx
    have hxy : x * y * x⁻¹ = y := by
      rw [show x * y * x⁻¹ = l * (g * y * g⁻¹) * l⁻¹ by rw [hx]; group, hlw]
    have hxN : x ∈ Subgroup.normalizer (Z₁ : Set G) := by
      by_contra hxN
      have hti := hTI x (Subgroup.mem_top x) hxN
      have hmem : y ∈ Z₁ ⊓ CFSG.conjugate Z₁ x := by
        refine ⟨hyZ, y, hyZ, ?_⟩
        show x⁻¹ * y * x⁻¹⁻¹ = y
        calc x⁻¹ * y * x⁻¹⁻¹ = x⁻¹ * (x * y * x⁻¹) * x := by rw [inv_inv, hxy]
          _ = y := by group
      rw [hti, Subgroup.mem_bot] at hmem
      exact hy1' hmem
    have hconj : conjSub g⁻¹ V = conjSub x⁻¹ V := by
      ext u
      rw [mem_conjSub, mem_conjSub, inv_inv, inv_inv]
      have hlV := s.L_le_normalizer_V hl
      constructor
      · intro hu
        have := (Subgroup.mem_normalizer_iff.mp hlV _).mp hu
        rwa [show l * (g * u * g⁻¹) * l⁻¹ = x * u * x⁻¹ by rw [hx]; group] at this
      · intro hu
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlV) _).mp hu
        rwa [show l⁻¹ * (x * u * x⁻¹) * l⁻¹⁻¹ = g * u * g⁻¹ by rw [hx]; group] at this
    have hab := habel _ hH₁Z le_rfl
    rw [hconj, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : w ∈ conjClosure V (Subgroup.normalizer (Z₁ : Set G)) := by
      rw [SetLike.mem_coe, mem_conjSub, inv_inv] at hw
      have := mem_conjClosure (Subgroup.inv_mem _ hxN) hw
      rwa [show x⁻¹ * (x * w * x⁻¹) * x⁻¹⁻¹ = w by group] at this
    have hv' : v ∈ conjClosure V (Subgroup.normalizer (Z₁ : Set G)) := le_conjClosure V _ hv
    have := hab.1
    have := mul_comm (⟨w, hw'⟩ : ↥(conjClosure V (Subgroup.normalizer (Z₁ : Set G)))) ⟨v, hv'⟩
    exact congrArg Subtype.val this
  ·
    refine lt_of_le_of_ne inf_le_right fun heq => ?_
    obtain ⟨v, hv⟩ := c.ε_bij.2 ![0, 1]
    have hvZ : (v : G) ∈ Z₁ := by rw [heq]; exact v.2
    have := (hmemZ₁ v).mp hvZ
    rw [hv] at this
    exact one_ne_zero this
  ·
    intro W hW1 hW2 hWN
    have hDW : D ≤ Subgroup.normalizer (W : Set G) := by
      intro d hd
      refine hWN (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨⟨hDL hd,
        s.D_le_normalizer_Z₁ hI hd⟩, orderOf d, ?_, pow_orderOf_eq_one d⟩))
      have h1 : orderOf d ∣ Nat.card D := by
        rw [← Subgroup.orderOf_mk d hd]
        exact orderOf_dvd_natCard _
      exact Odd.of_dvd_nat s.hyp.notation59.2.1.2.1 h1
    by_cases hWZ : W = Z₁
    · exact Or.inl hWZ
    right
    obtain ⟨w, hwW, hwZ⟩ : ∃ w ∈ W, w ∉ Z₁ := by
      by_contra hcon
      exact hWZ (le_antisymm (fun w hw => by
        by_contra hw'
        exact hcon ⟨w, hw, hw'⟩) hW1)
    have hwV : w ∈ V := hW2 hwW
    have hw1 : c.ε ⟨w, hwV⟩ 1 ≠ 0 := fun h0 => hwZ ((hmemZ₁ ⟨w, hwV⟩).mpr h0)
    refine le_antisymm hW2 fun v hv => ?_
    by_cases hv1 : c.ε ⟨v, hv⟩ 1 = 0
    · exact hW1 ((hmemZ₁ ⟨v, hv⟩).mpr hv1)
    obtain ⟨d, hdD, hd⟩ := s.exists_D_act_eq hI hF c (div_ne_zero hv1 hw1)
    have hdw : (d : G) * w * (d : G)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hDW hdD) w).mp hwW
    have hdwV : (d : G) * w * (d : G)⁻¹ ∈ V := hW2 hdw
    have hε : c.ε ⟨(d : G) * w * (d : G)⁻¹, hdwV⟩ 1 = c.ε ⟨v, hv⟩ 1 := by
      have h1 : c.ε ⟨(d : G) * w * (d : G)⁻¹, hdwV⟩ = c.act d (c.ε ⟨w, hwV⟩) := by
        rw [c.act_ε]
        exact congrArg c.ε (Subtype.ext (by rw [conjAct_apply_coe]))
      rw [h1, hd, div_mul_cancel₀ _ hw1]
    have hq : v * ((d : G) * w * (d : G)⁻¹)⁻¹ ∈ W := by
      refine hW1 ((hmemZ₁ ⟨_, V.mul_mem hv (V.inv_mem hdwV)⟩).mpr ?_)
      have := hεinv ⟨v, hv⟩ ⟨_, hdwV⟩
      have e : (⟨v * ((d : G) * w * (d : G)⁻¹)⁻¹, V.mul_mem hv (V.inv_mem hdwV)⟩ : ↥V) =
          ⟨v, hv⟩ * (⟨_, hdwV⟩ : ↥V)⁻¹ := rfl
      rw [e, this, Pi.sub_apply, hε, sub_self]
    have := W.mul_mem hq hdw
    rwa [inv_mul_cancel_right] at this
  ·
    refine sup_le ((oTwoRes_le _).trans ((s.inf_normalizer_le hI hF c).trans
      (sup_le_sup_right hTH D))) (hTH.trans le_sup_left)
  ·
    refine charTwo_of_inH' hh.qtke hh.sylow ⟨hTH.trans le_sup_left, fun hb => ?_⟩
    have hZn : H ⊔ D ≤ Subgroup.normalizer (Z : Set G) := by
      refine sup_le (hHZ.trans (Subgroup.centralizer_le_normalizer _)) ?_
      exact s.hyp.notation59.2.1.1.trans ((hh.borelL_le_normalizer_T_of_odd hI s.odd).trans
        normalizer_le_normalizer_Z)
    have hZT : Z ≤ T := fun z hz => (mem_quasithinOmegaOneCenter_iff.mp hz).1
    have hZ2 : IsPGroup 2 Z := (hh.isSylowTwoOf le_top).2.1.to_le hZT
    have hZO : Z ≤ pCoreOf 2 (H ⊔ D) :=
      le_pCoreOf_of_le_normalizer 2 (hZT.trans (hTH.trans le_sup_left)) hZn hZ2
    rw [hb] at hZO
    exact s.Z₁_ne_bot (eq_bot_iff.mpr (inf_le_left.trans hZO))
  ·
    set N := coreIn (centralizerMod Z₁ (H ⊔ D) V) (H ⊔ D) with hNdef
    have hNH : N ≤ H ⊔ D := coreIn_le_left _ _
    have hHN : H ⊔ D ≤ Subgroup.normalizer (N : Set G) := le_normalizer_coreIn _ _
    have hNC : N ≤ centralizerMod Z₁ (H ⊔ D) V := coreIn_le_right _ _
    have hNV : ∀ y ∈ N, y ∈ Subgroup.normalizer (V : Set G) := by
      intro y hy
      obtain ⟨-, -, hyc⟩ := hNC hy
      apply mem_normalizer_of_forall_conj_mem'
      intro u hu
      have h1 : y * u * y⁻¹ = (y * u * y⁻¹ * u⁻¹) * u := by group
      rw [h1]
      exact V.mul_mem (hyc u hu).2 hu
    have hKH : K ≤ H := oTwoUpper_le H
    have hHeq : H = K ⊔ T := eq_oTwoUpper_sup_of_isSylowTwoOf' (hh.isSylowTwoOf hTH)
    have hTK : T ≤ Subgroup.normalizer (K : Set G) := hTH.trans (le_normalizer_oTwoUpper H)
    have hNK : N ⊓ K ≤ pCoreOf 2 K := by
      have hsimp : IsSimpleGroup (O2Q K) := s.hyp.isSimple_K
      have hNKK : N ⊓ K ≤ K := inf_le_right
      have hKN : K ≤ Subgroup.normalizer ((N ⊓ K : Subgroup G) : Set G) := by
        intro k hk
        apply mem_normalizer_of_forall_conj_mem'
        intro x hx
        exact ⟨(Subgroup.mem_normalizer_iff.mp (hHN (Subgroup.mem_sup_left (hKH hk))) x).mp hx.1,
          K.mul_mem (K.mul_mem hk hx.2) (K.inv_mem hk)⟩
      have hn : ((N ⊓ K).subgroupOf K).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hNKK).mpr hKN
      have hmap : (((N ⊓ K).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).Normal :=
        hn.map _ (QuotientGroup.mk'_surjective _)
      rcases hsimp.eq_bot_or_eq_top_of_normal
        (((N ⊓ K).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) with hb | ht
      · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hb
        intro x hx
        have hxP : (⟨x, hNKK hx⟩ : ↥K) ∈ CFSG.Open.pCore 2 ↥K := by
          exact hb hx
        exact ⟨_, hxP, rfl⟩
      · exfalso
        have hodd : ∀ k ∈ K, Odd (orderOf k) → k ∈ N := by
          intro k hk hko
          have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) ⟨k, hk⟩ ∈
              ((N ⊓ K).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
            rw [ht]; exact Subgroup.mem_top _
          obtain ⟨n', hn', hn'k⟩ := hmem
          have hq : n'⁻¹ * ⟨k, hk⟩ ∈ CFSG.pCore 2 ↥K := by
            rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
            change (QuotientGroup.mk' (CFSG.pCore 2 ↥K) n')⁻¹ *
              QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨k, hk⟩ = 1
            rw [hn'k, inv_mul_cancel]
          obtain ⟨j, hj⟩ := CFSG.pCore_isPGroup ⟨_, hq⟩
          set Q := (N ⊓ K).subgroupOf K with hQ
          have hk1 : ((⟨k, hk⟩ : ↥K) : ↥K ⧸ Q) ^ 2 ^ j = 1 := by
            have e : ((⟨k, hk⟩ : ↥K) : ↥K ⧸ Q) = ((n'⁻¹ * ⟨k, hk⟩ : ↥K) : ↥K ⧸ Q) := by
              rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv,
                (QuotientGroup.eq_one_iff n').mpr hn', inv_one, one_mul]
            rw [e, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
            have := congrArg Subtype.val hj
            simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
            rw [this]
            exact Q.one_mem
          have hko0 : Odd (orderOf (⟨k, hk⟩ : ↥K)) := by
            rw [Subgroup.orderOf_mk]
            exact hko
          have hko' : Odd (orderOf ((⟨k, hk⟩ : ↥K) : ↥K ⧸ Q)) :=
            Odd.of_dvd_nat hko0 (orderOf_map_dvd (QuotientGroup.mk' Q) _)
          have hk2 : orderOf ((⟨k, hk⟩ : ↥K) : ↥K ⧸ Q) = 1 := by
            have h1 := orderOf_dvd_of_pow_eq_one hk1
            exact Nat.Coprime.eq_one_of_dvd
              (Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hko')) h1
          have := (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp hk2)
          exact (Subgroup.mem_subgroupOf.mp this).1
        have hKN' : K ≤ N := by
          rw [hKdef, oTwoUpper, Subgroup.closure_le]
          rintro x ⟨hx, hxo⟩
          exact hodd x (mem_oTwoUpper_of_odd hx hxo) hxo
        apply hHM
        rw [hHeq]
        exact sup_le (fun k hk => s.normalizer_V_le_M h323 (hNV k (hKN' hk)))
          (hh.T_le)
    have hDK : D ≤ Subgroup.normalizer (K : Set G) := s.D_le_normalizer
    have hDT : D ≤ Subgroup.normalizer (T : Set G) :=
      s.hyp.notation59.2.1.1.trans (hh.borelL_le_normalizer_T_of_odd hI s.odd)
    have hDH : D ≤ Subgroup.normalizer (H : Set G) := by
      intro d hd
      apply mem_normalizer_of_forall_conj_mem'
      intro x hx
      rw [hHeq] at hx ⊢
      have hx' : x ∈ (K : Set G) * (T : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left K T hTK]
        exact hx
      obtain ⟨k, hk, t, ht, rfl⟩ := hx'
      have e : d * (k * t) * d⁻¹ = (d * k * d⁻¹) * (d * t * d⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem_sup ((Subgroup.mem_normalizer_iff.mp (hDK hd) k).mp hk)
        ((Subgroup.mem_normalizer_iff.mp (hDT hd) t).mp ht)
    have hBH : B ≤ H := s.hyp.notation59.1.1.trans inf_le_right
    have hBC := s.B_le_centralizer h5114 hI hB3 c
    have hodd1 : ∀ y ∈ N, Odd (orderOf y) → y = 1 := by
      intro y hyN hyodd
      have hyV := hNV y hyN
      have hyM : y ∈ M := s.normalizer_V_le_M h323 hyV
      have hyHD : y ∈ (H : Set G) * (D : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left H D hDH]
        exact hNH hyN
      obtain ⟨h₀, hh₀, d, hd, rfl⟩ := hyHD
      have hDM : D ≤ M := hDL.trans hh.L_le
      have hh₀M : h₀ ∈ M := by
        have := M.mul_mem hyM (M.inv_mem (hDM hd))
        rwa [mul_inv_cancel_right] at this
      obtain ⟨t, ht, b, hb, rfl⟩ := s.exists_mem_T_mem_B ⟨hh₀M, hh₀⟩
      set tn : Subgroup.normalizer (V : Set G) :=
        ⟨t, s.le_normalizer_V (Subgroup.mem_sup_right ht)⟩
      set bn : Subgroup.normalizer (V : Set G) :=
        ⟨b, Subgroup.centralizer_le_normalizer _ (hBC hb)⟩
      set dn : Subgroup.normalizer (V : Set G) := ⟨d, s.L_le_normalizer_V (hDL hd)⟩
      have hbact : ∀ w, c.act bn w = w := (c.mem_centralizer_iff bn).mp (hBC hb)
      have hyact : ∀ w, (c.act (tn * bn * dn) w) 1 = w 1 := by
        intro w
        obtain ⟨u, rfl⟩ := c.ε_bij.2 w
        have hyc := (hNC hyN).2.2 u u.2
        rw [c.act_ε]
        set u' := conjAct V (tn * bn * dn) u with hu'
        have hu'c : ((u' * u⁻¹ : ↥V) : G) ∈ Z₁ := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, hu', conjAct_apply_coe]
          exact hyc
        have h1 := (hmemZ₁ (u' * u⁻¹)).mp hu'c
        rw [hεinv, Pi.sub_apply, sub_eq_zero] at h1
        exact h1
      have hdact : ∀ w, (c.act dn w) 1 = w 1 := by
        intro w
        have h1 := hyact w
        rw [c.act_mul, c.act_mul, hbact, s.T_act_snd hI c tn ht] at h1
        exact h1
      have hd1 : d = 1 := s.D_eq_one_of_act hI c hd hdact
      subst hd1
      simp only [mul_one] at hyN hyodd ⊢
      have hyH : t * b ∈ H := H.mul_mem (hTH ht) (hBH hb)
      have hyK : t * b ∈ K := mem_oTwoUpper_of_odd hyH hyodd
      have hyO := hNK ⟨hyN, hyK⟩
      obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 K) ⟨_, hyO⟩
      have hj' : (t * b) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      have h1 := orderOf_dvd_of_pow_eq_one hj'
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hyodd)) h1)
    refine le_pCoreOf_of_le_normalizer 2 hNH hHN ?_
    rintro ⟨x, hx⟩
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    have hord : orderOf (x ^ 2 ^ k) = m := by
      rw [orderOf_pow' x (pow_ne_zero k two_ne_zero), hkm, Nat.gcd_mul_right_left,
        Nat.mul_div_cancel_left _ (pow_pos two_pos k)]
    refine ⟨k, Subtype.ext ?_⟩
    have := hodd1 (x ^ 2 ^ k) (N.pow_mem hx _) (hord ▸ hm)
    simpa using this
  ·
    by_contra hne
    obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hne
    have heq := s.eq_M h323 hM'.1 (le_sup_left.trans hM'.2)
    exact hHM (heq ▸ (le_sup_left.trans (le_sup_right.trans hM'.2)))

end Setup5_1_17Odd

end CFSG.Quasithin.H13
