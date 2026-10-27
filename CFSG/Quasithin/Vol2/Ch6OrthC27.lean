module

public import CFSG.Quasithin.Vol2.Ch6OrthX
public import CFSG.Quasithin.Background.C2Seven
public import CFSG.Quasithin.EmptyFaithful.S14113Stage
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Basic
public import CFSG.Quasithin.Vol2.Ch6OrthNotNat

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative commutatorElement Matrix

theorem mul_self_eq_one_of_fix_ch6 {F : Type*} [Field F] (h2 : (2 : F) = 0)
    (g : Matrix.SpecialLinearGroup (Fin 2) F) {v : Fin 2 → F} (hv : v ≠ 0)
    (hg : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v) : g * g = 1 := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact g.2
  have h0 := congrFun hg 0
  have h1 := congrFun hg 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  set a := (g : Matrix (Fin 2) (Fin 2) F) 0 0
  set b := (g : Matrix (Fin 2) (Fin 2) F) 0 1
  set c := (g : Matrix (Fin 2) (Fin 2) F) 1 0
  set d := (g : Matrix (Fin 2) (Fin 2) F) 1 1
  have e0 : (a + d) * v 0 = 0 := by
    linear_combination (1 - d) * h0 + b * h1 + v 0 * hdet + v 0 * h2
  have e1 : (a + d) * v 1 = 0 := by
    linear_combination c * h0 + (1 - a) * h1 + v 1 * hdet + v 1 * h2
  have hs : a + d = 0 := by
    by_contra hs
    apply hv
    funext i
    fin_cases i
    · exact (mul_eq_zero.mp e0).resolve_left hs
    · exact (mul_eq_zero.mp e1).resolve_left hs
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true]
  · linear_combination a * hs - hdet - h2
  · linear_combination b * hs
  · linear_combination c * hs
  · linear_combination d * hs - hdet - h2

theorem sq_eq_one_of_pow_four_ch6 {F : Type*} [Field F] [CharP F 2]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) (hg : g ^ 4 = 1) : g ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hm4 : (g : Matrix (Fin 2) (Fin 2) F) ^ 4 = 1 := by
    have := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) F =>
      (x : Matrix (Fin 2) (Fin 2) F)) hg
    simpa using this
  have hN : ((g : Matrix (Fin 2) (Fin 2) F) - 1) ^ 2 ^ 2 = 0 := by
    rw [sub_pow_char_pow_of_commute 2 2 (Commute.one_right _), one_pow,
      show (2 : ℕ) ^ 2 = 4 by norm_num, hm4, sub_self]
  have hdet : ((g : Matrix (Fin 2) (Fin 2) F) - 1).det = 0 := by
    have := congrArg Matrix.det hN
    rw [Matrix.det_pow, Matrix.det_zero] at this
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  obtain ⟨v, hv, hmv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hfix : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hmv
    exact hmv
  rw [pow_two]
  exact mul_self_eq_one_of_fix_ch6 h2 g hv hfix

theorem card_alternatingGroup_ne_4080_ch6 (m : ℕ) :
    Nat.card (alternatingGroup (Fin m)) ≠ 4080 := by
  intro h
  have hdvd : Nat.card (alternatingGroup (Fin m)) ∣ m.factorial := by
    have := Subgroup.card_subgroup_dvd_card (alternatingGroup (Fin m))
    rwa [Nat.card_perm, Nat.card_fin] at this
  rcases Nat.lt_or_ge m 8 with hm | hm
  · rw [h] at hdvd
    interval_cases m <;> revert hdvd <;> decide
  · have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    have h8 : (8 : ℕ).factorial ≤ m.factorial := Nat.factorial_le hm
    have : (8 : ℕ).factorial = 40320 := by decide
    omega

theorem card_statedSp_ne_4080_ch6 {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4) :
    Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) ≠ 4080 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, Nat.card_eq_fintype_card,
    hF]
  decide

theorem card_ne_4080_of_isPSU_ch6 {X : Type} [Group X] (h : IsPSU 3 3 1 X) : Nat.card X ≠ 4080 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_three le_rfl hK
      (by norm_num)]
  decide

@[expose] def jMat3Ch6 (F : Type*) [Field F] : Matrix (Fin 3) (Fin 3) F :=
  !![1, 1, 0; 0, 1, 1; 0, 0, 1]

theorem det_jMat3Ch6 (F : Type*) [Field F] : (jMat3Ch6 F).det = 1 := by
  simp [jMat3Ch6, Matrix.det_fin_three]

theorem exists_statedSL3_pow_four_ch6 (F : Type) [Field F] [CharP F 2] :
    ∃ J : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F), J ^ 4 = 1 ∧ J ^ 2 ≠ 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  set A : Matrix.GeneralLinearGroup (Fin 3) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (jMat3Ch6 F) (by rw [det_jMat3Ch6]; exact one_ne_zero)
  have hA : A ∈ CFSG.Assembly.LowTwoRank.StatedSL 3 F := Subgroup.subset_closure (by
    show (jMat3Ch6 F).det = 1
    exact det_jMat3Ch6 F)
  have hsq : (jMat3Ch6 F) * (jMat3Ch6 F) = !![1, 0, 1; 0, 1, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [jMat3Ch6, Matrix.mul_apply, Fin.sum_univ_three] <;>
      linear_combination h2
  refine ⟨⟨A, hA⟩, ?_, ?_⟩
  · apply Subtype.ext
    apply Units.ext
    show (jMat3Ch6 F) ^ 4 = 1
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq (jMat3Ch6 F), hsq, sq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination h2
  · intro h1
    have := congrArg (fun x : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) =>
      ((x : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2) h1
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
      Units.val_one] at this
    change ((jMat3Ch6 F) ^ 2) 0 2 = (1 : Matrix (Fin 3) (Fin 3) F) 0 2 at this
    rw [pow_two, hsq] at this
    simp at this

theorem exists_statedSL_two_pow_four_ch6 (n : ℕ) (hn : n = 4 ∨ n = 5) :
    ∃ J : ↥(CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2)), J ^ 4 = 1 ∧ J ^ 2 ≠ 1 := by
  rcases hn with rfl | rfl
  · set N : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
      !![1, 1, 0, 0; 0, 1, 1, 0; 0, 0, 1, 0; 0, 0, 0, 1] with hN
    have hdet : N.det = 1 := by
      rw [Matrix.det_of_isUpperTriangular (by rw [hN]; decide +kernel)]; rw [hN]; decide +kernel
    set A := Matrix.GeneralLinearGroup.mkOfDetNeZero N (by rw [hdet]; exact one_ne_zero)
    have hA : A ∈ CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2) :=
      Subgroup.subset_closure (by exact hdet)
    refine ⟨⟨A, hA⟩, ?_, ?_⟩
    · apply Subtype.ext; apply Units.ext
      show N ^ 4 = 1
      rw [hN]; decide +kernel
    · intro h1
      have := congrArg (fun x : ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) =>
        ((x : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))) h1
      simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
        Units.val_one] at this
      change N ^ 2 = 1 at this
      rw [hN] at this
      revert this; decide +kernel
  · set N : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
      !![1, 1, 0, 0, 0; 0, 1, 1, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1] with hN
    have hdet : N.det = 1 := by
      rw [Matrix.det_of_isUpperTriangular (by rw [hN]; decide +kernel)]; rw [hN]; decide +kernel
    set A := Matrix.GeneralLinearGroup.mkOfDetNeZero N (by rw [hdet]; exact one_ne_zero)
    have hA : A ∈ CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2) :=
      Subgroup.subset_closure (by exact hdet)
    refine ⟨⟨A, hA⟩, ?_, ?_⟩
    · apply Subtype.ext; apply Units.ext
      show N ^ 4 = 1
      rw [hN]; decide +kernel
    · intro h1
      have := congrArg (fun x : ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)) =>
        ((x : Matrix.GeneralLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))) h1
      simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
        Units.val_one] at this
      change N ^ 2 = 1 at this
      rw [hN] at this
      revert this; decide +kernel

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611

theorem le_L_of_orth_ch6 (h : Hyp611 G T M L V n) (horth : IsOrthCh5 L V n) (hn : 2 ≤ n) :
    V ≤ L := by
  obtain ⟨hVL, -⟩ := h.commutator_eq_and_inf_of_orth_ch6 horth hn
  have hVN : V ≤ Subgroup.normalizer (L : Set G) := h.le_T.trans h.toHyp5_0_1.T_le_normalizer
  have hcL : ⁅V, L⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    rw [commutatorElement_def]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hVN hv) l).mp hl) (L.inv_mem hl)
  calc V = ⁅V, L⁆ := hVL.symm
    _ ≤ L := hcL

theorem le_blockU_of_orth_ch6 (h : Hyp611 G T M L V n) (horth : IsOrthCh5 L V n) (hn : 2 ≤ n) :
    V ≤ blockU L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVL, -⟩ := h.commutator_eq_and_inf_of_orth_ch6 horth hn
  have hVQ : V ≤ blockQ L :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (h.le_L_of_orth_ch6 horth hn)
      h.L_le_normalizer (B2F.isPGroup_of_isElemAbelian h.isElemAbelian)
  calc V = ⁅V, L⁆ := hVL.symm
    _ ≤ ⁅blockQ L, L⁆ := Subgroup.commutator_mono hVQ le_rfl
    _ = blockU L := rfl

theorem inf_blockZ_of_orth_ch6 (h : Hyp611 G T M L V n) (horth : IsOrthCh5 L V n) (hn : 2 ≤ n) :
    V ⊓ blockZ L = ⊥ := by
  obtain ⟨-, hC⟩ := h.commutator_eq_and_inf_of_orth_ch6 horth hn
  rw [eq_bot_iff, ← hC]
  exact inf_le_inf_left V (inf_le_right : blockU L ⊓ _ ≤ _)

theorem not_isLin2Type_of_orth_ch6 (h : Hyp611 G T M L V n) (horth : IsOrthCh5 L V n)
    (hn : 2 ≤ n) (k : ℕ) : ¬ IsLin2Type L k := by
  rintro ⟨F, _, _, -, α, hαs, -, β, -, hβk, hβe⟩
  obtain ⟨v₁, v₂, hv₁, hv₂, hnc⟩ := horth.exists_not_conj_ch6
  have hVU := h.le_blockU_of_orth_ch6 horth hn
  have hVZ := h.inf_blockZ_of_orth_ch6 horth hn
  have hU : L ≤ Subgroup.normalizer (blockU L : Set G) :=
    le_normalizer_commutator_of (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
      Subgroup.le_normalizer
  have hinj : ∀ (x y : G) (hx : x ∈ V) (hy : y ∈ V),
      Multiplicative.toAdd (β ⟨x, hVU hx⟩) = Multiplicative.toAdd (β ⟨y, hVU hy⟩) → x = y := by
    intro x y hx hy hxy
    have hk : (⟨x, hVU hx⟩ : ↥(blockU L)) * (⟨y, hVU hy⟩ : ↥(blockU L))⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_inv, hxy, add_neg_cancel, toAdd_one]
    rw [hβk, Subgroup.mem_subgroupOf] at hk
    have hmem : x * y⁻¹ ∈ V ⊓ blockZ L := ⟨V.mul_mem hx (V.inv_mem hy), hk⟩
    rw [hVZ, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_one.mp hmem
  have hne : ∀ v : ↥V, v ≠ 1 → Multiplicative.toAdd (β ⟨v, hVU v.2⟩) ≠ 0 := by
    intro v hv h0
    apply hv
    apply Subtype.ext
    refine hinj v 1 v.2 V.one_mem ?_
    rw [h0]
    have h1 : (⟨1, hVU V.one_mem⟩ : ↥(blockU L)) = 1 := rfl
    rw [h1, map_one, toAdd_one]
  obtain ⟨A, hA⟩ := exists_sl2_mulVec_eq _ _ (hne v₁ hv₁) (hne v₂ hv₂)
  obtain ⟨ℓ, rfl⟩ := hαs A
  apply hnc ℓ ℓ.2
  have hmemU : (ℓ : G) * v₁ * (ℓ : G)⁻¹ ∈ blockU L :=
    (Subgroup.mem_normalizer_iff.mp (hU ℓ.2) _).mp (hVU v₁.2)
  have hmemV : (ℓ : G) * v₁ * (ℓ : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (h.L_le_normalizer ℓ.2) _).mp v₁.2
  have h1 := hβe ℓ ⟨v₁, hVU v₁.2⟩ ⟨_, hmemU⟩ rfl
  rw [hA] at h1
  exact hinj _ _ hmemV v₂.2 h1

theorem card_quot_four_ch6 (h : Hyp611 G T M L V 4) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 4080 := by
  rw [h.toHyp5_0_1.card_quot]
  norm_num

theorem card_eq_of_surjective_ch6 (h : Hyp611 G T M L V 4) {H : Type*} [Group H] (α : ↥L →* H)
    (hα : Function.Surjective α) (hk : α.ker = CFSG.pCore 2 ↥L) : Nat.card H = 4080 := by
  rw [← h.card_quot_four_ch6]
  exact (Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)).toEquiv).symm

theorem not_isAltType_ch6 (h : Hyp611 G T M L V 4) (m : ℕ) : ¬ IsAltType L m := by
  rintro ⟨α, hαs, hαk, -⟩
  exact card_alternatingGroup_ne_4080_ch6 m (h.card_eq_of_surjective_ch6 α hαs hαk)

theorem not_isChiBlock2_ch6 (h : Hyp611 G T M L V 4) (horth : IsOrthCh5 L V 4)
    (X : Subgroup G) : ¬ IsChiBlock2 X L := by
  rintro ⟨-, ⟨k, -, hk⟩ | ⟨m, -, hm⟩⟩
  · exact h.not_isLin2Type_of_orth_ch6 horth (by norm_num) k hk
  · exact h.not_isAltType_ch6 m hm

theorem center_quot_eq_bot_ch6 (h : Hyp611 G T M L V 4) :
    Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
  have hs := h.toHyp5_0_1.isSimple
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) with h0 | h0
  · exact h0
  · exfalso
    have hcard := h.card_quot_four_ch6
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L ⧸ CFSG.pCore 2 ↥L) 2
      (by rw [hcard]; norm_num)
    have hN : (Subgroup.zpowers x).Normal := by
      refine ⟨fun y hy g => ?_⟩
      have hg : g ∈ Subgroup.center _ := by rw [h0]; exact Subgroup.mem_top g
      rw [Subgroup.mem_center_iff] at hg
      rw [(hg y).symm, mul_inv_cancel_right]
      exact hy
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ hN with h1 | h1
    · have : x = 1 := by
        have := Subgroup.mem_zpowers x
        rwa [h1, Subgroup.mem_bot] at this
      rw [this, orderOf_one] at hx
      exact absurd hx (by norm_num)
    · have h2 : Nat.card (Subgroup.zpowers x) = 2 := by rw [Nat.card_zpowers, hx]
      rw [h1, Subgroup.card_top, hcard] at h2
      exact absurd h2 (by norm_num)

theorem card_autOn_four_ch6 (h : Hyp611 G T M L V 4) : Nat.card ↥(autOn L V) = 4080 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLV := h.L_le_normalizer
  rw [card_autOn_eq_relIndex hLV]
  have heq : (L ⊓ Subgroup.centralizer (V : Set G)).subgroupOf L = CFSG.pCore 2 ↥L := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, hyx⟩ :=
        h.toHyp5_0_1.inf_centralizer_le hLV h.module.2.2 (Subgroup.mem_subgroupOf.mp hx)
      have hyx' : y = x := Subtype.ext hyx
      rw [← hyx']
      exact hy
    · intro x hx
      rw [Subgroup.mem_subgroupOf]
      refine ⟨x.2, ?_⟩
      have hxO : (x : G) ∈ pCoreOf 2 L := by
        exact ⟨x, hx, rfl⟩
      have hOO : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
          ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
          (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
            (h.toHyp5_0_1.T_le_normalizer.trans
              (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)))
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
      have hxQ : (x : G) ∈ ch6Q T V := by rw [h.centralizer_eq]; exact hOO hxO
      exact hxQ.2
  show ((L ⊓ Subgroup.centralizer (V : Set G)).subgroupOf L).index = 4080
  rw [heq, Subgroup.index, ← h.card_quot_four_ch6]

omit [Finite G] in
theorem sq_eq_one_of_mem_autOn_ch6 (horth : IsOrthCh5 L V 4) {a : MulAut ↥V}
    (ha : a ∈ autOn L V) (h4 : a ^ 4 = 1) : a ^ 2 = 1 := by
  obtain ⟨F, _, _, _, -, eρ, -, -⟩ := (show IsOrthCh5 L V (2 * 2) from horth).exists_equiv
  set γ := eρ.symm ⟨a, ha⟩ with hγ
  have ha' : (⟨a, ha⟩ : ↥(autOn L V)) = eρ γ := by rw [hγ, MulEquiv.apply_symm_apply]
  have hγ4 : γ ^ 4 = 1 := by
    apply eρ.injective
    rw [map_pow, ← ha', map_one]
    exact Subtype.ext h4
  have h2 := sq_eq_one_of_pow_four_ch6 γ hγ4
  have : (⟨a, ha⟩ : ↥(autOn L V)) ^ 2 = 1 := by rw [ha', ← map_pow, h2, map_one]
  exact congrArg Subtype.val this

theorem pow_510_of_mem_autOn_ch6 (h : Hyp611 G T M L V 4) (horth : IsOrthCh5 L V 4)
    {a : MulAut ↥V} (ha : a ∈ autOn L V) : a ^ 510 = 1 := by
  have hc : a ^ 4080 = 1 := by
    have := pow_card_eq_one' (G := ↥(autOn L V)) (x := ⟨a, ha⟩)
    rw [h.card_autOn_four_ch6] at this
    simpa using congrArg Subtype.val this
  have hmem : ∀ k : ℕ, (a ^ 255) ^ k ∈ autOn L V :=
    fun k => (autOn L V).pow_mem ((autOn L V).pow_mem ha 255) k
  have h16 : (a ^ 255) ^ 16 = 1 := by rw [← pow_mul]; exact hc
  have h8 : (a ^ 255) ^ 8 = 1 := by
    have := sq_eq_one_of_mem_autOn_ch6 horth (hmem 4) (by rw [← pow_mul]; exact h16)
    rwa [← pow_mul] at this
  have h4 : (a ^ 255) ^ 4 = 1 := by
    have := sq_eq_one_of_mem_autOn_ch6 horth (hmem 2) (by rw [← pow_mul]; exact h8)
    rwa [← pow_mul] at this
  have h2 := sq_eq_one_of_mem_autOn_ch6 horth (pow_one (a ^ 255) ▸ hmem 1) h4
  rw [show (510 : ℕ) = 255 * 2 by norm_num, pow_mul]
  exact h2

theorem pow_510_of_mem_autOn_of_le_ch6 (h : Hyp611 G T M L V 4) (horth : IsOrthCh5 L V 4)
    {W : Subgroup G} (hOW : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G)) {y : MulAut ↥W}
    (hy : y ∈ autOn L W) : y ^ 510 = 1 := by
  obtain ⟨ℓ, hℓL, rfl⟩ := mem_autOn_iff.mp hy
  have hℓV : (ℓ : G) ∈ Subgroup.normalizer (V : Set G) := h.L_le_normalizer hℓL
  have ha := h.pow_510_of_mem_autOn_ch6 horth (mem_autOn_iff.mpr ⟨⟨ℓ, hℓV⟩, hℓL, rfl⟩)
  rw [← map_pow, conjAct_eq_one_iff_ch6] at ha
  have hcL : ((ℓ : G) ^ 510) ∈ L ⊓ Subgroup.centralizer (V : Set G) :=
    ⟨L.pow_mem hℓL _, by simpa using ha⟩
  have hO := h.toHyp5_0_1.inf_centralizer_le h.L_le_normalizer h.module.2.2 hcL
  rw [← map_pow, conjAct_eq_one_iff_ch6]
  simpa using hOW hO

theorem false_of_pow_four_ch6 (h : Hyp611 G T M L V 4) (horth : IsOrthCh5 L V 4)
    {W : Subgroup G} (hOW : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G)) {H : Type*} [Group H]
    (e : ↥(autOn L W) ≃* H) {J : H} (hJ4 : J ^ 4 = 1) (hJ2 : J ^ 2 ≠ 1) : False := by
  have h510 : J ^ 510 = 1 := by
    have h1 : ((e.symm J : ↥(autOn L W)) : MulAut ↥W) ^ 510 = 1 :=
      h.pow_510_of_mem_autOn_of_le_ch6 horth hOW (e.symm J).2
    have h2 : (e.symm J) ^ 510 = 1 := Subtype.ext (by simpa using h1)
    rw [← map_pow] at h2
    exact e.symm.injective (by rw [h2, map_one])
  apply hJ2
  have := pow_gcd_eq_one.mpr ⟨h510, hJ4⟩
  rwa [show Nat.gcd 510 4 = 2 by norm_num] at this

theorem mem_cComp_ch6 (h : Hyp611 G T M L V n) : L ∈ cComp M := by
  obtain ⟨-, ⟨hne, hperf, -, hmin⟩, -, -⟩ := h.maximal.1
  have hLN : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).mpr h.normal
  refine ⟨hne, hperf, A3.subnormal_of_normal h.L_le hLN, fun K hKL hK hKp hKs => ?_⟩
  apply hmin K hKL hK hKp
  have h1 : IsSubnormal K L := A3.subnormal_of_le_of_le hKs hKL.le h.L_le
  have h2 : IsSubnormal L (L ⊔ T) := A3.subnormal_of_normal le_sup_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      h.toHyp5_0_1.sup_le_normalizer)
  exact A3.subnormal_trans h1 h2

theorem not_oTwoFstarIn_le_of_orth_ch6
    (hC27 : ∀ (G' : Type) [Group G'] [Finite G'], ASC27Statement G') (h432 : Stmt4_3_2)
    (h : Hyp611 G T M L V 4) (horth : IsOrthCh5 L V 4) {M₁ : Subgroup G}
    (hM₁ : quasithinIsMaxTwoLocal M₁) (hTM₁ : T ≤ M₁) (hne : M₁ ≠ M) :
    ¬ oTwoFstarIn M₁ ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hF
  set Q₁ := pCoreOf 2 M₁ with hQ₁def
  have hOX : Q₁ ≤ oTwoFstarIn M₁ := pCoreOf_le_oTwoFstarIn M₁
  have hXHK : oTwoFstarIn M₁ ≤ M₁ ⊓ M := le_inf (oTwoFstarIn_le M₁) hF
  have hA := a44Hyp_oTwoFstarIn M₁
  have h1 : pCoreOf 2 (M₁ ⊓ M) = Q₁ := a4_4_1 hOX hXHK hA
  have h2 : CKQ M (pCoreOf 2 (M₁ ⊓ M)) ≤ M₁ ⊓ M := a4_4_2 hOX hXHK hA hM₁
  rw [h1] at h2
  have hQ₁M : Q₁ ≤ M := hOX.trans hF
  have hNQ : Subgroup.normalizer (Q₁ : Set G) = M₁ := eq_normalizer_pCoreOf_of_isMaxTwoLocal hM₁
  have hQ₁ne : Q₁ ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hM₁.1
  have hcc : conjClosure Q₁ (M ⊓ M₁) = Q₁ := by
    apply le_antisymm
    · exact conjClosure_le fun g hg z hz =>
        (Subgroup.mem_normalizer_iff.mp
          ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M₁) hg.2) z).mp hz
    · exact le_conjClosure _ _
  have hyp : HypC23 M Q₁ (M ⊓ M₁) :=
    { sqtk := sqtkGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian
        (pCoreOf_ne_bot_of_isTwoLocal h.maxTwoLocal.1)
      radical := ⟨hQ₁M, hQ₁ne, by rw [hNQ, inf_comm, h1]⟩
      le := inf_le_left
      cgs := by rw [inf_comm]; exact h2
      sylow := by
        rw [hcc]
        exact ⟨le_rfl, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₁, by simp⟩ }
  by_cases hLM₁ : L ≤ M ⊓ M₁
  · exact hne ((h.isUniqueM h432).2 M₁ ⟨hM₁, sup_le (hLM₁.trans inf_le_right) hTM₁⟩)
  have hLc := h.mem_cComp_ch6
  have hLchar : CharTwo L := (quasithinGenFitting_eq_pCoreOf_iff L 2).mp h.faithful.2.2.1
  obtain ⟨-, -, h3⟩ := hC27 G M Q₁ (M ⊓ M₁) L _ hyp hLc h.toHyp5_0_1.isQuasisimple hLchar hLM₁
    (hQ₁M.trans h.normal) rfl
  have hOW : pCoreOf 2 L ≤
      Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (L ⊔ Q₁)) : Set G) := by
    have hOO : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ Q₁) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
        (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
          ((hQ₁M.trans h.normal).trans
            (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact ((Subgroup.mem_centralizer_iff.mp (A4.omegaOneCenterOf_le_centerOf _ hw).2 x
      (hOO hx))).symm
  rcases h3 with ⟨hchi, -⟩ | ⟨⟨k, α, -, -, -, hwith, -⟩, -⟩ | ⟨⟨-, hhat, -⟩, -⟩ |
      ⟨⟨-, ⟨α, hαs, hαk⟩, -⟩, -⟩ | ⟨⟨-, α, hwith6⟩ | ⟨-, F, _, _, hF4, α, hαs, hαk, -⟩, -⟩ |
      ⟨⟨-, hpsu, -⟩, -⟩ | ⟨⟨k, F, _, _, -, hFc, ⟨e⟩⟩, -⟩ | ⟨he | he, -⟩
  · exact h.not_isChiBlock2_ch6 horth M hchi
  · exact card_alternatingGroup_ne_4080_ch6 k (h.card_eq_of_surjective_ch6 α hwith.1 hwith.2.1)
  · have h3 := hhat.2.1
    rw [h.center_quot_eq_bot_ch6, Subgroup.card_bot] at h3
    exact absurd h3 (by norm_num)
  · exact card_alternatingGroup_ne_4080_ch6 7 (h.card_eq_of_surjective_ch6 α hαs hαk)
  · exact card_alternatingGroup_ne_4080_ch6 6
      (h.card_eq_of_surjective_ch6 α hwith6.1 hwith6.2.1)
  · exact card_statedSp_ne_4080_ch6 hF4 (h.card_eq_of_surjective_ch6 α hαs hαk)
  · exact card_ne_4080_of_isPSU_ch6 hpsu h.card_quot_four_ch6
  · have : CharP F 2 := charP_of_card_eq_prime_pow hFc
    obtain ⟨J, hJ4, hJ2⟩ := exists_statedSL3_pow_four_ch6 F
    exact h.false_of_pow_four_ch6 horth hOW e hJ4 hJ2
  · obtain ⟨e⟩ := he
    obtain ⟨J, hJ4, hJ2⟩ := exists_statedSL_two_pow_four_ch6 4 (Or.inl rfl)
    exact h.false_of_pow_four_ch6 horth hOW e hJ4 hJ2
  · obtain ⟨e⟩ := he
    obtain ⟨J, hJ4, hJ2⟩ := exists_statedSL_two_pow_four_ch6 5 (Or.inr rfl)
    exact h.false_of_pow_four_ch6 horth hOW e hJ4 hJ2

end Hyp611

end CFSG.Quasithin.H13
