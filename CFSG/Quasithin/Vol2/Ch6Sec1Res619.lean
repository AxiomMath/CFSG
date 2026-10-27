module

public import CFSG.Quasithin.Vol2.Ch6Sec1GreenBook
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516Cases
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch5Sec1BorelTorus
public import CFSG.Quasithin.Vol2.Ch6S5Parab

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin
open CFSG.LieType.BorelTits
open scoped IsMulCommutative

@[expose] def G24LongRootSplit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (f : ℕ), 2 ≤ f →
    Hyp111 L1 L2 S →
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S))
      (IsG2Over f) →
    IsL2Quot f (oTwoQuot ↥L1) → IsL2Quot f (oTwoQuot ↥L2) →
    (∃ E : Subgroup G, E ≤ S ⊓ L1 ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ f ∧
      E ⊓ pCoreOf 2 L1 = ⊥) ∧
    (∃ E : Subgroup G, E ≤ S ⊓ L2 ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ f ∧
      E ⊓ pCoreOf 2 L2 = ⊥)

theorem eq_two_of_isL2Quot_sixty {m : ℕ} (hm : 1 ≤ m) {X : Type*} [Group X] (h : IsL2Quot m X)
    (hX : Nat.card X = 60) : m = 2 := by
  have hc := h.card hm
  rw [hX] at hc
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · interval_cases m
    norm_num at hc
  · have h8 : 8 ≤ 2 ^ m := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hgt
    have h64 : 64 ≤ 4 ^ m := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hgt
    have : 8 * 63 ≤ 2 ^ m * (4 ^ m - 1) := Nat.mul_le_mul h8 (by omega)
    omega

theorem normalizer_ne_top_of_two_perm5 {U : Subgroup (Equiv.Perm (Fin 5))} (hU : IsPGroup 2 U)
    (hU1 : U ≠ ⊥) : Subgroup.normalizer (U : Set (Equiv.Perm (Fin 5))) ≠ ⊤ := by
  intro htop
  have : U.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  exact hU1 (L619.eq_bot_of_normal_two_perm5 hU)

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611Nat

theorem mem_centralizer_ZS_of_mem_L (h : Hyp611Nat G T M L V n) {t : G} (htL : t ∈ L)
    (htZ : t ∈ Subgroup.normalizer (ch6ZS T L V : Set G)) {k : ℕ} (htk : t ^ 2 ^ k = 1) :
    t ∈ Subgroup.centralizer (ch6ZS T L V : Set G) := by
  obtain ⟨v, hv, hle⟩ := h.exists_line
  set m : Subgroup.normalizer (V : Set G) := ⟨t, h.toHyp611.L_le_normalizer htL⟩ with hm
  have hlin : ∀ (c : h.data.K) (w : Fin 2 → h.data.K),
      h.data.conj m (c • w) = c • h.data.conj m w := by
    intro c w
    have e : m = ⟨((⟨t, htL⟩ : ↥L) : G), h.data.le_normalizer (⟨t, htL⟩ : ↥L).2⟩ := rfl
    rw [e, h.data.conj_eq_rho, h.data.conj_eq_rho, Matrix.mulVec_smul]
  obtain ⟨μ, hμ⟩ : ∃ μ : h.data.K, h.data.conj m v = μ • v := by
    set z : ↥V := h.data.E.symm (Multiplicative.ofAdd v) with hzdef
    have hEz : Multiplicative.toAdd (h.data.E z) = v := by simp [hzdef]
    have hz : (z : G) ∈ ch6ZS T L V := (h.mem_ZS_iff_line hv hle z).mpr ⟨1, by rw [hEz, one_smul]⟩
    have hz' : ((conjAct V m z : ↥V) : G) ∈ ch6ZS T L V := by
      rw [conjAct_apply_coe]
      exact (Subgroup.mem_normalizer_iff.mp htZ z).mp hz
    obtain ⟨μ, hμ⟩ := (h.mem_ZS_iff_line hv hle (conjAct V m z)).mp hz'
    refine ⟨μ, ?_⟩
    calc h.data.conj m v = h.data.conj m (Multiplicative.toAdd (h.data.E z)) := by rw [hEz]
      _ = Multiplicative.toAdd (h.data.E (conjAct V m z)) := h.data.conj_apply m z
      _ = μ • v := hμ
  have hiter : ∀ j : ℕ, (h.data.conj m)^[j] v = μ ^ j • v := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [Function.iterate_succ_apply', ih, hlin, hμ, smul_smul, pow_succ]
  have hpow : (h.data.conj m)^[2 ^ k] v = v := by
    rw [← h.data.conj_pow]
    have : m ^ 2 ^ k = 1 := Subtype.ext (by simpa [hm] using htk)
    rw [this]
    exact h.data.conj_eq_of_mem_centralizer 1 (Subgroup.one_mem _) v
  have hμk : μ ^ 2 ^ k = 1 := by
    rw [hiter] at hpow
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    have h1 := congrFun hpow i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 hi
    have h2 : (μ ^ 2 ^ k - 1) * v i = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hi)
  have hμ1 : μ = 1 := eq_one_of_pow_two_pow_eq_one_offender h.two_dvd_card_K hμk
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨c, hc⟩ := (h.mem_ZS_iff_line hv hle ⟨z, hz.1⟩).mp hz
  have h1 : h.data.conj m (Multiplicative.toAdd (h.data.E ⟨z, hz.1⟩)) =
      Multiplicative.toAdd (h.data.E ⟨z, hz.1⟩) := by
    rw [hc, hlin, hμ, hμ1, one_smul]
  rw [h.data.conj_apply] at h1
  have h2 := congrArg Subtype.val (h.data.E.injective (Multiplicative.toAdd.injective h1))
  rw [conjAct_apply_coe] at h2
  have h3 : t * z * t⁻¹ = z := h2
  calc z * t = (t * z * t⁻¹) * t := by rw [h3]
    _ = t * z := by group

end Hyp611Nat

theorem hyp111R_of_s5 (h432 : Stmt4_3_2) (hR1 : L2RankOneSylowFact)
    (h : Hyp611Nat G T M L V 2) {T' : Subgroup G} (hT' : Hyp611 G T' M L V 2)
    {A D' : Subgroup G}
    (hZT : ch6ZS T L V ≤ T') (hT'Z : T' ≤ Subgroup.normalizer (ch6ZS T L V : Set G))
    (hAI : A ≤ Subgroup.centralizer (ch6ZS T L V : Set G))
    (hT'A : T' ≤ Subgroup.normalizer (A : Set G)) (hsylA : IsSylowTwoOf (T' ⊓ A) A)
    (hlistA : IsRankOneListed (oTwoQuot ↥A)) (hrankA : IsRankOneSylow (oTwoQuot ↥A))
    (hBA : borelOf A T' ≤ M) (hD'L : D' ≤ L) (hcD' : Nat.card D' = 3)
    (hD'Z : D' ≤ Subgroup.normalizer (ch6ZS T L V : Set G))
    (hD'A : D' ≤ Subgroup.normalizer (A : Set G))
    (hD'S : D' ≤ Subgroup.normalizer
      ((T' ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) : Subgroup G) : Set G))
    (hAM : ¬ A ≤ M) : Hyp111R L A T' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT'syl := hT'.sylow
  have hT'L : T' ≤ Subgroup.normalizer (L : Set G) := fun _ ht => hT'.normal (hT'.T_le ht)
  have hfin : Finite ↥T' := inferInstance
  have hTLC : T' ⊓ L ≤ Subgroup.centralizer (ch6ZS T L V : Set G) := by
    rintro t ⟨htT, htL⟩
    obtain ⟨k, hk⟩ := hT'syl.1 ⟨t, htT⟩
    exact h.mem_centralizer_ZS_of_mem_L htL (hT'Z htT) (k := k)
      (by simpa using congrArg Subtype.val hk)
  have hTLeq : T' ⊓ L = (T' ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓ L := by
    refine le_antisymm (fun x hx => ⟨⟨hx.1, hTLC hx⟩, hx.2⟩) (fun x hx => ⟨hx.1.1, hx.2⟩)
  have hD'N : D' ≤ Subgroup.normalizer ((T' ⊓ L : Subgroup G) : Set G) := by
    rw [hTLeq]
    exact fun d hd => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hD'S hd, Subgroup.le_normalizer (hD'L hd)⟩
  have hD'B : D' ≤ borelL T' L := le_inf hD'L hD'N
  obtain ⟨D'', hD''⟩ := hT'.toHyp5_0_1.exists_isHall_borel
  have hcD'' : Nat.card D'' = 3 := by
    rw [(hT'.toHyp5_0_1.isCyclic_card_of_isHall l2TorusFact hD'').2]
    norm_num
  have hD'Hall : Lin2.IsHallTwoPrimeOf D' (borelL T' L) := by
    refine ⟨hD'B, by rw [hcD']; decide, ?_⟩
    obtain ⟨m, hm⟩ := hD''.2.2
    refine ⟨m, ?_⟩
    have h1 := card_mul_relIndex_of_le hD''.1
    have h2 := card_mul_relIndex_of_le hD'B
    rw [hcD'', hm] at h1
    rw [hcD'] at h2
    omega
  have hBL : borelOf L T' = D' ⊔ (T' ⊓ L) := (hT'.toHyp5_0_1.borelL_eq_sup hD'Hall).symm
  have hBLA : borelOf L T' ≤ Subgroup.normalizer (A : Set G) := by
    rw [hBL]
    exact sup_le hD'A (inf_le_left.trans hT'A)
  have hBLZ : borelOf L T' ≤ Subgroup.normalizer (ch6ZS T L V : Set G) := by
    rw [hBL]
    exact sup_le hD'Z (inf_le_left.trans hT'Z)
  have hX1 : CharTwo (L ⊔ T' ⊔ borelOf A T') := by
    have hXM : L ⊔ T' ⊔ borelOf A T' ≤ M := sup_le (sup_le h.L_le hT'.T_le) hBA
    have hTX : T' ≤ L ⊔ T' ⊔ borelOf A T' := le_sup_right.trans le_sup_left
    refine charTwo_of_inH' h.qtke hT'syl ⟨hTX, fun h0 => ?_⟩
    have hsylM : IsSylowTwoOf T' M :=
      ⟨hT'.T_le, hT'syl.1, fun hd => hT'syl.2 (by
        rw [← Subgroup.relIndex_mul_index hT'.T_le]
        exact Dvd.dvd.mul_right hd _)⟩
    have hO : pCoreOf 2 M ≤ pCoreOf 2 (L ⊔ T' ⊔ borelOf A T') :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le_of_isSylowTwoOf hsylM).trans hTX)
        (hXM.trans (le_normalizer_pCoreOf 2 M)) (pCoreOf_isPGroup 2 M)
    rw [h0, le_bot_iff] at hO
    exact pCoreOf_ne_bot_of_isTwoLocal hT'.maxTwoLocal.1 hO
  have hX2 : CharTwo (A ⊔ T' ⊔ borelOf L T') := by
    have hXZ : A ⊔ T' ⊔ borelOf L T' ≤ Subgroup.normalizer (ch6ZS T L V : Set G) :=
      sup_le (sup_le (hAI.trans (Subgroup.centralizer_le_normalizer _)) hT'Z) hBLZ
    have hTX : T' ≤ A ⊔ T' ⊔ borelOf L T' := le_sup_right.trans le_sup_left
    refine charTwo_of_inH' h.qtke hT'syl ⟨hTX, fun h0 => ?_⟩
    have hZ : ch6ZS T L V ≤ pCoreOf 2 (A ⊔ T' ⊔ borelOf L T') :=
      le_pCoreOf_of_le_normalizer 2 (hZT.trans hTX) hXZ
        ((B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian).to_le h.ZS_le)
    rw [h0, le_bot_iff] at hZ
    exact h.ZS_ne_bot hZ
  have hlistL : IsRankOneListed (oTwoQuot ↥L) := Or.inl ⟨2, by norm_num, h.isL2Quot_L⟩
  have h1 : Hyp111At L A T' :=
    ⟨hfin, hT'syl.1, hT'L, hT'.toHyp5_0_1.isSylowTwoOf_inf, hlistL, hBA.trans hT'.normal, hX1⟩
  have h2 : Hyp111At A L T' := ⟨hfin, hT'syl.1, hT'A, hsylA, hlistA, hBLA, hX2⟩
  have ho2 : pCoreOf 2 (L ⊔ A ⊔ T') = ⊥ := by
    by_contra hne
    obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hne
    have hLT : L ⊔ T' ≤ M' :=
      sup_le (le_sup_left.trans (le_sup_left.trans hM'.2)) (le_sup_right.trans hM'.2)
    have hM'eq : M' = M := (hT'.isUniqueM h432).2 M' ⟨hM'.1, hLT⟩
    exact hAM (hM'eq ▸ (le_sup_right.trans (le_sup_left.trans hM'.2)))
  exact ⟨⟨h1, h2, ho2⟩, hT'.toHyp5_0_1.rankOneAt hR1,
    F1.rankOneAt_of_isRankOneSylow hsylA hrankA⟩

theorem not_isSolvable_alt5_ch6 : ¬ Group.IsSolvable ↥(alternatingGroup (Fin 5)) := by
  intro hs
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hc := (IsSimpleGroup.comm_iff_isSolvable (G := ↥(alternatingGroup (Fin 5)))).mpr hs
  have h1 : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have h2 : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 3) ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have hne : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) * (Equiv.swap 0 1 * Equiv.swap 1 3) ≠
      (Equiv.swap 0 1 * Equiv.swap 1 3) * (Equiv.swap 0 1 * Equiv.swap 1 2) := by decide
  exact hne (congrArg Subtype.val (hc ⟨_, h1⟩ ⟨_, h2⟩))

end CFSG.Quasithin.H13
