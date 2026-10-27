module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End4Proof2125
public import CFSG.RankThree.PartTwo.Sec21.Item218Res2ProofAssembly
import CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof2125Unique
public import CFSG.RankThree.PartTwo.Sec6.Item612
public import CFSG.RankThree.PartTwo.Sec6.Item65Tools

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Item2125Star : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G) (e : G) (Y : Subgroup G),
    Gen2125 G A E U c L d U₀ a X e Y →
      ∃ U₁ ∈ fourGroups E, ∃ Y' : Subgroup G, (e, Y') ∈ lThreeStarPairs A E U₁

@[expose] def Item2125V : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G) (e : G) (Y : Subgroup G),
    Gen2125 G A E U c L d U₀ a X e Y →
      ∃ U₁ ∈ fourGroupsMinus E, e ∈ Subgroup.centralizer (U₁ : Set G) ∧ sixTwelveV E U₁ e ≠ ⊥

namespace Item2119End4Proof

open Item2119EndProof Item2119End3Proof

variable {G : Type} [Group G] [Finite G]

theorem config2119_of_pair
    (h211 : Item211) (h2115 : Item2115) (h218 : Item218) (h2118 : Item2118)
    (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) {A E U Z : Subgroup G} {b d : G}
    (hpair : Sec21Pair G A E U b Z) (h27 : Nat.card A = 27) (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hnd : ∀ g ∈ Subgroup.normalizer (A : Set G), g * d * g⁻¹ ∈ Subgroup.zpowers d) :
    d ∉ Subgroup.zpowers b ∧ Config2119 G A E U b Z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hbA : b ∈ A := hpair.mem_E.2 hpairs.1.1
  have hb1 : b ≠ 1 := hpairs.2.1
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hb3 : b ^ 3 = 1 := hAe.2 b hbA
  have hZb' : Z ∈ thetaComponentsAt 3 b := (lZeroStarAt_subset A b) hpairs.2.2.1
  have hZC : Z ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hZb'
  have hZb : ∀ x ∈ Z, x * b * x⁻¹ = b := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hZC hx), mul_inv_cancel_right]
  have hNd : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers d : Subgroup G) : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    exact (Subgroup.zpowers d).zpow_mem (hnd g hg) k
  have hZd : Z ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G) := inf_le_right.trans hNd
  have hdb : d ∉ Subgroup.zpowers b := by
    intro h
    apply h2115 G A E U b Z hpair
    have hZ : Subgroup.zpowers d = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr h)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hb3 hb1,
          orderOf_eq_prime hd3 hd1])
    rw [← hZ]
    exact hNd
  refine ⟨hdb, ?_⟩
  have h4Q : orderOf (QuaternionGroup.a 1 : QuaternionGroup 2) = 4 :=
    QuaternionGroup.orderOf_a_one
  have h4D : orderOf (DihedralGroup.r 1 : DihedralGroup 4) = 4 := DihedralGroup.orderOf_r_one
  have h8 : orderOf (CFSG.Semidihedral.r 4) = 8 := by
    rw [CFSG.Semidihedral.orderOf_r 4 (by norm_num)]
    rfl
  have h4S : orderOf (CFSG.Semidihedral.r 4 ^ 2) = 4 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [h8]; norm_num), h8]
  have four : ∀ {H : Type} [Group H], Nonempty (starOf A Z ≃* H) →
      ∀ h : H, orderOf h = 4 → False := fun ⟨e⟩ h hh =>
    Item218Res2Proof.false_of_orderOf_four hAe h27 hbA hdA hb1 hdb hZb hZd e hh
  have list : IsList218 Z → False := not_isList218_of_item218 h218 hpair
  have h81 : Nat.card A = 3 ^ 4 → False := fun h => by
    rw [h27] at h
    norm_num at h
  rcases h211 G A E U b Z hpair with ⟨-, hT, -⟩ | ⟨-, -, hQ⟩ | ⟨-, -, hSD⟩ |
      ⟨hM, -, -⟩ | ⟨hJ, -, -⟩ | ⟨hM, -, -⟩ | ⟨⟨m, hm, hme, h7c⟩, h27', hS3⟩ |
      ⟨⟨m, -, -, h8'⟩, -, -⟩ | ⟨-, -, hD8⟩ | ⟨-, h81', -⟩ | ⟨-, h81', -⟩ | ⟨-, -, hD8⟩ |
      ⟨-, h81', -⟩
  · exact (Item218Res2Proof.not_le_normalizer_of_isTripleCover h45 h66 hpair hT hdA hdb
      hZd).elim
  · exact (four hQ _ h4Q).elim
  · exact (four hSD _ h4S).elim
  · rcases hM with e | e
    · exact (list (Or.inl e)).elim
    · exact (list (Or.inr (Or.inl e))).elim
  · exact (list (Or.inr (Or.inr (Or.inl hJ)))).elim
  · rcases hM with e | e
    · exact (list (Or.inr (Or.inr (Or.inr (Or.inl e))))).elim
    · exact (list (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))).elim
  · rcases h7c with ⟨⟨eZ⟩, hC⟩ | ⟨⟨eZ⟩, -⟩
    · exact ⟨hpair, ⟨m, hm, hme, ⟨eZ⟩⟩, hC, h27', hS3⟩
    · exact (false_of_isIrreducibleOn (h2118 G A E U b Z hpair ⟨m, ⟨eZ⟩⟩) hdA hd1 hd3 h27
        hnd).elim
  · rcases h8' with h | h
    · exact (list (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, h⟩))))))).elim
    · exact (list (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, h⟩))))))).elim
  · exact (four hD8 _ h4D).elim
  · exact (h81 h81').elim
  · exact (h81 h81').elim
  · exact (four hD8 _ h4D).elim
  · exact (h81 h81').elim

theorem mem_and_type_of_pair (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    {A E U Z : Subgroup G} {b d : G} (hcfgZ : Config2119 G A E U b Z) (hdA : d ∈ A)
    (hd1 : d ≠ 1) (hdb : d ∉ Subgroup.zpowers b)
    (hnd : ∀ g ∈ Subgroup.normalizer (A : Set G), g * d * g⁻¹ ∈ Subgroup.zpowers d) :
    d ∈ Z ∧ Sec4.InducesTypeOn Z d 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hbZ, d', hd'B, hd'1, hd'T, -, -, -, -, ⟨w', ⟨hw'Z, hw'N⟩, -, hw'd', hw'A, hw'move⟩,
    t', ⟨ht'Z, ht'N⟩, ht'd'⟩ := Item21Late2Proof.frame_of h45 h66 hcfgZ
  have hpair := hcfgZ.pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have h27 : Nat.card A = 27 := by rw [hcfgZ.card]; norm_num
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hbA : b ∈ A := hpair.mem_E.2 hpairs.1.1
  have hb1 : b ≠ 1 := hpairs.2.1
  have hb3 : b ^ 3 = 1 := h3 b hbA
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have hd'A : d' ∈ A := hd'B.1
  have hd'Z : d' ∈ Z := hd'B.2
  have hd'3 : d' ^ 3 = 1 := h3 d' hd'A
  have hZb' : Z ∈ thetaComponentsAt 3 b := (lZeroStarAt_subset A b) hpairs.2.2.1
  have hZC : Z ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hZb'
  have hZb : ∀ x ∈ Z, x * b * x⁻¹ = b := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hZC hx), mul_inv_cancel_right]
  have hconj : ∀ (g x y : G) (i j : ℕ), g * (x ^ i * y ^ j) * g⁻¹ =
      (g * x * g⁻¹) ^ i * (g * y * g⁻¹) ^ j := fun g x y i j => by
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, ← MulAut.conj_apply, map_mul, map_pow,
      map_pow]
  have hdd' : d ∈ Subgroup.zpowers d' := by
    by_contra hdd'
    have hint : ∀ x ∈ Subgroup.zpowers d, x ∈ Subgroup.zpowers d' → x = 1 := by
      intro x hx hx'
      by_contra hx1
      exact hdd' ((Subgroup.zpowers_le.mpr hx')
        (Item21Late2Proof.mem_zpowers_of_mem hd3 hx hx1 (Subgroup.mem_zpowers d)))
    have hw'dd : w' * d * w'⁻¹ = d := by
      have h1 := hint _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers d))
        (hnd w' hw'N)) (hw'A d hdA)
      rw [inv_mul_eq_one] at h1
      exact h1.symm
    have hd'b : d' ∉ Subgroup.zpowers b := by
      intro h
      apply hbZ
      exact (Subgroup.zpowers_le.mpr hd'Z)
        (Item21Late2Proof.mem_zpowers_of_mem hb3 h hd'1 (Subgroup.mem_zpowers b))
    have hB9 := Item21LateProof.card_zpowers_sup_zpowers (hcomm b hbA d' hd'A) hb3 hd'3 hb1 hd'b
    have hBA : Subgroup.zpowers b ⊔ Subgroup.zpowers d' ≤ A :=
      sup_le (Subgroup.zpowers_le.mpr hbA) (Subgroup.zpowers_le.mpr hd'A)
    have hw'B : ∀ y ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers d', w' * y * w'⁻¹ = y := by
      intro y hy
      obtain ⟨i, -, j, -, rfl⟩ :=
        Item21Late2Proof.exists_pow_mul_pow_of_mem_sup (hcomm b hbA d' hd'A) hb3 hd'3 hy
      rw [hconj, hZb w' hw'Z, hw'd']
    have hdB : d ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers d' := by
      by_contra hdB
      obtain ⟨y, hyA, hy⟩ := hw'move
      exact hy (Item21Late2Proof.conj_eq_of_fix hcomm h3 hBA (by rw [h27, hB9]) hdA hdB hw'B
        hw'dd y hyA)
    obtain ⟨i, hi, j, -, hdij⟩ :=
      Item21Late2Proof.exists_pow_mul_pow_of_mem_sup (hcomm b hbA d' hd'A) hb3 hd'3 hdB
    have hi0 : i ≠ 0 := by
      rintro rfl
      apply hdd'
      rw [hdij, pow_zero, one_mul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d') j
    have hdt : d * (t' * d * t'⁻¹) = b ^ (2 * i) := by
      have e1 : t' * d * t'⁻¹ = b ^ i * d'⁻¹ ^ j := by
        rw [hdij, hconj, hZb t' ht'Z, ht'd']
      have hc1 : Commute (d' ^ j) (b ^ i) :=
        Commute.pow_pow (show Commute d' b from hcomm d' hd'A b hbA) j i
      rw [e1, hdij]
      calc b ^ i * d' ^ j * (b ^ i * d'⁻¹ ^ j) = b ^ i * (d' ^ j * b ^ i) * d'⁻¹ ^ j := by group
        _ = b ^ i * (b ^ i * d' ^ j) * d'⁻¹ ^ j := by rw [hc1.eq]
        _ = b ^ (2 * i) := by rw [two_mul, pow_add, inv_pow]; group
    have hmem : b ^ (2 * i) ∈ Subgroup.zpowers d := by
      rw [← hdt]
      exact Subgroup.mul_mem _ (Subgroup.mem_zpowers d) (hnd t' ht'N)
    have hb2i : b ^ (2 * i) ≠ 1 := by
      interval_cases i
      · exact absurd rfl hi0
      · rw [show 2 * 1 = 2 by norm_num, Item21LateProof.sq_eq_inv_of_pow_three hb3]
        exact inv_ne_one.mpr hb1
      · rw [show 2 * 2 = 3 + 1 by norm_num, pow_add, hb3, one_mul, pow_one]
        exact hb1
    apply hdb
    exact (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers b) _))
      (Item21Late2Proof.mem_zpowers_of_mem hd3 hmem hb2i (Subgroup.mem_zpowers d))
  obtain ⟨k, hk, rfl⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hd'3 hdd'
  refine ⟨Subgroup.pow_mem _ hd'Z k, ?_⟩
  interval_cases k
  · exact absurd (pow_zero d') hd1
  · simpa using hd'T
  · rw [Item21LateProof.sq_eq_inv_of_pow_three hd'3]
    exact inducesTypeOn_one_inv hd'T

theorem exists_generic_offPlane_star
    (h211 : Item211) (h2115 : Item2115) (h2116 : Item2116) (h218 : Item218)
    (h2118 : Item2118) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h66 : Sec6.Item6_6)
    (hStar : Item2125Star) {A E U L U₀ X : Subgroup G} {c d a : G}
    (hE : Config2119End G A E U c L d U₀ a X) (h23 : Concl2123 L X c d)
    (h24 : Concl2124 A L X d) {e : G} (he : e ∈ A)
    (hecd : e ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d)
    (head : e ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers d)
    (heac : e ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers c) :
    ∃ Le ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card Le ∧ Nonempty (lBar Le ≃* lBar L) ∧
      d ∈ Le ∧ Sec4.InducesTypeOn Le d 1 ∧ Sec4.InducesTypeOn Le c 2 := by
  obtain ⟨Y, hgen⟩ := exists_gen2125 h211 h2116 h45 h48 h66 hE h23 h24 he hecd head heac
  obtain ⟨U₁, hU₁, Y', hpY⟩ := hStar G A E U c L d U₀ a X e Y hgen
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcfg := hE.cfg
  have hpair := hcfg.pair
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have h27 : Nat.card A = 27 := by rw [hcfg.card]; norm_num
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hdA : d ∈ A := hE.mem_d.1
  have hdL : d ∈ L := hE.mem_d.2
  have hd1 := hE.ne_one_d
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have he3 : e ^ 3 = 1 := h3 e he
  have hed : e ∉ Subgroup.zpowers d := fun h => hecd (Subgroup.mem_sup_right h)
  have he1 : e ≠ 1 := fun h => hed (h ▸ Subgroup.one_mem _)
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpairs.2.2.1
  have hcL : c ∉ L := (Item21Late2Proof.frame_of h45 h66 hcfg).1
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL ((Subgroup.zpowers_le.mpr hdL) h)
  obtain ⟨n, hn0, hne, ⟨eL⟩, -⟩ := hgen.iso
  have hpairY : Sec21Pair G A E U₁ e Y' :=
    { toSec21Std := hpair.toSec21Std
      mem_E := hpair.mem_E
      mem_U := hU₁
      mem_pair := hpY }
  obtain ⟨hde, hcfgY⟩ := config2119_of_pair h211 h2115 h218 h2118 h45 h66 hpairY h27 hdA hd1
    hE.normal_d
  obtain ⟨hdY', hdTY⟩ := mem_and_type_of_pair h45 h66 hcfgY hdA hd1 hde hE.normal_d
  have hY'e : Y' ∈ thetaComponentsAt 3 e :=
    lZeroStarAt_subset A e (mem_lThreeStarPairs_iff.mp hpY).2.2.1
  obtain ⟨m', hm'0, hm'e, ⟨eY'⟩⟩ := hcfgY.lthree
  have hZY' : Subgroup.center (lBar Y') = ⊥ :=
    center_eq_bot_of_mulEquiv' eY' (Item21Early2Proof.center_projSL_three_eq_bot hm'0 hm'e)
  have hYY' : Y = Y' := eq_of_mem_thetaComponentsAt_of_mem hgen.mem_Y hY'e le_rfl hZY' hdY'
    (hgen.le_I ((show d ∈ A ⊓ Sec11.sec11K L e by rw [hgen.inf_I]; exact Subgroup.mem_zpowers d).2))
    hd3 hd1
  subst hYY'
  have hdY : d ∈ Y := hdY'
  have hcTY : Sec4.InducesTypeOn Y c 2 :=
    inducesTypeOn_two_gen h45 h66 hcA hc1 hdA hd1 hcd hcfgY hdY hdTY hecd
  obtain ⟨m, hm0, hme, ⟨eY⟩⟩ := hcfgY.lthree
  obtain ⟨-, -, hIcard⟩ :=
    kf2123TypeTwo G L n hn0 hne ⟨eL⟩ e he3 hgen.type_L d hdL hd3 hE.type_d (hcomm e he d hdA)
  obtain ⟨hdJ, hJq, hJcard⟩ :=
    kf2123TypeTwo G Y m hm0 hme ⟨eY⟩ c (h3 c hcA) hcTY d hdY hd3 hdTY (hcomm c hcA d hdA)
  have hG4 := hpair.standing.toTheoremFourHyp
  have hE27 : Late.IsE27 A := ⟨hAe, h27⟩
  obtain ⟨K', hK', hJK'⟩ := Sec14.exists_mem_thetaComponentsAt_le_residual h48
    (hG4.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hG4 hc1)) hE27 he hcA he1
    hgen.mem_Y hJq
  have hZL : Subgroup.center (lBar L) = ⊥ :=
    center_eq_bot_of_mulEquiv' eL (Item21Early2Proof.center_projSL_three_eq_bot hn0 hne)
  have hK'L : K' = L := by
    by_contra hne'
    have h1 := le_thetaQuotCentralizer_of_ne hLc hK' (Ne.symm hne')
    exact hd1 (eq_one_of_mem_thetaQuotCentralizer hZL hdL (h1 (hJK' hdJ)) hd3)
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hYC : Y ≤ Subgroup.centralizer ({e} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hgen.mem_Y
  set I := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({e} : Set G)) with hIdef
  set J := inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({c} : Set G)) with hJdef
  have hIL : I ≤ L := (Sec6.inSubgroup_perfectResidual_le _).trans inf_le_left
  have hJY : J ≤ Y := (Sec6.inSubgroup_perfectResidual_le _).trans inf_le_left
  have hJI : J ≤ I := Sec6.le_inSubgroup_perfectResidual_of_isPerfect
    (Sec6.isPerfect_inSubgroup_perfectResidual _) (le_inf (hK'L ▸ hJK') (hJY.trans hYC))
  have hIJ : I ≤ J := Sec6.le_inSubgroup_perfectResidual_of_isPerfect
    (Sec6.isPerfect_inSubgroup_perfectResidual _) (le_inf hgen.le_I (hIL.trans hLC))
  have heq : I = J := le_antisymm hIJ hJI
  rw [heq, hJcard] at hIcard
  obtain rfl := eq_of_two_pow_mul_eq hIcard
  refine ⟨Y, hgen.mem_Y, ?_, ⟨eY.trans eL.symm⟩, hdY, hdTY, hcTY⟩
  have h1 := orderOf_dvd_natCard (⟨d, hdY⟩ : Y)
  rwa [Subgroup.orderOf_mk, orderOf_eq_prime hd3 hd1] at h1

theorem exists_generic_onPlane_star
    (h211 : Item211) (h2115 : Item2115) (h2116 : Item2116) (h218 : Item218)
    (h2118 : Item2118) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h66 : Sec6.Item6_6)
    (hStar : Item2125Star) {A E U L U₀ X : Subgroup G} {c d a : G}
    (hE : Config2119End G A E U c L d U₀ a X) (h23 : Concl2123 L X c d)
    (h24 : Concl2124 A L X d) {e : G} (he : e ∈ A)
    (hecd : e ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d)
    (head : e ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers d)
    (heac : e ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c) :
    ∃ Le ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card Le ∧ Nonempty (lBar Le ≃* lBar L) ∧
      d ∈ Le ∧ Sec4.InducesTypeOn Le d 1 ∧ Sec4.InducesTypeOn Le c 2 :=
  exists_onPlane_of_offPlane h45 h66 hE
    (fun _ he' hecd' head' heac' => exists_generic_offPlane_star h211 h2115 h2116 h218 h2118 h45
      h48 h66 hStar hE h23 h24 he' hecd' head' heac') he hecd head heac

theorem item2125Star_of_v (h45 : Sec4.Item4_5) (h49 : Sec4.Item4_9) (hV : Item2125V) :
    Item2125Star := by
  intro G _ _ A E U c L d U₀ a X e Y hgen
  obtain ⟨U₁, hU₁, heU₁, hV1⟩ := hV G A E U c L d U₀ a X e Y hgen
  have hpair := hgen.cfg.cfg.pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have he := hgen.mem_e
  have hed : e ∉ Subgroup.zpowers d := fun h => hgen.not_mem_cd (Subgroup.mem_sup_right h)
  have he1 : e ≠ 1 := fun h => hed (h ▸ Subgroup.one_mem _)
  have hEA : E ≤ A := hpair.mem_E.2
  have h27 : Nat.card A = 27 := by rw [hgen.cfg.cfg.card]; norm_num
  have hEeq : E = A := Subgroup.eq_of_le_of_card_ge hEA (by rw [h27, hpair.mem_E.1.2.1])
  have heE : e ∈ E := hEeq ▸ he
  obtain ⟨L', hL', hUL', hLU', -, hLV'⟩ := Sec6.exists_pair_of_mem_fourGroupsMinus
    hpair.standing h45 h49 hpair.mem_S hpair.mem_E hU₁ inf_le_left inf_le_right heE heU₁ he1 hV1
  have hA : ∀ L'' ∈ thetaComponentsAt 3 e, A ≤ Subgroup.normalizer (L'' : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe he he1
  exact ⟨U₁, hU₁.1, L', mem_lThreeStarPairs_of_six_twelve hEA hA ⟨heE, heU₁⟩ he1 hL' hUL' hLU'
    hLV'⟩

end Item2119End4Proof

open Item2119End4Proof

theorem item2125Generic_of_star
    (h211 : Item211) (h2115 : Item2115) (h2116 : Item2116) (h218 : Item218)
    (h2118 : Item2118) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h66 : Sec6.Item6_6)
    (hStar : Item2125Star) : Item2125Generic := by
  intro G _ _ A E U c L d U₀ a X hE h23 h24 e he hecd head
  by_cases heac : e ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c
  · exact exists_generic_onPlane_star h211 h2115 h2116 h218 h2118 h45 h48 h66 hStar hE h23 h24
      he hecd head heac
  · exact exists_generic_offPlane_star h211 h2115 h2116 h218 h2118 h45 h48 h66 hStar hE h23 h24
      he hecd head heac

end CFSG.RankThree.PartTwo.Sec21
