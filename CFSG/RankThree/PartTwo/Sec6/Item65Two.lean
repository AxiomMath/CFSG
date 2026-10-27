module

public import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.Milestones.OO_odd_order_solvable
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem two_dvd_card_of_isPerfect {X : Subgroup G} (hXp : Group.IsPerfect X) (hX1 : X ≠ ⊥) :
    2 ∣ Nat.card X := by
  by_contra hodd
  have hsol : Group.IsSolvable X :=
    CFSG.Milestones.odd_order_solvable (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd))
  have : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX1
  have := hXp
  exact Group.IsPerfect.not_isSolvable X hsol

theorem isElemAbelian_sup_zpowers_three {B : Subgroup G} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    {x : G} (hxB : x ∉ B) (hx3 : x ^ 3 = 1) (hxc : ∀ β ∈ B, β * x = x * β) :
    CFSG.Assembly.IsElemAbelian 3 (B ⊔ Subgroup.zpowers x) ∧
      Nat.card (B ⊔ Subgroup.zpowers x : Subgroup G) = Nat.card B * 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact Sec5.isElemAbelian_sup_zpowers hB hxB hx3 hxc

theorem rank3II_6_5_two (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (hG : PartTwoStanding G)
    {A : Subgroup G} (hA : A ∈ partTwoS G) {L : Subgroup G} (hL : L ∈ thetaComponentFamily 3 A)
    {B : Subgroup G} (hBab : CFSG.Assembly.IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hBAL : B ≤ A ⊓ thetaQuotCentralizer L)
    (hno : ∀ E ∈ collectionIn (partTwoE G) (A ⊔ L), ¬ B ≤ E) :
    3 < CFSG.Open.pRank 3 A ∧ ∃ b ∈ B, b ≠ 1 ∧ ∃ K ∈ thetaComponentsAt 3 b,
      inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {b}) ⊔
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {b})) < K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a₀, ha₀A, ha₀1, hLa₀⟩ := mem_thetaComponentFamily_iff.mp hL
  have hAF := hA.1
  have hAab := hAF.1
  have hA3 : IsPGroup 3 A := Sec5.isPGroup_of_isElemAbelian hAab
  have hBA : B ≤ A := hBAL.trans inf_le_left
  have hBC : B ≤ thetaQuotCentralizer L := hBAL.trans inf_le_right
  have hB3 : IsPGroup 3 B := Sec5.isPGroup_of_isElemAbelian hBab
  have hLp := isPerfect_of_mem_thetaComponentsAt hLa₀
  have hLq := isQuasisimple_of_mem_thetaComponentsAt hLa₀
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_mem_thetaComponentsAt h45 hG.toTheoremFourHyp hAab ha₀A ha₀1 L hLa₀
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hkey : ∀ E : Subgroup G, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 → B ≤ E →
      E ≤ A ⊔ L → ∀ U : Subgroup G, U ≠ ⊥ → IsPGroup 2 U →
        E ≤ Subgroup.normalizer (U : Set G) → False :=
    fun E hE hE27 hBE hEAL U hU1 hU2 hEU => hno E ⟨⟨hE, hE27, U, hU1, hU2, hEU⟩, hEAL⟩ hBE
  obtain ⟨n, hn3, hAcard⟩ := exists_card_eq_of_mem_partTwoF hAF
  have hn4 : 4 ≤ n := by
    by_contra hlt
    have hn : n = 3 := by omega
    obtain ⟨E₀, hE₀, hE₀A⟩ := hAF.2.2
    have hE₀eq : E₀ = A := Subgroup.eq_of_le_of_card_ge hE₀A (by rw [hAcard, hn, hE₀.2.1]; norm_num)
    exact hno E₀ ⟨hE₀, hE₀eq ▸ le_sup_left⟩ (hE₀eq ▸ hBA)
  have hrank : 3 < CFSG.Open.pRank 3 A := by
    have hle : n ≤ CFSG.Open.pRank 3 A :=
      le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three A)
        ⟨A, le_rfl, hAab, hAcard⟩
    omega
  refine ⟨hrank, ?_⟩
  by_contra hcon
  push Not at hcon
  have hBlt : B < A := by
    refine lt_of_le_of_ne hBA fun h => ?_
    have h1 : Nat.card A = 9 := h ▸ hB9
    rw [hAcard] at h1
    have : 3 ^ n ≥ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) hn4
    omega
  by_cases hL3 : 3 ∣ Nat.card L
  ·
    set Z := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (B : Set G)) with hZ
    have hZp : Group.IsPerfect Z := isPerfect_inSubgroup_perfectResidual _
    have hZL : Z ≤ L := (inSubgroup_perfectResidual_le _).trans inf_le_left
    have hZB : Z ≤ Subgroup.centralizer (B : Set G) :=
      (inSubgroup_perfectResidual_le _).trans inf_le_right
    have hcov := le_residual_inf_centralizer_sup_theta hLp hB3 hBC
    have hZ3 : 3 ∣ Nat.card Z := by
      have hLeq : Z ⊔ inSubgroup (aschbacherSolvableCore 3) L = L :=
        le_antisymm (sup_le hZL (theta_le L)) hcov
      have h1 := card_sup_mul_card_inf (X := Z) (N := inSubgroup (aschbacherSolvableCore 3) L)
        (hZL.trans (le_normalizer_theta L))
      rw [hLeq] at h1
      have h2 : 3 ∣ Nat.card Z * Nat.card (inSubgroup (aschbacherSolvableCore 3) L) :=
        h1 ▸ hL3.mul_right _
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h2 with h | h
      · exact h
      · exact absurd h (theta_solvable_and_not_dvd L).2
    have hBZ : B ≤ Subgroup.centralizer (Z : Set G) := fun β hβ =>
      Subgroup.mem_centralizer_iff.mpr fun z hz =>
        (Subgroup.mem_centralizer_iff.mp (hZB hz) β hβ).symm
    obtain ⟨e, heZ, he3, heB⟩ := exists_pow_three_eq_one_not_mem hZp hZ3 hBZ
    have hec : ∀ β ∈ B, β * e = e * β := fun β hβ =>
      Subgroup.mem_centralizer_iff.mp (hZB heZ) β hβ
    obtain ⟨hEab, hEcard⟩ := isElemAbelian_sup_zpowers_three hBab heB he3 hec
    set E := B ⊔ Subgroup.zpowers e with hE
    have hE27 : Nat.card E = 27 := by rw [hEcard, hB9]
    have hEAL : E ≤ A ⊔ L :=
      sup_le (hBA.trans le_sup_left) (Subgroup.zpowers_le.mpr (le_sup_right (a := A) (hZL heZ)))
    have hE3 : IsPGroup 3 E := Sec5.isPGroup_of_isElemAbelian hEab
    have hZ1 : Z ≠ ⊥ := residual_inf_centralizer_ne_bot hLp hLq hB3 hBC
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (two_dvd_card_of_isPerfect hZp hZ1)
    set T := Subgroup.zpowers (t : G) with hT
    have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 1) (by
      rw [hT, Nat.card_zpowers, Subgroup.orderOf_coe, ht, pow_one])
    have hT1 : T ≠ ⊥ := by
      intro h
      have : (t : G) = 1 := by
        have := Subgroup.mem_zpowers (t : G)
        rw [← hT, h, Subgroup.mem_bot] at this
        exact this
      have : t = 1 := Subtype.ext this
      rw [this, orderOf_one] at ht
      norm_num at ht
    have hBT : B ≤ Subgroup.centralizer (T : Set G) := by
      rw [hT, centralizer_zpowers_eq]
      intro β hβ
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hZB t.2) β hβ)
    have hB1 : B ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hB9
      norm_num at hB9
    obtain ⟨b, hbB, hb1, hR⟩ := exists_commutator_inf_centralizer_ne_bot hG.charTwoType hT2 hT1
      hBab hB9.ge hBT le_rfl hB1
    set Q := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (T : Set G)) with hQ
    set S := Q ⊓ Subgroup.centralizer {b} with hS
    set R := ⁅S, B⁆ with hRdef
    have hbA := hBA hbB
    have hBb : B ≤ Subgroup.centralizer ({b} : Set G) := fun β hβ =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcommA β (hBA hβ) b hbA)
    have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup.map _
    have hBQ : B ≤ Subgroup.normalizer (Q : Set G) :=
      hBT.trans (Subgroup.le_normalizer.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
          (CFSG.pCore 2 (Subgroup.centralizer (T : Set G)))))
    have hBS : B ≤ Subgroup.normalizer (S : Set G) :=
      (le_inf hBQ (hBb.trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hRS : R ≤ S := Subgroup.le_normalizer_iff_commutator_le_left.mp hBS
    have hR2 : IsPGroup 2 R := (hQ2.to_le inf_le_left).to_le hRS
    have hRRB : ⁅R, B⁆ = R := by
      have hcop : (Nat.card B).Coprime (Nat.card S) := by
        obtain ⟨k, hk⟩ := (hQ2.to_le inf_le_left).exists_card_eq
        rw [hB9, hk]
        exact Nat.Coprime.pow_right k (by norm_num)
      exact CFSG.BenderSuzuki.ig1114_commutator_idempotent_of_coprime S B hcop hBS
    have hRb : R ≤ Subgroup.centralizer ({b} : Set G) := hRS.trans inf_le_right
    have hBR : B ≤ Subgroup.normalizer (R : Set G) := le_normalizer_commutator_right S B
    obtain ⟨K, hK, hLbK⟩ :=
      exists_mem_thetaComponentsAt_residual_le h48 hG hAF ha₀A ha₀1 hbA hb1 hLa₀ (hBC hbB)
    have heq : inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {b}) ⊔
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {b})) = K :=
      eq_of_le_of_not_lt hLbK (hcon b hbB hb1 K hK)
    have hAK : ∀ K' ∈ thetaComponentsAt 3 b, A ≤ Subgroup.normalizer (K' : Set G) :=
      le_normalizer_of_mem_thetaComponentsAt h45 hG.toTheoremFourHyp hAab hbA hb1
    have hBK : B ≤ Subgroup.normalizer (K : Set G) := hBA.trans (hAK K hK)
    have hBKC : B ≤ thetaQuotCentralizer K :=
      le_thetaQuotCentralizer_of_residual_eq hBC hBb hK hBK heq
    have hRK : R ≤ Subgroup.normalizer (K : Set G) :=
      commutator_le_normalizer_of_mem_thetaComponentsAt (X := S) (inf_le_right.trans le_rfl)
        (fun L' hL' => hBA.trans (hAK L' hL')) hK
    have hRKC : R ≤ thetaQuotCentralizer K := by
      rw [← hRRB, Subgroup.commutator_le]
      intro r hr β hβ
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (conj_mem_thetaQuotCentralizer (hBKC hβ) (hRK hr))
        (inv_mem (hBKC hβ))
    have heK : e ∈ K := by
      rw [← heq]
      refine inSubgroup_perfectResidual_mono le_sup_left
        (inSubgroup_perfectResidual_mono ?_ heZ)
      exact inf_le_inf_left L (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB))
    set θb := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G))
      with hθb
    have hθKb : inSubgroup (aschbacherSolvableCore 3) K ≤ θb := by
      rw [theta_eq_inf_of_mem_thetaComponentsAt hK]
      exact inf_le_right
    have heb : e ∈ Subgroup.centralizer ({b} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hec b hbB).symm
    set X := R ⊔ θb with hX
    have hEX : E ≤ Subgroup.normalizer (X : Set G) := by
      refine sup_le (le_normalizer_sup_of_conj ?_ ?_) ?_
      · intro β hβ x hx
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hBR hβ) x).mp hx)
      · intro β hβ x hx
        exact Subgroup.mem_sup_right
          ((Subgroup.mem_normalizer_iff.mp (le_normalizer_theta _ (hBb hβ)) x).mp hx)
      · refine le_normalizer_sup_of_conj (A := Subgroup.zpowers e) ?_ ?_
        · intro g hg r hr
          have hgK : g ∈ K := (Subgroup.zpowers_le.mpr heK) hg
          have hr' : r⁻¹ ∈ thetaQuotCentralizer K := inv_mem (hRKC hr)
          have h1 := (mem_thetaQuotCentralizer_iff.mp hr').2 g hgK
          have h2 : g * (g⁻¹ * (r⁻¹ * g * r⁻¹⁻¹)) * g⁻¹ ∈
              inSubgroup (aschbacherSolvableCore 3) K :=
            (Subgroup.mem_normalizer_iff.mp (le_normalizer_theta K hgK) _).mp h1
          rw [show g * r * g⁻¹ = r * (g * (g⁻¹ * (r⁻¹ * g * r⁻¹⁻¹)) * g⁻¹) by group]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right (hθKb h2))
        · intro g hg x hx
          have hgb : g ∈ Subgroup.centralizer ({b} : Set G) :=
            (Subgroup.zpowers_le.mpr heb) hg
          exact Subgroup.mem_sup_right
            ((Subgroup.mem_normalizer_iff.mp (le_normalizer_theta _ hgb) x).mp hx)
    have hX3 : ¬ 3 ∣ Nat.card X := not_dvd_card_sup_of_isPGroup Nat.prime_three (by norm_num) hR2
      (hRb.trans (le_normalizer_theta _)) (theta_solvable_and_not_dvd _).2
    obtain ⟨P, hEP⟩ :=
      CFSG.RankThreeEvenClassification.Helpers.exists_normalized_sylow_in_prime_complement_subgroup
        3 Nat.prime_three E X hE3 hX3 hEX 2 Nat.prime_two
    have hR1 : R ≠ ⊥ := hR
    have h2X : 2 ∣ Nat.card X := by
      obtain ⟨k, hk⟩ := hR2.exists_card_eq
      have hk0 : k ≠ 0 := by
        rintro rfl
        apply hR1
        exact Subgroup.eq_bot_of_card_eq R (by rw [hk, pow_zero])
      have h1 : 2 ∣ Nat.card R := hk ▸ dvd_pow_self 2 hk0
      exact h1.trans (Subgroup.card_dvd_of_le le_sup_left)
    have hP1 : (P : Subgroup X).map X.subtype ≠ ⊥ := by
      rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective]
      exact Sylow.ne_bot_of_dvd_card P h2X
    exact hkey E hEab hE27 le_sup_left hEAL _ hP1 (P.isPGroup'.map X.subtype) hEP
  ·
    obtain ⟨S, hAS⟩ :=
      CFSG.RankThreeEvenClassification.Helpers.exists_normalized_sylow_in_prime_complement_subgroup
        3 Nat.prime_three A L hA3 hL3 hAL 2 Nat.prime_two
    have hL1 : L ≠ ⊥ := by
      intro h
      apply (CFSG.LocalCores.isQuasisimple_nontrivial hLq).exists_pair_ne.elim
      intro x hx
      obtain ⟨y, hxy⟩ := hx
      apply hxy
      induction x using QuotientGroup.induction_on with
      | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
      have hx1 : x = 1 := Subtype.ext (by simpa [h] using x.2)
      have hy1 : y = 1 := Subtype.ext (by simpa [h] using y.2)
      rw [hx1, hy1]
    have hS1 : (S : Subgroup L).map L.subtype ≠ ⊥ := by
      rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective]
      exact Sylow.ne_bot_of_dvd_card S (two_dvd_card_of_isPerfect hLp hL1)
    obtain ⟨x, hxA, hxB⟩ := IsConcreteLE.exists_of_lt hBlt
    obtain ⟨hEab, hEcard⟩ := isElemAbelian_sup_zpowers_three hBab hxB (hAab.2 x hxA)
      (fun β hβ => hcommA β (hBA hβ) x hxA)
    exact hkey _ hEab (by rw [hEcard, hB9]) le_sup_left
      ((sup_le hBA (Subgroup.zpowers_le.mpr hxA)).trans le_sup_left) _ hS1
      (S.isPGroup'.map L.subtype) ((sup_le hBA (Subgroup.zpowers_le.mpr hxA)).trans hAS)

end CFSG.RankThree.PartTwo.Sec6
