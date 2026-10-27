module

public import CFSG.RankThree.PartTwo.Sec15.Item15Type
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
import CFSG.RankThree.PartTwo.Sec14.Item145Bot
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec15.Item15Statements

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem three_dvd_card_quotient_of_eq_oPrimeResidualOf [Finite G] {Y : Subgroup G}
    (hY : Y = oPrimeResidualOf 3 Y) (N : Subgroup ↥Y) [N.Normal] (hN : N ≠ ⊤) :
    3 ∣ Nat.card (↥Y ⧸ N) := by
  by_contra h3
  apply hN
  have hres : oPrimeResidual 3 ↥Y = ⊤ := by
    apply Subgroup.map_injective Y.subtype_injective
    change oPrimeResidualOf 3 Y = (⊤ : Subgroup ↥Y).map Y.subtype
    rw [← hY, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [eq_top_iff, ← hres]
  refine (Subgroup.closure_le _).mpr fun y hy => ?_
  obtain ⟨k, hk⟩ := hy
  rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff]
  have h1 : orderOf (y : ↥Y ⧸ N) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one (by
    rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one])
  have h2 : orderOf (y : ↥Y ⧸ N) ∣ Nat.card (↥Y ⧸ N) := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (↥Y ⧸ N)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem not_dvd_relIndex_sup_of_card {X O : Subgroup G} (hO : ¬ 3 ∣ Nat.card O)
    (hcard : Nat.card (X ⊔ O : Subgroup G) * Nat.card (X ⊓ O : Subgroup G) =
      Nat.card X * Nat.card O) : ¬ 3 ∣ X.relIndex (X ⊔ O) := by
  have h1 := Subgroup.relIndex_mul_card X (X ⊔ O)
  rw [inf_of_le_left le_sup_left] at h1
  have h2 : X.relIndex (X ⊔ O) * Nat.card (X ⊓ O : Subgroup G) = Nat.card O := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := X))
    rw [← hcard, ← h1]
    ring
  intro h3
  exact hO (h3.trans ⟨_, h2.symm⟩)

theorem not_dvd_relIndex_sup_of_le_normalizer {X O : Subgroup G} (hO : ¬ 3 ∣ Nat.card O)
    (hXO : X ≤ Subgroup.normalizer (O : Set G)) : ¬ 3 ∣ X.relIndex (X ⊔ O) := by
  refine not_dvd_relIndex_sup_of_card hO ?_
  have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hXO
  rw [sup_comm, inf_comm, mul_comm (Nat.card O)] at h
  exact h

theorem not_dvd_relIndex_sup_of_normalizer_le {X O : Subgroup G} (hO : ¬ 3 ∣ Nat.card O)
    (hOX : O ≤ Subgroup.normalizer (X : Set G)) : ¬ 3 ∣ X.relIndex (X ⊔ O) :=
  not_dvd_relIndex_sup_of_card hO
    (CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hOX)

theorem relIndex_sup_dvd_of_le_normalizer {A X L : Subgroup G} (hXL : X ≤ L)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    (A ⊔ X).relIndex (A ⊔ L) ∣ X.relIndex L := by
  have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hAX
  have h2 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hAL
  rw [sup_comm] at h1 h2
  have hle : A ⊔ X ≤ A ⊔ L := sup_le_sup_left hXL A
  have h3 := Subgroup.relIndex_mul_card (A ⊔ X) (A ⊔ L)
  rw [inf_of_le_left hle] at h3
  have h4 := Subgroup.relIndex_mul_card X L
  rw [inf_of_le_left hXL] at h4
  have hinf : X ⊓ A ≤ L ⊓ A := inf_le_inf_right A hXL
  have h5 := Subgroup.relIndex_mul_card (X ⊓ A) (L ⊓ A)
  rw [inf_of_le_left hinf] at h5
  refine ⟨(X ⊓ A).relIndex (L ⊓ A), ?_⟩
  have hpos : 0 < Nat.card X * Nat.card A := Nat.mul_pos Nat.card_pos Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc X.relIndex L * (Nat.card X * Nat.card A)
      = Nat.card (A ⊔ L : Subgroup G) * Nat.card (L ⊓ A : Subgroup G) := by
        rw [h2, ← h4]; ring
    _ = (A ⊔ X).relIndex (A ⊔ L) * (X ⊓ A).relIndex (L ⊓ A) * (Nat.card X * Nat.card A) := by
        rw [← h3, ← h5, ← h1]; ring

theorem exists_le_map_conj_of_not_dvd_relIndex {M K E : Subgroup G} (hMK : M ≤ K)
    (hidx : ¬ 3 ∣ M.relIndex K) (hEK : E ≤ K) (hE : IsPGroup 3 E) :
    ∃ k ∈ K, E ≤ M.map (MulAut.conj k).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, hT⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 M
  have hT' := hT
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hT'
  have hTK : CFSG.ABGLocalTools.IsSylowOf 3 T K := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hT'.1.trans hMK, hT'.2.1, fun h => ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex T M K hT'.1 hMK] at h
    exact ((Nat.Prime.dvd_mul Nat.prime_three).mp h).elim hT'.2.2 hidx
  obtain ⟨Q, hQ⟩ := hTK.exists_sylow_eq_subgroupOf
  obtain ⟨P, hP⟩ := (hE.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q P
  refine ⟨(g : G), g.2, fun x hx => ?_⟩
  have hxP : (⟨x, hEK hx⟩ : K) ∈ (P : Subgroup K) := hP hx
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hxP
  obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp hxP
  have hqT : (q : G) ∈ T := by
    have : q ∈ T.subgroupOf K := hQ ▸ hq
    exact Subgroup.mem_subgroupOf.mp this
  refine ⟨q, hT'.1 hqT, ?_⟩
  have := congrArg Subtype.val hqx
  simpa [MulAut.conj_apply] using this

theorem mem_partTwoE_of_not_dvd_relIndex {M K U E : Subgroup G} (hMK : M ≤ K)
    (hidx : ¬ 3 ∣ M.relIndex K) (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) (hEK : E ≤ K)
    (hEab : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) : E ∈ partTwoE G := by
  have hE3 : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hEab.2 g g.2)⟩
  obtain ⟨k, -, hk⟩ := exists_le_map_conj_of_not_dvd_relIndex hMK hidx hEK hE3
  refine ⟨hEab, hE27, U.map (MulAut.conj k).toMonoidHom,
    fun h => hU ((Subgroup.map_eq_bot_iff_of_injective U (MulAut.conj k).injective).mp h),
    hU2.map _, ?_⟩
  rw [← Subgroup.map_equiv_normalizer_eq]
  exact hk.trans (Subgroup.map_mono hMU)

theorem exists_lA_dec_of_isSimpleGroup_img148
    {A : Subgroup G} {LB : Subgroup G → Subgroup G} (h148 : Item148 A LB) {Y : Subgroup G}
    (hY : Y ∈ scriptY A) (hAab : IsMulCommutative A) (hPGL : KFacts.KS15Z3PGLNonabelian)
    {K : Type} [Group K] (hKs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a)
    (he : letI := ker148_normal hY.2
      Nonempty (↥(img148 A Y (deltaZero A LB Y)) ≃* K))
    (hA5 : IsEmpty (K ≃* alternatingGroup (Fin 5)))
    (hA7 : IsEmpty (K ≃* alternatingGroup (Fin 7)))
    (hA10 : IsEmpty (K ≃* alternatingGroup (Fin 10)))
    (hL3 : ∀ (p f : ℕ) [Fact p.Prime], ¬ IsLThreeEpsAt K p f) :
    ∃ c' : G, Subgroup.zpowers c' ∈ omegaA A ∧
      deltaZero A LB Y = pPrimeCoreOf 3 (deltaZero A LB Y) ⊔
        deltaZero A LB (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G)) ∧
      ∃ L' ∈ lA A c', Nonempty (K ≃* ↥L' ⧸ aschbacherSolvableCore 3 ↥L') := by
  let := ker148_normal hY.2
  obtain ⟨e⟩ := he
  set X := img148 A Y (deltaZero A LB Y) with hX
  have hXs : IsSimpleGroup ↥X := e.isSimpleGroup
  have hXnab : ∃ a b : ↥X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hXnt : Nontrivial ↥X := hXs.toNontrivial
  rcases (h148 Y hY).2 with h1 | h2 | h3 | h4 | h5 | h6 | h7
  ·
    exfalso
    have hX1 : X = ⊥ := img148_eq_bot_of_le h1
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥X)
    exact hx (Subtype.ext ((Subgroup.mem_bot).mp (hX1 ▸ x.2)))
  ·
    obtain ⟨c', hc', hdec, L', hL', hcases⟩ := h2
    rcases hcases with hφ | ⟨-, hφ⟩ | ⟨p, f, e', hp, -, -, -, hL3'⟩ | ⟨-, h3A6 | hφ⟩
    · obtain ⟨φ⟩ := hφ
      exact ⟨c', hc', hdec, L', hL', ⟨e.symm.trans φ⟩⟩
    · obtain ⟨φ⟩ := hφ
      exact (hA7.false (e.symm.trans φ)).elim
    · exact (hL3 p f (IsLThreeEpsAt.of_mulEquiv e hL3')).elim
    · exact (not_isTripleCover_of_isSimpleGroup hXs hXnab h3A6).elim
    · obtain ⟨φ⟩ := hφ
      exact (hA5.false (e.symm.trans φ)).elim
  ·
    exfalso
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h⟩ := h3
    rcases h with hON | hCP | hA6A5 | hφ | hφ | ⟨_, hφ⟩
    · exact not_isTripleCover_of_isSimpleGroup hXs hXnab hON
    · exact not_isCentralProductA6Covers_of_isSimpleGroup hXs hXnab hCP
    · exact not_isA6CoverTimesA5_of_isSimpleGroup hXs hA6A5
    · obtain ⟨φ⟩ := hφ
      exact (isEmpty_mulEquiv_prod_of_isSimpleGroup hXs).false φ
    · obtain ⟨φ⟩ := hφ
      exact hA7.false (e.symm.trans φ)
    · obtain ⟨φ⟩ := hφ
      exact hL3 7 1 (Or.inl ⟨e.symm.trans φ⟩)
  ·
    obtain ⟨hφ, -⟩ := h4
    obtain ⟨φ⟩ := hφ
    exact (hA10.false (e.symm.trans φ)).elim
  ·
    obtain ⟨-, -, -, n, -, -, -, hn, -, hiso, -⟩ := h5
    have hq : 2 < 2 ^ (3 * n) := by
      calc 2 < 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (hL3 2 (3 * n) (IsLThreeEpsAt.of_mulEquiv e (isLThreeEpsAt_of_isoLThreePi hq hiso))).elim
  ·
    obtain ⟨hφ, -⟩ := h6
    obtain ⟨φ⟩ := hφ
    exact ((isEmpty_mulEquiv_prod_of_isSimpleGroup' hXs
      ⟨fun ψ => hA5.false (e.symm.trans ψ)⟩).false φ).elim
  ·
    exfalso
    obtain ⟨-, -, L₁, L₂, J₁, J₂, p₁, f₁, -, p₂, f₂, -, -, -, -, -, -, -, hJ₁, hJ₂, hsup, hinf,
      hcomm, -, -, -, -, hZ₁, hZ₂, -, -⟩ := h7
    rw [← hX] at hsup
    have hJ₁le : img148 A Y J₁ ≤ X := hsup ▸ le_sup_left
    have hJ₂le : img148 A Y J₂ ≤ X := hsup ▸ le_sup_right
    have hN : ((img148 A Y J₁).subgroupOf X).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJ₁le).mpr ?_
      rw [← hsup]
      refine sup_le Subgroup.le_normalizer ?_
      have hC : img148 A Y J₂ ≤ Subgroup.centralizer (img148 A Y J₁ : Set _) := by
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
        exact hcomm
      exact hC.trans (Subgroup.centralizer_le_normalizer _)
    have hbot : img148 A Y J₁ = ⊥ ∨ img148 A Y J₂ = ⊥ := by
      rcases hN.eq_bot_or_eq_top with h | h
      · left
        rw [Subgroup.subgroupOf_eq_bot] at h
        exact disjoint_self.mp (h.mono_right hJ₁le)
      · right
        rw [Subgroup.subgroupOf_eq_top] at h
        have := le_inf (hJ₂le.trans h) le_rfl
        rwa [hinf, le_bot_iff] at this
    have hAle : A ≤ Y ⊔ A := le_sup_right
    have key : ∀ J : Subgroup G, J ≤ Y → img148 A Y J = ⊥ →
        ∀ p f : ℕ, IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f → False := by
      intro J hJY hJ p f hZ
      rw [img148_sup (hJY.trans le_sup_left) hAle, hJ, bot_sup_eq] at hZ
      obtain ⟨a, b, hab⟩ := hPGL _ p f hZ
      exact hab (img148_comm hAab a b)
    rcases hbot with h | h
    · exact key J₁ (hJ₁.trans inf_le_right) h p₁ f₁ hZ₁
    · exact key J₂ (hJ₂.trans inf_le_right) h p₂ f₂ hZ₂

@[expose] def Claim157EY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A),
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.M12) →
      ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
        Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M12) →
        Y = pPrimeCoreOf 3 Y ⊔
          deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G)) →
        ∀ E : Subgroup G, E ≤ (A ⊔ L') ⊓ Subgroup.normalizer (A : Set G) →
          CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
          Nonempty (Sec4.autIn L' E ≃* GL (Fin 2) (ZMod 3)) → E ∈ partTwoE G

theorem rank3II_15_7_of_eq_deltaZero
    (h137 : Item137) (hPGL : KFacts.KS15Z3PGLNonabelian)
    (hM12s : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M12)
    (hM12L3 : ∀ (p f : ℕ) [Fact p.Prime], ¬ IsLThreeEpsAt CFSG.Blueprint.NativeSporadic.M12 p f)
    (hM12A : IsEmpty (CFSG.Blueprint.NativeSporadic.M12 ≃* alternatingGroup (Fin 5)) ∧
      IsEmpty (CFSG.Blueprint.NativeSporadic.M12 ≃* alternatingGroup (Fin 7)) ∧
      IsEmpty (CFSG.Blueprint.NativeSporadic.M12 ≃* alternatingGroup (Fin 10)))
    (hE : Claim157EY) {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h148 : Item148 A (lB A))
    (hΔ : ∀ Y ∈ scriptY4 A (lB A), Y = deltaZero A (lB A) Y) : Item157 A (lB A) := by
  intro Y hY
  refine ⟨fun φ => ?_⟩
  have hY4 : Y ∈ scriptY4 A (lB A) := hY.prop.1
  have hYΔ : Y = deltaZero A (lB A) Y := hΔ Y hY4
  have hYY : Y ∈ scriptY A := hY4.1
  have hM12nab : ∃ a b : CFSG.Blueprint.NativeSporadic.M12, a * b ≠ b * a := by
    obtain ⟨-, -, a, b, hab⟩ := hY4.2.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨φ a, φ b, fun h => hab ?_⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact φ.injective (by rw [map_mul, map_mul, h])
  have hQs : IsSimpleGroup (↥Y ⧸ CFSG.pCore 2 ↥Y) := φ.isSimpleGroup
  have hO2 : CFSG.pCore 2 ↥Y ≠ ⊤ := by
    intro h2
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥Y ⧸ CFSG.pCore 2 ↥Y)
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    exact hx ((QuotientGroup.eq_one_iff y).mpr (h2 ▸ Subgroup.mem_top y))
  have h3 := three_dvd_card_quotient_of_eq_oPrimeResidualOf hY4.2.1 (CFSG.pCore 2 ↥Y) hO2
  have hcore : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y :=
    pPrimeCore_three_eq_pCore_two (pPrimeCore_three_eq_bot_of_isSimpleGroup hQs h3)
  have he : letI := ker148_normal hY.prop.1.1.2
      Nonempty (↥(img148 A Y (deltaZero A (lB A) Y)) ≃* CFSG.Blueprint.NativeSporadic.M12) := by
    let := ker148_normal hY.prop.1.1.2
    obtain ⟨ψ⟩ := nonempty_img148_equiv hYY.2
    rw [← hYΔ]
    exact ⟨ψ.trans ((QuotientGroup.quotientMulEquivOfEq hcore).trans φ)⟩
  obtain ⟨c', hc', hdec, L', hL', ⟨ψ⟩⟩ := exists_lA_dec_of_isSimpleGroup_img148 h148 hYY
    h.isElemAbelian.1 hPGL hM12s hM12nab he hM12A.1 hM12A.2.1 hM12A.2.2 hM12L3
  rw [← hYΔ] at hdec
  have hD' : Sec13Data G A c' L' :=
    { h.toSec13Data with zpowers_mem_omegaA := hc', mem_lA := hL' }
  obtain ⟨E, hEle, hEab, hE27, hEaut, -, hnT⟩ := h137 G A c' L' hD' ⟨ψ.symm⟩
  have hEE : E ∈ partTwoE G :=
    hE G A c L h Y hY ⟨φ⟩ c' L' hc' hL' ⟨ψ.symm⟩ hdec E hEle hEab hE27 hEaut
  have hFE : partTwoF G = partTwoE G :=
    (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
  have hc'3 : c' ^ 3 = 1 := by
    rw [← hD'.orderOf_eq]
    exact pow_orderOf_eq_one c'
  have hEC : E ≤ Subgroup.centralizer ({c'} : Set G) :=
    hEle.trans (inf_le_left.trans (sup_le hD'.A_le_centralizer hD'.le_centralizer))
  have hc'E : c' ∈ E := Sec15.mem_of_mem_partTwoF (hFE ▸ hEE) hc'3 hEC
  have hAE : A ∈ partTwoE G := hD'.mem_partTwoE
  have hER : E ∈ reachE A :=
    ⟨hEE, Relation.ReflTransGen.single ⟨hAE, hEE, ⟨Subgroup.zpowers c', hc',
      Subgroup.zpowers_le.mpr hc'E⟩⟩⟩
  exact hnT (hypT_of_mem_reachE h.toTheoremFourHyp h.partTwoS_eq h.hypR hER)

theorem rank3II_15_7_of
    (h137 : Item137) (h134 : Item134) (h135 : Item135)
    (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (hJ2c : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥)
    (hPGL : KFacts.KS15Z3PGLNonabelian)
    (hM12s : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M12)
    (hM12L3 : ∀ (p f : ℕ) [Fact p.Prime], ¬ IsLThreeEpsAt CFSG.Blueprint.NativeSporadic.M12 p f)
    (hM12A : IsEmpty (CFSG.Blueprint.NativeSporadic.M12 ≃* alternatingGroup (Fin 5)) ∧
      IsEmpty (CFSG.Blueprint.NativeSporadic.M12 ≃* alternatingGroup (Fin 7)) ∧
      IsEmpty (CFSG.Blueprint.NativeSporadic.M12 ≃* alternatingGroup (Fin 10)))
    (hE : Claim157EY) {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h148 : Item148 A (lB A)) : Item157 A (lB A) :=
  rank3II_15_7_of_eq_deltaZero h137 hPGL hM12s hM12L3 hM12A hE h h148 fun _ hY4 =>
    rank3II_15_1_of h134 h135 h48 h415 hJ2c h.toSec14Std hY4

end CFSG.RankThree.PartTwo.Sec15
