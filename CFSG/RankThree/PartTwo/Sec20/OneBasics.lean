module

public import CFSG.RankThree.PartTwo.Sec20.OneTools
public import CFSG.RankThree.PartTwo.KFacts.L34NormalizerMax
import CFSG.RankThree.PartTwo.Sec18.Item184a
import CFSG.RankThree.PartTwo.Sec18.Item181b
import CFSG.RankThree.PartTwo.KFacts.KS18OuterHeis
import CFSG.RankThree.PartTwo.Sec20.Step208MSPairProof

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

theorem exists_sec18H_of_hyp201One {A M L N : Subgroup G} {c : G}
    (h : Hyp201One G A M L N c) :
    ∃ H : Subgroup G, Sec18.Sec18H G A M H c ∧ Sec18.Hyp187 A M H c ∧
      L = inSubgroup perfectResidual H ∧ N = Subgroup.normalizer (L : Set G) := by
  obtain ⟨T, hT⟩ := exists_ctx20 h.1
  exact exists_sec18H_of_ctx20One ⟨hT, h.2⟩

theorem not_le_of_hyp201One {A M L N : Subgroup G} {c : G} (h : Hyp201One G A M L N c) :
    ¬ L ≤ M := by
  obtain ⟨H, hH18, -, hL, -⟩ := exists_sec18H_of_hyp201One h
  rw [hL]
  exact Sec18.perfectResidual_not_le_of_mem_scriptH hH18.toSec18Std hH18.mem_scriptH

theorem le_normalizer_of_hyp201One {A M L N : Subgroup G} {c : G} (h : Hyp201One G A M L N c) :
    A ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨H, hH18, -, hL, -⟩ := exists_sec18H_of_hyp201One h
  rw [hL]
  exact (Sec18.le_of_mem_scriptH₀ (mem_scriptH_iff_mem_scriptH₀.mp hH18.mem_scriptH).1).trans
    (Sec18.le_normalizer_inSubgroup_perfectResidual H)

theorem pCoreOf_le_of_hyp201One {A M L N : Subgroup G} {c : G} (h : Hyp201One G A M L N c) :
    CFSG.Open.pCoreOf 2 L ≤ M :=
  Sec18.le_of_le_normalizer_of_isPGroup_two (sec18Std_of_hyp201 h.1)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    ((le_normalizer_of_hyp201One h).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))

theorem nonempty_quotient_of_hyp201One (h184 : Sec18.Item184_1) {A M L N : Subgroup G} {c : G}
    (h : Hyp201One G A M L N c) :
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* projSL 3 (GaloisField 2 2)) := by
  obtain ⟨H, hH18, -, hL, -⟩ := exists_sec18H_of_hyp201One h
  subst hL
  exact (h184 G A M hH18.toSec18Std H hH18.mem_scriptH).1

omit [Finite G] in
theorem card_eq_card_map_mul_inf_ker {Y X : Type*} [Group Y] [Group X] (f : Y →* X)
    (K : Subgroup Y) : Nat.card K = Nat.card (K.map f) * Nat.card ↥(K ⊓ f.ker) := by
  have h := Subgroup.relIndex_mul_card f.ker K
  rw [Subgroup.relIndex_ker, inf_comm] at h
  exact h.symm

theorem card_inf_eq_one_of_isPGroup {Y : Type*} [Group Y] [Finite Y] {P Q : Subgroup Y}
    (hP : IsPGroup 3 P) (hQ : IsPGroup 2 Q) : Nat.card ↥(P ⊓ Q) = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (hP.to_le (inf_le_left : P ⊓ Q ≤ P)).exists_card_eq
  obtain ⟨b, hb⟩ := (hQ.to_le (inf_le_right : P ⊓ Q ≤ Q)).exists_card_eq
  have hcop : Nat.Coprime (3 ^ a) (2 ^ b) := Nat.Coprime.pow a b (by norm_num)
  rw [← ha, ← hb] at hcop
  exact (Nat.coprime_self _).mp hcop

omit [Finite G] in
theorem card_eq_of_nonempty_quotient {L : Subgroup G}
    (e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* projSL 3 (GaloisField 2 2)) :
    Nat.card L = 20160 * Nat.card (CFSG.pCore 2 ↥L) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L),
    Nat.card_congr e.toEquiv, KFacts.L34.card_projSL]

theorem factorization_three_of_nonempty_quotient {L : Subgroup G}
    (e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* projSL 3 (GaloisField 2 2)) :
    (Nat.card L).factorization 3 = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
  have h1 : (20160 * 2 ^ k).factorization 3 =
      (20160 : ℕ).factorization 3 + (2 ^ k).factorization 3 := by
    rw [Nat.factorization_mul (by norm_num) (by positivity), Finsupp.add_apply]
  have h2 : (2 ^ k).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun h =>
      absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  have h3 : (20160 : ℕ).factorization 3 = 2 := by
    rw [show (20160 : ℕ) = 3 ^ 2 * 2240 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rw [card_eq_of_nonempty_quotient e, hk, h1, h2, h3]

section Sylow

theorem isSylowOf_three_inf_of_mem_scriptH (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1)
    {A M H : Subgroup G} (hs : Sec18Std G A M) (hH : H ∈ scriptH A M) :
    CFSG.ABGLocalTools.IsSylowOf 3 (A ⊓ inSubgroup perfectResidual H)
      (inSubgroup perfectResidual H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  have hAH : A ≤ H := Sec18.le_of_mem_scriptH₀ hH₀
  have hA := isE27_of_mem_partTwoE hs.mem_partTwoE
  have hLH : inSubgroup perfectResidual H ≤ H := Subgroup.map_subtype_le _
  refine CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer ?_ hLH
    (Sec18.le_normalizer_inSubgroup_perfectResidual H)
  obtain ⟨⟨eL⟩, -⟩ := h184 G A M hs H hH
  obtain ⟨s, ⟨hsS, -, -, hsH, X, hXn, hX, hXt, -⟩, -, -⟩ := h1812 G A M hs H hH
  have := hXn
  set Q := CFSG.pCore 2 H with hQ
  set π : H →* H ⧸ Q := QuotientGroup.mk' Q with hπ
  have hS2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 (H ⊓ M)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have ht2 : IsPGroup 2 (Subgroup.zpowers (π ⟨s, hsH⟩)) := by
    have hT2 : IsPGroup 2 ((CFSG.Open.pCoreOf 2 (H ⊓ M)).subgroupOf H) := hS2.comap_subtype
    refine (hT2.map π).to_le (Subgroup.zpowers_le.mpr ?_)
    exact ⟨⟨s, hsH⟩, Subgroup.mem_subgroupOf.mpr hsS, rfl⟩
  have hq2 : IsPGroup 2 ((H ⧸ Q) ⧸ X) := by
    have h1 := ht2.map (QuotientGroup.mk' X)
    have h2 : (Subgroup.zpowers (π ⟨s, hsH⟩)).map (QuotientGroup.mk' X) = ⊤ := by
      rw [← Subgroup.map_top_of_surjective (QuotientGroup.mk' X)
        (QuotientGroup.mk'_surjective X), ← hXt, Subgroup.map_sup,
        (QuotientGroup.map_mk'_self X), bot_sup_eq]
    rw [h2] at h1
    exact h1.of_equiv Subgroup.topEquiv
  obtain ⟨a, ha⟩ := hq2.exists_card_eq
  obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).exists_card_eq
  have hcardH : Nat.card H = Nat.card X * (2 ^ a * 2 ^ b) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Q,
      Subgroup.card_eq_card_quotient_mul_card_subgroup X, ha, hb]
    ring
  have hcop : ∀ m : ℕ, Nat.Coprime (3 ^ m) (2 ^ a * 2 ^ b) := fun m =>
    Nat.Coprime.mul_right (Nat.Coprime.pow m a (by norm_num)) (Nat.Coprime.pow m b (by norm_num))
  rcases hX with heX | ⟨U, V, hsup, hUV, hU, ⟨eV⟩, h3UV⟩
  ·
    obtain ⟨eX⟩ := heX
    have hXc : Nat.card X = 60480 := by
      rw [Nat.card_congr eX.toEquiv, Nat.card_prod, KFacts.L34.card_projSL,
        Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hAH, hA.isPGroup, fun h3 => ?_⟩
    have hAH' := Subgroup.relIndex_mul_card A H
    rw [inf_eq_left.mpr hAH, hA.2] at hAH'
    obtain ⟨k, hk⟩ := h3
    have h81 : 3 ^ 4 ∣ Nat.card X * (2 ^ a * 2 ^ b) := ⟨k, by rw [← hcardH, ← hAH', hk]; ring⟩
    have h81' := (hcop 4).dvd_of_dvd_mul_right h81
    rw [hXc] at h81'
    norm_num at h81'
  ·
    exfalso
    set Lb : Subgroup (H ⧸ Q) := (perfectResidual H).map π with hLb
    have hqs : Group.IsSolvable ((H ⧸ Q) ⧸ X) := by
      have := hq2.isNilpotent
      infer_instance
    have hcomm := KFacts.KS18.commutator_eq_of_isHeisSL hsup hUV hU ⟨eV⟩ h3UV
    have hXX : ⁅X, X⁆ = V.map X.subtype := by
      rw [← Subgroup.map_subtype_commutator, hcomm]
    have hVp : Group.IsPerfect V := by
      have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
        CFSG.LinearGroups.special_linear_isPerfect (by norm_num) (Or.inl le_rfl)
      exact Group.IsPerfect.ofSurjective (f := eV.symm.toMonoidHom) eV.symm.surjective
    have hVmp : ⁅V.map X.subtype, V.map X.subtype⁆ = V.map X.subtype := by
      rw [← Subgroup.map_commutator, ← Subgroup.map_subtype_commutator,
        Group.IsPerfect.commutator_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hLbV : Lb = V.map X.subtype := by
      rw [hLb, Sec18.map_perfectResidual_eq (QuotientGroup.mk'_surjective Q),
        Sec18.perfectResidual_eq_commutator hqs (by rw [hXX, hVmp]), hXX]
    have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) = 60480 := by
      classical
      have := Fintype.ofFinite (GaloisField 2 2)
      have hq : Fintype.card (GaloisField 2 2) = 4 := by
        rw [← Nat.card_eq_fintype_card, KFacts.L34.card_galoisField_two_two]
      rw [Matrix.card_SL_field 3, hq]
      simp [Fin.prod_univ_three]
    have hLbc : Nat.card Lb = 60480 := by
      rw [hLbV, Subgroup.card_map_of_injective X.subtype_injective, Nat.card_congr eV.toEquiv,
        hSL]
    have hdvd : Nat.card Lb ∣ Nat.card (perfectResidual H) := by
      rw [card_eq_card_map_mul_inf_ker π (perfectResidual H)]
      exact dvd_mul_right _ _
    have hcardL : Nat.card (perfectResidual H) =
        Nat.card (inSubgroup perfectResidual H) := by
      rw [inSubgroup, Subgroup.card_map_of_injective H.subtype_injective]
    rw [hLbc, hcardL, card_eq_of_nonempty_quotient eL] at hdvd
    obtain ⟨c, hc⟩ := (CFSG.pCore_isPGroup (p := 2)
      (G := ↥(inSubgroup perfectResidual H))).exists_card_eq
    rw [hc] at hdvd
    have h27 : 3 ^ 3 ∣ 20160 * 2 ^ c := (show (3 : ℕ) ^ 3 ∣ 60480 by norm_num).trans hdvd
    have hcop' : Nat.Coprime (3 ^ 3) (2 ^ c) := Nat.Coprime.pow 3 c (by norm_num)
    have := hcop'.dvd_of_dvd_mul_right h27
    norm_num at this

theorem isSylowOf_three_inf_of_hyp201One (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1)
    {A M L N : Subgroup G} {c : G} (h : Hyp201One G A M L N c) :
    CFSG.ABGLocalTools.IsSylowOf 3 (A ⊓ L) L := by
  obtain ⟨H, hH18, -, hL, -⟩ := exists_sec18H_of_hyp201One h
  subst hL
  exact isSylowOf_three_inf_of_mem_scriptH h1812 h184 hH18.toSec18Std hH18.mem_scriptH

theorem card_inf_of_hyp201One (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1)
    {A M L N : Subgroup G} {c : G} (h : Hyp201One G A M L N c) :
    Nat.card (A ⊓ L : Subgroup G) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := nonempty_quotient_of_hyp201One h184 h
  rw [(isSylowOf_three_inf_of_hyp201One h1812 h184 h).card_eq,
    factorization_three_of_nonempty_quotient e]
  norm_num

end Sylow

theorem normalizer_inf_le_of_hyp201One {A M L N : Subgroup G} {c : G}
    (h : Hyp201One G A M L N c) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) :
    Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ≤ M := by
  have hA := isE27_of_mem_partTwoE h.1.mem_partTwoE
  have hBE : CFSG.Assembly.IsElemAbelian 3 (A ⊓ L) := Late.isElemAbelian_of_le hA.1 inf_le_left
  exact (normalizer_le_gamma inf_le_left (two_le_pRank_of_elemAbelian hBE h9.ge)).trans
    h.1.mem_scriptM.2

theorem sup_inf_eq_of_hyp201One {A M L N : Subgroup G} {c : G} (h : Hyp201One G A M L N c)
    (hsyl : CFSG.ABGLocalTools.IsSylowOf 3 (A ⊓ L) L)
    (hNB : Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ≤ M) : L ⊔ (N ⊓ M) = N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨H, -, -, -, hN⟩ := exists_sec18H_of_hyp201One h
  have hLN : L ≤ N := hN ▸ Subgroup.le_normalizer
  refine le_antisymm (sup_le hLN inf_le_left) ?_
  intro n hn
  obtain ⟨l, hl, m, hm, rfl⟩ := Sec18.exists_mul_of_isSylowOf hsyl (K := N)
    (le_of_eq hN) hn
  have hmN : m ∈ N := by
    have : m = l⁻¹ * (l * m) := by group
    rw [this]
    exact N.mul_mem (N.inv_mem (hLN hl)) hn
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right ⟨hmN, hNB hm⟩)

omit [Finite G] in
theorem mem_normalizer_of_mem_normalizer_subgroupOf {L B : Subgroup G} (hBL : B ≤ L) {m : L}
    (hm : m ∈ Subgroup.normalizer ((B.subgroupOf L : Subgroup L) : Set L)) :
    (m : G) ∈ Subgroup.normalizer (B : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hm ⊢
  intro g
  by_cases hg : g ∈ L
  · have h := hm ⟨g, hg⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h
    exact h
  · constructor
    · intro hgB
      exact absurd (hBL hgB) hg
    · intro hgB
      exfalso
      apply hg
      have h' := hBL hgB
      have heq : g = (m : G)⁻¹ * ((m : G) * g * (m : G)⁻¹) * m := by group
      rw [heq]
      exact L.mul_mem (L.mul_mem (L.inv_mem m.2) h') m.2

theorem exists_mul_of_mk_mem_normalizer {L B : Subgroup G} (hBL : B ≤ L) (hB : IsPGroup 3 B)
    {x : L} (hx : QuotientGroup.mk' (CFSG.pCore 2 ↥L) x ∈ Subgroup.normalizer
      (((B.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) : Subgroup _) : Set _)) :
    ∃ y ∈ B.subgroupOf L ⊔ CFSG.pCore 2 ↥L, ∃ m : L,
      (m : G) ∈ Subgroup.normalizer (B : Set G) ∧ x = y * m := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pCore 2 ↥L with hO
  set B' := B.subgroupOf L with hB'
  have hxN : x ∈ Subgroup.normalizer ((B' ⊔ O : Subgroup L) : Set L) := by
    have h1 : (B'.map (QuotientGroup.mk' O)).comap (QuotientGroup.mk' O) = B' ⊔ O := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    rw [← h1, ← Subgroup.comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective O)]
    exact hx
  have hB'3 : IsPGroup 3 B' := hB.comap_subtype
  have hO3 : ¬ 3 ∣ Nat.card O := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hB'O : B' ≤ Subgroup.normalizer (O : Set L) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  have hsyl := isSylowOf_sup_of_coprime hB'3 hO3 hB'O
  obtain ⟨y, hy, m, hm, hxym⟩ := Sec18.exists_mul_of_isSylowOf hsyl le_rfl hxN
  exact ⟨y, hy, m, mem_normalizer_of_mem_normalizer_subgroupOf hBL hm, hxym⟩

section Index

theorem card_map_inf_of_hyp201One (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1)
    {A M L N : Subgroup G} {c : G} (h : Hyp201One G A M L N c) :
    Nat.card (((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB3 : IsPGroup 3 ((A ⊓ L).subgroupOf L) :=
    (isSylowOf_three_inf_of_hyp201One h1812 h184 h).isPGroup.comap_subtype
  have h1 := card_eq_card_map_mul_inf_ker (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
    ((A ⊓ L).subgroupOf L)
  rw [QuotientGroup.ker_mk', card_inf_eq_one_of_isPGroup hB3 CFSG.pCore_isPGroup, mul_one,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ L ≤ L)).toEquiv,
    card_inf_of_hyp201One h1812 h184 h] at h1
  exact h1.symm

theorem normalizer_map_le_of_hyp201One (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1)
    {A M L N : Subgroup G} {c : G} (h : Hyp201One G A M L N c) :
    Subgroup.normalizer ((((A ⊓ L).subgroupOf L).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) : Subgroup _) : Set _) ≤
      ((L ⊓ M).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNB := normalizer_inf_le_of_hyp201One h (card_inf_of_hyp201One h1812 h184 h)
  have hO2 := pCoreOf_le_of_hyp201One h
  have hAM : A ≤ M := le_of_hyp201 h.1
  have hB3 : IsPGroup 3 (A ⊓ L : Subgroup G) :=
    (isSylowOf_three_inf_of_hyp201One h1812 h184 h).isPGroup
  intro z hz
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
  obtain ⟨y, hy, m, hm, rfl⟩ := exists_mul_of_mk_mem_normalizer inf_le_right hB3 hz
  have hle : (A ⊓ L).subgroupOf L ⊔ CFSG.pCore 2 ↥L ≤ (L ⊓ M).subgroupOf L := by
    refine sup_le ?_ ?_
    · intro b hb
      rw [Subgroup.mem_subgroupOf] at hb ⊢
      exact ⟨b.2, hAM hb.1⟩
    · intro b hb
      rw [Subgroup.mem_subgroupOf]
      exact ⟨b.2, hO2 ((Sec18.mem_pCore_iff_mem_pCoreOf b).mp hb)⟩
  refine ⟨y * m, ((L ⊓ M).subgroupOf L).mul_mem (hle hy) ?_, rfl⟩
  rw [Subgroup.mem_subgroupOf]
  exact ⟨m.2, hNB hm⟩

theorem relIndex_inf_eq_of_hyp201One (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1)
    {A M L N : Subgroup G} {c : G} (h : Hyp201One G A M L N c) : (L ⊓ M).relIndex L = 280 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := nonempty_quotient_of_hyp201One h184 h
  have hO2 := pCoreOf_le_of_hyp201One h
  set φ := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hφ
  set Y' := (L ⊓ M).subgroupOf L with hY'
  have hker : φ.ker ≤ Y' := by
    rw [hφ, QuotientGroup.ker_mk']
    intro x hx
    rw [hY', Subgroup.mem_subgroupOf]
    exact ⟨x.2, hO2 ((Sec18.mem_pCore_iff_mem_pCoreOf x).mp hx)⟩
  have hYtop : Y'.map φ ≠ ⊤ := by
    intro htop
    apply not_le_of_hyp201One h
    intro x hxL
    have hcomap : (Y'.map φ).comap φ = Y' := by
      rw [Subgroup.comap_map_eq, sup_eq_left.mpr hker]
    have hmem : (⟨x, hxL⟩ : L) ∈ (Y'.map φ).comap φ := by
      rw [Subgroup.mem_comap, htop]
      exact Subgroup.mem_top _
    rw [hcomap, hY', Subgroup.mem_subgroupOf] at hmem
    exact hmem.2
  have hidx := KFacts.L34Max.index_eq_of_normalizer_le e (card_map_inf_of_hyp201One h1812 h184 h)
    (normalizer_map_le_of_hyp201One h1812 h184 h) hYtop
  rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) hker] at hidx
  exact hidx

theorem card_eq_of_hyp201One (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1)
    {A M L N : Subgroup G} {c : G} (h : Hyp201One G A M L N c) :
    Nat.card N = 280 * Nat.card (N ⊓ M : Subgroup G) := by
  obtain ⟨H, -, -, -, hN⟩ := exists_sec18H_of_hyp201One h
  have hLN : L ≤ N := hN ▸ Subgroup.le_normalizer
  have hsyl := isSylowOf_three_inf_of_hyp201One h1812 h184 h
  have hNB := normalizer_inf_le_of_hyp201One h (card_inf_of_hyp201One h1812 h184 h)
  have hsup := sup_inf_eq_of_hyp201One h hsyl hNB
  have h1 := relIndex_sup_eq_of_le_normalizer (H := N ⊓ M) (N := L)
    (inf_le_left.trans (le_of_eq hN))
  rw [sup_comm, hsup] at h1
  have h2 := Subgroup.relIndex_mul_card L N
  rw [inf_eq_left.mpr hLN] at h2
  have h3 := Subgroup.relIndex_mul_card L (N ⊓ M)
  rw [show L ⊓ (N ⊓ M) = L ⊓ M by rw [← inf_assoc, inf_eq_left.mpr hLN]] at h3
  have h4 := Subgroup.relIndex_mul_card (L ⊓ M) L
  rw [show L ⊓ M ⊓ L = L ⊓ M by rw [inf_comm, ← inf_assoc, inf_idem],
    relIndex_inf_eq_of_hyp201One h1812 h184 h] at h4
  rw [← h2, ← h4, ← h3, ← h1]
  ring

end Index

end CFSG.RankThree.PartTwo.Sec20
