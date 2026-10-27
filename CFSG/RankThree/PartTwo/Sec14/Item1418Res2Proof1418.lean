module

public import CFSG.RankThree.PartTwo.Sec14.Item1418Res2ProofDefs
public import CFSG.RankThree.PartTwo.Sec14.Item1418Res2ProofTools
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res5ProofOdd
import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofTools
import CFSG.RankThree.PartTwo.Sec12.Item128Bar
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.PartTwo.Sec17.Item17ParaS
import CFSG.RankThree.PartOne.KE8F.HyperGen
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

namespace Proof1418Res2

variable {G : Type} [Group G] [Finite G]

theorem eq_sup_zpowers_of_not_mem {A B : Subgroup G} (hA : IsE27 A) (hB : IsHyperplane A B)
    {a : G} (haA : a ∈ A) (haB : a ∉ B) : A = B ⊔ Subgroup.zpowers a := by
  set S := B ⊔ Subgroup.zpowers a with hSdef
  have hSA : S ≤ A := sup_le hB.1 (Subgroup.zpowers_le.mpr haA)
  have hB9 : Nat.card B = 9 := by
    have h := hB.2
    rw [hA.2] at h
    omega
  have h2 : Nat.card S ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA.2]
    exact Subgroup.card_dvd_of_le hSA
  have h1 : 9 ∣ Nat.card S := hB9 ▸ Subgroup.card_dvd_of_le le_sup_left
  have h3 : Nat.card S ≠ 9 := by
    intro h
    have hBS : B = S := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h, hB9])
    exact haB (hBS ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
  obtain ⟨k, hk, hSk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
  have h27 : Nat.card S = 27 := by
    interval_cases k <;> simp_all
  exact (Subgroup.eq_of_le_of_card_ge hSA (by rw [h27, hA.2])).symm

theorem inf_centralizer_le_of_not_mem {A B : Subgroup G} (hA : IsE27 A) (hB : IsHyperplane A B)
    {a : G} (haA : a ∈ A) (haB : a ∉ B) :
    Subgroup.centralizer (B : Set G) ⊓ Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.centralizer (A : Set G) := by
  intro x hx
  obtain ⟨hxB, hxa⟩ := Subgroup.mem_inf.mp hx
  have hle : B ⊔ Subgroup.zpowers a ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (fun y hy => ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hxB y hy
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hxa).symm
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' := hle ((eq_sup_zpowers_of_not_mem hA hB haA haB) ▸ hy)
  rw [Subgroup.mem_centralizer_singleton_iff] at hy'
  exact hy'

omit [Finite G] in
theorem map_conj_le_centralizer {T : Subgroup G} {b : G}
    (hT : T ≤ Subgroup.centralizer ({b} : Set G)) (w : G) :
    T.map (MulAut.conj w).toMonoidHom ≤ Subgroup.centralizer ({w * b * w⁻¹} : Set G) := by
  rintro _ ⟨t, ht, rfl⟩
  have h := Subgroup.mem_centralizer_singleton_iff.mp (hT ht)
  rw [Subgroup.mem_centralizer_singleton_iff]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc w * t * w⁻¹ * (w * b * w⁻¹) = w * (t * b) * w⁻¹ := by group
    _ = w * (b * t) * w⁻¹ := by rw [h]
    _ = w * b * w⁻¹ * (w * t * w⁻¹) := by group

theorem map_conj_mem_scriptQPiStar_top {A S : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G)) (hS : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) :
    S.map (MulAut.conj w).toMonoidHom ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) :=
  maximal_map_conj (W := Subgroup.normalizer (A : Set G))
    (fun _ hQ _ hx => map_conj_mem_scriptQPi_top (isNaturalFamily_lB A) hx hQ) hS hw

theorem not_two_dvd_xA (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (h1413 : Item1413CR)
    {A L : Subgroup G} {c : G} (hR : Sec15R G A c L) (hfail : Fail1411 A (lB A)) {b : G}
    (hbΓ : Subgroup.zpowers b ∈ gammaA A (lB A)) : ¬ 2 ∣ Nat.card ↥(xA A) := by
  have hD := hR.toSec14Std.toSec13Data
  have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp hbΓ.1).1
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx hbA)
  obtain ⟨Lb, hLb⟩ := Sec12.exists_mem_lA422 h422 h45 hD.toPartTwoStanding hD.mem_partTwoF
    hD.card_eq hbΓ.1
  exact (h1413 G A c L hR hfail b hbΓ Lb (Sec12.mem_lA_of_mem_lA422 hAb hLb)).2

theorem inf_centralizer_eq_bot {A S : Subgroup G} (hA : IsE27 A)
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (hX : ¬ 2 ∣ Nat.card ↥(xA A))
    (hS : S ∈ scriptQ A (lB A)) (hS2 : IsPGroup 2 S) :
    S ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
  have hAC : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.1.1
  have hmem : S ⊓ Subgroup.centralizer (A : Set G) ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le hS inf_le_left
      (Late.le_normalizer_inf hS.1.2.2 (hAC.trans Subgroup.le_normalizer))
  exact Proof1413Res3.eq_bot_of_isPGroup_two_of_le (hS2.to_le inf_le_left)
    (le_pPrimeCoreOf_centralizer hbot hmem inf_le_right) hX

theorem zpowers_conj_eq {A B S : Subgroup G} (hA : IsE27 A) (hB : IsHyperplane A B)
    (hSA : S ⊓ Subgroup.centralizer (A : Set G) = ⊥)
    (hSB : S ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥) {b : G} (hbA : b ∈ A)
    (hbΓ : Subgroup.zpowers b ∈ gammaA A (lB A))
    (huniq : ∀ F ∈ gammaA A (lB A), F ≤ B → F = Subgroup.zpowers b) {w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G))
    (hSw : S ≤ Subgroup.centralizer ({w * b * w⁻¹} : Set G)) :
    Subgroup.zpowers (w * b * w⁻¹) = Subgroup.zpowers b := by
  have hb'A : w * b * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hw b).mp hbA
  have hb'B : w * b * w⁻¹ ∈ B := by
    by_contra hb'B
    apply hSB
    rw [eq_bot_iff, ← hSA]
    refine le_inf inf_le_left ?_
    exact (le_inf inf_le_right (inf_le_left.trans hSw)).trans
      (inf_centralizer_le_of_not_mem hA hB hb'A hb'B)
  have hΓ : Subgroup.zpowers (w * b * w⁻¹) ∈ gammaA A (lB A) := by
    have h := Proof1413Res2.map_conj_mem_gammaA hw hbΓ
    rwa [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  exact huniq _ hΓ (Subgroup.zpowers_le.mpr hb'B)

omit [Finite G] in
theorem le_centralizer_of_isConjIn_xA {A S T : Subgroup G} {b : G} (hbA : b ∈ A)
    (hS : S ≤ Subgroup.centralizer ({b} : Set G)) (h : IsConjIn (xA A) S T) :
    T ≤ Subgroup.centralizer ({b} : Set G) := by
  obtain ⟨x, hx, rfl⟩ := h
  have hxA : x ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hx
  have hxb : x * b * x⁻¹ = b := by
    rw [(Subgroup.mem_centralizer_iff.mp hxA b hbA).symm, mul_inv_cancel_right]
  have h := map_conj_le_centralizer hS x
  rwa [hxb] at h

theorem forall_le_centralizer_of_uniq {A B S : Subgroup G} (hT1411 : Item1411_1 A (lB A))
    (hA : IsE27 A) (hB : IsHyperplane A B)
    (hX : ¬ TransOn A (lB A) (xA A) ⊤) (hS : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2))
    (hSA : S ⊓ Subgroup.centralizer (A : Set G) = ⊥)
    (hSB : S ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥) {b : G} (hbA : b ∈ A)
    (hbΓ : Subgroup.zpowers b ∈ gammaA A (lB A))
    (huniq : ∀ F ∈ gammaA A (lB A), F ≤ B → F = Subgroup.zpowers b)
    (hall : ∀ T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), ¬ IsConjIn (xA A) S T →
      T ≤ Subgroup.centralizer ({b} : Set G)) :
    ∀ T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), T ≤ Subgroup.centralizer ({b} : Set G) := by
  obtain ⟨T₀, hT₀, hST₀⟩ := Proof1413Res2.exists_not_isConjIn hX S
  obtain ⟨w, hw, hwS⟩ := hT1411 T₀ hT₀ S hS
  have hwW : w ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp hw).1
  have hSw : S ≤ Subgroup.centralizer ({w * b * w⁻¹} : Set G) := by
    rw [hwS]
    exact map_conj_le_centralizer (hall T₀ hT₀ hST₀) w
  have hSb : S ≤ Subgroup.centralizer ({b} : Set G) := by
    rw [← centralizer_singleton_eq_of_zpowers_eq
      (zpowers_conj_eq hA hB hSA hSB hbA hbΓ huniq hwW hSw)]
    exact hSw
  intro T hT
  by_cases hST : IsConjIn (xA A) S T
  · exact le_centralizer_of_isConjIn_xA hbA hSb hST
  · exact hall T hT hST

theorem normalizer_le_of_forall_le {A B S : Subgroup G} (hA : IsE27 A) (hB : IsHyperplane A B)
    (hS : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2))
    (hSA : S ⊓ Subgroup.centralizer (A : Set G) = ⊥)
    (hSB : S ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥) {b : G} (hbA : b ∈ A)
    (hbΓ : Subgroup.zpowers b ∈ gammaA A (lB A))
    (huniq : ∀ F ∈ gammaA A (lB A), F ≤ B → F = Subgroup.zpowers b)
    (hall : ∀ T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), T ≤ Subgroup.centralizer ({b} : Set G)) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
  intro w hw
  have hSw : S ≤ Subgroup.centralizer ({w * b * w⁻¹} : Set G) := by
    have h := map_conj_le_centralizer (hall _ (map_conj_mem_scriptQPiStar_top (inv_mem hw) hS)) w
    rwa [map_conj_map_conj, mul_inv_cancel, map_conj_one] at h
  have heq := zpowers_conj_eq hA hB hSA hSB hbA hbΓ huniq hw hSw
  refine mem_normalizer_of_map_conj_self ?_
  rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact heq

omit [Finite G] in
theorem exists_not_le_centralizer (hchar : CFSG.Assembly.IsCharTwoType G) {A U : Subgroup G}
    (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hAU : A ≤ Subgroup.normalizer (U : Set G)) {b : G}
    (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1) :
    ∃ V : Subgroup G, IsPGroup 2 V ∧ A ≤ Subgroup.normalizer (V : Set G) ∧
      ¬ V ≤ Subgroup.centralizer ({b} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hUb : U ≤ Subgroup.centralizer ({b} : Set G)
  · have hAC : A ≤ Subgroup.normalizer (Subgroup.centralizer (U : Set G) : Set G) := by
      intro a ha
      refine mem_normalizer_of_map_conj_self ?_
      rw [map_conj_centralizer, Late.map_conj_eq_of_mem_normalizer (hAU ha)]
    refine ⟨inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)),
      CFSG.pCore_isPGroup.map _, hAC.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (CFSG.pCore 2 (Subgroup.centralizer (U : Set G)))), fun hQb => ?_⟩
    have hbU : Subgroup.zpowers b ≤ Subgroup.centralizer (U : Set G) := by
      refine Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun u hu => ?_)
      exact Subgroup.mem_centralizer_singleton_iff.mp (hUb hu)
    have hB3 : ∀ x ∈ Subgroup.zpowers b, x ^ 3 = 1 := by
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
    have h0 := Sec6.inf_centralizer_inSubgroup_pCore_eq_bot hchar hU2 hU1 hB3 hbU
    have hbQ : b ∈ Subgroup.centralizer
        (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
      exact Subgroup.mem_centralizer_singleton_iff.mp (hQb hq)
    have hb : b ∈ Subgroup.zpowers b ⊓ Subgroup.centralizer
        (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) : Set G) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_zpowers b, hbQ⟩
    rw [h0, Subgroup.mem_bot] at hb
    exact hb1 hb
  · exact ⟨U, hU2, hAU, hUb⟩

theorem le_of_forall_hyperplane {A V U : Subgroup G} (hA : IsE27 A)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hV3 : ¬ 3 ∣ Nat.card V)
    (hU : ∀ E, IsHyperplane A E → V ⊓ Subgroup.centralizer (E : Set G) ≤ U) : V ≤ U := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CFSG.IsElementaryAbelian 3 ↥A := Proof1413Res2.isElementaryAbelian_of_isElemAbelian hA.1
  have : Nontrivial ↥A := by
    rw [← Finite.one_lt_card_iff_nontrivial, hA.2]
    norm_num
  refine (PartOne.KE8F.le_iSup_hyperplane_centralizers hAV hV3).trans (iSup₂_le fun E hE => ?_)
  refine hU _ ⟨Subgroup.map_subtype_le E, ?_⟩
  rw [Subgroup.card_map_of_injective A.subtype_injective, ← hE, Subgroup.index_mul_card]

theorem mem_scriptQ_of_le_pPrimeCoreOf {A E Q : Subgroup G} (hA : IsE27 A)
    (hE : IsHyperplane A E) (hQ : Q ≤ pPrimeCoreOf 3 (Subgroup.centralizer (E : Set G)))
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) : Q ∈ scriptQ A (lB A) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO3 : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 (Subgroup.centralizer (E : Set G))) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hQ3 : ¬ 3 ∣ Nat.card Q := fun h => hO3 (h.trans (Subgroup.card_dvd_of_le hQ))
  have hE9 : Nat.card E = 9 := by
    have h := hE.2
    rw [hA.2] at h
    omega
  refine ⟨⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three Q).mpr hQ3, hAQ⟩, fun D hD => ?_⟩
  by_cases hDE : D = E
  · subst hDE
    exact (inf_le_left.trans hQ).trans (le_sup_left.trans le_sup_left)
  · have hD9 : Nat.card D = 9 := by
      have h := hD.2
      rw [hA.2] at h
      omega
    obtain ⟨a, haD, haE⟩ : ∃ a ∈ D, a ∉ E := by
      by_contra hno
      push Not at hno
      exact hDE (Subgroup.eq_of_le_of_card_ge (fun x hx => hno x hx) (by rw [hE9, hD9]))
    have hAE : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (E : Set G) :=
      Subgroup.centralizer_le hE.1
    have hle : Q ⊓ Subgroup.centralizer (D : Set G) ≤
        pPrimeCoreOf 3 (Subgroup.centralizer (E : Set G)) ⊓
          Subgroup.centralizer (A : Set G) := by
      refine le_inf (inf_le_left.trans hQ) ?_
      exact (le_inf ((inf_le_left.trans hQ).trans (pPrimeCoreOf_le 3 _))
        (inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haD)))).trans
        (inf_centralizer_le_of_not_mem hA hE (hD.1 haD) haE)
    refine hle.trans ((le_pPrimeCoreOf inf_le_right ?_ ?_).trans (le_sup_right.trans le_sup_left))
    · exact Late.le_normalizer_inf (hAE.trans (le_normalizer_pPrimeCoreOf 3 _))
        Subgroup.le_normalizer
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
        fun h => hO3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))

omit [Finite G] in
theorem isPGroup_zpowers_of_pow_three {b : G} (hb3 : b ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers b) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
  simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
  rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]

theorem le_centralizer_of_le_pPrimeCoreOf {A E : Subgroup G} (hA : IsE27 A)
    (hE : IsHyperplane A E) {b : G} (hbA : b ∈ A) (hb3 : b ^ 3 = 1)
    (hall : ∀ T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), T ≤ Subgroup.centralizer ({b} : Set G))
    (hfin : ∀ R : Subgroup G, R ≤ Subgroup.centralizer (E : Set G) → IsPGroup 2 R →
      A ≤ Subgroup.normalizer (R : Set G) → ⁅R, Subgroup.zpowers b⁆ = R →
        R ≤ pPrimeCoreOf 3 (Subgroup.centralizer (E : Set G)))
    {V : Subgroup G} (hVE : V ≤ Subgroup.centralizer (E : Set G)) (hV2 : IsPGroup 2 V)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) : V ≤ Subgroup.centralizer ({b} : Set G) := by
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set Z := Subgroup.zpowers b with hZdef
  have hZ3 : IsPGroup 3 Z := isPGroup_zpowers_of_pow_three hb3
  have hZV : Z ≤ Subgroup.normalizer (V : Set G) := Subgroup.zpowers_le.mpr (hAV hbA)
  have hV3 : ¬ 3 ∣ Nat.card V := Proof1413Res3.not_three_dvd_of_isPGroup_two hV2
  set R := ⁅V, Z⁆ with hRdef
  have hRV : R ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hZV
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) := fun a ha =>
    Sec13.centralizer_le_normalizer_zpowers b
      (Subgroup.mem_centralizer_singleton_iff.mpr (hAc a ha b hbA))
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := by
    intro a ha
    refine mem_normalizer_of_map_conj_self ?_
    rw [hRdef, Subgroup.map_commutator, Late.map_conj_eq_of_mem_normalizer (hAV ha),
      Late.map_conj_eq_of_mem_normalizer (hAZ ha)]
  have hRR : ⁅R, Z⁆ = R :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three Z V
      hZ3 hV3 hZV
  have hRO := hfin R (hRV.trans hVE) (hV2.to_le hRV) hAR hRR
  have hRQ := mem_scriptQ_of_le_pPrimeCoreOf hA hE hRO hAR
  have hpi : R ∈ scriptQPi A (lB A) ⊤ (piOf 2) :=
    ⟨⟨hRQ, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr (hV2.to_le hRV)⟩
  obtain ⟨T, hRT, hT⟩ := Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) ⊤ (piOf 2))) hpi
  have hRb : R ≤ Subgroup.centralizer (Z : Set G) := by
    rw [hZdef, ← Sec13.centralizer_singleton_eq_zpowers]
    exact hRT.trans (hall T hT)
  have hR0 : R = ⊥ := by
    rw [← hRR]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hRb
  rw [Sec13.centralizer_singleton_eq_zpowers]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hR0

theorem normalizer_le_normalizer_inf {A L : Subgroup G} {c : G} (hR : Sec15R G A c L) {b : G}
    (hbΩ : Subgroup.zpowers b ∈ omegaA A)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G))
    {Lb : Subgroup G} (hLb : Lb ∈ lA A b) (h3 : 3 ∣ Nat.card Lb) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ Lb : Subgroup G) : Set G) := by
  have hRb : Sec15R G A b Lb :=
    { Proof1413.sec14Std_at hR.toSec14Std hbΩ hLb with hypR := hR.hypR }
  exact Late.le_normalizer_inf le_rfl
    (hW.trans (Sec17.Sec15R.normalizer_zpowers_le_normalizer_L hRb h3))

end Proof1418Res2

open Proof1418Res2

theorem step1418UniqR_of_uniqAll (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (h1411 : Item1411_1FR) (h1413 : Item1413CR) (hbot : Item145BotS14)
    (hAll : Step1418UniqAllR) : Step1418UniqR := by
  intro G _ _ A c L hR hfail S hS B hB hSB b hbB hbΓ huniq hT
  have hA : IsE27 A := hR.toSec14Std.isE27
  have hX := not_two_dvd_xA h422 h45 h1413 hR hfail hbΓ
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS.prop.2
  have hSA := inf_centralizer_eq_bot hA (hbot G A c L hR.toSec14Std) hX hS.prop.1.1 hS2
  exact hAll G A c L hR hfail S hS B hB hSB b hbB hbΓ huniq
    (forall_le_centralizer_of_uniq (h1411 G A c L hR hfail) hA hB hfail.1 hS hSA hSB (hB.1 hbB) hbΓ
      huniq hT)

theorem step1418UniqAllR_of_off (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (h1413 : Item1413CR) (h142 : Concl142S14) (hbot : Item145BotS14) (hOff : Step1418OffR) :
    Step1418UniqAllR := by
  intro G _ _ A c L hR hfail S hS B hB hSB b hbB hbΓ huniq hall
  have hA : IsE27 A := hR.toSec14Std.isE27
  have hD := hR.toSec14Std.toSec13Data
  have hbA : b ∈ A := hB.1 hbB
  have hX := not_two_dvd_xA h422 h45 h1413 hR hfail hbΓ
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS.prop.2
  have hSA := inf_centralizer_eq_bot hA (hbot G A c L hR.toSec14Std) hX hS.prop.1.1 hS2
  have hW := normalizer_le_of_forall_le hA hB hS hSA hSB hbA hbΓ huniq hall
  obtain ⟨-, hb3c, -⟩ := zpowers_mem_omegaA_iff.mp hbΓ.1
  have hbo : orderOf b = 3 := by rw [← Nat.card_zpowers]; exact hb3c
  have hb1 : b ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hbo
    omega
  have hb3 : b ^ 3 = 1 := by rw [← hbo]; exact pow_orderOf_eq_one b
  obtain ⟨U, hU1, hU2, hAU⟩ := hD.mem_partTwoE.2.2
  obtain ⟨V, hV2, hAV, hVb⟩ :=
    exists_not_le_centralizer hR.charTwoType hU1 hU2 hAU hb1 hb3
  apply hVb
  refine le_of_forall_hyperplane hA hAV (Proof1413Res3.not_three_dvd_of_isPGroup_two hV2)
    fun E hE => ?_
  have hAE : A ≤ Subgroup.centralizer (E : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hD.commute (hE.1 hy) hx
  have hAVE : A ≤ Subgroup.normalizer
      ((V ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hAV (hAE.trans Subgroup.le_normalizer)
  have hVE2 : IsPGroup 2 (V ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) :=
    hV2.to_le inf_le_left
  by_cases hEΩ : ∃ F ∈ omegaA A, F ≤ E
  ·
    obtain ⟨F, hF, hFE⟩ := hEΩ
    obtain ⟨y, rfl, -⟩ := hF.2.2
    have hyE : y ∈ E := hFE (Subgroup.mem_zpowers y)
    have hN : V ⊓ Subgroup.centralizer (E : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers y : Set G) :=
      inf_le_right.trans ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hyE)).trans
        (Sec13.centralizer_le_normalizer_zpowers y))
    have hmem := Proof1413Res3.mem_scriptQ_of_le_normalizer h142 hR.toSec14Std hF hN hAVE
      (Proof1413Res3.not_three_dvd_of_isPGroup_two hVE2)
    have hpi : V ⊓ Subgroup.centralizer (E : Set G) ∈ scriptQPi A (lB A) ⊤ (piOf 2) :=
      ⟨⟨hmem, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hVE2⟩
    obtain ⟨T, hVT, hT⟩ := Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) ⊤ (piOf 2))) hpi
    exact hVT.trans (hall T hT)
  · push Not at hEΩ
    exact le_centralizer_of_le_pPrimeCoreOf hA hE hbA hb3 hall
      (hOff G A c L hR hfail S hS B hB hSB b hbB hbΓ huniq hall hW
        (fun Lb hLb h3 => normalizer_le_normalizer_inf hR hbΓ.1 hW hLb h3) E hE hEΩ)
      inf_le_right hVE2 hAVE

theorem step1418UniqR_of_off (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (h1411 : Item1411_1FR) (h1413 : Item1413CR) (h142 : Concl142S14) (hbot : Item145BotS14)
    (hOff : Step1418OffR) : Step1418UniqR :=
  step1418UniqR_of_uniqAll h422 h45 h1411 h1413 hbot
    (step1418UniqAllR_of_off h422 h45 h1413 h142 hbot hOff)

end CFSG.RankThree.PartTwo.Sec14
