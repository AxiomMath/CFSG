module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1Aut
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1Cent
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1Sec
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1LB
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1ON
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1ONCase
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJNotLeDefs
public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
public import CFSG.RankThree.PartTwo.Sec13.Item134Sylow
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item148Res9ONProofSub
public import CFSG.RankThree.PartTwo.Sec10.Item1015Proof
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofCases
public import CFSG.Permutation.UnitaryThreeRecognition.ModelFinite

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3 (NoSimpleSec)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.NoSimpleSec
  (of_not_dvd of_subsingleton)

variable {G : Type} [Group G] [Finite G]


section Step1


theorem exists_centralizing_ne {A L K : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hK : K ∈ scriptY A) {S : Type} [Group S] [IsSimpleGroup S]
    (hnab : ∃ x y : S, x * y ≠ y * x) (φ : ↥K ⧸ CFSG.pPrimeCore 3 ↥K ≃* S)
    (hS : ∀ B : Subgroup (MulAut S), CFSG.Assembly.IsElemAbelian 3 B → Nat.card B ≤ 9)
    (hSJ : ∀ (H' : Subgroup CFSG.Blueprint.NativeSporadic.J2) (f' : ↥H' →* S),
      ¬ Function.Surjective f') :
    ∃ a ∈ A, a ≠ 1 ∧ Subgroup.zpowers a ≠ Subgroup.zpowers c ∧
      ∀ x ∈ K, a * x * a⁻¹ * x⁻¹ ∈ pPrimeCoreOf 3 K := by
  by_cases hc : ∀ x ∈ K, c * x * c⁻¹ * x⁻¹ ∈ pPrimeCoreOf 3 K
  · obtain ⟨hcL, h9, -⟩ := j2_point_facts hR.toSec13Data hJ
    rcases Subgroup.bot_or_exists_ne_one (A ⊓ L) with hbot | ⟨d, hd, hd1⟩
    · rw [hbot, Subgroup.card_bot] at h9
      omega
    refine ⟨d, hd.1, hd1, fun heq => hcL ?_,
      centralizes_of_mem_inf hR hJ hK hnab φ hSJ hc hd.1 hd.2⟩
    have hcd : c ∈ Subgroup.zpowers d := by
      rw [heq]
      exact Subgroup.mem_zpowers c
    exact Subgroup.zpowers_le.mpr hd.2 hcd
  · obtain ⟨A₀, hA₀A, hA₀, hA₀c⟩ := exists_centralizing_subgroup
      (Late.isE27_of_mem_partTwoE hR.mem_partTwoE) hK.2 hS φ
    rcases Subgroup.bot_or_exists_ne_one A₀ with hbot | ⟨a, ha, ha1⟩
    · exact (hA₀ hbot).elim
    refine ⟨a, hA₀A ha, ha1, fun heq => hc (hA₀c c ?_), hA₀c a ha⟩
    have hca : c ∈ Subgroup.zpowers a := by
      rw [heq]
      exact Subgroup.mem_zpowers c
    exact Subgroup.zpowers_le.mpr ha hca

end Step1

section D2


theorem false_of_on_join (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h134 : Item134)
    {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hΩ : omegaA A = {Subgroup.zpowers c}) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdc : IsThreeCentralIn L d) {𝒳 : Set (Subgroup G)} (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d)
    (hON : Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
      CFSG.Blueprint.NativeSporadic.ON) : False := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hR.mem_partTwoE
  have hAX : A ≤ sSup 𝒳 := le_sSup_of_on h45 hR hdA hd1 h𝒳 hON
  obtain ⟨Kd, hKd, hJKd, hKd6⟩ := exists_kd h48 h134 h415 hR hJ hΩ hdA hd1 hdc
  obtain ⟨-, h9, -⟩ := j2_point_facts hR.toSec13Data hJ
  obtain ⟨hdL, S, hdS, hSd⟩ := hdc
  have hBK : A ⊓ L ≤ Kd := by
    intro x hx
    have hxd : x ∈ Subgroup.centralizer ({d} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx.1⟩ ⟨d, hdA⟩))
    exact hJKd (Sec13.mem_residual_of_pow_three h415 hJ hdL hd1 ⟨S, hdS, hSd⟩ hx.2 hxd
      (k := 1) (by rw [pow_one]; exact hA.1.2 x hx.1))
  have hB3 : IsPGroup 3 ↥(A ⊓ L) := (Sec4.isPGroup_of_isElemAbelian hA.1).to_le inf_le_left
  by_cases hmem : Kd ∈ 𝒳
  · exact false_of_mem h𝒳 hmem hKd6 hON
  · exact false_of_not_mem h𝒳 hKd hmem hON.1 hBK (inf_le_left.trans hAX) hB3 h9

theorem noSimpleSec21_delta {A L : Subgroup G} {c : G} (h143 : Ronan148Q.Item143Q A (lB A))
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h134 : Item134) (hR : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hΩ : omegaA A = {Subgroup.zpowers c}) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hac : Subgroup.zpowers a ≠ Subgroup.zpowers c) :
    NoSimpleSec 21 ↥(delta A (lB A) (Subgroup.centralizer ({a} : Set G))) := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hΩa : Subgroup.zpowers a ∉ omegaA A := by
    rw [hΩ, Set.mem_singleton_iff]
    exact hac
  obtain ⟨Q, hQ⟩ := maxInvariantPiSubgroups_nonempty
    (delta A (lB A) (Subgroup.centralizer ({a} : Set G))) A (piCompl 3)
  rcases (h143 a ha ha1 hΩa Q hQ).2 with h1 |
      ⟨b, d, Lb, hb, hLb, -, hdA, hd1, hdc, -, X, hX, hinv, hcase⟩
  · rw [h1]
    have h := noSimpleSec_sup (p := 21) (by norm_num) ha (X := ⊥) bot_le
      (by rw [sup_bot_eq]; exact inf_le_left.trans (le_normalizer_pPrimeCoreOf 3 _))
      (of_subsingleton 21)
    rwa [sup_bot_eq] at h
  · have hnorm : Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.normalizer (A : Set G) ≤
        Subgroup.normalizer
          ((pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X : Subgroup G) : Set G) :=
      hinv.elim (fun h => inf_le_left.trans h) (fun h => h.2.2.2)
    have hXa : X ≤ Subgroup.centralizer ({a} : Set G) := by
      have hΔ : delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ≤
          Subgroup.centralizer ({a} : Set G) := sSup_le fun Q hQ => hQ.2
      rw [hX] at hΔ
      exact le_sup_right.trans hΔ
    rw [hX]
    refine noSimpleSec_sup (by norm_num) ha hXa hnorm ?_
    rcases hcase with ⟨-, hXeq, -⟩ | ⟨had, ⟨𝒳, h𝒳, -, rfl⟩, hON | h6 | h66⟩
    · exact noSimpleSec_of_eq_sup_theta hXeq (of_not_dvd fun h21 =>
        not_seven_dvd_card_lB h415 hΩ ha1 hac (dvd_trans (by norm_num) h21))
    · exfalso
      have hbc : Subgroup.zpowers b = Subgroup.zpowers c := by
        rw [hΩ] at hb
        exact hb
      have h3L : 3 ∣ Nat.card L := by
        obtain ⟨φ⟩ := hJ
        exact Proof1515.three_dvd_card_of_mulEquiv φ
          (by rw [KFacts.KS14.card_nativeJ2]; norm_num)
      have hLb' : Lb = L := Proof1515.eq_of_mem_lA_of_zpowers_eq hR.toSec14Std h3L hbc hLb
      subst hLb'
      exact false_of_on_join h45 h48 h134 hR hJ hΩ hdA hd1 hdc
        (h𝒳.trans (Proof1515.thetaComponentsAt_eq_of_zpowers_eq had).le) hON
    · exact noSimpleSec21_of_a6 (Or.inl h6)
    · exact noSimpleSec21_of_a6 (Or.inr h66)

theorem false_of_mulEquiv {A L : Subgroup G} {c : G} (h143 : Ronan148Q.Item143Q A (lB A))
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h134 : Item134) (hR : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hΩ : omegaA A = {Subgroup.zpowers c}) {K : Subgroup G} (hK : K ∈ scriptY4 A (lB A))
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hSp : ¬ (Nat.card S).Prime)
    (φ : ↥K ⧸ CFSG.pPrimeCore 3 ↥K ≃* S)
    (hS : ∀ B : Subgroup (MulAut S), CFSG.Assembly.IsElemAbelian 3 B → Nat.card B ≤ 9)
    (hSJ : ∀ (H' : Subgroup CFSG.Blueprint.NativeSporadic.J2) (f' : ↥H' →* S),
      ¬ Function.Surjective f') (h21 : 21 ∣ Nat.card S) : False := by
  have hnab : ∃ x y : S, x * y ≠ y * x := by
    by_contra h
    push Not at h
    let _ : CommGroup S := { ‹Group S› with mul_comm := fun a b => h a b }
    exact hSp (CommGroup.is_simple_iff_prime_card.mp ‹IsSimpleGroup S›)
  obtain ⟨a, ha, ha1, hac, hcent⟩ := exists_centralizing_ne hR hJ hK.1 hnab φ hS hSJ
  obtain ⟨D, hDK, hDΔ, hKD⟩ := exists_le_delta_cover
    (Late.isE27_of_mem_partTwoE hR.mem_partTwoE) hK.2.2.1 ha hcent
  obtain ⟨f, hf⟩ := exists_surj_of_le_sup hDK hKD φ
  have hker : (Subgroup.inclusion hDΔ).ker ≤ f.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr (Subgroup.inclusion_injective hDΔ)]
    exact bot_le
  exact (noSimpleSec21_delta h143 h45 h48 h134 hR hJ hΩ ha ha1 hac).not_dvd_of_surjective_of_ker_le
    (Subgroup.inclusion hDΔ) f hf hker hnab h21

theorem res1J2X1_of (h143 : Ronan148Q.Item143QS14) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h134 : Item134) : Res1J2X1 := by
  intro G _ _ A c L hR hJ hΩ K hK
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hY4 : K ∈ scriptY4 A (lB A) := hK.prop.1
  have h143' : Ronan148Q.Item143Q A (lB A) := h143 G A c L hR.toSec14Std
  refine ⟨⟨fun φ => ?_⟩, fun ⟨hF, ⟨φ⟩⟩ => ?_⟩
  · haveI : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact false_of_mulEquiv h143' h45 h48 h134 hR hJ hΩ hY4
      (by rw [Res9ON.card_alternatingGroup_seven]; norm_num) φ
      Sec10.Item1015Proof.card_le_nine_of_mulAut_alt7 (fun H' f' => not_surj_j2_alt7 h415 H' f')
      (by rw [Res9ON.card_alternatingGroup_seven]; norm_num)
  · haveI : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) :=
      Sec4.Item462AltProof.isSimpleGroup_projSL_three _
    exact false_of_mulEquiv h143' h45 h48 h134 hR hJ hΩ hY4
      (by rw [Proof1515.card_projSL_three_seven]; norm_num) φ
      (Sec10.Item1015Proof.card_le_nine_of_mulAut_projSL (by norm_num) le_rfl (by norm_num))
      (fun H' f' => not_surj_j2_projSL_seven H' f')
      (by rw [Proof1515.card_projSL_three_seven]; norm_num)

end D2

end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1
