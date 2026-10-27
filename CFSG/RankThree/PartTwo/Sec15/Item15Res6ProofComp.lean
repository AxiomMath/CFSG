module

public import CFSG.RankThree.PartTwo.Sec15.Item152ConfBProofJ
import CFSG.RankThree.PartTwo.Sec15.Read148PerfProof
import CFSG.RankThree.PartTwo.Sec15.Item153Twin3ProofCase7
import CFSG.RankThree.PartTwo.Sec15.Item15Res3ProofInner
import CFSG.RankThree.PartTwo.KFacts.K71SU3AutFacts
import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.Sporadic.ON
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec15.Item15Type
public import CFSG.RankThree.PartTwo.Sec16.Item167Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Proof15Res6

theorem isQuasisimple_of_isSimpleGroup_of_isPerfect {X : Type*} [Group X] (hs : IsSimpleGroup X)
    (hX : Group.IsPerfect X) : IsQuasisimple X := by
  have : Nontrivial X := IsSimpleGroup.toNontrivial
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Y4Core.exists_ne_comm_of_isPerfect hX)).1

theorem isQuasisimple_of_isTripleCover_of_isPerfect {X S : Type*} [Group X] [Group S]
    [IsSimpleGroup S] (hX : Group.IsPerfect X) (h : Sec4.IsTripleCover X S) : IsQuasisimple X := by
  obtain ⟨hz, ⟨φ⟩⟩ := h
  have hSp : Group.IsPerfect S :=
    Group.IsPerfect.ofSurjective (f := φ.toMonoidHom.comp (QuotientGroup.mk' _))
      (φ.surjective.comp (QuotientGroup.mk'_surjective _))
  have : Nontrivial S := IsSimpleGroup.toNontrivial
  exact Y4Core.isQuasisimple_of_isTripleCover (Y4Core.exists_ne_comm_of_isPerfect hSp) hX
    ⟨hz, ⟨φ⟩⟩

omit [Finite G] in
theorem isElemAbelian_subgroupOf' {p : ℕ} {E : Subgroup G} (X : Subgroup G)
    (hE : CFSG.Assembly.IsElemAbelian p E) : CFSG.Assembly.IsElemAbelian p (E.subgroupOf X) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
  · show ((a : X) : G) * ((b : X) : G) = ((b : X) : G) * ((a : X) : G)
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨((a : X) : G), a.2⟩ ⟨((b : X) : G), b.2⟩)
  · show ((x : G)) ^ p = 1
    exact hE.2 x hx

theorem exists_elemAbelian_of_quot {Y : Subgroup G} {E : Subgroup (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) :
    ∃ B : Subgroup G, B ≤ Y ∧ CFSG.Assembly.IsElemAbelian 3 B ∧ Nat.card B = Nat.card E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := CFSG.pPrimeCore 3 ↥Y with hN
  set φ := QuotientGroup.mk' N with hφ
  have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 _ x.2)⟩
  have hEle : E ≤ (⊤ : Subgroup ↥Y).map φ := by
    rw [← MonoidHom.range_eq_map, QuotientGroup.range_mk']
    exact le_top
  obtain ⟨P, -, hP3, hPE⟩ := Proof15Res3Inner.exists_isPGroup_map_eq_of_le_map φ hE3 hEle
  have hN3 : ¬ 3 ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hinj : Function.Injective (φ.comp P.subtype) := by
    intro u v huv
    have h1 : (u : ↥Y)⁻¹ * v ∈ N := by
      have := huv
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, hφ, QuotientGroup.mk'_apply,
        QuotientGroup.eq] at this
      exact this
    obtain ⟨k, hk⟩ := hP3 (u⁻¹ * v)
    have h2 : ((u : ↥Y)⁻¹ * v) ^ 3 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have h3 := KFacts.eq_one_of_pow_three_pow_eq_one hN3 h1 h2
    exact Subtype.ext (inv_mul_eq_one.mp h3)
  have hrange : (φ.comp P.subtype).range = E := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hPE]
  let e : ↥P ≃* ↥E := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hPcard : Nat.card P = Nat.card E := Nat.card_congr e.toEquiv
  have hPab : CFSG.Assembly.IsElemAbelian 3 P := by
    refine ⟨⟨⟨fun x y => e.injective ?_⟩⟩, fun x hx => ?_⟩
    · rw [map_mul, map_mul]
      exact hE.1.is_comm.comm (e x) (e y)
    · have h1 : ((e ⟨x, hx⟩ : ↥E) : ↥Y ⧸ N) ^ 3 = 1 := hE.2 _ (e ⟨x, hx⟩).2
      have h2 : e (⟨x, hx⟩ ^ 3) = e 1 := by
        apply Subtype.ext
        rw [map_pow, map_one, Subgroup.coe_pow, h1]
        rfl
      exact congrArg Subtype.val (e.injective h2)
  refine ⟨P.map Y.subtype, Subgroup.map_subtype_le P, CFSG.SectionRank.isElemAbelian_map hPab _, ?_⟩
  rw [Subgroup.card_map_of_injective Y.subtype_injective, hPcard]

theorem false_of_e81_le {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {M : Subgroup G}
    (hO : CFSG.Open.pCoreOf 2 M ≠ ⊥) {F : Subgroup G} (hF : CFSG.Assembly.IsElemAbelian 3 F)
    (hF81 : Nat.card F = 81) (hFM : F ≤ M) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFE : partTwoF G = partTwoE G :=
    (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.toSec13Data.partTwoS_eq).1
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥F) 3 (n := 3)
    (by rw [hF81]; norm_num)
  set D := K.map F.subtype with hD
  have hDF : D ≤ F := Subgroup.map_subtype_le K
  have hD27 : Nat.card D = 27 := by
    rw [hD, Subgroup.card_map_of_injective F.subtype_injective, hK]
    norm_num
  have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hDe : CFSG.Assembly.IsElemAbelian 3 D :=
    ⟨⟨⟨fun x y => Subtype.ext (hFc x (hDF x.2) y (hDF y.2))⟩⟩, fun x hx => hF.2 x (hDF hx)⟩
  obtain ⟨w, hwF, hwD⟩ : ∃ w ∈ F, w ∉ D := by
    by_contra hcon
    push Not at hcon
    have hle := Subgroup.card_le_of_le (show F ≤ D from hcon)
    rw [hF81, hD27] at hle
    norm_num at hle
  have hw1 : w ≠ 1 := fun h1 => hwD (h1 ▸ one_mem _)
  have hw3 : orderOf w = 3 := orderOf_eq_prime (hF.2 w hwF) hw1
  have hwc : w ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact hFc d (hDF hd) w hwF
  exact Sec12.false_of_le_E81 hFE hDe hD27 hO (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) M)
    ((hDF.trans hFM).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)) hwc hw3 hwD

section Abstract

variable {Γ : Type} [Group Γ]

theorem exists_e9_le_factor {D B J : Subgroup Γ} (hBc : IsMulCommutative B)
    (hBD : B ≤ Subgroup.normalizer (D : Set Γ)) (hJD : J ≤ D) (hJn : (J.subgroupOf D).Normal)
    (hJq : IsQuasisimple ↥J) {p f : ℕ} (hP : IsZ3PGLThreeAt ↥(J ⊔ B) p f) :
    ∃ E : Subgroup Γ, E ≤ J ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have hUq : IsQuasisimple ↥(J.subgroupOf D) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJD).symm hJq
  have hUJ : (J.subgroupOf D).map D.subtype ≤ J := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_le_left
  obtain ⟨-, E, hE, hE9⟩ := Proof153Twin3.center_eq_bot_and_e9_of_le_factor hBc hBD hJD hP
    hJn.isSubnormal hUq hUJ
  set φ : ↥(J.subgroupOf D) →* Γ := D.subtype.comp (J.subgroupOf D).subtype with hφ
  have hφi : Function.Injective φ := D.subtype_injective.comp (Subgroup.subtype_injective _)
  refine ⟨E.map φ, ?_, CFSG.SectionRank.isElemAbelian_map hE φ, ?_⟩
  · rintro _ ⟨e, -, rfl⟩
    exact Subgroup.mem_subgroupOf.mp e.2
  · rw [Subgroup.card_map_of_injective hφi, hE9]

variable [Finite Γ]

theorem exists_e81_of_case7 {D J₁ J₂ B : Subgroup Γ} (hD : Group.IsPerfect ↥D)
    (hsup : J₁ ⊔ J₂ = D) (hinf : J₁ ⊓ J₂ = ⊥) (hcomm : ⁅J₁, J₂⁆ = ⊥) (hB : IsMulCommutative B)
    (hBD : B ≤ Subgroup.normalizer (D : Set Γ)) {p₁ f₁ p₂ f₂ : ℕ}
    (hZ₁ : IsZ3PGLThreeAt ↥(J₁ ⊔ B) p₁ f₁) (hZ₂ : IsZ3PGLThreeAt ↥(J₂ ⊔ B) p₂ f₂) :
    ∃ F : Subgroup Γ, F ≤ D ∧ CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 81 := by
  have hJ₁D : J₁ ≤ D := hsup ▸ le_sup_left
  have hJ₂D : J₂ ≤ D := hsup ▸ le_sup_right
  have hC₁ : J₂ ≤ Subgroup.centralizer (J₁ : Set Γ) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hcomm
  have hC₂ : J₁ ≤ Subgroup.centralizer (J₂ : Set Γ) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hN₁ : D ≤ Subgroup.normalizer (J₁ : Set Γ) := by
    rw [← hsup]
    exact sup_le Subgroup.le_normalizer (hC₁.trans (Subgroup.centralizer_le_normalizer _))
  have hN₂ : D ≤ Subgroup.normalizer (J₂ : Set Γ) := by
    rw [← hsup]
    exact sup_le (hC₂.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  set U := J₁.subgroupOf D with hU
  set V := J₂.subgroupOf D with hV
  have hUn : U.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hJ₁D).mpr hN₁
  have hVn : V.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hJ₂D).mpr hN₂
  have hsup' : U ⊔ V = ⊤ := by
    rw [hU, hV, ← Subgroup.subgroupOf_sup hJ₁D hJ₂D, hsup, Subgroup.subgroupOf_self]
  have hinf' : U ⊓ V = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : (x : Γ) ∈ J₁ ⊓ J₂ := ⟨hx.1, hx.2⟩
    rw [hinf] at h1
    exact (Subgroup.mem_bot).mpr (Subtype.ext ((Subgroup.mem_bot).mp h1))
  have hUp : ⁅U, U⁆ = U := Y4Core.commutator_eq_self_of_inf_eq_bot hD hsup' hinf'
  have hVp : ⁅V, V⁆ = V :=
    Y4Core.commutator_eq_self_of_inf_eq_bot hD (by rw [sup_comm]; exact hsup')
      (by rw [inf_comm]; exact hinf')
  have hJ₁p : ⁅J₁, J₁⁆ = J₁ := by
    have := congrArg (Subgroup.map D.subtype) hUp
    rwa [Subgroup.map_commutator, hU, Subgroup.map_subgroupOf_eq_of_le hJ₁D] at this
  have hJ₂p : ⁅J₂, J₂⁆ = J₂ := by
    have := congrArg (Subgroup.map D.subtype) hVp
    rwa [Subgroup.map_commutator, hV, Subgroup.map_subgroupOf_eq_of_le hJ₂D] at this
  have hG₁ : Y4Core.Good3 ↥J₁ := Y4Core.good3_of_isZ3PGLThreeAt hJ₁D hN₁ hJ₁p hB hBD hZ₁
  have hG₂ : Y4Core.Good3 ↥J₂ := Y4Core.good3_of_isZ3PGLThreeAt hJ₂D hN₂ hJ₂p hB hBD hZ₂
  obtain ⟨E₁, hE₁J, hE₁, hE₁9⟩ := exists_e9_le_factor hB hBD hJ₁D hUn hG₁.1 hZ₁
  obtain ⟨E₂, hE₂J, hE₂, hE₂9⟩ := exists_e9_le_factor hB hBD hJ₂D hVn hG₂.1 hZ₂
  have hc : ∀ x ∈ E₁, ∀ y ∈ E₂, x * y = y * x := fun x hx y hy =>
    ((Subgroup.mem_centralizer_iff.mp (hC₂ (hE₁J hx))) y (hE₂J hy)).symm
  have hEinf : E₁ ⊓ E₂ = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    exact inf_le_inf hE₁J hE₂J
  refine ⟨E₁ ⊔ E₂, sup_le (hE₁J.trans hJ₁D) (hE₂J.trans hJ₂D), Sec13.isElemAbelian_sup hE₁ hE₂ hc,
    ?_⟩
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E₁ E₂ hc).1
  rw [hEinf, Subgroup.card_bot, mul_one, hE₁9, hE₂9] at hcard
  rw [hcard]

end Abstract

theorem false_of_case148Seven_two
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (h148 : Item148 A (lB A)) {M : Subgroup G} (hM : M ∈ scriptY2 A)
    (h7 : letI := ker148_normal hM.1.2; Case148Seven A (lB A) M) : False := by
  let := ker148_normal hM.1.2
  have hAab : IsMulCommutative A := h.isElemAbelian.1
  obtain ⟨a₁, a₂, L₁, L₂, J₁, J₂, p₁, f₁, e₁, p₂, f₂, e₂, _, _, -, -, -, -, hJ₁, hJ₂,
    hsup, hinf, hcomm, -, -, -, -, hZ₁, hZ₂, -, -⟩ := h7
  have hperf : Group.IsPerfect ↥(img148 A M (deltaZero A (lB A) M)) :=
    Read148Perf.isPerfect_img148 h h148 hM.1
  have hB : IsMulCommutative ↥(img148 A M A) := ⟨⟨img148_comm hAab⟩⟩
  have hBD : img148 A M A ≤
      Subgroup.normalizer (img148 A M (deltaZero A (lB A) M) : Set _) :=
    Sec14.img148_le_normalizer (Sec16.le_normalizer_deltaZero (A := A) (LB := lB A) M)
  rw [img148_sup ((hJ₁.trans inf_le_right).trans le_sup_left) le_sup_right] at hZ₁
  rw [img148_sup ((hJ₂.trans inf_le_right).trans le_sup_left) le_sup_right] at hZ₂
  obtain ⟨F, hFD, hF, hF81⟩ := exists_e81_of_case7 hperf hsup hinf hcomm hB hBD hZ₁ hZ₂
  obtain ⟨e₀⟩ := Y4Core.nonempty_img148_equiv_map hM.1.2 (deltaZero_le (LB := lB A) M)
  set D' := ((deltaZero A (lB A) M).subgroupOf M).map
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) with hD'
  set ψ : ↥(img148 A M (deltaZero A (lB A) M)) →* ↥M ⧸ CFSG.pPrimeCore 3 ↥M :=
    D'.subtype.comp e₀.toMonoidHom with hψ
  have hψi : Function.Injective ψ := D'.subtype_injective.comp e₀.injective
  have hF' : CFSG.Assembly.IsElemAbelian 3
      ((F.subgroupOf (img148 A M (deltaZero A (lB A) M))).map ψ) :=
    CFSG.SectionRank.isElemAbelian_map (isElemAbelian_subgroupOf' _ hF) ψ
  have hF'81 : Nat.card ((F.subgroupOf (img148 A M (deltaZero A (lB A) M))).map ψ) = 81 := by
    rw [Subgroup.card_map_of_injective hψi,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFD).toEquiv, hF81]
  obtain ⟨E, hEM, hE, hE81⟩ := exists_elemAbelian_of_quot hF'
  exact false_of_e81_le h hM.2 hE (hE81.trans hF'81) hEM

end Proof15Res6

section Certificates


@[expose] noncomputable def Step152CompJProdR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY4 A (lB A), ∀ (M : Subgroup G) (hM : M ∈ scriptY2 A),
      Y ≤ M → generalizedFitting ↥M = CFSG.pCore 2 ↥M → Y ≤ deltaZero A (lB A) M →
      (Y.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) ≠ ⊥ →
      ¬ IsQuasisimple ↥(((deltaZero A (lB A) M).subgroupOf M).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))) →
      (letI := ker148_normal hM.1.2;
        (Case148Three A (lB A) M ∧
            (IsCentralProductA6Covers ↥(img148 A M (deltaZero A (lB A) M)) ∨
              IsA6CoverTimesA5 ↥(img148 A M (deltaZero A (lB A) M)) ∨
              Nonempty (↥(img148 A M (deltaZero A (lB A) M)) ≃*
                alternatingGroup (Fin 5) × alternatingGroup (Fin 5)))) ∨
          Case148Six A (lB A) M) →
        ∃ J : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M), IsComponent J ∧
          (Y.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) ≤ J

theorem step152CompJNTR_of_res6
    (h148 : Item148R) (hP : Step152CompJProdR) : Step152CompJNTR := by
  intro G _ _ A c L hR Y hY M hM hYM hF hYΔ hY1 hq
  have h14 := hR.toSec14Std
  have h148' := h148 G A c L hR
  let := ker148_normal hM.1.2
  obtain ⟨e₀⟩ := Y4Core.nonempty_img148_equiv_map hM.1.2 (deltaZero_le (LB := lB A) M)
  have hperf : Group.IsPerfect ↥(img148 A M (deltaZero A (lB A) M)) :=
    Read148Perf.isPerfect_img148 h14 h148' hM.1
  have hnq : ¬ IsQuasisimple ↥(img148 A M (deltaZero A (lB A) M)) := fun hq' =>
    hq (CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀ hq')
  have hsimp : ¬ IsSimpleGroup ↥(img148 A M (deltaZero A (lB A) M)) := fun hs =>
    hnq (Proof15Res6.isQuasisimple_of_isSimpleGroup_of_isPerfect hs hperf)
  obtain ⟨-, hcases⟩ := (item148_iff A (lB A)).mp h148' M hM.1
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7
  ·
    exfalso
    apply hY1
    rw [eq_bot_iff]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzy⟩ := h1 (hYΔ (Subgroup.mem_subgroupOf.mp hy))
    have hzy' : z = y := Subtype.ext hzy
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hzy' ▸ hz
  ·
    exfalso
    obtain ⟨c', -, -, L', hL', hcases⟩ := h2
    rcases hcases with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e, hp, hf, he, -, hε⟩ | ⟨-, h6' | ⟨⟨φ⟩⟩⟩
    · exact hnq (CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm
        (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL'.1))
    · have := Y4Core.isSimpleGroup_alternatingGroup 7 (by norm_num)
      exact hsimp φ.isSimpleGroup
    · exact hsimp (Main148.isSimpleGroup_of_isLThreeEpsAt148 hf hε)
    · have := Y4Core.isSimpleGroup_alternatingGroup 6 (by norm_num)
      exact hnq (Proof15Res6.isQuasisimple_of_isTripleCover_of_isPerfect hperf h6')
    · have := Y4Core.isSimpleGroup_alternatingGroup 5 le_rfl
      exact hsimp φ.isSimpleGroup
  ·
    have h3' := h3
    obtain ⟨c', d, L', -, -, -, -, -, -, -, hcases⟩ := h3'
    rcases hcases with hON | hCP | hA6A5 | hφ | ⟨⟨φ⟩⟩ | ⟨_, ⟨φ⟩⟩
    · exfalso
      have := CFSG.Sporadic.ON.fam_on_simplicity.2.2
      exact hnq (Proof15Res6.isQuasisimple_of_isTripleCover_of_isPerfect hperf hON)
    · exact hP G A c L hR Y hY M hM hYM hF hYΔ hY1 hq (Or.inl ⟨h3, Or.inl hCP⟩)
    · exact hP G A c L hR Y hY M hM hYM hF hYΔ hY1 hq (Or.inl ⟨h3, Or.inr (Or.inl hA6A5)⟩)
    · exact hP G A c L hR Y hY M hM hYM hF hYΔ hY1 hq (Or.inl ⟨h3, Or.inr (Or.inr hφ)⟩)
    · exfalso
      have := Y4Core.isSimpleGroup_alternatingGroup 7 (by norm_num)
      exact hsimp φ.isSimpleGroup
    · exfalso
      have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 7 1)
      exact hsimp φ.isSimpleGroup
  ·
    exfalso
    obtain ⟨⟨φ⟩, -, -⟩ := h4
    have := Y4Core.isSimpleGroup_alternatingGroup 10 (by norm_num)
    exact hsimp φ.isSimpleGroup
  ·
    exfalso
    obtain ⟨c', -, L', n, m, -, -, hn, -, hiso, -⟩ := h5
    have : Group.IsPerfect ↥(img148 A M (deltaZero A (lB A) M)) := hperf
    exact hsimp (Sec19.Step1914TriProof.isSimpleGroup_of_isoLThreePi (by omega : 1 ≤ 3 * n)
      hiso).1
  ·
    exact hP G A c L hR Y hY M hM hYM hF hYΔ hY1 hq (Or.inr h6)
  ·
    exact (Proof15Res6.false_of_case148Seven_two h14 h148' hM h7).elim

end Certificates

end CFSG.RankThree.PartTwo.Sec15
