module

public import CFSG.RankThree.PartTwo.Sec16.Item162Res5ProofOther
import CFSG.RankThree.PartTwo.Sec16.Item162Res5ProofFaithful
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec16.Item162ResProofTools
import CFSG.RankThree.PartTwo.Sec16.Item162StepsProofTools
import CFSG.RankThree.PartTwo.Sec16.Item163ProofY4
import CFSG.RankThree.PartTwo.Sec15.Item1515ResProofCover
import CFSG.RankThree.PartTwo.Sec17.Item17Q0Proof
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] def Step162A7OtherFreeMeet : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y₁ Y₂ S : Subgroup G, MaxCE162 A (lB A) Y₁ Y₂ S S → L ≤ Y₁ →
      MeetsY4 A (lB A) L Y₁ →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
      WStarS4 A → TransOmegaThree A c →
      Nonempty (↥Y₁ ⧸ CFSG.pCore 2 ↥Y₁ ≃* alternatingGroup (Fin 7)) →
      (¬ ∃ g ∈ Subgroup.normalizer (A : Set G), Y₂ = Y₁.map (MulAut.conj g).toMonoidHom) →
      Choice162 A c S →
      ∀ (b : G) (Lb : Subgroup G), Subgroup.zpowers b ∈ omegaA A → Lb ∈ lA A b →
        Subgroup.zpowers b ≠ Subgroup.zpowers c → MeetsY4 A (lB A) Lb Y₂ →
        Nonempty (↥Y₂ ⧸ CFSG.pCore 2 ↥Y₂ ≃* alternatingGroup (Fin 7)) →
        Late.sectionCentralizer A Y₂ (CFSG.Open.pCoreOf 2 Y₂) = (Subgroup.zpowers b : Set G) →
        CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) ⊓ Subgroup.normalizer (Subgroup.zpowers b : Set G) = ⊥ →
        (Y₂ ⊓ Lb) ⊓ CFSG.Open.pCoreOf 2 Y₂ = ⊥ →
        S ⊓ Subgroup.centralizer ({b} : Set G) ≤ Y₂ ⊓ Lb →
        (∀ w ∈ Subgroup.normalizer (A : Set G),
          Subgroup.zpowers b = (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom →
            CFSG.Open.pCoreOf 2 Y₂ ⊓
              CFSG.Open.pCoreOf 2 (Y₁.map (MulAut.conj w).toMonoidHom) = ⊥) →
          False

namespace Res162Six

variable {G : Type} [Group G] [Finite G]

theorem mem_scriptY4_oRes_sup {A : Subgroup G} {E D Y : Subgroup G}
    (hE4 : E ∈ scriptY4 A (lB A)) (hDQ : D ∈ scriptQ A (lB A))
    (hED : E ≤ Subgroup.normalizer (D : Set G)) (hY : Y ∈ scriptY4 A (lB A))
    (hEDY : E ⊔ D ≤ Y) (hcov : Y ≤ E ⊔ CFSG.Open.pCoreOf 2 Y) :
    oPrimeResidualOf 3 (E ⊔ D) ∈ scriptY4 A (lB A) := by
  set X := oPrimeResidualOf 3 (E ⊔ D) with hXdef
  have hXY : X ≤ E ⊔ D := Subgroup.map_subtype_le _
  have hEX : E ≤ X := hE4.2.1.le.trans (oPrimeResidualOf_mono 3 le_sup_left)
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := hDQ.1.2.2
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    Proof1515Res.le_normalizer_oRes3 (le_normalizer_sup hE4.1.2 hAD)
  have hXcov : X ≤ E ⊔ (X ⊓ D) := by
    intro x hx
    have hx' : x ∈ ((E ⊔ D : Subgroup G) : Set G) := hXY hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right E D hED] at hx'
    obtain ⟨e, he, d, hd, rfl⟩ := hx'
    have hdX : d ∈ X := by
      have := mul_mem (inv_mem (hEX he)) hx
      rwa [inv_mul_cancel_left] at this
    exact mul_mem (Subgroup.mem_sup_left he) (Subgroup.mem_sup_right ⟨hdX, hd⟩)
  have hXΔ : X = delta A (lB A) X := by
    refine le_antisymm (hXcov.trans (sup_le (hE4.2.2.1.le.trans (delta_mono hEX)) ?_))
      (delta_le _)
    exact le_delta (mem_scriptQ_of_le hDQ inf_le_right (Late.le_normalizer_inf hAX hAD))
      inf_le_left
  have h3 : 3 ∣ Nat.card X :=
    ((Proof1515.three_dvd_card_of_mem_scriptY4 hE4).trans
      (Subgroup.card_quotient_dvd_card _)).trans (Subgroup.card_dvd_of_le hEX)
  exact ⟨⟨fun ht => hY.1.1 (top_le_iff.mp (ht ▸ hXY.trans hEDY)), hAX⟩,
    (Proof1515Res.oRes3_idem _).symm, hXΔ,
    isQuasisimple_of_cover hY (hXY.trans hEDY) (hcov.trans (sup_le_sup_right hEX _)) h3⟩

theorem eq_of_sup_side {A : Subgroup G} (h155 : Item155 A (lB A))
    (h153 : Item153Main A (lB A)) {E D : Subgroup G} (hE4 : E ∈ scriptY4 A (lB A))
    (hDQ : D ∈ scriptQ A (lB A)) (hD2 : IsPGroup 2 D) (hD1 : D ≠ ⊥)
    (hED : E ≤ Subgroup.normalizer (D : Set G)) (htop : E ⊔ D ≠ ⊤)
    (hX4 : oPrimeResidualOf 3 (E ⊔ D) ∈ scriptY4 A (lB A))
    {K₁ K₂ : Subgroup G} (hK₁ : K₁ ∈ scriptY0Star A (lB A)) (hK₂ : K₂ ∈ scriptY0Star A (lB A))
    (hXK₁ : oPrimeResidualOf 3 (E ⊔ D) ≤ K₁) (hXK₂ : oPrimeResidualOf 3 (E ⊔ D) ≤ K₂)
    (hN₁ : E ⊔ D ≤ Subgroup.normalizer (K₁ : Set G))
    (hN₂ : E ⊔ D ≤ Subgroup.normalizer (K₂ : Set G))
    (hside : K₂ = oPrimeResidualOf 3 (E ⊔ D) ⊔ CFSG.Open.pCoreOf 2 K₂) : K₁ = K₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY'D : E ⊔ D ≤ Subgroup.normalizer (D : Set G) := sup_le hED Subgroup.le_normalizer
  have hDO : D ≤ CFSG.Open.pCoreOf 2 (E ⊔ D) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right hY'D hD2
  have hO2 : CFSG.Open.pCoreOf 2 (E ⊔ D) ≠ ⊥ := fun h0 => hD1 (le_bot_iff.mp (h0 ▸ hDO))
  have hY'Δ : E ⊔ D = delta A (lB A) (E ⊔ D) :=
    le_antisymm (sup_le (hE4.2.2.1.le.trans (delta_mono le_sup_left)) (le_delta hDQ le_sup_right))
      (delta_le _)
  have hAY' : A ≤ Subgroup.normalizer ((E ⊔ D : Subgroup G) : Set G) :=
    le_normalizer_sup hE4.1.2 hDQ.1.2.2
  have hY'3 : E ⊔ D ∈ scriptY3 A (lB A) := ⟨⟨⟨htop, hAY'⟩, hO2⟩, hY'Δ⟩
  have hEX : E ≤ oPrimeResidualOf 3 (E ⊔ D) :=
    hE4.2.1.le.trans (oPrimeResidualOf_mono 3 le_sup_left)
  have hY'eq : E ⊔ D = oPrimeResidualOf 3 (E ⊔ D) ⊔ CFSG.Open.pCoreOf 2 (E ⊔ D) :=
    le_antisymm (sup_le (hEX.trans le_sup_left) (hDO.trans le_sup_right))
      (sup_le (Subgroup.map_subtype_le _) (CFSG.LieType.BorelTits.pCoreOf_le 2 _))
  exact Proof162.eq_of_mem_gam155 h155 h153 hY'3 hX4 hY'eq ⟨hK₁, hXK₁, hN₁⟩ ⟨hK₂, hXK₂, hN₂⟩
    (Or.inr hside)

theorem pCoreOf_inf_conj_eq_bot {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (h155 : Item155 A (lB A)) (h153 : Item153Main A (lB A))
    (h142 : Concl142 A (lB A)) {b : G} {Lb : Subgroup G} (hb : Subgroup.zpowers b ∈ omegaA A)
    (hLb : Lb ∈ lA A b) (h1444b : Item1444 A (lB A)) (h146b : Item146 A (lB A))
    (hbotb : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) {Y₁ Y₂ : Subgroup G}
    (hY₁ : Y₁ ∈ scriptY0Star A (lB A)) (hY₂ : Y₂ ∈ scriptY0Star A (lB A)) (hLY₁ : L ≤ Y₁)
    (hm₂ : MeetsY4 A (lB A) Lb Y₂) (φ₂ : ↥Y₂ ⧸ CFSG.pCore 2 ↥Y₂ ≃* alternatingGroup (Fin 7))
    (hnW : ¬ ∃ g ∈ Subgroup.normalizer (A : Set G), Y₂ = Y₁.map (MulAut.conj g).toMonoidHom)
    {w : G} (hw : w ∈ Subgroup.normalizer (A : Set G))
    (hbw : Subgroup.zpowers b = (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom) :
    CFSG.Open.pCoreOf 2 Y₂ ⊓ CFSG.Open.pCoreOf 2 (Y₁.map (MulAut.conj w).toMonoidHom) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hD1
  have hb' : Sec15R G A b Lb := sec15R_of_point h hb hLb
  have hY₂4 : Y₂ ∈ scriptY4 A (lB A) := hY₂.prop.1
  have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp hb).1
  set Hb := Subgroup.normalizer (Subgroup.zpowers b : Set G) with hHb
  have hCb : Subgroup.centralizer ({b} : Set G) ≤ Hb :=
    centralizer_singleton_le_normalizer_zpowers b
  have hLbC : Lb ≤ Subgroup.centralizer ({b} : Set G) := hb'.toSec13Data.le_centralizer
  have hAY₂ : A ≤ Subgroup.normalizer (Y₂ : Set G) := hY₂.prop.1.1.2
  set M := Y₂ ⊓ Lb with hM
  set E := oPrimeResidualOf 3 M with hE
  have hEM : E ≤ M := Subgroup.map_subtype_le _
  have hEY₂ : E ≤ Y₂ := hEM.trans inf_le_left
  have hELb : E ≤ Lb := hEM.trans inf_le_right
  have hcovY₂ : Y₂ = (Y₂ ⊓ Lb) ⊔ CFSG.Open.pCoreOf 2 Y₂ := by
    have hcov := Res162b.eq_top_of_seven hb' hY₂ hm₂ φ₂
    refine Res162.eq_sup_of_forall_mem fun y hy => ?_
    obtain ⟨d, hd, hdy⟩ := hcov y hy
    exact ⟨d, ⟨hd.2, hd.1⟩, hdy⟩
  have hcovE : Y₂ ≤ E ⊔ CFSG.Open.pCoreOf 2 Y₂ :=
    Proof1515Res.le_oRes3_sup hY₂4.2.1 inf_le_left (CFSG.LieType.BorelTits.pCoreOf_le 2 Y₂)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₂) hcovY₂.le
  have hAE : A ≤ Subgroup.normalizer (E : Set G) :=
    Proof1515Res.le_normalizer_oRes3 (Late.le_normalizer_inf hAY₂ hLb.2.1)
  have hmemE : ∀ R' : Subgroup G, R' ≤ E → ¬ 3 ∣ Nat.card R' →
      A ≤ Subgroup.normalizer (R' : Set G) → R' ∈ scriptQ A (lB A) := fun R' hR'E hR'3 hAR' =>
    mem_scriptQ_of_concl142 h142 hb ⟨(hR'E.trans (hELb.trans hLbC)).trans hCb,
      (isPiSubgroup_piCompl_iff Nat.prime_three R').mpr hR'3, hAR'⟩
  have hE4 : E ∈ scriptY4 A (lB A) := Proof1515Res.mem_scriptY4_of_le_cover hY₂4 hEY₂ hcovE hAE
    (Proof1515Res.oRes3_idem M).symm hmemE
  have hLw : L.map (MulAut.conj w).toMonoidHom = Lb :=
    map_conj_eq_of_zpowers hb' h.zpowers_mem_omegaA h.mem_lA hw hbw
  set Y₁w := Y₁.map (MulAut.conj w).toMonoidHom with hY₁wdef
  have hY₁w : Y₁w ∈ scriptY0Star A (lB A) := map_conj_mem_scriptY0Star hw hY₁
  have hLbY₁w : Lb ≤ Y₁w := hLw ▸ Subgroup.map_mono hLY₁
  have hEY₁w : E ≤ Y₁w := hELb.trans hLbY₁w
  have hO₂Q : CFSG.Open.pCoreOf 2 Y₂ ∈ scriptQ A (lB A) :=
    Sec17.Proof17Q0.pCoreOf_mem_scriptQ_of_cover hb'.toSec14Std h1444b h146b hbotb h142 hY₂4
      (Or.inl hcovY₂)
  set D := CFSG.Open.pCoreOf 2 Y₂ ⊓ CFSG.Open.pCoreOf 2 Y₁w with hDdef
  have hAO₂ : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₂ : Set G) :=
    hAY₂.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₂)
  have hAO₁ : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₁w : Set G) :=
    hY₁w.prop.1.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₁w)
  have hDQ : D ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le hO₂Q inf_le_left (Late.le_normalizer_inf hAO₂ hAO₁)
  have hD2 : IsPGroup 2 D :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₂).to_le inf_le_left
  have hED : E ≤ Subgroup.normalizer (D : Set G) :=
    Late.le_normalizer_inf (hEY₂.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₂))
      (hEY₁w.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₁w))
  have hED₂ : E ⊔ D ≤ Y₂ :=
    sup_le hEY₂ (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 Y₂))
  have hED₁ : E ⊔ D ≤ Y₁w :=
    sup_le hEY₁w (inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 Y₁w))
  have htop : E ⊔ D ≠ ⊤ := fun ht => hY₂4.1.1 (top_le_iff.mp (ht ▸ hED₂))
  have hX4 := mem_scriptY4_oRes_sup hE4 hDQ hED hY₂4 hED₂ hcovE
  have hXY : oPrimeResidualOf 3 (E ⊔ D) ≤ E ⊔ D := Subgroup.map_subtype_le _
  have hEX : E ≤ oPrimeResidualOf 3 (E ⊔ D) :=
    hE4.2.1.le.trans (oPrimeResidualOf_mono 3 le_sup_left)
  have hside : Y₂ = oPrimeResidualOf 3 (E ⊔ D) ⊔ CFSG.Open.pCoreOf 2 Y₂ :=
    le_antisymm (hcovE.trans (sup_le_sup_right hEX _))
      (sup_le (hXY.trans hED₂) (CFSG.LieType.BorelTits.pCoreOf_le 2 Y₂))
  have heq := eq_of_sup_side h155 h153 hE4 hDQ hD2 hD1 hED htop hX4 hY₁w hY₂ (hXY.trans hED₁)
    (hXY.trans hED₂) (hED₁.trans Subgroup.le_normalizer) (hED₂.trans Subgroup.le_normalizer) hside
  exact hnW ⟨w, hw, heq.symm⟩

theorem exists_inv_mul_mem_centralizer_of_card {A D : Subgroup G}
    (h9 : Nat.card (Sec4.autThetaQuot A D) = 9)
    (φD : ↥D ⧸ aschbacherSolvableCore 3 ↥D ≃* alternatingGroup (Fin 7))
    (hθ : aschbacherSolvableCore 3 ↥D = ⊥) {Sc : Subgroup G} (hSc2 : IsPGroup 2 Sc)
    (hAS : A ≤ Subgroup.normalizer (Sc : Set G)) (hSD : Sc ≤ Subgroup.normalizer (D : Set G))
    {s : G} (hs : s ∈ Sc) : ∃ l ∈ D, l⁻¹ * s ∈ Subgroup.centralizer (D : Set G) := by
  classical
  set N := Subgroup.normalizer (D : Set G) with hN
  set ρ : N →* Equiv.Perm (Fin 7) :=
    (Res162Five.autToPerm φD).comp ((Sec4.thetaQuotMulAut ↥D).comp D.normalizerMonoidHom)
    with hρ
  set E := (Sec4.autThetaQuot A D).map (Res162Five.autToPerm φD) with hE
  set P := (Sec4.autThetaQuot Sc D).map (Res162Five.autToPerm φD) with hP
  have hE9 : Nat.card E = 9 := by
    rw [hE, Subgroup.card_map_of_injective (Res162Five.autToPerm_injective φD)]
    exact h9
  have hP2 : IsPGroup 2 P := by
    have h1 : IsPGroup 2 ((Sc ⊓ N).subgroupOf N) :=
      (hSc2.to_le inf_le_left).comap_of_injective N.subtype N.subtype_injective
    exact ((h1.map D.normalizerMonoidHom).map (Sec4.thetaQuotMulAut ↥D)).map
      (Res162Five.autToPerm φD)
  have hEP : E ≤ Subgroup.normalizer (P : Set (Equiv.Perm (Fin 7))) := by
    intro e he
    obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp he
    obtain ⟨a, haN, haA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
    refine Subgroup.mem_normalizer_fintype fun p hp => ?_
    obtain ⟨τ', hτ', rfl⟩ := Subgroup.mem_map.mp hp
    obtain ⟨t, htN, htS, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ'
    have hatN : a * t * a⁻¹ ∈ N := mul_mem (mul_mem haN htN) (inv_mem haN)
    have hatS : a * t * a⁻¹ ∈ Sc := (Subgroup.mem_normalizer_iff.mp (hAS haA) t).mp htS
    refine Subgroup.mem_map.mpr ⟨_, Sec4.mem_autThetaQuot_iff.mpr ⟨a * t * a⁻¹, hatN, hatS, rfl⟩,
      ?_⟩
    have heq : (⟨a * t * a⁻¹, hatN⟩ : N) = ⟨a, haN⟩ * ⟨t, htN⟩ * (⟨a, haN⟩ : N)⁻¹ := rfl
    change ρ ⟨a * t * a⁻¹, hatN⟩ = ρ ⟨a, haN⟩ * ρ ⟨t, htN⟩ * (ρ ⟨a, haN⟩)⁻¹
    rw [heq, map_mul, map_mul, map_inv]
  have hPA := Res162Five.le_alternatingGroup_of_le_normalizer hP2 hE9 hEP
  have hsP : Res162Five.autToPerm φD
      (Sec4.thetaQuotMulAut ↥D (D.normalizerMonoidHom ⟨s, hSD hs⟩)) ∈ P :=
    Subgroup.mem_map_of_mem _ (Sec4.mem_autThetaQuot_iff.mpr ⟨s, hSD hs, hs, rfl⟩)
  obtain ⟨x, hx⟩ := Res162Five.exists_eq_conj_of_mem_alternatingGroup φD (hPA hsP)
  exact Res162Five.exists_inv_mul_mem_centralizer hθ (hSD hs) hx

theorem inf_pCoreOf_eq_bot_of_free {b : G} {Lb Y₂ S : Subgroup G}
    (hLbC : Lb ≤ Subgroup.centralizer ({b} : Set G))
    (hSY₂ : S ≤ Subgroup.normalizer (Y₂ : Set G))
    (hfree : CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) ⊓
      Subgroup.normalizer (Subgroup.zpowers b : Set G) = ⊥) :
    (Y₂ ⊓ Lb) ⊓ CFSG.Open.pCoreOf 2 Y₂ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : CFSG.Open.pCoreOf 2 Y₂ ≤ CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y₂).trans le_sup_left)
      ((sup_le Subgroup.le_normalizer hSY₂).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₂))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₂)
  rw [eq_bot_iff, ← hfree]
  exact le_inf (inf_le_right.trans hO) (inf_le_left.trans (inf_le_right.trans
    (hLbC.trans (centralizer_singleton_le_normalizer_zpowers b))))

theorem centralizer_le_inf_of_free {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (h155 : Item155 A (lB A)) (h153 : Item153Main A (lB A))
    (hW : ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
      TransOn A (lB A) (Subgroup.normalizer (A : Set G)) Y)
    (h142 : Concl142 A (lB A)) {Y₁ Y₂ S : Subgroup G} (hmax : MaxCE162 A (lB A) Y₁ Y₂ S S)
    (hLY₁ : L ≤ Y₁) (hT : TransOmegaThree A c)
    (hnW : ¬ ∃ g ∈ Subgroup.normalizer (A : Set G), Y₂ = Y₁.map (MulAut.conj g).toMonoidHom)
    (hch : Choice162 A c S) {b : G} {Lb : Subgroup G} (hb : Subgroup.zpowers b ∈ omegaA A)
    (hLb : Lb ∈ lA A b) (hm₂ : MeetsY4 A (lB A) Lb Y₂)
    (φ₂ : ↥Y₂ ⧸ CFSG.pCore 2 ↥Y₂ ≃* alternatingGroup (Fin 7))
    (hsc : Late.sectionCentralizer A Y₂ (CFSG.Open.pCoreOf 2 Y₂) = (Subgroup.zpowers b : Set G))
    (hfree : CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) ⊓
      Subgroup.normalizer (Subgroup.zpowers b : Set G) = ⊥) :
    S ⊓ Subgroup.centralizer ({b} : Set G) ≤ Y₂ ⊓ Lb := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  have hb' : Sec15R G A b Lb := sec15R_of_point h hb hLb
  have hY₁ := hmax.1.mem₁
  have hY₂ := hmax.1.mem₂
  have hY₂4 : Y₂ ∈ scriptY4 A (lB A) := hY₂.prop.1
  have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp hb).1
  have hb3 : Nat.card (Subgroup.zpowers b) = 3 := (zpowers_mem_omegaA_iff.mp hb).2.1
  have hb1 : b ≠ 1 := by
    intro h1
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hb3
    omega
  set Hb := Subgroup.normalizer (Subgroup.zpowers b : Set G) with hHb
  have hCb : Subgroup.centralizer ({b} : Set G) ≤ Hb :=
    centralizer_singleton_le_normalizer_zpowers b
  have hLbC : Lb ≤ Subgroup.centralizer ({b} : Set G) := hb'.toSec13Data.le_centralizer
  have hHbL : Hb ≤ Subgroup.normalizer (Lb : Set G) :=
    normalizer_zpowers_le_normalizer_L hb' (three_dvd_card_of_mem_lA h hb hLb)
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute ha hbA)
  have hAY₂ : A ≤ Subgroup.normalizer (Y₂ : Set G) := hY₂.prop.1.1.2
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hmax.1.s₂.prop.1.1.1.2.2
  have hSY₂ : S ≤ Subgroup.normalizer (Y₂ : Set G) := hmax.1.s₂.prop.1.2
  have hAO₂ : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₂ : Set G) :=
    hAY₂.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₂)
  set Q := S ⊓ Subgroup.centralizer ({b} : Set G) with hQdef
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hmax.1.s₂.prop
  have hQ2 : IsPGroup 2 Q := hS2.to_le inf_le_left
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) :=
    Late.le_normalizer_inf hAS (hAb.trans Subgroup.le_normalizer)
  have hQ3 : ¬ 3 ∣ Nat.card Q := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ2
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hQH : Q ≤ Hb := inf_le_right.trans hCb
  have hQQ : Q ∈ scriptQ A (lB A) := mem_scriptQ_of_concl142 h142 hb
    ⟨hQH, (isPiSubgroup_piCompl_iff Nat.prime_three Q).mpr hQ3, hAQ⟩
  set D := Y₂ ⊓ Lb with hDdef
  have hDO := inf_pCoreOf_eq_bot_of_free hLbC hSY₂ hfree
  have hcovY₂ : Y₂ = D ⊔ CFSG.Open.pCoreOf 2 Y₂ := by
    have hcov := Res162b.eq_top_of_seven hb' hY₂ hm₂ φ₂
    refine Res162.eq_sup_of_forall_mem fun y hy => ?_
    obtain ⟨d, hd, hdy⟩ := hcov y hy
    exact ⟨d, ⟨hd.2, hd.1⟩, hdy⟩
  have hDY₂ : D ≤ Y₂ := inf_le_left
  have hDLb : D ≤ Lb := inf_le_right
  have hDN : D ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₂ : Set G) :=
    hDY₂.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₂)
  set P2 := CFSG.pCore 2 ↥Y₂ with hP2def
  set ψ : ↥D →* ↥Y₂ ⧸ P2 := (QuotientGroup.mk' P2).comp (Subgroup.inclusion hDY₂) with hψdef
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro d hd
    have h1 : Subgroup.inclusion hDY₂ d ∈ P2 := by
      have := MonoidHom.mem_ker.mp hd
      rwa [hψdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at this
    have h2 : (d : G) ∈ CFSG.Open.pCoreOf 2 Y₂ := by
      have h' : Subgroup.inclusion hDY₂ d ∈ CFSG.Open.pCore 2 ↥Y₂ := by
        exact h1
      exact Subgroup.mem_map_of_mem Y₂.subtype h'
    have h3 : (d : G) ∈ D ⊓ CFSG.Open.pCoreOf 2 Y₂ := ⟨d.2, h2⟩
    rw [hDO, Subgroup.mem_bot] at h3
    exact Subgroup.mem_bot.mpr (Subtype.ext h3)
  have hψsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective P2 q
    have hy : (y : G) ∈ ((D ⊔ CFSG.Open.pCoreOf 2 Y₂ : Subgroup G) : Set G) := by
      rw [← hcovY₂]
      exact y.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right D _ hDN] at hy
    obtain ⟨d, hd, o, ho, hdo⟩ := hy
    obtain ⟨o', ho', rfl⟩ := Subgroup.mem_map.mp
      (show o ∈ (CFSG.Open.pCore 2 ↥Y₂).map Y₂.subtype from ho)
    have ho'P : o' ∈ P2 := by rwa [hP2def]
    have hy' : y = Subgroup.inclusion hDY₂ ⟨d, hd⟩ * o' := Subtype.ext hdo.symm
    have h1 : QuotientGroup.mk' P2 o' = 1 := (QuotientGroup.eq_one_iff o').mpr ho'P
    refine ⟨⟨d, hd⟩, ?_⟩
    rw [hy', map_mul, h1, mul_one]
    try rfl
  set ψD : ↥D ≃* alternatingGroup (Fin 7) :=
    (MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩).trans φ₂ with hψDdef
  have hθ : aschbacherSolvableCore 3 ↥D = ⊥ :=
    Res162b.eq_bot_of_normal_of_isSolvable_a7 ψD _
      (solvable_prime_complement_core_characterization (H := ↥D) Nat.prime_three).1
  set φD : ↥D ⧸ aschbacherSolvableCore 3 ↥D ≃* alternatingGroup (Fin 7) :=
    ((QuotientGroup.quotientMulEquivOfEq hθ).trans QuotientGroup.quotientBot).trans ψD
    with hφDdef
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := Late.le_normalizer_inf hAY₂ hLb.2.1
  have hsecD : Late.sectionCentralizer A D ((aschbacherSolvableCore 3 ↥D).map D.subtype) =
      (Subgroup.zpowers b : Set G) := by
    rw [hθ, Subgroup.map_bot, ← hsc]
    ext a
    constructor
    · rintro ⟨haA, ha⟩
      refine ⟨haA, fun y hy => ?_⟩
      have hy' : y ∈ ((D ⊔ CFSG.Open.pCoreOf 2 Y₂ : Subgroup G) : Set G) := by
        rw [← hcovY₂]
        exact hy
      rw [Subgroup.coe_mul_of_left_le_normalizer_right D _ hDN] at hy'
      obtain ⟨d, hd, o, ho, rfl⟩ := hy'
      have had : a * d * a⁻¹ * d⁻¹ = 1 := Subgroup.mem_bot.mp (ha d hd)
      have had' : a * d = d * a := by
        calc a * d = a * d * a⁻¹ * d⁻¹ * (d * a) := by group
          _ = d * a := by rw [had, one_mul]
      have hao : a * o * a⁻¹ * o⁻¹ ∈ CFSG.Open.pCoreOf 2 Y₂ :=
        mul_mem ((Subgroup.mem_normalizer_iff.mp (hAO₂ haA) o).mp ho) (inv_mem ho)
      have e : a * (d * o) * a⁻¹ * (d * o)⁻¹ = d * (a * o * a⁻¹ * o⁻¹) * d⁻¹ := by
        calc a * (d * o) * a⁻¹ * (d * o)⁻¹ = (a * d) * o * a⁻¹ * o⁻¹ * d⁻¹ := by group
          _ = (d * a) * o * a⁻¹ * o⁻¹ * d⁻¹ := by rw [had']
          _ = d * (a * o * a⁻¹ * o⁻¹) * d⁻¹ := by group
      show a * (d * o) * a⁻¹ * (d * o)⁻¹ ∈ CFSG.Open.pCoreOf 2 Y₂
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hDN hd) _).mp hao
    · intro ha
      have hab : a ∈ Subgroup.zpowers b := by
        rw [← SetLike.mem_coe, ← hsc]
        exact ha
      refine ⟨ha.1, fun x hx => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hab
      have hxb : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.mp (hLbC (hDLb hx))
      have hc : Commute (b ^ k) x := (Commute.zpow_left hxb.symm k)
      rw [Subgroup.mem_bot, hc.eq, mul_inv_cancel_right, mul_inv_cancel]
  have h9 : Nat.card (Sec4.autThetaQuot A D) = 9 := by
    have hcard := card_inf_mul_card_autThetaQuot hAD
    rw [sectionCentralizer_eq_inf hAD] at hsecD
    have heq : A ⊓ Sec4.thetaQuotCentralizer D = Subgroup.zpowers b :=
      SetLike.coe_injective hsecD
    rw [heq, hb3, hD.card_eq] at hcard
    omega
  have hQD : Q ≤ Subgroup.normalizer (D : Set G) :=
    Late.le_normalizer_inf (inf_le_left.trans hSY₂) (hQH.trans hHbL)
  have hinner : ∀ s ∈ Q, ∃ l ∈ D, l⁻¹ * s ∈ Subgroup.centralizer (D : Set G) := fun s hs =>
    exists_inv_mul_mem_centralizer_of_card h9 φD hθ hQ2 hAQ hQD hs
  have hZ := Res162Five.inf_centralizer_eq_bot hθ φD
  set RQ := Subgroup.centralizer (D : Set G) ⊓ (Q ⊔ D) with hRQdef
  have hRQ2 : IsPGroup 2 RQ := by
    intro r
    have hrS : (r : G) ∈ ((Q ⊔ D : Subgroup G) : Set G) := (Subgroup.mem_inf.mp r.2).2
    have hrC : (r : G) ∈ Subgroup.centralizer (D : Set G) := (Subgroup.mem_inf.mp r.2).1
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Q D hQD] at hrS
    obtain ⟨s, hs, l, hl, hsl⟩ := hrS
    obtain ⟨k, hk⟩ := hQ2 ⟨s, hs⟩
    have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcomm : Commute (r : G) l⁻¹ :=
      (show Commute (r : G) l from (Subgroup.mem_centralizer_iff.mp hrC l hl).symm).inv_right
    have hs' : s = (r : G) * l⁻¹ := by rw [← hsl]; group
    have h1 : (r : G) ^ 2 ^ k = l ^ 2 ^ k := by
      rw [hs', hcomm.mul_pow, inv_pow, mul_inv_eq_one] at hk'
      exact hk'
    have h2 : (r : G) ^ 2 ^ k ∈ D ⊓ Subgroup.centralizer (D : Set G) :=
      ⟨h1 ▸ pow_mem hl _, pow_mem hrC _⟩
    rw [hZ, Subgroup.mem_bot] at h2
    exact ⟨k, Subtype.ext (by simpa using h2)⟩
  have hAR : A ≤ Subgroup.normalizer (RQ : Set G) :=
    Late.le_normalizer_inf (hAD.trans (Res162d.normalizer_le_normalizer_centralizer' D))
      (le_normalizer_sup hAQ hAD)
  have hQDH : Q ⊔ D ≤ Hb := sup_le hQH ((hDLb.trans hLbC).trans hCb)
  have hRQ3 : ¬ 3 ∣ Nat.card RQ := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hRQ2
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hRQQ : RQ ∈ scriptQ A (lB A) := mem_scriptQ_of_concl142 h142 hb
    ⟨inf_le_right.trans hQDH, (isPiSubgroup_piCompl_iff Nat.prime_three RQ).mpr hRQ3, hAR⟩
  have hRQ1 : RQ = ⊥ := by
    by_contra hRQ1
    set E := oPrimeResidualOf 3 D with hE
    have hED' : E ≤ D := Subgroup.map_subtype_le _
    have hEY₂ : E ≤ Y₂ := hED'.trans hDY₂
    have hELb : E ≤ Lb := hED'.trans hDLb
    have hcovE : Y₂ ≤ E ⊔ CFSG.Open.pCoreOf 2 Y₂ :=
      Proof1515Res.le_oRes3_sup hY₂4.2.1 inf_le_left (CFSG.LieType.BorelTits.pCoreOf_le 2 Y₂)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₂) hcovY₂.le
    have hAE : A ≤ Subgroup.normalizer (E : Set G) := Proof1515Res.le_normalizer_oRes3 hAD
    have hmemE : ∀ R' : Subgroup G, R' ≤ E → ¬ 3 ∣ Nat.card R' →
        A ≤ Subgroup.normalizer (R' : Set G) → R' ∈ scriptQ A (lB A) :=
      fun R' hR'E hR'3 hAR' => mem_scriptQ_of_concl142 h142 hb
        ⟨(hR'E.trans (hELb.trans hLbC)).trans hCb,
          (isPiSubgroup_piCompl_iff Nat.prime_three R').mpr hR'3, hAR'⟩
    have hE4 : E ∈ scriptY4 A (lB A) := Proof1515Res.mem_scriptY4_of_le_cover hY₂4 hEY₂ hcovE
      hAE (Proof1515Res.oRes3_idem D).symm hmemE
    obtain ⟨g, hg, hbg⟩ := hT.2 _ hb
    have hLg : L.map (MulAut.conj g).toMonoidHom = Lb :=
      map_conj_eq_of_zpowers hb' h.zpowers_mem_omegaA h.mem_lA hg hbg
    have hSb : (S ⊓ Subgroup.centralizer ({c} : Set G)).map (MulAut.conj g).toMonoidHom ∈
        scriptQPiStar A (lB A) Hb (piOf 2) := by
      have h1 := Sec17.HeadProof.map_conj_mem_scriptQPiStar hg hch
      rwa [Subgroup.map_equiv_normalizer_eq, ← hbg] at h1
    have hQmem : Q ∈ scriptQPi A (lB A) Hb (piOf 2) :=
      ⟨⟨hQQ, hQH⟩, (isPiSubgroup_piOf_iff Nat.prime_two Q).mpr hQ2⟩
    obtain ⟨Q', hQQ', hQ'⟩ := Finite.exists_le_maximal
      (p := (· ∈ scriptQPi A (lB A) Hb (piOf 2))) hQmem
    set Dl := delta A (lB A) Hb with hDl
    have hEDl : E ≤ Dl := hE4.2.2.1.le.trans (delta_mono (hELb.trans (hLbC.trans hCb)))
    have hDlC : Dl ≤ Subgroup.centralizer ({b} : Set G) :=
      sSup_le fun Q₀ hQ₀ => le_centralizer_of_le_normalizer_zpowers h.toSec14Std.isE27 hbA hQ₀.1
        hQ₀.2
    have hDlY : Dl ∈ scriptY A :=
      ⟨fun htop => Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp hb1
        (top_le_iff.mp (htop ▸ hDlC)), le_normalizer_sSup fun Q₀ hQ₀ => hQ₀.1.1.2.2⟩
    have hDlΔ : Dl = delta A (lB A) Dl := (delta_delta _).symm
    have hDlsol : ¬ Group.IsSolvable ↥Dl := fun hs => by
      have := hs
      exact Proof162.not_isSolvable_of_mem_scriptY4 hE4
        (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hEDl))
    have htr := hW Dl hDlΔ hDlY hDlsol
    have hSbD : (S ⊓ Subgroup.centralizer ({c} : Set G)).map (MulAut.conj g).toMonoidHom ∈
        scriptQPiStar A (lB A) Dl (piOf 2) := by
      rw [hDl, scriptQPiStar_delta]
      exact hSb
    have hQ'D : Q' ∈ scriptQPiStar A (lB A) Dl (piOf 2) := by
      rw [hDl, scriptQPiStar_delta]
      exact hQ'
    obtain ⟨x, hx, hxQ'⟩ := htr _ hSbD _ hQ'D
    have hxW : x ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp hx).1
    have hxHb : x ∈ Hb := delta_le Hb (Subgroup.mem_inf.mp hx).2
    set w := x * g with hw
    have hwW : w ∈ Subgroup.normalizer (A : Set G) := mul_mem hxW hg
    have hQSw : Q ≤ S.map (MulAut.conj w).toMonoidHom := by
      refine hQQ'.trans ?_
      rw [hxQ', Late.map_conj_map_conj]
      exact Subgroup.map_mono inf_le_left
    have hLw : L.map (MulAut.conj w).toMonoidHom = Lb := by
      rw [hw, ← Late.map_conj_map_conj, hLg, Late.map_conj_eq_of_mem_normalizer (hHbL hxHb)]
    set Y₁w := Y₁.map (MulAut.conj w).toMonoidHom with hY₁wdef
    have hY₁w : Y₁w ∈ scriptY0Star A (lB A) := map_conj_mem_scriptY0Star hwW hY₁
    have hLbY₁w : Lb ≤ Y₁w := hLw ▸ Subgroup.map_mono hLY₁
    have hSwN : S.map (MulAut.conj w).toMonoidHom ≤ Subgroup.normalizer (Y₁w : Set G) := by
      rw [hY₁wdef, ← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono hmax.1.s₁.prop.1.2
    have hRE : RQ ≤ Subgroup.normalizer (E : Set G) :=
      (inf_le_left.trans (Subgroup.centralizer_le hED')).trans
        (Subgroup.centralizer_le_normalizer _)
    have hER : E ≤ Subgroup.normalizer (RQ : Set G) :=
      (Subgroup.le_centralizer_iff.mp ((inf_le_left :
        RQ ≤ Subgroup.centralizer (D : Set G)).trans (Subgroup.centralizer_le hED'))).trans
        (Subgroup.centralizer_le_normalizer _)
    have hres : oPrimeResidualOf 3 (E ⊔ RQ) = E :=
      ((oPrimeResidualOf_eq_of_le le_sup_left fun z hz k hk =>
        mem_of_pow_three_of_mem_sup hRE hRQ2 hz hk).symm.trans hE4.2.1.symm)
    have hX4 : oPrimeResidualOf 3 (E ⊔ RQ) ∈ scriptY4 A (lB A) := by
      rw [hres]
      exact hE4
    have hERC : E ⊔ RQ ≤ Subgroup.centralizer ({b} : Set G) :=
      sup_le (hELb.trans hLbC) (inf_le_right.trans (sup_le inf_le_right (hDLb.trans hLbC)))
    have htop : E ⊔ RQ ≠ ⊤ := fun ht =>
      Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp hb1 (top_le_iff.mp (ht ▸ hERC))
    have hRQN₂ : RQ ≤ Subgroup.normalizer (Y₂ : Set G) :=
      inf_le_right.trans (sup_le (inf_le_left.trans hSY₂) (hDY₂.trans Subgroup.le_normalizer))
    have hRQN₁ : RQ ≤ Subgroup.normalizer (Y₁w : Set G) :=
      inf_le_right.trans (sup_le (hQSw.trans hSwN)
        ((hDLb.trans hLbY₁w).trans Subgroup.le_normalizer))
    have hXK₁ : oPrimeResidualOf 3 (E ⊔ RQ) ≤ Y₁w := by
      rw [hres]
      exact hELb.trans hLbY₁w
    have hXK₂ : oPrimeResidualOf 3 (E ⊔ RQ) ≤ Y₂ := by
      rw [hres]
      exact hEY₂
    have hside : Y₂ = oPrimeResidualOf 3 (E ⊔ RQ) ⊔ CFSG.Open.pCoreOf 2 Y₂ := by
      rw [hres]
      exact le_antisymm hcovE (sup_le hEY₂ (CFSG.LieType.BorelTits.pCoreOf_le 2 Y₂))
    have heq := eq_of_sup_side h155 h153 hE4 hRQQ hRQ2 hRQ1 hER htop hX4 hY₁w hY₂ hXK₁ hXK₂
      (sup_le ((hELb.trans hLbY₁w).trans Subgroup.le_normalizer) hRQN₁)
      (sup_le (hEY₂.trans Subgroup.le_normalizer) hRQN₂) hside
    exact hnW ⟨w, hwW, heq.symm⟩
  intro s hs
  obtain ⟨l, hl, hls⟩ := hinner s hs
  have hz : l⁻¹ * s ∈ RQ :=
    ⟨hls, mul_mem (Subgroup.mem_sup_right (inv_mem hl)) (Subgroup.mem_sup_left hs)⟩
  rw [hRQ1, Subgroup.mem_bot, inv_mul_eq_one] at hz
  exact hz ▸ hl

end Res162Six

theorem step162A7OtherFree_of_meet (h155 : Item155R) (h153 : Item153MainR)
    (hWloc : Claim1411NonsolvWR) (h1444 : Item1444S14) (h146 : Item146S14)
    (hbot : Item145BotS14) (h142 : Concl142S14) (hM : Step162A7OtherFreeMeet) :
    Step162A7OtherFree := by
  intro G _ _ A c L h Y₁ Y₂ S hmax hLY₁ hm₁ h7 hW4 hT hY₁7 hnW hch b Lb hb hLb hbc hm₂ hY₂7 hsc
    hfree
  obtain ⟨φ₂⟩ := hY₂7
  have hb' : Sec15R G A b Lb := sec15R_of_point h hb hLb
  have h14b := hb'.toSec14Std
  refine hM G A c L h Y₁ Y₂ S hmax hLY₁ hm₁ h7 hW4 hT hY₁7 hnW hch b Lb hb hLb hbc hm₂ ⟨φ₂⟩ hsc
    hfree (Res162Six.inf_pCoreOf_eq_bot_of_free hb'.toSec13Data.le_centralizer
      hmax.1.s₂.prop.1.2 hfree)
    (Res162Six.centralizer_le_inf_of_free h (h155 G A c L h) (h153 G A c L h) (hWloc G A c L h)
      (h142 G A c L h.toSec14Std) hmax hLY₁ hT hnW hch hb hLb hm₂ φ₂ hsc hfree)
    fun w hw hbw => ?_
  exact Res162Six.pCoreOf_inf_conj_eq_bot h (h155 G A c L h) (h153 G A c L h)
    (h142 G A c L h.toSec14Std) hb hLb (h1444 G A b Lb h14b) (h146 G A b Lb h14b)
    (hbot G A b Lb h14b) hmax.1.mem₁ hmax.1.mem₂ hLY₁ hm₂ φ₂ hnW hw hbw

end CFSG.RankThree.PartTwo.Sec16
