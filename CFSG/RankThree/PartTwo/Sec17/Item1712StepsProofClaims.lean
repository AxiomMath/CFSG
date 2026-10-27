module

public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProof
public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofTwenty
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
import CFSG.RankThree.PartTwo.Sec17.Item1712StepsProofSeven
public import CFSG.RankThree.PartTwo.Sec14.Item1411Strong

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17.HeadProof
open scoped commutatorElement

@[expose] def Claim17Q0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → CFSG.Open.pCoreOf 2 Y₀ ∈ scriptQ A (lB A)

namespace Proof1712

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G}
  {p : ℕ} {P : Subgroup G}

theorem mem_qStar_top (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (h166 : Item166 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h168 : Item168 A (lB A) c L) :
    S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) :=
  mem_qStar_top_of_item168 h.toSec17Std h166 hbot h168 h.mem_y1Star.prop.1 h.not_le_M
    (fun _ hN hYN => le_antisymm (h.mem_y1Star.2 hN hYN) hYN) h.mem_qStar_two

theorem pCoreOf_le_of_mem_scriptQ (h : Sec17Std G A c L Y₀) (h146 : Item146 A (lB A))
    (hSG : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2))
    (hK : CFSG.Open.pCoreOf 2 Y₀ ∈ scriptQ A (lB A)) : CFSG.Open.pCoreOf 2 Y₀ ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := CFSG.Open.pCoreOf 2 Y₀ with hKdef
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hSG.prop.2
  have hK2 : IsPGroup 2 K := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₀
  have hSK : S ≤ Subgroup.normalizer (K : Set G) :=
    (h.qStar_le S hSG).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀)
  set Z := S ⊔ K with hZ
  have hZ2 : IsPGroup 2 Z := IsPGroup.to_sup_of_normal_right' hS2 hK2 hSK
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_sup hSG.prop.1.1.1.2.2 hK.1.2.2
  have hZ3 : IsPiSubgroup (piCompl 3) Z := (isPiSubgroup_piCompl_iff Nat.prime_three Z).mpr
    fun h3 => by
      rcases hZ2.card_eq_or_dvd with h1 | h2
      · rw [h1] at h3
        omega
      · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ2
        rw [hk] at h3
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
          (Nat.prime_three.dvd_of_dvd_pow h3)
        omega
  have hΔZ : delta A (lB A) Z ∈ scriptQ A (lB A) :=
    delta_mem_scriptQ (isE27_of_std h) h146 ⟨le_top, hZ3, hAZ⟩
  have hSΔ : S ≤ delta A (lB A) Z := le_delta hSG.prop.1.1 le_sup_left
  have hKΔ : K ≤ delta A (lB A) Z := le_delta hK le_sup_right
  have hΔ2 : delta A (lB A) Z ∈ scriptQPi A (lB A) ⊤ (piOf 2) :=
    ⟨⟨hΔZ, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr (hZ2.to_le (delta_le Z))⟩
  exact hKΔ.trans (hSG.2 hΔ2 hSΔ)

omit [Finite G] in
theorem eq_of_imgY0_eq {X X' : Subgroup G} [(kerAO2 A Y₀).Normal] (hX : X ≤ A ⊔ Y₀)
    (hX' : X' ≤ A ⊔ Y₀) (hKX : CFSG.Open.pCoreOf 2 Y₀ ≤ X) (hKX' : CFSG.Open.pCoreOf 2 Y₀ ≤ X')
    (h : imgY0 A Y₀ X = imgY0 A Y₀ X') : X = X' := by
  have hk : ∀ {Z : Subgroup G}, CFSG.Open.pCoreOf 2 Y₀ ≤ Z →
      (QuotientGroup.mk' (kerAO2 A Y₀)).ker ≤ Z.subgroupOf (A ⊔ Y₀) := by
    intro Z hZ x hx
    rw [QuotientGroup.ker_mk'] at hx
    exact Subgroup.mem_subgroupOf.mpr (hZ (Subgroup.mem_subgroupOf.mp hx))
  have e1 := Subgroup.comap_map_eq (QuotientGroup.mk' (kerAO2 A Y₀)) (X.subgroupOf (A ⊔ Y₀))
  have e2 := Subgroup.comap_map_eq (QuotientGroup.mk' (kerAO2 A Y₀)) (X'.subgroupOf (A ⊔ Y₀))
  rw [sup_eq_left.mpr (hk hKX)] at e1
  rw [sup_eq_left.mpr (hk hKX')] at e2
  have h1 : X.subgroupOf (A ⊔ Y₀) = X'.subgroupOf (A ⊔ Y₀) := by
    rw [← e1, ← e2]
    exact congrArg (Subgroup.comap (QuotientGroup.mk' (kerAO2 A Y₀))) h
  rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hX, inf_eq_left.mpr hX'] at h1
  exact h1

omit [Finite G] in
theorem imgY0_sup {X X' : Subgroup G} [(kerAO2 A Y₀).Normal] (hX : X ≤ A ⊔ Y₀)
    (hX' : X' ≤ A ⊔ Y₀) : imgY0 A Y₀ (X ⊔ X') = imgY0 A Y₀ X ⊔ imgY0 A Y₀ X' := by
  simp only [imgY0]
  rw [Subgroup.subgroupOf_sup hX hX', Subgroup.map_sup]

omit [Finite G] in
theorem card_imgY0_dvd {X : Subgroup G} [(kerAO2 A Y₀).Normal] (hX : X ≤ A ⊔ Y₀) :
    Nat.card (imgY0 A Y₀ X) ∣ Nat.card X := by
  simp only [imgY0]
  refine (Subgroup.card_map_dvd _ _).trans ?_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv]

theorem x1720_facts (h : Sec17Y1 G A c L Y₀ Y₁ S p P) :
    A ≤ Subgroup.normalizer ((x1720 A Y₀ S L : Subgroup G) : Set G) ∧
      x1720 A Y₀ S L = delta A (lB A) (x1720 A Y₀ S L) := by
  have hSQ : S ∈ scriptQ A (lB A) := h.mem_qStar_two.prop.1.1
  have hASL : A ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hSQ.1.2.2 h.toSec13Data.le_normalizer
  have hAD : A ≤ Subgroup.normalizer ((delta A (lB A) (cQuot Y₀) : Subgroup G) : Set G) :=
    le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  refine ⟨le_normalizer_sup hAD hASL, le_antisymm (sup_le ?_ ?_) (delta_le _)⟩
  · calc delta A (lB A) (cQuot Y₀) = delta A (lB A) (delta A (lB A) (cQuot Y₀)) :=
          (delta_delta _).symm
      _ ≤ delta A (lB A) (x1720 A Y₀ S L) := delta_mono le_sup_left
  · exact le_delta (mem_scriptQ_of_le hSQ inf_le_left hASL) le_sup_right

omit [Finite G] in
theorem inf_sup_le_of_le {S L K : Subgroup G} (hKS : K ≤ S)
    (hLK : L ≤ Subgroup.normalizer (K : Set G)) : S ⊓ (L ⊔ K) ≤ (S ⊓ L) ⊔ K := by
  rintro x ⟨hxS, hxLK⟩
  have hx' : x ∈ ((L ⊔ K : Subgroup G) : Set G) := hxLK
  rw [Subgroup.coe_mul_of_left_le_normalizer_right L K hLK] at hx'
  obtain ⟨l, hl, k, hk, rfl⟩ := hx'
  have hlS : l ∈ S := by
    have := S.mul_mem hxS (S.inv_mem (hKS hk))
    rwa [mul_inv_cancel_right] at this
  exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hlS, hl⟩) hk

omit [Finite G] in
theorem pCoreOf_le_cQuot (Y₀ : Subgroup G) : CFSG.Open.pCoreOf 2 Y₀ ≤ cQuot Y₀ := by
  intro k hk
  rw [← SetLike.mem_coe, coe_cQuot]
  have hkY : k ∈ Y₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀ hk
  refine ⟨Subgroup.le_normalizer hkY, fun y hy => ?_⟩
  have hyN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀ hy
  have h1 : y * k⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y₀ :=
    (Subgroup.mem_normalizer_iff.mp hyN _).mp (inv_mem hk)
  have e : k * y * k⁻¹ * y⁻¹ = k * (y * k⁻¹ * y⁻¹) := by group
  rw [e]
  exact mul_mem hk h1

theorem exists_mem_inf_centralizer_of_dvd {p : ℕ} [Fact p.Prime] {P D : Subgroup G}
    (hP : IsPGroup p P) (hPD : P ≤ Subgroup.normalizer (D : Set G)) (hpD : p ∣ Nat.card D) :
    ∃ z ∈ D ⊓ Subgroup.centralizer (P : Set G), orderOf z = p := by
  let _ : MulDistribMulAction P D := Subgroup.conjMulDistribMulActionOfLeNormalizer P D hPD
  have hsmul : ∀ (a : P) (d : D), ((a • d : D) : G) = (a : G) * d * (a : G)⁻¹ := fun _ _ => rfl
  have hfix : p ∣ Nat.card (MulAction.fixedPoints P D) :=
    Nat.modEq_zero_iff_dvd.mp ((hP.card_modEq_card_fixedPoints D).symm.trans
      hpD.modEq_zero_nat)
  have e : MulAction.fixedPoints P D ≃ ↥(D ⊓ Subgroup.centralizer (P : Set G)) :=
    { toFun := fun d => ⟨(d.1 : G), d.1.2, Subgroup.mem_centralizer_iff.mpr fun a ha => by
        have h' := congrArg Subtype.val (d.2 ⟨a, ha⟩)
        rw [hsmul] at h'
        calc a * (d.1 : G) = a * d.1 * a⁻¹ * a := by group
          _ = d.1 * a := by rw [h']⟩
      invFun := fun z => ⟨⟨z, z.2.1⟩, fun a => Subtype.ext (by
        rw [hsmul]
        have hz := Subgroup.mem_centralizer_iff.mp z.2.2 a a.2
        change (a : G) * z * (a : G)⁻¹ = z
        rw [hz, mul_inv_cancel_right])⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hdvd : p ∣ Nat.card ↥(D ⊓ Subgroup.centralizer (P : Set G)) := by
    rwa [← Nat.card_congr e]
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  exact ⟨z, z.2, by rw [Subgroup.orderOf_coe]; exact hz⟩

omit [Finite G] in
theorem inf_cQuot_le_of_alternating_ten {Y₀ : Subgroup G}
    (φ : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 10)) :
    Y₀ ⊓ cQuot Y₀ ≤ CFSG.Open.pCoreOf 2 Y₀ := by
  intro z hz
  obtain ⟨hzY, hzC⟩ := Subgroup.mem_inf.mp hz
  rw [← SetLike.mem_coe, coe_cQuot] at hzC
  obtain ⟨hzN, hz⟩ := hzC
  refine Step163Alt.mem_pCoreOf_of_mem_centralizerSection (Step163Alt.center_eq_bot_of_ten φ) hzY
    ⟨hzN, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀ hzN, fun k hk => ?_⟩
  have e : ⁅k, z⁆ = (z * k * z⁻¹ * k⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact inv_mem (hz k hk)

end Proof1712

@[expose] noncomputable def Claim1718Quot : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (h : Sec17Y1 G A c L Y₀ Y₁ S p P),
    letI := kerAO2_normal h.le_normalizer_y0
    ∀ w ∈ Subgroup.normalizer (A : Set G) ⊓ Y₀,
      imgY0 A Y₀ ((S ⊓ Y₀).map (MulAut.conj w).toMonoidHom) ≠ imgY0 A Y₀ (S ⊓ Y₀) →
        3 ∣ Nat.card ↥(imgY0 A Y₀ (S ⊓ Y₀) ⊔
          imgY0 A Y₀ ((S ⊓ Y₀).map (MulAut.conj w).toMonoidHom))

theorem claim1718_of (hQ : Claim1718Quot) (hQ0 : Claim17Q0) (h146 : Item146S14)
    (h166 : Item166S17) (hbot : Item145BotS17) (h168 : Item168S17) : Claim1718 := by
  intro G _ _ A c L Y₀ Y₁ S p P h w hw hwS
  have hs := h.toSec17Std
  have : (kerAO2 A Y₀).Normal := kerAO2_normal h.le_normalizer_y0
  have hSG := Proof1712.mem_qStar_top h (h166 G A c L Y₀ hs) (hbot G A c L Y₀ hs)
    (h168 G A c L Y₀ hs)
  have hKS := Proof1712.pCoreOf_le_of_mem_scriptQ hs (h146 G A c L hs.toSec14Std) hSG
    (hQ0 G A c L Y₀ hs)
  set K := CFSG.Open.pCoreOf 2 Y₀ with hKdef
  set T := S ⊓ Y₀ with hT
  set T' := T.map (MulAut.conj w).toMonoidHom with hT'
  have hwY : w ∈ Y₀ := (Subgroup.mem_inf.mp hw).2
  have hTN : T ≤ A ⊔ Y₀ := inf_le_right.trans le_sup_right
  have hT'Y : T' ≤ Y₀ :=
    calc T' ≤ Y₀.map (MulAut.conj w).toMonoidHom := Subgroup.map_mono inf_le_right
      _ = Y₀ := Late.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hwY)
  have hT'N : T' ≤ A ⊔ Y₀ := hT'Y.trans le_sup_right
  have hKT : K ≤ T := le_inf hKS (CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀)
  have hKT' : K ≤ T' :=
    calc K = K.map (MulAut.conj w).toMonoidHom :=
          (Late.map_conj_eq_of_mem_normalizer
            (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀ hwY)).symm
      _ ≤ T' := Subgroup.map_mono hKT
  have hne : imgY0 A Y₀ T' ≠ imgY0 A Y₀ T := fun heq =>
    hwS (Sec14.mem_normalizer_of_map_conj_eq (Proof1712.eq_of_imgY0_eq hT'N hTN hKT' hKT heq))
  have h3 := hQ G A c L Y₀ Y₁ S p P h w hw hne
  rw [← Proof1712.imgY0_sup hTN hT'N] at h3
  have h3' : 3 ∣ Nat.card ↥(T ⊔ T') := h3.trans (Proof1712.card_imgY0_dvd (sup_le hTN hT'N))
  exact fun hbot' => not_three_dvd_of_oPrimeResidualOf_eq_bot' hbot' h3'

@[expose] def Claim1720Le : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P → S ≤ x1720 A Y₀ S L

@[expose] def Claim1720Inner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P → S ≤ (S ⊓ Y₀) ⊔ (S ⊓ cQuot Y₀)

@[expose] noncomputable def Claim1720A10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P →
      Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 10)) →
        S ⊓ Y₀ ≤ (S ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y₀

theorem claim1720Le_of (hInner : Claim1720Inner) (hA10 : Claim1720A10) (hQ0 : Claim17Q0)
    (h1715 : Item1715) (h146 : Item146S14) (h166 : Item166S17) (hbot : Item145BotS17)
    (h168 : Item168S17) : Claim1720Le := by
  intro G _ _ A c L Y₀ Y₁ S p P h
  have hs := h.toSec17Std
  have hKQ := hQ0 G A c L Y₀ hs
  have hSQ : S ∈ scriptQ A (lB A) := h.mem_qStar_two.prop.1.1
  have hAC : A ≤ Subgroup.normalizer ((cQuot Y₀ : Subgroup G) : Set G) :=
    (Subgroup.le_normalizer.trans hs.normalizer_le).trans
      (HeadProof.normalizer_le_normalizer_cQuot Y₀)
  have hSC : S ⊓ cQuot Y₀ ≤ delta A (lB A) (cQuot Y₀) :=
    le_delta (mem_scriptQ_of_le hSQ inf_le_left (Late.le_normalizer_inf hSQ.1.2.2 hAC))
      inf_le_right
  have hKD : CFSG.Open.pCoreOf 2 Y₀ ≤ delta A (lB A) (cQuot Y₀) :=
    le_delta hKQ (Proof1712.pCoreOf_le_cQuot Y₀)
  have hSY : S ⊓ Y₀ ≤ (S ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
    rcases h1715 G A c L Y₀ hs with ⟨-, hY, -, -⟩ | ⟨-, -, hA10', -, -⟩
    · have hSG := Proof1712.mem_qStar_top h (h166 G A c L Y₀ hs) (hbot G A c L Y₀ hs)
        (h168 G A c L Y₀ hs)
      have hKS := Proof1712.pCoreOf_le_of_mem_scriptQ hs (h146 G A c L hs.toSec14Std) hSG hKQ
      have hLK : L ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y₀ : Subgroup G) : Set G) :=
        hs.le_y0.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀)
      have e : S ⊓ Y₀ = S ⊓ (L ⊔ CFSG.Open.pCoreOf 2 Y₀) := by
        conv_lhs => rw [hY]
      rw [e]
      exact Proof1712.inf_sup_le_of_le hKS hLK
    · exact hA10 G A c L Y₀ Y₁ S p P h hA10'
  calc S ≤ (S ⊓ Y₀) ⊔ (S ⊓ cQuot Y₀) := hInner G A c L Y₀ Y₁ S p P h
    _ ≤ x1720 A Y₀ S L :=
        sup_le (hSY.trans (sup_le le_sup_right (hKD.trans le_sup_left)))
          (hSC.trans le_sup_left)

@[expose] def Claim1720Trans : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P → TransOn A (lB A) (xA A) (x1720 A Y₀ S L)

@[expose] def Claim1720Odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P → ¬ 3 ∣ Nat.card (x1720 A Y₀ S L)

@[expose] noncomputable def Claim1716Odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → omegaA A = {Subgroup.zpowers c} →
      ¬ 3 ∣ Nat.card (delta A (lB A) (cQuot Y₀))

theorem Proof1712.not_three_dvd_delta_cQuot (hOdd : Claim1716Odd) {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} (h : Sec17Std G A c L Y₀) :
    ¬ 3 ∣ Nat.card (delta A (lB A) (cQuot Y₀)) := by
  by_cases hΩ : omegaA A = {Subgroup.zpowers c}
  · exact hOdd G A c L Y₀ h hΩ
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ⟩ := h.a10_or_omega.resolve_right hΩ
  have hAY : A ≤ Y₀ := h.le_y0_of_alternating_ten ⟨φ⟩
  have hAD : A ≤ Subgroup.normalizer ((delta A (lB A) (cQuot Y₀) : Subgroup G) : Set G) :=
    le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  obtain ⟨z, ⟨hzD, hzC⟩, hz3⟩ :=
    Proof1712.exists_mem_inf_centralizer_of_dvd (isE27_of_std h).isPGroup hAD h3
  have hzA : z ∈ A := Sec15.mem_of_mem_partTwoF h.toSec13Data.mem_partTwoF
    (by rw [← hz3]; exact pow_orderOf_eq_one z)
    (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hzC a ha))
  have hzK := Proof1712.inf_cQuot_le_of_alternating_ten φ ⟨hAY hzA, delta_le _ hzD⟩
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₀ ⟨z, hzK⟩
  have hk' : z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hz1 : z = 1 := Step163Alt.eq_one_of_two_three (m := k) (n := 1) hk'
    (by rw [pow_one, ← hz3]; exact pow_orderOf_eq_one z)
  rw [hz1, orderOf_one] at hz3
  omega

theorem claim1720Odd_of (hOdd : Claim1716Odd) (hQ0 : Claim17Q0) : Claim1720Odd := by
  intro G _ _ A c L Y₀ Y₁ S p P h h3
  have hs := h.toSec17Std
  set D := delta A (lB A) (cQuot Y₀) with hD
  set K := CFSG.Open.pCoreOf 2 Y₀ with hK
  have hKD : K ≤ D := le_delta (hQ0 G A c L Y₀ hs) (Proof1712.pCoreOf_le_cQuot Y₀)
  have hSLD : S ⊓ L ≤ Subgroup.normalizer (D : Set G) := by
    intro s hsSL
    have hsY : s ∈ Y₀ := hs.le_y0 (Subgroup.mem_inf.mp hsSL).2
    have hle : D.map (MulAut.conj s).toMonoidHom ≤ D := by
      rw [Subgroup.map_le_iff_le_comap]
      refine sSup_le fun Q hQ q hq => ?_
      rw [Subgroup.mem_comap]
      have hqC : q⁻¹ ∈ (cQuot Y₀ : Set G) := inv_mem (hQ.2 hq)
      rw [coe_cQuot] at hqC
      have hkK := hqC.2 s hsY
      have e : (MulAut.conj s).toMonoidHom q = q * (q⁻¹ * s * q⁻¹⁻¹ * s⁻¹) := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact D.mul_mem (le_sSup hQ hq) (hKD hkK)
    refine Sec14.mem_normalizer_of_map_conj_eq (Subgroup.eq_of_le_of_card_ge hle ?_)
    rw [Subgroup.card_map_of_injective (MulAut.conj s).injective]
  have hdvd := card_sup_dvd_card_mul hSLD
  have hX : x1720 A Y₀ S L = (S ⊓ L) ⊔ D := sup_comm _ _
  rw [hX] at h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp (h3.trans hdvd) with h1 | h1
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp h.mem_qStar_two.prop.2
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (hS2.to_le (inf_le_left : S ⊓ L ≤ S))
    rw [hm] at h1
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h1)
    omega
  · exact Proof1712.not_three_dvd_delta_cQuot hOdd hs h1

theorem claim1720Trans_of (hOdd : Claim1720Odd) (h146 : Item146S14) (hbot : Item145BotS17) :
    Claim1720Trans := by
  intro G _ _ A c L Y₀ Y₁ S p P h
  have hs := h.toSec17Std
  obtain ⟨hAX, hXΔ⟩ := Proof1712.x1720_facts h
  have hX3 := hOdd G A c L Y₀ Y₁ S p P h
  have hXtop : x1720 A Y₀ S L ≠ ⊤ := by
    intro htop
    apply hX3
    rw [htop, Subgroup.card_top]
    have h27 : Nat.card A = 27 := (isE27_of_std hs).2
    exact (show 3 ∣ Nat.card A by rw [h27]; norm_num).trans (Subgroup.card_subgroup_dvd_card A)
  exact transOn_of_not_three_dvd (isE27_of_std hs) (h146 G A c L hs.toSec14Std)
    (hbot G A c L Y₀ hs) hXΔ ⟨hXtop, hAX⟩ hX3

theorem claim1720_of_trans (hLe : Claim1720Le) (hTrans : Claim1720Trans) (h166 : Item166S17)
    (hbot : Item145BotS17) (h168 : Item168S17) : Claim1720 := by
  intro G _ _ A c L Y₀ Y₁ S p P h
  have hs := h.toSec17Std
  have hSG := Proof1712.mem_qStar_top h (h166 G A c L Y₀ hs) (hbot G A c L Y₀ hs)
    (h168 G A c L Y₀ hs)
  refine ⟨⟨⟨⟨hSG.prop.1.1, hLe G A c L Y₀ Y₁ S p P h⟩, hSG.prop.2⟩,
    fun R hR hSR => hSG.2 ⟨⟨hR.1.1, le_top⟩, hR.2⟩ hSR⟩, hTrans G A c L Y₀ Y₁ S p P h⟩

theorem claim1720_of (hLe : Claim1720Le) (hOdd : Claim1720Odd) (h146 : Item146S14)
    (hbot : Item145BotS17) (h166 : Item166S17) (h168 : Item168S17) : Claim1720 :=
  claim1720_of_trans hLe (claim1720Trans_of hOdd h146 hbot) h166 hbot h168

theorem claim1720_of_inner (hInner : Claim1720Inner) (hA10 : Claim1720A10) (hQ0 : Claim17Q0)
    (h1715 : Item1715) (hOdd : Claim1720Odd) (h146 : Item146S14) (hbot : Item145BotS17)
    (h166 : Item166S17) (h168 : Item168S17) : Claim1720 :=
  claim1720_of (claim1720Le_of hInner hA10 hQ0 h1715 h146 h166 hbot h168) hOdd h146 hbot h166
    h168

theorem claim1720_of_steps (hInner : Claim1720Inner) (hA10 : Claim1720A10) (hQ0 : Claim17Q0)
    (h1715 : Item1715) (hOdd : Claim1716Odd) (h146 : Item146S14) (hbot : Item145BotS17)
    (h166 : Item166S17) (h168 : Item168S17) : Claim1720 :=
  claim1720_of_inner hInner hA10 hQ0 h1715 (claim1720Odd_of hOdd hQ0) h146 hbot h166 h168

end CFSG.RankThree.PartTwo.Sec17
