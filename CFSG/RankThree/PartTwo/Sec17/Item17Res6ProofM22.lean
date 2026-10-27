module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res6ProofQuot
public import CFSG.RankThree.PartTwo.Sec17.Item17Res6ProofA7W
public import CFSG.RankThree.PartTwo.Sec17.Item1722ProofHJ
public import CFSG.RankThree.PartTwo.KFacts.KP4
import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofMeet
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16
open scoped Pointwise

namespace Proof17Res6

variable {G : Type} [Group G] [Finite G] {A L Y₀ : Subgroup G} {c : G}

omit [Finite G] in
theorem exists_mem_L_mk_eq (hLY : L ≤ Y₀) (hY : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀)
    (z : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) :
    ∃ l : ↥Y₀, (l : G) ∈ L ∧ QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) l = z := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y₀) z
  have hLN : L ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₀ : Set G) :=
    hLY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀)
  have hy' : (y : G) ∈ (L : Set G) * (CFSG.Open.pCoreOf 2 Y₀ : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right L _ hLN, ← hY]
    exact y.2
  obtain ⟨l, hl, o, ho, hlo⟩ := hy'
  refine ⟨⟨l, hLY hl⟩, hl, (Step163Alt.mk_eq_mk_iff _ _).mpr ?_⟩
  have e : (⟨l, hLY hl⟩ : ↥Y₀)⁻¹.1 * y.1 = o := by
    rw [← hlo]
    simp
  rw [show ((⟨l, hLY hl⟩ : ↥Y₀) : G)⁻¹ * (y : G) = o by simpa using e]
  exact ho

theorem le_normalizer_of_inf
    (h : Sec17Std G A c L Y₀)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (V : Subgroup G) (hVL : V ≤ L)
    (hV : A ⊓ L ≤ Subgroup.normalizer (V : Set G)) : A ≤ Subgroup.normalizer (V : Set G) := by
  rw [Proof1721.eq_zpowers_sup_inf h h9]
  refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (V : Set G) ?_)) hV
  exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.toSec13Data.le_centralizer (hVL hv))

theorem card_kimg_inf (h : Sec17Std G A c L Y₀) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) :
    Nat.card (kimg Y₀ (A ⊓ L)) = 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hALY : A ⊓ L ≤ Y₀ := inf_le_right.trans h.le_y0
  have hB3 : IsPGroup 3 ((A ⊓ L).subgroupOf Y₀) :=
    ((HeadProof.isE27_of_std h).isPGroup.to_le inf_le_left).comap_subtype
  have hker : IsPGroup 2 (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)).ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  rw [kimg, TailProof.card_map_of_isPGroup_three _ hker hB3,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hALY).toEquiv, h9]

theorem three_dvd_of_typeMax [(kerAO2 A Y₀).Normal] {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (h142 : Concl142 A (lB A))
    (hLsurj : ∀ z : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀, ∃ l : ↥Y₀, (l : G) ∈ L ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) l = z)
    (hAnorm : ∀ V : Subgroup G, V ≤ L → A ⊓ L ≤ Subgroup.normalizer (V : Set G) →
      A ≤ Subgroup.normalizer (V : Set G))
    (hmax3 : ∀ X : Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀),
      kimg Y₀ (A ⊓ L) ≤ Subgroup.normalizer (X : Set _) → ¬ 3 ∣ Nat.card X → IsPGroup 2 X)
    {w : G} (hw : w ∈ Subgroup.normalizer (A : Set G) ⊓ Y₀)
    (hne : imgY0 A Y₀ ((S ⊓ Y₀).map (MulAut.conj w).toMonoidHom) ≠ imgY0 A Y₀ (S ⊓ Y₀)) :
    3 ∣ Nat.card ↥(imgY0 A Y₀ (S ⊓ Y₀) ⊔
      imgY0 A Y₀ ((S ⊓ Y₀).map (MulAut.conj w).toMonoidHom)) := by
  set T := S ⊓ Y₀ with hT
  set T' := T.map (MulAut.conj w).toMonoidHom with hT'
  obtain ⟨hwA, hwY⟩ := Subgroup.mem_inf.mp hw
  have hAT : A ≤ Subgroup.normalizer (T : Set G) :=
    Late.le_normalizer_inf h.mem_qStar_two.prop.1.1.1.2.2 h.le_normalizer_y0
  have hAT' : A ≤ Subgroup.normalizer (T' : Set G) := by
    intro a ha
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨t, ht, rfl⟩ := hx
    have ha' : w⁻¹ * a * w ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hwA) a).mp ha
      simpa using this
    have hat : (w⁻¹ * a * w) * t * (w⁻¹ * a * w)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (hAT ha') t).mp ht
    refine ⟨(w⁻¹ * a * w) * t * (w⁻¹ * a * w)⁻¹, hat, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hB := kimg_le_normalizer_kimg (Y₀ := Y₀) ((inf_le_left : A ⊓ L ≤ A).trans hAT)
  have hB' := kimg_le_normalizer_kimg (Y₀ := Y₀) ((inf_le_left : A ⊓ L ≤ A).trans hAT')
  exact three_dvd_of_maximal inf_le_right hwY hB hB'
    (fun X hBX h3 hTX => le_kimg_of_le h h142 hLsurj hAnorm (hmax3 X hBX h3) hBX hTX) hne

theorem isPGroup_two_of_m22
    {Λ : Type} [Group Λ]
    (hΛ : Nonempty (Λ ≃* CFSG.Blueprint.NativeSporadic.M22)) {B : Subgroup Λ}
    (hB : Nat.card B = 9) (X : Subgroup Λ) (hBX : B ≤ Subgroup.normalizer (X : Set Λ))
    (h3 : ¬ 3 ∣ Nat.card X) : IsPGroup 2 X :=
  KFacts.KP4.m22_isPGroup_of_mem_invariant hΛ hB
    ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three X).mpr h3, hBX⟩

theorem isPGroup_two_of_j2
    {Λ : Type} [Group Λ] [Finite Λ]
    (hΛ : Nonempty (Λ ≃* CFSG.Blueprint.NativeSporadic.J2)) {B : Subgroup Λ}
    (hB : Nat.card B = 9) (X : Subgroup Λ) (hBX : B ≤ Subgroup.normalizer (X : Set Λ))
    (h3 : ¬ 3 ∣ Nat.card X) : IsPGroup 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by rw [hB]; norm_num)
  have hall : ∀ {d : ℕ}, d.Prime → d ∣ Nat.card X → d = 2 := by
    intro d hd hdX
    by_contra hd2
    have hd3 : d ≠ 3 := fun e => h3 (e ▸ hdX)
    have hd3' : 3 < d := by
      have := hd.two_le
      omega
    have : Fact d.Prime := ⟨hd⟩
    obtain ⟨T, hT, -, hBT⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
      Nat.prime_three hd hB3 h3 hBX (bot_le : (⊥ : Subgroup Λ) ≤ X) IsPGroup.of_bot
      (fun b _ => Subgroup.mem_normalizer_iff.mpr fun x => by
        simp only [Subgroup.mem_bot]
        exact ⟨fun hx => by rw [hx]; group, fun hx => by
          have := congrArg (fun z => b⁻¹ * z * b) hx
          simpa [mul_assoc] using this⟩)
    have hT1 := Proof17Res3.j2_eq_bot_of_le_normalizer h415 hΛ hB hd hd3' hT.2.1 hBT
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) d hdX
    have hxp : IsPGroup d (Subgroup.zpowers (x : Λ)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx, pow_one]
    have hxX : Subgroup.zpowers (x : Λ) ≤ X := Subgroup.zpowers_le.mpr x.2
    have hxT := hT.2.2 _ hxX hxp (by rw [hT1]; exact bot_le)
    rw [hT1] at hxT
    have hx1 : (x : Λ) = 1 := by
      have : (x : Λ) ∈ Subgroup.zpowers (x : Λ) := Subgroup.mem_zpowers _
      rw [hxT] at this
      exact this
    have : orderOf (x : Λ) = d := by rw [Subgroup.orderOf_coe, hx]
    rw [hx1, orderOf_one] at this
    exact hd.one_lt.ne this
  exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' hall)

omit [Finite G] in
theorem nonempty_quot_equiv_of_theta (hLY : L ≤ Y₀) (hY : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀)
    (hθ : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L) {X : Type*} [Group X]
    (φL : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* X) : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* X) := by
  obtain ⟨e⟩ := Proof17Res3.nonempty_quotient_pCore_two_equiv hLY hY
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hθ.symm).trans φL)⟩

end Proof17Res6

@[expose] noncomputable def Claim1718QuotOneL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (h : Sec17Y1 G A c L Y₀ Y₁ S p P),
    omegaA A = {Subgroup.zpowers c} →
    (∃ (q : ℕ) (_ : Fact q.Prime), 3 < q ∧
      Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) q 1) →
    letI := kerAO2_normal h.le_normalizer_y0
    ∀ w ∈ Subgroup.normalizer (A : Set G) ⊓ Y₀,
      imgY0 A Y₀ ((S ⊓ Y₀).map (MulAut.conj w).toMonoidHom) ≠ imgY0 A Y₀ (S ⊓ Y₀) →
        3 ∣ Nat.card ↥(imgY0 A Y₀ (S ⊓ Y₀) ⊔
          imgY0 A Y₀ ((S ⊓ Y₀).map (MulAut.conj w).toMonoidHom))

section Provers

theorem claim1718QuotOne_of_L3 (hL3 : Claim1718QuotOneL3) (h1715 : Item1715) (h135 : Item135)
    (h142 : Concl142S14) (h9 : CardInfNineS17) : Claim1718QuotOne := by
  intro G _ _ A c L Y₀ Y₁ S p P h hΩ
  have hs := h.toSec17Std
  have := kerAO2_normal h.le_normalizer_y0
  obtain ⟨hY, htypes⟩ : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ ∧
      ((∃ (q : ℕ) (_ : Fact q.Prime), 3 < q ∧
          Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) q 1) ∨
        Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
        Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) := by
    rcases h1715 G A c L Y₀ hs with ⟨-, hY, -, htypes⟩ | ⟨-, -, -, -, hT⟩
    · exact ⟨hY, htypes⟩
    · exfalso
      have h3 := hT.1
      rw [hΩ, Set.ncard_singleton] at h3
      omega
  have h9' := h9 G A c L Y₀ hs
  have hLsurj := Proof17Res6.exists_mem_L_mk_eq hs.le_y0 hY
  have hAnorm := Proof17Res6.le_normalizer_of_inf hs h9'
  have hB9 := Proof17Res6.card_kimg_inf hs h9'
  have h142' := h142 G A c L hs.toSec14Std
  rcases htypes with hL3' | hA7 | hM22 | hJ2
  · exact hL3 G A c L Y₀ Y₁ S p P h hΩ hL3'
  · obtain ⟨φL⟩ := hA7
    obtain ⟨φ, g, hP⟩ := exists_a7Pic_of h1715 h135 h9 hs hΩ φL
    exact fun w hw hne => Proof17Res6.three_dvd_of_a7 h hP h142' hw hne
  · obtain ⟨φL⟩ := hM22
    have : Nontrivial ↥CFSG.Blueprint.NativeSporadic.M22 := by
      rw [← Finite.one_lt_card_iff_nontrivial, CFSG.Sporadic.Mathieu.card_M22]
      norm_num
    have hθ : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L :=
      Proof1515.theta_eq_pCore_two_of_multFree (h135 G A c L hs.toSec13Data hs.hypS_or_hypT)
        ⟨φL⟩ Proof1515.multFree_M22
    obtain ⟨e⟩ := Proof17Res6.nonempty_quot_equiv_of_theta hs.le_y0 hY hθ φL
    exact fun w hw hne => Proof17Res6.three_dvd_of_typeMax h h142' hLsurj hAnorm
      (fun X hBX h3 => Proof17Res6.isPGroup_two_of_m22 ⟨e⟩ hB9 X hBX h3) hw hne
  · obtain ⟨⟨f⟩, -⟩ := hs.j2_local hJ2
    obtain ⟨e⟩ := Proof17Res3.nonempty_quotient_pCore_two_equiv hs.le_y0 hY
    exact fun w hw hne => Proof17Res6.three_dvd_of_typeMax h h142' hLsurj hAnorm
      (fun X hBX h3 => Proof17Res6.isPGroup_two_of_j2 ⟨e.trans f⟩ hB9 X hBX h3) hw hne

end Provers

end CFSG.RankThree.PartTwo.Sec17
