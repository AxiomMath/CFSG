module

import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints
public import CFSG.RankThree.PartTwo.Sec15.Item156ProofType
public import CFSG.RankThree.PartTwo.Sec17.Item17Res6ProofM22

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16

namespace Proof17Res6

theorem alternatingGroup_six_no_index_five (H : Subgroup (alternatingGroup (Fin 6)))
    (hH : H.index = 5) : False := by
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hfin : H.FiniteIndex := ⟨by rw [hH]; norm_num⟩
  have hdvd := Subgroup.index_normalCore_dvd_factorial_index H
  rcases (Subgroup.normalCore_normal H).eq_bot_or_eq_top with h | h
  · rw [h, Subgroup.index_bot, hH, Sec15.card_alternatingGroup_six] at hdvd
    norm_num [Nat.factorial] at hdvd
  · have hHtop : H = ⊤ := top_le_iff.mp (h ▸ Subgroup.normalCore_le H)
    rw [hHtop, Subgroup.index_top] at hH
    norm_num at hH

variable {Λ : Type} [Group Λ] [Finite Λ]

theorem exists_not_mem_normalizer_of_m22
    (hΛ : Nonempty (Λ ≃* CFSG.Blueprint.NativeSporadic.M22)) {B R : Subgroup Λ}
    (hB : Nat.card B = 9) (hR : R ∈ maxInvariantPiSubgroups ⊤ B (piOf 2)) :
    ∃ x ∈ Subgroup.normalizer (B : Set Λ), x ∉ Subgroup.normalizer (R : Set Λ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  set NB := Subgroup.normalizer (B : Set Λ) with hNB
  set NR := Subgroup.normalizer (R : Set Λ) with hNR
  have hle : NB ≤ NR := fun x hx => hcon x hx
  have hR2 : IsPGroup 2 R := (isPiSubgroup_piOf_iff Nat.prime_two R).mp hR.1.2.1
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by rw [hB]; norm_num)
  have hBR : B ≤ NR := hR.1.2.2
  have hCB : Subgroup.centralizer (B : Set Λ) = B := KFacts.KP4.m22_centralizer_eq hΛ hB
  have hBR1 : ∀ z, z ∈ B → z ∈ R → z = 1 := by
    intro z hzB hzR
    obtain ⟨k, hk⟩ := hB3 ⟨z, hzB⟩
    obtain ⟨m, hm⟩ := hR2 ⟨z, hzR⟩
    exact Step163Alt.eq_one_of_two_three (m := m) (n := k) (by simpa using congrArg Subtype.val hm)
      (by simpa using congrArg Subtype.val hk)
  have hint : ∀ r ∈ NB, r ∈ R → r = 1 := by
    intro r hrN hrR
    have hrC : r ∈ Subgroup.centralizer (B : Set Λ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h1 : r * b * r⁻¹ * b⁻¹ ∈ B :=
        mul_mem ((Subgroup.mem_normalizer_iff.mp hrN b).mp hb) (inv_mem hb)
      have h2 : r * b * r⁻¹ * b⁻¹ ∈ R := by
        have h3 := (Subgroup.mem_normalizer_iff.mp (hBR hb) r⁻¹).mp (inv_mem hrR)
        have e : r * b * r⁻¹ * b⁻¹ = r * (b * r⁻¹ * b⁻¹) := by group
        rw [e]
        exact mul_mem hrR h3
      have h4 := hBR1 _ h1 h2
      calc b * r = (r * b * r⁻¹ * b⁻¹)⁻¹ * r * b := by group
        _ = r * b := by rw [h4]; group
    rw [hCB] at hrC
    exact hBR1 r hrC hrR
  obtain ⟨-, ⟨e⟩⟩ := KFacts.KP4.m22_normalizer_quotient hΛ hB hR
  set f : ↥NB →* alternatingGroup (Fin 6) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (R.subgroupOf NR)).comp (Subgroup.inclusion hle))
    with hf
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, map_eq_one_iff e e.injective, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hint x x.2 hx)
  have hcard : Nat.card f.range = 72 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv]
    exact KFacts.KP4.m22_card_normalizer hΛ hB
  have hidx : f.range.index = 5 := by
    have h := Subgroup.card_mul_index f.range
    rw [hcard, Sec15.card_alternatingGroup_six] at h
    omega
  exact alternatingGroup_six_no_index_five _ hidx

variable {G : Type} [Group G] [Finite G] {A L Y₀ : Subgroup G} {c : G}

theorem exists_w_of_m22
    {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (h142 : Concl142 A (lB A))
    (hLsurj : ∀ z : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀, ∃ l : ↥Y₀, (l : G) ∈ L ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) l = z)
    (hAnorm : ∀ V : Subgroup G, V ≤ L → A ⊓ L ≤ Subgroup.normalizer (V : Set G) →
      A ≤ Subgroup.normalizer (V : Set G))
    (hLnorm : ∀ t ∈ L, t ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) →
      t ∈ Subgroup.normalizer (A : Set G))
    (hB9 : Nat.card (kimg Y₀ (A ⊓ L)) = 9)
    (hΛ : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* CFSG.Blueprint.NativeSporadic.M22)) :
    ∃ w ∈ Subgroup.normalizer (A : Set G) ⊓ Y₀,
      w ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ∧
        w ∉ Subgroup.normalizer ((S ⊓ Y₀ : Subgroup G) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLY : L ≤ Y₀ := h.toSec17Std.le_y0
  set κ := QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) with hκ
  set B := kimg Y₀ (A ⊓ L) with hB
  set R := kimg Y₀ (S ⊓ Y₀) with hR
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp h.mem_qStar_two.prop.2
  have hAS : A ≤ Subgroup.normalizer ((S ⊓ Y₀ : Subgroup G) : Set G) :=
    Late.le_normalizer_inf h.mem_qStar_two.prop.1.1.1.2.2 h.le_normalizer_y0
  have hBR : B ≤ Subgroup.normalizer (R : Set _) := kimg_le_normalizer_kimg (inf_le_left.trans hAS)
  have hR2 : IsPGroup 2 R := ((hS2.to_le inf_le_left).comap_subtype).map _
  have hRmax : R ∈ maxInvariantPiSubgroups ⊤ B (piOf 2) :=
    ⟨⟨le_top, (isPiSubgroup_piOf_iff Nat.prime_two R).mpr hR2, hBR⟩, fun X hX hRX =>
      le_kimg_of_le h h142 hLsurj hAnorm ((isPiSubgroup_piOf_iff Nat.prime_two X).mp hX.2.1)
        hX.2.2 hRX⟩
  obtain ⟨x, hxB, hxR⟩ := exists_not_mem_normalizer_of_m22 hΛ hB9 hRmax
  set κL : ↥L →* ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ := κ.comp (Subgroup.inclusion hLY) with hκL
  have hκker : IsPGroup 2 κL.ker := by
    rw [hκL, ← MonoidHom.comap_ker, hκ, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup.comap_of_injective _ (Subgroup.inclusion_injective hLY)
  set BL : Subgroup ↥L := (A ⊓ L).subgroupOf L with hBL
  have hBL3 : IsPGroup 3 BL :=
    ((HeadProof.isE27_of_std h.toSec17Std).isPGroup.to_le inf_le_left).comap_subtype
  have hBLmap : BL.map κL = B := by
    ext z
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact mem_kimg.mpr ⟨Subgroup.inclusion hLY b, Subgroup.mem_subgroupOf.mp hb, rfl⟩
    · intro hz
      obtain ⟨b, hb, rfl⟩ := mem_kimg.mp hz
      exact ⟨⟨b, hb.2⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  have hBc : ∀ u ∈ BL.map κL, ∀ v ∈ BL.map κL, u * v = v * u := by
    rw [hBLmap]
    intro u hu v hv
    obtain ⟨a, ha, rfl⟩ := mem_kimg.mp hu
    obtain ⟨b, hb, rfl⟩ := mem_kimg.mp hv
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h.toSec17Std.commute_of_mem ha.1 hb.1)
  have hxκ : x ∈ κL.range := by
    obtain ⟨l, hl, hlx⟩ := hLsurj x
    exact ⟨⟨l, hl⟩, hlx⟩
  have hxN : x ∈ Subgroup.normalizer ((BL.map κL : Subgroup _) : Set _) := by
    rw [hBLmap]
    exact hxB
  obtain ⟨y, hyN, hyκ⟩ := Step163Alt.exists_normalizer_lift κL hκker hBL3 hBc hxκ hxN
  have hBLL : BL.map L.subtype = A ⊓ L := by
    rw [hBL, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
  have hwAL : (y : G) ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := by
    have := Subgroup.le_normalizer_map L.subtype ⟨y, hyN, rfl⟩
    rwa [hBLL] at this
  have hwY : (y : G) ∈ Y₀ := hLY y.2
  refine ⟨y, Subgroup.mem_inf.mpr ⟨hLnorm y y.2 hwAL, hwY⟩, hwAL, fun hwS => hxR ?_⟩
  have hwR : κ ⟨y, hwY⟩ ∈ Subgroup.normalizer (R : Set _) := mk_mem_normalizer_kimg hwS
  have hκy : κL y = κ ⟨y, hwY⟩ := rfl
  have hu : x⁻¹ * κ ⟨y, hwY⟩ ∈ Subgroup.centralizer (B : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [← hBLmap] at hz
    obtain ⟨b, hb, rfl⟩ := hz
    have h1 := hyκ b hb
    rw [map_mul, map_mul, map_inv, hκy] at h1
    calc κL b * (x⁻¹ * κ ⟨y, hwY⟩)
        = x⁻¹ * (x * κL b * x⁻¹) * κ ⟨y, hwY⟩ := by group
      _ = x⁻¹ * (κ ⟨y, hwY⟩ * κL b * (κ ⟨y, hwY⟩)⁻¹) * κ ⟨y, hwY⟩ := by rw [h1]
      _ = x⁻¹ * κ ⟨y, hwY⟩ * κL b := by group
  rw [KFacts.KP4.m22_centralizer_eq hΛ hB9] at hu
  have hx' : x = κ ⟨y, hwY⟩ * (x⁻¹ * κ ⟨y, hwY⟩)⁻¹ := by group
  rw [hx']
  exact mul_mem hwR (inv_mem (hBR hu))

end Proof17Res6

@[expose] def Claim1719WNJOneL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P →
      IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
      omegaA A = {Subgroup.zpowers c} →
      (∃ (q : ℕ) (_ : Fact q.Prime), 3 < q ∧
        Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) q 1) →
      ∃ w ∈ Subgroup.normalizer (A : Set G) ⊓ Y₀,
        w ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ∧
          w ∉ Subgroup.normalizer ((S ⊓ Y₀ : Subgroup G) : Set G)

section Provers

theorem claim1719WNJOne_of_L3 (hL3 : Claim1719WNJOneL3) (h1715 : Item1715) (h135 : Item135)
    (h142 : Concl142S14) (h9 : CardInfNineS17) : Claim1719WNJOne := by
  intro G _ _ A c L Y₀ Y₁ S p P h hJ hΩ
  have hs := h.toSec17Std
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
  rcases htypes with hL3' | hA7 | hM22 | hJ2
  · exact hL3 G A c L Y₀ Y₁ S p P h hJ hΩ hL3'
  · obtain ⟨φL⟩ := hA7
    obtain ⟨φ, g, hP⟩ := exists_a7Pic_of h1715 h135 h9 hs hΩ φL
    exact Proof17Res6.exists_w_of_a7 h hP (h142 G A c L hs.toSec14Std)
  · obtain ⟨φL⟩ := hM22
    have : Nontrivial ↥CFSG.Blueprint.NativeSporadic.M22 := by
      rw [← Finite.one_lt_card_iff_nontrivial, CFSG.Sporadic.Mathieu.card_M22]
      norm_num
    have hθ : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L :=
      Proof1515.theta_eq_pCore_two_of_multFree (h135 G A c L hs.toSec13Data hs.hypS_or_hypT)
        ⟨φL⟩ Proof1515.multFree_M22
    exact Proof17Res6.exists_w_of_m22 h (h142 G A c L hs.toSec14Std)
      (Proof17Res6.exists_mem_L_mk_eq hs.le_y0 hY) (Proof17Res6.le_normalizer_of_inf hs h9')
      (fun t ht htE => Proof1721.mem_normalizer_A_of_mem_L hs h9' ht htE)
      (Proof17Res6.card_kimg_inf hs h9')
      (Proof17Res6.nonempty_quot_equiv_of_theta hs.le_y0 hY hθ φL)
  · exact (hJ.false (Classical.choice hJ2)).elim

theorem claim1719WNJ_of_L3 (hL3 : Claim1719WNJOneL3) (h1715 : Item1715) (h135 : Item135)
    (h142 : Concl142S14) (h9 : CardInfNineS17) : Claim1719WNJ :=
  claim1719WNJ_of_one (claim1719WNJOne_of_L3 hL3 h1715 h135 h142 h9) h1715 h142 h9

end Provers

end CFSG.RankThree.PartTwo.Sec17
