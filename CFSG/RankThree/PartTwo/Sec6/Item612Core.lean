module

public import CFSG.RankThree.PartTwo.Sec6.Item612Fitting
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Source.OrderThreeMinimalTwoGroup
import CFSG.RankThree.PartTwo.Source.MinimalFaithfulCentralProduct
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem card_inf_centralizer_modEq {p : ℕ} [Fact p.Prime] {E Y : Subgroup G} (hE : IsPGroup p E)
    (hEY : E ≤ Subgroup.normalizer (Y : Set G)) :
    Nat.card (Y ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) ≡ Nat.card Y [MOD p] := by
  let : MulDistribMulAction E Y := Subgroup.conjMulDistribMulActionOfLeNormalizer E Y hEY
  have hsmul : ∀ (e : E) (y : Y), ((e • y : Y) : G) = (e : G) * y * (e : G)⁻¹ := fun _ _ => rfl
  have h := hE.card_modEq_card_fixedPoints Y
  have heq : Nat.card (MulAction.fixedPoints E Y) =
      Nat.card (Y ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun y => ⟨(y : Y), (y : Y).2, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
        invFun := fun y => ⟨⟨y, y.2.1⟩, MulAction.mem_fixedPoints.mpr fun e => Subtype.ext ?_⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl }
    · have h1 := MulAction.mem_fixedPoints.mp y.2 ⟨e, he⟩
      have h2 := congrArg Subtype.val h1
      rw [hsmul] at h2
      calc e * (y : G) = (e * (y : G) * e⁻¹) * e := by group
        _ = (y : G) * e := by rw [h2]
    · rw [hsmul]
      have h1 := Subgroup.mem_centralizer_iff.mp y.2.2 e e.2
      calc (e : G) * y * (e : G)⁻¹ = (y : G) * e * (e : G)⁻¹ := by rw [h1]
        _ = y := by group
  rw [heq] at h
  exact h.symm

theorem le_centralizer_or_irreducible {E U : Subgroup G} (hE : IsPGroup 3 E)
    (hEU : E ≤ Subgroup.normalizer (U : Set G)) (hU4 : Nat.card U = 4) :
    E ≤ Subgroup.centralizer (U : Set G) ∨ (U ⊓ Subgroup.centralizer (E : Set G) = ⊥ ∧
      ∀ X : Subgroup G, X ≤ U → E ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = U) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdiv4 : ∀ X : Subgroup G, X ≤ U → Nat.card X = 1 ∨ Nat.card X = 2 ∨ Nat.card X = 4 := by
    intro X hXU
    have hd := Subgroup.card_dvd_of_le hXU
    rw [hU4] at hd
    have : Nat.card X ≤ 4 := Nat.le_of_dvd (by norm_num) hd
    interval_cases h : Nat.card X <;> simp_all
  have hC := card_inf_centralizer_modEq hE hEU
  rw [hU4] at hC
  rcases hdiv4 _ (inf_le_left : U ⊓ Subgroup.centralizer (E : Set G) ≤ U) with h1 | h1 | h1
  · right
    have hbot : U ⊓ Subgroup.centralizer (E : Set G) = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    refine ⟨hbot, fun X hXU hEX => ?_⟩
    have hCX := card_inf_centralizer_modEq hE hEX
    have hXbot : X ⊓ Subgroup.centralizer (E : Set G) = ⊥ := by
      rw [eq_bot_iff, ← hbot]
      exact inf_le_inf_right _ hXU
    rw [hXbot, Subgroup.card_bot] at hCX
    rcases hdiv4 X hXU with h2 | h2 | h2
    · exact Or.inl (Subgroup.eq_bot_of_card_eq _ h2)
    · rw [h2] at hCX
      exact absurd hCX (by decide)
    · exact Or.inr (Subgroup.eq_of_le_of_card_ge hXU (by rw [h2, hU4]))
  · rw [h1] at hC
    exact absurd hC (by decide)
  · left
    have heq : U ⊓ Subgroup.centralizer (E : Set G) = U :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hU4])
    rw [Subgroup.le_centralizer_iff]
    exact inf_eq_left.mp heq

theorem mem_fourGroupsPlus_or_mem_fourGroupsMinus {E U : Subgroup G} (hE : IsPGroup 3 E)
    (hU : U ∈ fourGroups E) :
    U ∈ fourGroupsPlus E ∨ (U ∈ fourGroupsMinus E ∧
      ∀ X : Subgroup G, X ≤ U → E ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = U) := by
  obtain ⟨hEU, -, hU4⟩ := mem_fourGroups_iff.mp hU
  rcases le_centralizer_or_irreducible hE hEU hU4 with h | h
  · exact Or.inl (mem_fourGroupsPlus_iff.mpr ⟨hU, h⟩)
  · obtain ⟨hbot, hirr⟩ := h
    refine Or.inr ⟨⟨hU, ?_⟩, hirr⟩
    have hle : ⁅U, E⁆ ≤ U := Subgroup.le_normalizer_iff_commutator_le_left.mp hEU
    rcases hirr _ hle (le_normalizer_commutator_right U E) with h0 | heq
    · exfalso
      have hUC : U ≤ Subgroup.centralizer (E : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0
      rw [inf_eq_left.mpr hUC] at hbot
      rw [hbot, Subgroup.card_bot] at hU4
      norm_num at hU4
    · exact heq.symm


omit [Finite G] in
theorem pCoreOf_two_eq_inSubgroup (H : Subgroup G) :
    CFSG.Assembly.pCoreOf 2 H = inSubgroup (CFSG.pCore 2) H := by
  simp only [CFSG.Assembly.pCoreOf, inSubgroup]

omit [Finite G] in
theorem inf_centralizer_inSubgroup_pCore_eq_bot (hchar : CFSG.Assembly.IsCharTwoType G)
    {U B : Subgroup G} (hU2 : IsPGroup 2 U) (hU1 : U ≠ ⊥) (hB3 : ∀ b ∈ B, b ^ 3 = 1)
    (hBU : B ≤ Subgroup.centralizer (U : Set G)) :
    B ⊓ Subgroup.centralizer
      (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer (U : Set G) with hC
  set Q := inSubgroup (CFSG.pCore 2) C with hQ
  set N := Subgroup.normalizer (U : Set G) with hN
  set R := inSubgroup (CFSG.pCore 2) N with hR
  have hR2 : IsPGroup 2 R := CFSG.pCore_isPGroup.map N.subtype
  have hNR : N ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (CFSG.pCore 2 N))
  have hRN : R ≤ N := Subgroup.map_subtype_le _
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hRC : R ⊓ C ≤ Q := by
    rw [hQ, ← pCoreOf_two_eq_inSubgroup]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      (hR2.to_le inf_le_left)
    exact (le_inf (hCN.trans hNR) Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  set B0 := B ⊓ Subgroup.centralizer (Q : Set G)
  have hB0R : B0 ≤ Subgroup.centralizer (R : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hbT : b ∈ C := hBU hb.1
    have hrN : r ∈ N := hRN hr
    have hcR : b * r * b⁻¹ * r⁻¹ ∈ R :=
      R.mul_mem ((Subgroup.mem_normalizer_iff.mp (hNR (hCN hbT)) r).mp hr) (R.inv_mem hr)
    have hcC : b * r * b⁻¹ * r⁻¹ ∈ C := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have ht' : r⁻¹ * t * r ∈ U := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hrN) t).mp ht
        simpa using this
      have hb' : (r⁻¹ * t * r) * b = b * (r⁻¹ * t * r) :=
        Subgroup.mem_centralizer_iff.mp hbT _ ht'
      have hbt : t * b = b * t := Subgroup.mem_centralizer_iff.mp hbT t ht
      have hb'' : b⁻¹ * (r⁻¹ * t * r) = (r⁻¹ * t * r) * b⁻¹ := by
        calc b⁻¹ * (r⁻¹ * t * r) = b⁻¹ * ((r⁻¹ * t * r) * b) * b⁻¹ := by group
          _ = b⁻¹ * (b * (r⁻¹ * t * r)) * b⁻¹ := by rw [hb']
          _ = (r⁻¹ * t * r) * b⁻¹ := by group
      symm
      calc b * r * b⁻¹ * r⁻¹ * t = b * r * (b⁻¹ * (r⁻¹ * t * r)) * r⁻¹ := by group
        _ = b * r * ((r⁻¹ * t * r) * b⁻¹) * r⁻¹ := by rw [hb'']
        _ = b * t * (r * b⁻¹ * r⁻¹) := by group
        _ = t * b * (r * b⁻¹ * r⁻¹) := by rw [hbt]
        _ = t * (b * r * b⁻¹ * r⁻¹) := by group
    obtain ⟨c, hc⟩ : ∃ c : G, c = b * r * b⁻¹ * r⁻¹ := ⟨_, rfl⟩
    rw [← hc] at hcR hcC
    have hcQ : c ∈ Q := hRC ⟨hcR, hcC⟩
    have hbc : b * c = c * b := (Subgroup.mem_centralizer_iff.mp hb.2 c hcQ).symm
    have hb3 : b ^ 3 = 1 := hB3 b hb.1
    have hbrb : b * r * b⁻¹ = c * r := by rw [hc]; group
    have hconj : ∀ y : G, b * (c * y) * b⁻¹ = c * (b * y * b⁻¹) := fun y => by
      calc b * (c * y) * b⁻¹ = (b * c) * y * b⁻¹ := by group
        _ = (c * b) * y * b⁻¹ := by rw [hbc]
        _ = c * (b * y * b⁻¹) := by group
    have hb3' : b * (b * b) = 1 := by rw [← pow_three]; exact hb3
    have key : r = c * (c * (c * r)) := by
      calc r = b * (b * b) * r * (b * (b * b))⁻¹ := by rw [hb3', one_mul, inv_one, mul_one]
        _ = b * (b * (b * r * b⁻¹) * b⁻¹) * b⁻¹ := by group
        _ = b * (b * (c * r) * b⁻¹) * b⁻¹ := by rw [hbrb]
        _ = b * (c * (b * r * b⁻¹)) * b⁻¹ := by rw [hconj r]
        _ = b * (c * (c * r)) * b⁻¹ := by rw [hbrb]
        _ = c * (b * (c * r) * b⁻¹) := by rw [hconj (c * r)]
        _ = c * (c * (b * r * b⁻¹)) := by rw [hconj r]
        _ = c * (c * (c * r)) := by rw [hbrb]
    have hc3 : c ^ 3 = 1 := by
      have h' : c * (c * c) = 1 := by
        calc c * (c * c) = c * (c * (c * r)) * r⁻¹ := by group
          _ = r * r⁻¹ := by rw [← key]
          _ = 1 := mul_inv_cancel r
      rw [pow_three]
      exact h'
    have hc1 : c = 1 := Source.eq_one_of_pow_three_eq_one hR2 hcR hc3
    calc r * b = c⁻¹ * (b * r * b⁻¹) * b := by rw [hbrb]; group
      _ = b * r := by rw [hc1]; group
  have hB0R' : B0 ≤ R := by
    have h := hchar N ⟨U, hU1, hU2, rfl⟩
    rw [pCoreOf_two_eq_inSubgroup] at h
    exact (le_inf (inf_le_left.trans (hBU.trans hCN)) hB0R).trans h
  rw [eq_bot_iff]
  intro b hb
  exact Subgroup.mem_bot.mpr (Source.eq_one_of_pow_three_eq_one hR2 (hB0R' hb) (hB3 b hb.1))

theorem exists_commutator_inf_centralizer_ne_bot (hchar : CFSG.Assembly.IsCharTwoType G)
    {U B F : Subgroup G} (hU2 : IsPGroup 2 U) (hU1 : U ≠ ⊥)
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (hB9 : 9 ≤ Nat.card B)
    (hBU : B ≤ Subgroup.centralizer (U : Set G)) (hFB : F ≤ B) (hF1 : F ≠ ⊥) :
    ∃ c ∈ B, c ≠ 1 ∧ ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓
      Subgroup.centralizer {c}, F⁆ ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup.map _
  have hBQ : B ≤ Subgroup.normalizer (Q : Set G) :=
    hBU.trans (Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (CFSG.pCore 2 (Subgroup.centralizer (U : Set G)))))
  have hcop : Nat.Coprime 3 (Nat.card Q) := by
    obtain ⟨k, hk⟩ := hQ2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  by_contra hno
  push Not at hno
  have hQF : Q ≤ Subgroup.centralizer (F : Set G) :=
    Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hB (by simpa using hB9) hBQ hcop
      fun c hc hc1 => Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hno c hc hc1)
  have hbot := inf_centralizer_inSubgroup_pCore_eq_bot hchar hU2 hU1 (fun b hb => hB.2 b hb) hBU
  apply hF1
  rw [eq_bot_iff, ← hbot]
  exact le_inf hFB (Subgroup.le_centralizer_iff.mp hQF)


theorem centralizer_ne_top_of_ne_one (hG : TheoremFourHyp G) {c : G} (hc1 : c ≠ 1) :
    Subgroup.centralizer ({c} : Set G) ≠ ⊤ := by
  intro hC
  have := hG.isSimpleGroup
  obtain ⟨x, y, hxy⟩ := hG.nonabelian
  have hz : c ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hC ▸ Subgroup.mem_top g)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h' | h'
  · rw [h', Subgroup.mem_bot] at hz
    exact hc1 hz
  · exact hxy (Subgroup.mem_center_iff.1 (h' ▸ Subgroup.mem_top x) y).symm

theorem exists_mem_thetaComponentsAt_moved (hG : PartTwoStanding G) (h45 : Sec4.Item4_5)
    {A E U F : Subgroup G} (hA : A ∈ partTwoS G) (hE : E ∈ collectionIn (partTwoE G) A)
    (hU : U ∈ fourGroups E) (hFE : F ≤ E) (hFU : F ≤ Subgroup.centralizer (U : Set G))
    {c : G} (hcE : c ∈ E) (hcU : c ∈ Subgroup.centralizer (U : Set G)) (hc1 : c ≠ 1)
    (hV : ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓
      Subgroup.centralizer {c}, F⁆ ≠ ⊥) :
    ∃ L ∈ thetaComponentsAt 3 c,
      ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓ Subgroup.centralizer {c},
        F⁆ ≤ Subgroup.normalizer (L : Set G) ∧
      ¬ ⁅L, ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓
        Subgroup.centralizer {c}, F⁆⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hEmem, hEA⟩ := hE
  have hEab := hEmem.1
  have hE3 : IsPGroup 3 E := Sec5.isPGroup_of_isElemAbelian hEab
  have hAab := hA.1.1
  set Q := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) with hQ
  set S := Q ⊓ Subgroup.centralizer {c} with hS
  set V := ⁅S, F⁆ with hVdef
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup.map _
  have hS2 : IsPGroup 2 S := hQ2.to_le inf_le_left
  have hEc : E ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hEab.1.is_comm.comm ⟨x, hx⟩ ⟨c, hcE⟩))
  obtain ⟨hEU, hUab, hU4⟩ := mem_fourGroups_iff.mp hU
  have hEQ : E ≤ Subgroup.normalizer (Q : Set G) := fun e he =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.pCore 2 (Subgroup.centralizer (U : Set G))) (Source.mem_normalizer_centralizer (hEU he))
  have hES : E ≤ Subgroup.normalizer (S : Set G) :=
    (le_inf hEQ (hEc.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hFS : F ≤ Subgroup.normalizer (S : Set G) := hFE.trans hES
  have hVS : V ≤ S := Subgroup.le_normalizer_iff_commutator_le_left.mp hFS
  have hV2 : IsPGroup 2 V := hS2.to_le hVS
  have hUC : U ≤ Subgroup.centralizer (U : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.mpr fun v hv =>
      congrArg Subtype.val (hUab.1.is_comm.comm ⟨v, hv⟩ ⟨u, hu⟩)
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [hU4]; norm_num)
  have hUQ : U ≤ Q := by
    rw [hQ, ← pCoreOf_two_eq_inSubgroup]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUC
      (Subgroup.centralizer_le_normalizer _) hU2
  have hUc : U ≤ Subgroup.centralizer ({c} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hcU u hu)
  have hUS : U ≤ S := le_inf hUQ hUc
  have hSmem : S ∈ invariantPiSubgroups ⊤ E (piOf 2) :=
    (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top, hS2, hES⟩
  have h64 : ∀ P : Subgroup G, IsPGroup 3 P → E ⊔ S ≤ Subgroup.normalizer (P : Set G) →
      P ≤ Subgroup.centralizer (S : Set G) := by
    intro P hP3 hPN
    have hPmem : P ∈ invariantPiSubgroups ⊤ (E ⊔ S) (piOf 3) :=
      (mem_invariantPiSubgroups_piOf_iff Nat.prime_three).mpr ⟨le_top, hP3, hPN⟩
    rcases mem_fourGroupsPlus_or_mem_fourGroupsMinus hE3 hU with hUp | ⟨hUm, -⟩
    · exact rank3II_6_4_2_of_evenRank_eq hG.evenRank_eq (Late.isE27_of_mem_partTwoE hEmem) hUp
        hSmem hUS hPmem
    · refine rank3II_6_4_4_of_evenRank_eq hG.evenRank_eq (Late.isE27_of_mem_partTwoE hEmem) hUm
        hSmem hUS ?_ hPmem
      intro hbot
      apply hV
      rw [eq_bot_iff, ← hbot]
      exact Subgroup.commutator_mono le_rfl (le_inf hFE hFU)
  have h3 := map_le_centralizer_pCore_of_mem_partTwoS hG hA ⟨hEmem, hEA⟩ hcE hS2 inf_le_right hES
    h64
  have hEV : E ≤ Subgroup.normalizer (V : Set G) := fun e he =>
    Source.mem_normalizer_commutator (hES he) (by
      rw [Subgroup.mem_normalizer_iff]
      intro f
      have hcomm : ∀ f ∈ F, e * f * e⁻¹ = f := fun f hf => by
        have := hEab.1.is_comm.comm ⟨e, he⟩ ⟨f, hFE hf⟩
        have h' := congrArg Subtype.val this
        simp only [Subgroup.coe_mul] at h'
        rw [h']
        group
      constructor
      · intro hf
        rw [hcomm f hf]
        exact hf
      · intro hf
        have := hcomm _ hf
        have h2 : f = e * f * e⁻¹ := by
          have := hcomm (e * f * e⁻¹) hf
          calc f = e⁻¹ * (e * (e * f * e⁻¹) * e⁻¹) * e := by rw [this]; group
            _ = e * f * e⁻¹ := by group
        rw [h2]
        exact hf)
  have hVF : V = ⁅V, F⁆ := by
    have hcop : (Nat.card F).Coprime (Nat.card S) := by
      obtain ⟨a, ha⟩ := (hE3.to_le hFE).exists_card_eq
      obtain ⟨b, hb⟩ := hS2.exists_card_eq
      rw [ha, hb]
      exact Nat.Coprime.pow a b (by norm_num)
    exact (CFSG.BenderSuzuki.ig1114_commutator_idempotent_of_coprime S F hcop hFS).symm
  have hVθ : ¬ V ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) := by
    intro hle
    have hVE := commutator_eq_bot_of_mem_partTwoS hA (hEA hcE) hc1 hEA hle hV2 hEV
    apply hV
    rw [eq_bot_iff]
    calc V = ⁅V, F⁆ := hVF
      _ ≤ ⁅V, E⁆ := Subgroup.commutator_mono le_rfl hFE
      _ = ⊥ := hVE
  have h3V : (V.subgroupOf (Subgroup.centralizer ({c} : Set G))).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 (Subgroup.centralizer ({c} : Set G)))) ≤
      Subgroup.centralizer (CFSG.pCore 3 (Subgroup.centralizer ({c} : Set G) ⧸
        aschbacherSolvableCore 3 (Subgroup.centralizer ({c} : Set G))) :
          Set (Subgroup.centralizer ({c} : Set G) ⧸
            aschbacherSolvableCore 3 (Subgroup.centralizer ({c} : Set G)))) :=
    (Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hVS (Subgroup.mem_subgroupOf.mp hx))).trans h3
  obtain ⟨L, hL, hLV⟩ := exists_mem_thetaComponentsAt_not_le hV2 (hVS.trans inf_le_right) hVθ h3V
  have hAL := le_normalizer_of_mem_thetaComponentsAt h45 hG.toTheoremFourHyp hAab (hEA hcE) hc1
  have hVN : V ≤ Subgroup.normalizer (L : Set G) :=
    commutator_le_normalizer_of_mem_thetaComponentsAt (X := S) inf_le_right
      (fun L' hL' => hFE.trans (hEA.trans (hAL L' hL'))) hL
  refine ⟨L, hL, hVN, fun h => hLV (h.trans ?_)⟩
  rw [theta_eq_inf_of_mem_thetaComponentsAt hL]
  exact inf_le_right


omit [Finite G] in
theorem mem_normalizer_of_mem_normalizer_map {H : Subgroup G} {K : Subgroup H} {g : H}
    (hg : (g : G) ∈ Subgroup.normalizer ((K.map H.subtype : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer (K : Set H) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro h
  have h1 := hg (h : G)
  constructor
  · intro hh
    obtain ⟨y, hy, hyeq⟩ := h1.mp ⟨h, hh, rfl⟩
    have : y = g * h * g⁻¹ := Subtype.ext hyeq
    rwa [← this]
  · intro hh
    obtain ⟨y, hy, hyeq⟩ := h1.mpr ⟨g * h * g⁻¹, hh, by simp⟩
    have : y = h := Subtype.ext hyeq
    rwa [← this]

theorem map_thetaQuotCentralizer_le {H : Subgroup G} (L : Subgroup H) :
    (thetaQuotCentralizer L).map H.subtype ≤ thetaQuotCentralizer (L.map H.subtype) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨hxN, hxl⟩ := mem_thetaQuotCentralizer_iff.mp hx
  refine mem_thetaQuotCentralizer_iff.mpr ⟨Subgroup.le_normalizer_map H.subtype ⟨x, hxN, rfl⟩,
    ?_⟩
  rintro _ ⟨l, hl, rfl⟩
  rw [← map_inSubgroup_theta_of_injective H.subtype H.subtype_injective L]
  exact ⟨_, hxl l hl, by simp⟩

theorem props_of_moved (hG : PartTwoStanding G) (h45 : Sec4.Item4_5) (h49 : Sec4.Item4_9)
    {A E V : Subgroup G} (hA : A ∈ partTwoS G) (hE : E ∈ collectionIn (partTwoE G) A)
    {c : G} (hcE : c ∈ E) (hc1 : c ≠ 1) {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 c)
    (hV2 : IsPGroup 2 V) (hVc : V ≤ Subgroup.centralizer ({c} : Set G))
    (hEV : E ≤ Subgroup.normalizer (V : Set G)) (hVE : V ≤ ⁅V, E⁆)
    (hVL : V ≤ Subgroup.normalizer (L : Set G))
    (hLV : ¬ ⁅L, V⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L) :
    ⁅L, V⁆ = L ∧ E ≤ Subgroup.normalizer (L : Set G) ∧ ⁅L, E⁆ = L ∧ L ∈ lZero E ∧
      A ⊓ thetaQuotCentralizer L ≤ E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hEmem, hEA⟩ := hE
  have hEab := hEmem.1
  have hE3 : IsPGroup 3 E := Sec5.isPGroup_of_isElemAbelian hEab
  have hAab := hA.1.1
  have hLp := isPerfect_of_mem_thetaComponentsAt hL
  have hLq := isQuasisimple_of_mem_thetaComponentsAt hL
  have hAL' := le_normalizer_of_mem_thetaComponentsAt h45 hG.toTheoremFourHyp hAab (hEA hcE) hc1
  have hEL : E ≤ Subgroup.normalizer (L : Set G) := hEA.trans (hAL' L hL)
  have hVC : ¬ V ≤ thetaQuotCentralizer L := fun h => hLV ((commutator_le_theta_iff hVL).mpr h)
  have hLE : ⁅L, E⁆ = L := by
    refine commutator_eq_of_not_le_theta hLp hLq hEL fun h => hVC ?_
    have hEC := (commutator_le_theta_iff hEL).mp h
    refine hVE.trans ?_
    rw [Subgroup.commutator_le]
    intro v hv e he
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (conj_mem_thetaQuotCentralizer (hEC he) (hVL hv)) (inv_mem (hEC he))
  set H := Subgroup.centralizer ({c} : Set G) with hH
  obtain ⟨hLH, hL'⟩ := mem_thetaComponentsIn_iff.mp hL
  have hEH : E ≤ H := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hEab.1.is_comm.comm ⟨x, hx⟩ ⟨c, hcE⟩))
  have hH4 : SectionFourHyp H :=
    hG.toTheoremFourHyp.sectionFourHyp (centralizer_ne_top_of_ne_one hG.toTheoremFourHyp hc1)
  have h3Z : 3 ∣ Nat.card (Subgroup.center H) := by
    set c' : H := ⟨c, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have hc'3 : orderOf c' = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (hEab.2 c hcE) hc1
    have hle : Subgroup.zpowers c' ≤ Subgroup.center H := by
      rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, hc'3] at this
  have hXK : ∀ K ∈ thetaComponents 3 H, E.subgroupOf H ≤ Subgroup.normalizer (K : Set H) := by
    intro K hK x hx
    exact mem_normalizer_of_mem_normalizer_map
      (hEA.trans (hAL' (K.map H.subtype) ⟨K, hK, rfl⟩) (Subgroup.mem_subgroupOf.mp hx))
  have hVEeq : ⁅E, V⁆ = V := by
    rw [Subgroup.commutator_comm]
    exact le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp hEV) hVE
  have hV' : V.subgroupOf H ∈ invariantPiSubgroups ⊤ (E.subgroupOf H) (piOf 2) :=
    (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top,
      hV2.comap_of_injective H.subtype H.subtype_injective,
      subgroupOf_le_normalizer_subgroupOf hEV⟩
  have hVE' : ⁅E.subgroupOf H, V.subgroupOf H⁆ = V.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hEH,
      Subgroup.map_subgroupOf_eq_of_le hVc]
    exact hVEeq
  have h49' := h49 H hH4 h3Z (L.subgroupOf H) hL' (E.subgroupOf H)
    (hE3.comap_of_injective H.subtype H.subtype_injective) hXK (V.subgroupOf H) hV' hVE'
  have hVLC : V ≤ L ⊔ thetaQuotCentralizer L := by
    have h1 := Subgroup.map_mono (f := H.subtype) h49'
    rw [Subgroup.map_subgroupOf_eq_of_le hVc, Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hLH] at h1
    refine h1.trans (sup_le_sup_left ?_ L)
    have h2 := map_thetaQuotCentralizer_le (L.subgroupOf H)
    rwa [Subgroup.map_subgroupOf_eq_of_le hLH] at h2
  obtain ⟨U', hU', hU'E⟩ :=
    exists_invariant_two_subgroup_not_le_theta hE3 hEL hV2 hEV hVL hVLC hVE hVC
  refine ⟨commutator_eq_of_not_le_theta hLp hLq hVL hLV, hEL, hLE,
    ⟨mem_thetaComponentFamily_iff.mpr ⟨c, hcE, hc1, hL⟩, U', hU', hU'E⟩, ?_⟩
  exact inf_thetaQuotCentralizer_le_of_invariant hG.evenRank_eq hAab hEA hEmem.2.1 hEL hU' hU'E

end CFSG.RankThree.PartTwo.Sec6
