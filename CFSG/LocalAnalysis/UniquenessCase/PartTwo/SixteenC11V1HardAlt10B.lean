module

public import CFSG.GF2Type.Smith1979W3.CaseD.Jordan
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigOrb
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardBlocks
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.BHS.SymNatBasic
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.Quasithin.G6 CFSG.Quasithin.H13

@[expose] def s16c11_v1_p123_ten : Equiv.Perm (Fin 10) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def s16c11_v1_p456_ten : Equiv.Perm (Fin 10) := Equiv.swap 3 4 * Equiv.swap 4 5

@[expose] def s16c11_v1_blocks_ten : Subgroup (MulAut ↥(coreMod 10)) :=
  (Subgroup.closure ({s16c11_v1_p123_ten, s16c11_v1_p456_ten} : Set (Equiv.Perm (Fin 10)))).map
    (G6.coreAct 10)

private def s16c11_v1_ten_fixFinset : Finset (PermMod 10) :=
  Finset.univ.filter fun v =>
    (∑ i, Multiplicative.toAdd v i = 0) ∧ permAct 10 s16c11_v1_p123_ten v = v ∧
      permAct 10 s16c11_v1_p456_ten v = v

private lemma s16c11_v1_ten_fixFinset_card : s16c11_v1_ten_fixFinset.card = 2 ^ 5 := by
  simp only [s16c11_v1_ten_fixFinset]
  decide +kernel

private lemma s16c11_v1_ten_coreAct_fix_iff (σ : Equiv.Perm (Fin 10)) (v : coreMod 10) :
    coreAct 10 σ v = v ↔ permAct 10 σ (v : PermMod 10) = (v : PermMod 10) := by
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    rwa [coreAct_coe] at h'
  · intro h
    exact Subtype.ext (by rw [coreAct_coe]; exact h)

private lemma s16c11_v1_ten_mem_fixV_iff (v : coreMod 10) :
    v ∈ fixV s16c11_v1_blocks_ten ↔
      permAct 10 s16c11_v1_p123_ten (v : PermMod 10) = (v : PermMod 10) ∧
        permAct 10 s16c11_v1_p456_ten (v : PermMod 10) = (v : PermMod 10) := by
  change (∀ x ∈ s16c11_v1_blocks_ten, x v = v) ↔
    permAct 10 s16c11_v1_p123_ten (v : PermMod 10) = (v : PermMod 10) ∧
      permAct 10 s16c11_v1_p456_ten (v : PermMod 10) = (v : PermMod 10)
  constructor
  · intro h
    refine ⟨?_, ?_⟩ <;> rw [← s16c11_v1_ten_coreAct_fix_iff] <;>
      exact h _ (Subgroup.mem_map.mpr ⟨_, Subgroup.subset_closure (by simp), rfl⟩)
  · rintro ⟨h1, h2⟩ x hx
    let T : Subgroup (Equiv.Perm (Fin 10)) :=
      { carrier := {σ | coreAct 10 σ v = v}
        one_mem' := by simp
        mul_mem' := by
          intro σ τ hσ hτ
          have hσ' : coreAct 10 σ v = v := hσ
          have hτ' : coreAct 10 τ v = v := hτ
          change coreAct 10 (σ * τ) v = v
          rw [map_mul]
          show (coreAct 10 σ) ((coreAct 10 τ) v) = v
          rw [hτ', hσ']
        inv_mem' := by
          intro σ hσ
          have hσ' : coreAct 10 σ v = v := hσ
          change coreAct 10 σ⁻¹ v = v
          rw [map_inv]
          apply (coreAct 10 σ).injective
          rw [MulAut.inv_apply, MulEquiv.apply_symm_apply, hσ'] }
    have hTle : Subgroup.closure ({s16c11_v1_p123_ten, s16c11_v1_p456_ten} :
        Set (Equiv.Perm (Fin 10))) ≤ T := by
      rw [Subgroup.closure_le]
      rintro σ (rfl | rfl)
      · exact (s16c11_v1_ten_coreAct_fix_iff _ v).mpr h1
      · exact (s16c11_v1_ten_coreAct_fix_iff _ v).mpr h2
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hx
    exact hTle hσ

private noncomputable def s16c11_v1_ten_fixEquiv :
    ↥(fixV s16c11_v1_blocks_ten) ≃ ↥s16c11_v1_ten_fixFinset where
  toFun v := ⟨(v.1 : PermMod 10), by
    simp only [s16c11_v1_ten_fixFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    obtain ⟨h1, h2⟩ := (s16c11_v1_ten_mem_fixV_iff v.1).mp v.2
    exact ⟨mem_coreMod.mp v.1.2, h1, h2⟩⟩
  invFun w := ⟨⟨w.1, mem_coreMod.mpr (by
      have hw : (∑ i, Multiplicative.toAdd w.1 i = 0) ∧
          permAct 10 s16c11_v1_p123_ten w.1 = w.1 ∧
            permAct 10 s16c11_v1_p456_ten w.1 = w.1 := by
        simpa only [s16c11_v1_ten_fixFinset, Finset.mem_filter, Finset.mem_univ, true_and]
          using w.2
      exact hw.1)⟩,
    (s16c11_v1_ten_mem_fixV_iff _).mpr (by
      have hw : (∑ i, Multiplicative.toAdd w.1 i = 0) ∧
          permAct 10 s16c11_v1_p123_ten w.1 = w.1 ∧
            permAct 10 s16c11_v1_p456_ten w.1 = w.1 := by
        simpa only [s16c11_v1_ten_fixFinset, Finset.mem_filter, Finset.mem_univ, true_and]
          using w.2
      exact ⟨hw.2.1, hw.2.2⟩)⟩
  left_inv v := Subtype.ext rfl
  right_inv w := Subtype.ext rfl

theorem s16c11_v1_blocks_ten_fixV :
    Nat.card ↥(fixV s16c11_v1_blocks_ten) = 2 ^ 5 := by
  rw [Nat.card_congr s16c11_v1_ten_fixEquiv, Nat.card_eq_fintype_card, Fintype.card_coe,
    s16c11_v1_ten_fixFinset_card]

private lemma s16c11_v1_p123_ten_isThreeCycle : s16c11_v1_p123_ten.IsThreeCycle := by
  rw [s16c11_v1_p123_ten, Equiv.swap_comm 0 1]
  exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

private lemma s16c11_v1_p456_ten_isThreeCycle : s16c11_v1_p456_ten.IsThreeCycle := by
  rw [s16c11_v1_p456_ten, Equiv.swap_comm 3 4]
  exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

private lemma s16c11_v1_p123_p456_disjoint :
    s16c11_v1_p123_ten.Disjoint s16c11_v1_p456_ten := by
  rw [Equiv.Perm.disjoint_iff_eq_or_eq]
  decide +kernel

private lemma s16c11_v1_p123_ten_pow_three : s16c11_v1_p123_ten ^ 3 = 1 := by
  decide +kernel

private lemma s16c11_v1_p456_ten_pow_three : s16c11_v1_p456_ten ^ 3 = 1 := by
  decide +kernel

private lemma s16c11_v1_closure_pair_card :
    Nat.card ↥(Subgroup.closure ({s16c11_v1_p123_ten, s16c11_v1_p456_ten} :
      Set (Equiv.Perm (Fin 10)))) = 9 := by
  exact CFSG.GF2Type.Smith1979W3.CaseD.card_closure_threeCycles
    s16c11_v1_p123_ten_isThreeCycle s16c11_v1_p456_ten_isThreeCycle
    s16c11_v1_p123_p456_disjoint

private lemma s16c11_v1_closure_pair_isElementaryAbelian :
    IsElementaryAbelian 3 ↥(Subgroup.closure ({s16c11_v1_p123_ten, s16c11_v1_p456_ten} :
      Set (Equiv.Perm (Fin 10)))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hC : IsElementaryAbelian 3 ↥(Subgroup.zpowers s16c11_v1_p123_ten) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (p := 3) s16c11_v1_p123_ten_pow_three
  have hD : IsElementaryAbelian 3 ↥(Subgroup.zpowers s16c11_v1_p456_ten) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (p := 3) s16c11_v1_p456_ten_pow_three
  have hle : Subgroup.zpowers s16c11_v1_p456_ten ≤
      Subgroup.centralizer
        (Subgroup.zpowers s16c11_v1_p123_ten : Set (Equiv.Perm (Fin 10))) := by
    rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    simpa using
      ((s16c11_v1_p123_p456_disjoint.commute).symm.zpow_zpow n 1).eq
  have hsup := by
    letI := hC
    letI := hD
    exact IsElementaryAbelian.sup_of_le_centralizer (p := 3) hle
  have hCD : (Subgroup.zpowers s16c11_v1_p123_ten ⊔
        Subgroup.zpowers s16c11_v1_p456_ten : Subgroup (Equiv.Perm (Fin 10))) =
      Subgroup.closure ({s16c11_v1_p123_ten, s16c11_v1_p456_ten} :
        Set (Equiv.Perm (Fin 10))) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
  rw [hCD] at hsup
  exact hsup

theorem s16c11_v1_blocks_ten_of_realizes {J : Type} [CommGroup J] [Finite J]
    (hJ : ∀ j : J, j ^ 2 = 1) {H : Subgroup (MulAut J)}
    (hReal : (altCoreModel 10).Realizes H ⊤ ⊥) :
    ∃ E : Subgroup (MulAut J), E ≤ H ∧ IsPGroup 3 ↥E ∧ ¬ IsCyclic ↥E ∧
      Nat.card ↥(fixV E) = 2 ^ 5 := by
  let B : Subgroup (Equiv.Perm (Fin 10)) :=
    Subgroup.closure ({s16c11_v1_p123_ten, s16c11_v1_p456_ten} :
      Set (Equiv.Perm (Fin 10)))
  have hBcard : Nat.card ↥B = 9 := s16c11_v1_closure_pair_card
  have hBEA : IsElementaryAbelian 3 ↥B := s16c11_v1_closure_pair_isElementaryAbelian
  have hBle : B ≤ alternatingGroup (Fin 10) := by
    rw [show B = Subgroup.closure
      ({s16c11_v1_p123_ten, s16c11_v1_p456_ten} : Set (Equiv.Perm (Fin 10))) from rfl]
    rw [Subgroup.closure_le]
    intro σ hσ
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
    rcases hσ with rfl | rfl
    · exact Equiv.Perm.mem_alternatingGroup.mpr s16c11_v1_p123_ten_isThreeCycle.sign
    · exact Equiv.Perm.mem_alternatingGroup.mpr s16c11_v1_p456_ten_isThreeCycle.sign
  obtain ⟨E, hEH, hEiso, hEcard⟩ :=
    s16c11_v1_fixV_card_of_realizes (n := 10) (J := J) (by norm_num) hReal B hBle
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBp : IsPGroup 3 ↥B := by
    haveI := hBEA
    exact IsElementaryAbelian.isPGroup 3 ↥B
  have hBc : ¬ IsCyclic ↥B := by
    haveI := hBEA
    exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 3)
      (by rw [hBcard]; norm_num)
  refine ⟨E, hEH, ?_, ?_, ?_⟩
  · obtain ⟨e⟩ := hEiso
    exact hBp.of_equiv e.symm
  · obtain ⟨e⟩ := hEiso
    exact fun hc => hBc ((MulEquiv.isCyclic e).mp hc)
  · rw [hEcard]
    exact s16c11_v1_blocks_ten_fixV

private theorem s16c11_v1_ten_coreAct_injective : Function.Injective (G6.coreAct 10) :=
  CFSG.CGT.PushingUpLit.BHS.coreAct_injective (n := 10) (by norm_num)

private lemma s16c11_v1_ten_zmod2_eq_add_one {a b : ZMod 2} (h : a = b + 1) : b = a + 1 := by
  rw [h]
  exact (by decide : ∀ c : ZMod 2, c = (c + 1) + 1) b

private lemma s16c11_v1_ten_not_shift {x : Fin 10 → ZMod 2} (hx : ∑ i, x i = 0)
    (σ : Equiv.Perm (Fin 10)) (h : ∀ i, x (σ⁻¹ i) = x i + 1) : False := by
  classical
  let S : Set (Fin 10) := {i | x i = 1}
  have hxS : x = fun i => if i ∈ S then 1 else 0 := by
    funext i
    by_cases hi : i ∈ S
    · rw [if_pos hi]; exact hi
    · rw [if_neg hi]
      rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (x i) with h0 | h1
      · exact h0
      · exact absurd h1 hi
  have hσj : ∀ j, x (σ j) = x j + 1 := by
    intro j
    have hj := h (σ j)
    rw [show σ⁻¹ (σ j) = j from Equiv.symm_apply_apply σ j] at hj
    exact s16c11_v1_ten_zmod2_eq_add_one hj
  have hiff : ∀ j, j ∈ S ↔ σ j ∉ S := by
    intro j
    change x j = 1 ↔ x (σ j) ≠ 1
    constructor
    · intro hj hσj'
      rw [hσj j, hj] at hσj'
      exact absurd hσj' (by decide)
    · intro hj
      by_contra hx1
      have hx0 : x j = 0 := by
        rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (x j) with h0 | h1
        · exact h0
        · exact absurd h1 hx1
      have h1 : x (σ j) = 0 + 1 := by
        rw [← hx0]; exact hσj j
      exact hj (by simpa using h1)
  have hcompl : σ '' S = Sᶜ := by
    ext i
    rw [Set.mem_image]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact (hiff j).mp hj
    · intro hi
      exact ⟨σ⁻¹ i, (hiff (σ⁻¹ i)).mpr (by simpa using hi), by simp⟩
  have hcardS : S.ncard = 5 := by
    have himg : (σ '' S).ncard = S.ncard := Set.ncard_image_of_injective S σ.injective
    have hc : (Sᶜ).ncard = Nat.card (Fin 10) - S.ncard := Set.ncard_compl S
    have h2 : S.ncard = 10 - S.ncard := by
      have h1 : S.ncard = (Sᶜ).ncard := by rw [← himg, hcompl]
      calc S.ncard = (Sᶜ).ncard := h1
        _ = Nat.card (Fin 10) - S.ncard := hc
        _ = 10 - S.ncard := by rw [Nat.card_fin]
    have hle : S.ncard ≤ 10 := by simpa using Set.ncard_le_card (s := S)
    omega
  have hsum : ∑ i, x i = (S.ncard : ZMod 2) := by
    rw [hxS, Finset.sum_boole]
    congr 1
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext i
    simp
  rw [hsum, hcardS] at hx
  exact (by decide : ¬ ((5 : ZMod 2) = 0)) hx

private lemma s16c11_v1_ten_class_property {P : Subgroup (Equiv.Perm (Fin 10))}
    (hVP : ∀ Q : Subgroup (Equiv.Perm (Fin 10)), Q ≤ P → Q.relIndex P ≤ 2 →
      fixV (Q.map (G6.coreAct 10)) = fixV (P.map (G6.coreAct 10))) :
    ∀ B : Subgroup (Equiv.Perm (Fin 10)), B ≤ P → B.relIndex P ≤ 2 →
      ∀ q : (FFModel.symDn 10).Mod,
        (∀ σ ∈ B, (FFModel.symDn_isActionModel 10).modAct σ q = q) →
          ∀ σ ∈ P, (FFModel.symDn_isActionModel 10).modAct σ q = q := by
  intro B hB hBrel q hqfix σ hσ
  obtain ⟨x, hx, hq⟩ := s16c11BigCls_surjective 10 q
  rw [hq] at hqfix ⊢
  have hxfixed : ∀ τ ∈ B, (fun i => x (τ⁻¹ i)) = x := by
    intro τ hτ
    have h1 : (FFModel.symDn_isActionModel 10).modAct τ (s16c11BigCls 10 x hx) =
        s16c11BigCls 10 x hx := hqfix τ hτ
    rw [s16c11BigCls_modAct 10 τ (x := x) (hx := hx)
      (hx' := by rw [Equiv.sum_comp]; exact hx)] at h1
    rcases (s16c11BigCls_eq_iff).mp h1 with h | h
    · exact h.symm
    · exfalso
      refine s16c11_v1_ten_not_shift hx τ (fun i => ?_)
      have hi := congrFun h i
      exact s16c11_v1_ten_zmod2_eq_add_one hi
  have huB : (⟨Multiplicative.ofAdd x, hx⟩ : coreMod 10) ∈
      fixV (B.map (G6.coreAct 10)) := by
    rw [mem_fixV]
    intro z hz
    obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp hz
    apply Subtype.ext
    change G6.permAct 10 τ (Multiplicative.ofAdd x) = Multiplicative.ofAdd x
    change Multiplicative.ofAdd (fun i => x (τ⁻¹ i)) = Multiplicative.ofAdd x
    rw [hxfixed τ hτ]
  have huP : (⟨Multiplicative.ofAdd x, hx⟩ : coreMod 10) ∈
      fixV (P.map (G6.coreAct 10)) := by
    rw [← hVP B hB hBrel]; exact huB
  have hσfix : G6.coreAct 10 σ (⟨Multiplicative.ofAdd x, hx⟩ : coreMod 10) =
      ⟨Multiplicative.ofAdd x, hx⟩ :=
    (mem_fixV.mp huP) (G6.coreAct 10 σ) (Subgroup.mem_map.mpr ⟨σ, hσ, rfl⟩)
  rw [s16c11BigCls_modAct 10 σ (x := x) (hx := hx)
    (hx' := by rw [Equiv.sum_comp]; exact hx)]
  apply s16c11BigCls_eq_iff.mpr
  left
  funext i
  have hp : G6.permAct 10 σ (Multiplicative.ofAdd x) = Multiplicative.ofAdd x := by
    have h := congrArg Subtype.val hσfix
    change G6.permAct 10 σ (Multiplicative.ofAdd x) = Multiplicative.ofAdd x at h
    exact h
  have h := congrFun (congrArg Multiplicative.toAdd hp) i
  change Multiplicative.toAdd (G6.permAct 10 σ (Multiplicative.ofAdd x)) i =
    Multiplicative.toAdd (Multiplicative.ofAdd x) i at h
  rw [G6.permAct_apply] at h
  exact h.symm

private def s16c11_v1_ten_coreFinset : Finset (PermMod 10) :=
  Finset.univ.filter fun v => ∑ i, Multiplicative.toAdd v i = 0

private lemma s16c11_v1_ten_coreFinset_card : s16c11_v1_ten_coreFinset.card = 2 ^ 9 := by
  simp only [s16c11_v1_ten_coreFinset]
  decide +kernel

private noncomputable def s16c11_v1_ten_coreEquiv :
    ↥(coreMod 10) ≃ ↥s16c11_v1_ten_coreFinset where
  toFun v := ⟨(v : PermMod 10), by
    simp only [s16c11_v1_ten_coreFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact mem_coreMod.mp v.2⟩
  invFun w := ⟨w.1, mem_coreMod.mpr (by
    have hw := w.2
    simpa only [s16c11_v1_ten_coreFinset, Finset.mem_filter, Finset.mem_univ, true_and] using hw)⟩
  left_inv v := Subtype.ext rfl
  right_inv w := Subtype.ext rfl

private lemma s16c11_v1_ten_card_coreMod : Nat.card ↥(coreMod 10) = 2 ^ 9 := by
  rw [Nat.card_congr s16c11_v1_ten_coreEquiv, Nat.card_eq_fintype_card, Fintype.card_coe,
    s16c11_v1_ten_coreFinset_card]

theorem s16c11_v1_coreMod_ten_dimD1 {E : Subgroup (MulAut ↥(coreMod 10))}
    (hE : E ∈ E3.aSet 2 (G6.coreAct 10).range)
    (h2 : IsPGroup 2 ↥E) (hEne : E ≠ ⊥) :
    4 ≤ rkIdx (fixV E) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcore : Nat.card ↥(coreMod 10) = 2 ^ 9 := s16c11_v1_ten_card_coreMod
  have hpg : IsPGroup 2 ↥(coreMod 10) := IsPGroup.of_card (n := 9) hcore
  let P : Subgroup (Equiv.Perm (Fin 10)) := E.comap (G6.coreAct 10)
  have hPmap : P.map (G6.coreAct 10) = E := Subgroup.map_comap_eq_self hE.1
  have hPne : P ≠ ⊥ := by
    intro hbot
    have hEbot : E = ⊥ := by
      calc E = P.map (G6.coreAct 10) := hPmap.symm
        _ = (⊥ : Subgroup (Equiv.Perm (Fin 10))).map (G6.coreAct 10) := by rw [hbot]
        _ = ⊥ := Subgroup.map_bot _
    exact hEne hEbot
  have hPab : CFSG.Open.IsElemAbelian 2 P := by
    refine ⟨IsMulCommutative.of_comm (fun a b => ?_), ?_⟩
    · apply Subtype.ext
      apply s16c11_v1_ten_coreAct_injective
      change G6.coreAct 10 ((a : Equiv.Perm (Fin 10)) * (b : Equiv.Perm (Fin 10))) =
        G6.coreAct 10 ((b : Equiv.Perm (Fin 10)) * (a : Equiv.Perm (Fin 10)))
      rw [map_mul, map_mul]
      exact hE.2.2.1.1 (G6.coreAct 10 a) (Subgroup.mem_comap.mp a.2)
        (G6.coreAct 10 b) (Subgroup.mem_comap.mp b.2)
    · intro x hx
      apply s16c11_v1_ten_coreAct_injective
      change G6.coreAct 10 (x ^ 2) = G6.coreAct 10 (1 : Equiv.Perm (Fin 10))
      rw [map_pow, map_one]
      exact hE.2.2.1.2 (G6.coreAct 10 x) (Subgroup.mem_comap.mp hx)
  have hVP : ∀ Q : Subgroup (Equiv.Perm (Fin 10)), Q ≤ P → Q.relIndex P ≤ 2 →
      fixV (Q.map (G6.coreAct 10)) = fixV (P.map (G6.coreAct 10)) := by
    intro Q hQ hQrel
    have hQmap : Q.map (G6.coreAct 10) ≤ E := hPmap ▸ Subgroup.map_mono hQ
    have hrel : (Q.map (G6.coreAct 10)).relIndex E = Q.relIndex P :=
      hPmap ▸ Subgroup.relIndex_map_map_of_injective Q P s16c11_v1_ten_coreAct_injective
    have hmq : E3.mQuot E (Q.map (G6.coreAct 10)) < 2 := by
      unfold E3.mQuot
      rw [hrel]
      rcases eq_or_ne (Q.relIndex P) 0 with h0 | h0
      · rw [h0]; norm_num
      · by_contra hlt
        have hle2 : 2 ≤ padicValNat 2 (Q.relIndex P) := not_lt.1 hlt
        have h4 : 4 ∣ Q.relIndex P :=
          (padicValNat_dvd_iff_le (p := 2) (a := Q.relIndex P) (n := 2) h0).2 hle2
        omega
    exact (hE.2.2.2 (Q.map (G6.coreAct 10)) hQmap hmq).trans (congrArg fixV hPmap).symm
  obtain ⟨j, hj_ne, hj_inv, hj_or, hj_surj⟩ :=
    s16c11_big_a2_orbits (Or.inr rfl) hPab hPne (s16c11_v1_ten_class_property hVP)
  let T : Finset (Fin 10) := Finset.univ.filter fun i => i < j i
  have hmemT : ∀ i : Fin 10, i ∈ T ↔ i < j i := by intro i; simp [T]
  have hnotmemT : ∀ i : Fin 10, i ∉ T ↔ j i < i := by
    intro i
    rw [hmemT, not_lt]
    exact ⟨fun h => lt_of_le_of_ne h (hj_ne i), fun h => h.le⟩
  have hTcard : T.card = 5 := by
    have himg : T.image j = Tᶜ := by
      ext b
      rw [Finset.mem_image, Finset.mem_compl]
      constructor
      · rintro ⟨a, ha, rfl⟩
        rw [hnotmemT, hj_inv a]
        exact (hmemT a).mp ha
      · intro hb
        refine ⟨j b, ?_, hj_inv b⟩
        rw [hmemT, hj_inv b]
        exact (hnotmemT b).mp hb
    have hcard : Tᶜ.card = T.card := by
      rw [← himg, Finset.card_image_of_injective _ j.injective]
    have hsum := Finset.card_add_card_compl T
    rw [Fintype.card_fin] at hsum
    omega
  have hfix_j : ∀ v : ↥(fixV E), ∀ i : Fin 10,
      (v.1 : PermMod 10) (j i) = (v.1 : PermMod 10) i := by
    intro v i
    obtain ⟨τ, hτ, hτi⟩ := hj_surj i
    have hv := (mem_fixV.mp v.2) (G6.coreAct 10 τ)
      (hPmap ▸ Subgroup.mem_map.mpr ⟨τ, hτ, rfl⟩)
    have hv' : G6.permAct 10 τ (v.1 : PermMod 10) = (v.1 : PermMod 10) := by
      have h := congrArg Subtype.val hv
      change G6.permAct 10 τ (v.1 : PermMod 10) = (v.1 : PermMod 10) at h
      exact h
    have h1 : (v.1 : PermMod 10) (τ⁻¹ i) = (v.1 : PermMod 10) i := by
      have h2 := congrFun (congrArg Multiplicative.toAdd hv') i
      change Multiplicative.toAdd (G6.permAct 10 τ (v.1 : PermMod 10)) i =
        Multiplicative.toAdd (v.1 : PermMod 10) i at h2
      rw [G6.permAct_apply] at h2
      exact h2
    have hτi' : τ⁻¹ i = j i := by
      have hτj : τ (j i) = i := by
        have hpow : τ ^ 2 = 1 := hPab.2 τ hτ
        calc τ (j i) = τ (τ i) := by rw [hτi]
          _ = i := by
            have h2 : (τ ^ 2) i = i := by rw [hpow]; rfl
            simpa [pow_two] using h2
      have h3 : τ⁻¹ i = τ⁻¹ (τ (j i)) := by rw [hτj]
      simpa using h3
    rw [← hτi']; exact h1
  have hinj : Function.Injective
      (fun v : ↥(fixV E) => fun t : ↥T => (v.1 : PermMod 10) t.1) := by
    intro v w hvw
    apply Subtype.ext
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ T
    · exact congrFun hvw ⟨i, hi⟩
    · have hji : j i ∈ T := by
        rw [hmemT, hj_inv i]
        exact (hnotmemT i).mp hi
      have h1 : (v.1 : PermMod 10) (j i) = (w.1 : PermMod 10) (j i) :=
        congrFun hvw ⟨j i, hji⟩
      calc (v.1 : PermMod 10) i = (v.1 : PermMod 10) (j i) := (hfix_j v i).symm
        _ = (w.1 : PermMod 10) (j i) := h1
        _ = (w.1 : PermMod 10) i := hfix_j w i
  have hcard_le : Nat.card ↥(fixV E) ≤ 2 ^ 5 := by
    calc Nat.card ↥(fixV E) ≤ Nat.card (↥T → ZMod 2) :=
          Nat.card_le_card_of_injective _ hinj
      _ = 2 ^ Nat.card ↥T := by rw [Nat.card_fun, Nat.card_zmod]
      _ = 2 ^ 5 := by rw [Nat.card_eq_fintype_card, Fintype.card_coe, hTcard]
  have hmul : Nat.card ↥(fixV E) * (fixV E).index = 2 ^ 9 := by
    rw [Subgroup.card_mul_index (fixV E), hcore]
  have hidx_ge : 2 ^ 4 ≤ (fixV E).index := by
    by_contra h
    have hi : (fixV E).index ≤ 2 ^ 4 - 1 := by omega
    have hclt : Nat.card ↥(fixV E) * (fixV E).index ≤ 2 ^ 5 * (2 ^ 4 - 1) :=
      Nat.mul_le_mul hcard_le hi
    rw [hmul] at hclt
    norm_num at hclt
  have hidx_dvd : (fixV E).index ∣ 2 ^ 9 := ⟨Nat.card ↥(fixV E), by rw [mul_comm, hmul]⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hidx_dvd
  have hk4 : 4 ≤ k := by
    rw [hk] at hidx_ge
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hidx_ge
  unfold rkIdx
  rw [hk, padicValNat.prime_pow]
  exact hk4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
