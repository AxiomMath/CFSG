module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirteenBoundsAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirteenProof
public import CFSG.LocalAnalysis.WeakClosure81.FiveFiveFstar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourElevenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.WeakClosure81 CFSG.Quasithin
open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]


@[expose] def shapeIndex (q : ℕ) : ℕ := if 9 < q then 1 else if q = 9 then 3 else 2

@[expose] def OddComponentShape (q : ℕ) (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ (∃ a b : X, a * b ≠ b * a) ∧
    ((∃ q' : ℕ, IsL2Over17 X q' ∧ (q' = q ∨ q' = q ^ 3) ∧ 3 < q') ∨
      (IsL3EpsOdd17 X q ∧ 3 < q))

theorem shapeIndex_of_gt {q : ℕ} (h : 9 < q) : shapeIndex q = 1 := by
  simp only [shapeIndex, h, if_true]

theorem shapeIndex_of_eq {q : ℕ} (h : q = 9) : shapeIndex q = 3 := by
  subst h
  simp only [shapeIndex, lt_irrefl, if_false, if_true]

theorem shapeIndex_of_le {q : ℕ} (h : ¬ 9 < q) (h9 : q ≠ 9) : shapeIndex q = 2 := by
  simp only [shapeIndex, h, if_false, h9, if_false]

theorem one_le_shapeIndex (q : ℕ) : 1 ≤ shapeIndex q := by
  unfold shapeIndex
  split_ifs <;> omega

theorem inFGroup_shapeIndex_of_w4Lem4_11 (h411 : W4Lem4_11Prime)
    {A : Type} [Group A] [Finite A] {L : Subgroup A} [L.Normal] {q : ℕ}
    (hnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hF : Fstar (⊤ : Subgroup A) = L) (hL3 : IsL3EpsOdd17 ↥L q) (hq3 : 3 < q)
    {T : Subgroup A} (hT : IsSylowIn 2 T ⊤) (hsup : L ⊔ T = ⊤) :
    InFGroup (shapeIndex q) A := by
  have hp : q.Prime := by rcases hL3 with h | h <;> exact h.admissible.1
  rcases h411 A L q ⟨inferInstance, hF, hp, by omega, hL3, hnab, fun h => absurd h (by omega),
      ⟨T, hT, hsup⟩⟩ with h1 | ⟨rfl, h2⟩
  · exact inFGroup_mono (one_le_shapeIndex q) h1
  · rwa [shapeIndex_of_le (q := 5) (by norm_num) (by norm_num)]

theorem inFGroup_of_oddShape (h410 : W4Lem4_10)
    (hrank57 : CFSG.ComponentClassification.GSThmB.CFAutL2Rank)
    (hrankAll : CFSG.ComponentClassification.GSThmB.CFL2Rank)
    (h411 : W4Lem4_11Prime)
    {A : Type} [Group A] [Finite A] {L : Subgroup A} [L.Normal] {q : ℕ}
    (hC : Subgroup.centralizer (L : Set A) = ⊥)
    (hquot : IsPGroup 2 (A ⧸ L)) (hodd : Odd q) (hq3 : 3 < q)
    (hshape : OddComponentShape q ↥L) :
    InFGroup (shapeIndex q) A := by
  obtain ⟨hsimple, hnab, hshape⟩ := hshape
  have hF : Fstar (⊤ : Subgroup A) = L := by
    refine CFSG.LocalAnalysis.WeakClosure81.fstar_eq_of_isSimpleGroup_of_centralizer_eq_bot
      le_top (Subgroup.Normal.subgroupOf inferInstance ⊤) hsimple ?_ (by rw [hC, inf_bot_eq])
    rintro h
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (Subtype.ext (h a a.2 b b.2))
  rcases hshape with ⟨q', hL2, hq', hq'3⟩ | ⟨hL3, hq3'⟩
  · have htriple :=
      inFGroup_of_almostSimple_l2Odd h410 hrank57 hrankAll hF hC hL2 hq'3 (by
        rcases hq' with hq' | hq'
        · rw [hq']; exact hodd
        · rw [hq']; exact hodd.pow) hquot
    have hmem : InFGroup (shapeIndex q') A := by
      by_cases h9 : 9 < q'
      · rw [shapeIndex_of_gt h9]; exact htriple.1 h9
      · by_cases hq9 : q' = 9
        · rw [shapeIndex_of_eq hq9]; exact htriple.2.2 hq9
        · rw [shapeIndex_of_le h9 hq9]; exact htriple.2.1 (by omega) hq9
    rcases hq' with hq' | hq'
    · rw [hq'] at hmem; exact hmem
    · rw [hq'] at hmem
      have hq3pos : 9 < q ^ 3 := by
        have h3 : 3 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left (by omega) 3
        norm_num at h3
        omega
      have h1 : InFGroup 1 A := by rw [shapeIndex_of_gt hq3pos] at hmem; exact hmem
      exact inFGroup_mono (one_le_shapeIndex q) h1
  · obtain ⟨T⟩ := Sylow.nonempty (p := 2) (G := A)
    have hTsyl : IsSylowIn 2 (T : Subgroup A) ⊤ := isSylowIn_top T
    have hsup : L ⊔ (T : Subgroup A) = ⊤ :=
      CFSG.OrderReductions.PrimeQuotientFrattini.kernel_sup_sylow_eq_top 2 L hquot T
    exact inFGroup_shapeIndex_of_w4Lem4_11 h411 hnab hF hL3 hq3' hTsyl hsup

theorem inFGroup_quot_of_normal_simple_odd {N : Type} [Group N] [Finite N]
    {L K C : Subgroup N} [L.Normal] [C.Normal] {q : ℕ}
    (hC : C = Subgroup.centralizer (L : Set N))
    (hK2 : IsPGroup 2 K) (hsup : L ⊔ K = ⊤)
    (hshape : OddComponentShape q ↥L) (hodd : Odd q) (hq3 : 3 < q)
    (h410 : W4Lem4_10)
    (hrank57 : CFSG.ComponentClassification.GSThmB.CFAutL2Rank)
    (hrankAll : CFSG.ComponentClassification.GSThmB.CFL2Rank)
    (h411 : W4Lem4_11Prime) :
    InFGroup (shapeIndex q) (N ⧸ C) := by
  classical
  obtain ⟨hsimple, hnab, hshape⟩ := hshape
  have hcenter : Subgroup.center ↥L = ⊥ :=
    CFSG.Quasithin.Vol2.Ch11.SecE3.center_eq_bot_of_simple hnab
  have hLC : L ⊓ C = ⊥ := by
    rw [hC]
    refine le_bot_iff.mp ?_
    rintro x ⟨hxL, hxC⟩
    have hx' : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC (y : N) y.2)
    rw [hcenter] at hx'
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hx')
  let mk : N →* N ⧸ C := QuotientGroup.mk' C
  let Lbar : Subgroup (N ⧸ C) := L.map mk
  let f : ↥L →* ↥Lbar :=
    (mk.comp L.subtype).codRestrict Lbar (fun x => Subgroup.mem_map.mpr ⟨(x : N), x.2, rfl⟩)
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have h1 : mk ((x : N)⁻¹ * (y : N)) = 1 := by
      have h2 : mk (x : N) = mk (y : N) := congrArg (fun z : ↥Lbar => (z : N ⧸ C)) hxy
      rw [map_mul, map_inv, h2, inv_mul_cancel]
    have h2 : (x : N)⁻¹ * (y : N) ∈ C := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : (x : N)⁻¹ * (y : N) ∈ L := L.mul_mem (L.inv_mem x.2) y.2
    have h4 : (x : N)⁻¹ * (y : N) = 1 := by
      have h5 : (x : N)⁻¹ * (y : N) ∈ L ⊓ C := ⟨h3, h2⟩
      rw [hLC] at h5
      exact Subgroup.mem_bot.mp h5
    exact Subtype.ext (inv_mul_eq_one.mp h4)
  have hf_surj : Function.Surjective f := by
    intro y
    obtain ⟨x, hxL, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hxL⟩, Subtype.ext hxy⟩
  let e : ↥L ≃* ↥Lbar := MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hLbar_normal : Lbar.Normal :=
    Subgroup.Normal.map inferInstance mk (QuotientGroup.mk'_surjective C)
  have hsimple_bar : IsSimpleGroup ↥Lbar := e.isSimpleGroup_congr.mp hsimple
  have hnab_bar : ∃ a b : ↥Lbar, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨e a, e b, fun h => hab ?_⟩
    exact e.injective (by rw [map_mul, map_mul]; exact h)
  have hCbar : Subgroup.centralizer (Lbar : Set (N ⧸ C)) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective a
    have hn : n ∈ C := by
      rw [hC]
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hmem : mk l ∈ Lbar := Subgroup.mem_map.mpr ⟨l, hl, rfl⟩
      have hcomm := Subgroup.mem_centralizer_iff.mp ha (mk l) hmem
      have hcomm' : mk n * mk l = mk l * mk n := hcomm.symm
      have h1 : mk (n * l * n⁻¹ * l⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        rw [hcomm']
        group
      have h2 : n * l * n⁻¹ * l⁻¹ ∈ C := (QuotientGroup.eq_one_iff _).mp h1
      have h3 : n * l * n⁻¹ * l⁻¹ ∈ L :=
        L.mul_mem ((inferInstance : L.Normal).conj_mem l hl n) (L.inv_mem hl)
      have h4 : n * l * n⁻¹ * l⁻¹ = 1 := by
        have h5 : n * l * n⁻¹ * l⁻¹ ∈ L ⊓ C := ⟨h3, h2⟩
        rw [hLC] at h5
        exact Subgroup.mem_bot.mp h5
      have h5 : n * l * n⁻¹ = l := mul_inv_eq_one.mp h4
      have h6 : n * l = l * n := by
        calc n * l = (n * l * n⁻¹) * n := by group
          _ = l * n := by rw [h5]
      exact h6.symm
    exact (QuotientGroup.eq_one_iff n).mpr hn
  have hquot : IsPGroup 2 ((N ⧸ C) ⧸ Lbar) := by
    have hsurj : Function.Surjective
        ((QuotientGroup.mk' Lbar).comp ((QuotientGroup.mk' C).comp K.subtype)) := by
      intro x
      obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective x
      obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective a
      have hmem : n ∈ L ⊔ K := by rw [hsup]; exact Subgroup.mem_top n
      obtain ⟨l, hl, k, hk, hlk⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
      have hlbar : (QuotientGroup.mk' C) l ∈ Lbar := Subgroup.mem_map.mpr ⟨l, hl, rfl⟩
      have hkill : (QuotientGroup.mk' Lbar) ((QuotientGroup.mk' C) l) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hlbar
      have h1 : (QuotientGroup.mk' Lbar) ((QuotientGroup.mk' C) (l * k))
          = (QuotientGroup.mk' Lbar) ((QuotientGroup.mk' C) k) := by
        rw [map_mul (QuotientGroup.mk' C) l k, map_mul (QuotientGroup.mk' Lbar),
          hkill, one_mul]
      refine ⟨⟨k, hk⟩, ?_⟩
      show (QuotientGroup.mk' Lbar) ((QuotientGroup.mk' C) k) = x
      rw [← ha, ← hn, ← hlk]
      exact h1.symm
    exact IsPGroup.of_surjective hK2 _ hsurj
  have hshape_bar : OddComponentShape q ↥Lbar := by
    refine ⟨hsimple_bar, hnab_bar, ?_⟩
    rcases hshape with ⟨q', hL2, hq', hq3'⟩ | ⟨hL3, hq3'⟩
    · obtain ⟨p, f, hp, hp2, hq, hf, hm⟩ := hL2
      exact Or.inl ⟨q', ⟨p, f, hp, hp2, hq, hf, LieModel.of_mulEquiv e hm⟩, hq', hq3'⟩
    · rcases hL3 with hL3 | hL3
      · exact Or.inr ⟨Or.inl (LieModel.of_mulEquiv e hL3), hq3'⟩
      · exact Or.inr ⟨Or.inr (LieModel.of_mulEquiv e hL3), hq3'⟩
  exact inFGroup_of_oddShape h410 hrank57 hrankAll h411 hCbar hquot hodd hq3 hshape_bar

theorem cFAutInFGroup_of_oddShape {Q : Type} [Group Q] [Finite Q] (S : Subgroup Q) {q : ℕ}
    (hS2 : IsPGroup 2 S) (hodd : Odd q) (hq3 : 3 < q)
    (hshape : ∀ X : Subgroup Q, X.Normal → X ≠ ⊥ →
      (∀ N : Subgroup Q, N.Normal → N ≤ X → N = ⊥ ∨ N = X) → ¬ IsMulCommutative X →
      ∀ L : Subgroup Q, CFSG.Open.IsComponentOf L X → OddComponentShape q ↥L)
    (h410 : W4Lem4_10)
    (hrank57 : CFSG.ComponentClassification.GSThmB.CFAutL2Rank)
    (hrankAll : CFSG.ComponentClassification.GSThmB.CFL2Rank)
    (h411 : W4Lem4_11Prime) :
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.CFAutInFGroup (shapeIndex q) Q S := by
  intro X hX hXne hmin hnc L hL
  have hshapeL : OddComponentShape q ↥L := hshape X hX hXne hmin hnc L hL
  let N : Subgroup Q := F12.autNL S L
  let Lq : Subgroup ↥N := L.subgroupOf N
  let Kq : Subgroup ↥N := (S ⊓ Subgroup.normalizer (L : Set Q)).subgroupOf N
  have hKN : S ⊓ Subgroup.normalizer (L : Set Q) ≤ N := by
    show _ ≤ (S ⊓ Subgroup.normalizer (L : Set Q)) ⊔ L
    exact le_sup_left
  have hNL : N ≤ Subgroup.normalizer (L : Set Q) := by
    show (S ⊓ Subgroup.normalizer (L : Set Q)) ⊔ L ≤ _
    exact sup_le inf_le_right Subgroup.le_normalizer
  have hLq : Lq.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (show L ≤ N from le_sup_right)).mpr hNL
  have hKq2 : IsPGroup 2 Kq := by
    have h1 : IsPGroup 2 ↥(S ⊓ Subgroup.normalizer (L : Set Q)) := hS2.to_le inf_le_left
    let e : ↥Kq ≃* ↥(S ⊓ Subgroup.normalizer (L : Set Q)) :=
      Subgroup.subgroupOfEquivOfLe hKN
    exact IsPGroup.of_equiv h1 e.symm
  have hsup : Lq ⊔ Kq = ⊤ := by
    have hN : L ⊔ (S ⊓ Subgroup.normalizer (L : Set Q)) = N := by
      show L ⊔ (S ⊓ Subgroup.normalizer (L : Set Q)) =
        (S ⊓ Subgroup.normalizer (L : Set Q)) ⊔ L
      exact sup_comm ..
    have h1 : (L ⊔ (S ⊓ Subgroup.normalizer (L : Set Q))).subgroupOf N = Lq ⊔ Kq :=
      Subgroup.subgroupOf_sup (A := L) (A' := S ⊓ Subgroup.normalizer (L : Set Q))
        (B := N) le_sup_right le_sup_left
    rw [hN] at h1
    rw [← h1, Subgroup.subgroupOf_self]
  have hshapeLq : OddComponentShape q ↥Lq := by
    obtain ⟨hsimple, hnab, hrest⟩ := hshapeL
    have e : ↥Lq ≃* ↥L := Subgroup.subgroupOfEquivOfLe le_sup_right
    refine ⟨e.isSimpleGroup_congr.mpr hsimple, ?_, ?_⟩
    · obtain ⟨a, b, hab⟩ := hnab
      exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
    · rcases hrest with ⟨q', hL2, hq', hq3'⟩ | ⟨hL3, hq3'⟩
      · obtain ⟨p, f, hp, hp2, hq, hf, hm⟩ := hL2
        exact Or.inl ⟨q', ⟨p, f, hp, hp2, hq, hf,
          LieModel.of_mulEquiv e.symm hm⟩, hq', hq3'⟩
      · rcases hL3 with hL3 | hL3
        · exact Or.inr ⟨Or.inl (LieModel.of_mulEquiv e.symm hL3), hq3'⟩
        · exact Or.inr ⟨Or.inr (LieModel.of_mulEquiv e.symm hL3), hq3'⟩
  have hCeq : (F12.autC S L).subgroupOf N =
      Subgroup.centralizer (Lq : Set ↥N) := by
    ext x
    show (x : Q) ∈ F12.autC S L ↔ x ∈ Subgroup.centralizer (Lq : Set ↥N)
    simp only [F12.autC, F12.autNL, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨-, hc⟩ y hy
      exact Subtype.ext (hc (y : Q) hy)
    · intro hc
      refine ⟨x.2, fun y hy => ?_⟩
      have hyN : y ∈ N := by
        show y ∈ (S ⊓ Subgroup.normalizer (L : Set Q)) ⊔ L
        exact Subgroup.mem_sup_right hy
      let yN : ↥N := ⟨y, hyN⟩
      have hyLq : yN ∈ Lq := Subgroup.mem_subgroupOf.mpr hy
      exact congrArg Subtype.val (hc yN hyLq)
  have hCn : ((F12.autC S L).subgroupOf N).Normal :=
    hCeq ▸ Subgroup.normal_centralizer
  have hres := inFGroup_quot_of_normal_simple_odd (N := ↥N) (L := Lq) (K := Kq)
    (C := (F12.autC S L).subgroupOf N) (q := q) hCeq hKq2 hsup hshapeLq hodd hq3
    h410 hrank57 hrankAll h411
  exact ⟨hCeq ▸ Subgroup.normal_centralizer, hres⟩

theorem compFactorAutInF_of_oddShape {G : Type} [Group G] [Finite G] {H S : Subgroup G} {q : ℕ}
    (hSH : S ≤ H) (hS2 : IsPGroup 2 S) (hodd : Odd q) (hq3 : 3 < q)
    (hshape : ∀ (Y : Subgroup G), Y ≤ H → ∀ hY : (Y.subgroupOf H).Normal,
      ∀ X : Subgroup (↥H ⧸ Y.subgroupOf H), X.Normal → X ≠ ⊥ →
        (∀ N : Subgroup (↥H ⧸ Y.subgroupOf H), N.Normal → N ≤ X → N = ⊥ ∨ N = X) →
        ¬ IsMulCommutative X →
        ∀ L : Subgroup (↥H ⧸ Y.subgroupOf H), CFSG.Open.IsComponentOf L X →
          OddComponentShape q ↥L)
    (h410 : W4Lem4_10)
    (hrank57 : CFSG.ComponentClassification.GSThmB.CFAutL2Rank)
    (hrankAll : CFSG.ComponentClassification.GSThmB.CFL2Rank)
    (h411 : W4Lem4_11Prime) :
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.CompFactorAutInF (shapeIndex q) H S := by
  intro Y hY hYn
  let S' : Subgroup (↥H ⧸ Y.subgroupOf H) :=
    (S.subgroupOf H).map (QuotientGroup.mk' (Y.subgroupOf H))
  have hS'2 : IsPGroup 2 S' := by
    have h1 : IsPGroup 2 (S.subgroupOf H) :=
      hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
    exact IsPGroup.map h1 (QuotientGroup.mk' (Y.subgroupOf H))
  exact cFAutInFGroup_of_oddShape S' hS'2 hodd hq3 (fun X hX hXne hmin hnc L hL =>
    hshape Y hY hYn X hX hXne hmin hnc L hL) h410 hrank57 hrankAll h411

@[expose] def HasOddComponentShapes (Q : Type) [Group Q] [Finite Q] (q : ℕ) : Prop :=
  ∀ (Y : Subgroup Q) (hY : Y.Normal) (X : Subgroup (Q ⧸ Y)) (hXn : X.Normal) (hXne : X ≠ ⊥)
    (hXmin : ∀ N : Subgroup (Q ⧸ Y), N.Normal → N ≤ X → N = ⊥ ∨ N = X)
    (hXnc : ¬ IsMulCommutative X),
    ∀ L : Subgroup (Q ⧸ Y), CFSG.Open.IsComponentOf L X → OddComponentShape q ↥L

theorem compFactorAutInF_of_hasOddComponentShapes {Q : Type} [Group Q] [Finite Q]
    {T : Subgroup Q} {q : ℕ} (hT2 : IsPGroup 2 T) (hodd : Odd q) (hq3 : 3 < q)
    (hshape : HasOddComponentShapes (↥(⊤ : Subgroup Q)) q)
    (h410 : W4Lem4_10)
    (hrank57 : CFSG.ComponentClassification.GSThmB.CFAutL2Rank)
    (hrankAll : CFSG.ComponentClassification.GSThmB.CFL2Rank)
    (h411 : W4Lem4_11Prime) :
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.CompFactorAutInF (shapeIndex q) ⊤ T := by
  refine compFactorAutInF_of_oddShape (H := ⊤) (S := T) le_top hT2 hodd hq3 ?_ h410 hrank57
    hrankAll h411
  intro Y _ hY
  exact hshape (Y.subgroupOf ⊤) hY

@[expose] def Gap17_13_structure (D : Data G)
    (V₀ V L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  ∀ H ∈ Delta17_12 D (fundPred q) r q L,
    (∃ K : Subgroup (Bar2 H),
      CFSG.IsComponent K ∧
        orbitClosure K (CFSG.LocalAnalysis.WeakClosure81.barImage H D.T) ⊔
          CFSG.LocalAnalysis.WeakClosure81.barImage H D.T = ⊤) ∧
      HasOddComponentShapes (↥(⊤ : Subgroup (Bar2 H))) q

theorem gap17_13_diagonal_of (h410 : W4Lem4_10)
    (hrank57 : CFSG.ComponentClassification.GSThmB.CFAutL2Rank)
    (hrankAll : CFSG.ComponentClassification.GSThmB.CFL2Rank)
    (h411 : W4Lem4_11Prime)
    (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q)
    (h9 : R17_9At D V₀ V L r q hC)
    (hstr : Gap17_13_structure D V₀ V L r q hC) :
    Gap17_13_diagonal D V₀ V L r q hC := by
  intro H hH
  obtain ⟨⟨K, hK, hKT⟩, hshape⟩ := hstr H hH
  refine ⟨K, hK, hKT, ?_⟩
  obtain ⟨hr, hr2, t, n, f, hadm, hq, hm⟩ := hC.lie
  have hodd : Odd q := by
    have hodd_r : Odd r := hr.odd_of_ne_two hr2
    rw [hq]
    exact hodd_r.pow
  have hq3 : 3 < q := h9
  intro T' hT'
  have hT'in : IsSylowIn 2 T' ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.mp hT'
  have hT'2 : IsPGroup 2 T' := hT'in.isPGroup
  have hcf : CompFactorAutInF (shapeIndex q) ⊤ T' :=
    compFactorAutInF_of_hasOddComponentShapes hT'2 hodd hq3 hshape h410 hrank57 hrankAll h411
  refine ⟨fun hq9 => ?_, fun hqle hqne9 => ?_, fun hq9 => ?_⟩
  · rw [shapeIndex_of_gt hq9] at hcf
    exact hcf
  · rw [shapeIndex_of_le (by omega) hqne9] at hcf
    exact hcf
  · rw [shapeIndex_of_eq hq9] at hcf
    exact hcf

theorem seventeen_thirteen_of_diagonal (D : Data G)
    (V₀ V L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q)
    (h9 : R17_9At D V₀ V L r q hC)
    (hRee : K_ReeSylowGeneration) (hFunNe : K_FunNonempty)
    (h43c : W3Lem45_2Chief)
    (h410 : W4Lem4_10)
    (hrank57 : CFSG.ComponentClassification.GSThmB.CFAutL2Rank)
    (hrankAll : CFSG.ComponentClassification.GSThmB.CFL2Rank)
    (h411 : W4Lem4_11Prime)
    (hstr : Gap17_13_structure D V₀ V L r q hC) :
    R17_13At D (fundPred q) V₀ V L r q hC :=
  seventeen_thirteen D V₀ V L r q hC h9 hRee hFunNe h43c
    (gap17_13_diagonal_of h410 hrank57 hrankAll h411 D V₀ V L r q hC h9 hstr)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
