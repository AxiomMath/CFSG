module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3AutL3
public import CFSG.Sporadic.Recognition.LyonsAmalgamExtAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupAlmostSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81

theorem s1611e3_inFGroup_of_normal_simple_l3 {A : Type} [Group A] [Finite A]
    {L : Subgroup A} [L.Normal] (hsimple : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hC : Subgroup.centralizer (L : Set A) = ⊥)
    (hquot : IsPGroup 2 (A ⧸ L))
    (hshape : IsL3 ↥L 1) : InFGroup 2 A := by
  have hm : CFSG.Open.pRank 2 (⊤ : Subgroup A) ≤ 2 := by
    have hinj : Function.Injective (MulAut.conjNormal : A →* MulAut ↥L) :=
      CFSG.Sporadic.Recognition.LyonsSims.conjNormal_injective_of_centralizer_eq_bot L hC
    refine (CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) _ hinj).trans ?_
    refine CFSG.SectionRank.pRank_le (by norm_num) ?_
    intro E _ hE
    have h := s1611e3_card_le_four_mulAut_l3 hshape hE
    norm_num at h ⊢
    exact h
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := A)
  have hS : IsSylowIn 2 (S : Subgroup A) ⊤ := isSylowIn_top S
  have hsup : L ⊔ (S : Subgroup A) = ⊤ := by
    rw [sup_comm]
    exact CFSG.section10_sylow_sup_normal_of_p_quotient_eq_top (N := L) hquot S
  exact inFGroup_of_twoRank_le inferInstance hsimple hnab hC ⟨_, hS, hsup⟩ hm

theorem s1611e3_inFGroup_quot_of_normal_simple_l3 {N : Type} [Group N] [Finite N]
    {L K C : Subgroup N} [L.Normal] [C.Normal]
    (hC : C = Subgroup.centralizer (L : Set N))
    (hsimple : IsSimpleGroup ↥L) (hperf : Group.IsPerfect ↥L)
    (hK2 : IsPGroup 2 K) (hsup : L ⊔ K = ⊤)
    (hshape : IsL3 ↥L 1) : InFGroup 2 (N ⧸ C) := by
  classical
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hperf.not_isMulCommutative ↥L ⟨⟨fun a b => h a b⟩⟩
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
  haveI : Lbar.Normal := hLbar_normal
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
        L.mul_mem (Subgroup.Normal.conj_mem inferInstance l hl n) (L.inv_mem hl)
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
  have hshape_bar : IsL3 ↥Lbar 1 := CFSG.Blueprint.LieModel.of_mulEquiv e hshape
  exact s1611e3_inFGroup_of_normal_simple_l3 hsimple_bar hnab_bar hCbar hquot hshape_bar

theorem s1611e3_cFAutInFGroup_of_shapeL3 {Q : Type} [Group Q] [Finite Q] (S : Subgroup Q)
    (hS2 : IsPGroup 2 S)
    (hshape : ∀ X : Subgroup Q, X.Normal → X ≠ ⊥ →
      (∀ N : Subgroup Q, N.Normal → N ≤ X → N = ⊥ ∨ N = X) → ¬ IsMulCommutative X →
      ∀ L : Subgroup Q, CFSG.Open.IsComponentOf L X → IsL3 ↥L 1) :
    CFAutInFGroup 2 Q S := by
  intro X hX hXne hmin hnc L hL
  have hshapeL : IsL3 ↥L 1 := hshape X hX hXne hmin hnc L hL
  have hsimpleL : IsSimpleGroup ↥L := isSimpleGroup_of_isL3 hshapeL
  have hperfL : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
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
  haveI : Lq.Normal := hLq
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
  have hshapeLq : IsL3 ↥Lq 1 := by
    have e : ↥Lq ≃* ↥L := Subgroup.subgroupOfEquivOfLe le_sup_right
    exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm hshapeL
  have hsimpleLq : IsSimpleGroup ↥Lq :=
    (Subgroup.subgroupOfEquivOfLe le_sup_right).isSimpleGroup_congr.mpr hsimpleL
  have hperfLq : Group.IsPerfect ↥Lq :=
    ⟨(CFSG.Open.IsQuasisimple.of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe le_sup_right) hL.2.2).1⟩
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
  haveI : ((F12.autC S L).subgroupOf N).Normal := hCn
  have hres := s1611e3_inFGroup_quot_of_normal_simple_l3 (N := ↥N) (L := Lq) (K := Kq)
    (C := (F12.autC S L).subgroupOf N) hCeq hsimpleLq hperfLq hKq2 hsup hshapeLq
  exact ⟨hCeq ▸ Subgroup.normal_centralizer, hres⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
