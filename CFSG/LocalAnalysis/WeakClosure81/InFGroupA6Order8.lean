module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsA
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Shape
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82A10Sym
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.Blueprint.LieModelAPI
public import CFSG.Quasithin.H13.A6S1356S6Fr
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Vol2.Ch11SecBNPAut
public import CFSG.Assembly.OrderReductions.PrimeQuotientFrattini
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.GH74.Orders.LieType
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82A10
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8L4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42Kernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Alm
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Bridge
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.C1GNC124
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5Top

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

theorem altSix_isL2_three_two : F6.IsL2 3 2 (alternatingGroup (Fin 6)) :=
  (CFSG.Blueprint.LieModel.classical_iff (t := .PSL) (by decide)).1
    CFSG.ComponentClassification.GSThmB.Catalog82A10.lieModel_alternatingGroup_six

theorem inFGroup_one_of_normal_A6 (h410 : W4Lem4_10) {A : Type} [Group A] [Finite A]
    {L : Subgroup A} [L.Normal] (hA6 : Nonempty (↥L ≃* alternatingGroup (Fin 6)))
    (hC : Subgroup.centralizer (L : Set A) = ⊥) (hquot : IsPGroup 2 (A ⧸ L))
    (ha : ∃ a : A, a ^ 4 ≠ 1 ∧ ∃ n : ℕ, a ^ 2 ^ n = 1) : InFGroup 1 A := by
  classical
  obtain ⟨eA⟩ := hA6
  have hnabA6 := CFSG.QuasithinUnique.Vol2Native.A312L.Seven.alt6_nonabelian
  have hnabL : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnabA6
    exact ⟨eA.symm a, eA.symm b, fun h => hab (by simpa using congrArg eA h)⟩
  have hsimpleA6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (α := Fin 6) (by simp)
  have hsimpleL : IsSimpleGroup ↥L := (MulEquiv.isSimpleGroup_congr eA).mpr hsimpleA6
  have hquasi : CFSG.IsQuasisimple ↥L :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnabL).1
  have hcomp : CFSG.IsComponent L :=
    ⟨hquasi, (inferInstance : L.Normal).isSubnormal⟩
  have hFstar : Fstar (⊤ : Subgroup A) = L := by
    have hgen := CFSG.Quasithin.Vol2.Ch11.SecB.generalizedFitting_eq_of_component
      (G := A) L hcomp hC
    unfold Fstar
    rw [CFSG.Adapters.genFittingFStar_eq_foundations, ← hgen]
    exact CFSG.WholeGroup.generalizedFitting_map_mulEquiv (Subgroup.topEquiv (G := A))
  have hLcard : Nat.card ↥L = 360 := by
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup]
    norm_num
  obtain ⟨T⟩ := Sylow.nonempty (p := 2) (G := A)
  have hLT : L ⊔ (T : Subgroup A) = ⊤ :=
    CFSG.OrderReductions.PrimeQuotientFrattini.kernel_sup_sylow_eq_top 2 L hquot T
  have hTsylIn : CFSG.Quasithin.IsSylowIn 2 (T : Subgroup A) ⊤ :=
    CFSG.Quasithin.isSylowIn_top T
  have hF6L : F6.IsL2 3 2 ↥L :=
    isoInvPred_f6IsL2 3 2 ↥(alternatingGroup (Fin 6)) ↥L ⟨eA.symm⟩
      altSix_isL2_three_two
  have hFconcl := h410 A L (T : Subgroup A) 9 (inferInstance : L.Normal) hFstar
    ⟨3, 2, by norm_num, by norm_num, by norm_num, hF6L⟩ (by norm_num) (by norm_num)
    hTsylIn hLT
  rcases hFconcl with hF | hAlt | ⟨hsmall, -⟩
  · exact hF
  · exact absurd hAlt
      (not_isAlt_five_of_isL2_odd
        (p := 3) (e := 2) (by norm_num) (by norm_num) (by norm_num) hF6L)
  · rcases hsmall with hL27 | hL29 | hSym
    · exfalso
      have h2 := two_mul_card_isL2_odd (p := 7) (e := 1) (by norm_num) (by norm_num) hL27
      have hle : Nat.card ↥L ≤ Nat.card A := by
        simpa [Subgroup.card_top] using
          Subgroup.card_le_of_le (H := L) (K := (⊤ : Subgroup A)) le_top
      omega
    · exfalso
      have h2 := two_mul_card_isL2_odd (p := 3) (e := 2) (by norm_num) (by norm_num) hL29
      have hAcard : Nat.card A = 360 := by omega
      have hLtop : L = ⊤ := by
        refine Subgroup.eq_of_le_of_card_ge (H := L) (K := ⊤) le_top ?_
        rw [Subgroup.card_top, hLcard]
        omega
      obtain ⟨a, ha4, n, han⟩ := ha
      have haL : a ∈ L := by rw [hLtop]; exact Subgroup.mem_top a
      let aL : ↥L := ⟨a, haL⟩
      have hσ : ((eA aL : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) ^ 4 = 1 := by
        refine CFSG.Quasithin.H13.A6.perm6_pow_four_of_two (k := n) ?_
        have h1 : aL ^ 2 ^ n = 1 := by
          apply Subtype.ext
          simpa using han
        have h2 := congrArg
          (fun x : ↥L => ((eA x : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))) h1
        simpa using h2
      have h4 : aL ^ 4 = 1 := by
        apply eA.injective
        rw [map_pow, map_one]
        exact Subtype.ext hσ
      exact ha4 (by simpa using congrArg Subtype.val h4)
    · exfalso
      obtain ⟨eSym⟩ := hSym
      obtain ⟨a, ha4, n, han⟩ := ha
      have hσ : (eSym a) ^ 4 = 1 := by
        refine CFSG.Quasithin.H13.A6.perm6_pow_four_of_two (k := n) ?_
        have h2 := congrArg eSym han
        simpa using h2
      have h4 : a ^ 4 = 1 := by
        have h2 := congrArg eSym.symm hσ
        simpa using h2
      exact ha4 h4

theorem inFGroup_one_quot_of_normal_A6 (h410 : W4Lem4_10) {N : Type} [Group N] [Finite N]
    {L K C : Subgroup N} [L.Normal] [C.Normal] (hC : C = Subgroup.centralizer (L : Set N))
    (hA6 : Nonempty (↥L ≃* alternatingGroup (Fin 6))) (hK2 : IsPGroup 2 K) (hsup : L ⊔ K = ⊤)
    (ha : ∃ a ∈ K, a ^ 4 ∉ C) : InFGroup 1 (N ⧸ C) := by
  classical
  obtain ⟨eA⟩ := hA6
  have hnabA6 := CFSG.QuasithinUnique.Vol2Native.A312L.Seven.alt6_nonabelian
  have hnabL : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnabA6
    exact ⟨eA.symm a, eA.symm b, fun h => hab (by simpa using congrArg eA h)⟩
  have hsimpleA6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (α := Fin 6) (by simp)
  have hsimpleL : IsSimpleGroup ↥L := (MulEquiv.isSimpleGroup_congr eA).mpr hsimpleA6
  have hcenter : Subgroup.center ↥L = ⊥ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnabL).2
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
  have : Lbar.Normal := hLbar_normal
  have hA6bar : Nonempty (↥Lbar ≃* alternatingGroup (Fin 6)) := ⟨e.symm.trans eA⟩
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
      obtain ⟨a, hax⟩ := QuotientGroup.mk_surjective x
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
      rw [← hax, ← hn, ← hlk]
      exact h1.symm
    exact IsPGroup.of_surjective hK2 _ hsurj
  obtain ⟨a, haK, ha4⟩ := ha
  refine inFGroup_one_of_normal_A6 h410 hA6bar hCbar hquot ⟨mk a, ?_, ?_⟩
  · intro h
    apply ha4
    have h' : mk (a ^ 4) = 1 := by simpa [mk] using h
    exact (QuotientGroup.eq_one_iff _).mp h'
  · obtain ⟨n, hn⟩ := hK2 ⟨a, haK⟩
    have hn' : a ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    exact ⟨n, by simpa [mk] using congrArg mk hn'⟩

theorem cFAutInFGroup_one_of_A6 (h410 : W4Lem4_10) {Q : Type} [Group Q] [Finite Q]
    (S : Subgroup Q) (hS2 : IsPGroup 2 S)
    (hshape : ∀ X : Subgroup Q, X.Normal → X ≠ ⊥ →
      (∀ N : Subgroup Q, N.Normal → N ≤ X → N = ⊥ ∨ N = X) → ¬ IsMulCommutative X →
      ∀ L : Subgroup Q, CFSG.Open.IsComponentOf L X →
        Nonempty (↥L ≃* alternatingGroup (Fin 6)) ∧
          ∃ s ∈ S ⊓ Subgroup.normalizer (L : Set Q), s ^ 4 ∉ Subgroup.centralizer (L : Set Q)) :
    CFAutInFGroup 1 Q S := by
  intro X hX hXne hmin hnc L hL
  obtain ⟨hA6, s, hs, hs4⟩ := hshape X hX hXne hmin hnc L hL
  have hsimpleA6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (α := Fin 6) (by simp)
  have hsimpleL : IsSimpleGroup ↥L := by
    obtain ⟨eA⟩ := hA6
    exact (MulEquiv.isSimpleGroup_congr eA).mpr hsimpleA6
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
  have : Lq.Normal := hLq
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
  have hA6q : Nonempty (↥Lq ≃* alternatingGroup (Fin 6)) := by
    obtain ⟨eA⟩ := hA6
    exact ⟨(Subgroup.subgroupOfEquivOfLe le_sup_right).trans eA⟩
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
  have : ((F12.autC S L).subgroupOf N).Normal := hCn
  have hsN : s ∈ N := hKN hs
  have ha : ∃ a ∈ Kq, a ^ 4 ∉ (F12.autC S L).subgroupOf N := by
    refine ⟨⟨s, hsN⟩, Subgroup.mem_subgroupOf.mpr hs, ?_⟩
    intro hmem
    apply hs4
    have hmem' : ((⟨s, hsN⟩ : ↥N) ^ 4 : Q) ∈ F12.autC S L :=
      Subgroup.mem_subgroupOf.mp hmem
    simpa using hmem'.2
  have hres := inFGroup_one_quot_of_normal_A6 h410 (N := ↥N) (L := Lq) (K := Kq)
    (C := (F12.autC S L).subgroupOf N) hCeq hA6q hKq2 hsup ha
  exact ⟨hCeq ▸ Subgroup.normal_centralizer, hres⟩

end CFSG.LocalAnalysis.WeakClosure81
