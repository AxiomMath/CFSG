module

public import CFSG.Quasithin.EmptyFaithful.E22PTypeII
public import CFSG.Quasithin.Vol2.Ch11SecE3LieLow
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5EF
public import CFSG.Quasithin.Background.VolIE54
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  (InFGroup IsOmegaColl genEi InCalEi InCalE ECaseII tA)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (IsEP eGenP InF ETwoPrint)
open CFSG.Quasithin.Vol2.Ch11.SecE3
open scoped Pointwise commutatorElement

theorem pCoreOf_top_eq_bot_of_almostSimple {Q : Type} [Group Q] [Finite Q]
    {L : Subgroup Q} (hL : L.Normal) (hsimple : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hC : Subgroup.centralizer (L : Set Q) = ⊥) :
    pCoreOf 2 (⊤ : Subgroup Q) = ⊥ := by
  haveI : L.Normal := hL
  haveI : IsSimpleGroup ↥L := hsimple
  exact CFSG.Quasithin.E1.pCoreOf_top_eq_bot_of_normal_simple L hnab hC

theorem almostSimple_of_normal_simple_sup_sylow {Q : Type} [Group Q] [Finite Q]
    {L T : Subgroup Q} (hL : L.Normal) (hsimple : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hC : Subgroup.centralizer (L : Set Q) = ⊥)
    (hT : IsSylowIn 2 T ⊤) (hLT : L ⊔ T = ⊤) : AlmostSimple L := by
  haveI : L.Normal := hL
  refine ⟨hL, hsimple, hnab, hC, ?_⟩
  intro x
  have hx : x ∈ L ⊔ T := by rw [hLT]; exact Subgroup.mem_top x
  obtain ⟨l, hl, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  obtain ⟨k, hk⟩ := hT.isPGroup ⟨t, ht⟩
  refine ⟨k, ?_⟩
  refine (QuotientGroup.eq_one_iff ((l * t) ^ 2 ^ k)).mp ?_
  have ht1 : t ^ 2 ^ k = 1 := by
    have hval := congrArg Subtype.val hk
    simpa using hval
  have hlq : (QuotientGroup.mk' L) l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
  have hlt : (QuotientGroup.mk' L) (l * t) = (QuotientGroup.mk' L) t := by
    rw [map_mul, hlq, one_mul]
  change (QuotientGroup.mk' L) ((l * t) ^ 2 ^ k) = 1
  rw [map_pow, hlt, ← map_pow, ht1, map_one]

theorem almostSimple_eTwo_first {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q}
    (h : AlmostSimple L) {S B : Subgroup Q} (hB : B ≠ ⊥) :
    ∃ L' : Subgroup (Q ⧸ CFSG.solvableRadical Q), CFSG.IsComponent L' ∧
      CFSG.layer (Q ⧸ CFSG.solvableRadical Q) =
        ⨆ t ∈ (E1.tauOf (⊤ : Subgroup Q) S B).map
            (QuotientGroup.mk' (CFSG.solvableRadical Q)),
          L'.map (MulAut.conj t).toMonoidHom ∧
      L' = ⁅L', E1.barRad Q B⁆ := by
  haveI : L.Normal := h.normal
  have hR := h.solvableRadical_eq_bot
  set π := QuotientGroup.mk' (CFSG.solvableRadical Q)
  have hπi : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hR]
  let e : Q ≃* Q ⧸ CFSG.solvableRadical Q :=
    MulEquiv.ofBijective π ⟨hπi, QuotientGroup.mk'_surjective _⟩
  have he : ∀ X : Subgroup Q, X.map e.toMonoidHom = X.map π := fun X => rfl
  have hLbar : CFSG.IsComponent (L.map π) := by
    rw [← he]
    exact CFSG.LocalCores.isComponent_map_mulEquiv e h.isComponent
  have hlayer : CFSG.layer (Q ⧸ CFSG.solvableRadical Q) = L.map π := by
    rw [← E1.layer_map_mulEquiv e, h.layer_eq, he]
  have hLn' : (L.map π).Normal :=
    Subgroup.Normal.map h.normal π (QuotientGroup.mk'_surjective _)
  have hconj : ∀ t, CFSG.Quasithin.A1b.conjSub t (L.map π) = L.map π := fun t =>
    CFSG.Quasithin.B6.conjSub_eq_self
      ((Subgroup.normalizer_eq_top (h := hLn')).ge (Subgroup.mem_top t))
  refine ⟨L.map π, hLbar, ?_, ?_⟩
  · rw [hlayer]
    refine le_antisymm (le_iSup₂_of_le 1 (Subgroup.one_mem _) (hconj 1).ge)
      (iSup₂_le fun t _ => (hconj t).le)
  · unfold E1.barRad
    rw [← Subgroup.map_commutator, h.commutator_eq hB]

theorem eCaseII_top_of_almostSimple {Q : Type} [Group Q] [Finite Q] {L T A : Subgroup Q}
    (h : AlmostSimple L) (hA : A ≠ ⊥) : ECaseII T A ⊤ := by
  have h' : AlmostSimple (L.subgroupOf (⊤ : Subgroup Q)) := almostSimple_subgroupOf h le_top
  have hB : (A.subgroupOf (⊤ : Subgroup Q)) ≠ ⊥ := by
    rw [Ne, Subgroup.subgroupOf_eq_bot, disjoint_top]
    exact hA
  obtain ⟨h1, h2, h3, _⟩ :=
    h'.eTwo (S := T.subgroupOf (⊤ : Subgroup Q)) (B := A.subgroupOf (⊤ : Subgroup Q)) hB
  obtain ⟨L', hcomp, hlayer, hcomm⟩ :=
    almostSimple_eTwo_first h'
      (S := T.subgroupOf (⊤ : Subgroup Q)) (B := A.subgroupOf (⊤ : Subgroup Q)) hB
  have hTa : E1.tauOf (⊤ : Subgroup ↥(⊤ : Subgroup Q)) (T.subgroupOf ⊤)
      (A.subgroupOf ⊤) = (tA T A).subgroupOf ⊤ :=
    E1.tauOf_top_subgroupOf le_top le_top
  refine ⟨h1, h2, h3, L', hcomp, ?_, Or.inl hcomm⟩
  rw [hTa] at hlayer
  exact hlayer

theorem inCalE_top_of_almostSimple {Q : Type} [Group Q] [Finite Q] {L T A : Subgroup Q}
    (h : AlmostSimple L) (hT : IsSylowIn 2 T ⊤) (hA : A ≠ ⊥) : InCalE T A ⊤ := by
  have hO2 : pCoreOf 2 (⊤ : Subgroup Q) = ⊥ :=
    pCoreOf_top_eq_bot_of_almostSimple h.normal h.simple h.nonabelian h.centralizer_eq
  refine ⟨le_inf (E1.tauOf_le (⊤ : Subgroup Q) T A) le_top, ?_, ?_,
    Or.inr (eCaseII_top_of_almostSimple h hA)⟩
  · rw [inf_top_eq]
    exact CFSG.ABGLocalTools.isSylowOf_iff.mpr hT
  · rw [hO2, le_bot_iff]
    exact hA

theorem inCalEi_top_of_almostSimple {Q : Type} [Group Q] [Finite Q] {L T A : Subgroup Q}
    {j : ℕ} (h : AlmostSimple L) (hT : IsSylowIn 2 T ⊤) (hA : A ≠ ⊥)
    (hm : E3.mQuot A (pCoreOf 2 (⊤ : Subgroup Q)) ≤ j) : InCalEi j T A ⊤ :=
  ⟨inCalE_top_of_almostSimple h hT hA, hm⟩

theorem mQuot_pCoreOf_top_le_of_card_le {Q : Type} [Group Q] [Finite Q] {L A : Subgroup Q}
    {j : ℕ} (h : AlmostSimple L) (hA2 : IsPGroup 2 A) (hcard : Nat.card A ≤ 2 ^ j) :
    E3.mQuot A (pCoreOf 2 (⊤ : Subgroup Q)) ≤ j := by
  have hO2 : pCoreOf 2 (⊤ : Subgroup Q) = ⊥ :=
    pCoreOf_top_eq_bot_of_almostSimple h.normal h.simple h.nonabelian h.centralizer_eq
  rw [hO2]
  have hpow : 2 ^ E3.mQuot A (⊥ : Subgroup Q) = Nat.card A := by
    rw [← E3.relIndex_eq_two_pow hA2 (⊥ : Subgroup Q), Subgroup.relIndex_bot_left]
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (hpow.symm ▸ hcard)

theorem inFGroup_of_twoRank_le {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q} {j : ℕ}
    (hL : L.Normal) (hsimple : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hC : Subgroup.centralizer (L : Set Q) = ⊥)
    (hT : ∃ T : Subgroup Q, IsSylowIn 2 T ⊤ ∧ L ⊔ T = ⊤)
    (hm : CFSG.Open.pRank 2 (⊤ : Subgroup Q) ≤ j) : InFGroup j Q := by
  obtain ⟨T, hTsyl, hLT⟩ := hT
  have has : AlmostSimple L :=
    almostSimple_of_normal_simple_sup_sylow hL hsimple hnab hC hTsyl hLT
  intro S hS Ω hΩ
  have hΩ' : E1.IsInvColl (⊤ : Subgroup Q) Ω :=
    { le := fun _ _ => le_top
      isElemAbelian := hΩ.elemAbelian
      conj := fun A hA g _ => by
        have h1 := hΩ.conj A hA g⁻¹
        rwa [CFSG.Quasithin.conjSubgroup_eq_conjSub A g⁻¹, inv_inv] at h1 }
  obtain ⟨A, hAΩ, hAS⟩ := exists_mem_le_of_isSylowOf hS hΩ' hΩ.nonempty
  have hAel : IsElemAbelian 2 A := hΩ.elemAbelian A hAΩ
  have hA : A ≠ ⊥ := hΩ.ne_bot A hAΩ
  have hcard : Nat.card A ≤ 2 ^ j :=
    (CFSG.Quasithin.VolI.E54.card_le_two_pow_pRank_of_le (H := ⊤) le_top hAel).trans
      (Nat.pow_le_pow_right (by norm_num) hm)
  have hmq : E3.mQuot A (pCoreOf 2 (⊤ : Subgroup Q)) ≤ j :=
    mQuot_pCoreOf_top_le_of_card_le has hAel.isPGroup hcard
  have hIn : InCalEi j S A ⊤ :=
    inCalEi_top_of_almostSimple has
      (CFSG.ABGLocalTools.isSylowOf_iff.mp hS) hA hmq
  have htop : genEi j S Ω = ⊤ :=
    le_antisymm le_top
      (le_iSup₂_of_le A hAΩ (le_iSup_of_le hAS (le_iSup₂_of_le ⊤ hIn le_rfl)))
  change ((genEi j S Ω : Subgroup Q) : Set Q) * (S : Set Q) = Set.univ
  rw [htop, Subgroup.coe_top]
  exact Set.univ_mul ⟨1, S.one_mem⟩

end CFSG.LocalAnalysis.WeakClosure81
