module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Core
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Concl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem map_normalizer_subtype_le' {X : Subgroup G} (Q : Subgroup ↥X) :
    (Subgroup.normalizer (Q : Set ↥X)).map X.subtype ≤
      Subgroup.normalizer (Q.map X.subtype : Set G) :=
  Subgroup.le_normalizer_map (H := Q) X.subtype

theorem pCoreOf_map_subtype' {X : Subgroup G} (p : ℕ) (K : Subgroup ↥X) :
    (pCoreOf p K).map X.subtype = pCoreOf p (K.map X.subtype) := by
  let e : ↥K ≃* ↥(K.map X.subtype) := K.equivMapOfInjective X.subtype X.subtype_injective
  have hcomp : (X.subtype : ↥X →* G).comp K.subtype =
      (K.map X.subtype).subtype.comp e.toMonoidHom := MonoidHom.ext fun x =>
    Subgroup.coe_equivMapOfInjective_apply K X.subtype X.subtype_injective x
  simp only [pCoreOf]
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, CFSG.pCore_map_iso p e]

theorem twoLocalPrimeRank_subgroup_le' {q : ℕ} (hq : q.Prime) (X : Subgroup G) :
    twoLocalPrimeRank q X ≤ twoLocalPrimeRank q G := by
  refine csSup_le' ?_
  rintro _ ⟨L, ⟨P, hP1, hP2, rfl⟩, rfl⟩
  set L' : Subgroup G := normalizer ((P.map X.subtype : Subgroup G) : Set G) with hL'
  have hL'loc : IsTwoLocal L' := by
    refine ⟨P.map X.subtype, ?_,
      hP2.of_equiv (P.equivMapOfInjective X.subtype X.subtype_injective), rfl⟩
    intro h
    exact hP1 ((Subgroup.map_eq_bot_iff_of_injective P X.subtype_injective).mp h)
  have hle : (normalizer (P : Set X)).map X.subtype ≤ L' :=
    Subgroup.le_normalizer_map (H := P) X.subtype
  have h1 : CFSG.Open.pRank q (normalizer (P : Set X)) ≤ CFSG.Open.pRank q L' :=
    (CFSG.SectionRank.pRank_le_map hq.one_lt X.subtype X.subtype_injective _).trans
      (CFSG.SectionRank.pRank_mono hq.one_lt hle)
  refine h1.trans (le_csSup ⟨Nat.card G, ?_⟩ ⟨L', hL'loc, rfl⟩)
  rintro _ ⟨K, -, rfl⟩
  exact CFSG.SectionRank.pRank_le_card_of_one_lt hq.one_lt K

theorem le_subgroupOf_of_isTwoLocal {M E : Subgroup G} {p : ℕ} (h : Hyp36 G M p E) {X : Subgroup G}
    (hEX : E ≤ X) {N : Subgroup ↥X} (hN : IsTwoLocal N) (hE'N : E.subgroupOf X ≤ N) :
    N ≤ M.subgroupOf X := by
  obtain ⟨P, hPne, hP2, rfl⟩ := hN
  have hP₀ne : P.map X.subtype ≠ ⊥ := fun h =>
    hPne (Subgroup.map_eq_bot_iff_of_injective P X.subtype_injective |>.1 h)
  have hP₀2 : IsPGroup 2 (P.map X.subtype) := hP2.map X.subtype
  obtain ⟨N', hN'max, hN'⟩ := exists_isMaxTwoLocal_ge_of_isTwoLocal
    (show IsTwoLocal (Subgroup.normalizer (P.map X.subtype : Set G)) from ⟨_, hP₀ne, hP₀2, rfl⟩)
  have hEN' : E ≤ N' := by
    have h2 : E = (E.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hEX).symm
    rw [h2]
    exact (Subgroup.map_mono hE'N).trans ((map_normalizer_subtype_le' P).trans hN')
  have hN'eq : N' = M := by
    have hmem : N' ∈ calMOf E := ⟨hN'max, hEN'⟩
    rw [h.uniq] at hmem
    simpa using hmem
  intro x hx
  have hx' : (x : G) ∈ M :=
    (hN'eq ▸ hN') ((map_normalizer_subtype_le' P) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
  exact Subgroup.mem_subgroupOf.mpr hx'

theorem calMOf_subgroupOf_eq_singleton {M E : Subgroup G} {p : ℕ} (h : Hyp36 G M p E) {X : Subgroup G}
    (hEX : E ≤ X) (hQ : pCoreOf 2 (M.subgroupOf X) ≠ ⊥) :
    calMOf (E.subgroupOf X) = {M.subgroupOf X} := by
  have hE'HM : E.subgroupOf X ≤ M.subgroupOf X := fun x hx => h.E_le hx
  have hP2 : IsPGroup 2 (pCoreOf 2 (M.subgroupOf X)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (M.subgroupOf X)
  have hle : M.subgroupOf X ≤ Subgroup.normalizer (pCoreOf 2 (M.subgroupOf X) : Set ↥X) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (M.subgroupOf X)
  have hge : Subgroup.normalizer (pCoreOf 2 (M.subgroupOf X) : Set ↥X) ≤ M.subgroupOf X :=
    le_subgroupOf_of_isTwoLocal h hEX ⟨_, hQ, hP2, rfl⟩ (hE'HM.trans hle)
  have hM2local : IsTwoLocal (M.subgroupOf X) := ⟨_, hQ, hP2, le_antisymm hle hge⟩
  have hMmax : IsMaxTwoLocalSubgroup (M.subgroupOf X) := by
    refine ⟨hM2local, fun K hK hleKM => ?_⟩
    exact le_antisymm (le_subgroupOf_of_isTwoLocal h hEX hK (hE'HM.trans hleKM)) hleKM
  ext N
  constructor
  · rintro ⟨hNmax, hE'N⟩
    have hNle : N ≤ M.subgroupOf X := le_subgroupOf_of_isTwoLocal h hEX hNmax.1 hE'N
    exact (hNmax.2 _ hM2local hNle).symm
  · rintro rfl
    exact ⟨hMmax, hE'HM⟩

namespace Hyp36

variable {M E : Subgroup G} {p : ℕ} (h : Hyp36 G M p E)
include h

theorem subgroupOf {X : Subgroup G} (hEX : E ≤ X) (hXM : ¬ X ≤ M)
    (hQX : pCoreOf 2 (X ⊓ M) ≠ ⊥) :
    Hyp36 ↥X (M.subgroupOf X) p (E.subgroupOf X) := by
  have hmap_eq : (M.subgroupOf X).map X.subtype = X ⊓ M := by
    rw [Subgroup.subgroupOf_map_subtype, inf_comm]
  have hQ' : pCoreOf 2 (M.subgroupOf X) ≠ ⊥ := by
    intro hb
    apply hQX
    have h2 : (pCoreOf 2 (M.subgroupOf X)).map X.subtype = (⊥ : Subgroup ↥X).map X.subtype := by
      rw [hb]
    rwa [Subgroup.map_bot, pCoreOf_map_subtype', hmap_eq] at h2
  have hE'card : Nat.card (E.subgroupOf X) = p ^ 2 := by
    calc Nat.card (E.subgroupOf X) = Nat.card ((E.subgroupOf X).map X.subtype) :=
          (Subgroup.card_map_of_injective X.subtype_injective).symm
      _ = Nat.card E := by rw [Subgroup.map_subgroupOf_eq_of_le hEX]
      _ = p ^ 2 := h.card
  have hΓ' : rankThreeGamma 1 p (E.subgroupOf X) ≤ M.subgroupOf X := by
    rw [CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff]
    intro Y hYE' hY1
    have hY0E : Y.map X.subtype ≤ E := by
      rw [Subgroup.map_le_iff_le_comap, Subgroup.comap_subtype]
      exact hYE'
    have hY0rank : 1 ≤ CFSG.Open.pRank p (Y.map X.subtype) :=
      hY1.trans (CFSG.SectionRank.pRank_le_map h.prime.one_lt X.subtype X.subtype_injective Y)
    have hNle : Subgroup.normalizer (Y.map X.subtype : Set G) ≤ M :=
      (CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff 1 p E M).1 h.gamma
        (Y.map X.subtype) hY0E hY0rank
    intro x hx
    have hx' : (x : G) ∈ M := hNle ((map_normalizer_subtype_le' Y) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
    exact Subgroup.mem_subgroupOf.mpr hx'
  exact ⟨fun hb => hXM (Subgroup.subgroupOf_eq_top.1 hb), hQ', h.prime, h.odd, h.elem.subgroupOf X,
    hE'card, hΓ', calMOf_subgroupOf_eq_singleton h hEX hQ'⟩

end Hyp36

theorem isGraphFieldAut_conj' {K K' : Type} [Group K] [Group K'] (φ : K ≃* K')
    {β : K ≃* K} (h : CFSG.ASVolI.ChIJK.IsGraphFieldAut β) :
    CFSG.ASVolI.ChIJK.IsGraphFieldAut (φ.symm.trans (β.trans φ)) := by
  obtain ⟨e, c, he⟩ := h
  let q := QuotientGroup.congr (Subgroup.center K) (Subgroup.center K') φ
    (Subgroup.map_center_eq φ)
  refine ⟨q.symm.trans e, c, fun k' => ?_⟩
  have h1 : ((φ.symm.trans (β.trans φ)) k' : K' ⧸ Subgroup.center K') =
      q (((β (φ.symm k') : K) : K ⧸ Subgroup.center K)) := by
    rw [QuotientGroup.congr_apply]
    rfl
  have hq : q.symm = QuotientGroup.congr (Subgroup.center K') (Subgroup.center K) φ.symm
      ((Subgroup.map_symm_eq_iff_map_eq _).mpr (Subgroup.map_center_eq φ)) := by
    rw [QuotientGroup.congr_symm]
  have hL : (q.symm.trans e) (((φ.symm.trans (β.trans φ)) k' : K') : K' ⧸ Subgroup.center K') =
      e (((β (φ.symm k') : K) : K ⧸ Subgroup.center K)) := by
    rw [MulEquiv.trans_apply, h1, MulEquiv.symm_apply_apply]
  have hR : (q.symm.trans e) (k' : K' ⧸ Subgroup.center K') =
      e ((φ.symm k' : K) : K ⧸ Subgroup.center K) := by
    rw [MulEquiv.trans_apply, hq, QuotientGroup.congr_apply]
    rfl
  rw [hL, he (φ.symm k'), hR]

theorem conjOn_map_subtype_apply' {X : Subgroup G} (L : Subgroup ↥X) {t : ↥X}
    (ht : t ∈ Subgroup.normalizer (L : Set ↥X))
    (ht' : (t : G) ∈ Subgroup.normalizer (L.map X.subtype : Set G)) (x : ↥L) :
    (Subgroup.equivMapOfInjective L X.subtype X.subtype_injective) (UC6.conjOn L ht x) =
      UC6.conjOn (L.map X.subtype) ht'
        ((Subgroup.equivMapOfInjective L X.subtype X.subtype_injective) x) := by
  apply Subtype.ext
  show X.subtype (t * x * t⁻¹) =
    (t : G) * (Subgroup.equivMapOfInjective L X.subtype X.subtype_injective x : G) * (t : G)⁻¹
  rw [Subgroup.coe_equivMapOfInjective_apply, map_mul, map_mul, map_inv]
  rfl

theorem inducesGraphField_map_subtype' {X : Subgroup G} {L : Subgroup ↥X} {t : ↥X}
    (h : UC6.InducesGraphField t L) :
    UC6.InducesGraphField (t : G) (L.map X.subtype) := by
  obtain ⟨ht, hauto⟩ := h
  have ht' : (t : G) ∈ Subgroup.normalizer (L.map X.subtype : Set G) :=
    map_normalizer_subtype_le' L (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)
  refine ⟨ht', ?_⟩
  have hconj : UC6.conjOn (L.map X.subtype) ht' =
      (Subgroup.equivMapOfInjective L X.subtype X.subtype_injective).symm.trans
        ((UC6.conjOn L ht).trans (Subgroup.equivMapOfInjective L X.subtype X.subtype_injective)) := by
    apply MulEquiv.ext
    intro x
    calc UC6.conjOn (L.map X.subtype) ht' x
        = UC6.conjOn (L.map X.subtype) ht'
            ((Subgroup.equivMapOfInjective L X.subtype X.subtype_injective)
              ((Subgroup.equivMapOfInjective L X.subtype X.subtype_injective).symm x)) := by
          rw [MulEquiv.apply_symm_apply]
      _ = (Subgroup.equivMapOfInjective L X.subtype X.subtype_injective)
            (UC6.conjOn L ht
              ((Subgroup.equivMapOfInjective L X.subtype X.subtype_injective).symm x)) :=
          (conjOn_map_subtype_apply' L ht ht' _).symm
      _ = ((Subgroup.equivMapOfInjective L X.subtype X.subtype_injective).symm.trans
            ((UC6.conjOn L ht).trans
              (Subgroup.equivMapOfInjective L X.subtype X.subtype_injective))) x := by
          rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
  rw [hconj]
  exact isGraphFieldAut_conj' (Subgroup.equivMapOfInjective L X.subtype X.subtype_injective) hauto

theorem inducesTransposition_map_subtype' {X : Subgroup G} {L : Subgroup ↥X} {t : ↥X}
    (h : UC6.InducesTransposition t L) :
    UC6.InducesTransposition (t : G) (L.map X.subtype) := by
  obtain ⟨ht, e, τ, hτ, he⟩ := h
  have ht' : (t : G) ∈ Subgroup.normalizer (L.map X.subtype : Set G) :=
    map_normalizer_subtype_le' L (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)
  let eL := Subgroup.equivMapOfInjective L X.subtype X.subtype_injective
  refine ⟨ht', eL.symm.trans e, τ, hτ, fun x => ?_⟩
  have hx : UC6.conjOn (L.map X.subtype) ht' x = eL (UC6.conjOn L ht (eL.symm x)) := by
    rw [conjOn_map_subtype_apply' L ht ht' (eL.symm x), MulEquiv.apply_symm_apply]
  rw [hx]
  simpa only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using he (eL.symm x)

theorem graphFieldShape_map_subtype' {X : Subgroup G} {t : ↥X} {L : Subgroup ↥X}
    (h : UC6.GraphFieldShape t L) :
    UC6.GraphFieldShape (t : G) (L.map X.subtype) := by
  let eL := Subgroup.equivMapOfInjective L X.subtype X.subtype_injective
  rcases h with ⟨hcase, hgf⟩ | ⟨L₁, L₂, hsup, hcomm, h₁, h₂, hcenter, hgf₁, hgf₂⟩
  · left
    refine ⟨?_, inducesGraphField_map_subtype' hgf⟩
    rcases hcase with hcase | hcase
    · exact Or.inl ⟨eL.symm.trans (Classical.choice hcase)⟩
    · exact Or.inr ⟨eL.symm.trans (Classical.choice hcase)⟩
  · right
    let e₁' := Subgroup.equivMapOfInjective L₁ X.subtype X.subtype_injective
    let e₂' := Subgroup.equivMapOfInjective L₂ X.subtype X.subtype_injective
    refine ⟨L₁.map X.subtype, L₂.map X.subtype, ?_, ?_,
      ⟨e₁'.symm.trans (Classical.choice h₁)⟩,
      ⟨e₂'.symm.trans (Classical.choice h₂)⟩, ?_, inducesGraphField_map_subtype' hgf₁,
      inducesGraphField_map_subtype' hgf₂⟩
    · rw [← Subgroup.map_sup, hsup]
    · intro a ha b hb
      obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
      simpa using congrArg X.subtype (hcomm a₀ ha₀ b₀ hb₀)
    · rw [← Subgroup.map_inf_eq L₁ L₂ X.subtype X.subtype_injective, hcenter,
        Subgroup.map_map]
      have hcomp : (X.subtype : ↥X →* G).comp L₁.subtype =
          (L₁.map X.subtype).subtype.comp e₁'.toMonoidHom := MonoidHom.ext fun x =>
        Subgroup.coe_equivMapOfInjective_apply L₁ X.subtype X.subtype_injective x
      have hcenter' : (Subgroup.center ↥L₁).map e₁'.toMonoidHom =
          Subgroup.center ↥(L₁.map X.subtype) := Subgroup.map_center_eq e₁'
      rw [hcomp, ← Subgroup.map_map, hcenter']

@[expose] def K36ConclIn (X M : Subgroup G) (p : ℕ) : Prop :=
  p = 3 ∧ ∃ t : G, orderOf t = 2 ∧ pCoreOf 2 (X ⊓ M) = zpowers t ∧
    ∃ L : Subgroup G, L ≤ X ∧ (L.subgroupOf X).Normal ∧ X = (X ⊓ M) ⊔ L ∧
      (UC6.GraphFieldShape t L ∨
        (Nonempty (↥L ≃* alternatingGroup (Fin 11)) ∧ UC6.InducesTransposition t L))

theorem K36Concl.toConclIn {X M : Subgroup G} {p : ℕ} (hc : K36Concl (M.subgroupOf X) p) :
    K36ConclIn X M p := by
  have hmap_eq : (M.subgroupOf X).map X.subtype = X ⊓ M := by
    rw [Subgroup.subgroupOf_map_subtype, inf_comm]
  obtain ⟨hr3, t, htord, hpceq, L, hLnorm, htop, hshape⟩ := hc
  refine ⟨hr3, (t : G), ?_, ?_, ?_⟩
  · exact (orderOf_injective X.subtype X.subtype_injective t).trans htord
  · have h := congrArg (Subgroup.map X.subtype) hpceq
    rwa [pCoreOf_map_subtype', hmap_eq, MonoidHom.map_zpowers] at h
  · refine ⟨L.map X.subtype, Subgroup.map_subtype_le L, ?_, ?_, ?_⟩
    · have hsub : (L.map X.subtype).subgroupOf X = L := by
        rw [← Subgroup.comap_subtype,
          Subgroup.comap_map_eq_self_of_injective X.subtype_injective L]
      rw [hsub]
      exact hLnorm
    · have htopG : (⊤ : Subgroup ↥X).map X.subtype = X := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      have hmap_sup : (L ⊔ M.subgroupOf X).map X.subtype = L.map X.subtype ⊔ (X ⊓ M) := by
        rw [Subgroup.map_sup, hmap_eq]
      have h := congrArg (Subgroup.map X.subtype) htop
      rw [htopG, hmap_sup] at h
      exact h.symm.trans (sup_comm _ _)
    · rcases hshape with hgf | ⟨halt, htrans⟩
      · exact Or.inl (graphFieldShape_map_subtype' hgf)
      · obtain ⟨eL⟩ := halt
        exact Or.inr ⟨⟨(Subgroup.equivMapOfInjective L X.subtype X.subtype_injective).symm.trans
          eL⟩, inducesTransposition_map_subtype' htrans⟩

end CFSG.LocalAnalysis.UniquenessCase.UCK
