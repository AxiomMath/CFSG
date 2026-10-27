module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneThree
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs
import CFSG.LocalAnalysis.UniquenessCase.UC6S9

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

@[expose] def Star36 (X : Type) [Group X] [Finite X] : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → 3 < CFSG.Open.twoLocalPrimeRank q X →
    ∀ S : Subgroup X, CFSG.ABGLocalTools.IsSylowOf q S ⊤ →
      (rankThreeGamma 1 q S ⊔ ⨆ (Y : Subgroup X) (_ : Y ≤ S) (_ : 1 < CFSG.Open.pRank q Y),
          ⨆ N ∈ calMOf Y, N) ≠ ⊤ ∨
        (3 < q ∧ (3 ∣ Nat.card X → ∃ N : Subgroup X, IsStronglyPEmbedded 3 N))

variable {G : Type} [Group G] [Finite G]

private theorem map_normalizer_subtype_le {H : Subgroup G} (Q : Subgroup ↥H) :
    (Subgroup.normalizer (Q : Set ↥H)).map H.subtype ≤
      Subgroup.normalizer (Q.map H.subtype : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  show ∀ n, n ∈ Q.map H.subtype ↔ H.subtype x * n * (H.subtype x)⁻¹ ∈ Q.map H.subtype
  intro y
  constructor
  · rintro ⟨y', hy', rfl⟩
    exact Subgroup.mem_map.mpr ⟨x * y' * x⁻¹, (hx y').1 hy', by simp [map_mul]⟩
  · rintro ⟨y', hy', hy'eq⟩
    refine Subgroup.mem_map.mpr ⟨x⁻¹ * y' * x, (hx (x⁻¹ * y' * x)).2 ?_, ?_⟩
    · have : x * (x⁻¹ * y' * x) * x⁻¹ = y' := by group
      rw [this]; exact hy'
    · rw [map_mul, map_mul, map_inv, hy'eq]
      group

private theorem pCoreOf_map_subtype {H : Subgroup G} (p : ℕ) (K : Subgroup ↥H) :
    (pCoreOf p K).map H.subtype = pCoreOf p (K.map H.subtype) := by
  let e : ↥K ≃* ↥(K.map H.subtype) := K.equivMapOfInjective H.subtype H.subtype_injective
  have hcomp : (H.subtype : ↥H →* G).comp K.subtype =
      (K.map H.subtype).subtype.comp e.toMonoidHom := MonoidHom.ext fun x =>
    Subgroup.coe_equivMapOfInjective_apply K H.subtype H.subtype_injective x
  simp only [pCoreOf]
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, CFSG.pCore_map_iso p e]

private theorem isGraphFieldAut_conj {K K' : Type} [Group K] [Group K'] (φ : K ≃* K')
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

private theorem conjOn_map_subtype_apply {H : Subgroup G} (L : Subgroup ↥H) {t : ↥H}
    (ht : t ∈ Subgroup.normalizer (L : Set ↥H))
    (ht' : (t : G) ∈ Subgroup.normalizer (L.map H.subtype : Set G)) (x : ↥L) :
    (Subgroup.equivMapOfInjective L H.subtype H.subtype_injective) (UC6.conjOn L ht x) =
      UC6.conjOn (L.map H.subtype) ht'
        ((Subgroup.equivMapOfInjective L H.subtype H.subtype_injective) x) := by
  apply Subtype.ext
  show H.subtype (t * x * t⁻¹) =
    (t : G) * (Subgroup.equivMapOfInjective L H.subtype H.subtype_injective x : G) * (t : G)⁻¹
  rw [Subgroup.coe_equivMapOfInjective_apply, map_mul, map_mul, map_inv]
  rfl

private theorem inducesGraphField_map_subtype {H : Subgroup G} {L : Subgroup ↥H} {t : ↥H}
    (h : UC6.InducesGraphField t L) :
    UC6.InducesGraphField (t : G) (L.map H.subtype) := by
  obtain ⟨ht, hauto⟩ := h
  have ht' : (t : G) ∈ Subgroup.normalizer (L.map H.subtype : Set G) :=
    map_normalizer_subtype_le L (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)
  refine ⟨ht', ?_⟩
  have hconj : UC6.conjOn (L.map H.subtype) ht' =
      (Subgroup.equivMapOfInjective L H.subtype H.subtype_injective).symm.trans
        ((UC6.conjOn L ht).trans (Subgroup.equivMapOfInjective L H.subtype H.subtype_injective)) := by
    apply MulEquiv.ext
    intro x
    calc UC6.conjOn (L.map H.subtype) ht' x
        = UC6.conjOn (L.map H.subtype) ht'
            ((Subgroup.equivMapOfInjective L H.subtype H.subtype_injective)
              ((Subgroup.equivMapOfInjective L H.subtype H.subtype_injective).symm x)) := by
          rw [MulEquiv.apply_symm_apply]
      _ = (Subgroup.equivMapOfInjective L H.subtype H.subtype_injective)
            (UC6.conjOn L ht ((Subgroup.equivMapOfInjective L H.subtype H.subtype_injective).symm x)) :=
          (conjOn_map_subtype_apply L ht ht' _).symm
      _ = ((Subgroup.equivMapOfInjective L H.subtype H.subtype_injective).symm.trans
            ((UC6.conjOn L ht).trans
              (Subgroup.equivMapOfInjective L H.subtype H.subtype_injective))) x := by
          rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
  rw [hconj]
  exact isGraphFieldAut_conj (Subgroup.equivMapOfInjective L H.subtype H.subtype_injective) hauto

private theorem inducesTransposition_map_subtype {H : Subgroup G} {L : Subgroup ↥H} {t : ↥H}
    (h : UC6.InducesTransposition t L) :
    UC6.InducesTransposition (t : G) (L.map H.subtype) := by
  obtain ⟨ht, e, τ, hτ, he⟩ := h
  have ht' : (t : G) ∈ Subgroup.normalizer (L.map H.subtype : Set G) :=
    map_normalizer_subtype_le L (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)
  let eL := Subgroup.equivMapOfInjective L H.subtype H.subtype_injective
  refine ⟨ht', eL.symm.trans e, τ, hτ, fun x => ?_⟩
  have hx : UC6.conjOn (L.map H.subtype) ht' x = eL (UC6.conjOn L ht (eL.symm x)) := by
    rw [conjOn_map_subtype_apply L ht ht' (eL.symm x), MulEquiv.apply_symm_apply]
  rw [hx]
  simpa only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using he (eL.symm x)

private theorem graphFieldShape_map_subtype {H : Subgroup G} {t : ↥H} {L : Subgroup ↥H}
    (h : UC6.GraphFieldShape t L) :
    UC6.GraphFieldShape (t : G) (L.map H.subtype) := by
  let eL := Subgroup.equivMapOfInjective L H.subtype H.subtype_injective
  rcases h with ⟨hcase, hgf⟩ | ⟨L₁, L₂, hsup, hcomm, h₁, h₂, hcenter, hgf₁, hgf₂⟩
  · left
    refine ⟨?_, inducesGraphField_map_subtype hgf⟩
    rcases hcase with hcase | hcase
    · exact Or.inl ⟨eL.symm.trans (Classical.choice hcase)⟩
    · exact Or.inr ⟨eL.symm.trans (Classical.choice hcase)⟩
  · right
    let e₁' := Subgroup.equivMapOfInjective L₁ H.subtype H.subtype_injective
    let e₂' := Subgroup.equivMapOfInjective L₂ H.subtype H.subtype_injective
    refine ⟨L₁.map H.subtype, L₂.map H.subtype, ?_, ?_,
      ⟨e₁'.symm.trans (Classical.choice h₁)⟩,
      ⟨e₂'.symm.trans (Classical.choice h₂)⟩, ?_, inducesGraphField_map_subtype hgf₁,
      inducesGraphField_map_subtype hgf₂⟩
    · rw [← Subgroup.map_sup, hsup]
    · intro a ha b hb
      obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
      simpa using congrArg H.subtype (hcomm a₀ ha₀ b₀ hb₀)
    · rw [← Subgroup.map_inf_eq L₁ L₂ H.subtype H.subtype_injective, hcenter,
        Subgroup.map_map]
      have hcomp : (H.subtype : ↥H →* G).comp L₁.subtype =
          (L₁.map H.subtype).subtype.comp e₁'.toMonoidHom := MonoidHom.ext fun x =>
        Subgroup.coe_equivMapOfInjective_apply L₁ H.subtype H.subtype_injective x
      have hcenter' : (Subgroup.center ↥L₁).map e₁'.toMonoidHom =
          Subgroup.center ↥(L₁.map H.subtype) := Subgroup.map_center_eq e₁'
      rw [hcomp, ← Subgroup.map_map, hcenter']

private theorem le_subgroupOf_of_isTwoLocal {D : Data G} {H : Subgroup G} {E : Subgroup G}
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (h63 : UC6.R6_3 D) (hEM : E ≤ D.M)
    (hEel : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2)
    (hΓ : rankThreeGamma 1 r E ≤ D.M) (hEH : E ≤ H)
    {N : Subgroup ↥H} (hN : IsTwoLocal N) (hE'N : E.subgroupOf H ≤ N) :
    N ≤ D.M.subgroupOf H := by
  obtain ⟨P, hPne, hP2, rfl⟩ := hN
  have hP₀ne : P.map H.subtype ≠ ⊥ := fun h =>
    hPne (Subgroup.map_eq_bot_iff_of_injective P H.subtype_injective |>.1 h)
  have hP₀2 : IsPGroup 2 (P.map H.subtype) := hP2.map H.subtype
  obtain ⟨N', hN'max, hN'⟩ := UC6.exists_rankThreeIsMaxTwoLocal_ge_uc6
    (show IsTwoLocal (Subgroup.normalizer (P.map H.subtype : Set G)) from
      ⟨_, hP₀ne, hP₀2, rfl⟩)
  have hEN' : E ≤ N' := by
    have h2 : E = (E.subgroupOf H).map H.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hEH).symm
    rw [h2]
    exact (Subgroup.map_mono hE'N).trans ((map_normalizer_subtype_le P).trans hN')
  have hN'eq : N' = D.M := by
    have hmem : N' ∈ calMOf E := ⟨hN'max, hEN'⟩
    have hEq : calMOf E = {D.M} := h63 r hr hr2 E hEM hEel hEcard hΓ
    rw [hEq] at hmem
    simpa using hmem
  intro x hx
  have hx' : (x : G) ∈ D.M :=
    (hN'eq ▸ hN') ((map_normalizer_subtype_le P) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
  exact Subgroup.mem_subgroupOf.mpr hx'

private theorem calMOf_subgroupOf_eq_singleton {D : Data G} {H : Subgroup G} {E : Subgroup G}
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (h63 : UC6.R6_3 D) (hEM : E ≤ D.M)
    (hEel : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2)
    (hΓ : rankThreeGamma 1 r E ≤ D.M) (hEH : E ≤ H)
    (hQ : pCoreOf 2 (D.M.subgroupOf H) ≠ ⊥) :
    calMOf (E.subgroupOf H) = {D.M.subgroupOf H} := by
  have hE'HM : E.subgroupOf H ≤ D.M.subgroupOf H := fun x hx => hEM hx
  have hP2 : IsPGroup 2 (pCoreOf 2 (D.M.subgroupOf H)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (D.M.subgroupOf H)
  have hle : D.M.subgroupOf H ≤ Subgroup.normalizer (pCoreOf 2 (D.M.subgroupOf H) : Set ↥H) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (D.M.subgroupOf H)
  have hge : Subgroup.normalizer (pCoreOf 2 (D.M.subgroupOf H) : Set ↥H) ≤
      D.M.subgroupOf H :=
    le_subgroupOf_of_isTwoLocal hr hr2 h63 hEM hEel hEcard hΓ hEH
      ⟨_, hQ, hP2, rfl⟩ (hE'HM.trans hle)
  have hM2local : IsTwoLocal (D.M.subgroupOf H) :=
    ⟨_, hQ, hP2, le_antisymm hle hge⟩
  have hMmax : rankThreeIsMaxTwoLocal (D.M.subgroupOf H) := by
    refine ⟨hM2local, fun K hK hleKM => ?_⟩
    exact le_antisymm
      (le_subgroupOf_of_isTwoLocal hr hr2 h63 hEM hEel hEcard hΓ hEH hK
        (hE'HM.trans hleKM)) hleKM
  ext N
  constructor
  · rintro ⟨hNmax, hE'N⟩
    have hNle : N ≤ D.M.subgroupOf H :=
      le_subgroupOf_of_isTwoLocal hr hr2 h63 hEM hEel hEcard hΓ hEH hNmax.1 hE'N
    exact (hNmax.2 _ hM2local hNle).symm
  · rintro rfl
    exact ⟨hMmax, hE'HM⟩

private theorem twoLocalPrimeRank_subgroupOf_le_evenRank (H : Subgroup G) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) :
    CFSG.Open.twoLocalPrimeRank q ↥H ≤ evenRank G := by
  unfold CFSG.Open.twoLocalPrimeRank
  apply csSup_le'
  rintro k ⟨N, hN, hk⟩
  rw [← hk]
  obtain ⟨P, hPne, hP2, rfl⟩ := hN
  have hP₀ne : P.map H.subtype ≠ ⊥ := fun h =>
    hPne (Subgroup.map_eq_bot_iff_of_injective P H.subtype_injective |>.1 h)
  have hP₀2 : IsPGroup 2 (P.map H.subtype) := hP2.map H.subtype
  have hloc : IsTwoLocal (Subgroup.normalizer (P.map H.subtype : Set G)) :=
    ⟨_, hP₀ne, hP₀2, rfl⟩
  have h1 : CFSG.Open.pRank q (Subgroup.normalizer (P : Set ↥H)) ≤
      CFSG.Open.pRank q ((Subgroup.normalizer (P : Set ↥H)).map H.subtype) :=
    CFSG.SectionRank.pRank_le_map hq.one_lt H.subtype H.subtype_injective
      (Subgroup.normalizer (P : Set ↥H))
  have h2 : CFSG.Open.pRank q ((Subgroup.normalizer (P : Set ↥H)).map H.subtype) ≤
      CFSG.Open.pRank q (Subgroup.normalizer (P.map H.subtype : Set G)) :=
    CFSG.SectionRank.pRank_mono hq.one_lt (map_normalizer_subtype_le P)
  exact h1.trans (h2.trans
    (CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank q hq hq2 _ hloc))

theorem r6_7_of_K36 (D : Data G) (hK : UCK.K36) (h63 : UC6.R6_3 D)
    (hstar : ∀ H : Subgroup G, H ≠ ⊤ → Star36 ↥H) : UC6.R6_7 D := by
  intro _hsub r hr hr2 E hEM hEel hEcard hΓ H hEH hHtop hQ HnM
  have hmap_eq : (D.M.subgroupOf H).map H.subtype = H ⊓ D.M := by
    rw [Subgroup.subgroupOf_map_subtype, inf_comm]
  have hHMtop : D.M.subgroupOf H ≠ ⊤ := fun h => HnM ((Subgroup.subgroupOf_eq_top).1 h)
  have hQ' : pCoreOf 2 (D.M.subgroupOf H) ≠ ⊥ := by
    intro h
    apply hQ
    have h2 : (pCoreOf 2 (D.M.subgroupOf H)).map H.subtype =
        (⊥ : Subgroup ↥H).map H.subtype := by rw [h]
    rw [Subgroup.map_bot, pCoreOf_map_subtype, hmap_eq] at h2
    exact h2
  have hE'el : IsElemAbelian r (E.subgroupOf H) := hEel.subgroupOf H
  have hE'card : Nat.card (E.subgroupOf H) = r ^ 2 := by
    calc Nat.card (E.subgroupOf H) = Nat.card ((E.subgroupOf H).map H.subtype) :=
          (Subgroup.card_map_of_injective H.subtype_injective).symm
      _ = Nat.card E := by rw [Subgroup.map_subgroupOf_eq_of_le hEH]
      _ = r ^ 2 := hEcard
  have hΓ' : rankThreeGamma 1 r (E.subgroupOf H) ≤ D.M.subgroupOf H := by
    rw [CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff]
    intro Y hYE' hY1
    have hY0E : Y.map H.subtype ≤ E := by
      rw [Subgroup.map_le_iff_le_comap, Subgroup.comap_subtype]
      exact hYE'
    have hY0rank : 1 ≤ CFSG.Open.pRank r (Y.map H.subtype) :=
      hY1.trans (CFSG.SectionRank.pRank_le_map hr.one_lt H.subtype H.subtype_injective Y)
    have hNle : Subgroup.normalizer (Y.map H.subtype : Set G) ≤ D.M :=
      (CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff 1 r E D.M).1 hΓ
        (Y.map H.subtype) hY0E hY0rank
    intro x hx
    have hx' : (x : G) ∈ D.M :=
      hNle ((map_normalizer_subtype_le Y) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
    exact Subgroup.mem_subgroupOf.mpr hx'
  have hcal : calMOf (E.subgroupOf H) = {D.M.subgroupOf H} :=
    calMOf_subgroupOf_eq_singleton hr hr2 h63 hEM hEel hEcard hΓ hEH hQ'
  obtain ⟨hr3, t, htord, hpceq, L, hLnorm, htop, hshape⟩ :=
    hK ↥H (D.standing.kProper.isKGroup H hHtop) (D.M.subgroupOf H) hHMtop hQ' r hr hr2
      (E.subgroupOf H) hE'el hE'card hΓ' hcal (hstar H hHtop)
  refine ⟨hr3, (t : G), ?_, ?_, ?_⟩
  · exact (orderOf_injective H.subtype H.subtype_injective t).trans htord
  · have h := congrArg (Subgroup.map H.subtype) hpceq
    rwa [pCoreOf_map_subtype, hmap_eq, MonoidHom.map_zpowers] at h
  · refine ⟨L.map H.subtype, Subgroup.map_subtype_le L, ?_, ?_, ?_⟩
    · have hsub : (L.map H.subtype).subgroupOf H = L := by
        rw [← Subgroup.comap_subtype,
          Subgroup.comap_map_eq_self_of_injective H.subtype_injective L]
      rw [hsub]
      exact hLnorm
    · have htopG : (⊤ : Subgroup ↥H).map H.subtype = H := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      have hmap_sup : (L ⊔ D.M.subgroupOf H).map H.subtype =
          L.map H.subtype ⊔ (H ⊓ D.M) := by
        rw [Subgroup.map_sup, hmap_eq]
      have h := congrArg (Subgroup.map H.subtype) htop
      rw [htopG, hmap_sup] at h
      exact h.symm.trans (sup_comm _ _)
    · rcases hshape with hgf | ⟨halt, htrans⟩
      · exact Or.inl (graphFieldShape_map_subtype hgf)
      · obtain ⟨eL⟩ := halt
        exact Or.inr ⟨⟨(Subgroup.equivMapOfInjective L H.subtype H.subtype_injective).symm.trans
          eL⟩, inducesTransposition_map_subtype htrans⟩

@[expose] def Star36At (D : Data G) : Prop :=
  D.sig ⊆ D.sig1 → ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian r E →
    Nat.card E = r ^ 2 → rankThreeGamma 1 r E ≤ D.M → ∀ H : Subgroup G, E ≤ H → H ≠ ⊤ →
      pCoreOf 2 (H ⊓ D.M) ≠ ⊥ → ¬ H ≤ D.M → Star36 ↥H

theorem r6_7_of_K36_at (D : Data G) (hK : UCK.K36) (h63 : UC6.R6_3 D) (hstar : Star36At D) :
    UC6.R6_7 D := by
  intro hsub r hr hr2 E hEM hEel hEcard hΓ H hEH hHtop hQ HnM
  have hmap_eq : (D.M.subgroupOf H).map H.subtype = H ⊓ D.M := by
    rw [Subgroup.subgroupOf_map_subtype, inf_comm]
  have hHMtop : D.M.subgroupOf H ≠ ⊤ := fun h => HnM ((Subgroup.subgroupOf_eq_top).1 h)
  have hQ' : pCoreOf 2 (D.M.subgroupOf H) ≠ ⊥ := by
    intro h
    apply hQ
    have h2 : (pCoreOf 2 (D.M.subgroupOf H)).map H.subtype =
        (⊥ : Subgroup ↥H).map H.subtype := by rw [h]
    rw [Subgroup.map_bot, pCoreOf_map_subtype, hmap_eq] at h2
    exact h2
  have hE'el : IsElemAbelian r (E.subgroupOf H) := hEel.subgroupOf H
  have hE'card : Nat.card (E.subgroupOf H) = r ^ 2 := by
    calc Nat.card (E.subgroupOf H) = Nat.card ((E.subgroupOf H).map H.subtype) :=
          (Subgroup.card_map_of_injective H.subtype_injective).symm
      _ = Nat.card E := by rw [Subgroup.map_subgroupOf_eq_of_le hEH]
      _ = r ^ 2 := hEcard
  have hΓ' : rankThreeGamma 1 r (E.subgroupOf H) ≤ D.M.subgroupOf H := by
    rw [CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff]
    intro Y hYE' hY1
    have hY0E : Y.map H.subtype ≤ E := by
      rw [Subgroup.map_le_iff_le_comap, Subgroup.comap_subtype]
      exact hYE'
    have hY0rank : 1 ≤ CFSG.Open.pRank r (Y.map H.subtype) :=
      hY1.trans (CFSG.SectionRank.pRank_le_map hr.one_lt H.subtype H.subtype_injective Y)
    have hNle : Subgroup.normalizer (Y.map H.subtype : Set G) ≤ D.M :=
      (CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff 1 r E D.M).1 hΓ
        (Y.map H.subtype) hY0E hY0rank
    intro x hx
    have hx' : (x : G) ∈ D.M :=
      hNle ((map_normalizer_subtype_le Y) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
    exact Subgroup.mem_subgroupOf.mpr hx'
  have hcal : calMOf (E.subgroupOf H) = {D.M.subgroupOf H} :=
    calMOf_subgroupOf_eq_singleton hr hr2 h63 hEM hEel hEcard hΓ hEH hQ'
  obtain ⟨hr3, t, htord, hpceq, L, hLnorm, htop, hshape⟩ :=
    hK ↥H (D.standing.kProper.isKGroup H hHtop) (D.M.subgroupOf H) hHMtop hQ' r hr hr2
      (E.subgroupOf H) hE'el hE'card hΓ' hcal (hstar hsub r hr hr2 E hEM hEel hEcard hΓ H hEH hHtop hQ HnM)
  refine ⟨hr3, (t : G), ?_, ?_, ?_⟩
  · exact (orderOf_injective H.subtype H.subtype_injective t).trans htord
  · have h := congrArg (Subgroup.map H.subtype) hpceq
    rwa [pCoreOf_map_subtype, hmap_eq, MonoidHom.map_zpowers] at h
  · refine ⟨L.map H.subtype, Subgroup.map_subtype_le L, ?_, ?_, ?_⟩
    · have hsub' : (L.map H.subtype).subgroupOf H = L := by
        rw [← Subgroup.comap_subtype,
          Subgroup.comap_map_eq_self_of_injective H.subtype_injective L]
      rw [hsub']
      exact hLnorm
    · have htopG : (⊤ : Subgroup ↥H).map H.subtype = H := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      have hmap_sup : (L ⊔ D.M.subgroupOf H).map H.subtype =
          L.map H.subtype ⊔ (H ⊓ D.M) := by
        rw [Subgroup.map_sup, hmap_eq]
      have h := congrArg (Subgroup.map H.subtype) htop
      rw [htopG, hmap_sup] at h
      exact h.symm.trans (sup_comm _ _)
    · rcases hshape with hgf | ⟨halt, htrans⟩
      · exact Or.inl (graphFieldShape_map_subtype hgf)
      · obtain ⟨eL⟩ := halt
        exact Or.inr ⟨⟨(Subgroup.equivMapOfInjective L H.subtype H.subtype_injective).symm.trans
          eL⟩, inducesTransposition_map_subtype htrans⟩

namespace Three

open CFSG.LocalAnalysis.RankThreeUC

theorem r6_7_dataOfSetup (hS : Standing G) (hUC : rankThreeUC G) (hC : AGL81TheoremC G)
    (hK : UCK.K36) (S : Setup G) : UC6.R6_7 (dataOfSetup hS S) := by
  refine r6_7_of_K36 (dataOfSetup hS S) hK (r6_3_dataOfSetup hS hUC hC S) (fun H _ => ?_)
  intro q hq hq2 h3
  exfalso
  have hle : CFSG.Open.twoLocalPrimeRank q ↥H ≤ evenRank G :=
    twoLocalPrimeRank_subgroupOf_le_evenRank H hq hq2
  rw [hS.rank] at hle
  omega

end Three

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
