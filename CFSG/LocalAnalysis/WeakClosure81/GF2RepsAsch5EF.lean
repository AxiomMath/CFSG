module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (IsEP eGenP InEP InFFor InF ETwoPrint)
open scoped Pointwise

private theorem gf2_EF_map_map_mk'_congr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    {N : Subgroup Q} {N' : Subgroup Q'} [N.Normal] [N'.Normal] (h : N.map e.toMonoidHom = N')
    (B : Subgroup Q) :
    (B.map (QuotientGroup.mk' N)).map (QuotientGroup.congr N N' e h).toMonoidHom =
      (B.map e.toMonoidHom).map (QuotientGroup.mk' N') := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

theorem eTwoPrint_map_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] [Finite Q] [Finite Q']
    (e : Q ≃* Q') (Ta B : Subgroup Q) :
    ETwoPrint Q Ta B ↔ ETwoPrint Q' (Ta.map e.toMonoidHom) (B.map e.toMonoidHom) := by
  have hR := E1.solvableRadical_map_mulEquiv e
  have hO := E1.oInftyE_map_mulEquiv e
  have hbar : (E1.barRad Q B).map (QuotientGroup.congr _ _ e hR).toMonoidHom =
      E1.barRad Q' (B.map e.toMonoidHom) := gf2_EF_map_map_mk'_congr e hR B
  unfold ETwoPrint
  refine and_congr (by rw [← hR, E1.isTwoClosed_map_mulEquiv]) (and_congr ?_ (and_congr ?_ ?_))
  · rw [← E1.map_eq_top_iff_mulEquiv (QuotientGroup.congr _ _ e hO),
      CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (QuotientGroup.congr _ _ e hO)]
  · have h1 : (twoResidual (⊤ : Subgroup Q)).map e.toMonoidHom =
        twoResidual (⊤ : Subgroup Q') := by
      rw [E1.twoResidual_map_mulEquiv, Subgroup.map_top_of_surjective _ e.surjective]
    have h2 : (perfectCore (⊤ : Subgroup Q)).map e.toMonoidHom = perfectCore (⊤ : Subgroup Q') := by
      rw [map_perfectCore, Subgroup.map_top_of_surjective _ e.surjective]
    rw [← h1, ← h2, E1.map_inj_mulEquiv]
  · refine E1.exists_subgroup_congr (QuotientGroup.congr _ _ e hR) fun L => ?_
    have hτ : (Ta.map (QuotientGroup.mk' (solvableRadical Q))).map
        (QuotientGroup.congr _ _ e hR).toMonoidHom =
        (Ta.map e.toMonoidHom).map (QuotientGroup.mk' (solvableRadical Q')) :=
      gf2_EF_map_map_mk'_congr e hR Ta
    refine and_congr ((CFSG.LocalCores.component_isomorphism _).1 L) (and_congr ?_ ?_)
    · have hb := E1.map_biSup_conjSub (QuotientGroup.congr _ _ e hR)
        (Ta.map (QuotientGroup.mk' (solvableRadical Q))) L
      unfold A1b.conjSub at hb
      rw [← E1.map_inj_mulEquiv (QuotientGroup.congr _ _ e hR), E1.layer_map_mulEquiv, hb, hτ]
    · rw [E1.card_barRad_map, ← hbar, ← Subgroup.map_commutator, E1.map_inj_mulEquiv,
        ← Subgroup.map_equiv_normalizer_eq, E1.map_le_map_iff_mulEquiv]

private abbrev gf2_EF_restrictEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (K : Subgroup G) : ↥K ≃* ↥(K.map e.toMonoidHom) :=
  e.subgroupMap K

private theorem gf2_EF_map_subgroupOf_restrictEquiv {G G' : Type} [Group G] [Group G']
    (e : G ≃* G') (A K : Subgroup G) :
    (A.subgroupOf K).map (gf2_EF_restrictEquiv e K).toMonoidHom =
      (A.map e.toMonoidHom).subgroupOf (K.map e.toMonoidHom) := by
  ext ⟨y, hy⟩
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    Subgroup.mem_map_equiv]
  exact Iff.rfl

theorem isEP_map_mulEquiv {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']
    (e : G ≃* G') {i : ℕ} {H T A K : Subgroup G} :
    IsEP i (H.map e.toMonoidHom) (T.map e.toMonoidHom) (A.map e.toMonoidHom)
        (K.map e.toMonoidHom) ↔ IsEP i H T A K := by
  unfold IsEP
  rw [← Subgroup.map_inf T K e.toMonoidHom e.injective, E1.tauOf_map_mulEquiv,
    ← gf2_EF_map_subgroupOf_restrictEquiv e A K,
    ← gf2_EF_map_subgroupOf_restrictEquiv e (E1.tauOf H T A) K,
    E1.map_le_map_iff_mulEquiv, E1.map_le_map_iff_mulEquiv, E1.isSylowIn_map_mulEquiv,
    ← E1.eOne_map, ← eTwoPrint_map_mulEquiv, E1.card_barO2_map, E1.card_barRad_map]

private theorem gf2_EF_eGenP_map_image {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']
    (e : G ≃* G') (i : ℕ) (H T : Subgroup G) (Ω : Set (Subgroup G)) :
    eGenP i (H.map e.toMonoidHom) (T.map e.toMonoidHom) (Subgroup.map e.toMonoidHom '' Ω) =
      (eGenP i H T Ω).map e.toMonoidHom := by
  apply le_antisymm
  · refine iSup₂_le fun A' hA' => iSup_le fun hA'T => iSup₂_le fun K' hK' => ?_
    obtain ⟨A, hA, rfl⟩ := hA'
    obtain ⟨K, rfl⟩ : ∃ K : Subgroup G, K.map e.toMonoidHom = K' :=
      ⟨K'.comap e.toMonoidHom, Subgroup.map_comap_eq_self_of_surjective e.surjective K'⟩
    have hK : IsEP i H T A K := (isEP_map_mulEquiv e).mp hK'
    exact Subgroup.map_mono (le_iSup₂_of_le A hA (le_iSup_of_le
      ((E1.map_le_map_iff_mulEquiv e).mp hA'T) (le_iSup₂_of_le K hK le_rfl)))
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_iSup₂_of_le (A.map e.toMonoidHom) ⟨A, hA, rfl⟩ (le_iSup_of_le
      (Subgroup.map_mono hAT) (le_iSup₂_of_le (K.map e.toMonoidHom)
        ((isEP_map_mulEquiv e).mpr hK) le_rfl))

theorem conjSub_eGenP {G : Type} [Group G] [Finite G] (i : ℕ) {T : Subgroup G}
    {Ω : Set (Subgroup G)} (hΩ : E1.IsInvColl (⊤ : Subgroup G) Ω) {t : G} (ht : t ∈ T) :
    A1b.conjSub t (eGenP i (⊤ : Subgroup G) T Ω) = eGenP i (⊤ : Subgroup G) T Ω := by
  have h := gf2_EF_eGenP_map_image (MulAut.conj t) i (⊤ : Subgroup G) T Ω
  have hT : A1b.conjSub t T = T := A1b.conjSub_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer ht)
  have hTop : A1b.conjSub t (⊤ : Subgroup G) = ⊤ :=
    Subgroup.map_top_of_surjective _ (MulAut.conj t).surjective
  have hΩt : A1b.conjSub t '' Ω = Ω := by
    ext B
    refine ⟨?_, fun hB => ⟨A1b.conjSub t⁻¹ B, hΩ.conj B hB t⁻¹ (Subgroup.mem_top _), ?_⟩⟩
    · rintro ⟨C, hC, rfl⟩
      exact hΩ.conj C hC t (Subgroup.mem_top _)
    · rw [← A1b.conjSub_mul, mul_inv_cancel, A1b.conjSub_one]
  change eGenP i (A1b.conjSub t ⊤) (A1b.conjSub t T) (A1b.conjSub t '' Ω) = _ at h
  rw [hTop, hT, hΩt] at h
  exact h.symm

theorem le_normalizer_eGenP {G : Type} [Group G] [Finite G] (i : ℕ) {T : Subgroup G}
    {Ω : Set (Subgroup G)} (hΩ : E1.IsInvColl (⊤ : Subgroup G) Ω) :
    T ≤ normalizer (eGenP i (⊤ : Subgroup G) T Ω : Set G) := fun _ ht =>
  A1b.conjSub_eq_iff_mem_normalizer.mp (conjSub_eGenP i hΩ ht)

theorem exists_mem_le_of_isSylowOf {Q : Type} [Group Q] [Finite Q] {T : Subgroup Q}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) {Ω : Set (Subgroup Q)}
    (hΩ : E1.IsInvColl (⊤ : Subgroup Q) Ω) (hne : Ω.Nonempty) : ∃ A ∈ Ω, A ≤ T := by
  obtain ⟨B, hB⟩ := hne
  have hB2 : IsPGroup 2 B :=
    fun g => ⟨1, Subtype.ext (by simpa using (hΩ.isElemAbelian B hB).2 g g.2)⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hBS⟩ := hB2.exists_le_sylow
  have hS : IsSylowIn 2 (S : Subgroup Q) ⊤ := isSylowIn_top S
  have hT' : IsSylowIn 2 T ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.mp hT
  obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj hS hT'
  refine ⟨A1b.conjSub g B, hΩ.conj B hB g (Subgroup.mem_top _), ?_⟩
  rw [hg]
  exact A1b.conjSub_mono g hBS

theorem normalizer_weakClosure_lt_top {Q : Type} [Group Q] [Finite Q] {T : Subgroup Q}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) {Ω : Set (Subgroup Q)}
    (hΩ : E1.IsInvColl (⊤ : Subgroup Q) Ω) (hne : Ω.Nonempty) (hbot : ∀ A ∈ Ω, A ≠ ⊥)
    (hO : CFSG.pCore 2 Q = ⊥) : normalizer (E1.weakClosure T Ω : Set Q) < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro hN
  obtain ⟨A, hA, hAT⟩ := exists_mem_le_of_isSylowOf hT hΩ hne
  have hAW : A ≤ E1.weakClosure T Ω := le_iSup₂_of_le A hA (le_iSup_of_le hAT le_rfl)
  have hWT : E1.weakClosure T Ω ≤ T := iSup₂_le fun B _ => iSup_le fun hBT => hBT
  have hT2 : IsPGroup 2 T := (CFSG.ABGLocalTools.isSylowOf_iff.mp hT).2.1
  have hW2 : IsPGroup 2 (E1.weakClosure T Ω) := hT2.to_le hWT
  have hWn : (E1.weakClosure T Ω).Normal := Subgroup.normalizer_eq_top_iff.mp hN
  have hle : E1.weakClosure T Ω ≤ CFSG.pCore 2 Q :=
    CFSG.LieType.BorelTits.le_pCore 2 hWn hW2
  rw [hO] at hle
  exact hbot A hA (le_bot_iff.mp (hAW.trans hle))

theorem inFFor_top_of_inEP {Q : Type} [Group Q] [Finite Q] (j : ℕ) {T : Subgroup Q}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hE : InEP j (⊤ : Subgroup Q))
    (hU : HasUniqueMaxOver T) (hO : CFSG.pCore 2 Q = ⊥) : InFFor j (⊤ : Subgroup Q) T := by
  intro Ω hΩ hne hbot
  obtain ⟨M, hMtop, hM⟩ := hU
  have h1 : eGenP j (⊤ : Subgroup Q) T Ω ⊔ normalizer (E1.weakClosure T Ω : Set Q) = ⊤ := by
    have := hE T hT Ω hΩ hne hbot
    rwa [top_inf_eq] at this
  have hTN : T ≤ normalizer (E1.weakClosure T Ω : Set Q) := E1.le_normalizer_weakClosure hΩ
  have hNlt : normalizer (E1.weakClosure T Ω : Set Q) < ⊤ :=
    normalizer_weakClosure_lt_top hT hΩ hne hbot hO
  have hNM : normalizer (E1.weakClosure T Ω : Set Q) ≤ M := hM _ hTN hNlt
  have hET : eGenP j (⊤ : Subgroup Q) T Ω ⊔ T = ⊤ := by
    by_contra hne'
    have hlt : eGenP j (⊤ : Subgroup Q) T Ω ⊔ T < ⊤ := lt_top_iff_ne_top.mpr hne'
    have hX : eGenP j (⊤ : Subgroup Q) T Ω ⊔ T ≤ M := hM _ le_sup_right hlt
    have htop : (⊤ : Subgroup Q) ≤ M := by
      rw [← h1]
      exact sup_le (le_sup_left.trans hX) hNM
    exact absurd (lt_of_lt_of_le hMtop htop) (lt_irrefl _)
  have hnorm : T ≤ normalizer (eGenP j (⊤ : Subgroup Q) T Ω : Set Q) :=
    le_normalizer_eGenP j hΩ
  rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ T hnorm, hET]

theorem hasUniqueMaxOver_of_isSylowOf {Q : Type} [Group Q] [Finite Q] {T T' : Subgroup Q}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hT' : CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤)
    (hU : HasUniqueMaxOver T) : HasUniqueMaxOver T' := by
  obtain ⟨M, hMtop, hM⟩ := hU
  obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj (CFSG.ABGLocalTools.isSylowOf_iff.mp hT)
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hT')
  refine ⟨A1b.conjSub g M, ?_, fun X hTX hXtop => ?_⟩
  · rw [lt_top_iff_ne_top]
    intro h
    exact absurd ((E1.map_eq_top_iff_mulEquiv (MulAut.conj g) M).mp h) (ne_of_lt hMtop)
  · have hcancel : ∀ Y : Subgroup Q, A1b.conjSub g (A1b.conjSub g⁻¹ Y) = Y := fun Y => by
      rw [← A1b.conjSub_mul, mul_inv_cancel, A1b.conjSub_one]
    have hcancel' : ∀ Y : Subgroup Q, A1b.conjSub g⁻¹ (A1b.conjSub g Y) = Y := fun Y => by
      rw [← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one]
    have hTX' : A1b.conjSub g T ≤ X := by
      rw [hg] at hTX
      exact hTX
    have h1 : T ≤ A1b.conjSub g⁻¹ X := by
      have := A1b.conjSub_mono g⁻¹ hTX'
      rwa [hcancel'] at this
    have h2 : A1b.conjSub g⁻¹ X < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro h
      exact absurd ((E1.map_eq_top_iff_mulEquiv (MulAut.conj g⁻¹) X).mp h) (ne_of_lt hXtop)
    have h3 := A1b.conjSub_mono g (hM _ h1 h2)
    rwa [hcancel] at h3

theorem inF_top_of_inEP {Q : Type} [Group Q] [Finite Q] (j : ℕ) (hE : InEP j (⊤ : Subgroup Q))
    (hU : ∃ T : Subgroup Q, CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ ∧ HasUniqueMaxOver T)
    (hO : CFSG.pCore 2 Q = ⊥) : InF j (⊤ : Subgroup Q) := by
  obtain ⟨T₀, hT₀, hU₀⟩ := hU
  intro T hT
  exact inFFor_top_of_inEP j hT hE (hasUniqueMaxOver_of_isSylowOf hT₀ hT hU₀) hO

end CFSG.LocalAnalysis.WeakClosure81
