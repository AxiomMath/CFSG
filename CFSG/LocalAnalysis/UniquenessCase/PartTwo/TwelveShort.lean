module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp
public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge4
public import CFSG.LocalAnalysis.WeakClosure81.Eleven
public import CFSG.LocalAnalysis.WeakClosure81.SixEleven
public import CFSG.LocalAnalysis.WeakClosure81.SixFourSz
public import CFSG.LocalAnalysis.WeakClosure81.SixSixteenUncond
public import CFSG.Goldschmidt.Steps.G63Basic
public import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
public import CFSG.Blueprint.SourceExceptionalModels
public import CFSG.GF2Type.Aschbacher1976
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsSetting
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
public import CFSG.Quasithin.Background.E1ElevenLift
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Walter.Bender1970.S1
public import CFSG.Walter.Bender1970.S2
public import CFSG.Walter.PSL2Facts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def R126 (D : Data G) : Prop :=
  ∀ H₀ : Subgroup G, Hyp124Min D H₀ → E1.InE D.k H₀

@[expose] def R127 (D : Data G) : Prop :=
  (∃ H₀ ∈ RankThreeUC.hSet D.T D.M, RankThreeUC.Hyp124 D.M H₀) →
    ∀ V : Subgroup G, InCalV D.M V → CFSG.CGT.Timmesfeld75.IsTI V → 8 ≤ Nat.card V →
      ¬ InCalV1 D.M D.T V ∧
        ((∀ z ∈ D.T, (∀ t ∈ D.T, z * t = t * z) → z ≠ 1 →
            centralizer ({z} : Set G) ≤ D.M) →
          ∀ X : Subgroup G, ¬ F11.InP11 D X)

@[expose] def R1211_1 (D : Data G) : Prop :=
  ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → (∃ X : Subgroup G, F11.InP11 D X) → V₀ ≠ ⊥ →
    ¬ MBarGT D.M V₀ V (D.k + 1)

@[expose] def W3Thm111 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ M V Q : Subgroup G, Setting11 M V Q → MBarGT M ⊥ V 2 →
    ∀ n : ℕ, MBarGT M ⊥ V n → (n : ℕ∞) < rMV M V

@[expose] def W3Lem616_1ii (G : Type) [Group G] [Finite G] : Prop :=
  ∀ {V M H S X : Subgroup G} (hV : IsElemAbelian 2 V), rankThreeIsMaxTwoLocal M →
    normalizer (V : Set G) = M → CFSG.QuasithinUnique.CharTwo H →
    IsSylowIn 2 S H → ∀ {k : ℕ}, 1 ≤ k → E1.InE k H → E3.wClos V 0 S ≠ ⊥ →
    k + 1 < E3.sParam hV → ∀ {p : ℕ}, p.Prime → p ≠ 2 → X ≤ M → (∀ x ∈ X, x ^ p = 1) →
    ¬ IsCyclic X → (X : Set G) * (S : Set G) = (S : Set G) * (X : Set G) →
    (∀ Y : Subgroup G, Y ≤ X → ¬ IsCyclic Y → InCalU M Y) →
    (∃ a ∈ F11.Omega1p 2 S, F11.Omega1p 2 S =
      Subgroup.zpowers a ⊔ (F11.Omega1p 2 S ⊓ pCoreOf 2 (X ⊔ S))) → H ≤ M

@[expose] def CFAutInFGroup (j : ℕ) (Q : Type) [Group Q] [Finite Q] (S : Subgroup Q) : Prop :=
  ∀ X : Subgroup Q, X.Normal → X ≠ ⊥ → (∀ N : Subgroup Q, N.Normal → N ≤ X → N = ⊥ ∨ N = X) →
    ¬ IsMulCommutative X →
    ∀ L : Subgroup Q, IsComponentOf L X →
      ∃ h : ((F12.autC S L).subgroupOf (F12.autNL S L)).Normal,
        haveI := h
        InFGroup j (↥(F12.autNL S L) ⧸ (F12.autC S L).subgroupOf (F12.autNL S L))

@[expose] def CompFactorAutInF (j : ℕ) (H S : Subgroup G) : Prop :=
  ∀ Y : Subgroup G, Y ≤ H → ∀ hY : (Y.subgroupOf H).Normal,
    haveI := hY
    CFAutInFGroup j (↥H ⧸ Y.subgroupOf H)
      ((S.subgroupOf H).map (QuotientGroup.mk' (Y.subgroupOf H)))

@[expose] def W3Lem45_2 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (H S : Subgroup G) (j : ℕ) (Ω : Set (Subgroup G)), 1 ≤ j → IsSylowIn 2 S H →
    E1.IsInvColl H Ω → CompFactorAutInF j H S →
      (H : Set G) = ((E1.eGen j H S Ω : Subgroup G) : Set G) *
        ((H ⊓ normalizer (E1.weakClosure S Ω : Set G) : Subgroup G) : Set G)

namespace TwelveShort

theorem mBarGT_mono {M V₀ V : Subgroup G} {m n : ℕ} (h : MBarGT M V₀ V n) (hmn : m ≤ n) :
    MBarGT M V₀ V m :=
  uc22br4_mBarGT_mono M V₀ V h hmn

theorem one_le_k (D : Data G) : 1 ≤ D.k := by
  unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
  split_ifs <;> norm_num

@[expose] noncomputable def mkTilEquiv (V : Subgroup G) (hV : IsElemAbelian 2 V) :
    IntMod V hV ≃* Vtil (⊥ : Subgroup G) V hV :=
  MulEquiv.ofBijective (mkTil (⊥ : Subgroup G) V hV)
    ⟨fun x y h => by
      have h1 : x.val * y.val⁻¹ = 1 :=
        Subgroup.mem_bot.1 ((mkTil_eq_iff (⊥ : Subgroup G) V hV x y).1 h)
      exact IntMod.val_injective (mul_inv_eq_one.1 h1),
     mkTil_surjective (⊥ : Subgroup G) V hV⟩

theorem mkTilEquiv_apply (V : Subgroup G) (hV : IsElemAbelian 2 V) (x : IntMod V hV) :
    mkTilEquiv V hV x = mkTil (⊥ : Subgroup G) V hV x := rfl

theorem actStab_bot_eq_convI (V : Subgroup G) (hV : IsElemAbelian 2 V)
    (g : stabTil (⊥ : Subgroup G) V) :
    actStab (⊥ : Subgroup G) V hV g = convI hV ⟨(g : G), g.2.1⟩ := rfl

theorem actTil_bot_eq_congr (V : Subgroup G) (hV : IsElemAbelian 2 V)
    (g : stabTil (⊥ : Subgroup G) V) :
    actTil (⊥ : Subgroup G) V hV g =
      MulAut.congr (mkTilEquiv V hV) (convI hV ⟨(g : G), g.2.1⟩) := by
  refine MulEquiv.ext fun q => ?_
  obtain ⟨x, rfl⟩ := mkTil_surjective (⊥ : Subgroup G) V hV q
  rw [actTil_mk, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have hsymm : (mkTilEquiv V hV).symm (mkTil (⊥ : Subgroup G) V hV x) = x := by
    rw [← mkTilEquiv_apply V hV x]
    exact (mkTilEquiv V hV).symm_apply_apply x
  rw [hsymm, mkTilEquiv_apply, actStab_bot_eq_convI]

theorem barSub_bot_eq_map_congr (M V : Subgroup G) (hV : IsElemAbelian 2 V)
    (hMn : M = normalizer (V : Set G)) :
    barSub (⊥ : Subgroup G) V hV M =
      (autI hV ⊤).map (MulAut.congr (mkTilEquiv V hV)).toMonoidHom := by
  ext ψ
  rw [mem_barSub, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hgM, rfl⟩
    refine ⟨convI hV ⟨(g : G), g.2.1⟩,
      (mem_autI hV).2 ⟨⟨(g : G), g.2.1⟩, trivial, rfl⟩, ?_⟩
    exact (actTil_bot_eq_congr V hV g).symm
  · rintro ⟨χ, hχ, rfl⟩
    obtain ⟨g, -, rfl⟩ := (mem_autI hV).1 hχ
    have hg0 : (g : G) ∈ normalizer (⊥ : Subgroup G) := by
      rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top _
    let g' : stabTil (⊥ : Subgroup G) V := ⟨(g : G), ⟨g.2, hg0⟩⟩
    have hgM : (g : G) ∈ M := by
      rw [hMn]
      exact g.2
    exact ⟨g', hgM, actTil_bot_eq_congr V hV g'⟩

theorem mBarGT_bot_iff_lt_mParam_autI (D : Data G) {V : Subgroup G} (hV : InCalV D.M V)
    (n : ℕ) : MBarGT D.M ⊥ V n ↔ n < E3.mParam (autI hV.2.2.2 ⊤) := by
  have hV' := hV.2.2.2
  rw [mBarGT_iff_lt_mParam D.M ⊥ V hV' bot_le hV.2.2.1
    (by rw [Subgroup.normalizer_eq_top]; exact le_top) n]
  have hMbar : Mbar D.M ⊥ V hV' =
      (autI hV' ⊤).map (MulAut.congr (mkTilEquiv V hV')).toMonoidHom :=
    barSub_bot_eq_map_congr D.M V hV' (normalizer_eq_of_inCalV D hV).symm
  rw [hMbar, E3.mParam_map_congr (mkTilEquiv V hV') (autI hV' ⊤)]

theorem setting11_of_inCalV1 (D : Data G) {V : Subgroup G} (hV : InCalV1 D.M D.T V) :
    Setting11 D.M V (D.T ⊓ centralizer (V : Set G)) := by
  refine ⟨D.standing.charTwo, D.maxLocal, hV.1.2.2.2, hV.1.2.1, hV.1.2.2.1, hV.1.1, ?_, ?_⟩
  · have hMnorm : D.M ≤ Subgroup.normalizer
        ((D.M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
      A1a.le_normalizer_inf Subgroup.le_normalizer
        (A1a.le_normalizer_centralizer hV.1.2.2.1)
    have hsyl := D.sylowM.inf_of_le_normalizer (N := D.M ⊓ Subgroup.centralizer (V : Set G))
      inf_le_left hMnorm
    have hset : D.T ⊓ (D.M ⊓ Subgroup.centralizer (V : Set G)) =
        D.T ⊓ Subgroup.centralizer (V : Set G) := by
      rw [← inf_assoc, inf_eq_left.2 D.sylowM.le]
    rw [hset] at hsyl
    exact (CFSG.ABGLocalTools.isSylowOf_iff (p := 2)
      (P := D.T ⊓ Subgroup.centralizer (V : Set G))
      (K := D.M ⊓ Subgroup.centralizer (V : Set G))).1 hsyl
  · rw [inf_comm]; exact hV.2

theorem lt_sParam_of_mBarGT (D : Data G) (h111 : W3Thm111 G) {V : Subgroup G}
    (hV : InCalV1 D.M D.T V) (hm : MBarGT D.M ⊥ V 2) {n : ℕ} (hn : MBarGT D.M ⊥ V n) :
    n < E3.sParam hV.1.2.2.2 := by
  have hV' := hV.1.2.2.2
  have hr : (n : ℕ∞) < E3.rParam V := by
    have h := h111 D.M V (D.T ⊓ centralizer (V : Set G)) (setting11_of_inCalV1 D hV) hm n hn
    rwa [rMV_eq_rParam_of_inCalV D hV.1] at h
  have hm' : n < E3.mParam (autI hV' ⊤) := (mBarGT_bot_iff_lt_mParam_autI D hV.1 n).1 hn
  exact E3.lt_sParam_of_lt hV' hr hm'

theorem isSylowIn_of_le (D : Data G) {H : Subgroup G} (hTH : D.T ≤ H) :
    IsSylowIn 2 D.T H := by
  have h := (CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := D.T) (K := ⊤)).1 D.sylowG
  obtain ⟨-, hT2, hndvd⟩ := h
  have hmul := Subgroup.relIndex_mul_relIndex D.T H ⊤ hTH le_top
  refine ⟨hTH, hT2, fun h2 => hndvd (hmul ▸ dvd_mul_of_dvd_left h2 _)⟩

theorem eq_mul_of_le_sup {H S C N E : Subgroup G} (hCH : C ≤ H) (hNH : N ≤ H) (hSN : S ≤ N)
    (hSC : S ≤ normalizer (C : Set G)) (hE : E ≤ C ⊔ S)
    (hprod : (H : Set G) = (E : Set G) * (N : Set G)) :
    (H : Set G) = (C : Set G) * (N : Set G) := by
  rw [hprod]
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨e, he, n, hn, rfl⟩
    have he' : e ∈ (C : Set G) * (S : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left C S hSC]
      exact hE he
    obtain ⟨c, hc, s, hs, rfl⟩ := he'
    exact ⟨c, hc, s * n, N.mul_mem (hSN hs) hn, by group⟩
  · rintro x ⟨c, hc, n, hn, rfl⟩
    have hcH : c ∈ (H : Set G) := hCH hc
    rw [hprod] at hcH
    obtain ⟨e, he, n', hn', rfl⟩ := hcH
    exact ⟨e, he, n' * n, N.mul_mem hn' hn, by group⟩

theorem eq_of_isPGroup_of_ne_bot {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {X : Subgroup G}
    (hX : X ≠ ⊥) (hXp : IsPGroup p X) (hXq : IsPGroup q X) : p = q := by
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hX
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨k, hk⟩ := IsPGroup.exists_orderOf_eq_pow hXp x
  obtain ⟨l, hl⟩ := IsPGroup.exists_orderOf_eq_pow hXq x
  have hord : orderOf x ≠ 1 := fun h => hx (orderOf_eq_one_iff.1 h)
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, pow_zero] at hk; exact absurd hk hord
    · exact hpos
  have hlpos : 0 < l := by
    rcases Nat.eq_zero_or_pos l with h0 | hpos
    · rw [h0, pow_zero] at hl; exact absurd hl hord
    · exact hpos
  have hqdvd : q ∣ p ^ k := by
    rw [← hk, hl]
    exact dvd_pow_self q (Nat.pos_iff_ne_zero.mp hlpos)
  exact ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hqdvd)).symm

theorem wClos_zero_ne_bot (D : Data G) {V : Subgroup G} (hV : InCalV D.M V) :
    E3.wClos V 0 D.T ≠ ⊥ := by
  have hV2 : IsPGroup 2 V := CFSG.Open.IsElemAbelian.isPGroup hV.2.2.2
  have hTM : IsSylowIn 2 D.T D.M := isSylowIn_of_le D D.sylowM.le
  have hnorm : (V.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hV.2.1).2 hV.2.2.1
  have hVT : V ≤ D.T := IsSylowIn.le_of_normal hTM hV.2.1 hnorm hV2
  have hmem : V ∈ E3.gammaSet V 0 D.T := by
    refine ⟨hVT, 1, ?_, ?_⟩
    · exact le_of_eq (conjSubgroup_one V).symm
    · simpa [conjSubgroup_one] using E3.mQuot_self V
  have hle : V ≤ E3.wClos V 0 D.T := E3.le_wClos hmem
  exact fun hbot => hV.1 (le_bot_iff.1 (hbot ▸ hle))

theorem inCalU_of_inP11 (D : Data G) (h63 : UC6.R6_3 D) {X : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hXM : X ≤ D.M) (hXp : IsPGroup p X)
    (hexp : ∀ x ∈ X, x ^ p = 1) (hΓ : rankThreeGamma 1 p X ≤ D.M) :
    ∀ Y : Subgroup G, Y ≤ X → ¬ IsCyclic Y → InCalU D.M Y := by
  intro Y hYX hYnc
  obtain ⟨E, hEY, hE, hEcard⟩ :=
    CFSG.Goldschmidt.G63.exists_isElemAbelian_card_sq hp hp2 (hXp.to_le hYX) hYnc
  have hEM : E ≤ D.M := hEY.trans (hYX.trans hXM)
  have hΓE : rankThreeGamma 1 p E ≤ D.M :=
    (CFSG.HardMathSupport.Solomon.Proving.GLBCore_mono (p := p) (k := 1) hEY).trans
      ((CFSG.HardMathSupport.Solomon.Proving.GLBCore_mono (p := p) (k := 1) hYX).trans hΓ)
  exact InCalU.mono D.maxLocal (h63 p hp hp2 E hEM hE hEcard hΓE) hEY (hYX.trans hXM)

theorem eGen_le_sup_of_lt_sParam {V H S : Subgroup G} (hV : IsElemAbelian 2 V)
    (hS : IsSylowIn 2 S H) {i j : ℕ} (hij : i + j < E3.sParam hV) :
    E1.eGen j H S (E3.gammaSet V i H) ≤
      (H ⊓ centralizer (E3.cClos V (i + j) S : Set G)) ⊔ S := by
  refine iSup₂_le fun A hA => iSup_le fun hAS => iSup₂_le fun K hK => ?_
  have hAΓ : A ∈ E3.gammaSet V i S := ⟨hAS, hA.2⟩
  have hSK : IsSylowIn 2 (S ⊓ K) K := hK.2.2.1
  have hKeq : K = (S ⊓ K) ⊔ twoResidual K := (sup_twoResidual_eq hSK).symm
  have hcomm := E3.e3_19_comm hV hS hij hAΓ hK
  have h1 : S ⊓ K ≤ S := inf_le_left
  have h2 : twoResidual K ≤ H ⊓ centralizer (E3.cClos V (i + j) S : Set G) :=
    le_inf ((twoResidual_le K).trans hK.1)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm)
  rw [hKeq]
  exact sup_le (h1.trans le_sup_right) (h2.trans le_sup_left)

end TwelveShort

open TwelveShort

theorem twelve_nine (D : Data G) (h127 : R127 D) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) :
    ¬ CFSG.CGT.Timmesfeld75.IsTI V ∧
      (8 ≤ Nat.card V₀ → ¬ InCalV1 D.M D.T V₀ ∧ ∀ X : Subgroup G, ¬ F11.InP11 D X) := by
  rcases h.1 with ⟨hW, h0⟩ | ⟨h0, hcu, -⟩
  · refine ⟨?_, ?_⟩
    · intro hTI
      exact (h127 h.2 V hW.1.1.1 hTI hW.1.2.1).1 hW.1.1
    · intro h8
      rw [h0, Subgroup.card_bot] at h8
      omega
  · refine ⟨h0.2.2.2.2.1, ?_⟩
    intro h8
    have h127' := h127 h.2 V₀ h0.1 h0.2.2.2.1 h8
    exact ⟨h127'.1, h127'.2 fun z hz hzc hz1 => (hcu z hz hzc hz1).1⟩

theorem Hyp125.hyp11 {D : Data G} (h127 : R127 D) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) :
    F11.Hyp11 D V₀ V := by
  refine ⟨?_, twelve_nine D h127 h⟩
  rcases h.1 with ⟨hW, h0⟩ | ⟨h0, -, -⟩
  · exact Or.inr ⟨h0, hW.1⟩
  · exact Or.inl h0

theorem twelve_twelve (D : Data G) (h63 : UC6.R6_3 D) (h126 : R126 D) (h1211 : R1211_1 D)
    (h111 : W3Thm111 G) (h6161ii : W3Lem616_1ii G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hm : MBarGT D.M V₀ V (D.k + 1)) : ∀ X : Subgroup G, ¬ InPStar D V₀ X := by
  intro X hX
  by_cases hV0 : V₀ = ⊥
  · subst hV0
    rcases h.1 with ⟨hW, -⟩ | ⟨h0, -, -⟩
    · have hV1 : InCalV1 D.M D.T V := hW.1.1
      have hVV : InCalV D.M V := hV1.1
      have hV' : IsElemAbelian 2 V := hVV.2.2.2
      have hm2 : MBarGT D.M ⊥ V 2 := mBarGT_mono hm (by have := one_le_k D; omega)
      have hgt : D.k + 1 < E3.sParam hV' := lt_sParam_of_mBarGT D h111 hV1 hm2 hm
      obtain ⟨H₀, hmin⟩ := h.exists_hyp124Min
      have hS : IsSylowIn 2 D.T H₀ := isSylowIn_of_le D hmin.1.1
      have hE : E1.InE D.k H₀ := h126 H₀ hmin
      have hW0 : E3.wClos V 0 D.T ≠ ⊥ := wClos_zero_ne_bot D hVV
      obtain ⟨p, hp, hp2, hXM, hXp, hexp, hnc, hperm, hΓ, -⟩ := hX.1
      have hUY := inCalU_of_inP11 D h63 hp hp2 hXM hXp hexp hΓ
      obtain ⟨p', hp', hXp', hcase⟩ := hX.2 rfl
      have hXne : X ≠ ⊥ := fun hbot => hnc (hbot ▸ isCyclic_of_subsingleton)
      have hpp : p = p' := eq_of_isPGroup_of_ne_bot hp hp' hXne hXp hXp'
      rcases hcase with hbig | hcase2 | hirr
      · exact hmin.1.2.1 (six_sixteen_one_i_uncond hV' D.maxLocal hS (one_le_k D) hE hW0 hgt
          hp hp2 hXM hexp (hpp.symm ▸ hbig) hperm hUY)
      · exact hmin.1.2.1 (h6161ii hV' D.maxLocal (Hyp125.normalizer_eq h) hmin.1.2.2 hS
          (one_le_k D) hE hW0 hgt hp hp2 hXM hexp hnc hperm hUY hcase2)
      · exact hmin.1.2.1 (six_sixteen_one_iii_uncond hV' D.maxLocal hS (one_le_k D) hE hW0 hgt
          hp hp2 hXp hXM hnc hirr hperm hUY)
    · exact absurd rfl h0.1.1
  · exact (h1211 V₀ V h ⟨X, hX.1⟩ hV0) hm

theorem twelve_twentyOne_one (D : Data G) (h111 : W3Thm111 G) {V : Subgroup G}
    (hV : InCalV1 D.M D.T V) (hm : MBarGT D.M ⊥ V 2) {H S : Subgroup G}
    (hF : CFSG.QuasithinUnique.CharTwo H) (hS : IsSylowIn 2 S H) {i : ℕ}
    (hi : MBarGT D.M ⊥ V
      (i + E3.aParam (autI (omegaOneCenter_conjClosure_isElemAbelian hF hS) H))) :
    ⁅E3.wClos V i S, CFSG.Quasithin.conjClosure (omegaOneCenterOf S) H⁆ = ⊥ ∧
      (H : Set G) = ((H ⊓ centralizer (omegaOneCenterOf S : Set G) : Subgroup G) : Set G) *
        ((H ⊓ normalizer (E3.wClos V i S : Set G) : Subgroup G) : Set G) := by
  have hV' := hV.1.2.2.2
  have hlt : i + E3.aParam (autI (omegaOneCenter_conjClosure_isElemAbelian hF hS) H) <
      E3.sParam hV' := lt_sParam_of_mBarGT D h111 hV hm hi
  exact six_eleven_one hV' hF hS (Nat.lt_sub_iff_add_lt.2 hlt)

theorem twelve_twentyOne_two (D : Data G) (h111 : W3Thm111 G) (h45 : W3Lem45_2 G)
    {V : Subgroup G}
    (hV : InCalV1 D.M D.T V) (hm : MBarGT D.M ⊥ V 2) {H S : Subgroup G}
    (hS : IsSylowIn 2 S H) {i j : ℕ}
    (hFj : CompFactorAutInF j H S) (hn : MBarGT D.M ⊥ V (j + i))
    (hj1 : 1 ≤ j := by omega) :
    (H : Set G) = ((H ⊓ centralizer (E3.cClos V (j + i) S : Set G) : Subgroup G) : Set G) *
      ((H ⊓ normalizer (E3.wClos V i S : Set G) : Subgroup G) : Set G) := by
  have hV' := hV.1.2.2.2
  have hlt : j + i < E3.sParam hV' := lt_sParam_of_mBarGT D h111 hV hm hn
  have hltij : i + j < E3.sParam hV' := by rw [Nat.add_comm j i] at hlt; exact hlt
  have h45' := h45 H S j (E3.gammaSet V i H) hj1 hS (E3.isInvColl_gammaSet hV' i H) hFj
  rw [E3.weakClosure_gammaSet hS.le] at h45'
  have h45'' : (H : Set G) =
      (E1.eGen j H S (E3.gammaSet V i H) : Set G) *
        ((H ⊓ normalizer (E3.wClos V i S : Set G) : Subgroup G) : Set G) := h45'
  have hSN : S ≤ H ⊓ normalizer (E3.wClos V i S : Set G) :=
    fun s hs => ⟨hS.le hs,
      (Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos S)) hs⟩
  have hSC : S ≤ normalizer
      ((H ⊓ centralizer (E3.cClos V (i + j) S : Set G) : Subgroup G) : Set G) :=
    A1a.le_normalizer_inf (hS.le.trans Subgroup.le_normalizer)
      (A1a.le_normalizer_centralizer
        (Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_cClos (V := V) (i := i + j) S)))
  have hmain := eq_mul_of_le_sup (H := H) (S := S)
    (C := H ⊓ centralizer (E3.cClos V (i + j) S : Set G))
    (N := H ⊓ normalizer (E3.wClos V i S : Set G))
    (E := E1.eGen j H S (E3.gammaSet V i H))
    inf_le_left inf_le_left hSN hSC (eGen_le_sup_of_lt_sParam hV' hS hltij) h45''
  rw [Nat.add_comm j i]
  exact hmain

theorem twelve_twentyOne_three (D : Data G) (h111 : W3Thm111 G) {V : Subgroup G}
    (hV : InCalV1 D.M D.T V) (hm : MBarGT D.M ⊥ V 2) {H S : Subgroup G} (hS : IsSylowIn 2 S H)
    {i j : ℕ} (hE : E1.InE j H) (hn : MBarGT D.M ⊥ V (i + j)) :
    (H ⊓ centralizer (E3.cClos V (i + j) S : Set G)) ⊔
      (H ⊓ normalizer (E3.wClos V i S : Set G)) = H := by
  exact six_eleven_three hV.1.2.2.2 hS hE (lt_sParam_of_mBarGT D h111 hV hm hn)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
