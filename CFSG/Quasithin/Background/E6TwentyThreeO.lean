module

public import CFSG.Quasithin.Background.E6TwentyThreeN
public import CFSG.Quasithin.Background.E6EighteenC

public section

namespace CFSG.Quasithin.E6

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

section Reduction

variable {G : Type} [Group G] [Finite G] {T M V : Subgroup G}

theorem le_centralizer_of_isPGroup_of_mQuot_lt (hV : IsElemAbelian 2 V) (h : HypE61 T M V)
    {W S : Subgroup G} (hWV : W ≤ V) (hW1 : W ≠ ⊥)
    (hlt : E3.mQuot V W < E3.mParam (autI hV M)) (hS : IsPGroup 2 S)
    (hSH : S ≤ M ⊓ Subgroup.centralizer (W : Set G)) : S ≤ Subgroup.centralizer (V : Set G) := by
  have hHN : M ⊓ Subgroup.centralizer (W : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    inf_centralizer_le_normalizer h hWV hW1
  by_contra hSC
  have hSN : S ≤ Subgroup.normalizer (V : Set G) := hSH.trans hHN
  have hA1 : autI hV S ≠ ⊥ := (autI_eq_bot_iff hV hSN).not.2 hSC
  have hle := E3.mParam_le_rkIdx_fixV (autI_mono hV (hSH.trans inf_le_left))
    (B6.isPGroup_autOn hS V) hA1
  rw [E3.rkIdx_fixV_autI hV hSN] at hle
  have hWS : W ≤ V ⊓ Subgroup.centralizer (S : Set G) := by
    intro u hu
    refine ⟨hWV hu, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (hSH hs).2 u hu).symm
  have := E3.mQuot_mono (V := V) hWS
  omega

theorem exists_isSylowIn_le_centralizer_of_mQuot_lt (hV : IsElemAbelian 2 V)
    (h : HypE61 T M V) {W N : Subgroup G} (hWV : W ≤ V) (hW1 : W ≠ ⊥)
    (hlt : E3.mQuot V W < E3.mParam (autI hV M)) (hNW : N ≤ Subgroup.centralizer (W : Set G))
    (hNn : (N.subgroupOf (Subgroup.centralizer (W : Set G))).Normal) :
    ∃ S : Subgroup G, IsSylowIn 2 S N ∧ V ≤ Subgroup.centralizer (S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hCM : Subgroup.centralizer (W : Set G) ≤ M
  · obtain ⟨S, hS⟩ := E1.exists_isSylowIn_two N
    refine ⟨S, hS, Subgroup.le_centralizer_iff.1 ?_⟩
    exact le_centralizer_of_isPGroup_of_mQuot_lt hV h hWV hW1 hlt hS.isPGroup
      (le_inf (hS.le.trans (hNW.trans hCM)) (hS.le.trans hNW))
  · have hQ := e6_5_one h (mem_gammaE64_of_mQuot_lt hV h hWV hW1 hCM hlt)
    refine ⟨_, hQ.inf_normal hNW hNn, fun v hv => ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (Subgroup.mem_centralizer_iff.1 hq.1.2 v hv).symm

end Reduction

@[expose] def E623A6Insp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y E X : Subgroup G) (a z : G),
    CFSG.IsQuasisimple ↥Y → Lemma115Cases Y z → IsElemAbelian 2 E →
    E ≤ Subgroup.normalizer (Y : Set G) → a ∈ E → ¬ Y ≤ Subgroup.centralizer ({a} : Set G) →
    IsComponentIn X (Y ⊓ Subgroup.centralizer ({a} : Set G)) →
    Nonempty (↥X ≃* alternatingGroup (Fin 6)) →
    (∀ b ∈ E, ¬ Y ≤ Subgroup.centralizer ({b} : Set G) →
      ∃ S : Subgroup G, IsSylowIn 2 S (Y ⊓ Subgroup.centralizer ({b} : Set G)) ∧
        E ≤ Subgroup.centralizer (S : Set G)) →
    ((∃ S : Subgroup G, IsSylowIn 2 S Y ∧ E ≤ Subgroup.centralizer (S : Set G)) ∨
      (E ⊓ Subgroup.centralizer (Y : Set G)).relIndex E = 8) →
    False

theorem e623A6Over_of (h311 : Theorem311Stmt) (hlist : Lemma115_3_List)
    (hInsp : E623A6Insp) : E623A6Over := by
  intro G _ _ T M V U L U₀ X Y g hV h hm hr1 hUV hU1 hUM hH hLb hL3 hLM hZ hU₀U hU₀q hX hXA6 hLX
    hg hgX hYc hYn hXY hYU₀
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm h.isElemAbelian ha hb
  have h15 : HypE615 hV M := Or.inr hm
  have h6 : 6 ≤ E3.mQuot V ⊥ := (e6_17 h311 hV h h15 hr1).2
  have hgN : g ∈ Subgroup.normalizer (V : Set G) := hg.2
  have hU₀V : U₀ ≤ V := hU₀U.le.trans hUV
  have hU₀2 : E3.mQuot V U₀ = 2 := by
    have hadd := E3.mQuot_add hU₀U.le hUV
    have hne : E3.mQuot U U₀ ≠ 0 := fun h0 =>
      hU₀U.ne ((E3.mQuot_eq_zero_iff (hV2.to_le hUV) hU₀U.le).1 h0)
    omega
  set U₁ := U₀ ⊓ CFSG.conjugate U g with hU₁def
  have hU₁U₀ : U₁ ≤ U₀ := inf_le_left
  have hU₁V : U₁ ≤ V := hU₁U₀.trans hU₀V
  have hq1 : E3.mQuot V U₁ ≤ 3 := by
    have h1 := mQuot_inf_le (U := U₀) (U' := CFSG.conjugate U g) hV2
    rw [← hU₁def, mQuot_conjugate hgN] at h1
    omega
  have hU₁1 : U₁ ≠ ⊥ := by
    intro h0
    rw [h0] at hq1
    omega
  have hU₁c : U₁ ≤ Subgroup.centralizer (U₁ : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.2 fun w hw => hVc _ (hU₁V hw) _ (hU₁V hu)
  have hYH₁ : Y ≤ Subgroup.centralizer (U₁ : Set G) := hYc.1
  have hH₁N : Subgroup.centralizer (U₁ : Set G) ≤ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYc.1).1 hYn
  have hVN : V ≤ Subgroup.normalizer (Y : Set G) := fun v hv =>
    hH₁N (Subgroup.mem_centralizer_iff.2 fun u hu => hVc _ (hU₁V hu) _ hv)
  obtain ⟨W₀, hW₀def⟩ : ∃ W₀ : Subgroup G, W₀ = V ⊓ Subgroup.centralizer (Y : Set G) :=
    ⟨_, rfl⟩
  have hW₀V : W₀ ≤ V := by rw [hW₀def]; exact inf_le_left
  have hW₀Y : W₀ ≤ Subgroup.centralizer (Y : Set G) := by rw [hW₀def]; exact inf_le_right
  have hU₁W₀ : U₁ ≤ W₀ := by
    rw [hW₀def]
    exact le_inf hU₁V (Subgroup.le_centralizer_iff.1 hYH₁)
  have hqW₀ : E3.mQuot V W₀ ≤ 3 := (E3.mQuot_mono hU₁W₀).trans hq1
  obtain ⟨a, haU₀, haY⟩ : ∃ a ∈ U₀, a ∉ Subgroup.centralizer (Y : Set G) := by
    by_contra hall
    push Not at hall
    exact hYU₀ hall
  have haV : a ∈ V := hU₀V haU₀
  have haY' : ¬ Y ≤ Subgroup.centralizer ({a} : Set G) := fun hle =>
    haY (Subgroup.mem_centralizer_iff.2 fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.1 (hle hy))
  have haU₁ : a ∉ U₁ := fun h1 => haY (Subgroup.le_centralizer_iff.1 hYH₁ h1)
  have hU₀le : U₀ ≤ U₁ ⊔ Subgroup.zpowers a := by
    have hA : U₁ ⊔ Subgroup.zpowers a ≤ U₀ := sup_le hU₁U₀ (Subgroup.zpowers_le.2 haU₀)
    have hlt : U₁ < U₁ ⊔ Subgroup.zpowers a := lt_of_le_of_ne le_sup_left fun heq =>
      haU₁ (by rw [heq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
    have hadd1 := E3.mQuot_add hU₁U₀ hU₀V
    have hadd2 := E3.mQuot_add hlt.le hA
    have hne : E3.mQuot (U₁ ⊔ Subgroup.zpowers a) U₁ ≠ 0 := fun h0 =>
      hlt.ne ((E3.mQuot_eq_zero_iff (hV2.to_le (hA.trans hU₀V)) hlt.le).1 h0)
    have h0 : E3.mQuot U₀ (U₁ ⊔ Subgroup.zpowers a) = 0 := by omega
    exact ((E3.mQuot_eq_zero_iff (hV2.to_le hU₀V) hA).1 h0).ge
  have hCYa : Y ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.centralizer (U₀ : Set G) := by
    intro y hy
    have hle : U₁ ⊔ Subgroup.zpowers a ≤ Subgroup.centralizer ({y} : Set G) := sup_le
      (fun u hu => Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 (hYH₁ hy.1) u hu))
      (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_singleton_iff.1 hy.2).symm))
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle (hU₀le hu))
  have hXYa : X ≤ Y ⊓ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    ⟨hXY.le hx, Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 (hX.1 hx) a haU₀).symm⟩
  have hXc : IsComponentIn X (Y ⊓ Subgroup.centralizer ({a} : Set G)) :=
    BenderBranch.isComponentIn_of_le hX hXYa hCYa
  have := h.simple
  have hq : QTKECore G := qtkeCore_of_cat h.nonabelian h.qtke
  obtain ⟨z, hz⟩ := exists_lemma115Cases_centralizer hlist h.simple h.nonabelian hq
    (hV2.to_le hU₁V) hU₁1 hU₁c hYc
  have hstar : ∀ b ∈ V, ¬ Y ≤ Subgroup.centralizer ({b} : Set G) →
      ∃ S : Subgroup G, IsSylowIn 2 S (Y ⊓ Subgroup.centralizer ({b} : Set G)) ∧
        V ≤ Subgroup.centralizer (S : Set G) := by
    intro b hbV hbY
    obtain ⟨W, hWdef⟩ : ∃ W : Subgroup G, W = W₀ ⊔ Subgroup.zpowers b := ⟨_, rfl⟩
    have hWV : W ≤ V := by rw [hWdef]; exact sup_le hW₀V (Subgroup.zpowers_le.2 hbV)
    have hbW : b ∈ W := by rw [hWdef]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
    have hbW₀ : b ∉ W₀ := fun hb => hbY fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hW₀Y hb) y hy)
    have hW₀W : W₀ < W := lt_of_le_of_ne (by rw [hWdef]; exact le_sup_left) fun heq =>
      hbW₀ (heq ▸ hbW)
    have hW1 : W ≠ ⊥ := fun h0 => hU₁1 (le_bot_iff.1 (by rw [← h0]; exact hU₁W₀.trans hW₀W.le))
    have hqW : E3.mQuot V W < E3.mParam (autI hV M) := by
      have hadd := E3.mQuot_add hW₀W.le hWV
      have hne : E3.mQuot W W₀ ≠ 0 := fun h0 =>
        hW₀W.ne ((E3.mQuot_eq_zero_iff (hV2.to_le hWV) hW₀W.le).1 h0)
      omega
    have hYW : Y ⊓ Subgroup.centralizer ({b} : Set G) = Y ⊓ Subgroup.centralizer (W : Set G) := by
      refine le_antisymm (fun y hy => ⟨hy.1, ?_⟩) (inf_le_inf_left _
        (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hbW)))
      have hle : W ≤ Subgroup.centralizer ({y} : Set G) := by
        rw [hWdef]
        exact sup_le (fun w hw => Subgroup.mem_centralizer_singleton_iff.2
            (Subgroup.mem_centralizer_iff.1 (hW₀Y hw) y hy.1).symm)
          (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2
            (Subgroup.mem_centralizer_singleton_iff.1 hy.2).symm))
      exact Subgroup.mem_centralizer_iff.2 fun w hw =>
        Subgroup.mem_centralizer_singleton_iff.1 (hle hw)
    have hNW : Y ⊓ Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer (W : Set G) :=
      inf_le_right
    have hNn : ((Y ⊓ Subgroup.centralizer (W : Set G)).subgroupOf
        (Subgroup.centralizer (W : Set G))).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNW]
      exact B2F.le_normalizer_inf
        ((Subgroup.centralizer_le (hU₁W₀.trans hW₀W.le)).trans hH₁N) Subgroup.le_normalizer
    obtain ⟨S, hS, hSV⟩ := exists_isSylowIn_le_centralizer_of_mQuot_lt hV h hWV hW1 hqW hNW hNn
    exact ⟨S, by rw [hYW]; exact hS, hSV⟩
  have h8 : (∃ S : Subgroup G, IsSylowIn 2 S Y ∧ V ≤ Subgroup.centralizer (S : Set G)) ∨
      (V ⊓ Subgroup.centralizer (Y : Set G)).relIndex V = 8 := by
    rw [← hW₀def]
    by_cases hlt : E3.mQuot V W₀ < E3.mParam (autI hV M)
    · left
      have hW₀1 : W₀ ≠ ⊥ := fun h0 => hU₁1 (le_bot_iff.1 (by rw [← h0]; exact hU₁W₀))
      have hYW₀ : Y ≤ Subgroup.centralizer (W₀ : Set G) := Subgroup.le_centralizer_iff.1 hW₀Y
      have hYn₀ : (Y.subgroupOf (Subgroup.centralizer (W₀ : Set G))).Normal := by
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer hYW₀]
        exact (Subgroup.centralizer_le hU₁W₀).trans hH₁N
      exact exists_isSylowIn_le_centralizer_of_mQuot_lt hV h hW₀V hW₀1 hlt hYW₀ hYn₀
    · right
      push Not at hlt
      have h3 : E3.mQuot V W₀ = 3 := by omega
      rw [E3.relIndex_eq_two_pow hV2, h3]
      norm_num
  exact hInsp G Y V X a z (BenderBranch.isQuasisimple_of_isComponentIn hYc) hz hV hVN haV haY'
    hXc hXA6 hstar h8

end CFSG.Quasithin.E6
