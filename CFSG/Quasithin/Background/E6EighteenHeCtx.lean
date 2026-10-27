module

public import CFSG.Quasithin.Background.E6EighteenHeE68
public import CFSG.Quasithin.Background.E6EighteenC
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

@[expose] def E618HeResidual : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U L : Subgroup G) (hV : IsElemAbelian 2 V),
    HypE61 T M V → HypE615 hV M → U ∈ gammaE64 V M → E3.mQuot V U ≤ 2 →
    IsComponentIn L (Subgroup.centralizer (U : Set G)) → IsA7Type L →
    ∀ U' : Subgroup G, U' = V ⊓ Subgroup.centralizer (L : Set G) → E3.mQuot V U' = 2 →
    E3.mParam (autI hV M) = 3 →
    ∀ A K : Subgroup G, A ≤ U' → A ≠ ⊥ → IsComponentIn K (Subgroup.centralizer (A : Set G)) →
      U' ≤ Subgroup.normalizer (K : Set G) →
      IsComponentIn L (K ⊓ Subgroup.centralizer (U' : Set G)) → IsHeQuot K →
      U' ≤ Subgroup.centralizer (K : Set G)

theorem le_centralizer_of_heAt (hlist : Lemma115_3_List) (hI31 : AS_I_3_1_three)
    (hfam : NoA7FixL115NotHe) {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hq : QTKECore G) {P L : Subgroup G} (hP : IsPGroup 2 P)
    (hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hL7 : IsA7Type L)
    (hHe : ∀ A K : Subgroup G, A ≤ P → A ≠ ⊥ →
      IsComponentIn K (Subgroup.centralizer (A : Set G)) → P ≤ Subgroup.normalizer (K : Set G) →
      IsComponentIn L (K ⊓ Subgroup.centralizer (P : Set G)) → IsHeQuot K →
      P ≤ Subgroup.centralizer (K : Set G))
    {A K : Subgroup G} (hAP : A ≤ P) (hA1 : A ≠ ⊥)
    (hK : IsComponentIn K (Subgroup.centralizer (A : Set G)))
    (hPN : P ≤ Subgroup.normalizer (K : Set G))
    (hL : IsComponentIn L (K ⊓ Subgroup.centralizer (P : Set G))) :
    P ≤ Subgroup.centralizer (K : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  suffices key : ∀ n : ℕ, ∀ A K : Subgroup G, Nat.card K = n → A ≤ P → A ≠ ⊥ →
      IsComponentIn K (Subgroup.centralizer (A : Set G)) → P ≤ Subgroup.normalizer (K : Set G) →
      IsComponentIn L (K ⊓ Subgroup.centralizer (P : Set G)) →
      P ≤ Subgroup.centralizer (K : Set G) from
    key _ A K rfl hAP hA1 hK hPN hL
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A K hn hAP hA1 hK hPN hL
    by_cases hHeK : IsHeQuot K
    · exact hHe A K hAP hA1 hK hPN hL hHeK
    by_contra hPK
    set H := Subgroup.centralizer (A : Set G) with hHdef
    have hA2 : IsPGroup 2 A := hP.to_le hAP
    have hAc : A ≤ Subgroup.centralizer (A : Set G) := fun w hw =>
      Subgroup.mem_centralizer_iff.2 fun w' hw' => hPab _ (hAP hw') _ (hAP hw)
    have hpc : pCoreOf 2 H ≠ ⊥ := by
      intro h0
      apply hA1
      exact le_bot_iff.1 (h0 ▸ C1.le_pCoreOf_of_normalized hAc
        (Subgroup.centralizer_le_normalizer _) hA2)
    have hH : CFSG.SectionRank.IsSQTKCat ↥H := hq.1 H hpc
    have hPH : P ≤ H := fun x hx =>
      Subgroup.mem_centralizer_iff.2 fun a ha => hPab _ (hAP ha) _ hx
    have hKq : CFSG.IsQuasisimple ↥K := BenderBranch.isQuasisimple_of_isComponentIn hK
    obtain ⟨t, htP, ht2, ht1, K₀, hLK₀, hK₀c, hPN₀, -, hLK₀c⟩ :=
      exists_step_of_not_le hI31 hH hK hPH hP hPN hL hL7 hPK
    set A' := A ⊔ Subgroup.zpowers (t : G) with hA'def
    have hA'P : A' ≤ P := sup_le hAP (Subgroup.zpowers_le.2 htP)
    have hA'1 : A' ≠ ⊥ := fun h0 => hA1 (le_bot_iff.1 (h0 ▸ le_sup_left))
    have hCA' := centralizer_sup_zpowers A (t : G)
    have hKsub : IsSubnormal (K ⊓ Subgroup.centralizer ({(t : G)} : Set G))
        (Subgroup.centralizer (A' : Set G)) := by
      have h1 := A3.subnormal_inf_right (subnormal_of_mem_cComp
        (Id2519.mem_cComp_of_isComponentIn hK))
        (show Subgroup.centralizer (A' : Set G) ≤ H from
          Subgroup.centralizer_le (le_sup_left : A ≤ A'))
      have heq : K ⊓ Subgroup.centralizer (A' : Set G) =
          K ⊓ Subgroup.centralizer ({(t : G)} : Set G) := by
        rw [hCA', ← inf_assoc, inf_eq_left.2 hK.1]
      rwa [heq] at h1
    have hK₀q := BenderBranch.isQuasisimple_of_isComponentIn hK₀c
    have hK₀A' : IsComponentIn K₀ (Subgroup.centralizer (A' : Set G)) :=
      Id2519.isComponentIn_of_mem_cComp
        (cComp_mem_of_subnormal hKsub (Id2519.mem_cComp_of_isComponentIn hK₀c)) hK₀q
    have hlt : Nat.card K₀ < n := by
      rw [← hn]
      have hK₀le : K₀ ≤ K := hK₀c.1.trans inf_le_left
      refine Subgroup.card_lt_of_lt (lt_of_le_of_ne hK₀le fun heq => ht1 ?_)
      rw [Bar.barHom_eq_one_iff hKq.1]
      intro x
      have hx : (x : G) ∈ Subgroup.centralizer ({(t : G)} : Set G) :=
        (hK₀c.1.trans inf_le_right) (heq ▸ x.2)
      exact (Subgroup.mem_centralizer_singleton_iff.1 hx).symm
    have hPK₀ := ih _ hlt A' K₀ rfl hA'P hA'1 hK₀A' hPN₀ hLK₀c
    have hLeq := eq_of_le_centralizer htP hK₀c hL hLK₀ hPK₀
    rw [← hLeq] at hK₀c
    obtain ⟨z, hz⟩ := exists_lemma115Cases_centralizer hlist hs hnab hq hA2 hA1 hAc hK
    exact hfam G K z hKq hz hHeK _ ht2 ht1 (hasA7Component_fix_barHom t hK₀c hL7)

theorem le_centralizer_of_isHeQuot_ctx
    (h68 : E68Stmt) (hRes : E618HeResidual) {G : Type} [Group G] [Finite G]
    {T M V U L : Subgroup G} (hV : IsElemAbelian 2 V) (h : HypE61 T M V) (h15 : HypE615 hV M)
    (hU : U ∈ gammaE64 V M) (hU2 : E3.mQuot V U ≤ 2)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) (hLA7 : IsA7Type L)
    (hm : 2 < E3.mParam (autI hV M))
    (hq2 : E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) ≤ 2) (hLM : ¬ L ≤ M)
    {A K : Subgroup G} (hAU' : A ≤ V ⊓ Subgroup.centralizer (L : Set G)) (hA1 : A ≠ ⊥)
    (hK : IsComponentIn K (Subgroup.centralizer (A : Set G)))
    (hU'N : V ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hLK' : IsComponentIn L (K ⊓ Subgroup.centralizer
      ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G)))
    (hHeK : IsHeQuot K) :
    V ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.centralizer (K : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U' := V ⊓ Subgroup.centralizer (L : Set G) with hU'def
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  have hU'V : U' ≤ V := inf_le_left
  have hKq := BenderBranch.isQuasisimple_of_isComponentIn hK
  have hLq := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hLK : L ≤ K := hLK'.1.trans inf_le_left
  have hLU' : L ≤ Subgroup.centralizer (U' : Set G) := hLK'.1.trans inf_le_right
  have hP2 : ∀ u ∈ U', u * u = 1 := fun u hu => by
    rw [← pow_two]
    exact hV.2 u (hU'V hu)
  have hidx := relIndex_inf_centralizer_le_two_of_isHeQuot hKq hHeK hU'N hP2 hLK hLU' hLq hLA7
  set W := U' ⊓ Subgroup.centralizer (K : Set G) with hWdef
  have hWU' : W ≤ U' := inf_le_left
  have hWV : W ≤ V := hWU'.trans hU'V
  have hAW : A ≤ W := le_inf hAU' (Subgroup.le_centralizer_iff.1 hK.1)
  have hW1 : W ≠ ⊥ := fun h0 => hA1 (le_bot_iff.1 (h0 ▸ hAW))
  have hWq : E3.mQuot U' W ≤ 1 := by
    rw [E3.relIndex_eq_two_pow (hV2.to_le hU'V) W] at hidx
    by_contra hlt
    push Not at hlt
    have : 2 ^ 2 ≤ 2 ^ E3.mQuot U' W := Nat.pow_le_pow_right (by norm_num) hlt
    omega
  have hadd := E3.mQuot_add hWU' hU'V
  have hKW : IsComponentIn K (Subgroup.centralizer (W : Set G)) :=
    BenderBranch.isComponentIn_of_le hK (Subgroup.le_centralizer_iff.1 inf_le_right)
      (Subgroup.centralizer_le hAW)
  have hWM : ¬ Subgroup.centralizer (W : Set G) ≤ M := fun hle =>
    hLM (hLK.trans (hKW.1.trans hle))
  by_cases hlt : E3.mQuot V W < E3.mParam (autI hV M)
  ·
    exfalso
    have hWΓ := mem_gammaE64_of_mQuot_lt hV h hWV hW1 hWM hlt
    refine not_e68Cases_of_isHeQuot hV hKq hHeK ?_ (h68 G T M V W K hV h hWΓ hKW).2
    have := E3.mQuot_mono (V := V) (le_inf hWV inf_le_right :
      W ≤ V ⊓ Subgroup.centralizer (K : Set G))
    omega
  ·
    push Not at hlt
    exact hRes G T M V U L hV h h15 hU hU2 hL hLA7 U' rfl (by omega) (by omega) A K hAU' hA1 hK
      hU'N hLK' hHeK

theorem e618Stmt_of_heCtx
    (h311 : Theorem311Stmt) (hlist : Lemma115_3_List) (hI31 : AS_I_3_1_three)
    (hA7 : E618A7Facts) (hfam : NoA7FixL115NotHe) (h68 : E68Stmt) (hRes : E618HeResidual) :
    E618Stmt := by
  intro G _ _ T M V U L hV h h15 hU hU2 hL hLA7
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := h.simple
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  have hUV : U ≤ V := hU.1
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm h.isElemAbelian ha hb
  set H := Subgroup.centralizer (U : Set G) with hHdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hLq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hLM : ¬ L ≤ M := fun hLM => DoubleA3.not_isComponentIn_of_charTwo (e6_6_one h hUV) L
    (BenderBranch.isComponentIn_of_le hL (le_inf hLM hL.1) inf_le_right)
  have hQH : IsSylowTwoOf Q H := e6_5_one h hU
  have hVQ : V ≤ Q := h.le_inf_centralizer
  have hVN : V ≤ Subgroup.normalizer (L : Set G) := fun v hv =>
    mem_normalizer_of_mem_center_sylow hQH hL (hVQ hv)
      (Subgroup.mem_centralizer_iff.2 fun q hq => (Subgroup.mem_centralizer_iff.1 hq.2 v hv).symm)
  set U' := V ⊓ Subgroup.centralizer (L : Set G) with hU'def
  have hU'V : U' ≤ V := inf_le_left
  have hUU' : U ≤ U' := le_inf hUV fun u hu =>
    Subgroup.mem_centralizer_iff.2 fun l hl => (Subgroup.mem_centralizer_iff.1 (hL.1 hl) u hu).symm
  have hU'1 : U' ≠ ⊥ := fun h0 => hU.2.1 (le_bot_iff.1 (h0 ▸ hUU'))
  have hLU' : L ≤ Subgroup.centralizer (U' : Set G) := fun l hl =>
    Subgroup.mem_centralizer_iff.2 fun u hu => (Subgroup.mem_centralizer_iff.1 hu.2 l hl).symm
  have hLc' : IsComponentIn L (Subgroup.centralizer (U' : Set G)) :=
    BenderBranch.isComponentIn_of_le hL hLU' (Subgroup.centralizer_le hUU')
  have hU'M : ¬ Subgroup.centralizer (U' : Set G) ≤ M := fun hle => hLM (hLU'.trans hle)
  set R := Q ⊓ Subgroup.normalizer (L : Set G) with hRdef
  have hSL : IsSylowTwoOf (Q ⊓ L) L := isSylowTwoOf_inf_of_subnormal' hQH hL.1 hL.2.2
  have hRL : R ⊓ L = Q ⊓ L := by
    rw [hRdef, inf_assoc, inf_eq_right.2 (Subgroup.le_normalizer : L ≤ _)]
  have hbase : E68BaseHyp L V R :=
    { quasisimple := hLq
      elemAbelian := hV
      isPGroup := h.isPGroup_Q.to_le inf_le_left
      le := le_inf hVQ hVN
      centralizer := inf_le_left.trans inf_le_right
      normalizer := inf_le_right
      sylow := by rw [hRL]; exact hSL }
  obtain ⟨⟨E, hEL, hE3, hE9⟩, hidx4, hgen⟩ := hA7 G L V R hLA7 hbase
  have hq2 : E3.mQuot V U' ≤ 2 := by
    have h1 : 2 ^ E3.mQuot V U' ≤ 2 ^ 2 := by
      rw [← E3.relIndex_eq_two_pow hV2]
      exact hidx4
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have hr : E3.rParam V = 1 := by
    refine le_antisymm ?_ (one_le_rParam h)
    obtain ⟨A, hAV, hA1, hAC⟩ : ∃ A : Subgroup G, A ≤ V ∧ E3.mQuot V A ≤ 1 ∧
        ¬ Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (V : Set G) := by
      rcases Nat.lt_or_ge (E3.mQuot V U') 2 with hlt | hge
      · exact ⟨U', hU'V, by omega, fun hle => hU'M (hle.trans h.normalizer_le)⟩
      · have h4 : U'.relIndex V = 4 := by
          rw [E3.relIndex_eq_two_pow hV2, show E3.mQuot V U' = 2 by omega]
          norm_num
        have hLsup := hgen h4
        by_contra hall
        push Not at hall
        apply hLM
        refine hLsup.trans (iSup₂_le fun a ha => ?_)
        set A := U' ⊔ Subgroup.zpowers a with hAdef
        have hAV : A ≤ V := sup_le hU'V (Subgroup.zpowers_le.2 ha.1)
        have hU'A : U' < A := by
          refine lt_of_le_of_ne le_sup_left fun heq => ha.2 ?_
          have haA : a ∈ A := (le_sup_right : Subgroup.zpowers a ≤ A) (Subgroup.mem_zpowers a)
          rw [← heq] at haA
          exact haA.2
        have hA1 : E3.mQuot V A ≤ 1 := by
          have h1 := E3.mQuot_add hU'A.le hAV
          have h2 : E3.mQuot A U' ≠ 0 := fun h0 =>
            hU'A.ne ((E3.mQuot_eq_zero_iff (hV2.to_le hAV) hU'A.le).1 h0)
          omega
        have hle : L ⊓ Subgroup.centralizer ({a} : Set G) ≤
            Subgroup.centralizer (A : Set G) := by
          intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hAx : A ≤ Subgroup.centralizer ({x} : Set G) := sup_le
            (fun u hu => Subgroup.mem_centralizer_singleton_iff.2
              (Subgroup.mem_centralizer_iff.1 hu.2 x hx.1).symm)
            (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2
              (Subgroup.mem_centralizer_singleton_iff.1 hx.2).symm))
          exact Subgroup.mem_centralizer_singleton_iff.1 (hAx hy)
        exact hle.trans ((hall A hAV hA1).trans h.normalizer_le)
    calc E3.rParam V ≤ E3.mQuot V A := rParam_le_mQuot hAV hAC
      _ ≤ 1 := by exact_mod_cast hA1
  obtain ⟨hm, h6⟩ := e6_17 h311 hV h h15 hr
  have hU'Γ : U' ∈ gammaE64 V M := mem_gammaE64_of_mQuot_lt hV h hU'V hU'1 hU'M (by omega)
  have hm3 : CFSG.Open.pRank 3 L = 2 := by
    refine le_antisymm ?_ ?_
    · exact (CFSG.SectionRank.pRank_mono (by norm_num)
        (hLU'.trans (Subgroup.centralizer_le_normalizer _))).trans
        ((A1b.pRank_le_evenRank Nat.prime_three (by norm_num)
          ⟨U', hU'1, hV2.to_le hU'V, rfl⟩).trans h.qtke.2.2)
    · exact CFSG.SectionRank.le_pRank (by norm_num) hEL hE3 (by rw [hE9]; norm_num)
  have hq : QTKECore G := qtkeCore_of_cat h.nonabelian h.qtke
  have hU₁ : ∀ t ∈ Subgroup.normalizer (V : Set G), U' ⊓ CFSG.conjugate U' t ≤ V ∧
      U' ⊓ CFSG.conjugate U' t ≠ ⊥ := by
    intro t ht
    refine ⟨inf_le_left.trans hU'V, fun h0 => ?_⟩
    have h1 := mQuot_inf_le (U := U') (U' := CFSG.conjugate U' t) hV2
    rw [h0, mQuot_conjugate ht] at h1
    omega
  have hrank : ∀ t ∈ Subgroup.normalizer (V : Set G), CFSG.Open.pRank 3
      (Subgroup.centralizer ((U' ⊓ CFSG.conjugate U' t : Subgroup G) : Set G)) ≤ 2 := by
    intro t ht
    exact (CFSG.SectionRank.pRank_mono (by norm_num) (Subgroup.centralizer_le_normalizer _)).trans
      ((A1b.pRank_le_evenRank Nat.prime_three (by norm_num)
        ⟨_, (hU₁ t ht).2, hV2.to_le (hU₁ t ht).1, rfl⟩).trans h.qtke.2.2)
  have hcomp : ∀ t ∈ Subgroup.normalizer (V : Set G),
      IsComponentIn L (Subgroup.centralizer ((U' ⊓ CFSG.conjugate U' t : Subgroup G) : Set G)) := by
    intro t ht
    set U₁ := U' ⊓ CFSG.conjugate U' t with hU₁def
    obtain ⟨hU₁V, hU₁1⟩ := hU₁ t ht
    set H₁ := Subgroup.centralizer (U₁ : Set G) with hH₁def
    have hpc : pCoreOf 2 H₁ ≠ ⊥ := by
      intro h0
      apply hU₁1
      refine le_bot_iff.1 (h0 ▸ C1.le_pCoreOf_of_normalized ?_
        (Subgroup.centralizer_le_normalizer _) (hV2.to_le hU₁V))
      exact fun w hw => Subgroup.mem_centralizer_iff.2 fun w' hw' => hVc _ (hU₁V hw') _ (hU₁V hw)
    have hK1 : CFSG.SectionRank.IsSQTKCat ↥H₁ := hq.1 H₁ hpc
    have hCH₁ : Subgroup.centralizer (U' : Set G) ≤ H₁ := Subgroup.centralizer_le inf_le_left
    have hU'H₁ : U' ≤ H₁ := fun u hu => Subgroup.mem_centralizer_iff.2 fun w hw =>
      hVc _ (hU₁V hw) _ (hU'V hu)
    have hL2 : Id2519.IsTwoComponentIn L (H₁ ⊓ Subgroup.centralizer (U' : Set G)) := by
      rw [inf_eq_right.2 hCH₁]
      exact Id2519.isTwoComponentIn_of_isComponentIn hLc' (two_dvd_card_of_isQuasisimple hLq)
    obtain ⟨K, hK2, hLK, hKn, -, hKq⟩ := hI31 G H₁ U' L hK1 hU'H₁ (hV2.to_le hU'V) hL2 hm3
    have hKc : IsComponentIn K H₁ := Id2519.isComponentIn_of_mem_cComp hK2.1 hKq
    have hU'NK : U' ≤ Subgroup.normalizer (K : Set G) :=
      hU'H₁.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKc.1).1 hKn)
    have hLKC : IsComponentIn L (K ⊓ Subgroup.centralizer (U' : Set G)) :=
      BenderBranch.isComponentIn_of_le hLc' (le_inf hLK hLc'.1) inf_le_right
    have hU'K := le_centralizer_of_heAt hlist hI31 hfam h.simple h.nonabelian hq
      (hV2.to_le hU'V) (fun x hx y hy => hVc _ (hU'V hx) _ (hU'V hy)) hLA7
      (fun A K' hAU' hA1 hK' hU'N hLK' hHe => le_centralizer_of_isHeQuot_ctx h68 hRes hV h h15
        hU hU2 hL hLA7 hm hq2 hLM hAU' hA1 hK' hU'N hLK' hHe)
      inf_le_left hU₁1 hKc hU'NK hLKC
    have hKc' : IsComponentIn K (Subgroup.centralizer (U' : Set G)) :=
      BenderBranch.isComponentIn_of_le hKc (Subgroup.le_centralizer_iff.1 hU'K) hCH₁
    rcases BenderBranch.eq_or_commute_of_isComponentIn hLc' hKc' with heq | hcomm
    · rw [heq]
      exact hKc
    · exfalso
      have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hLq.1
      have hbot : L = ⊥ := by
        rw [← hperf, eq_bot_iff, ← hcomm]
        exact Subgroup.commutator_mono le_rfl hLK
      exact (Subgroup.nontrivial_iff_ne_bot L).mp
        (CFSG.LocalCores.isQuasisimple_nontrivial hLq) hbot
  have hconjc : ∀ t ∈ Subgroup.normalizer (V : Set G), IsComponentIn (CFSG.conjugate L t)
      (Subgroup.centralizer ((U' ⊓ CFSG.conjugate U' t : Subgroup G) : Set G)) := by
    intro t ht
    have h1 := isComponentIn_conjugate'
      (hcomp t⁻¹ ((Subgroup.normalizer (V : Set G)).inv_mem ht)) t
    rwa [BenderBranch.conjugate_inf, BenderBranch.conjugate_conjugate, inv_mul_cancel,
      BenderBranch.conjugate_one, inf_comm (CFSG.conjugate U' t) U'] at h1
  have hnorm : ∀ t ∈ T, CFSG.conjugate L t = L := by
    intro t ht
    have htN : t ∈ Subgroup.normalizer (V : Set G) := h.normal ht
    by_contra hne
    have hc : ⁅L, CFSG.conjugate L t⁆ = ⊥ :=
      (BenderBranch.eq_or_commute_of_isComponentIn (hcomp t htN) (hconjc t htN)).resolve_left
        (Ne.symm hne)
    have hc' : L ≤ Subgroup.centralizer ((CFSG.conjugate L t : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc
    set Et := CFSG.conjugate E t with hEtdef
    have hEtL : Et ≤ CFSG.conjugate L t := BenderBranch.conjugate_mono hEL t
    have hEt3 : IsElemAbelian 3 Et :=
      CFSG.SectionRank.isElemAbelian_map hE3 (MulAut.conj t⁻¹).toMonoidHom
    have hne' : ¬ Et ≤ E := by
      intro hle
      have h1 : Et ≤ L ⊓ Subgroup.centralizer (L : Set G) :=
        le_inf (hle.trans hEL) (hEtL.trans (Subgroup.le_centralizer_iff.1 hc'))
      have h2 := Subgroup.card_le_of_le h1
      have h3 := card_inf_centralizer_le_card_center L
      rw [hEtdef, BenderBranch.card_conjugate, hE9] at h2
      rcases hLA7.2 with h4 | h4 <;> omega
    have h3 := three_le_pRank_of_commuting_E (p := 3) hc' (hcomp t htN).1 (hconjc t htN).1 hEL
      hEtL hE3 hEt3 (by rw [hE9]; norm_num) hne'
    have := hrank t htN
    omega
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := fun t ht =>
    BenderBranch.conjugate_eq_iff_mem_normalizer.1 (hnorm t ht)
  have hTU' : T ≤ Subgroup.normalizer (U' : Set G) :=
    B2F.le_normalizer_inf h.normal (B2F.le_normalizer_centralizer hTL)
  exact hU'M (e6_13 h311 h hU'V hU'1 hU'Γ.2.2.2 hTU')

end E6

end CFSG.Quasithin
