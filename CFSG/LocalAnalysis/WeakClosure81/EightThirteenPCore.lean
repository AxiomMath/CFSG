module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPBorel
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPFit
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPShape

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
  (IsL2 IsSz IsL3 IsU3 IsSp4 IsU4 IsU5 IsOmega8m Is3D4 IsAlt IsSL3 Bar2 OInf Opp)

private theorem wc813pcore_hasQuotShape_bot_of {Y : Type} [Group Y] {J : Subgroup Y}
    {P : ∀ (X : Type) [Group X], Prop} (h : P ↥J) :
    HasQuotShape J ((⊥ : Subgroup Y) : Set Y) P :=
  ⟨↥J, inferInstance, MonoidHom.id ↥J, Function.surjective_id, by
    intro k
    exact ⟨fun hk => Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val hk),
      fun hk => Subtype.ext (Subgroup.mem_bot.mp hk)⟩, h⟩

theorem isComponentModN_of_isComponentOf {Y : Type} [Group Y] [Finite Y] {J : Subgroup Y}
    (h : IsComponentOf J ⊤) : IsComponentModN (⊥ : Subgroup Y) ⊤ J := by
  refine ⟨?_, bot_le, le_top, h.2.1, ?_⟩
  · rw [Subgroup.bot_subgroupOf]
    infer_instance
  · refine wc813pcore_hasQuotShape_bot_of (P := fun X _ => CFSG.IsQuasisimple X) ?_
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open ↥J).mpr h.2.2)

theorem shape_of_oddShape5 {Y : Type} [Group Y] [Finite Y] {J : Subgroup Y} (h : OddShape5 J) :
    (ShapeL2Mod (⊥ : Subgroup Y) J ∨ ShapeU3Mod (⊥ : Subgroup Y) J) ∨
      (RankTwoShape J ∧ ShapeRankTwoMod (⊥ : Subgroup Y) J) := by
  rcases h.2.2 with h2 | h2 | h3 | h4 | h5
  · exact Or.inl (Or.inl (wc813pcore_hasQuotShape_bot_of h2))
  · exact Or.inl (Or.inr (wc813pcore_hasQuotShape_bot_of h2))
  · exact Or.inr ⟨Or.inl h3, Or.inl (wc813pcore_hasQuotShape_bot_of h3)⟩
  · exact Or.inr ⟨Or.inr (Or.inl h4), Or.inr (Or.inr (wc813pcore_hasQuotShape_bot_of h4))⟩
  · exact Or.inr ⟨Or.inr (Or.inr h5), Or.inr (Or.inl (wc813pcore_hasQuotShape_bot_of h5))⟩

variable {Q : Type} [Group Q] [Finite Q] {T A B R L₀ : Subgroup Q}

private theorem wc813pcore_oTwoMod_le {Y : Type} [Group Y] (N K : Subgroup Y) :
    oTwoMod N K ≤ K :=
  iSup₂_le fun _ hW => hW.2.1

private theorem wc813pcore_isPGroup_oTwoMod_bot {Y : Type} [Group Y] (K : Subgroup Y) :
    IsPGroup 2 (oTwoMod (⊥ : Subgroup Y) K) := by
  classical
  let famY : Set (Subgroup Y) :=
    {W | (⊥ : Subgroup Y) ≤ W ∧ W ≤ K ∧ (W.subgroupOf K).Normal ∧
      ∀ w ∈ W, ∃ k : ℕ, w ^ 2 ^ k ∈ (⊥ : Subgroup Y)}
  have hoTwo : oTwoMod (⊥ : Subgroup Y) K = ⨆ W ∈ famY, W := rfl
  let H : {W : Subgroup Y // W ∈ famY} → Subgroup ↥K := fun W => W.1.subgroupOf K
  have hHp : ∀ i, IsPGroup 2 (H i) := by
    rintro ⟨W, hW⟩
    have hWY : IsPGroup 2 W := by
      intro w
      obtain ⟨k, hk⟩ := hW.2.2.2 (w : Y) w.2
      refine ⟨k, ?_⟩
      apply Subtype.ext
      simpa using (Subgroup.mem_bot.mp hk)
    exact hWY.of_equiv (Subgroup.subgroupOfEquivOfLe hW.2.1).symm
  have hHn : ∀ i, (H i).Normal := fun i => i.2.2.2.1
  have hpK : IsPGroup 2 ↥(⨆ i, H i) := by
    haveI : ∀ i, (H i).Normal := hHn
    exact Sylow.iSup_of_normal H hHp
  have hmap : (⨆ i, H i).map K.subtype = oTwoMod (⊥ : Subgroup Y) K := by
    rw [Subgroup.map_iSup]
    have hWi : ∀ i, (H i).map K.subtype = (i.1 : Subgroup Y) := fun i =>
      Subgroup.map_subgroupOf_eq_of_le i.2.2.1
    simp only [hWi]
    rw [hoTwo]
    exact iSup_subtype'' famY id
  rw [← hmap]
  exact hpK.map K.subtype

theorem Cfg813.b_not_le_of_astar (hF0 : OddSchurMultiplierFact) (hF1 : InvolutionCentralizerFact)
    (hF2 : FourGroupInnerFact) (h : Cfg813 T A B R L₀) {J K : Subgroup Q}
    (hJ : IsComponentOf J ⊤) (hne : ¬ A ≤ centralizer (J : Set Q)) (hK : K ≤ J)
    (hnot : ¬ Astar T J A ≤ oTwoMod (⊥ : Subgroup Q) K) :
    ¬ ∀ x ∈ A, ∃ o ∈ oTwoMod (⊥ : Subgroup Q) K,
      ∃ t ∈ cenTMod (⊥ : Subgroup Q) J T, (o * t)⁻¹ * x ∈ (⊥ : Subgroup Q) := by
  classical
  intro hprop
  apply hnot
  intro ℓ hℓ
  obtain ⟨hℓTJ, c, hc, hℓcA⟩ := mem_Astar.mp hℓ
  obtain ⟨hℓT, hℓJ⟩ := Subgroup.mem_inf.mp hℓTJ
  obtain ⟨hcT, hcC⟩ := Subgroup.mem_inf.mp hc
  obtain ⟨o, ho, t, ht, hott⟩ := hprop (ℓ * c) hℓcA
  have hot : o * t = ℓ * c := by
    have h1 : (o * t)⁻¹ * (ℓ * c) = 1 := Subgroup.mem_bot.mp hott
    exact inv_mul_eq_one.mp h1
  have hoK : o ∈ K := wc813pcore_oTwoMod_le (⊥ : Subgroup Q) K ho
  have hoJ : o ∈ J := hK hoK
  set z : Q := ℓ⁻¹ * o with hz_def
  have hz_eq : z = c * t⁻¹ := by
    rw [hz_def]
    calc ℓ⁻¹ * o = ℓ⁻¹ * (o * t) * t⁻¹ := by group
      _ = ℓ⁻¹ * (ℓ * c) * t⁻¹ := by rw [hot]
      _ = c * t⁻¹ := by group
  have hzJ : z ∈ J := by
    rw [hz_def]
    exact J.mul_mem (J.inv_mem hℓJ) hoJ
  have hzC : z ∈ Subgroup.centralizer (J : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hxJ
    rw [hz_eq]
    have hcx : Commute x c := Subgroup.mem_centralizer_iff.mp hcC x hxJ
    have htx : Commute x t := by
      have h1 : t * x = x * t := by
        have h2 := Subgroup.mem_bot.mp (ht.2 x hxJ)
        calc t * x = (t * x * t⁻¹ * x⁻¹) * (x * t) := by group
          _ = 1 * (x * t) := by rw [h2]
          _ = x * t := by group
      exact h1.symm
    exact hcx.mul_right htx.inv_right
  have hz_mem_center : (⟨z, hzJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzC (g : Q) g.2
  have hcenter_odd : Odd (Nat.card (Subgroup.center ↥J)) := Cfg813.center_odd h hJ
  have hdiv : orderOf z ∣ Nat.card (Subgroup.center ↥J) := by
    rw [← Subgroup.orderOf_mk z hzJ]
    exact Subgroup.orderOf_dvd_natCard (Subgroup.center ↥J) hz_mem_center
  have hP : IsPGroup 2 (oTwoMod (⊥ : Subgroup Q) K) := wc813pcore_isPGroup_oTwoMod_bot K
  obtain ⟨a, ha⟩ := hP.exists_pow_pow_eq_one (⟨o, ho⟩ : ↥(oTwoMod (⊥ : Subgroup Q) K))
  have ha' : o ^ 2 ^ a = 1 := by
    have := congrArg (fun x : ↥(oTwoMod (⊥ : Subgroup Q) K) => (x : Q)) ha
    simpa using this
  obtain ⟨b, hb⟩ := h.sylow.2.1 ⟨ℓ, hℓT⟩
  have hb' : ℓ ^ 2 ^ b = 1 := by
    have := congrArg (fun x : ↥T => (x : Q)) hb
    simpa using this
  have hz_comm_o : o * z = z * o := Subgroup.mem_centralizer_iff.mp hzC o hoJ
  have hcomm : Commute (ℓ⁻¹) o := by
    have h1 : o * ℓ⁻¹ = ℓ⁻¹ * o := by
      have h2 : o * ℓ⁻¹ * o = ℓ⁻¹ * o * o := by
        simpa [mul_assoc, hz_def] using hz_comm_o
      exact mul_right_cancel h2
    exact h1.symm
  have hoM : o ^ 2 ^ max a b = 1 := by
    have hdvd : 2 ^ a ∣ 2 ^ max a b := Nat.pow_dvd_pow 2 (le_max_left a b)
    exact orderOf_dvd_iff_pow_eq_one.mp
      (dvd_trans (orderOf_dvd_iff_pow_eq_one.mpr ha') hdvd)
  have hℓM : ℓ ^ 2 ^ max a b = 1 := by
    have hdvd : 2 ^ b ∣ 2 ^ max a b := Nat.pow_dvd_pow 2 (le_max_right a b)
    exact orderOf_dvd_iff_pow_eq_one.mp
      (dvd_trans (orderOf_dvd_iff_pow_eq_one.mpr hb') hdvd)
  have hz2 : z ^ 2 ^ max a b = 1 := by
    rw [hz_def, hcomm.mul_pow (2 ^ max a b), inv_pow, hℓM, hoM]
    group
  have hz2dvd : orderOf z ∣ 2 ^ max a b := orderOf_dvd_iff_pow_eq_one.mpr hz2
  have hcop2 : Nat.Coprime (Nat.card (Subgroup.center ↥J)) 2 :=
    Nat.coprime_two_right.mpr hcenter_odd
  have hcop : Nat.Coprime (2 ^ max a b) (Nat.card (Subgroup.center ↥J)) :=
    (hcop2.pow_right (max a b)).symm
  have hord1 : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes hcop hz2dvd hdiv
  have hz1 : z = 1 := orderOf_eq_one_iff.mp hord1
  have hℓ_eq : ℓ = o := by
    rw [hz_def] at hz1
    exact inv_mul_eq_one.mp hz1
  rw [hℓ_eq]
  exact ho

theorem Cfg813.commute_inf_conjClosure (hF0 : OddSchurMultiplierFact)
    (hF1 : InvolutionCentralizerFact) (hF2 : FourGroupInnerFact) (h : Cfg813 T A B R L₀)
    {J₀ : Subgroup Q} (hJ₀ : IsComponentOf J₀ ⊤)
    (hall : ∀ J : Subgroup Q, IsComponentOf J ⊤ → ¬ A ≤ centralizer (J : Set Q) →
      ∀ ℓ ∈ Astar T J A, ∀ s ∈ T ⊓ J, ℓ * s = s * ℓ) :
    ∀ a ∈ A, ∀ t ∈ T ⊓ conjClosure J₀ ⊤, a * t * a⁻¹ * t⁻¹ ∈ (⊥ : Subgroup Q) := by
  classical
  have hconj_le : conjClosure J₀ ⊤ ≤ genFittingLayer Q := by
    refine conjClosure_le (fun g _ z hz => ?_)
    have hcomp : IsComponentOf (conjSubgroup J₀ g⁻¹) ⊤ :=
      (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj (g⁻¹)⁻¹) J₀).mpr hJ₀
    have hle : conjSubgroup J₀ g⁻¹ ≤ genFittingLayer Q := by
      rw [genFittingLayer.eq_sSup]
      exact le_sSup hcomp
    have hmem : g * z * g⁻¹ ∈ conjSubgroup J₀ g⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have h : g⁻¹ * (g * z * g⁻¹) * g = z := by group
      rw [inv_inv, h]
      exact hz
    exact hle hmem
  have hgen : ∀ J : Subgroup Q, IsComponentOf J ⊤ →
      A ≤ Subgroup.centralizer ((T ⊓ J : Subgroup Q) : Set Q) := by
    intro J hJ a haA
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    by_cases hne : A ≤ Subgroup.centralizer (J : Set Q)
    · have hac : a ∈ Subgroup.centralizer (J : Set Q) := hne haA
      exact Subgroup.mem_centralizer_iff.mp hac s (Subgroup.mem_inf.mp hs).2
    · obtain ⟨-, -, -, hAst_decomp⟩ := Cfg813.astar_facts hF0 hF1 hF2 h hJ hne
      obtain ⟨ℓ, hℓ, c, hc, haeq⟩ := hAst_decomp a haA
      obtain ⟨hsT, hsJ⟩ := Subgroup.mem_inf.mp hs
      have hℓs : ℓ * s = s * ℓ := hall J hJ hne ℓ hℓ s hs
      have hcs : s * c = c * s :=
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 s hsJ
      calc s * a = s * (ℓ * c) := by rw [haeq]
        _ = (s * ℓ) * c := by group
        _ = (ℓ * s) * c := by rw [hℓs]
        _ = ℓ * (s * c) := by group
        _ = ℓ * (c * s) := by rw [hcs]
        _ = (ℓ * c) * s := by group
        _ = a * s := by rw [haeq]
  intro a haA t ht
  have hmem : t ∈ ⨆ (J : Subgroup Q) (_ : IsComponentOf J ⊤), T ⊓ J :=
    Cfg813.inf_layer_le_iSup h ⟨ht.1, hconj_le ht.2⟩
  have ht_comm : t * a = a * t := by
    rw [iSup_subtype'] at hmem
    refine Subgroup.iSup_induction (C := fun x => x * a = a * x)
      (fun J : {J : Subgroup Q // IsComponentOf J ⊤} => T ⊓ J.1) hmem ?_ ?_ ?_
    · intro J s hs
      exact Subgroup.mem_centralizer_iff.mp (hgen J.1 J.2 haA) s hs
    · group
    · intro x y hx hy
      calc x * y * a = x * (y * a) := by group
        _ = x * (a * y) := by rw [hy]
        _ = (x * a) * y := by group
        _ = (a * x) * y := by rw [hx]
        _ = a * (x * y) := by group
  exact Subgroup.mem_bot.mpr (by rw [ht_comm.symm]; group)

private theorem wc813pcore_main (hF0 : OddSchurMultiplierFact)
    (hF1 : InvolutionCentralizerFact) (hF2 : FourGroupInnerFact) (hF3 : BorelOvergroupFact)
    (hF4 : ChoiceOfKFact) (h : Cfg813 T A B R L₀) {J : Subgroup Q}
    (hJ : IsComponentOf J ⊤) (hne : ¬ A ≤ centralizer (J : Set Q))
    (hcase : (RankTwoShape J → ¬ (∀ ℓ ∈ Astar T J A, ∀ s ∈ T ⊓ J, ℓ * s = s * ℓ)) ∨
      (∀ a ∈ A, ∀ t ∈ T ⊓ conjClosure J ⊤, a * t * a⁻¹ * t⁻¹ ∈ (⊥ : Subgroup Q))) :
    ∃ K : Subgroup Q, Concl813Gen (⊥ : Subgroup Q) B ⊤ T A J K := by
  obtain ⟨hAst_le, hAst_elem, hAst_card, hAst_decomp⟩ :=
    Cfg813.astar_facts hF0 hF1 hF2 h hJ hne
  obtain ⟨K, hKJ, hAstK, hnotAst, hKquot, hSylK, hidx, hpar⟩ :=
    hF4 Q J (T ⊓ J) (Astar T J A) (Cfg813.oddShape5 hF0 h hJ)
      (Cfg813.isSylowIn_inf_component h hJ) hAst_le hAst_elem hAst_card
      (Cfg813.astar_k1 hF0 hF1 hF2 h hJ hne) (Cfg813.tis_astar hF0 hF1 hF2 hF3 h hJ hne)
  have hS : T ⊓ J ≠ ⊥ := by
    intro hbot
    have hle : Astar T J A ≤ ⊥ := by
      rw [hbot] at hAst_le
      exact hAst_le
    have hbot' : Astar T J A = ⊥ := le_bot_iff.mp hle
    rw [hbot', Subgroup.card_bot] at hAst_card
    norm_num at hAst_card
  refine ⟨K, ?_⟩
  have hJB : J ⊓ B = J ⊓ normalizer ((T ⊓ J : Subgroup Q) : Set Q) :=
    (inf_comm J B).trans (Cfg813.inf_component_eq hF0 hF3 h hJ hS)
  have hKB : K ⊓ B = K ⊓ (J ⊓ normalizer ((T ⊓ J : Subgroup Q) : Set Q)) := by
    have h1 : K ⊓ B = K ⊓ (J ⊓ B) := by
      ext x
      constructor
      · intro hx; exact ⟨hx.1, hKJ hx.1, hx.2⟩
      · intro hx; exact ⟨hx.1, hx.2.2⟩
    rw [h1, hJB]
  have hTK : T ⊓ K = (T ⊓ J) ⊓ K := by
    ext x
    constructor
    · intro hx; exact ⟨⟨hx.1, hKJ hx.2⟩, hx.2⟩
    · intro hx; exact ⟨hx.1.1, hx.2⟩
  have hshape := shape_of_oddShape5 (Cfg813.oddShape5 hF0 h hJ)
  refine ⟨?_, hKJ, bot_le, ?_, ?_, hKquot, ?_, ?_, ?_⟩
  · exact isComponentModN_of_isComponentOf hJ
  · intro x hx
    obtain ⟨ℓ, hℓ, c, hc, rfl⟩ := hAst_decomp x hx
    refine ⟨ℓ, hAstK hℓ, c, ?_, ?_⟩
    · exact ⟨(Subgroup.mem_inf.mp hc).1, fun l hl => by
        have hcomm : c * l = l * c :=
          (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 l hl).symm
        exact Subgroup.mem_bot.mpr (by rw [hcomm]; group)⟩
    · exact Subgroup.mem_bot.mpr (by group)
  · exact Cfg813.b_not_le_of_astar hF0 hF1 hF2 h hJ hne hKJ hnotAst
  · rw [hKB]; exact hidx
  · rcases hshape with (hL2 | hU3) | ⟨hr, hrt⟩
    · exact Or.inl (Or.inl hL2)
    · exact Or.inl (Or.inr hU3)
    · refine Or.inr ⟨hrt, ?_⟩
      rcases hcase with hleft | hright
      · exact Or.inl (hpar hr (hleft hr))
      · exact Or.inr hright
  · rw [hTK]; exact hSylK

theorem Cfg813.exists_concl (hF0 : OddSchurMultiplierFact) (hF1 : InvolutionCentralizerFact)
    (hF2 : FourGroupInnerFact) (hF3 : BorelOvergroupFact) (hF4 : ChoiceOfKFact)
    (h : Cfg813 T A B R L₀) :
    ∃ L K : Subgroup Q, Concl813Gen (⊥ : Subgroup Q) B ⊤ T A L K := by
  by_cases hex : ∃ J : Subgroup Q, IsComponentOf J ⊤ ∧ ¬ A ≤ centralizer (J : Set Q) ∧
      ¬ ∀ ℓ ∈ Astar T J A, ∀ s ∈ T ⊓ J, ℓ * s = s * ℓ
  · obtain ⟨J, hJ, hne, hnc⟩ := hex
    obtain ⟨K, hK⟩ :=
      wc813pcore_main hF0 hF1 hF2 hF3 hF4 h hJ hne (Or.inl (fun _ => hnc))
    exact ⟨J, K, hK⟩
  · obtain ⟨J, hJ, hne⟩ := h.exists_component
    have hall : ∀ J : Subgroup Q, IsComponentOf J ⊤ → ¬ A ≤ centralizer (J : Set Q) →
        ∀ ℓ ∈ Astar T J A, ∀ s ∈ T ⊓ J, ℓ * s = s * ℓ := by
      intro J hJ hne
      by_contra h
      exact hex ⟨J, hJ, hne, h⟩
    obtain ⟨K, hK⟩ := wc813pcore_main hF0 hF1 hF2 hF3 hF4 h hJ hne
      (Or.inr (Cfg813.commute_inf_conjClosure hF0 hF1 hF2 h hJ hall))
    exact ⟨J, K, hK⟩

end CFSG.LocalAnalysis.WeakClosure81

end
