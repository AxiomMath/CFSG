module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.Defs
public import CFSG.Quasithin.Background.E3MParamAttained
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.Assembly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCATwoRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3TenBlocksA
public import CFSG.GroupTheory.SwappedFactorsOffenders
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13FoundA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise


private theorem component_eq_left_or_right_of_le_sup {W : Type*} [CommGroup W] [Finite W]
    {Y L₁ L₂ X K : Subgroup (MulAut W)} (hc₁ : IsComponentOf L₁ Y)
    (hc₂ : IsComponentOf L₂ Y) (hK : IsComponentOf K Y) (hKX : K ≤ X)
    (hX : X = L₁ ⊔ L₂) : K = L₁ ∨ K = L₂ := by
  rcases eq_or_commute_of_isComponentOf hK hc₁ with h1 | h1
  · exact Or.inl h1
  rcases eq_or_commute_of_isComponentOf hK hc₂ with h2 | h2
  · exact Or.inr h2
  exfalso
  have hKcomm : ∀ k ∈ K, ∀ x ∈ (L₁ ⊔ L₂ : Subgroup (MulAut W)), k * x = x * k := by
    intro k hk x hx
    rw [Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
        rcases hx with hx | hx
        · exact h1 k hk x hx
        · exact h2 k hk x hx
    | one => simp
    | mul x y _ _ ihx ihy =>
        calc k * (x * y) = k * x * y := (mul_assoc _ _ _).symm
          _ = x * k * y := by rw [ihx]
          _ = x * (k * y) := mul_assoc _ _ _
          _ = x * (y * k) := by rw [ihy]
          _ = x * y * k := (mul_assoc _ _ _).symm
    | inv x _ ih =>
        have h' : x⁻¹ * k = k * x⁻¹ := by
          calc x⁻¹ * k = x⁻¹ * (k * x) * x⁻¹ := by group
            _ = x⁻¹ * (x * k) * x⁻¹ := by rw [ih]
            _ = k * x⁻¹ := by group
        exact h'.symm
  have hKabel : IsMulCommutative ↥K := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have hb : (b : MulAut W) ∈ L₁ ⊔ L₂ := by
      have hbx := hKX b.2
      rwa [hX] at hbx
    exact hKcomm a.1 a.2 b.1 hb
  have hq : CFSG.Open.IsQuasisimple ↥K := hK.2.2
  have hbot : commutator ↥K = ⊥ := (commutator_eq_bot_iff (G := ↥K)).mpr hKabel
  haveI : _root_.IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  haveI : Nontrivial ↥K :=
    (QuotientGroup.mk_surjective (s := Subgroup.center ↥K)).nontrivial
  have htopbot : (⊤ : Subgroup ↥K) = ⊥ := by rw [← hq.1, hbot]
  exact top_ne_bot htopbot

theorem w4Thm14_4_swap (hKI : KInvolGen) (hKS : KSimpleGen2) (hPair : KA5PairIrr)
    (hSw : K144Swap16)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L₁ L₂ X : Subgroup (MulAut W)} (hO2 : O2Trivial Y) (hB : IsBasicModule Y)
    (hc₁ : IsComponentOf L₁ Y) (hc₂ : IsComponentOf L₂ Y) (ha₁ : IsAlt ↥L₁ 5)
    (ha₂ : IsAlt ↥L₂ 5) (hne : L₁ ≠ L₂) (hX : X = L₁ ⊔ L₂) (hXn : (X.subgroupOf Y).Normal)
    (hb₁ : bParam L₁ Y = 2) (hfix : fixV X = ⊥) (hm : E3.mParam Y = 4)
    (hsw : ∃ g ∈ Y, L₂ = L₁.map (MulAut.conj g).toMonoidHom) :
    ((∃ g ∈ Y, L₂ = L₁.map (MulAut.conj g).toMonoidHom) ∧
        commSub (commSub (⊤ : Subgroup W) L₁) L₂ = ⊥) ∨
      ((∃ g ∈ Y, L₂ = L₁.map (MulAut.conj g).toMonoidHom) ∧ IsOmegaPlus ↥X 4 2 ∧
        SumOfNat (fun H U Z => NatOmegaPlus H U Z 4 2) X ⊤ ⊥ 2) ∨
      (IsOmegaPlus ↥X 4 2 ∧ NatOmegaPlus X ⊤ ⊥ 4 2) := by
  classical
  have hXle : X ≤ Y := hX.le.trans (sup_le hc₁.1 hc₂.1)
  have hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a :=
    B69.components_mul_comm_of_ne hc₂ hc₁ (Ne.symm hne)
  have hdisj : L₁ ⊓ L₂ = ⊥ := inf_eq_bot_of_commute_isAlt_five hcomm ha₁
  have hL₁X : L₁ ≤ X := by rw [hX]; exact le_sup_left
  have hL₂X : L₂ ≤ X := by rw [hX]; exact le_sup_right
  have hfix_inter : fixV X = fixV L₁ ⊓ fixV L₂ := by
    ext v
    rw [hX, s16t_blk_mem_fixV_sup_iff]
    simp
  have hL₁nX : (L₁.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hL₁X, hX]
    have hL₂cent : L₂ ≤ Subgroup.centralizer (L₁ : Set (MulAut W)) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcomm a ha b hb
    exact sup_le Subgroup.le_normalizer
      (hL₂cent.trans (Subgroup.centralizer_le_normalizer (L₁ : Set (MulAut W))))
  have hL₂nX : (L₂.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hL₂X, hX]
    have hL₁cent : L₁ ≤ Subgroup.centralizer (L₂ : Set (MulAut W)) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hcomm a ha b hb).symm
    exact sup_le (hL₁cent.trans (Subgroup.centralizer_le_normalizer (L₂ : Set (MulAut W))))
      Subgroup.le_normalizer
  have hconj₁ : ∀ x ∈ X, ∀ l ∈ L₁, x * l * x⁻¹ ∈ L₁ :=
    conj_mem_of_normal_subgroupOf hL₁X hL₁nX
  have hconj₂ : ∀ x ∈ X, ∀ l ∈ L₂, x * l * x⁻¹ ∈ L₂ :=
    conj_mem_of_normal_subgroupOf hL₂X hL₂nX
  have key : ∀ K : Subgroup (MulAut W), IsComponentOf K Y → K ≤ X → K = L₁ ∨ K = L₂ :=
    fun K hK hKX => component_eq_left_or_right_of_le_sup hc₁ hc₂ hK hKX hX
  have hgen₁ : (⨆ g ∈ Y, L₁.map (MulAut.conj g).toMonoidHom) = X :=
    iSup_conj_eq_of_swap hc₁ hc₂ ha₁ ha₂ hne hX hXn hsw
  have hHc₁ : X = ⨆ X' ∈ conjSet L₁ Y, X' := by
    rw [iSup_conjSet_eq_biSup_conj]
    exact hgen₁.symm
  obtain ⟨hbi, -, hHY, -, hnormH, hXne⟩ := h_facts hc₁ hHc₁
  have htop : (⨆ I ∈ irrSet X, I) = ⊤ :=
    ((w4Lem12_5_holds W hW Y hO2 hB X hXne hHY hnormH).2 L₁ hc₁ hbi).1.1
  have hQ : QuadTrivial X := by
    rw [hbi]
    exact quadTrivial_biSup_conj hc₁.2.2.1 Y
  have hsw' : ∃ g ∈ Y, L₁ = L₂.map (MulAut.conj g).toMonoidHom := by
    obtain ⟨g, hg, hg2⟩ := hsw
    refine ⟨g⁻¹, Y.inv_mem hg, ?_⟩
    rw [hg2, CFSG.Quasithin.B19.map_conj_map_conj, inv_mul_cancel]
    rw [show (MulAut.conj (1 : MulAut W)).toMonoidHom = MonoidHom.id (MulAut W) by
      ext x
      simp]
    exact (Subgroup.map_id L₁).symm
  have hgen₂ : (⨆ g ∈ Y, L₂.map (MulAut.conj g).toMonoidHom) = X :=
    iSup_conj_eq_of_swap hc₂ hc₁ ha₂ ha₁ (Ne.symm hne) (by rw [hX, sup_comm]) hXn hsw'
  have hHc₂ : X = ⨆ X' ∈ conjSet L₂ Y, X' := by
    rw [iSup_conjSet_eq_biSup_conj]
    exact hgen₂.symm
  have hL₁mem : L₁ ∈ conjSet L₂ Y := by
    obtain ⟨g, hg, hg2⟩ := hsw'
    exact ⟨g, hg, hg2⟩
  have hcard₁ : Nat.card ↥L₁ = 60 := by
    obtain ⟨e⟩ := ha₁
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hEvenY : Even (Nat.card Y) := by
    have hdvd : Nat.card ↥L₁ ∣ Nat.card ↥Y := Subgroup.card_dvd_of_le hc₁.1
    exact even_iff_two_dvd.mpr (dvd_trans ⟨30, by rw [hcard₁]; norm_num⟩ hdvd)
  obtain ⟨t, htY, htord, htval⟩ := E3.exists_involution_rkIdx_fixV_eq_mParam Y hEvenY
  have htpow : t ^ 2 = 1 := by rw [← htord]; exact pow_orderOf_eq_one t
  have hmval : rkIdx (fixV (Subgroup.zpowers t)) = 4 := htval.trans hm
  have hrkt : rk ↥(commV (Subgroup.zpowers t)) = 4 := by
    rw [← rkIdx_fixV_zpowers, hmval]
  have hnormX : Y ≤ Subgroup.normalizer (X : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXle).mp hXn
  have hXmap : X.map (MulAut.conj t).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnormX htY)
  have hK₁comp : IsComponentOf (L₁.map (MulAut.conj t).toMonoidHom) Y :=
    isComponentOf_map_conj_of_mem hc₁ htY
  have hK₁le : L₁.map (MulAut.conj t).toMonoidHom ≤ X := by
    have hle : L₁.map (MulAut.conj t).toMonoidHom ≤ X.map (MulAut.conj t).toMonoidHom :=
      Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom) hL₁X
    rwa [hXmap] at hle
  have hK₂comp : IsComponentOf (L₂.map (MulAut.conj t).toMonoidHom) Y :=
    isComponentOf_map_conj_of_mem hc₂ htY
  have hK₂le : L₂.map (MulAut.conj t).toMonoidHom ≤ X := by
    have hle : L₂.map (MulAut.conj t).toMonoidHom ≤ X.map (MulAut.conj t).toMonoidHom :=
      Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom) hL₂X
    rwa [hXmap] at hle
  have hK₁case := key _ hK₁comp hK₁le
  have hK₂case := key _ hK₂comp hK₂le
  have htperm : (L₁.map (MulAut.conj t).toMonoidHom = L₁ ∧
        L₂.map (MulAut.conj t).toMonoidHom = L₂) ∨
      (L₁.map (MulAut.conj t).toMonoidHom = L₂ ∧
        L₂.map (MulAut.conj t).toMonoidHom = L₁) := by
    rcases hK₁case with h1 | h1 <;> rcases hK₂case with h2 | h2
    · exfalso
      apply hne
      exact Subgroup.map_injective (f := (MulAut.conj t).toMonoidHom)
        (MulAut.conj t).injective (h1.trans h2.symm)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exfalso
      apply hne
      exact Subgroup.map_injective (f := (MulAut.conj t).toMonoidHom)
        (MulAut.conj t).injective (h1.trans h2.symm)
  have support_case :
      ((∃ U ∈ irrSet X, commSub U L₁ = ⊥ ∨ commSub U L₂ = ⊥) →
        ((∃ g ∈ Y, L₂ = L₁.map (MulAut.conj g).toMonoidHom) ∧
          commSub (commSub (⊤ : Subgroup W) L₁) L₂ = ⊥)) := by
    rintro ⟨U, hU, hUL₁ | hUL₂⟩
    ·
      have huniq : ∀ X' ∈ conjSet L₂ Y, ¬ commSub U X' ≤ fixV X → X' = L₂ := by
        intro X' hX' hnot
        obtain ⟨hX'comp, hX'X, -⟩ := conjSet_facts hc₂ hHc₂ hX'
        rcases key X' hX'comp hX'X with rfl | rfl
        · exfalso
          exact absurd (by rw [hUL₁]; exact bot_le) hnot
        · rfl
      have hforall := forall_unique_of_unique hW hO2 hB hc₂ hHc₂ hU huniq
      have hbot := commSub_commSub_eq_bot_of_unique hW hO2 hB hc₂ hHc₂ hfix hforall
        (self_mem_conjSet L₂ Y) hL₁mem (Ne.symm hne)
      refine ⟨hsw, ?_⟩
      have hcommut : ⁅L₁, L₂⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact (hcomm a ha b hb).symm
      rw [s13_commSub_comm L₁ L₂ hcommut (⊤ : Subgroup W)]
      exact hbot
    ·
      have huniq : ∀ X' ∈ conjSet L₁ Y, ¬ commSub U X' ≤ fixV X → X' = L₁ := by
        intro X' hX' hnot
        obtain ⟨hX'comp, hX'X, -⟩ := conjSet_facts hc₁ hHc₁ hX'
        rcases key X' hX'comp hX'X with rfl | rfl
        · rfl
        · exfalso
          exact absurd (by rw [hUL₂]; exact bot_le) hnot
      have hforall := forall_unique_of_unique hW hO2 hB hc₁ hHc₁ hU huniq
      exact ⟨hsw, commSub_commSub_eq_bot_of_unique hW hO2 hB hc₁ hHc₁ hfix hforall
        (self_mem_conjSet L₁ Y) hsw hne⟩
  by_cases hcase : ∃ U ∈ irrSet X, commSub U L₁ = ⊥ ∨ commSub U L₂ = ⊥
  · exact Or.inl (support_case hcase)
  · push Not at hcase
    have hIirr : ∀ I ∈ irrSet X, IsIrrOn X I ⊥ := by
      intro I hI
      have h := hI.2
      rwa [hfix, inf_bot_eq] at h
    have hIrank : ∀ I ∈ irrSet X, 8 ≤ rk ↥I := by
      intro I hI
      rcases hPair W hW L₁ L₂ X I hX hcomm ha₁ ha₂ (hIirr I hI)
        (hcase I hI).1 (hcase I hI).2 with h | h
      · omega
      · omega
    have hCommI₁ : ∀ I ∈ irrSet X, commSub I L₁ = I := by
      intro I hI
      have hirr := hIirr I hI
      have hle : commSub I L₁ ≤ I :=
        commSub_le_of_invariant fun l hl w hw => hirr.2.1 l (hL₁X hl) w hw
      have hstab : StableUnder X (commSub I L₁) :=
        stableUnder_commSub (fun x hx l hl => hconj₁ x hx l hl) hirr.2.1
      rcases hirr.2.2.2 (commSub I L₁) hstab bot_le hle with h | h
      · exact absurd h (hcase I hI).1
      · exact h
    have hCommI₂ : ∀ I ∈ irrSet X, commSub I L₂ = I := by
      intro I hI
      have hirr := hIirr I hI
      have hle : commSub I L₂ ≤ I :=
        commSub_le_of_invariant fun l hl w hw => hirr.2.1 l (hL₂X hl) w hw
      have hstab : StableUnder X (commSub I L₂) :=
        stableUnder_commSub (fun x hx l hl => hconj₂ x hx l hl) hirr.2.1
      rcases hirr.2.2.2 (commSub I L₂) hstab bot_le hle with h | h
      · exact absurd h (hcase I hI).2
      · exact h
    have htopL₁ : commSub (⊤ : Subgroup W) L₁ = ⊤ := by
      rw [eq_top_iff]
      conv_lhs => rw [← htop]
      refine iSup₂_le fun I hI => ?_
      rw [← hCommI₁ I hI]
      exact commSub_mono le_top le_rfl
    have htopL₂ : commSub (⊤ : Subgroup W) L₂ = ⊤ := by
      rw [eq_top_iff]
      conv_lhs => rw [← htop]
      refine iSup₂_le fun I hI => ?_
      rw [← hCommI₂ I hI]
      exact commSub_mono le_top le_rfl
    have htopX : commSub (⊤ : Subgroup W) X = ⊤ := by
      rw [eq_top_iff]
      conv_lhs => rw [← htop]
      exact iSup₂_le fun I hI => by
        rw [← hI.1]
        exact commSub_mono le_top le_rfl
    have hrkWle : rk W ≤ 16 := by
      by_cases hcent : ∀ x ∈ X, t * x = x * t
      ·
        have hTstab : StableUnder X (commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) := by
          refine stableUnder_commSub ?_ (fun x _ u _ => Subgroup.mem_top u)
          intro h hh x hx
          have hcx : h * x = x * h := by
            have hle : Subgroup.zpowers t ≤ Subgroup.centralizer ({h} : Set (MulAut W)) := by
              rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
              intro y hy
              rw [Set.mem_singleton_iff] at hy
              rw [hy]
              exact (hcent h hh).symm
            exact Subgroup.mem_centralizer_iff.mp (hle hx) h (Set.mem_singleton h)
          rw [hcx]
          simpa using hx
        have hneT : commSub (commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) X ≠ ⊥ := by
          intro hbot
          have hle : commSub (⊤ : Subgroup W) (Subgroup.zpowers t) ≤ fixV X :=
            commSub_eq_bot_iff.mp hbot
          have hbot2 : commSub (⊤ : Subgroup W) (Subgroup.zpowers t) = ⊥ :=
            le_bot_iff.mp (hle.trans (le_of_eq hfix))
          have h4 : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) = 4 := by
            rw [← commV_eq_commSub]
            exact hrkt
          rw [hbot2, rk_bot] at h4
          omega
        obtain ⟨I, hI, hIle⟩ := exists_mem_irrSet_le hQ hTstab hneT
        have h4 : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) = 4 := by
          rw [← commV_eq_commSub]
          exact hrkt
        have h8 := hIrank I hI
        have := rk_mono hIle
        omega
      · push Not at hcent
        obtain ⟨x₀, hx₀X, hx₀⟩ := hcent
        rcases htperm with ⟨hK₁eq, hK₂eq⟩ | ⟨hK₁eq, hK₂eq⟩
        ·
          have hnotboth : ¬ (∀ x ∈ L₁, t * x = x * t) ∨
              ¬ (∀ x ∈ L₂, t * x = x * t) := by
            by_cases hnc₁ : ∀ x ∈ L₁, t * x = x * t
            · by_cases hnc₂ : ∀ x ∈ L₂, t * x = x * t
              · exfalso
                have htC₁ : t ∈ Subgroup.centralizer (L₁ : Set (MulAut W)) := by
                  rw [Subgroup.mem_centralizer_iff]
                  intro a ha
                  exact (hnc₁ a ha).symm
                have htC₂ : t ∈ Subgroup.centralizer (L₂ : Set (MulAut W)) := by
                  rw [Subgroup.mem_centralizer_iff]
                  intro a ha
                  exact (hnc₂ a ha).symm
                have htC : t ∈ Subgroup.centralizer
                    ((L₁ ⊔ L₂ : Subgroup (MulAut W)) : Set (MulAut W)) := by
                  rw [CFSG.GroupTheory.centralizer_sup_eq_inf_centralizer]
                  exact Subgroup.mem_inf.mpr ⟨htC₁, htC₂⟩
                have htX : t ∈ Subgroup.centralizer (X : Set (MulAut W)) := by
                  rwa [hX]
                exact hx₀ (Subgroup.mem_centralizer_iff.mp htX x₀ hx₀X).symm
              · exact Or.inr hnc₂
            · exact Or.inl hnc₁
          rcases hnotboth with hnc₁ | hnc₂
          · push Not at hnc₁
            have hnorm₁ : ∀ x ∈ L₁, t * x * t⁻¹ ∈ L₁ := by
              intro x hx
              have hmem : (MulAut.conj t) x ∈ L₁.map (MulAut.conj t).toMonoidHom :=
                Subgroup.mem_map_of_mem _ hx
              rw [hK₁eq] at hmem
              simpa [MulAut.conj_apply] using hmem
            obtain ⟨y₁, hy₁, y₂, hy₂, y₃, hy₃, hle⟩ :=
              hKI (MulAut W) L₁ t (Or.inr ha₁) htpow hnorm₁ hnc₁
            have h16 : rk ↥(commSub (⊤ : Subgroup W) L₁) ≤ 16 := by
              have h := rk_commSub_le_of_le_closure hle
              rw [hrkt] at h
              simpa using h
            rw [← rk_top, ← htopL₁]
            exact h16
          · push Not at hnc₂
            have hnorm₂ : ∀ x ∈ L₂, t * x * t⁻¹ ∈ L₂ := by
              intro x hx
              have hmem : (MulAut.conj t) x ∈ L₂.map (MulAut.conj t).toMonoidHom :=
                Subgroup.mem_map_of_mem _ hx
              rw [hK₂eq] at hmem
              simpa [MulAut.conj_apply] using hmem
            obtain ⟨y₁, hy₁, y₂, hy₂, y₃, hy₃, hle⟩ :=
              hKI (MulAut W) L₂ t (Or.inr ha₂) htpow hnorm₂ hnc₂
            have h16 : rk ↥(commSub (⊤ : Subgroup W) L₂) ≤ 16 := by
              have h := rk_commSub_le_of_le_closure hle
              rw [hrkt] at h
              simpa using h
            rw [← rk_top, ← htopL₂]
            exact h16
        ·
          have hsimple₁ : IsSimpleGroup ↥L₁ := by
            obtain ⟨e⟩ := ha₁
            haveI : IsSimpleGroup (alternatingGroup (Fin 5)) :=
              alternatingGroup.isSimpleGroup (by simp)
            exact e.isSimpleGroup
          obtain ⟨y₁, hy₁, y₂, hy₂, hgen, hnc⟩ := hKS (MulAut W) L₁ (Or.inr ha₁)
          have hcommXt : ∀ x ∈ L₁, ∀ x' ∈ L₁.map (MulAut.conj t).toMonoidHom,
              x * x' = x' * x := by
            intro x hx x' hx'
            rw [hK₁eq] at hx'
            exact hcomm x hx x' hx'
          have hsum : L₁ ⊔ L₁.map (MulAut.conj t).toMonoidHom ≤
              Subgroup.closure {t, y₁ * t * y₁⁻¹, y₂ * t * y₂⁻¹,
                (y₁ * y₂) * t * (y₁ * y₂)⁻¹} :=
            sup_map_conj_le_closure hsimple₁
              hy₁ hy₂ hgen hnc hcommXt
          have hXleClosure : X ≤ Subgroup.closure
              {t, y₁ * t * y₁⁻¹, y₂ * t * y₂⁻¹, (y₁ * y₂) * t * (y₁ * y₂)⁻¹} := by
            rw [hX, ← hK₁eq]
            exact hsum
          have h16 : rk ↥(commSub (⊤ : Subgroup W) X) ≤ 16 := by
            have h := rk_commSub_le_of_le_closure hXleClosure
            rw [hrkt] at h
            simpa using h
          rw [htopX] at h16
          rw [rk_top] at h16
          exact h16
    have hPairApply : ∀ I ∈ irrSet X, rk ↥I = 8 ∧ NatOmegaPlus X I ⊥ 4 2 := by
      intro I hI
      rcases hPair W hW L₁ L₂ X I hX hcomm ha₁ ha₂ (hIirr I hI)
        (hcase I hI).1 (hcase I hI).2 with h | h
      · exact h
      · exfalso
        have hIeqTop : I = ⊤ := by
          refine eq_of_le_of_rk_le hW le_top ?_
          rw [rk_top, h]
          exact hrkWle
        have hrkW16 : rk W = 16 := by
          rw [← rk_top, ← hIeqTop]
          exact h
        have hIrrOnTop : IsIrrOn X ⊤ ⊥ := by
          simpa [hIeqTop] using hIirr I hI
        have hb := hSw W hW Y L₁ L₂ X hX hcomm ha₁ ha₂ hXle hXn hsw hIrrOnTop hrkW16
        omega
    obtain ⟨I₀, hI₀⟩ := exists_mem_irrSet_of_ne_bot hQ hXne
    have hSspan : sSup (irrSet X) = ⊤ := by
      rw [sSup_eq_iSup]
      exact htop
    obtain ⟨s, hI₀s, hsS, hsind, hssup⟩ :=
      exists_sSupIndep_spanning_of_family (L := X) (S := irrSet X) (I := I₀) hI₀
        (fun K hK => hK) (fun K _ => by rw [hfix, inf_bot_eq]) hSspan
    have hrkS : rk ↥(⊤ : Subgroup W) = s.ncard * 8 := by
      have h := s15_Lin_rk_sSup_eq_finsum hsind
      rw [hssup] at h
      have hconst : ∑ᶠ U ∈ s, rk ↥U = s.ncard * 8 :=
        s15_Two_finsum_mem_eq_ncard_mul s (fun U => rk ↥U) 8 (Set.toFinite s)
          (fun U hU => (hPairApply U (hsS hU)).1)
      rw [hconst] at h
      exact h
    have hrkW8 : rk W = s.ncard * 8 := by
      rw [← rk_top]
      exact hrkS
    have hnpos : 0 < s.ncard := (Set.ncard_pos (Set.toFinite s)).2 ⟨I₀, hI₀s⟩
    have hnle : s.ncard ≤ 2 := by
      have h : s.ncard * 8 ≤ 16 := by
        rw [← hrkW8]
        exact hrkWle
      omega
    have hOm : IsOmegaPlus ↥X 4 2 := by
      rw [hX]
      exact isOmegaPlus_sup_of_isAlt_five hcomm hdisj ha₁ ha₂
    have hn : s.ncard = 1 ∨ s.ncard = 2 := by omega
    rcases hn with hn1 | hn2
    · obtain ⟨J, hJ⟩ := Set.ncard_eq_one.mp hn1
      have hJI : J = I₀ := by
        have hJs : J ∈ s := by rw [hJ]; exact Set.mem_singleton J
        rw [hJ] at hI₀s
        exact (Set.mem_singleton_iff.mp hI₀s).symm
      have hJtop : J = ⊤ := by
        have hsupJ : sSup s = J := by rw [hJ, sSup_singleton]
        rw [hsupJ] at hssup
        exact hssup
      have hI₀top : I₀ = ⊤ := by
        rw [← hJI]
        exact hJtop
      have hNat : NatOmegaPlus X ⊤ ⊥ 4 2 := by
        simpa [hI₀top] using (hPairApply I₀ hI₀).2
      exact Or.inr (Or.inr ⟨hOm, hNat⟩)
    · have hWrk : rk ↥(⊤ : Subgroup W) = 2 * rk ↥I₀ := by
        rw [hrkS, hn2, (hPairApply I₀ hI₀).1]
      obtain ⟨J, hJ, hJI, hdisj', hsup'⟩ :=
        exists_second_summand_of_rank_two hW hI₀ (fun K hK => hK)
          (fun K _ => by rw [hfix, inf_bot_eq]) hSspan
          (fun K hK => by
            rw [(hPairApply K hK).1, (hPairApply I₀ hI₀).1])
          (by rw [(hPairApply I₀ hI₀).1]; norm_num) hWrk
      have hsum2 : SumOfNat (fun H U Z => NatOmegaPlus H U Z 4 2) X ⊤ ⊥ 2 :=
        s16c13bcA_sumOfNat_of_two (hPairApply I₀ hI₀).2 (hPairApply J hJ).2
          hdisj' hsup'
      exact Or.inr (Or.inl ⟨hsw, hOm, hsum2⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
