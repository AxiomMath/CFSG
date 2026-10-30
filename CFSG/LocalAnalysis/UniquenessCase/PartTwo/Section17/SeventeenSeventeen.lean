module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ModuleBridges
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyEight
public import CFSG.LocalAnalysis.UniquenessCase.UC6C636a
public import CFSG.GroupTheory.SteinbergCBFTSCN

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Open CFSG.Quasithin
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]


theorem not_isSpor_He_of_isSpor_J2 :
    ∀ (X : Type) [Group X], IsSpor X .He → IsSpor X .J2 → False := by
  intro X _ hHe hJ2
  obtain ⟨eHe⟩ := hHe
  obtain ⟨eJ2⟩ := hJ2
  have h1 : Nat.card X = 4030387200 := by
    rw [Nat.card_congr eHe.toEquiv]
    exact CFSG.Sporadic.He.card_He
  have h2 : Nat.card X = 604800 := by
    rw [Nat.card_congr eJ2.toEquiv]
    exact CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2
  omega

private theorem exists_mem_gam_two_not_le_centralizer {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) (hV0 : V₀ = ⊥)
    (hCi : ¬ centralizer (F12.Ci 2 D.T V : Set G) ≤ D.M) :
    ∃ A ∈ F12.Gam 2 D.T V, ¬ A ≤ centralizer (V : Set G) := by
  classical
  by_contra hall
  push Not at hall
  have hWi : F12.Wi 2 D.T V ≤ centralizer (V : Set G) := by
    unfold F12.Wi
    exact iSup₂_le hall
  have hVleCi : V ≤ F12.Ci 2 D.T V := by
    rw [F12.Ci]
    refine le_inf (TwelveTwentyTwo.le_T_of_hyp125 h) ?_
    intro v hv w hw
    exact (Subgroup.mem_centralizer_iff.1 (hWi hw) v hv).symm
  exact hCi ((Subgroup.centralizer_le hVleCi).trans
    (centralizer_le_of_inCalV D (hyp123_inCalV h.1)))





private theorem not_le_conjSubgroup_of_mem_gam {D : Data G} {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hV0 : V₀ = ⊥)
    (h27 : F12.Wi 0 D.T V ≤ F11.CTilde D.M V₀ V ∧
      normalizer ((F12.Wi 0 D.T V : Subgroup G) : Set G) ≤ D.M)
    {A : Subgroup G} (hA : A ∈ F12.Gam 2 D.T V)
    (hAne : ¬ A ≤ Subgroup.centralizer (V : Set G)) {g : G}
    (hAg : A ≤ conjSubgroup V g) :
    ¬ V ≤ conjSubgroup D.M g := by
  classical
  intro hVMg
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVginvM : conjSubgroup V g⁻¹ ≤ D.M :=
    (CFSG.Quasithin.E3.conjSubgroup_le_iff_le_inv (A := V) (B := D.M) g⁻¹).2
      (by simpa using hVMg)
  have hVginvP : IsPGroup 2 (conjSubgroup V g⁻¹) :=
    (CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian h.pairFacts.elemAbelian).map _
  have hsyl : CFSG.Quasithin.IsSylowIn 2 D.T D.M := by
    refine ⟨D.sylowM.le, D.sylowM.isPGroup, ?_⟩
    exact (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM).2.2
  obtain ⟨m, hmM, hmle⟩ :=
    CFSG.Quasithin.E3.exists_le_conj_of_isSylowIn hsyl hVginvM hVginvP
  have hconj : conjSubgroup V (g⁻¹ * m⁻¹) ≤ D.T := by
    have h := CFSG.Quasithin.E3.conjSubgroup_mono_left m⁻¹ hmle
    rwa [CFSG.Quasithin.conjSubgroup_conjSubgroup,
      CFSG.Quasithin.E3.conjSubgroup_conj_inv] at h
  have hmem : conjSubgroup V (g⁻¹ * m⁻¹) ∈ F12.Gam 0 D.T V := by
    refine ⟨hconj, V, (g⁻¹ * m⁻¹)⁻¹, le_rfl, ?_, ?_⟩
    · rw [pow_zero, one_mul]
    · rfl
  have hW0 : conjSubgroup V (g⁻¹ * m⁻¹) ≤ F12.Wi 0 D.T V := by
    unfold F12.Wi
    exact le_iSup₂_of_le _ hmem le_rfl
  have hCT : F11.CTilde D.M V₀ V = D.M ⊓ Subgroup.centralizer (V : Set G) := by
    rw [hV0]
    exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22u_cTilde_bot D.M V
  have hleC : conjSubgroup V (g⁻¹ * m⁻¹) ≤ Subgroup.centralizer (V : Set G) :=
    (hW0.trans (h27.1.trans (le_of_eq hCT))).trans inf_le_right
  have hMnormC : D.M ≤ Subgroup.normalizer
      (Subgroup.centralizer (V : Set G) : Set G) :=
    CFSG.GroupTheory.FT63ChII.le_normalizer_centralizer h.pairFacts.le_normalizer
  have hCinv : conjSubgroup V g⁻¹ ≤ Subgroup.centralizer (V : Set G) := by

    have h1 := CFSG.Quasithin.E3.conjSubgroup_mono_left m hleC
    have hCm : conjSubgroup (Subgroup.centralizer (V : Set G)) m =
        Subgroup.centralizer (V : Set G) :=
      conjSubgroup_eq_iff_mem_normalizer.2 (hMnormC hmM)
    rw [hCm] at h1
    have heq : (g⁻¹ * m⁻¹) * m = g⁻¹ := by group
    simpa [CFSG.Quasithin.conjSubgroup_conjSubgroup, heq] using h1
  have hVleC : V ≤ Subgroup.centralizer (conjSubgroup V g : Set G) := by
    have h := CFSG.Quasithin.E3.conjSubgroup_mono_left g hCinv
    simpa only [CFSG.Quasithin.conjSubgroup_conjSubgroup, inv_mul_cancel,
      conjSubgroup_one, CFSG.Quasithin.E3.conjSubgroup_centralizer] using h
  refine hAne (hAg.trans ?_)
  intro a ha
  refine Subgroup.mem_centralizer_iff.2 ?_
  intro v hv
  exact (Subgroup.mem_centralizer_iff.1 (hVleC hv) a ha).symm


private theorem mQuot_sup_zpowers_lt {A B : Subgroup G} {a : G}
    (hA2 : IsPGroup 2 A) (hBA : B ≤ A) (haA : a ∈ A) (haB : a ∉ B)
    {n : ℕ} (hm : E3.mQuot A B = n + 1) :
    E3.mQuot A (B ⊔ Subgroup.zpowers a) ≤ n := by
  have hB'le : B ⊔ Subgroup.zpowers a ≤ A :=
    sup_le hBA (Subgroup.zpowers_le.2 haA)
  have hadd := E3.mQuot_add (V := A) (U := B) (U' := B ⊔ Subgroup.zpowers a)
    le_sup_left hB'le
  have hne : E3.mQuot (B ⊔ Subgroup.zpowers a) B ≠ 0 := by
    intro h0
    rw [E3.mQuot_eq_zero_iff (hA2.to_le hB'le) le_sup_left] at h0
    exact haB (h0 ▸ (le_sup_right : Subgroup.zpowers a ≤ B ⊔ Subgroup.zpowers a)
      (Subgroup.mem_zpowers a))
  omega

private theorem four_le_mQuot_of_mem_gam {D : Data G} {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hV0 : V₀ = ⊥)
    (h27 : F12.Wi 0 D.T V ≤ F11.CTilde D.M V₀ V ∧
      normalizer ((F12.Wi 0 D.T V : Subgroup G) : Set G) ≤ D.M)
    (h30 : (6 : ℕ∞) ≤ rMV D.M V)
    {A : Subgroup G} (hA : A ∈ F12.Gam 2 D.T V)
    (hAne : ¬ A ≤ Subgroup.centralizer (V : Set G)) {g : G}
    (hAg : A ≤ conjSubgroup V g) (hmA : E3.mQuot (conjSubgroup V g) A = 2) :
    4 ≤ E3.mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) := by
  classical
  set B : Subgroup G := A ⊓ Subgroup.centralizer (V : Set G) with hBdef
  have hBA : B ≤ A := inf_le_left
  have hBVg : B ≤ conjSubgroup V g := hBA.trans hAg
  have hA2 : IsPGroup 2 A :=
    CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian
      ((CFSG.Open.IsElemAbelian.mono (E3.isElemAbelian_conjSubgroup h.pairFacts.elemAbelian g)) hAg)
  by_contra hlt
  push Not at hlt
  have hmB : E3.mQuot (conjSubgroup V g) B ≤ 5 := by
    have hadd := E3.mQuot_add (V := conjSubgroup V g) (U := B) (U' := A) hBA hAg
    rw [hmA] at hadd
    omega
  have hCB : Subgroup.centralizer (B : Set G) ≤ conjSubgroup D.M g := by
    by_contra hnot
    have hr : rMV (conjSubgroup D.M g) (conjSubgroup V g) = rMV D.M V :=
      CFSG.LocalAnalysis.WeakClosure81.rMV_conj (by rw [normalizer_eq_of_inCalV D (hyp123_inCalV h.1)]) g
    have h6 : (6 : ℕ∞) ≤ rMV (conjSubgroup D.M g) (conjSubgroup V g) := by
      rw [hr]; exact h30
    have hle : rMV (conjSubgroup D.M g) (conjSubgroup V g) ≤
        (E3.mQuot (conjSubgroup V g) B : ℕ∞) := by
      unfold rMV
      exact iInf₂_le B ⟨hBVg, hnot⟩
    have h6' : 6 ≤ E3.mQuot (conjSubgroup V g) B := Nat.cast_le.mp (h6.trans hle)
    omega
  have hVleCB : V ≤ Subgroup.centralizer (B : Set G) := by
    intro v hv
    refine Subgroup.mem_centralizer_iff.2 ?_
    intro b hb
    exact (Subgroup.mem_centralizer_iff.1 hb.2 v hv).symm
  exact (not_le_conjSubgroup_of_mem_gam h hV0 h27 hA hAne hAg)
    (hVleCB.trans hCB)



private theorem gammaOne_le_conj_of_mem_gam {D : Data G} {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hV0 : V₀ = ⊥)
    (h30 : (6 : ℕ∞) ≤ rMV D.M V)
    {A : Subgroup G} (hA : A ∈ F12.Gam 2 D.T V)
    (hAne : ¬ A ≤ Subgroup.centralizer (V : Set G)) {g : G}
    (hAg : A ≤ conjSubgroup V g) (hmA : E3.mQuot (conjSubgroup V g) A = 2)
    (hmAB : E3.mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) = 4) :
    gammaOneABarB D V₀ V A ≤ conjSubgroup D.M g := by
  classical
  set B : Subgroup G := A ⊓ Subgroup.centralizer (V : Set G) with hBdef
  have hBA : B ≤ A := inf_le_left
  have hA2 : IsPGroup 2 A :=
    CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian
      ((CFSG.Open.IsElemAbelian.mono (E3.isElemAbelian_conjSubgroup h.pairFacts.elemAbelian g)) hAg)
  have hCT : F11.CTilde D.M V₀ V = D.M ⊓ Subgroup.centralizer (V : Set G) := by
    rw [hV0]
    exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22u_cTilde_bot D.M V
  have hmVgB' : ∀ {a : G}, a ∈ A → a ∉ Subgroup.centralizer (V : Set G) →
      E3.mQuot (conjSubgroup V g) (B ⊔ Subgroup.zpowers a) ≤ 5 := by
    intro a haA haC
    have haB : a ∉ B := fun hmem => haC (Subgroup.mem_inf.1 hmem).2
    have hm' : E3.mQuot A B = 3 + 1 := by omega
    have hle3 := mQuot_sup_zpowers_lt hA2 hBA haA haB hm'
    have hB'le : B ⊔ Subgroup.zpowers a ≤ A :=
      sup_le hBA (Subgroup.zpowers_le.2 haA)
    have hadd := E3.mQuot_add (V := conjSubgroup V g) (U := B ⊔ Subgroup.zpowers a)
      (U' := A) hB'le hAg
    rw [hmA] at hadd
    omega
  have hCB' : ∀ {a : G}, a ∈ A → a ∉ Subgroup.centralizer (V : Set G) →
      Subgroup.centralizer ((B ⊔ Subgroup.zpowers a : Subgroup G) : Set G) ≤
        conjSubgroup D.M g := by
    intro a haA haC
    have hB'le : B ⊔ Subgroup.zpowers a ≤ A :=
      sup_le hBA (Subgroup.zpowers_le.2 haA)
    have hB'Vg : B ⊔ Subgroup.zpowers a ≤ conjSubgroup V g := hB'le.trans hAg
    have hm' := hmVgB' haA haC
    by_contra hnot
    have hr : rMV (conjSubgroup D.M g) (conjSubgroup V g) = rMV D.M V :=
      CFSG.LocalAnalysis.WeakClosure81.rMV_conj (by rw [normalizer_eq_of_inCalV D (hyp123_inCalV h.1)]) g
    have h6 : (6 : ℕ∞) ≤ rMV (conjSubgroup D.M g) (conjSubgroup V g) := by
      rw [hr]; exact h30
    have hle : rMV (conjSubgroup D.M g) (conjSubgroup V g) ≤
        (E3.mQuot (conjSubgroup V g) (B ⊔ Subgroup.zpowers a) : ℕ∞) := by
      unfold rMV
      exact iInf₂_le (B ⊔ Subgroup.zpowers a) ⟨hB'Vg, hnot⟩
    have h6' : 6 ≤ E3.mQuot (conjSubgroup V g) (B ⊔ Subgroup.zpowers a) :=
      Nat.cast_le.mp (h6.trans hle)
    omega
  unfold gammaOneABarB
  refine iSup₂_le fun a haA => ?_
  by_cases haC : a ∈ F11.CTilde D.M V₀ V
  ·
    have : ¬ a ∉ F11.CTilde D.M V₀ V := not_not.2 haC
    rw [iSup_neg this]
    exact bot_le
  · refine (iSup_le fun _ => ?_)
    have haM : a ∈ D.M := D.sylowM.le (hA.1 haA)
    have haC' : a ∉ Subgroup.centralizer (V : Set G) := by
      intro hmem
      exact haC (by rw [hCT]; exact ⟨haM, hmem⟩)
    refine (le_trans ?_ (hCB' haA haC'))
    intro v hv
    obtain ⟨hvV, hva⟩ := Subgroup.mem_inf.1 hv
    have hBC : B ≤ Subgroup.centralizer ({(v : G)} : Set G) := by
      intro b hb
      refine Subgroup.mem_centralizer_iff.2 ?_
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst v
      exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hb).2 h hvV)
    have haC : Subgroup.zpowers a ≤ Subgroup.centralizer ({(v : G)} : Set G) := by
      intro x hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← hk]
      refine Subgroup.mem_centralizer_iff.2 ?_
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst v
      have hcomm : Commute a h := Subgroup.mem_centralizer_iff.1 hva a rfl
      exact (hcomm.zpow_left k).eq.symm
    have hB'C : B ⊔ Subgroup.zpowers a ≤ Subgroup.centralizer ({(v : G)} : Set G) :=
      sup_le hBC haC
    refine Subgroup.mem_centralizer_iff.2 ?_
    intro b hb
    exact (Subgroup.mem_centralizer_iff.1 (hB'C hb) v rfl).symm





theorem exists_order_five_centralizer {D : Data G} {V₀ V L : Subgroup G}
    (c : Ctx17_17 D V₀ V L) (h17_26b_1 : R17_26b_1At D V₀ V)
    (h17_28 : R17_28At D V₀ V) :
    ∃ x : G, x ∈ D.M ∧ x ∈ Subgroup.centralizer (V : Set G) ∧
      orderOf x = 5 ∧ x ≠ 1 := by
  have hV := c.hyp125
  obtain ⟨hV0, -⟩ := h17_28 L c
  have hVne : V ≠ ⊥ := hV.pairFacts.ne_bot
  obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hVne
  have hvV : (v : G) ∈ V := v.2
  have hv1' : (v : G) ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hvV₀ : (v : G) ∉ V₀ := by rw [hV0]; exact fun h => hv1' (Subgroup.mem_bot.1 h)
  have h26 := h17_26b_1 L c v hv1' hvV₀
  have h26le : ((D.M ⊓ Subgroup.centralizer ({(v : G)} : Set G)) ⊓
      F11.CTilde D.M V₀ V : Subgroup G) ≤
      D.M ⊓ Subgroup.centralizer (V : Set G) := by
    refine le_inf (inf_le_left.trans inf_le_left) ?_
    intro x hx
    have hxCT : x ∈ F11.CTilde D.M V₀ V := hx.2
    rw [hV0, CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22u_cTilde_bot] at hxCT
    exact (Subgroup.mem_inf.1 hxCT).2
  have hEq : CFSG.Open.pRank 5
      ((D.M ⊓ Subgroup.centralizer ({(v : G)} : Set G)) ⊓ F11.CTilde D.M V₀ V) =
      CFSG.pRank 5 ↥((D.M ⊓ Subgroup.centralizer ({(v : G)} : Set G)) ⊓
        F11.CTilde D.M V₀ V) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup
        ((D.M ⊓ Subgroup.centralizer ({(v : G)} : Set G)) ⊓ F11.CTilde D.M V₀ V),
      ← CFSG.SectionRank.pRank_eq_open_pRank_top (p := 5)
        (H := ↥((D.M ⊓ Subgroup.centralizer ({(v : G)} : Set G)) ⊓ F11.CTilde D.M V₀ V))]
  have h1 : 1 ≤ CFSG.Open.pRank 5
      ((D.M ⊓ Subgroup.centralizer ({(v : G)} : Set G)) ⊓ F11.CTilde D.M V₀ V) := by
    rw [hEq]
    rw [show CFSG.pRank 5 ↥((D.M ⊓ Subgroup.centralizer ({(v : G)} : Set G)) ⊓
      F11.CTilde D.M V₀ V) = 1 from h26]
  obtain ⟨E, hEH, hEel, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 5) (k := 1) h1
  have hE5 : Nat.card E = 5 := by simpa using hEcard
  have hEne : E ≠ ⊥ := by
    intro hbot
    rw [hbot] at hE5
    simp at hE5
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hEne
  have hxE : (x : G) ∈ E := x.2
  have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxH : (x : G) ∈ (D.M ⊓ Subgroup.centralizer ({(v : G)} : Set G)) ⊓
      F11.CTilde D.M V₀ V := hEH hxE
  have hxM : (x : G) ∈ D.M := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hxH).1).1
  have hxCT : (x : G) ∈ F11.CTilde D.M V₀ V := (Subgroup.mem_inf.1 hxH).2
  have hxCV : (x : G) ∈ Subgroup.centralizer (V : Set G) := by
    rw [hV0, CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22u_cTilde_bot] at hxCT
    exact (Subgroup.mem_inf.1 hxCT).2
  have hxord : orderOf (x : G) = 5 := by
    have hdvd : orderOf (x : G) ∣ 5 :=
      orderOf_dvd_of_pow_eq_one (hEel.2 (x : G) hxE)
    have hne : orderOf (x : G) ≠ 1 := by
      simpa [orderOf_eq_one_iff] using hx1'
    exact (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_five (orderOf (x : G)) hdvd).resolve_left hne
  exact ⟨x, hxM, hxCV, hxord, hx1'⟩

private theorem final_conjugation_step {D : Data G} {V₀ V L A : Subgroup G} {g x : G}
    {v₁ v₂ : V} (c : Ctx17_17 D V₀ V L)
    (hsp5 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 D.M)
    (hVg : ¬ V ≤ conjSubgroup D.M g) (hVM : V ≤ D.M)
    (hxCV : x ∈ Subgroup.centralizer (V : Set G)) (hxM : x ∈ D.M)
    (hxord : orderOf x = 5)
    (hcomm : ⁅gammaOneABarB D V₀ V A, A⁆ ≤ conjSubgroup V g)
    (h17_29_3 : R17_29_3At D V₀ V) (h29ctx : Ctx17_29 D V₀ V L)
    (hP : P17_29_1 D V₀ V L c.hyp125.isElemAbelian v₁ v₂)
    (hCv₂ : Subgroup.centralizer ({(v₂ : G)} : Set G) ≤ D.M)
    (hAT : A ≤ D.T)
    (hE16 : IsElemAbelian2 (barSub V₀ V c.hyp125.isElemAbelian A))
    (hcardA : Nat.card ↥(barSub V₀ V c.hyp125.isElemAbelian A) = 16)
    (hbarT : barSub V₀ V c.hyp125.isElemAbelian A ≤
      barSub V₀ V c.hyp125.isElemAbelian D.T) : False := by
  obtain ⟨l, hlL, w, hw, hwcomm⟩ := h17_29_3 L h29ctx v₂ ⟨v₁, hP⟩ A
    (hAT.trans D.sylowM.le) hE16 hcardA hbarT
  have hwVg : (w : G) ∈ conjSubgroup V g := hcomm hwcomm
  have hCw : Subgroup.centralizer ({(w : G)} : Set G) ≤ D.M := by
    have hwconj : (w : G) = l * (v₂ : G) * l⁻¹ := hw
    have hLleM : L ≤ D.M := CFSG.Open.IsSubnormal.le c.mem_calC.1
    have hlM : l ∈ D.M := hLleM hlL
    have hcent : Subgroup.centralizer ({(w : G)} : Set G) =
        conjSubgroup (Subgroup.centralizer ({(v₂ : G)} : Set G)) l⁻¹ := by
      rw [hwconj]
      have h := (CFSG.LocalAnalysis.WeakClosure81.conjSubgroup_centralizer_singleton (v₂ : G) l⁻¹).symm
      simpa [inv_inv] using h
    rw [hcent]
    refine (CFSG.Quasithin.E3.conjSubgroup_mono_left l⁻¹ hCv₂).trans ?_
    rw [conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer (D.M.inv_mem hlM))]
  have hx'C : g⁻¹ * (x : G) * g ∈ Subgroup.centralizer (conjSubgroup V g : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 ?_
    intro v' hv'
    have hvV : g * v' * g⁻¹ ∈ V := mem_conjSubgroup_iff.1 hv'
    have hv'eq : v' = g⁻¹ * (g * v' * g⁻¹) * g := by group
    rw [hv'eq]
    calc (g⁻¹ * (g * v' * g⁻¹) * g) * (g⁻¹ * (x : G) * g)
        = g⁻¹ * ((g * v' * g⁻¹) * (x : G)) * g := by group
      _ = g⁻¹ * ((x : G) * (g * v' * g⁻¹)) * g := by
        rw [Subgroup.mem_centralizer_iff.1 hxCV (g * v' * g⁻¹) hvV]
      _ = (g⁻¹ * (x : G) * g) * (g⁻¹ * (g * v' * g⁻¹) * g) := by group
  have hx'wC : g⁻¹ * (x : G) * g ∈ Subgroup.centralizer ({(w : G)} : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Subgroup.mem_centralizer_iff.1 hx'C (w : G) hwVg
  have hx'M : g⁻¹ * (x : G) * g ∈ D.M := hCw hx'wC
  have hx'Mg : g⁻¹ * (x : G) * g ∈ conjSubgroup D.M g := by
    rw [mem_conjSubgroup_iff]
    show g * (g⁻¹ * (x : G) * g) * g⁻¹ ∈ D.M
    rw [show g * (g⁻¹ * (x : G) * g) * g⁻¹ = (x : G) by group]
    exact hxM
  have hx'ord : orderOf (g⁻¹ * (x : G) * g) = 5 := by
    have hconj : IsConj (g⁻¹ * (x : G) * g) (x : G) :=
      isConj_iff.2 ⟨g, by group⟩
    rw [hconj.orderOf_eq]
    exact hxord
  have hdvd : 5 ∣ Nat.card ↥(D.M ⊓ conjSubgroup D.M g) := by
    have h := Subgroup.orderOf_dvd_natCard (D.M ⊓ conjSubgroup D.M g)
      (Subgroup.mem_inf.2 ⟨hx'M, hx'Mg⟩)
    rwa [hx'ord] at h
  have hgM : g ∉ D.M := by
    intro hg
    exact hVg (by
      rw [conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hg)]
      exact hVM)
  have hginvM : g⁻¹ ∉ D.M := fun h => hgM (by simpa using D.M.inv_mem h)
  exact hsp5.2.2 g⁻¹ hginvM hdvd


private theorem seventeen_seventeen_final_contradiction {D : Data G} {V₀ V L : Subgroup G}
    (c : Ctx17_17 D V₀ V L)
    (h17_22 : R17_22At D V₀ V) (h17_23 : R17_23At D V₀ V) (h17_25 : R17_25At D V₀ V)
    (h17_26b_1 : R17_26b_1At D V₀ V)
    (h17_27 : R17_27At D V₀ V) (h17_28 : R17_28At D V₀ V)
    (h17_29_1 : R17_29_1At D V₀ V) (h17_29_3 : R17_29_3At D V₀ V)
    (h17_30 : R17_30At D V₀ V)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    : False := by
  classical
  have hV := c.hyp125
  have hVel := hV.isElemAbelian
  obtain ⟨hV0, hCi⟩ := h17_28 L c
  have h5sig : 5 ∈ D.sig := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 L
    have h22 := h17_22 L P (centerOf P) c hP rfl
    rcases h22 with hHe | ⟨-, hsig5, -⟩
    · exact False.elim (not_isSpor_He_of_isSpor_J2 (Bar2 L) hHe (h17_23 L c))
    · rw [hsig5]; simp
  have hsp5 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 D.M :=
    hSg.sig1_sp 5 (by rw [← h1219]; exact h5sig)
  have h29ctx : Ctx17_29 D V₀ V L := ⟨c, hV0⟩
  obtain ⟨v₁, v₂, hP⟩ := h17_29_1 L h29ctx
  have hCv₂ : Subgroup.centralizer ({(v₂ : G)} : Set G) ≤ D.M := hP.2.2.2.2.2.2.2.2.2
  obtain ⟨x, hxM, hxCV, hxord, hx1'⟩ :=
    exists_order_five_centralizer c h17_26b_1 h17_28
  obtain ⟨A, hA, hAne⟩ := exists_mem_gam_two_not_le_centralizer hV hV0 hCi
  have hAgamma : A ∈ E3.gammaSet V 2 D.T := by
    rw [← gam_eq_gammaSet 2 D.T V hVel]
    exact hA
  obtain ⟨hAT, g, hAg, hmA⟩ := E3.mem_gammaSet_iff.1 hAgamma
  have hVg : ¬ V ≤ conjSubgroup D.M g :=
    not_le_conjSubgroup_of_mem_gam hV hV0 (h17_27 L c) hA hAne hAg
  have h30 : (6 : ℕ∞) ≤ rMV D.M V := h17_30 L h29ctx
  have h4 := four_le_mQuot_of_mem_gam hV hV0 (h17_27 L c) h30 hA hAne hAg hmA
  have hAM : A ≤ D.M := hAT.trans D.sylowM.le
  have hAel : IsElemAbelian 2 A :=
    CFSG.Open.IsElemAbelian.mono (E3.isElemAbelian_conjSubgroup hVel g) hAg
  have hLopp : L = Opp 3 D.M := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 L
    have h22 := h17_22 L P (centerOf P) c hP rfl
    rcases h22 with hHe | h
    · exact False.elim (not_isSpor_He_of_isSpor_J2 (Bar2 L) hHe (h17_23 L c))
    · exact h.2.2.2.1
  have hMN : D.M ≤ Subgroup.normalizer (L : Set G) := by
    rw [hLopp]
    intro m hm
    exact CFSG.LocalAnalysis.UniquenessCase.UC6.mem_normalizer_Opp_uc6
      ((Subgroup.le_normalizer : D.M ≤ Subgroup.normalizer (D.M : Set G)) hm) 3
  have hle4 : E3.mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) ≤ 4 :=
    mQuot_le_four_of_J2 hV c h17_25 h17_23 hV0 hMN hA hAel
  have hmAB : E3.mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) = 4 := by
    omega
  have hcardAbar : Nat.card ↥(barSub V₀ V hVel A) =
      (A ⊓ F11.CTilde D.M V₀ V).relIndex A :=
    CFSG.LocalAnalysis.WeakClosure81.card_barSub_eq_relIndex hVel
      hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀ hAM
  have hA2 : IsPGroup 2 ↥A := CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hAel
  have hrel : (A ⊓ F11.CTilde D.M V₀ V).relIndex A =
      2 ^ E3.mQuot A (A ⊓ F11.CTilde D.M V₀ V) :=
    CFSG.Quasithin.E3.relIndex_eq_two_pow hA2 (A ⊓ F11.CTilde D.M V₀ V)
  have hcardm : Nat.card ↥(barSub V₀ V hVel A) =
      2 ^ E3.mQuot A (A ⊓ F11.CTilde D.M V₀ V) := by
    rw [hcardAbar, hrel]
  have hE16 : IsElemAbelian2 (barSub V₀ V hVel A) :=
    isElemAbelian2_barSub hVel hAel
  have hbar2 : IsPGroup 2 ↥(barSub V₀ V hVel A) :=
    IsPGroup.of_card (n := E3.mQuot A (A ⊓ F11.CTilde D.M V₀ V)) hcardm
  have hcard2 : Nat.card ↥(barSub V₀ V hVel A) =
      2 ^ rk (barSub V₀ V hVel A) :=
    card_eq_two_pow_mSub hbar2
  have hrank : E3.mQuot A (A ⊓ F11.CTilde D.M V₀ V) =
      rk (barSub V₀ V hVel A) := by
    rw [hcard2] at hcardm
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 2) hcardm).symm
  have hCT : F11.CTilde D.M V₀ V = D.M ⊓ Subgroup.centralizer (V : Set G) := by
    rw [hV0]
    exact uc22p22u_cTilde_bot D.M V
  have hAB : A ⊓ F11.CTilde D.M V₀ V =
      A ⊓ Subgroup.centralizer (V : Set G) := by
    rw [hCT, ← inf_assoc, inf_eq_left.mpr hAM]
  rw [hAB] at hrank hcardm
  have hcardA : Nat.card ↥(barSub V₀ V hVel A) = 16 := by
    rw [hcardm, hmAB]
    norm_num
  have hbarT : barSub V₀ V hVel A ≤ barSub V₀ V hVel D.T :=
    barSub_mono V₀ V hVel hAT
  have hΓ : gammaOneABarB D V₀ V A ≤ conjSubgroup D.M g :=
    gammaOne_le_conj_of_mem_gam hV hV0 h30 hA hAne hAg hmA hmAB
  have hcomm : ⁅gammaOneABarB D V₀ V A, A⁆ ≤ conjSubgroup V g := by
    have hN : conjSubgroup D.M g = normalizer (conjSubgroup V g : Set G) := by
      rw [← normalizer_eq_of_inCalV D (hyp123_inCalV hV.1),
        CFSG.Quasithin.E3.conjSubgroup_normalizer]
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hxN : x ∈ normalizer (conjSubgroup V g : Set G) := by
      rw [← hN]; exact hΓ hx
    have hxy : x * y * x⁻¹ ∈ conjSubgroup V g :=
      (Subgroup.mem_normalizer_iff.1 hxN y).1 (hAg hy)
    have hyi : y⁻¹ ∈ conjSubgroup V g := (conjSubgroup V g).inv_mem (hAg hy)
    rw [commutatorElement_def]
    exact (conjSubgroup V g).mul_mem hxy hyi
  exact final_conjugation_step c hsp5 hVg hV.pairFacts.le_M hxCV hxM hxord hcomm
    h17_29_3 h29ctx hP hCv₂ hAT hE16 hcardA hbarT


private theorem ctx_of_not_concl {D : Data G} {V₀ V L : Subgroup G}
    (hV : Hyp125 D V₀ V) (hL : L ∈ calC D.M)
    (hsp : ∃ s : TauCeti.SporadicName, IsSpor (BarInf L) s)
    (hcon : ¬ Concl17_17 D V₀ V L)
    (h17_22 : R17_22At D V₀ V) (h17_23 : R17_23At D V₀ V) (h17_25 : R17_25At D V₀ V)
    (h17_26b_1 : R17_26b_1At D V₀ V)
    (h17_27 : R17_27At D V₀ V) (h17_28 : R17_28At D V₀ V)
    (h17_29_1 : R17_29_1At D V₀ V) (h17_29_3 : R17_29_3At D V₀ V)
    (h17_30 : R17_30At D V₀ V)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
: Ctx17_17 D V₀ V L := by
  refine ⟨hV, hL, hsp, hcon, ?_⟩
  intro hex
  by_cases hJ : IsJ1 (Bar2 L)
  · obtain ⟨K, hK, hspK, hJ1K, hconK⟩ := hex
    have hctxK : Ctx17_17 D V₀ V K :=
      ⟨hV, hK, hspK, hconK, fun _ => hJ1K⟩
    exact False.elim (seventeen_seventeen_final_contradiction hctxK h17_22 h17_23 h17_25 h17_26b_1 h17_27 h17_28
      h17_29_1 h17_29_3 h17_30 hSg h1219)
  · exact hJ

theorem seventeen_seventeen (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (h17_22 : R17_22At D V₀ V) (h17_23 : R17_23At D V₀ V) (h17_25 : R17_25At D V₀ V)
    (h17_26b_1 : R17_26b_1At D V₀ V)
    (h17_27 : R17_27At D V₀ V) (h17_28 : R17_28At D V₀ V)
    (h17_29_1 : R17_29_1At D V₀ V) (h17_29_3 : R17_29_3At D V₀ V)
    (h17_30 : R17_30At D V₀ V)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
: R17_17At D V₀ V := by
  intro L hL hsp
  by_contra hcon
  exact False.elim (seventeen_seventeen_final_contradiction
    (ctx_of_not_concl hV hL hsp hcon h17_22 h17_23 h17_25 h17_26b_1 h17_27 h17_28
      h17_29_1 h17_29_3 h17_30 hSg h1219)
    h17_22 h17_23 h17_25 h17_26b_1 h17_27 h17_28 h17_29_1 h17_29_3 h17_30 hSg h1219)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
