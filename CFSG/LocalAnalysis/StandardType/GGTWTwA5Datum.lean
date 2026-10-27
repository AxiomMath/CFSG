module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly
public import CFSG.LocalAnalysis.StandardType.GGTWRowData
public import CFSG.LocalAnalysis.StandardType.GGTWRowDataL
public import CFSG.LocalAnalysis.StandardType.GGResXDatumAHLK
public import CFSG.LocalAnalysis.StandardType.GGHLNbrInput
public import CFSG.LocalAnalysis.StandardType.GGTWRowGenDefs
public import CFSG.LocalAnalysis.StandardType.GGResXDatumARankFrom
public import CFSG.LocalAnalysis.StandardType.GGResXDatumAHLFrom
public import CFSG.LocalAnalysis.StandardType.GGTWTwA5Defs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrdD
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6Type9Basic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nQW_two_pow_fact_ne (n : ℕ) (hn : 2 ≤ n) : 2 ^ n * n.factorial ≠ 720 := by
  intro h
  by_cases hn5 : n ≤ 5
  · interval_cases n <;> norm_num at h
  · have hn6 : 6 ≤ n := by omega
    have hpow : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn6
    have hfac : Nat.factorial 6 ≤ n.factorial := Nat.factorial_le hn6
    have hbig : 2 ^ 6 * Nat.factorial 6 ≤ 2 ^ n * n.factorial := Nat.mul_le_mul hpow hfac
    norm_num at hbig
    omega

private theorem l05nQW_two_pow_pred_fact_ne (n : ℕ) (hn : 4 ≤ n) :
    2 ^ (n - 1) * n.factorial ≠ 720 := by
  intro h
  by_cases hn5 : n ≤ 5
  · interval_cases n <;> norm_num at h
  · have hn6 : 6 ≤ n := by omega
    have hpow : 2 ^ 5 ≤ 2 ^ (n - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hfac : Nat.factorial 6 ≤ n.factorial := Nat.factorial_le hn6
    have hbig : 2 ^ 5 * Nat.factorial 6 ≤ 2 ^ (n - 1) * n.factorial :=
      Nat.mul_le_mul hpow hfac
    norm_num at hbig
    omega

theorem l05nQW_ord_coxeterE6 :
    Nat.card (CoxeterMatrix.E₆).Group = 51840 := by
  have hmat : CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan CFSG.Blueprint.Chevalley.Tag.E6) =
      CoxeterMatrix.E₆ :=
    coxeterMatrix_eq_of_ggIntCartan
      (CFSG.LieType.Chevalley.isFiniteType_cartan CFSG.Blueprint.Chevalley.Tag.E6)
      (by
        rw [show CFSG.Blueprint.Chevalley.Tag.cartan CFSG.Blueprint.Chevalley.Tag.E6 =
            CartanMatrix.E 6 from CFSG.LieType.Chevalley.cartanE_eq 6]
        exact ggIntCartan_E₆)
  have hgroup : CFSG.LieType.Chevalley.WeylGroup CFSG.Blueprint.Chevalley.Tag.E6 =
      (CoxeterMatrix.E₆).Group := congrArg CoxeterMatrix.Group hmat
  have hcardW : Nat.card (CFSG.LieType.Chevalley.WeylGroup CFSG.Blueprint.Chevalley.Tag.E6) =
      Nat.card (CoxeterMatrix.E₆).Group := Nat.card_congr (Equiv.cast hgroup)
  rw [← hcardW]
  exact NoOffExc.card_weyl_E6

theorem l05nQW_ord_coxeterE7 :
    Nat.card (CoxeterMatrix.E₇).Group = 2903040 := by
  have hmat : CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan CFSG.Blueprint.Chevalley.Tag.E7) =
      CoxeterMatrix.E₇ :=
    coxeterMatrix_eq_of_ggIntCartan
      (CFSG.LieType.Chevalley.isFiniteType_cartan CFSG.Blueprint.Chevalley.Tag.E7)
      (by
        rw [show CFSG.Blueprint.Chevalley.Tag.cartan CFSG.Blueprint.Chevalley.Tag.E7 =
            CartanMatrix.E 7 from CFSG.LieType.Chevalley.cartanE_eq 7]
        exact ggIntCartan_E₇)
  have hgroup : CFSG.LieType.Chevalley.WeylGroup CFSG.Blueprint.Chevalley.Tag.E7 =
      (CoxeterMatrix.E₇).Group := congrArg CoxeterMatrix.Group hmat
  have hcardW : Nat.card (CFSG.LieType.Chevalley.WeylGroup CFSG.Blueprint.Chevalley.Tag.E7) =
      Nat.card (CoxeterMatrix.E₇).Group := Nat.card_congr (Equiv.cast hgroup)
  rw [← hcardW]
  exact NoOffExc.card_weyl_E7

theorem l05nQW_ord_coxeterE8 :
    Nat.card (CoxeterMatrix.E₈).Group = 696729600 := by
  have hmat : CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan CFSG.Blueprint.Chevalley.Tag.E8) =
      CoxeterMatrix.E₈ :=
    coxeterMatrix_eq_of_ggIntCartan
      (CFSG.LieType.Chevalley.isFiniteType_cartan CFSG.Blueprint.Chevalley.Tag.E8)
      (by
        rw [show CFSG.Blueprint.Chevalley.Tag.cartan CFSG.Blueprint.Chevalley.Tag.E8 =
            CartanMatrix.E 8 from CFSG.LieType.Chevalley.cartanE_eq 8]
        exact ggIntCartan_E₈)
  have hgroup : CFSG.LieType.Chevalley.WeylGroup CFSG.Blueprint.Chevalley.Tag.E8 =
      (CoxeterMatrix.E₈).Group := congrArg CoxeterMatrix.Group hmat
  have hcardW : Nat.card (CFSG.LieType.Chevalley.WeylGroup CFSG.Blueprint.Chevalley.Tag.E8) =
      Nat.card (CoxeterMatrix.E₈).Group := Nat.card_congr (Equiv.cast hgroup)
  rw [← hcardW]
  exact NoOffExc.card_weyl_E8

private theorem l05nQW_res (p : ℕ) (hp : p = 3) {labX : LargeEvenLabel}
    (htw : labX.tag = .twA ∧ labX.rank = 5 ∧ 3 ∣ 2 ^ labX.n + 1) :
    GGTBWeylRowRes p labX := by
  obtain ⟨htag, hrank, hdvd⟩ := htw
  refine ⟨?_, Or.inl (Or.inr (Or.inl ⟨?_, ?_, ?_⟩)), ?_, ?_, ?_⟩
  · rintro ⟨r, m, N, C, M, hrow⟩
    cases hrow with
    | aDep h1 h2 h3 h4 h5 => exact h5 ⟨hp, hrank, by rw [hp]; exact hdvd⟩
    | aInd h1 h2 h3 => exact h2 (by rw [hrank, hp]; norm_num)
    | e6Three h1 h2 h3 => rw [htag] at h1; exact absurd h1 (by decide)
    | e8Three h1 h2 => rw [htag] at h1; exact absurd h1 (by decide)
    | c h1 h2 => rcases h1 with h | h <;> rw [htag] at h <;> exact absurd h (by decide)
    | d h1 => rcases h1 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [htag] at h <;> exact absurd h (by decide)
    | e6Ind h1 h2 h3 => exact h1 hp
    | e7 h1 h2 => rw [htag] at h1; exact absurd h1 (by decide)
    | e8Ind h1 h2 h3 => exact h1 hp
    | f4 h1 h2 h3 => rw [htag] at h1; exact absurd h1 (by decide)
    | g2 h1 h2 => rw [htag] at h1; exact absurd h1 (by decide)
    | relD h1 =>
      rcases h1 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [htag] at h <;> exact absurd h (by decide)
    | relE6 h1 h2 => exact h1 hp
    | relA5 h1 h2 =>
      rcases h2 with ⟨h, -⟩ | ⟨-, h'⟩
      · rw [htag] at h; exact absurd h (by decide)
      · exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.not_three_dvd_two_pow_sub_one hdvd (hp ▸ h')
  · rw [htag]; simp [LargeEvenUntwisted]
  · rw [htag]; decide
  · rw [hp]; exact hdvd
  · rintro ⟨hp7, -⟩; omega
  · rw [htag]; decide
  · rw [htag]; decide

private theorem l05nQW_innerDiagOnLabel (hRig : GGLabelRigidInput) {G : Type} [Group G]
    {p : ℕ} {Bs X : Subgroup G} (hInner : GGInnerDiagOn Bs X) {labX : LargeEvenLabel}
    (hXΛ : LargeEvenInLambda2 labX) (hXl : GGHasLabel labX (↥X ⧸ Subgroup.center ↥X))
    (hres : GGTBWeylRowRes p labX) :
    GGInnerDiagOnLabel GGTBWeylRowRes p Bs X := by
  unfold GGInnerDiagOnLabel
  refine largeEvenMarking_mono ?_ (ggInnerDiagOn_relabel hRig hInner hXΛ hXl)
  intro lab R _ I _ θ hP
  exact ⟨by rw [hP.1]; exact hres, hP.2⟩

theorem l05nQW_A5_of_weyl
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G} {Λ : Type}
    (M : CoxeterMatrix Λ) (hM : GGIsWeylMatrix M)
    (hW : GGWeylOfType p M (ggAutomizer X Bs))
    (hcard : Nat.card ↥(ggAutomizer X Bs) = 720) :
    ∃ e : Fin 5 ≃ Λ, M = (CoxeterMatrix.A 5).reindex e := by
  have hcardM : Nat.card M.Group = 720 := by
    obtain ⟨f, -⟩ := hW
    rw [Nat.card_congr f.toEquiv, hcard]
  rcases hM with ⟨n, e, hn, hAd⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ | ⟨e, hF4⟩ | ⟨e, hG2⟩
  · rcases hAd with hA | ⟨hn2, hB⟩ | ⟨hn4, hD⟩
    · have hWA : GGWeylOfType p (CoxeterMatrix.A n) (ggAutomizer X Bs) :=
        GGWeylOfType.of_reindex (M := CoxeterMatrix.A n) (e := e) (hA ▸ hW)
      have hfac : (n + 1).factorial = Nat.factorial 6 := by
        rw [← ggWeylOfType_A_card hWA, hcard]; norm_num
      have hn5 : n = 5 := by
        have h6 : n + 1 = 6 := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have hlt' : (n + 1).factorial < Nat.factorial 6 :=
              (Nat.factorial_lt (Nat.succ_pos n)).mpr hlt
            omega
          · have hgt' : Nat.factorial 6 < (n + 1).factorial :=
              (Nat.factorial_lt (by norm_num : 0 < 6)).mpr hgt
            omega
        omega
      subst hn5
      exact ⟨e, hA⟩
    · have hWB : GGWeylOfType p (CoxeterMatrix.B n) (ggAutomizer X Bs) :=
        GGWeylOfType.of_reindex (M := CoxeterMatrix.B n) (e := e) (hB ▸ hW)
      have h12 := OrthF3.card_of_nonSimplyLaced (Or.inl ⟨n, hn2, hWB⟩)
      rw [hcard] at h12
      rcases h12 with h | h | ⟨k, hk, h⟩
      · norm_num at h
      · norm_num at h
      · exact absurd h.symm (l05nQW_two_pow_fact_ne k hk)
    · have hDcard : Nat.card (ggCoxeterMatrixD n).Group = 720 := by
        have h1 : Nat.card M.Group = Nat.card (ggCoxeterMatrixD n).Group := by
          rw [hD]
          exact Nat.card_congr ((ggCoxeterMatrixD n).reindexGroupEquiv e).toEquiv
        rw [← h1]; exact hcardM
      rw [OrthF3.card_coxeterD_eq n hn4] at hDcard
      exact absurd hDcard (l05nQW_two_pow_pred_fact_ne n hn4)
  · have hE6card : Nat.card (CoxeterMatrix.E₆).Group = 720 := by
      have h1 : Nat.card M.Group = Nat.card (CoxeterMatrix.E₆).Group := by
        rw [hE6]
        exact Nat.card_congr (CoxeterMatrix.E₆.reindexGroupEquiv e).toEquiv
      rw [← h1]; exact hcardM
    rw [l05nQW_ord_coxeterE6] at hE6card
    norm_num at hE6card
  · have hE7card : Nat.card (CoxeterMatrix.E₇).Group = 720 := by
      have h1 : Nat.card M.Group = Nat.card (CoxeterMatrix.E₇).Group := by
        rw [hE7]
        exact Nat.card_congr (CoxeterMatrix.E₇.reindexGroupEquiv e).toEquiv
      rw [← h1]; exact hcardM
    rw [l05nQW_ord_coxeterE7] at hE7card
    norm_num at hE7card
  · have hE8card : Nat.card (CoxeterMatrix.E₈).Group = 720 := by
      have h1 : Nat.card M.Group = Nat.card (CoxeterMatrix.E₈).Group := by
        rw [hE8]
        exact Nat.card_congr (CoxeterMatrix.E₈.reindexGroupEquiv e).toEquiv
      rw [← h1]; exact hcardM
    rw [l05nQW_ord_coxeterE8] at hE8card
    norm_num at hE8card
  · have hWF4 : GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizer X Bs) :=
      GGWeylOfType.of_reindex (M := CoxeterMatrix.F₄) (e := e) (hF4 ▸ hW)
    have h12 := OrthF3.card_of_nonSimplyLaced (Or.inr (Or.inl hWF4))
    rw [hcard] at h12
    rcases h12 with h | h | ⟨k, hk, h⟩
    · norm_num at h
    · norm_num at h
    · exact absurd h.symm (l05nQW_two_pow_fact_ne k hk)
  · have hWG2 : GGWeylOfType p CoxeterMatrix.G₂ (ggAutomizer X Bs) :=
      GGWeylOfType.of_reindex (M := CoxeterMatrix.G₂) (e := e) (hG2 ▸ hW)
    have h12 := OrthF3.card_of_nonSimplyLaced (Or.inr (Or.inr hWG2))
    rw [hcard] at h12
    rcases h12 with h | h | ⟨k, hk, h⟩
    · norm_num at h
    · norm_num at h
    · exact absurd h.symm (l05nQW_two_pow_fact_ne k hk)

private theorem l05nQW_resXDatumA_of_datum
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (hiso : Nonempty (↥(ggAutomizer X Bs) ≃* Equiv.Perm (Fin 6)))
    (hdat : GGResXDatum p Bs X) : GGResXDatumA p Bs X 5 := by
  obtain ⟨iso⟩ := hiso
  have hcard : Nat.card ↥(ggAutomizer X Bs) = 720 := by
    rw [Nat.card_congr iso.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin]
    norm_num
  obtain ⟨Λ, iF, iD, M, C, V, iVadd, iVmod, ι, φ, h, α, hMw, hMC, hlin, hrefl, hpair,
    hIso, hgen⟩ := hdat
  obtain ⟨f, hf⟩ := hIso
  have hW : GGWeylOfType p M (ggAutomizer X Bs) :=
    ⟨f, fun i => by rw [hf i]; exact hrefl i⟩
  obtain ⟨e, he⟩ := l05nQW_A5_of_weyl M hMw hW hcard
  exact ⟨Λ, iF, iD, M, C, V, iVadd, iVmod, ι, φ, h, α, e, he, hMw, hMC, hlin, hrefl, hpair,
    ⟨f, hf⟩, hgen⟩

theorem ggTWTwA5_datum
    (hRig : GGLabelRigidInput) (hR : GGTBXDatumResInput) (hO : GGTWTwA5Open)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {X : Subgroup G} {z : G} (hX : (X = L ∧ z = x) ∨ (X = K ∧ z = y)) (hp : p = 3)
    {labX : LargeEvenLabel} (hXΛ : LargeEvenInLambda2 labX)
    (hXl : GGHasLabel labX (↥X ⧸ Subgroup.center ↥X))
    (htw : labX.tag = .twA ∧ labX.rank = 5 ∧ 3 ∣ 2 ^ labX.n + 1) :
    GGResXDatumA p Bs X 5 ∧ ((X = L ∧ z = x) → GGTWHLAt p Bs X z) ∧
      ((X = K ∧ z = y) → y ∉ K → Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y →
        GGTWHLAt p Bs X z) := by
  have hres : GGTBWeylRowRes p labX := l05nQW_res p hp htw
  have hiso := hO G p B Bs x L D J y K hH X z hX hp labX hXΛ hXl htw
  have hdat : GGResXDatum p Bs X := by
    rcases hX with ⟨hXL, hzx⟩ | ⟨hXK, hzy⟩
    · subst X
      subst z
      exact (hR G p B Bs x L D J y K hH).1
        (l05nQW_innerDiagOnLabel hRig hH.2.2.1.1 hXΛ hXl hres)
    · subst X
      subst z
      exact (hR G p B Bs x L D J y K hH).2
        (l05nQW_innerDiagOnLabel hRig (hH.2.2.1.2 y K hH.2.2.2.2.1) hXΛ hXl hres)
  exact ⟨l05nQW_resXDatumA_of_datum hiso.1 hdat, hiso.2.1, hiso.2.2⟩

end CFSG.StandardType

end
