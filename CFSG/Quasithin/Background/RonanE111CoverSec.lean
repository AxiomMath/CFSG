module

public import CFSG.Quasithin.Background.RonanE111Sec
public import CFSG.Quasithin.Background.RonanE111Cov
public import CFSG.Quasithin.Background.A1bTransvection
public import CFSG.Quasithin.Background.RonanE111Cover

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E2.E22N
  CFSG.Quasithin.E2.E22N.E111R
open scoped commutatorElement

variable {G : Type} [Group G]

section Helpers

variable [Finite G]

theorem le_Cov_of_dimg {X T A J C : Subgroup G} [Fintype ↥C] (h : DiagSetting X T A J C)
    {U H₁ : Subgroup G} (hUJ : U ≤ J) (hU : dimg h.diagComm U ≤ H₁) : U ≤ Cov H₁ J := by
  intro x hx
  have hxJ : x ∈ J := hUJ hx
  refine ⟨Subgroup.le_normalizer hxJ, diagHom J C h.diagComm ⟨x, hxJ⟩, hU ?_,
    inv_mul_diagHom_mem h.diagComm ⟨x, hxJ⟩⟩
  exact (mem_dimg_iff h.diagComm).mpr ⟨⟨x, hxJ⟩, hx, rfl⟩

theorem Cov_mono {H₁ H₂ : Subgroup G} (J : Subgroup G) (h : H₁ ≤ H₂) : Cov H₁ J ≤ Cov H₂ J :=
  fun _ hg => ⟨hg.1, hg.2.choose, h hg.2.choose_spec.1, hg.2.choose_spec.2⟩

theorem le_of_le_sup_of_perfect {XM R YM : Subgroup G} (hXperf : ⁅XM, XM⁆ = XM)
    (hRX : ∀ x ∈ XM, ∀ r ∈ R, x * r * x⁻¹ ∈ R) (hRY : ∀ y ∈ YM, ∀ r ∈ R, y * r * y⁻¹ ∈ R)
    (hYs : Group.IsSolvable ↥YM) (hle : XM ≤ R ⊔ YM) : XM ≤ R := by
  have key : ∀ k, XM ≤ R ⊔ derivedSeriesOf YM k := by
    intro k
    induction k with
    | zero => simpa [derivedSeriesOf_zero] using hle
    | succ k ih =>
      set Yk := derivedSeriesOf YM k with hYk
      set Y' := R ⊔ derivedSeriesOf YM (k + 1) with hY'
      have hYkY : Yk ≤ YM := derivedSeriesOf_le YM k
      have hRY' : R ≤ Y' := le_sup_left
      have hD : derivedSeriesOf YM (k + 1) ≤ Y' := le_sup_right
      have hnorm : ∀ p ∈ Yk, ∀ y ∈ Y', p * y * p⁻¹ ∈ Y' := by
        intro p hp y hy
        refine conj_mem_sup_of (x := p) (fun c hc => ?_) (fun c hc => ?_) hy
        · exact Subgroup.mem_sup_left (hRY p (hYkY hp) c hc)
        · refine Subgroup.mem_sup_right ?_
          rw [derivedSeriesOf_succ]
          exact commutator_conj_mem_of_mem hp hc
      have hcomm : ∀ a ∈ Yk, ∀ b ∈ Yk, a * b * a⁻¹ * b⁻¹ ∈ Y' := by
        intro a ha b hb
        refine hD ?_
        rw [derivedSeriesOf_succ]
        have := Subgroup.commutator_mem_commutator ha hb
        simpa [commutatorElement_def] using this
      have hcom := wr_commutator_sup_le (Y := Y') (P₁ := Yk) (P₂ := Yk) hnorm hnorm hcomm
      calc XM = ⁅XM, XM⁆ := hXperf.symm
        _ ≤ ⁅R ⊔ Yk, R ⊔ Yk⁆ := Subgroup.commutator_mono ih ih
        _ ≤ ⁅Yk ⊔ Y', Yk ⊔ Y'⁆ :=
          Subgroup.commutator_mono (sup_le (hRY'.trans le_sup_right) le_sup_left)
            (sup_le (hRY'.trans le_sup_right) le_sup_left)
        _ ≤ Y' := hcom
  obtain ⟨k, hk⟩ := (isSolvable_iff_exists_derivedSeriesOf_eq_bot YM).mp hYs
  simpa [hk] using key k

end Helpers

section Main

variable [Finite G]

theorem cover_section_core {n : ℕ} (hn : 1 ≤ n) {X T A J C : Subgroup G} [Fintype ↥C]
    (h : DiagSetting X T A J C) {M XM YM : Subgroup G} {ℒ : Set (Subgroup G)}
    (hS : SecData M XM YM ℒ)
    (hMT : M ≤ T ⊓ Subgroup.normalizer (J : Set G)) (hEM : actE T A J ≤ M) (hXJ : XM ≤ J)
    (hSylX : IsSylowIn 2 (T ⊓ XM) XM) {L₁ : Subgroup G} (hL₁ : L₁ ∈ ℒ)
    (hmove : (∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G), ∃ s ∈ L₁, v * s * v⁻¹ * s⁻¹ ∉ YM) ∨
      (∃ a ∈ A, a ∉ C ⊔ (A ⊓ Subgroup.normalizer (J : Set G))))
    (hrank : ∀ L ∈ ℒ,
      (∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (L : Set G),
        ∃ s ∈ L, v * s * v⁻¹ * s⁻¹ ∉ YM) →
      ∃ B ≤ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (L : Set G),
        (∀ b ∈ B, ∀ s ∈ L, b * s * b⁻¹ * s⁻¹ ∈ YM) ∧
          B.relIndex (A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (L : Set G)) ≤ 2 ^ n) :
    ∃ R : Subgroup G, R ≤ Cov (T ⊔ ⨆ K ∈ {K : Subgroup G | E1.IsE n ⊤ T A K}, K) J ∧
      XM ≤ R ⊔ YM ∧ (∀ x ∈ XM, ∀ r ∈ R, x * r * x⁻¹ ∈ R) := by
  classical
  obtain ⟨D, Y, D₁, 𝒟, hJD, hSylD, hD₁, hD₁D, hDX, hY, hD₁Y, hLcov⟩ :=
    jdata_of_section hS hEM hXJ hSylX hL₁
  have hkey : L₁ ≤ perfectCore L₁ ⊔ YM := key_le_perfectCore_sup hS hL₁
  subst hD₁
  subst hY
  have hVE : A ⊓ Subgroup.normalizer (J : Set G) ≤ actE T A J := by
    intro v hv
    rw [mem_actE_iff]
    refine ⟨h.AT hv.1, hv.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact h.comm ha hv.1
  have hEYM : ∀ e ∈ actE T A J, e ∈ Subgroup.normalizer (YM : Set G) := fun e he =>
    hS.M_Y (hEM he)
  have hYMX : YM ≤ XM := (hS.SM.Y_le L₁ hL₁).trans (hS.SM.le_D L₁ hL₁)
  have hDnorm : ∀ e ∈ actE T A J, ∀ d ∈ D, e * d * e⁻¹ ∈ D := by
    intro e he d hd
    have hd' : d ∈ ⨆ S ∈ 𝒟, S := by rw [hJD.SM.gen]; exact hd
    refine wr_join_induction 𝒟 (fun S => S) (P := fun x => e * x * e⁻¹ ∈ D) hd' ?_ ?_ ?_
    · intro S hS' y hy
      exact hJD.SM.le_D _ (hJD.SM.conj S hS' e he) (A1b.mem_conjSub_of_mem hy)
    · simp
    · intro a b ha hb
      have : e * (a * b) * e⁻¹ = (e * a * e⁻¹) * (e * b * e⁻¹) := by group
      rw [this]
      exact D.mul_mem ha hb
  have hmove' : (∃ S ∈ 𝒟, ∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G), ∃ s ∈ S,
        v * s * v⁻¹ * s⁻¹ ∉ D ⊓ YM) ∨
      (∃ a ∈ A, a ∉ C ⊔ (A ⊓ Subgroup.normalizer (J : Set G))) := by
    rcases hmove with ⟨v, hv, s, hs, hvs⟩ | h2
    · left
      refine ⟨perfectCore L₁ ⊔ D ⊓ YM, hD₁Y, v, hv, ?_⟩
      by_contra hcon
      push Not at hcon
      have hvE : v ∈ actE T A J := hVE hv
      obtain ⟨d, hd, y, hy, rfl⟩ := wr_mem_sup (H := perfectCore L₁) (K := YM)
        (fun d hd y hy => by
          have := (Subgroup.mem_normalizer_iff.mp (hS.X_Y ((hD₁D.trans hDX) hd)) y).mp hy
          simpa using this) (hkey hs)
      have hd1 : v * d * v⁻¹ * d⁻¹ ∈ YM :=
        (hcon d (Subgroup.mem_sup_left hd)).2
      have hvy : v * y * v⁻¹ * y⁻¹ ∈ YM := by
        have h1 := (Subgroup.mem_normalizer_iff.mp (hEYM v hvE) y).mp hy
        exact YM.mul_mem h1 (YM.inv_mem hy)
      have hdn : d * (v * y * v⁻¹ * y⁻¹) * d⁻¹ ∈ YM :=
        (Subgroup.mem_normalizer_iff.mp (hS.X_Y ((hD₁D.trans hDX) hd)) _).mp hvy
      apply hvs
      have key : v * (d * y) * v⁻¹ * (d * y)⁻¹ =
          (v * d * v⁻¹ * d⁻¹) * (d * (v * y * v⁻¹ * y⁻¹) * d⁻¹) := by group
      rw [key]
      exact YM.mul_mem hd1 hdn
    · exact Or.inr h2
  have hrank' : ∀ S ∈ 𝒟,
      (∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S : Set G),
        ∃ s ∈ S, v * s * v⁻¹ * s⁻¹ ∉ D ⊓ YM) →
      ∃ B ≤ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S : Set G),
        (∀ b ∈ B, ∀ s ∈ S, b * s * b⁻¹ * s⁻¹ ∈ D ⊓ YM) ∧
          B.relIndex (A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S : Set G)) ≤ 2 ^ n := by
    intro S hSD hex
    obtain ⟨e, he, hSeq⟩ := hJD.SM.trans (perfectCore L₁ ⊔ D ⊓ YM) hD₁Y S hSD
    have heM : e ∈ M := hEM he
    have hL : A1b.conjSub e L₁ ∈ ℒ := hS.SM.conj L₁ hL₁ e heM
    have hSL : S ≤ A1b.conjSub e L₁ := by
      rw [← hSeq]
      refine A1b.conjSub_mono e (sup_le (perfectCore_le L₁) ?_)
      exact inf_le_right.trans (hS.SM.Y_le L₁ hL₁)
    have hLS : A1b.conjSub e L₁ ≤ S ⊔ YM := by
      have h1 : A1b.conjSub e L₁ ≤ A1b.conjSub e (perfectCore L₁ ⊔ YM) := A1b.conjSub_mono e hkey
      rw [A1b.conjSub_sup, E111R.conjSub_eq_of_mem_normalizer (hEYM e he)] at h1
      refine h1.trans (sup_le_sup_right ?_ _)
      rw [← hSeq]
      exact A1b.conjSub_mono e le_sup_left
    have hYML : YM ≤ A1b.conjSub e L₁ := hS.SM.Y_le _ hL
    have hLeq : A1b.conjSub e L₁ = S ⊔ YM := le_antisymm hLS (sup_le hSL hYML)
    have hvL : ∀ v ∈ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S : Set G),
        v ∈ Subgroup.normalizer ((A1b.conjSub e L₁ : Subgroup G) : Set G) := by
      intro v hv
      have hvE : v ∈ actE T A J := hVE ⟨hv.1.1, hv.1.2⟩
      rw [hLeq]
      apply E111R.mem_normalizer_of_conjSub_eq
      rw [A1b.conjSub_sup, E111R.conjSub_eq_of_mem_normalizer hv.2,
        E111R.conjSub_eq_of_mem_normalizer (hEYM v hvE)]
    obtain ⟨v, hv, s, hs, hvs⟩ := hex
    have hvE : v ∈ actE T A J := hVE ⟨hv.1.1, hv.1.2⟩
    have hsD : s ∈ D := hJD.SM.le_D S hSD hs
    have hvsD : v * s * v⁻¹ * s⁻¹ ∈ D := D.mul_mem (hDnorm v hvE s hsD) (D.inv_mem hsD)
    have hvsYM : v * s * v⁻¹ * s⁻¹ ∉ YM := fun hh => hvs ⟨hvsD, hh⟩
    obtain ⟨B, hBle, hBc, hBr⟩ := hrank (A1b.conjSub e L₁) hL
      ⟨v, ⟨hv.1, hvL v hv⟩, s, hSL hs, hvsYM⟩
    refine ⟨B ⊓ (A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S : Set G)),
      inf_le_right, ?_, ?_⟩
    · intro b hb s' hs'
      have hbE : b ∈ actE T A J := hVE ⟨hb.2.1.1, hb.2.1.2⟩
      have hs'D : s' ∈ D := hJD.SM.le_D S hSD hs'
      exact ⟨D.mul_mem (hDnorm b hbE s' hs'D) (D.inv_mem hs'D), hBc b hb.1 s' (hSL hs')⟩
    · rw [Subgroup.inf_relIndex_right]
      calc B.relIndex (A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S : Set G))
          ≤ B.relIndex (A ⊓ Subgroup.normalizer (J : Set G) ⊓
              Subgroup.normalizer ((A1b.conjSub e L₁ : Subgroup G) : Set G)) :=
            Subgroup.relIndex_le_of_le_right (fun x hx => ⟨hx.1, hvL x hx⟩)
              (by unfold Subgroup.relIndex; exact Subgroup.index_ne_zero_of_finite)
        _ ≤ 2 ^ n := hBr
  have hcov := cover_diag hn h hJD hSylD hmove' hrank'
  have hDcov : D ≤ Cov (T ⊔ ⨆ K ∈ {K : Subgroup G | E1.IsE n ⊤ T A K}, K) J :=
    le_Cov_of_dimg h hJD.D_le hcov
  have hMcov : M ≤ Cov (T ⊔ ⨆ K ∈ {K : Subgroup G | E1.IsE n ⊤ T A K}, K) J := fun m hm =>
    mem_Cov_of_mem (Subgroup.mem_sup_left (hMT hm).1) (hMT hm).2
  have hRcov : (⨆ m ∈ M, A1b.conjSub m (perfectCore L₁)) ≤
      Cov (T ⊔ ⨆ K ∈ {K : Subgroup G | E1.IsE n ⊤ T A K}, K) J := by
    refine iSup₂_le fun m hm x hx => ?_
    rw [A1b.mem_conjSub_iff] at hx
    have hx' := hDcov (hD₁D hx)
    have h2 := (Cov _ J).mul_mem ((Cov _ J).mul_mem (hMcov hm) hx') ((Cov _ J).inv_mem (hMcov hm))
    have e : m * (m⁻¹ * x * m) * m⁻¹ = x := by group
    rwa [e] at h2
  have hRX : (⨆ m ∈ M, A1b.conjSub m (perfectCore L₁)) ≤ XM :=
    iSup₂_le fun m hm => (A1b.conjSub_mono m (perfectCore_le L₁)).trans
      (hS.SM.le_D _ (hS.SM.conj L₁ hL₁ m hm))
  have hXR : ∀ x ∈ XM, ∀ r ∈ (⨆ m ∈ M, A1b.conjSub m (perfectCore L₁)),
      x * r * x⁻¹ ∈ (⨆ m ∈ M, A1b.conjSub m (perfectCore L₁)) := by
    intro x hx r hr
    refine wr_join_induction (M : Set G) (fun m => A1b.conjSub m (perfectCore L₁))
      (P := fun y => x * y * x⁻¹ ∈ (⨆ m ∈ M, A1b.conjSub m (perfectCore L₁))) hr ?_ ?_ ?_
    · intro m hm y hy
      have hLm : A1b.conjSub m L₁ ∈ ℒ := hS.SM.conj L₁ hL₁ m hm
      have hconj : A1b.conjSub m (perfectCore L₁) = perfectCore (A1b.conjSub m L₁) :=
        map_perfectCore (MulAut.conj m).toMonoidHom L₁
      have hxn : x ∈ Subgroup.normalizer ((perfectCore (A1b.conjSub m L₁) : Subgroup G) : Set G) :=
        normalizer_le_normalizer_perfectCore _ (hS.SM.D_le_normalizer hLm hx)
      rw [hconj] at hy
      have := (Subgroup.mem_normalizer_iff.mp hxn y).mp hy
      rw [← hconj] at this
      have hsub : A1b.conjSub m (perfectCore L₁) ≤
          ⨆ m ∈ M, A1b.conjSub m (perfectCore L₁) :=
        le_iSup₂_of_le (f := fun m (_ : m ∈ M) => A1b.conjSub m (perfectCore L₁)) m hm le_rfl
      exact hsub this
    · simp
    · intro a b ha hb
      have : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ ha hb
  have hle : XM ≤ (⨆ m ∈ M, A1b.conjSub m (perfectCore L₁)) ⊔ YM := by
    rw [← hS.SM.gen]
    refine iSup₂_le fun L hL => ?_
    obtain ⟨m, hm, hLm⟩ := hLcov L hL
    refine hLm.trans (sup_le_sup_right ?_ _)
    exact le_iSup₂_of_le (f := fun m (_ : m ∈ M) => A1b.conjSub m (perfectCore L₁)) m hm le_rfl
  exact ⟨_, hRcov, hle, hXR⟩

theorem cover_section {n : ℕ} (hn : 1 ≤ n) {X T A J C : Subgroup G} [Fintype ↥C]
    (h : DiagSetting X T A J C) {M XM YM : Subgroup G} {ℒ : Set (Subgroup G)}
    (hS : SecData M XM YM ℒ) (hXperf : ⁅XM, XM⁆ = XM)
    (hMT : M ≤ T ⊓ Subgroup.normalizer (J : Set G)) (hEM : actE T A J ≤ M) (hXJ : XM ≤ J)
    (hSylX : IsSylowIn 2 (T ⊓ XM) XM) {L₁ : Subgroup G} (hL₁ : L₁ ∈ ℒ)
    (hmove : (∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G), ∃ s ∈ L₁, v * s * v⁻¹ * s⁻¹ ∉ YM) ∨
      (∃ a ∈ A, a ∉ C ⊔ (A ⊓ Subgroup.normalizer (J : Set G))))
    (hrank : ∀ L ∈ ℒ,
      (∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (L : Set G),
        ∃ s ∈ L, v * s * v⁻¹ * s⁻¹ ∉ YM) →
      ∃ B ≤ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (L : Set G),
        (∀ b ∈ B, ∀ s ∈ L, b * s * b⁻¹ * s⁻¹ ∈ YM) ∧
          B.relIndex (A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (L : Set G)) ≤ 2 ^ n) :
    XM ≤ Cov (T ⊔ ⨆ K ∈ {K : Subgroup G | E1.IsE n ⊤ T A K}, K) J := by
  obtain ⟨R, hRcov, hle, hXR⟩ := cover_section_core hn h hS hMT hEM hXJ hSylX hL₁ hmove hrank
  have hYMX : YM ≤ XM := (hS.SM.Y_le L₁ hL₁).trans (hS.SM.le_D L₁ hL₁)
  exact (le_of_le_sup_of_perfect hXperf hXR (fun y hy r hr => hXR y (hYMX hy) r hr) hS.Ysolv hle).trans
    hRcov

theorem cover_section_sup {n : ℕ} (hn : 1 ≤ n) {X T A J C : Subgroup G} [Fintype ↥C]
    (h : DiagSetting X T A J C) {M XM YM : Subgroup G} {ℒ : Set (Subgroup G)}
    (hS : SecData M XM YM ℒ)
    (hMT : M ≤ T ⊓ Subgroup.normalizer (J : Set G)) (hEM : actE T A J ≤ M) (hXJ : XM ≤ J)
    (hSylX : IsSylowIn 2 (T ⊓ XM) XM) {L₁ : Subgroup G} (hL₁ : L₁ ∈ ℒ)
    (hmove : (∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G), ∃ s ∈ L₁, v * s * v⁻¹ * s⁻¹ ∉ YM) ∨
      (∃ a ∈ A, a ∉ C ⊔ (A ⊓ Subgroup.normalizer (J : Set G))))
    (hrank : ∀ L ∈ ℒ,
      (∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (L : Set G),
        ∃ s ∈ L, v * s * v⁻¹ * s⁻¹ ∉ YM) →
      ∃ B ≤ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (L : Set G),
        (∀ b ∈ B, ∀ s ∈ L, b * s * b⁻¹ * s⁻¹ ∈ YM) ∧
          B.relIndex (A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (L : Set G)) ≤ 2 ^ n) :
    XM ≤ Cov (T ⊔ ⨆ K ∈ {K : Subgroup G | E1.IsE n ⊤ T A K}, K) J ⊔ YM := by
  obtain ⟨R, hRcov, hle, -⟩ := cover_section_core hn h hS hMT hEM hXJ hSylX hL₁ hmove hrank
  exact hle.trans (sup_le_sup_right hRcov _)

end Main

end CFSG.Quasithin.RonanE111
