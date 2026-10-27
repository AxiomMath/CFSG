module

public import CFSG.Quasithin.Background.RonanE111MemE1
public import CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer.PrintTen

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E2.E22N
  CFSG.Quasithin.E2.E22N.E111R CFSG.Quasithin.RonanE111
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def DiagCoverIn [Finite G] (n : ℕ) {X T A J C : Subgroup G} [Fintype ↥C]
    (h : E111R.DiagSetting X T A J C) (H₁ : Subgroup G) : Prop :=
  ∀ (D Y : Subgroup G) (𝒟 : Set (Subgroup G)),
    RonanE111.JData (RonanE111.actE T A J) J D Y 𝒟 → IsSylowIn 2 (T ⊓ D) D →
    ((∃ S ∈ 𝒟, ∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G), ∃ s ∈ S,
        v * s * v⁻¹ * s⁻¹ ∉ Y) ∨
      (∃ a ∈ A, a ∉ C ⊔ (A ⊓ Subgroup.normalizer (J : Set G)))) →
    (∀ S ∈ 𝒟,
      (∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S : Set G),
        ∃ s ∈ S, v * s * v⁻¹ * s⁻¹ ∉ Y) →
      ∃ B ≤ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S : Set G),
        (∀ b ∈ B, ∀ s ∈ S, b * s * b⁻¹ * s⁻¹ ∈ Y) ∧
          B.relIndex (A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S : Set G)) ≤
            2 ^ n) →
    RonanE111.dimg h.diagComm D ≤ H₁

private theorem le_centralizer_self_covP {A V : Subgroup G} (hVA : V ≤ A)
    (hAab : IsElemAbelian 2 A) : V ≤ Subgroup.centralizer (V : Set G) := by
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have := congrArg Subtype.val (hAab.1.is_comm.comm ⟨w, hVA hw⟩ ⟨v, hVA hv⟩)
  exact this

private theorem inf_normalizer_le_of_tauOf_covP [Finite G] {A T J P H : Subgroup G} (hAT : A ≤ T)
    (hAab : IsElemAbelian 2 A)
    (hTH : T ⊓ Subgroup.normalizer (J : Set G) ≤ H)
    (htau : E1.tauOf H (T ⊓ Subgroup.normalizer (J : Set G))
        (A ⊓ Subgroup.normalizer (J : Set G)) ≤
      (T ⊓ Subgroup.normalizer (J : Set G)) ⊓ P) :
    A ⊓ Subgroup.normalizer (J : Set G) ≤ P := by
  intro v hv
  have hvT : v ∈ T ⊓ Subgroup.normalizer (J : Set G) := ⟨hAT hv.1, hv.2⟩
  have hcent : v ∈ Subgroup.centralizer
      ((A ⊓ Subgroup.normalizer (J : Set G) : Subgroup G) : Set G) :=
    le_centralizer_self_covP inf_le_left hAab hv
  exact (htau (centralizer_inf_le_tauOf hTH ⟨hvT, hcent⟩)).2

private theorem actE_le_of_tauOf_covP [Finite G] {A T J P H : Subgroup G}
    (hTH : T ⊓ Subgroup.normalizer (J : Set G) ≤ H)
    (htau : E1.tauOf H (T ⊓ Subgroup.normalizer (J : Set G))
        (A ⊓ Subgroup.normalizer (J : Set G)) ≤
      (T ⊓ Subgroup.normalizer (J : Set G)) ⊓ P) :
    RonanE111.actE T A J ≤ (T ⊓ Subgroup.normalizer (J : Set G)) ⊓ P := by
  intro e he
  obtain ⟨heT, heN, heA⟩ := mem_actE_iff.mp he
  refine htau (centralizer_inf_le_tauOf hTH ⟨⟨heT, heN⟩, ?_⟩)
  show e ∈ Subgroup.centralizer
    ((A ⊓ Subgroup.normalizer (J : Set G) : Subgroup G) : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact Subgroup.mem_centralizer_iff.mp heA v hv.1

private theorem conjSub_eq_of_conj_mem_covP {P U : Subgroup G}
    (hU : ∀ x ∈ P, ∀ u ∈ U, x * u * x⁻¹ ∈ U) :
    ∀ e ∈ P, A1b.conjSub e U = U := by
  intro e he
  apply le_antisymm
  · intro x hx
    rw [A1b.mem_conjSub_iff] at hx
    have := hU e he _ hx
    simpa [mul_assoc] using this
  · intro x hx
    rw [A1b.mem_conjSub_iff]
    simpa using hU e⁻¹ (P.inv_mem he) x hx

private theorem dnorm_covP [Finite G] {E J D Y : Subgroup G} {𝒟 : Set (Subgroup G)}
    (hJD : RonanE111.JData E J D Y 𝒟) :
    ∀ e ∈ E, ∀ d ∈ D, e * d * e⁻¹ ∈ D := by
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

private theorem inf_normalizer_le_actE_covP [Finite G] {X T A J C : Subgroup G}
    (h : E111R.DiagSetting X T A J C) :
    A ⊓ Subgroup.normalizer (J : Set G) ≤ RonanE111.actE T A J := by
  intro v hv
  rw [mem_actE_iff]
  exact ⟨h.AT hv.1, hv.2, Subgroup.mem_centralizer_iff.mpr fun a ha => h.comm ha hv.1⟩

private theorem move_diag_covP [Finite G] {X T A J C M XM YM D L₁ : Subgroup G}
    {ℒ 𝒟 : Set (Subgroup G)} (h : E111R.DiagSetting X T A J C)
    (hS : RonanE111.SecData M XM YM ℒ) (hL₁ : L₁ ∈ ℒ)
    (hEM : RonanE111.actE T A J ≤ M) (hD₁D : perfectCore L₁ ≤ D) (hDX : D ≤ XM)
    (hD₁Y : perfectCore L₁ ⊔ D ⊓ YM ∈ 𝒟)
    (hmove : (∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G), ∃ s ∈ L₁,
        v * s * v⁻¹ * s⁻¹ ∉ YM) ∨
      (∃ a ∈ A, a ∉ C ⊔ (A ⊓ Subgroup.normalizer (J : Set G)))) :
    (∃ S ∈ 𝒟, ∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G), ∃ s ∈ S,
        v * s * v⁻¹ * s⁻¹ ∉ D ⊓ YM) ∨
      (∃ a ∈ A, a ∉ C ⊔ (A ⊓ Subgroup.normalizer (J : Set G))) := by
  have hkey : L₁ ≤ perfectCore L₁ ⊔ YM := key_le_perfectCore_sup hS hL₁
  have hVE : A ⊓ Subgroup.normalizer (J : Set G) ≤ RonanE111.actE T A J :=
    inf_normalizer_le_actE_covP h
  have hEYM : ∀ e ∈ RonanE111.actE T A J, e ∈ Subgroup.normalizer (YM : Set G) := fun e he =>
    hS.M_Y (hEM he)
  rcases hmove with ⟨v, hv, s, hs, hvs⟩ | h2
  · left
    refine ⟨perfectCore L₁ ⊔ D ⊓ YM, hD₁Y, v, hv, ?_⟩
    by_contra hcon
    push Not at hcon
    have hvE : v ∈ RonanE111.actE T A J := hVE hv
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

private theorem rank_diag_covP [Finite G] {n : ℕ} {T A J M XM YM D L₁ : Subgroup G}
    {ℒ 𝒟 : Set (Subgroup G)}
    (hJD : RonanE111.JData (RonanE111.actE T A J) J D (D ⊓ YM) 𝒟)
    (hS : RonanE111.SecData M XM YM ℒ) (hL₁ : L₁ ∈ ℒ)
    (hEM : RonanE111.actE T A J ≤ M) (hD₁Y : perfectCore L₁ ⊔ D ⊓ YM ∈ 𝒟)
    (hDnorm : ∀ e ∈ RonanE111.actE T A J, ∀ d ∈ D, e * d * e⁻¹ ∈ D)
    (hVE : A ⊓ Subgroup.normalizer (J : Set G) ≤ RonanE111.actE T A J)
    (hrank : ∀ L ∈ ℒ,
      (∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (L : Set G),
        ∃ s ∈ L, v * s * v⁻¹ * s⁻¹ ∉ YM) →
      ∃ B ≤ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (L : Set G),
        (∀ b ∈ B, ∀ s ∈ L, b * s * b⁻¹ * s⁻¹ ∈ YM) ∧
          B.relIndex
            (A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (L : Set G)) ≤ 2 ^ n) :
    ∀ S ∈ 𝒟,
      (∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S : Set G),
        ∃ s ∈ S, v * s * v⁻¹ * s⁻¹ ∉ D ⊓ YM) →
      ∃ B ≤ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S : Set G),
        (∀ b ∈ B, ∀ s ∈ S, b * s * b⁻¹ * s⁻¹ ∈ D ⊓ YM) ∧
          B.relIndex
            (A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S : Set G)) ≤ 2 ^ n := by
  have hkey : L₁ ≤ perfectCore L₁ ⊔ YM := key_le_perfectCore_sup hS hL₁
  have hEYM : ∀ e ∈ RonanE111.actE T A J, e ∈ Subgroup.normalizer (YM : Set G) := fun e he =>
    hS.M_Y (hEM he)
  intro S hSD hex
  obtain ⟨e, he, hSeq⟩ := hJD.SM.trans (perfectCore L₁ ⊔ D ⊓ YM) hD₁Y S hSD
  have heM : e ∈ M := hEM he
  have hL : A1b.conjSub e L₁ ∈ ℒ := hS.SM.conj L₁ hL₁ e heM
  have hSL : S ≤ A1b.conjSub e L₁ := by
    rw [← hSeq]
    refine A1b.conjSub_mono e (sup_le (perfectCore_le L₁) ?_)
    exact inf_le_right.trans (hS.SM.Y_le L₁ hL₁)
  have hLS : A1b.conjSub e L₁ ≤ S ⊔ YM := by
    have h1 : A1b.conjSub e L₁ ≤ A1b.conjSub e (perfectCore L₁ ⊔ YM) :=
      A1b.conjSub_mono e hkey
    rw [A1b.conjSub_sup, E111R.conjSub_eq_of_mem_normalizer (hEYM e he)] at h1
    refine h1.trans (sup_le_sup_right ?_ _)
    rw [← hSeq]
    exact A1b.conjSub_mono e le_sup_left
  have hYML : YM ≤ A1b.conjSub e L₁ := hS.SM.Y_le _ hL
  have hLeq : A1b.conjSub e L₁ = S ⊔ YM := le_antisymm hLS (sup_le hSL hYML)
  have hvL : ∀ v ∈ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S : Set G),
      v ∈ Subgroup.normalizer ((A1b.conjSub e L₁ : Subgroup G) : Set G) := by
    intro v hv
    have hvE : v ∈ RonanE111.actE T A J := hVE ⟨hv.1.1, hv.1.2⟩
    rw [hLeq]
    apply E111R.mem_normalizer_of_conjSub_eq
    rw [A1b.conjSub_sup, E111R.conjSub_eq_of_mem_normalizer hv.2,
      E111R.conjSub_eq_of_mem_normalizer (hEYM v hvE)]
  obtain ⟨v, hv, s, hs, hvs⟩ := hex
  have hvE : v ∈ RonanE111.actE T A J := hVE ⟨hv.1.1, hv.1.2⟩
  have hsD : s ∈ D := hJD.SM.le_D S hSD hs
  have hvsD : v * s * v⁻¹ * s⁻¹ ∈ D := D.mul_mem (hDnorm v hvE s hsD) (D.inv_mem hsD)
  have hvsYM : v * s * v⁻¹ * s⁻¹ ∉ YM := fun hh => hvs ⟨hvsD, hh⟩
  obtain ⟨B, hBle, hBc, hBr⟩ := hrank (A1b.conjSub e L₁) hL
    ⟨v, ⟨hv.1, hvL v hv⟩, s, hSL hs, hvsYM⟩
  refine ⟨B ⊓ (A ⊓ Subgroup.normalizer (J : Set G) ⊓
      Subgroup.normalizer (S : Set G)), inf_le_right, ?_, ?_⟩
  · intro b hb s' hs'
    have hbE : b ∈ RonanE111.actE T A J := hVE ⟨hb.2.1.1, hb.2.1.2⟩
    have hs'D : s' ∈ D := hJD.SM.le_D S hSD hs'
    exact ⟨D.mul_mem (hDnorm b hbE s' hs'D) (D.inv_mem hs'D), hBc b hb.1 s' (hSL hs')⟩
  · rw [Subgroup.inf_relIndex_right]
    calc B.relIndex (A ⊓ Subgroup.normalizer (J : Set G) ⊓
          Subgroup.normalizer (S : Set G))
        ≤ B.relIndex (A ⊓ Subgroup.normalizer (J : Set G) ⊓
            Subgroup.normalizer ((A1b.conjSub e L₁ : Subgroup G) : Set G)) :=
          Subgroup.relIndex_le_of_le_right (fun x hx => ⟨hx.1, hvL x hx⟩)
            (by unfold Subgroup.relIndex; exact Subgroup.index_ne_zero_of_finite)
      _ ≤ 2 ^ n := hBr

private theorem conj_join_covP [Finite G] {M XM YM L₁ : Subgroup G} {ℒ : Set (Subgroup G)}
    (hS : RonanE111.SecData M XM YM ℒ) (hL₁ : L₁ ∈ ℒ) :
    ∀ x ∈ XM, ∀ r ∈ (⨆ m ∈ M, A1b.conjSub m (perfectCore L₁)),
      x * r * x⁻¹ ∈ (⨆ m ∈ M, A1b.conjSub m (perfectCore L₁)) := by
  intro x hx r hr
  refine wr_join_induction (M : Set G) (fun m => A1b.conjSub m (perfectCore L₁))
    (P := fun y => x * y * x⁻¹ ∈ (⨆ m ∈ M, A1b.conjSub m (perfectCore L₁))) hr ?_ ?_ ?_
  · intro m hm y hy
    have hLm : A1b.conjSub m L₁ ∈ ℒ := hS.SM.conj L₁ hL₁ m hm
    have hconj : A1b.conjSub m (perfectCore L₁) = perfectCore (A1b.conjSub m L₁) :=
      map_perfectCore (MulAut.conj m).toMonoidHom L₁
    have hxn : x ∈ Subgroup.normalizer
        ((perfectCore (A1b.conjSub m L₁) : Subgroup G) : Set G) :=
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

private theorem exists_R_covP {H₁ J M XM YM D L₁ : Subgroup G} {ℒ : Set (Subgroup G)}
    (hS : RonanE111.SecData M XM YM ℒ) (hL₁ : L₁ ∈ ℒ)
    (hDcov : D ≤ RonanE111.Cov H₁ J) (hMcov : M ≤ RonanE111.Cov H₁ J)
    (hD₁D : perfectCore L₁ ≤ D)
    (hLcov : ∀ L ∈ ℒ, ∃ m ∈ M, L ≤ A1b.conjSub m (perfectCore L₁) ⊔ YM)
    (hXR : ∀ x ∈ XM, ∀ r ∈ (⨆ m ∈ M, A1b.conjSub m (perfectCore L₁)),
      x * r * x⁻¹ ∈ (⨆ m ∈ M, A1b.conjSub m (perfectCore L₁))) :
    ∃ R : Subgroup G, R ≤ RonanE111.Cov H₁ J ∧ XM ≤ R ⊔ YM ∧
      (∀ x ∈ XM, ∀ r ∈ R, x * r * x⁻¹ ∈ R) := by
  refine ⟨⨆ m ∈ M, A1b.conjSub m (perfectCore L₁), ?_, ?_, hXR⟩
  · refine iSup₂_le fun m hm x hx => ?_
    rw [A1b.mem_conjSub_iff] at hx
    have hx' := hDcov (hD₁D hx)
    have h2 := (RonanE111.Cov H₁ J).mul_mem
      ((RonanE111.Cov H₁ J).mul_mem (hMcov hm) hx')
      ((RonanE111.Cov H₁ J).inv_mem (hMcov hm))
    have e : m * (m⁻¹ * x * m) * m⁻¹ = x := by group
    rwa [e] at h2
  · rw [← hS.SM.gen]
    refine iSup₂_le fun L hL => ?_
    obtain ⟨m, hm, hLm⟩ := hLcov L hL
    refine hLm.trans (sup_le_sup_right ?_ _)
    exact le_iSup₂_of_le (f := fun m (_ : m ∈ M) => A1b.conjSub m (perfectCore L₁)) m hm le_rfl

private theorem cover_section_core_covP [Finite G] {n : ℕ} {X T A J C : Subgroup G}
    [Fintype ↥C] (h : E111R.DiagSetting X T A J C) {H₁ : Subgroup G} (hTH : T ≤ H₁)
    (hdiag : DiagCoverIn n h H₁) {M XM YM : Subgroup G} {ℒ : Set (Subgroup G)}
    (hS : RonanE111.SecData M XM YM ℒ)
    (hMT : M ≤ T ⊓ Subgroup.normalizer (J : Set G)) (hEM : RonanE111.actE T A J ≤ M)
    (hXJ : XM ≤ J) (hSylX : IsSylowIn 2 (T ⊓ XM) XM) {L₁ : Subgroup G} (hL₁ : L₁ ∈ ℒ)
    (hmove : (∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G), ∃ s ∈ L₁,
        v * s * v⁻¹ * s⁻¹ ∉ YM) ∨
      (∃ a ∈ A, a ∉ C ⊔ (A ⊓ Subgroup.normalizer (J : Set G))))
    (hrank : ∀ L ∈ ℒ,
      (∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (L : Set G),
        ∃ s ∈ L, v * s * v⁻¹ * s⁻¹ ∉ YM) →
      ∃ B ≤ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (L : Set G),
        (∀ b ∈ B, ∀ s ∈ L, b * s * b⁻¹ * s⁻¹ ∈ YM) ∧
          B.relIndex
            (A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (L : Set G)) ≤ 2 ^ n) :
    ∃ R : Subgroup G, R ≤ RonanE111.Cov H₁ J ∧ XM ≤ R ⊔ YM ∧
      (∀ x ∈ XM, ∀ r ∈ R, x * r * x⁻¹ ∈ R) := by
  classical
  obtain ⟨D, Y, D₁, 𝒟, hJD, hSylD, hD₁, hD₁D, hDX, hY, hD₁Y, hLcov⟩ :=
    jdata_of_section hS hEM hXJ hSylX hL₁
  subst hD₁
  subst hY
  unfold DiagCoverIn at hdiag
  have hDnorm : ∀ e ∈ RonanE111.actE T A J, ∀ d ∈ D, e * d * e⁻¹ ∈ D := dnorm_covP hJD
  have hVE : A ⊓ Subgroup.normalizer (J : Set G) ≤ RonanE111.actE T A J :=
    inf_normalizer_le_actE_covP h
  have hmove' := move_diag_covP h hS hL₁ hEM hD₁D hDX hD₁Y hmove
  have hrank' := rank_diag_covP hJD hS hL₁ hEM hD₁Y hDnorm hVE hrank
  have hcov : RonanE111.dimg h.diagComm D ≤ H₁ :=
    hdiag D (D ⊓ YM) 𝒟 hJD hSylD hmove' hrank'
  have hDcov : D ≤ RonanE111.Cov H₁ J := le_Cov_of_dimg h hJD.D_le hcov
  have hMcov : M ≤ RonanE111.Cov H₁ J := fun m hm =>
    mem_Cov_of_mem (hTH (hMT hm).1) (hMT hm).2
  exact exists_R_covP hS hL₁ hDcov hMcov hD₁D hLcov (conj_join_covP hS hL₁)

theorem cover_section_of_diagCoverIn [Finite G] {n : ℕ} {X T A J C : Subgroup G} [Fintype ↥C]
    (h : E111R.DiagSetting X T A J C) {H₁ : Subgroup G} (hTH : T ≤ H₁)
    (hdiag : DiagCoverIn n h H₁) {M XM YM : Subgroup G} {ℒ : Set (Subgroup G)}
    (hS : RonanE111.SecData M XM YM ℒ) (hXperf : ⁅XM, XM⁆ = XM)
    (hMT : M ≤ T ⊓ Subgroup.normalizer (J : Set G)) (hEM : RonanE111.actE T A J ≤ M)
    (hXJ : XM ≤ J) (hSylX : IsSylowIn 2 (T ⊓ XM) XM) {L₁ : Subgroup G} (hL₁ : L₁ ∈ ℒ)
    (hmove : (∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G), ∃ s ∈ L₁,
        v * s * v⁻¹ * s⁻¹ ∉ YM) ∨
      (∃ a ∈ A, a ∉ C ⊔ (A ⊓ Subgroup.normalizer (J : Set G))))
    (hrank : ∀ L ∈ ℒ,
      (∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (L : Set G),
        ∃ s ∈ L, v * s * v⁻¹ * s⁻¹ ∉ YM) →
      ∃ B ≤ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (L : Set G),
        (∀ b ∈ B, ∀ s ∈ L, b * s * b⁻¹ * s⁻¹ ∈ YM) ∧
          B.relIndex
            (A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (L : Set G)) ≤ 2 ^ n) :
    XM ≤ RonanE111.Cov H₁ J := by
  obtain ⟨R, hRcov, hle, hXR⟩ :=
    cover_section_core_covP h hTH hdiag hS hMT hEM hXJ hSylX hL₁ hmove hrank
  have hYMX : YM ≤ XM := (hS.SM.Y_le L₁ hL₁).trans (hS.SM.le_D L₁ hL₁)
  exact (le_of_le_sup_of_perfect hXperf hXR (fun y hy r hr => hXR y (hYMX hy) r hr) hS.Ysolv
    hle).trans hRcov

theorem P_le_cov_E2_of_diagCoverIn [Finite G] {X T J : Subgroup G}
    (hR : CFSG.Quasithin.Vol2.Ch11.SecB.E111Reduced G X T) (hJ : E111R.IsComp X J) {n : ℕ}
    {G₁ : Subgroup G} (hTG : T ≤ G₁) {A : Subgroup G} (hAT : A ≤ T) (hAab : IsElemAbelian 2 A)
    (hdiag : ∀ (Z : Subgroup G) [Fintype ↥Z] (h : E111R.DiagSetting X T A J Z),
      DiagCoverIn n h G₁)
    {P : Subgroup G} (hPH : P ≤ J ⊔ (T ⊓ Subgroup.normalizer (J : Set G)))
    (htau : E1.tauOf (J ⊔ (T ⊓ Subgroup.normalizer (J : Set G)))
        (T ⊓ Subgroup.normalizer (J : Set G)) (A ⊓ Subgroup.normalizer (J : Set G)) ≤
      (T ⊓ Subgroup.normalizer (J : Set G)) ⊓ P)
    (hSyl : IsSylowIn 2 ((T ⊓ Subgroup.normalizer (J : Set G)) ⊓ P) P)
    (hE2 : E1.ETwo ↥P
      (((T ⊓ Subgroup.normalizer (J : Set G)) ⊓ P).subgroupOf P)
      ((A ⊓ Subgroup.normalizer (J : Set G)).subgroupOf P))
    (hbar : Nat.card (E1.barRad ↥P ((A ⊓ Subgroup.normalizer (J : Set G)).subgroupOf P)) ≤
      2 ^ n) :
    P ≤ RonanE111.Cov G₁ J := by
  classical
  have hHS : T ⊓ Subgroup.normalizer (J : Set G) ≤
      J ⊔ (T ⊓ Subgroup.normalizer (J : Set G)) := le_sup_right
  have hVP : A ⊓ Subgroup.normalizer (J : Set G) ≤ P :=
    inf_normalizer_le_of_tauOf_covP hAT hAab hHS htau
  have hEM : RonanE111.actE T A J ≤ (T ⊓ Subgroup.normalizer (J : Set G)) ⊓ P :=
    actE_le_of_tauOf_covP hHS htau
  obtain ⟨XM, YM, ℒ, L₁, hXM, hYX, hSec, hL₁, hperf, hSylX, hPX, hmove, hrank⟩ :=
    e2_sec hVP hSyl hE2 hbar
  have hT : IsSylowIn 2 T ⊤ := hR.2.2.2.2.2.1
  have hSN : T ⊓ Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (J : Set G) := inf_le_right
  have hS2 : IsPGroup 2 ↥(T ⊓ Subgroup.normalizer (J : Set G)) := hT.2.1.to_le inf_le_left
  have hXJ : XM ≤ J := by
    rw [hXM]
    exact perfectCore_le_of_le_sup_two hSN hS2 hPH
  obtain ⟨Z, hZA, hZV, hZVA⟩ :=
    exists_compl hAab (inf_le_left : A ⊓ Subgroup.normalizer (J : Set G) ≤ A)
  have hset : E111R.DiagSetting X T A J Z := ⟨hR, hAT, hAab, hJ, hZA, hZV⟩
  haveI : Fintype ↥Z := Fintype.ofFinite _
  have hSylX' : IsSylowIn 2 (T ⊓ XM) XM := by
    have e : T ⊓ XM = (T ⊓ Subgroup.normalizer (J : Set G)) ⊓ XM := by
      ext x
      exact ⟨fun hx => ⟨⟨hx.1, Subgroup.le_normalizer (hXJ hx.2)⟩, hx.2⟩,
        fun hx => ⟨hx.1.1, hx.2⟩⟩
    rw [e]
    exact hSylX
  have hcov : XM ≤ RonanE111.Cov G₁ J :=
    cover_section_of_diagCoverIn hset hTG (hdiag Z hset) hSec hperf
      (inf_le_left : (T ⊓ Subgroup.normalizer (J : Set G)) ⊓ P ≤
        T ⊓ Subgroup.normalizer (J : Set G)) hEM hXJ hSylX' hL₁ (Or.inl hmove) hrank
  have hSCov : T ⊓ Subgroup.normalizer (J : Set G) ≤ RonanE111.Cov G₁ J := fun s hs =>
    mem_Cov_of_mem (hTG hs.1) hs.2
  rw [hPX]
  exact sup_le hcov (inf_le_left.trans hSCov)

theorem P_le_cov_E1P [Finite G] {X T J : Subgroup G}
    (hR : CFSG.Quasithin.Vol2.Ch11.SecB.E111Reduced G X T) (hJ : E111R.IsComp X J) {n : ℕ}
    (hn : 1 ≤ n) {G₁ : Subgroup G} (hTG : T ≤ G₁) {A : Subgroup G} (hAT : A ≤ T)
    (hAab : IsElemAbelian 2 A)
    (hmem : ∀ K : Subgroup G, UniquenessCase.UC22.F12.IsEP n ⊤ T A K → K ≤ G₁)
    {P : Subgroup G} (hPH : P ≤ J ⊔ (T ⊓ Subgroup.normalizer (J : Set G)))
    (htau : E1.tauOf (J ⊔ (T ⊓ Subgroup.normalizer (J : Set G)))
        (T ⊓ Subgroup.normalizer (J : Set G)) (A ⊓ Subgroup.normalizer (J : Set G)) ≤
      (T ⊓ Subgroup.normalizer (J : Set G)) ⊓ P)
    (hSyl : IsSylowIn 2 ((T ⊓ Subgroup.normalizer (J : Set G)) ⊓ P) P)
    (hE1 : E1.EOne ↥P ((A ⊓ Subgroup.normalizer (J : Set G)).subgroupOf P)) :
    P ≤ RonanE111.Cov G₁ J := by
  classical
  have hHS : T ⊓ Subgroup.normalizer (J : Set G) ≤
      J ⊔ (T ⊓ Subgroup.normalizer (J : Set G)) := le_sup_right
  have hVP : A ⊓ Subgroup.normalizer (J : Set G) ≤ P :=
    inf_normalizer_le_of_tauOf_covP hAT hAab hHS htau
  have hEP : RonanE111.actE T A J ≤ P :=
    (actE_le_of_tauOf_covP hHS htau).trans inf_le_right
  obtain ⟨p, R, YR, hp, hp2, hRdef, hRP, hYR, hYRS, hRn, hYn, hPR, hpq, hgen⟩ :=
    e1_data hVP hSyl hE1
  have hT : IsSylowIn 2 T ⊤ := hR.2.2.2.2.2.1
  have hSN : T ⊓ Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (J : Set G) := inf_le_right
  have hS2 : IsPGroup 2 ↥(T ⊓ Subgroup.normalizer (J : Set G)) := hT.2.1.to_le inf_le_left
  have hRJ : R ≤ J := by
    rw [hRdef]
    exact twoResidual_le_of_le_sup_two hSN hS2 hPH
  obtain ⟨Z, hZA, hZV, hZVA⟩ :=
    exists_compl hAab (inf_le_left : A ⊓ Subgroup.normalizer (J : Set G) ≤ A)
  have hset : E111R.DiagSetting X T A J Z := ⟨hR, hAT, hAab, hJ, hZA, hZV⟩
  haveI : Fintype ↥Z := Fintype.ofFinite _
  have hYRn : ∀ r ∈ R, ∀ y ∈ YR, r * y * r⁻¹ ∈ YR := fun r hr y hy => hYn r (hRP hr) y hy
  have hYRS' : YR ≤ T ⊓ Subgroup.normalizer (J : Set G) := hYRS.trans inf_le_left
  have hYT : YR ≤ T := hYRS'.trans inf_le_left
  have hcov := pgroup_diag_coverP hn hset hp hp2 hRJ hYR hYRn hYT
    (fun e he => conjSub_eq_of_conj_mem_covP hRn e (hEP he))
    (fun e he => conjSub_eq_of_conj_mem_covP hYn e (hEP he)) hpq hgen
  have hG₁ : T ⊔ ⨆ K ∈ {K : Subgroup G | UniquenessCase.UC22.F12.IsEP n ⊤ T A K}, K ≤ G₁ :=
    sup_le hTG (iSup₂_le fun K hK => hmem K hK)
  have hRCov : R ≤ RonanE111.Cov G₁ J := le_Cov_of_dimg hset hRJ (hcov.trans hG₁)
  have hSCov : T ⊓ Subgroup.normalizer (J : Set G) ≤ RonanE111.Cov G₁ J := fun s hs =>
    mem_Cov_of_mem (hTG hs.1) hs.2
  rw [hPR]
  exact sup_le hRCov (inf_le_left.trans hSCov)

theorem P_le_cov_of_diagCoverIn [Finite G] {X T J : Subgroup G}
    (hR : CFSG.Quasithin.Vol2.Ch11.SecB.E111Reduced G X T) (hJ : E111R.IsComp X J) {n : ℕ}
    (hn : 1 ≤ n) {G₁ : Subgroup G} (hTG : T ≤ G₁) {A : Subgroup G} (hAT : A ≤ T)
    (hAab : IsElemAbelian 2 A)
    (hmem : ∀ K : Subgroup G, UniquenessCase.UC22.F12.IsEP n ⊤ T A K → K ≤ G₁)
    (hdiag : ∀ (Z : Subgroup G) [Fintype ↥Z] (h : E111R.DiagSetting X T A J Z),
      DiagCoverIn n h G₁)
    {P : Subgroup G}
    (hP : E1.IsE n (J ⊔ (T ⊓ Subgroup.normalizer (J : Set G)))
      (T ⊓ Subgroup.normalizer (J : Set G)) (A ⊓ Subgroup.normalizer (J : Set G)) P) :
    P ≤ RonanE111.Cov G₁ J := by
  obtain ⟨hPH, htau, hSyl, hcase⟩ := hP
  rcases hcase with ⟨hE1, -⟩ | ⟨hE2, hbar⟩
  · exact P_le_cov_E1P hR hJ hn hTG hAT hAab hmem hPH htau hSyl hE1
  · exact P_le_cov_E2_of_diagCoverIn hR hJ hTG hAT hAab hdiag hPH htau hSyl hE2 hbar

end CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer
