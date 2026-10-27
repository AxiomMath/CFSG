module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Regimes
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1DTransport
public import CFSG.LocalAnalysis.StandardType.GGE0PSLComp
public import CFSG.LocalAnalysis.StandardType.GGE0PSUFrame
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestInner
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.LieType.SemisimpleCentralizers.HeldSLFacts
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Unitary
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.StandardType.Q1DSmall

open CFSG CFSG.Assembly
open CFSG.StandardType.S2MathAs51642Interfaces

@[expose] def LowDTwD (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  CenterPrimeTo p lab ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧ lab.rank < 4

theorem inLambda2_D3_iff_A3 (n : ℕ) :
    LargeEvenInLambda2 (⟨.D, 3, n⟩ : LargeEvenLabel) ↔
      LargeEvenInLambda2 (⟨.A, 3, n⟩ : LargeEvenLabel) := by
  simp [LargeEvenInLambda2]

theorem inLambda2_twD3_iff_twA3 (n : ℕ) :
    LargeEvenInLambda2 (⟨.twD, 3, n⟩ : LargeEvenLabel) ↔
      LargeEvenInLambda2 (⟨.twA, 3, n⟩ : LargeEvenLabel) := by
  simp [LargeEvenInLambda2]

theorem inLambda2_twD2_iff_A1 (n : ℕ) :
    LargeEvenInLambda2 (⟨.twD, 2, n⟩ : LargeEvenLabel) ↔
      LargeEvenInLambda2 (⟨.A, 1, 2 * n⟩ : LargeEvenLabel) := by
  simp only [LargeEvenInLambda2]
  omega

theorem labelIso_D3_A3 (n : ℕ) :
    GGLabelIso (⟨.D, 3, n⟩ : LargeEvenLabel) ⟨.A, 3, n⟩ :=
  Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))

theorem labelIso_A3_D3 (n : ℕ) :
    GGLabelIso (⟨.A, 3, n⟩ : LargeEvenLabel) ⟨.D, 3, n⟩ :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))

theorem labelIso_twD3_twA3 (n : ℕ) :
    GGLabelIso (⟨.twD, 3, n⟩ : LargeEvenLabel) ⟨.twA, 3, n⟩ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))

theorem labelIso_twA3_twD3 (n : ℕ) :
    GGLabelIso (⟨.twA, 3, n⟩ : LargeEvenLabel) ⟨.twD, 3, n⟩ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))

theorem labelIso_twD2_A1 (n : ℕ) :
    GGLabelIso (⟨.twD, 2, n⟩ : LargeEvenLabel) ⟨.A, 1, 2 * n⟩ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))

theorem labelIso_A1_twD2 (n : ℕ) :
    GGLabelIso (⟨.A, 1, 2 * n⟩ : LargeEvenLabel) ⟨.twD, 2, n⟩ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))))

theorem rawDatum_D3_iff_A3 (n : ℕ) (Q : LargeEvenRawCont) :
    LargeEvenRawDatum (⟨.D, 3, n⟩ : LargeEvenLabel) Q ↔
      LargeEvenRawDatum (⟨.A, 3, n⟩ : LargeEvenLabel) Q :=
  ⟨largeEvenRawDatum_of_ggLabelIso (labelIso_D3_A3 n),
    largeEvenRawDatum_of_ggLabelIso (labelIso_A3_D3 n)⟩

theorem rawDatum_twD3_iff_twA3 (n : ℕ) (Q : LargeEvenRawCont) :
    LargeEvenRawDatum (⟨.twD, 3, n⟩ : LargeEvenLabel) Q ↔
      LargeEvenRawDatum (⟨.twA, 3, n⟩ : LargeEvenLabel) Q :=
  ⟨largeEvenRawDatum_of_ggLabelIso (labelIso_twD3_twA3 n),
    largeEvenRawDatum_of_ggLabelIso (labelIso_twA3_twD3 n)⟩

theorem rawDatum_twD2_iff_A1 (n : ℕ) (Q : LargeEvenRawCont) :
    LargeEvenRawDatum (⟨.twD, 2, n⟩ : LargeEvenLabel) Q ↔
      LargeEvenRawDatum (⟨.A, 1, 2 * n⟩ : LargeEvenLabel) Q :=
  ⟨largeEvenRawDatum_of_ggLabelIso (labelIso_twD2_A1 n),
    largeEvenRawDatum_of_ggLabelIso (labelIso_A1_twD2 n)⟩

abbrev LargeEvenMarkCont (X : Type*) [Group X] : Type _ :=
  (R : Type) → [Group R] → Set (MulAut R) → Set (MulAut R) →
    (X ⧸ Subgroup.center X ≃* R) → Prop

theorem largeEvenMarking_relabel {X : Type*} [Group X] {lab₁ lab₂ : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 lab₁ ↔ LargeEvenInLambda2 lab₂)
    (hraw : ∀ Q : LargeEvenRawCont, LargeEvenRawDatum lab₁ Q ↔ LargeEvenRawDatum lab₂ Q)
    {P : LargeEvenMarkCont X}
    (h : LargeEvenMarking X (fun lab R _ I F θ => lab = lab₁ ∧ P R I F θ)) :
    LargeEvenMarking X (fun lab R _ I F θ => lab = lab₂ ∧ P R I F θ) := by
  obtain ⟨hperf, lab, hΛlab, hrawd⟩ := h
  obtain ⟨R, hR, I, F, hq⟩ := largeEvenRawDatum_exists hrawd
  obtain ⟨hsimple, hnonab, θ, hlab₁, hP⟩ := hq
  rw [hlab₁] at hrawd
  have hraw₁ : LargeEvenRawDatum lab₁ (fun R _ I F =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : X ⧸ Subgroup.center X ≃* R, P R I F θ) :=
    largeEvenRawDatum_mono (fun R _ I F hh => by
      obtain ⟨hs, hna, θ, -, hP⟩ := hh
      exact ⟨hs, hna, θ, hP⟩) hrawd
  rw [hlab₁] at hΛlab
  refine ⟨hperf, lab₂, hΛ.mp hΛlab, ?_⟩
  refine largeEvenRawDatum_mono (fun R _ I F hh => ?_) ((hraw _).1 hraw₁)
  obtain ⟨hs, hna, θ, hP⟩ := hh
  exact ⟨hs, hna, θ, rfl, hP⟩

theorem largeEvenMarking_D3_iff_A3 {X : Type*} [Group X] (n : ℕ) {P : LargeEvenMarkCont X} :
    LargeEvenMarking X (fun lab R _ I F θ => lab = (⟨.D, 3, n⟩ : LargeEvenLabel) ∧ P R I F θ) ↔
      LargeEvenMarking X (fun lab R _ I F θ => lab = (⟨.A, 3, n⟩ : LargeEvenLabel) ∧ P R I F θ) :=
  ⟨largeEvenMarking_relabel (inLambda2_D3_iff_A3 n) (rawDatum_D3_iff_A3 n),
    largeEvenMarking_relabel (inLambda2_D3_iff_A3 n).symm (fun Q => (rawDatum_D3_iff_A3 n Q).symm)⟩

theorem largeEvenMarking_twD3_iff_twA3 {X : Type*} [Group X] (n : ℕ)
    {P : LargeEvenMarkCont X} :
    LargeEvenMarking X
        (fun lab R _ I F θ => lab = (⟨.twD, 3, n⟩ : LargeEvenLabel) ∧ P R I F θ) ↔
      LargeEvenMarking X
        (fun lab R _ I F θ => lab = (⟨.twA, 3, n⟩ : LargeEvenLabel) ∧ P R I F θ) :=
  ⟨largeEvenMarking_relabel (inLambda2_twD3_iff_twA3 n) (rawDatum_twD3_iff_twA3 n),
    largeEvenMarking_relabel (inLambda2_twD3_iff_twA3 n).symm
      (fun Q => (rawDatum_twD3_iff_twA3 n Q).symm)⟩

theorem largeEvenMarking_twD2_iff_A1 {X : Type*} [Group X] (n : ℕ)
    {P : LargeEvenMarkCont X} :
    LargeEvenMarking X
        (fun lab R _ I F θ => lab = (⟨.twD, 2, n⟩ : LargeEvenLabel) ∧ P R I F θ) ↔
      LargeEvenMarking X
        (fun lab R _ I F θ => lab = (⟨.A, 1, 2 * n⟩ : LargeEvenLabel) ∧ P R I F θ) :=
  ⟨largeEvenMarking_relabel (inLambda2_twD2_iff_A1 n) (rawDatum_twD2_iff_A1 n),
    largeEvenMarking_relabel (inLambda2_twD2_iff_A1 n).symm
      (fun Q => (rawDatum_twD2_iff_A1 n Q).symm)⟩

theorem q1Quotient_inner_actor_component_action
    {H R : Type} [Group H] [Group R] (e : H ≃* R)
    (hconj : Function.Injective (MulAut.conj : H →* MulAut H))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (A : Subgroup (MulAut R))
    (hA : CFSG.Open.IsElemAbelian p A)
    (hAI : ∀ a ∈ A, a ∈ LargeEvenInnSet R)
    (u : MulAut R) (hu : u ∈ A) (huord : orderOf u = p)
    (J : Subgroup R) (hJ : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u))
    (hdonor : ∀ (s : H), Odd (orderOf s) → ∀ C : Subgroup H,
      CFSG.Assembly.IsComponentOf C (Subgroup.centralizer ({s} : Set H)) →
      Subgroup.centralizer ({s} : Set H) ≤ Subgroup.normalizer (C : Set H) ∧
      LargeEvenMarking ↥C (fun _ _ _ I _ θ =>
        ∀ ε ∈ Subgroup.centralizer ({s} : Set H), ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' : ↥C => (l' : H) = ε⁻¹ * l * ε) φ)) :
    LargeEvenMarking J (fun _ _ _ IJ _ θJ =>
      True ∧ (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧ GGAutsInduceOn A J θJ IJ) := by
  classical
  obtain ⟨r₀, hr₀⟩ := hAI u hu
  let s : H := e.symm r₀
  let AH : Subgroup (MulAut H) := A.map (MulAut.congr e.symm).toMonoidHom
  let uH : MulAut H := MulAut.congr e.symm u
  let C : Subgroup H := J.map e.symm.toMonoidHom
  have hs : MulAut.conj s = uH := by
    change MulAut.conj (e.symm r₀) = MulAut.congr e.symm u
    rw [← hr₀]
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hsord : orderOf s = p := by
    have h1 : orderOf (MulAut.conj s) = orderOf s :=
      orderOf_injective (MulAut.conj : H →* MulAut H) hconj s
    rw [hs, gdf_orderOf_congr e.symm u, huord] at h1
    exact h1.symm
  have hsodd : Odd (orderOf s) := by
    rw [hsord]
    exact hp.odd_of_ne_two hp2
  have hAHinn : (AH : Set (MulAut H)) ⊆ LargeEvenInnSet H := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨r, hr⟩ := hAI a ha
    refine ⟨e.symm r, ?_⟩
    change MulAut.conj (e.symm r) = MulAut.congr e.symm a
    rw [← hr]
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hcommH : ∀ a ∈ AH, Commute a uH := by
    rintro _ ⟨a, ha, rfl⟩
    have : IsMulCommutative ↥A := hA.1
    have hcomm : Commute a u :=
      congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥A) (⟨u, hu⟩ : ↥A))
    exact hcomm.map (MulAut.congr e.symm)
  have hfix : ggAutFixedSubgroup uH = Subgroup.centralizer ({s} : Set H) := by
    rw [show uH = MulAut.conj s from hs.symm]
    exact ggAutFixedSubgroup_mulAut_conj s
  have hCH : CFSG.Open.IsComponentOf C (ggAutFixedSubgroup uH) := by
    have h := isComponentOf_map_mulEquiv e.symm (CFSG.Assembly.isComponentOf_iff_open.mpr hJ)
    change CFSG.Assembly.IsComponentOf (J.map e.symm.toMonoidHom)
      ((ggAutFixedSubgroup u).map e.symm.toMonoidHom) at h
    rw [← gdf_fixed_congr e.symm u] at h
    exact CFSG.Assembly.isComponentOf_iff_open.mp h
  have hdonor' : ∀ C' : Subgroup H, CFSG.Assembly.IsComponentOf C'
      (ggAutFixedSubgroup uH) →
      Subgroup.centralizer ({s} : Set H) ≤ Subgroup.normalizer (C' : Set H) ∧
      LargeEvenMarking ↥C' (fun _ _ _ I _ θ =>
        ∀ ε ∈ Subgroup.centralizer ({s} : Set H), ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' : ↥C' => (l' : H) = ε⁻¹ * l * ε) φ) := by
    intro C' hC'
    rw [hfix] at hC'
    exact hdonor s hsodd C' hC'
  obtain ⟨hnorm, hmark⟩ :=
    ggAutFixedSubgroup_inner_actor (C := C) hconj hAHinn hs hcommH hdonor'
      (CFSG.Assembly.isComponentOf_iff_open.mpr hCH)
  have htrans := largeEvenMarking_action_mulEquiv (C := C) e ⟨hnorm, hmark⟩
  have hCJ : C.map e.toMonoidHom = J := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨j, hj, hjc⟩ := hc
      rw [← hjc]
      simpa using hj
    · intro hx
      exact ⟨e.symm x, ⟨x, hx, rfl⟩, by simp⟩
  have hAJ : AH.map (MulAut.congr e).toMonoidHom = A := by
    ext a
    constructor
    · rintro ⟨aH, ⟨a', ha', h1⟩, h2⟩
      rw [← h2, ← h1]
      have hcongr : MulAut.congr e (MulAut.congr e.symm a') = a' := by
        ext x; simp [MulAut.congr_apply]
      change MulAut.congr e (MulAut.congr e.symm a') ∈ A
      rw [hcongr]
      exact ha'
    · intro ha
      exact ⟨MulAut.congr e.symm a, ⟨a, ha, rfl⟩, by ext x; simp [MulAut.congr_apply]⟩
  rw [hAJ, hCJ] at htrans
  exact largeEvenMarking_mono (fun _ _ _ _ _ _ hθ => ⟨trivial, htrans.1, hθ⟩) htrans.2

theorem q1StrongDonor_of_mulEquiv
    {H R : Type} [Group H] [Group R] (e : H ≃* R)
    (hdonor : ∀ s : R, Odd (orderOf s) → ∀ C : Subgroup R,
      CFSG.Assembly.IsComponentOf C (Subgroup.centralizer ({s} : Set R)) →
      Subgroup.centralizer ({s} : Set R) ≤ Subgroup.normalizer (C : Set R) ∧
      LargeEvenMarking ↥C (fun _ _ _ I _ θ =>
        ∀ ε ∈ Subgroup.centralizer ({s} : Set R), ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' : ↥C => (l' : R) = ε⁻¹ * l * ε) φ)) :
    ∀ s : H, Odd (orderOf s) → ∀ C : Subgroup H,
      CFSG.Assembly.IsComponentOf C (Subgroup.centralizer ({s} : Set H)) →
      Subgroup.centralizer ({s} : Set H) ≤ Subgroup.normalizer (C : Set H) ∧
      LargeEvenMarking ↥C (fun _ _ _ I _ θ =>
        ∀ ε ∈ Subgroup.centralizer ({s} : Set H), ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' : ↥C => (l' : H) = ε⁻¹ * l * ε) φ) := by
  intro s hs C hC
  let C' : Subgroup R := C.map e.toMonoidHom
  let eC : ↥C ≃* ↥C' := C.equivMapOfInjective e.toMonoidHom e.injective
  have hs' : Odd (orderOf (e s)) := by
    rwa [MulEquiv.orderOf_eq]
  have hcent : (Subgroup.centralizer ({s} : Set H)).map e.toMonoidHom =
      Subgroup.centralizer ({e s} : Set R) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y * s = s * y :=
        Subgroup.mem_centralizer_singleton_iff.mp (by simpa using hy)
      change e.toMonoidHom y ∈ Subgroup.centralizer ({e s} : Set R)
      rw [Subgroup.mem_centralizer_singleton_iff]
      change e y * e s = e s * e y
      calc e y * e s = e (y * s) := (map_mul e y s).symm
        _ = e (s * y) := congrArg e hy'
        _ = e s * e y := map_mul e s y
    · intro hx
      have hx' : x * e s = e s * x :=
        Subgroup.mem_centralizer_singleton_iff.mp (by simpa using hx)
      refine ⟨e.symm x, ?_, by simp⟩
      change e.symm x ∈ Subgroup.centralizer ({s} : Set H)
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using hx'
  have hC' : CFSG.Assembly.IsComponentOf C' (Subgroup.centralizer ({e s} : Set R)) := by
    have h := isComponentOf_map_mulEquiv e hC
    rwa [hcent] at h
  obtain ⟨hnorm', hmark'⟩ := hdonor (e s) hs' C' hC'
  refine ⟨?_, ?_⟩
  · have hnormmap : (Subgroup.centralizer ({s} : Set H)).map e.toMonoidHom ≤
        Subgroup.normalizer (C.map e.toMonoidHom : Set R) := by
      rw [hcent]
      exact hnorm'
    intro x hx
    have hx' : e x ∈ (Subgroup.normalizer (C : Set H)).map e.toMonoidHom := by
      rw [Subgroup.map_normalizer_eq_of_bijective C e.bijective]
      exact hnormmap (Subgroup.mem_map_of_mem e.toMonoidHom hx)
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
    rwa [e.injective hyx] at hy
  · refine largeEvenMarking_congr eC ?_ hmark'
    intro lab R0 instR I F θ' hθ' ε hε
    obtain ⟨φ, hφI, hind⟩ := hθ' (e ε) (by
      have hε' : ε * s = s * ε :=
        Subgroup.mem_centralizer_singleton_iff.mp (by simpa using hε)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc e ε * e s = e (ε * s) := (map_mul e ε s).symm
        _ = e (s * ε) := congrArg e hε'
        _ = e s * e ε := map_mul e s ε)
    refine ⟨φ, hφI, ?_⟩
    refine (largeEvenInduces_congr_equiv eC θ'
      (fun l l' : ↥C => (l' : H) = ε⁻¹ * l * ε)
      (fun x x' : ↥C' => (x' : R) = (e ε)⁻¹ * x * (e ε)) ?_ φ).2 hind
    intro l l'
    constructor
    · intro h
      have hmem : ε⁻¹ * (l : H) * ε ∈ C := by
        rw [← h]
        exact l'.2
      have h' : l' = ⟨ε⁻¹ * (l : H) * ε, hmem⟩ := Subtype.ext h
      rw [h']
      change e (ε⁻¹ * (l : H) * ε) = (e ε)⁻¹ * e (l : H) * e ε
      simp only [map_mul, map_inv]
    · intro h
      apply e.injective
      simp only [map_mul, map_inv]
      change ((eC l' : ↥C') : R) = (e ε)⁻¹ * ((eC l : ↥C') : R) * e ε
      exact h

theorem q1RToralTransfer_DTwD_low :
    Q1RToralTransfer (fun _ _ _ => True) LowDTwD (fun _ _ _ => True) := by
  intro p hp hp2 lab hΛ hS
  obtain ⟨-, htag, hrank⟩ := hS
  intro Q hQ
  rcases lab with ⟨tag, rank, n⟩
  dsimp only at htag hrank
  rcases htag with rfl | rfl
  ·
    dsimp only [LargeEvenInLambda2] at hΛ
    obtain ⟨hn1, h3le⟩ := hΛ
    have h3 : rank = 3 := by omega
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
    rw [if_pos h3] at hQ ⊢
    obtain ⟨K, fieldK, finiteK, hK, hQK⟩ := hQ
    let : Field K := fieldK
    let : Finite K := finiteK
    have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
    have hIinn : LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 4) K)) Set.univ ⊆
        LargeEvenInnSet (LargeEvenProj (LargeEvenSLGroup (Fin 4) K)) := by
      refine CFSG.StandardType.matConjImage_gl_subset_inn (K := K) (d := 4) ?_
      have hcard : Nat.card Kˣ = 2 ^ n - 1 := by rw [Nat.card_units, hK]
      rw [hcard]
      exact Nat.Coprime.pow_right 2
        (Nat.coprime_two_right.mpr (CFSG.StandardType.ggOdd_two_pow_sub_one hn1))
    have hscal : (LargeEvenScalars (Fin 4) K).subgroupOf (CFSG.Open.StatedSL 4 K) = ⊥ := by
      rw [CFSG.Assembly.largeEvenScalars_eq_statedScalars]
      rw [eq_bot_iff]
      intro g hg
      obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hg
      have hdet := CFSG.Open.StatedAPI.det_of_mem_statedSL g.2
      rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
      have hc1 : (c : K) = 1 := CFSG.SectionRank.EvenCover.eq_one_of_det_scalar_four hdet
      rw [Subgroup.mem_bot]
      apply Subtype.ext
      rw [← hc]
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_scalar, hc1, map_one]
      rfl
    have hscalH : (LargeEvenScalars (Fin 4) K).subgroupOf (LargeEvenSLGroup (Fin 4) K) = ⊥ := by
      rw [CFSG.Assembly.largeEvenSLGroup_eq_statedSL]
      exact hscal
    have hZ : Subgroup.center (CFSG.Open.StatedSL 4 K) = ⊥ := by
      rw [CFSG.LieType.SemisimpleCentralizers.Held.center_statedSL_eq]
      exact hscal
    have hZH : Subgroup.center (LargeEvenSLGroup (Fin 4) K) = ⊥ := by
      have eG : LargeEvenSLGroup (Fin 4) K ≃* CFSG.Open.StatedSL 4 K :=
        MulEquiv.subgroupCongr (CFSG.Assembly.largeEvenSLGroup_eq_statedSL 4)
      have hmap := Subgroup.map_center_eq eG
      rw [hZ] at hmap
      exact (Subgroup.map_eq_bot_iff_of_injective (H := Subgroup.center _)
        (f := eG.toMonoidHom) eG.injective).mp hmap
    have hconj : Function.Injective (MulAut.conj :
        LargeEvenSLGroup (Fin 4) K →* MulAut (LargeEvenSLGroup (Fin 4) K)) :=
      CFSG.StandardType.mulAut_conj_injective hZH
    let e : LargeEvenSLGroup (Fin 4) K ≃* LargeEvenProj (LargeEvenSLGroup (Fin 4) K) :=
      ((QuotientGroup.quotientMulEquivOfEq hscalH).trans
        (QuotientGroup.quotientBot (G := LargeEvenSLGroup (Fin 4) K))).symm
    refine ⟨K, fieldK, finiteK, hK, hQK, ?_⟩
    intro A hA hAI _ u hu huord J hJ
    exact q1Quotient_inner_actor_component_action (H := ↥(LargeEvenSLGroup (Fin 4) K)) e hconj
      hp hp2 A hA (fun a ha => hIinn (hAI a ha)) u hu huord J hJ
      (q1StrongDonor_of_mulEquiv
        (MulEquiv.subgroupCongr (CFSG.Assembly.largeEvenSLGroup_eq_statedSL 4)) (by
          intro s hs C hC
          obtain ⟨hnorm, hmark⟩ :=
            CFSG.StandardType.ggE0Concl_centralizer_statedSL_strong (N := 4) (F := K) s hs (C := C) hC
          exact ⟨hnorm, largeEvenMarking_mono (fun _ _ _ _ _ _ hθ => hθ.2) hmark⟩))
  ·
    dsimp only [LargeEvenInLambda2] at hΛ
    obtain ⟨hn1, h2le⟩ := hΛ
    by_cases hr2 : rank = 2
    ·
      dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
      rw [if_pos hr2] at hQ ⊢
      obtain ⟨K, fieldK, finiteK, hK, hQK⟩ := hQ
      let : Field K := fieldK
      let : Finite K := finiteK
      have hK2 : Nat.card K = 2 ^ (2 * n) := by
        rw [hK, ← pow_mul, Nat.mul_comm]
      have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK2
      have hIinn : LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K)) Set.univ ⊆
          LargeEvenInnSet (LargeEvenProj (LargeEvenSLGroup (Fin 2) K)) := by
        refine CFSG.StandardType.matConjImage_gl_subset_inn (K := K) (d := 2) ?_
        have hcard : Nat.card Kˣ = (2 ^ n) ^ 2 - 1 := by rw [Nat.card_units, hK]
        have hodd : Odd ((2 ^ n) ^ 2 - 1) := by
          rw [← pow_mul]
          exact CFSG.StandardType.ggOdd_two_pow_sub_one (by omega : 1 ≤ n * 2)
        rw [hcard]
        exact Nat.coprime_two_right.mpr hodd
      have hscal : (LargeEvenScalars (Fin 2) K).subgroupOf (CFSG.Open.StatedSL 2 K) = ⊥ :=
        CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot
      have hscalH : (LargeEvenScalars (Fin 2) K).subgroupOf (LargeEvenSLGroup (Fin 2) K) = ⊥ := by
        rw [CFSG.Assembly.largeEvenSLGroup_eq_statedSL]
        exact hscal
      have hZ : Subgroup.center (CFSG.Open.StatedSL 2 K) = ⊥ := by
        rw [CFSG.LieType.SemisimpleCentralizers.Held.center_statedSL_eq]
        exact hscal
      have hZH : Subgroup.center (LargeEvenSLGroup (Fin 2) K) = ⊥ := by
        have eG : LargeEvenSLGroup (Fin 2) K ≃* CFSG.Open.StatedSL 2 K :=
          MulEquiv.subgroupCongr (CFSG.Assembly.largeEvenSLGroup_eq_statedSL 2)
        have hmap := Subgroup.map_center_eq eG
        rw [hZ] at hmap
        exact (Subgroup.map_eq_bot_iff_of_injective (H := Subgroup.center _)
          (f := eG.toMonoidHom) eG.injective).mp hmap
      have hconj : Function.Injective (MulAut.conj :
          LargeEvenSLGroup (Fin 2) K →* MulAut (LargeEvenSLGroup (Fin 2) K)) :=
        CFSG.StandardType.mulAut_conj_injective hZH
      let e : LargeEvenSLGroup (Fin 2) K ≃* LargeEvenProj (LargeEvenSLGroup (Fin 2) K) :=
        ((QuotientGroup.quotientMulEquivOfEq hscalH).trans
          (QuotientGroup.quotientBot (G := LargeEvenSLGroup (Fin 2) K))).symm
      refine ⟨K, fieldK, finiteK, hK, hQK, ?_⟩
      intro A hA hAI _ u hu huord J hJ
      exact q1Quotient_inner_actor_component_action (H := ↥(LargeEvenSLGroup (Fin 2) K)) e hconj
        hp hp2 A hA (fun a ha => hIinn (hAI a ha)) u hu huord J hJ
        (q1StrongDonor_of_mulEquiv
          (MulEquiv.subgroupCongr (CFSG.Assembly.largeEvenSLGroup_eq_statedSL 2)) (by
            intro s hs C hC
            obtain ⟨hnorm, hmark⟩ :=
              CFSG.StandardType.ggE0Concl_centralizer_statedSL_strong (N := 2) (F := K) s hs (C := C) hC
            exact ⟨hnorm, largeEvenMarking_mono (fun _ _ _ _ _ _ hθ => hθ.2) hmark⟩))
    ·
      have hr3 : rank = 3 := by omega
      dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
      rw [if_neg hr2, if_pos hr3] at hQ ⊢
      obtain ⟨K, fieldK, finiteK, hK, hQK⟩ := hQ
      let : Field K := fieldK
      let : Finite K := finiteK
      have hK2 : Nat.card K = 2 ^ (2 * n) := by
        rw [hK, ← pow_mul, Nat.mul_comm]
      have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK2
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hIinn : LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
          (LargeEvenGUSet (Fin 4) K (2 ^ n)) ⊆
          LargeEvenInnSet (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n))) :=
        CFSG.StandardType.TableB.matConjImage_gu_subset_inn (n := n) (d := 4) hK
          (CFSG.StandardType.coprime_two_pow_add_one_four hn1)
      have hscal : (LargeEvenScalars (Fin 4) K).subgroupOf
          (CFSG.Open.StatedSU 4 (2 ^ n) K) = ⊥ :=
        CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedSU_four_eq_bot (q := 2 ^ n)
      have hZ : Subgroup.center (CFSG.Open.StatedSU 4 (2 ^ n) K) = ⊥ := by
        have hq := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
          (F := K) (p := 2) (f := n) (n := 4) hK (by norm_num) (by simp)).2
        rw [hq]
        exact CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedSU_four_eq_bot (q := 2 ^ n)
      have hconj : Function.Injective (MulAut.conj :
          CFSG.Open.StatedSU 4 (2 ^ n) K →* MulAut (CFSG.Open.StatedSU 4 (2 ^ n) K)) :=
        CFSG.StandardType.mulAut_conj_injective hZ
      let e : CFSG.Open.StatedSU 4 (2 ^ n) K ≃*
          LargeEvenProj (CFSG.Open.StatedSU 4 (2 ^ n) K) :=
        ((QuotientGroup.quotientMulEquivOfEq hscal).trans
          (QuotientGroup.quotientBot (G := CFSG.Open.StatedSU 4 (2 ^ n) K))).symm
      refine ⟨K, fieldK, finiteK, hK, hQK, ?_⟩
      intro A hA hAI _ u hu huord J hJ
      exact q1Quotient_inner_actor_component_action e hconj hp hp2 A hA
        (fun a ha => hIinn (hAI a ha)) u hu huord J hJ (by
          intro s hs C hC
          obtain ⟨hnorm, hmark⟩ :=
            CFSG.StandardType.ggE0Concl_centralizer_statedSU_strong (N := 4) (Q := 2 ^ n)
              (E := K) hK s hs (C := C) hC
          exact ⟨hnorm, largeEvenMarking_mono (fun _ _ _ _ _ _ hθ => hθ.2) hmark⟩)

end CFSG.StandardType.Q1DSmall

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggInnerDiagOnLabel_D3_to_A3 {G : Type} [Group G] {Bs L : Subgroup G} {p : ℕ}
    {S : ℕ → Prop}
    (h : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .D ∧ lab.rank = 3 ∧ S lab.n) p Bs L) :
    GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ lab.rank = 3 ∧ S lab.n) p Bs L := by
  classical
  obtain ⟨hperf, lab, hΛ, hraw⟩ := h
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨_, _, _, _, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, _, _, hP⟩ := hQ
  obtain ⟨hS0, _, _⟩ := hP
  obtain ⟨htag, hrank, hS⟩ : tag = .D ∧ rank = 3 ∧ S n := by
    simpa only using hS0
  subst htag
  subst hrank
  let lab₁ : LargeEvenLabel := ⟨.D, 3, n⟩
  let lab₂ : LargeEvenLabel := ⟨.A, 3, n⟩
  let P : Q1DSmall.LargeEvenMarkCont ↥L := fun _ _ I _ θ => S n ∧
      Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ
  have hΛ₁ : LargeEvenInLambda2 lab₁ := by
    simpa only [lab₁] using hΛ
  have hrawFix : LargeEvenRawDatum lab₁ (fun R _ I F =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* R, lab₁ = lab₁ ∧ P R I F θ) := by
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, hS, hN, hInd⟩
    exact ⟨hs, hna, θ, rfl, hS.2.2, hN, hInd⟩
  have hFix : LargeEvenMarking ↥L (fun lab R _ I F θ => lab = lab₁ ∧ P R I F θ) :=
    ⟨hperf, lab₁, hΛ₁, hrawFix⟩
  have hTarget : LargeEvenMarking ↥L (fun lab R _ I F θ => lab = lab₂ ∧ P R I F θ) :=
    (Q1DSmall.largeEvenMarking_D3_iff_A3 n).1 hFix
  unfold GGInnerDiagOnLabel
  refine largeEvenMarking_mono ?_ hTarget
  rintro lab R _ I F θ ⟨hlab, hS, hN, hInd⟩
  rw [hlab]
  exact ⟨⟨rfl, rfl, hS⟩, hN, hInd⟩

theorem ggInnerDiagOnLabel_twD_to_twA {G : Type} [Group G] {Bs L : Subgroup G} {p : ℕ}
    {S : ℕ → Prop}
    (h : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twD ∧ lab.rank = 3 ∧ S lab.n) p Bs L) :
    GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 3 ∧ S lab.n) p Bs L := by
  classical
  obtain ⟨hperf, lab, hΛ, hraw⟩ := h
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨_, _, _, _, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, _, _, hP⟩ := hQ
  obtain ⟨hS0, _, _⟩ := hP
  obtain ⟨htag, hrank, hS⟩ : tag = .twD ∧ rank = 3 ∧ S n := by
    simpa only using hS0
  subst htag
  subst hrank
  let lab₁ : LargeEvenLabel := ⟨.twD, 3, n⟩
  let lab₂ : LargeEvenLabel := ⟨.twA, 3, n⟩
  let P : Q1DSmall.LargeEvenMarkCont ↥L := fun _ _ I _ θ => S n ∧
      Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ
  have hΛ₁ : LargeEvenInLambda2 lab₁ := by
    simpa only [lab₁] using hΛ
  have hrawFix : LargeEvenRawDatum lab₁ (fun R _ I F =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* R, lab₁ = lab₁ ∧ P R I F θ) := by
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, hS, hN, hInd⟩
    exact ⟨hs, hna, θ, rfl, hS.2.2, hN, hInd⟩
  have hFix : LargeEvenMarking ↥L (fun lab R _ I F θ => lab = lab₁ ∧ P R I F θ) :=
    ⟨hperf, lab₁, hΛ₁, hrawFix⟩
  have hTarget : LargeEvenMarking ↥L (fun lab R _ I F θ => lab = lab₂ ∧ P R I F θ) :=
    (Q1DSmall.largeEvenMarking_twD3_iff_twA3 n).1 hFix
  unfold GGInnerDiagOnLabel
  refine largeEvenMarking_mono ?_ hTarget
  rintro lab R _ I F θ ⟨hlab, hS, hN, hInd⟩
  rw [hlab]
  exact ⟨⟨rfl, rfl, hS⟩, hN, hInd⟩

end CFSG.StandardType

namespace CFSG.StandardType.S2MathAs51642Interfaces

open CFSG CFSG.Assembly
open CFSG.StandardType.Q1DSmall

theorem q1RToralTransfer_DTwD :
    Q1RToralTransfer (fun _ _ _ => True)
      (fun p lab => CenterPrimeTo p lab ∧ (lab.tag = .D ∨ lab.tag = .twD))
      (fun _ _ _ => True) := by
  intro p hp hp2 lab hlab hS
  by_cases h4 : 4 ≤ lab.rank
  · exact q1RToralTransfer_DTwD_high p hp hp2 lab hlab ⟨hS.1, hS.2, h4⟩
  · exact q1RToralTransfer_DTwD_low p hp hp2 lab hlab ⟨hS.1, hS.2, by omega⟩

theorem q1ToralActionTransfer_DTwD :
    Q1ToralActionTransfer (fun _ _ _ => True)
      (fun p lab => CenterPrimeTo p lab ∧ (lab.tag = .D ∨ lab.tag = .twD))
      (fun _ _ _ => True) :=
  q1ToralActionTransfer_of_rToral q1RToralTransfer_DTwD

theorem q1SelectedTransfer_DTwD :
    Q1SelectedTransfer
      (fun p lab => CenterPrimeTo p lab ∧ (lab.tag = .D ∨ lab.tag = .twD))
      (fun _ _ _ => True) :=
  q1SelectedTransfer_of_toral q1ToralActionTransfer_DTwD (by
    intro G _ _ p B Bs x L D J hcfg P hP
    exact largeEvenMarking_mono
      (fun lab R _ I F θ hθ => ⟨hθ, by intro hS hN hact; trivial⟩) hP)

theorem q1DTwDInnerDiag_holds :
    GGBstarInnerDiagJInputOn
      (fun p lab => CenterPrimeTo p lab ∧ (lab.tag = .D ∨ lab.tag = .twD)) :=
  q1On_of_selectedTransfer q1SelectedTransfer_DTwD

theorem ggBstarInnerDiagJInputOn_of_not_DTwD {S : ℕ → LargeEvenLabel → Prop}
    (hrest : GGBstarInnerDiagJInputOn (fun p lab => S p lab ∧
      ¬ (CenterPrimeTo p lab ∧ (lab.tag = .D ∨ lab.tag = .twD)))) :
    GGBstarInnerDiagJInputOn S := by
  classical
  intro G _ _ p B Bs x L D J hcfg hmark
  refine (q1On_or hrest q1DTwDInnerDiag_holds) G p B Bs x L D J hcfg ?_
  refine largeEvenMarking_mono (fun lab R _ I F θ h => ⟨?_, h.2⟩) hmark
  by_cases hD : CenterPrimeTo p lab ∧ (lab.tag = .D ∨ lab.tag = .twD)
  · exact Or.inr hD
  · exact Or.inl ⟨h.1, hD⟩

end CFSG.StandardType.S2MathAs51642Interfaces

end
