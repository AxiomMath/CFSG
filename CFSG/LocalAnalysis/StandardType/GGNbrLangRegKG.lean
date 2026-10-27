module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangRegStepZero
public import CFSG.LocalAnalysis.StandardType.GGNbrLangKGInputs
public import CFSG.LocalAnalysis.StandardType.GGNbrLangAxisOn
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherAssembly

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def KGRawFieldCyclic : LargeEvenRawCont := fun R _ _ F => IsCyclic (Subgroup.closure F)

@[expose] def KGRawFieldCyclicOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab → S p lab →
    LargeEvenLabelAll lab KGRawFieldCyclic

theorem ggRegKG_markingAll_guard {S : ℕ → LargeEvenLabel → Prop} {P : LargeEvenRawCont} {p : ℕ}
    (h : ∀ lab, LargeEvenInLambda2 lab → S p lab → LargeEvenLabelAll lab P) (K : Type*)
    [Group K] : GGMarkingAll (K := K) fun lab R _ I F _ => S p lab → P R I F := by
  intro Q hQ
  obtain ⟨hX, lab, hlab, hraw⟩ := hQ
  by_cases hs : S p lab
  · refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ (h lab hlab hs _ hraw)⟩
    rintro R _ I F ⟨⟨hsi, hna, θ, hθ⟩, hc⟩
    exact ⟨hsi, hna, θ, hθ, fun _ => hc⟩
  · refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hsi, hna, θ, hθ⟩
    exact ⟨hsi, hna, θ, hθ, fun h' => absurd h' hs⟩

theorem ggMarkingAll_kgRawFieldCyclic {S : ℕ → LargeEvenLabel → Prop} (h : KGRawFieldCyclicOn S)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (K : Type*) [Group K] :
    GGMarkingAll (K := K) fun lab R _ I F _ => S p lab → KGRawFieldCyclic R I F :=
  ggRegKG_markingAll_guard (fun lab hlab hs => h p lab hp hp2 hlab hs) K

theorem ggRegKG_markingAll_perfect_simple (K : Type*) [Group K] :
    GGMarkingAll (K := K) fun _ R _ _ _ _ =>
      commutator K = ⊤ ∧ IsSimpleGroup R ∧ ∃ a b : R, a * b ≠ b * a := by
  intro P hP
  obtain ⟨hX, lab, hlab, hraw⟩ := hP
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  exact ⟨hs, hna, θ, hθ, hX, hs, hna⟩

theorem ggRegKG_markingAll_of_labelAll {K : Type*} [Group K] {P' : LargeEvenRawCont}
    (hall : ∀ lab, LargeEvenInLambda2 lab → LargeEvenLabelAll lab P') :
    GGMarkingAll (K := K) fun _ R _ I F _ => P' R I F := by
  intro P hP
  obtain ⟨hX, lab, hlab, hraw⟩ := hP
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ (hall lab hlab _ hraw)⟩
  rintro R _ I F ⟨⟨hs, hna, θ, hθ⟩, hP'⟩
  exact ⟨hs, hna, θ, hθ, hP'⟩

theorem ggRegKG_markingAll_of_labelAll_simple {K : Type*} [Group K]
    {P' : LargeEvenRawCont}
    (hall : ∀ lab, LargeEvenInLambda2 lab → LargeEvenLabelAll lab (LargeEvenSimpleGuard P')) :
    GGMarkingAll (K := K) fun _ R _ I F _ => P' R I F := by
  intro P hP
  obtain ⟨hX, lab, hlab, hraw⟩ := hP
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ (hall lab hlab _ hraw)⟩
  rintro R _ I F ⟨⟨hs, hna, θ, hθ⟩, hP'⟩
  exact ⟨hs, hna, θ, hθ, hP' hs hna⟩

theorem ggRegKG_markingAll_and {K : Type*} [Group K] {Q₁ Q₂ : LargeEvenMarkProp K}
    (h₁ : GGMarkingAll Q₁) (h₂ : GGMarkingAll Q₂) :
    GGMarkingAll fun lab R _ I F θ => Q₁ lab R I F θ ∧ Q₂ lab R I F θ :=
  NbrLangTypeA.ggMarkingAll_of_and h₁ h₂ fun _ _ _ _ _ _ a b => ⟨a, b⟩

@[expose] def ggBsAut {G : Type} [Group G] {Bs K : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) : ↥Bs →* MulAut ↥K :=
  K.normalizerMonoidHom.comp (Subgroup.inclusion hN)

theorem ggBsAut_range_isElemAbelian {G : Type} [Group G] {p : ℕ} {Bs K : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    IsElemAbelian p (ggBsAut hN).range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨_, x, rfl⟩ := a
    obtain ⟨_, y, rfl⟩ := b
    have hxy : x * y = y * x := Subtype.ext (TableB.IsElemAbelian.comm hBs x.2 y.2)
    refine Subtype.ext ?_
    show ggBsAut hN x * ggBsAut hN y = ggBsAut hN y * ggBsAut hN x
    rw [← map_mul, ← map_mul, hxy]
  · rintro _ ⟨x, rfl⟩
    have hx : x ^ p = 1 := Subtype.ext (hBs.2 x x.2)
    rw [← map_pow, hx, map_one]

@[expose] def KGLangTorusConcl (p : ℕ) {K R : Type} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (I : Set (MulAut R)) (A : Subgroup (MulAut K))
    (α₀ : MulAut K) : Prop :=
  ∃ T : Subgroup K, (∀ a ∈ T, ∀ c ∈ T, a * c = c * a) ∧ (∀ t : K, α₀ t ∈ T ↔ t ∈ T) ∧
    (∀ α ∈ A, kgInducedAut θ α ∈ I → ∀ t ∈ T, α t = t) ∧
    (∀ t ∈ T, α₀ t = t → ∃ s ∈ T, t = ((List.range p).map fun i => (α₀ ^ i) s).prod) ∧
    ∃ e ∈ T, e ≠ 1 ∧ e ^ p = 1 ∧ ∀ α ∈ A, α e = e

theorem ggNbrLangRegCore_of_data {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs : Subgroup G} (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {K : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    {R : Type} [Group R] {I : Set (MulAut R)} (θ : ↥K ⧸ Subgroup.center ↥K ≃* R)
    (hinn : ∀ r : R, MulAut.conj r ∈ I) (b₀ : G) (hb₀ : b₀ ∈ Bs)
    {B₀ : Subgroup G} (hB₀ : B₀ ≤ Bs)
    (hmem : ∀ (b : G) (hb : b ∈ Bs), b ∈ B₀ ↔ ggLAut K θ ⟨b, hN hb⟩ ∈ I)
    (hKG : KGLangTorusConcl p θ I (ggBsAut hN).range (ggBsAut hN ⟨b₀, hb₀⟩)) :
    ∃ T : Subgroup G, T ≤ Subgroup.centralizer (B₀ : Set G) ∧
      (∀ a ∈ T, ∀ c ∈ T, a * c = c * a) ∧
      b₀ ∈ Subgroup.normalizer (T : Set G) ∧
      (∀ t ∈ T, b₀ * t * b₀⁻¹ = t → ∃ s ∈ T,
        t = ((List.range p).map fun i => b₀ ^ i * s * (b₀ ^ i)⁻¹).prod) ∧
      ∃ e ∈ B₀ ⊓ T, e ≠ 1 := by
  let ν : ↥Bs →* MulAut ↥K := ggBsAut hN
  have hBsK : ∀ (b : ↥Bs) (k : ↥K), ν b k = k → (b : G) * (k : G) = (k : G) * (b : G) := by
    intro b k h
    have h1 : (b : G) * (k : G) * (b : G)⁻¹ = (k : G) := congrArg Subtype.val h
    calc (b : G) * (k : G) = (b : G) * (k : G) * (b : G)⁻¹ * (b : G) := by group
      _ = (k : G) * (b : G) := by rw [h1]
  obtain ⟨T', hT'ab, hT'stab, hT'cent, hT'norm, e', he'T', he'1, he'p, he'fix⟩ := hKG
  refine ⟨T'.map K.subtype, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨t, ht, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbBs : b ∈ Bs := hB₀ hb
    have hbI : ggLAut K θ ⟨b, hN hbBs⟩ ∈ I := (hmem b hbBs).1 hb
    exact hBsK ⟨b, hbBs⟩ t (hT'cent (ν ⟨b, hbBs⟩) ⟨_, rfl⟩ hbI t ht)
  ·
    rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩
    exact congrArg Subtype.val (hT'ab a ha c hc)
  ·
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨ν ⟨b₀, hb₀⟩ t, (hT'stab t).2 ht, rfl⟩
    · rintro ⟨t, ht, hth⟩
      have hhK : h ∈ K := by
        have h1 : b₀ * h * b₀⁻¹ ∈ K := by rw [← hth]; exact t.2
        exact (Subgroup.mem_normalizer_iff.mp (hN hb₀) h).2 h1
      have h2 : ν ⟨b₀, hb₀⟩ ⟨h, hhK⟩ = t := Subtype.ext hth.symm
      refine ⟨⟨h, hhK⟩, (hT'stab ⟨h, hhK⟩).1 ?_, rfl⟩
      rw [h2]
      exact ht
  ·
    rintro _ ⟨t, ht, rfl⟩ hfix
    obtain ⟨s, hs, hts⟩ := hT'norm t ht (Subtype.ext hfix)
    refine ⟨K.subtype s, ⟨s, hs, rfl⟩, ?_⟩
    have h1 := congrArg K.subtype hts
    rw [map_list_prod, List.map_map] at h1
    rw [h1]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    show (((ν ⟨b₀, hb₀⟩ ^ i) s : ↥K) : G) = _
    rw [← map_pow]
    rfl
  ·
    have heBs : (e' : G) ∈ Bs := by
      refine hSC _ (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_) (congrArg Subtype.val he'p)
      exact hBsK ⟨b, hb⟩ e' (he'fix (ν ⟨b, hb⟩) ⟨_, rfl⟩)
    have heB₀ : (e' : G) ∈ B₀ := by
      refine (hmem _ heBs).2 ?_
      have h1 : ggLAut K θ ⟨(e' : G), hN heBs⟩ = MulAut.conj (θ ((⟨(e' : G), e'.2⟩ : ↥K) :
          ↥K ⧸ Subgroup.center ↥K)) := ggLAut_of_mem_outdiag K θ e'.2
      rw [h1]
      exact hinn _
    exact ⟨(e' : G), ⟨heB₀, ⟨e', he'T', rfl⟩⟩, fun h => he'1 (Subtype.ext h)⟩

@[expose] def GGNbrLangRest12NonRegLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrLangRest12Label p lab ∧ ¬ GGNbrLangRegLabel p lab

end CFSG.StandardType
