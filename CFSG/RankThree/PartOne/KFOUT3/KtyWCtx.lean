module

public import CFSG.RankThree.PartOne.KF.WCtx

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU

variable {G M P V Γ : Type} [Group G] [Group M] [Group P] [Group V] [Group Γ] {p : ℕ}
  {L F : Subgroup G} {T : Subgroup M} {act : Γ →* MulAut V}

theorem wctx_ofCentralQuot' (hVexp : ∀ d : V, d ^ p = 1) (SM : WCtx act (⊤ : Subgroup M) T)
    (q : M →* P) (hq : IsCentralPQuot p q)
    (ε : ↥L →* P) (hε : IsCentralPQuot p ε) (hFL : F ≤ L) (hFexp : ∀ f ∈ F, f ^ p = 1)
    (hFT₁ : ∀ t ∈ T, ∃ f : F, ε (Subgroup.inclusion hFL f) = q t)
    (hFT₂ : ∀ f : F, ∃ t ∈ T, ε (Subgroup.inclusion hFL f) = q t) :
    ∃ S : WCtx act L F, ∀ d : V, ε (Subgroup.inclusion hFL (S.tor d)) = q (SM.tor d : M) := by
  classical
  let Fl : F →* ↥L := Subgroup.inclusion hFL
  have hFexp' : ∀ f : F, f ^ p = 1 := fun f => Subtype.ext (hFexp _ f.2)
  have hFlexp : ∀ f : F, Fl f ^ p = 1 := fun f => by rw [← map_pow, hFexp', map_one]
  have hεF_inj : ∀ a b : F, ε (Fl a) = ε (Fl b) → a = b := fun a b h =>
    Subgroup.inclusion_injective hFL (hε.eq_of_map_eq (hFlexp a) (hFlexp b) h)
  have hTexp : ∀ t : T, t ^ p = 1 := by
    intro t
    obtain ⟨d, rfl⟩ := SM.tor.surjective t
    rw [← map_pow, hVexp, map_one]
  have hTexp' : ∀ t ∈ T, t ^ p = 1 := fun t ht => by
    have := congrArg (fun x : T => (x : M)) (hTexp ⟨t, ht⟩)
    simpa using this
  have hex : ∀ d : V, ∃ f : F, ε (Fl f) = q (SM.tor d : M) := fun d =>
    hFT₁ _ (SM.tor d).2
  choose φ hφ using hex
  have hφinj : ∀ d d', φ d = φ d' → d = d' := by
    intro d d' h
    have h1 : q (SM.tor d : M) = q (SM.tor d' : M) := by rw [← hφ, ← hφ, h]
    have h2 : (SM.tor d : M) = (SM.tor d' : M) :=
      hq.eq_of_map_eq (hTexp' _ (SM.tor d).2) (hTexp' _ (SM.tor d').2) h1
    exact SM.tor.injective (Subtype.ext h2)
  have hφmul : ∀ d d', φ (d * d') = φ d * φ d' := by
    intro d d'
    apply hεF_inj
    rw [map_mul, map_mul, hφ, hφ, hφ, map_mul]
    simp only [Subgroup.coe_mul, map_mul]
  have hφone : φ 1 = 1 := by
    apply hεF_inj
    rw [hφ, map_one, map_one, map_one]
    simp
  let φh : V →* F := { toFun := φ, map_one' := hφone, map_mul' := hφmul }
  have hφsurj : Function.Surjective φh := by
    intro f
    obtain ⟨t, ht, hft⟩ := hFT₂ f
    obtain ⟨d, hd⟩ := SM.tor.surjective ⟨t, ht⟩
    refine ⟨d, hεF_inj _ _ ?_⟩
    show ε (Fl (φ d)) = ε (Fl f)
    rw [hφ, hft]
    exact congrArg (fun x : T => q (x : M)) hd
  let tor : V ≃* F := MulEquiv.ofBijective φh ⟨hφinj, hφsurj⟩
  have hrel : ∀ d, ε (Fl (tor d)) = q (SM.tor d : M) := hφ
  have hconj_F : ∀ (l : ↥L) (m : M), m ∈ Subgroup.normalizer (T : Set M) → ε l = q m →
      ∀ f : F, ∃ f' : F, Fl f' = l * Fl f * l⁻¹ := by
    intro l m hm hl f
    obtain ⟨t, ht, hft⟩ := hFT₂ f
    have hmt : m * t * m⁻¹ ∈ T := ((Subgroup.mem_normalizer_iff.mp hm) t).mp ht
    obtain ⟨f', hf'⟩ := hFT₁ _ hmt
    refine ⟨f', hε.eq_of_map_eq (hFlexp f') ?_ ?_⟩
    · have : (l * Fl f * l⁻¹) ^ p = l * (Fl f) ^ p * l⁻¹ := conj_pow
      rw [this, hFlexp, mul_one, mul_inv_cancel]
    · rw [map_mul, map_mul, map_inv, hl, hft, hf']
      simp only [map_mul, map_inv]
  have hnorm_F : ∀ (l : ↥L) (m : M), m ∈ Subgroup.normalizer (T : Set M) → ε l = q m →
      (l : G) ∈ Subgroup.normalizer (F : Set G) := by
    intro l m hm hl
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨f', hf'⟩ := hconj_F l m hm hl ⟨h, hh⟩
      have h3 : (f' : G) = (l : G) * h * (l : G)⁻¹ := congrArg (fun x : ↥L => (x : G)) hf'
      rw [← h3]
      exact f'.2
    · intro hh
      have hm' : m⁻¹ ∈ Subgroup.normalizer (T : Set M) := Subgroup.inv_mem _ hm
      have hl' : ε l⁻¹ = q m⁻¹ := by rw [map_inv, map_inv, hl]
      obtain ⟨f', hf'⟩ := hconj_F l⁻¹ m⁻¹ hm' hl' ⟨(l : G) * h * (l : G)⁻¹, hh⟩
      have h3 : (f' : G) = (l : G)⁻¹ * ((l : G) * h * (l : G)⁻¹) * ((l : G)⁻¹)⁻¹ :=
        congrArg (fun x : ↥L => (x : G)) hf'
      have h2 : (l : G)⁻¹ * ((l : G) * h * (l : G)⁻¹) * ((l : G)⁻¹)⁻¹ = h := by group
      rw [h2] at h3
      rw [← h3]
      exact f'.2
  have haction : ∀ (l : ↥L) (m : M) (hm : m ∈ Subgroup.normalizer (T : Set M)) (hl : ε l = q m)
      (σ : Γ),
      T.normalizerMonoidHom ⟨m, hm⟩ = MulAut.congr SM.tor (act σ) →
      F.normalizerMonoidHom ⟨(l : G), hnorm_F l m hm hl⟩ = MulAut.congr tor (act σ) := by
    intro l m hm hl σ hσ
    refine MulEquiv.ext fun f => ?_
    obtain ⟨d, rfl⟩ := tor.surjective f
    rw [SymCtx.congr_apply_tor]
    apply Subtype.ext
    have h1 : l * Fl (tor d) * l⁻¹ = Fl (tor (act σ d)) := by
      apply hε.eq_of_map_eq
      · have : (l * Fl (tor d) * l⁻¹) ^ p = l * (Fl (tor d)) ^ p * l⁻¹ := conj_pow
        rw [this, hFlexp, mul_one, mul_inv_cancel]
      · exact hFlexp _
      · rw [map_mul, map_mul, map_inv, hl, hrel, hrel]
        have h2 := congrArg (fun x : T => (x : M)) (DFunLike.congr_fun hσ (SM.tor d))
        simp only [SymCtx.congr_apply_tor] at h2
        have h3 : m * (SM.tor d : M) * m⁻¹ = (SM.tor (act σ d) : M) := h2
        rw [← map_inv, ← map_mul, ← map_mul, h3]
    exact congrArg (fun x : ↥L => (x : G)) h1
  have hnormT : ∀ (l : ↥L) (m : M), (l : G) ∈ Subgroup.normalizer (F : Set G) → ε l = q m →
      ∀ t ∈ T, m * t * m⁻¹ ∈ T := by
    intro l m hg hl t ht
    obtain ⟨f, hf⟩ := hFT₁ t ht
    have hmem : (l : G) * (f : G) * (l : G)⁻¹ ∈ F :=
      ((Subgroup.mem_normalizer_iff.mp hg) f).mp f.2
    obtain ⟨t', ht', hft'⟩ := hFT₂ ⟨_, hmem⟩
    have h1 : Fl ⟨_, hmem⟩ = l * Fl f * l⁻¹ := rfl
    have h2 : q t' = q (m * t * m⁻¹) := by
      rw [← hft', h1, map_mul, map_mul, map_inv, hl, hf, map_mul, map_mul, map_inv]
    have h3 : t' = m * t * m⁻¹ := by
      refine hq.eq_of_map_eq (hTexp' _ ht') ?_ h2
      have : (m * t * m⁻¹) ^ p = m * t ^ p * m⁻¹ := conj_pow
      rw [this, hTexp' t ht, mul_one, mul_inv_cancel]
    rw [← h3]
    exact ht'
  refine ⟨{ tor := tor, exists_elt := ?_, induced := ?_ }, hrel⟩
  · intro σ
    obtain ⟨m, hm, -, hmσ⟩ := SM.exists_elt σ
    obtain ⟨l, hl⟩ := hε.surjective (q m)
    exact ⟨(l : G), hnorm_F l m hm hl, l.2, haction l m hm hl σ hmσ⟩
  · intro g hg hgL
    obtain ⟨m, hm⟩ := hq.surjective (ε ⟨g, hgL⟩)
    have hmN : m ∈ Subgroup.normalizer (T : Set M) := by
      rw [Subgroup.mem_normalizer_iff]
      intro t
      constructor
      · exact hnormT ⟨g, hgL⟩ m hg hm.symm t
      · intro ht
        have hg' : (⟨g, hgL⟩ : ↥L)⁻¹.1 ∈ Subgroup.normalizer (F : Set G) :=
          Subgroup.inv_mem _ hg
        have := hnormT ⟨g, hgL⟩⁻¹ m⁻¹ hg' (by rw [map_inv, map_inv, hm]) _ ht
        have h2 : m⁻¹ * (m * t * m⁻¹) * m⁻¹⁻¹ = t := by group
        rwa [h2] at this
    obtain ⟨σ, hσ⟩ := SM.induced m hmN (Subgroup.mem_top _)
    exact ⟨σ, haction ⟨g, hgL⟩ m hmN hm.symm σ hσ⟩

end CFSG.RankThree.PartOne.KFOUT3
