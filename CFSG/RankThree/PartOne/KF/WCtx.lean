module

public import CFSG.RankThree.PartOne.KF.SymCtxQuot

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.RankThree.PartOne

structure WCtx {G : Type} [Group G] {Γ V : Type} [Group Γ] [Group V] (act : Γ →* MulAut V)
    (L F : Subgroup G) where
  tor : V ≃* F
  exists_elt : ∀ γ : Γ, ∃ (g : G) (hg : g ∈ Subgroup.normalizer (F : Set G)),
    g ∈ L ∧ F.normalizerMonoidHom ⟨g, hg⟩ = MulAut.congr tor (act γ)
  induced : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (F : Set G)), g ∈ L →
    ∃ γ : Γ, F.normalizerMonoidHom ⟨g, hg⟩ = MulAut.congr tor (act γ)

namespace WCtx

variable {G M P V Γ : Type} [Group G] [Group M] [Group P] [Group V] [Group Γ] {p : ℕ}
  {L F : Subgroup G} {T : Subgroup M} {act : Γ →* MulAut V}

theorem ofCentralQuot (hVexp : ∀ d : V, d ^ p = 1) (SM : WCtx act (⊤ : Subgroup M) T)
    (q : M →* P) (hq : IsCentralPQuot p q)
    (ε : ↥L →* P) (hε : IsCentralPQuot p ε) (hFL : F ≤ L) (hFexp : ∀ f ∈ F, f ^ p = 1)
    (hFT₁ : ∀ t ∈ T, ∃ f : F, ε (Subgroup.inclusion hFL f) = q t)
    (hFT₂ : ∀ f : F, ∃ t ∈ T, ε (Subgroup.inclusion hFL f) = q t) :
    Nonempty (WCtx act L F) := by
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
  refine ⟨{ tor := tor, exists_elt := ?_, induced := ?_ }⟩
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

theorem ofIso (hVexp : ∀ d : V, d ^ p = 1) (SM : WCtx act (⊤ : Subgroup M) T) (ψ : M ≃* ↥L)
    (hFL : F ≤ L) (hFexp : ∀ f ∈ F, f ^ p = 1) (hψ : ∀ m : M, (ψ m : G) ∈ F ↔ m ∈ T) :
    Nonempty (WCtx act L F) := by
  refine ofCentralQuot (P := ↥L) hVexp SM ψ.toMonoidHom
    (SymCtx.isCentralPQuot_of_bijective _ ψ.bijective p) (MonoidHom.id ↥L)
    (SymCtx.isCentralPQuot_of_bijective _ Function.bijective_id p) hFL hFexp
    (fun t ht => ⟨⟨(ψ t : G), (hψ t).mpr ht⟩, rfl⟩)
    (fun f => ⟨ψ.symm (Subgroup.inclusion hFL f), ?_, ?_⟩)
  · rw [← hψ]
    show ((ψ (ψ.symm (Subgroup.inclusion hFL f)) : ↥L) : G) ∈ F
    rw [MulEquiv.apply_symm_apply]
    exact f.2
  · exact (MulEquiv.apply_symm_apply ψ _).symm

variable (S : WCtx act L F)

@[expose] noncomputable def actF : Γ →* MulAut F :=
  (MulAut.congr S.tor).toMonoidHom.comp act

theorem actF_eq (γ : Γ) : S.actF γ = MulAut.congr S.tor (act γ) := rfl

theorem actF_apply (γ : Γ) (d : V) : S.actF γ (S.tor d) = S.tor (act γ d) := by
  show S.tor (act γ (S.tor.symm (S.tor d))) = _
  rw [MulEquiv.symm_apply_apply]

theorem coe_normalizerMonoidHom_apply {g : G} (hg : g ∈ Subgroup.normalizer (F : Set G)) (e : F) :
    ((F.normalizerMonoidHom ⟨g, hg⟩ e : F) : G) = g * e * g⁻¹ := rfl

include S in
theorem torusImage_eq_range : torusImage F L = S.actF.range := by
  ext t
  constructor
  · intro ht
    obtain ⟨w, hwL, hwF, rfl⟩ := Sec12Three.mem_torusImage_iff.mp ht
    obtain ⟨γ, hγ⟩ := S.induced w hwF hwL
    exact ⟨γ, hγ.symm⟩
  · rintro ⟨γ, rfl⟩
    obtain ⟨g, hg, hgL, hgγ⟩ := S.exists_elt γ
    exact Sec12Three.mem_torusImage_iff.mpr ⟨g, hgL, hg, hgγ⟩

include S in
theorem normalizes_act {y : G} (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hyF : y ∈ Subgroup.normalizer (F : Set G)) (γ : Γ) :
    ∃ γ' : Γ, (MulAut.congr S.tor).symm (F.normalizerMonoidHom ⟨y, hyF⟩) * act γ *
      ((MulAut.congr S.tor).symm (F.normalizerMonoidHom ⟨y, hyF⟩))⁻¹ = act γ' := by
  set φ : MulAut F := F.normalizerMonoidHom ⟨y, hyF⟩ with hφdef
  obtain ⟨g, hg, hgL, hgσ⟩ := S.exists_elt γ
  have hywL : y * g * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyL _).mp hgL
  have hywF : y * g * y⁻¹ ∈ Subgroup.normalizer (F : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hyF hg) (Subgroup.inv_mem _ hyF)
  obtain ⟨γ', hγ'⟩ := S.induced _ hywF hywL
  refine ⟨γ', ?_⟩
  have h1 : φ * MulAut.congr S.tor (act γ) * φ⁻¹ = MulAut.congr S.tor (act γ') := by
    rw [← hγ', ← hgσ]
    have : (⟨y * g * y⁻¹, hywF⟩ : Subgroup.normalizer (F : Set G)) =
        ⟨y, hyF⟩ * ⟨g, hg⟩ * ⟨y, hyF⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
  have h2 := congrArg (MulAut.congr S.tor).symm h1
  rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at h2
  exact h2

include S in
theorem torusIrreducible_of
    (hirr : ∀ B' : Subgroup V, (∀ γ : Γ, ∀ d ∈ B', act γ d ∈ B') → B' = ⊥ ∨ B' = ⊤)
    (B : Subgroup G) (hBF : B ≤ F) (hB : torusInvariant F L B) : B = ⊥ ∨ B = F := by
  set B' : Subgroup V := (B.subgroupOf F).comap S.tor.toMonoidHom with hB'
  have hinv : ∀ γ : Γ, ∀ d ∈ B', act γ d ∈ B' := by
    intro γ d hd
    have hd' : ((S.tor d : F) : G) ∈ B := hd
    obtain ⟨g, hg, hgL, hgγ⟩ := S.exists_elt γ
    have hw : g ∈ L ⊓ torusNormalizer F := Subgroup.mem_inf.mpr ⟨hgL, hg⟩
    have h1 := hB _ hw _ hd'
    have h2 : ((S.tor (act γ d) : F) : G) = g * ((S.tor d : F) : G) * g⁻¹ := by
      rw [← S.actF_apply, S.actF_eq, ← hgγ]
      rfl
    show ((S.tor (act γ d) : F) : G) ∈ B
    rw [h2]
    exact h1
  rcases hirr B' hinv with h | h
  · left
    rw [eq_bot_iff]
    intro b hb
    have hbF : b ∈ F := hBF hb
    obtain ⟨d, hd⟩ := S.tor.surjective ⟨b, hbF⟩
    have hdB : d ∈ B' := by
      show ((S.tor d : F) : G) ∈ B
      rw [hd]
      exact hb
    rw [h, Subgroup.mem_bot] at hdB
    subst hdB
    rw [map_one] at hd
    have := congrArg (fun x : F => (x : G)) hd
    exact (Subgroup.mem_bot.mpr this.symm)
  · right
    apply le_antisymm hBF
    intro e he
    obtain ⟨d, hd⟩ := S.tor.surjective ⟨e, he⟩
    have hdB : d ∈ B' := by rw [h]; trivial
    have : ((S.tor d : F) : G) ∈ B := hdB
    rwa [hd] at this

end WCtx

end CFSG.RankThree.PartOne.KFU
