module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixConj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixNormB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W W' : Type} [CommGroup W] [Finite W] [CommGroup W'] [Finite W']
  {M L : Subgroup (MulAut W)} {L' : Subgroup (MulAut W')} {κ : W →* W'} {e : ↥L' →* ↥L}

private def s1611e3_sixConj (g : ↥sixGhat) : MulAut ↥sixLhat where
  toFun l :=
    ⟨(g : MulAut (SixE6 × SixE6)) * (l : MulAut (SixE6 × SixE6)) *
        (g : MulAut (SixE6 × SixE6))⁻¹,
      sixGhat_normalizes (g : MulAut (SixE6 × SixE6)) g.2
        (l : MulAut (SixE6 × SixE6)) l.2⟩
  invFun l :=
    ⟨(g : MulAut (SixE6 × SixE6))⁻¹ * (l : MulAut (SixE6 × SixE6)) *
        (g : MulAut (SixE6 × SixE6)),
      sixGhat_normalizes (g : MulAut (SixE6 × SixE6))⁻¹ (sixGhat.inv_mem g.2)
        (l : MulAut (SixE6 × SixE6)) l.2⟩
  left_inv l := Subtype.ext (by group)
  right_inv l := Subtype.ext (by group)
  map_mul' l m := Subtype.ext (by simp only [Subtype.coe_mk, Subgroup.coe_mul]; group)

private theorem s1611e3_sixConj_mul_apply (g g' : ↥sixGhat) (l : ↥sixLhat) :
    s1611e3_sixConj (g * g') l = s1611e3_sixConj g (s1611e3_sixConj g' l) := by
  apply Subtype.ext
  show ((g * g' : ↥sixGhat) : MulAut (SixE6 × SixE6)) * (l : MulAut (SixE6 × SixE6)) *
      (((g * g' : ↥sixGhat)) : MulAut (SixE6 × SixE6))⁻¹ =
    (g : MulAut (SixE6 × SixE6)) *
      ((g' : MulAut (SixE6 × SixE6)) * (l : MulAut (SixE6 × SixE6)) *
        (g' : MulAut (SixE6 × SixE6))⁻¹) * (g : MulAut (SixE6 × SixE6))⁻¹
  rw [Subgroup.coe_mul]
  group

private def s1611e3_sixEps (θ : ↥sixLhat ≃* ↥L) (g : ↥sixGhat) : MulAut ↥L :=
  θ.symm.trans ((s1611e3_sixConj g).trans θ)

private theorem s1611e3_sixEps_apply' (θ : ↥sixLhat ≃* ↥L) (g : ↥sixGhat) (ℓ : ↥L) :
    s1611e3_sixEps θ g ℓ = θ (s1611e3_sixConj g (θ.symm ℓ)) := rfl

private theorem s1611e3_sixEps_apply (θ : ↥sixLhat ≃* ↥L) (g : ↥sixGhat) (l : ↥sixLhat) :
    s1611e3_sixEps θ g (θ l) = θ (s1611e3_sixConj g l) := by
  rw [s1611e3_sixEps_apply', MulEquiv.symm_apply_apply]

private theorem s1611e3_sixEps_mul_apply (θ : ↥sixLhat ≃* ↥L) (g g' : ↥sixGhat) (ℓ : ↥L) :
    s1611e3_sixEps θ (g * g') ℓ = s1611e3_sixEps θ g (s1611e3_sixEps θ g' ℓ) := by
  rw [s1611e3_sixEps_apply', s1611e3_sixEps_apply', s1611e3_sixEps_apply',
    MulEquiv.symm_apply_apply, s1611e3_sixConj_mul_apply]

private theorem s1611e3_sixEps_one (θ : ↥sixLhat ≃* ↥L) : s1611e3_sixEps θ 1 = 1 := by
  apply MulEquiv.ext
  intro ℓ
  rw [s1611e3_sixEps_apply']
  have h1 : s1611e3_sixConj (1 : ↥sixGhat) (θ.symm ℓ) = θ.symm ℓ := by
    apply Subtype.ext
    show (1 : MulAut (SixE6 × SixE6)) * ((θ.symm ℓ : ↥sixLhat) : MulAut (SixE6 × SixE6)) *
        (1 : MulAut (SixE6 × SixE6))⁻¹ = ((θ.symm ℓ : ↥sixLhat) : MulAut (SixE6 × SixE6))
    group
  rw [h1, MulEquiv.apply_symm_apply]
  rfl

private theorem s1611e3_sixK_map {K : Subgroup (SixE6 × SixE6)} (hK : K = ⊥ ∨ K = sixDiag)
    (g : ↥sixGhat) (u : SixE6 × SixE6) :
    (g : MulAut (SixE6 × SixE6)) u ∈ K ↔ u ∈ K := by
  rcases hK with rfl | rfl
  · simp
  · constructor
    · intro hu
      have hmem : (g : MulAut (SixE6 × SixE6))⁻¹ ∈ sixGhat := sixGhat.inv_mem g.2
      have h2 := sixDiag_invariant ((g : MulAut (SixE6 × SixE6))⁻¹) hmem _ hu
      rwa [MulAut.inv_apply_self] at h2
    · intro hu
      exact sixDiag_invariant (g : MulAut (SixE6 × SixE6)) g.2 u hu

private def s1611e3_mConj (h : SixHyp M L L' κ e) (m : MulAut W) (hm : m ∈ M) : MulAut ↥L where
  toFun ℓ := ⟨m * (ℓ : MulAut W) * m⁻¹, SixHyp.normalizes h m hm ℓ ℓ.2⟩
  invFun ℓ := ⟨m⁻¹ * (ℓ : MulAut W) * m, SixHyp.normalizes h m⁻¹ (M.inv_mem hm) ℓ ℓ.2⟩
  left_inv ℓ := Subtype.ext (by group)
  right_inv ℓ := Subtype.ext (by group)
  map_mul' ℓ₁ ℓ₂ := Subtype.ext (by simp only [Subtype.coe_mk, Subgroup.coe_mul]; group)

private theorem s1611e3_six_comp_eq (h : SixHyp M L L' κ e)
    {K : Subgroup (SixE6 × SixE6)} {Φ : SixE6 × SixE6 →* W} {θ : ↥sixLhat ≃* ↥L}
    (hK : K = ⊥ ∨ K = sixDiag) (hΦ : Function.Surjective Φ) (hker : Φ.ker = K)
    (hθ : ∀ (l : ↥sixLhat) (u : SixE6 × SixE6),
      Φ ((l : MulAut (SixE6 × SixE6)) u) = ((θ l : ↥L) : MulAut W) (Φ u))
    {g : ↥sixGhat} {m : MulAut W}
    (hm : ∀ ℓ : ↥L, m * (ℓ : MulAut W) * m⁻¹ =
      ((s1611e3_sixEps θ g ℓ : ↥L) : MulAut W)) :
    ∀ u : SixE6 × SixE6, Φ ((g : MulAut (SixE6 × SixE6)) u) = m (Φ u) := by
  classical
  let f₁ : SixE6 × SixE6 →* W := Φ.comp (g : MulAut (SixE6 × SixE6)).toMonoidHom
  let f₂ : SixE6 × SixE6 →* W := m.toMonoidHom.comp Φ
  have hf₁ : Function.Surjective f₁ := hΦ.comp (g : MulAut (SixE6 × SixE6)).surjective
  have hf₂ : Function.Surjective f₂ := m.surjective.comp hΦ
  have hker₂ : f₂.ker = K := by
    ext u
    rw [MonoidHom.mem_ker, ← hker, MonoidHom.mem_ker]
    change m (Φ u) = 1 ↔ Φ u = 1
    exact m.map_eq_one_iff
  have hker₁ : f₁.ker = K := by
    have h1 : f₁.ker = K.comap (g : MulAut (SixE6 × SixE6)).toMonoidHom := by
      change (Φ.comp (g : MulAut (SixE6 × SixE6)).toMonoidHom).ker =
        K.comap (g : MulAut (SixE6 × SixE6)).toMonoidHom
      rw [← MonoidHom.comap_ker, hker]
    rw [h1]
    ext u
    rw [Subgroup.mem_comap]
    exact s1611e3_sixK_map hK g u
  have hker_le : f₁.ker ≤ f₂.ker := by rw [hker₁, hker₂]
  let ψ : W →* W := (f₁.liftOfSurjective hf₁) ⟨f₂, hker_le⟩
  have hψ : ∀ u, ψ (f₁ u) = f₂ u := by
    intro u
    change ((f₁.liftOfSurjective hf₁) ⟨f₂, hker_le⟩) (f₁ u) = f₂ u
    rw [MonoidHom.liftOfRightInverse_comp_apply]
  have hf₁_eqv : ∀ (l : ↥sixLhat) (u : SixE6 × SixE6),
      f₁ ((l : MulAut (SixE6 × SixE6)) u) =
        ((s1611e3_sixEps θ g (θ l) : ↥L) : MulAut W) (f₁ u) := by
    intro l u
    have h1 : (g : MulAut (SixE6 × SixE6)) ((l : MulAut (SixE6 × SixE6)) u) =
        (s1611e3_sixConj g l : MulAut (SixE6 × SixE6)) ((g : MulAut (SixE6 × SixE6)) u) := by
      show (g : MulAut (SixE6 × SixE6)) ((l : MulAut (SixE6 × SixE6)) u) =
        ((g : MulAut (SixE6 × SixE6)) * (l : MulAut (SixE6 × SixE6)) *
          (g : MulAut (SixE6 × SixE6))⁻¹) ((g : MulAut (SixE6 × SixE6)) u)
      simp only [MulAut.mul_apply, MulAut.inv_apply_self]
    calc f₁ ((l : MulAut (SixE6 × SixE6)) u)
        = Φ ((g : MulAut (SixE6 × SixE6)) ((l : MulAut (SixE6 × SixE6)) u)) := rfl
      _ = Φ ((s1611e3_sixConj g l : MulAut (SixE6 × SixE6))
              ((g : MulAut (SixE6 × SixE6)) u)) := by rw [h1]
      _ = ((θ (s1611e3_sixConj g l) : ↥L) : MulAut W)
              (Φ ((g : MulAut (SixE6 × SixE6)) u)) :=
            hθ (s1611e3_sixConj g l) ((g : MulAut (SixE6 × SixE6)) u)
      _ = ((s1611e3_sixEps θ g (θ l) : ↥L) : MulAut W) (f₁ u) := by
            rw [s1611e3_sixEps_apply]
            rfl
  have hf₂_eqv : ∀ (l : ↥sixLhat) (u : SixE6 × SixE6),
      f₂ ((l : MulAut (SixE6 × SixE6)) u) =
        ((s1611e3_sixEps θ g (θ l) : ↥L) : MulAut W) (f₂ u) := by
    intro l u
    calc f₂ ((l : MulAut (SixE6 × SixE6)) u)
        = m (Φ ((l : MulAut (SixE6 × SixE6)) u)) := rfl
      _ = m (((θ l : ↥L) : MulAut W) (Φ u)) := by rw [hθ l u]
      _ = (m * ((θ l : ↥L) : MulAut W) * m⁻¹) (m (Φ u)) := by
            rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
      _ = ((s1611e3_sixEps θ g (θ l) : ↥L) : MulAut W) (m (Φ u)) := by rw [hm (θ l)]
      _ = ((s1611e3_sixEps θ g (θ l) : ↥L) : MulAut W) (f₂ u) := rfl
  have hψsurj : Function.Surjective ψ := by
    intro w
    obtain ⟨u, rfl⟩ := hf₂ w
    exact ⟨f₁ u, hψ u⟩
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro w hw
    obtain ⟨u, rfl⟩ := hf₁ w
    rw [hψ u] at hw
    have hu : u ∈ f₂.ker := MonoidHom.mem_ker.2 hw
    rw [hker₂, ← hker₁] at hu
    exact MonoidHom.mem_ker.1 hu
  let ψA : MulAut W := MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  have hψAc : ψA ∈ Subgroup.centralizer (L : Set (MulAut W)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro ℓ hℓ
    apply MulEquiv.ext
    intro w
    obtain ⟨u, rfl⟩ := hf₁ w
    set l : ↥sixLhat := θ.symm ((s1611e3_sixEps θ g).symm ⟨ℓ, hℓ⟩) with hl
    have hℓ_eq : s1611e3_sixEps θ g (θ l) = ⟨ℓ, hℓ⟩ := by
      rw [hl, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    have hℓ_eq' : ((s1611e3_sixEps θ g (θ l) : ↥L) : MulAut W) = ℓ := by
      rw [hℓ_eq]
    calc ℓ (ψA (f₁ u))
        = ((s1611e3_sixEps θ g (θ l) : ↥L) : MulAut W) (ψA (f₁ u)) := by rw [hℓ_eq']
      _ = ((s1611e3_sixEps θ g (θ l) : ↥L) : MulAut W) (ψ (f₁ u)) := by
            rw [show ψA (f₁ u) = ψ (f₁ u) from rfl]
      _ = ((s1611e3_sixEps θ g (θ l) : ↥L) : MulAut W) (f₂ u) := by rw [hψ u]
      _ = f₂ ((l : MulAut (SixE6 × SixE6)) u) := by rw [hf₂_eqv]
      _ = ψ (f₁ ((l : MulAut (SixE6 × SixE6)) u)) := by rw [hψ]
      _ = ψ (((s1611e3_sixEps θ g (θ l) : ↥L) : MulAut W) (f₁ u)) := by rw [hf₁_eqv]
      _ = ψ (ℓ (f₁ u)) := by rw [hℓ_eq']
      _ = ψA (ℓ (f₁ u)) := rfl
  have hψ1 : ∀ w, ψ w = w := by
    intro w
    have h1 := congrArg (fun f : MulAut W => f w) (SixHyp.cent_eq_one h ψA hψAc)
    show ψA w = w
    simpa using h1
  intro u
  have h1 : f₂ u = f₁ u := by
    have h2 : ψ (f₁ u) = f₁ u := hψ1 (f₁ u)
    rw [hψ u] at h2
    exact h2
  exact h1.symm

theorem s1611e3_six_theta (h : SixHyp M L L' κ e)
    {K : Subgroup (SixE6 × SixE6)} {Φ : SixE6 × SixE6 →* W} {θ : ↥sixLhat ≃* ↥L}
    (hK : K = ⊥ ∨ K = sixDiag) (hΦ : Function.Surjective Φ) (hker : Φ.ker = K)
    (hθ : ∀ (l : ↥sixLhat) (u : SixE6 × SixE6),
      Φ ((l : MulAut (SixE6 × SixE6)) u) = ((θ l : ↥L) : MulAut W) (Φ u)) :
    ∃ Θ : ↥sixGhat ≃* ↥M, ∀ (g : ↥sixGhat) (u : SixE6 × SixE6),
      Φ ((g : MulAut (SixE6 × SixE6)) u) = ((Θ g : ↥M) : MulAut W) (Φ u) := by
  classical
  have hex : ∀ g : ↥sixGhat, ∃ m ∈ M, ∀ ℓ : ↥L,
      m * (ℓ : MulAut W) * m⁻¹ = ((s1611e3_sixEps θ g ℓ : ↥L) : MulAut W) :=
    fun g => SixHyp.exists_conj h (s1611e3_sixEps θ g)
  have huniq : ∀ {g : ↥sixGhat} {m m' : MulAut W}, m ∈ M → m' ∈ M →
      (∀ ℓ : ↥L, m * (ℓ : MulAut W) * m⁻¹ =
        ((s1611e3_sixEps θ g ℓ : ↥L) : MulAut W)) →
      (∀ ℓ : ↥L, m' * (ℓ : MulAut W) * m'⁻¹ =
        ((s1611e3_sixEps θ g ℓ : ↥L) : MulAut W)) →
      m = m' := by
    intro g m m' hm hm' hgm hgm'
    have hcent : m'⁻¹ * m ∈ Subgroup.centralizer (L : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro ℓ hℓ
      have hℓ' : m * (ℓ : MulAut W) * m⁻¹ = m' * (ℓ : MulAut W) * m'⁻¹ := by
        rw [hgm ⟨ℓ, hℓ⟩, hgm' ⟨ℓ, hℓ⟩]
      have hconj : (m'⁻¹ * m) * (ℓ : MulAut W) * (m'⁻¹ * m)⁻¹ = (ℓ : MulAut W) := by
        rw [show (m'⁻¹ * m) * (ℓ : MulAut W) * (m'⁻¹ * m)⁻¹ =
          m'⁻¹ * (m * (ℓ : MulAut W) * m⁻¹) * m' by group, hℓ']
        group
      have hcomm : (m'⁻¹ * m) * (ℓ : MulAut W) = (ℓ : MulAut W) * (m'⁻¹ * m) := by
        calc (m'⁻¹ * m) * (ℓ : MulAut W)
            = ((m'⁻¹ * m) * (ℓ : MulAut W) * (m'⁻¹ * m)⁻¹) * (m'⁻¹ * m) := by group
          _ = (ℓ : MulAut W) * (m'⁻¹ * m) := by rw [hconj]
      exact hcomm.symm
    have h1 := SixHyp.cent_eq_one h (m'⁻¹ * m) hcent
    calc m = m' * (m'⁻¹ * m) := by group
      _ = m' * 1 := by rw [h1]
      _ = m' := by simp
  let Θfun : ↥sixGhat → ↥M := fun g => ⟨(hex g).choose, (hex g).choose_spec.1⟩
  have Θfun_spec : ∀ g : ↥sixGhat, ∀ ℓ : ↥L,
      (Θfun g : MulAut W) * (ℓ : MulAut W) * (Θfun g : MulAut W)⁻¹ =
        ((s1611e3_sixEps θ g ℓ : ↥L) : MulAut W) :=
    fun g => (hex g).choose_spec.2
  have Θfun_comp : ∀ g : ↥sixGhat, ∀ u : SixE6 × SixE6,
      Φ ((g : MulAut (SixE6 × SixE6)) u) = (Θfun g : MulAut W) (Φ u) :=
    fun g => s1611e3_six_comp_eq h hK hΦ hker hθ (Θfun_spec g)
  have Θmap_one : Θfun 1 = 1 := by
    apply Subtype.ext
    refine huniq (g := (1 : ↥sixGhat)) (m := (Θfun 1 : MulAut W))
      (m' := ((1 : ↥M) : MulAut W)) (Θfun 1).2 (Subgroup.one_mem M) (Θfun_spec 1) ?_
    intro ℓ
    rw [s1611e3_sixEps_one]
    simp
  have Θmap_mul : ∀ g g' : ↥sixGhat, Θfun (g * g') = Θfun g * Θfun g' := by
    intro g g'
    apply Subtype.ext
    refine huniq (g := g * g') (m := (Θfun (g * g') : MulAut W))
      (m' := ((Θfun g * Θfun g' : ↥M) : MulAut W)) (Θfun (g * g')).2
      (M.mul_mem (Θfun g).2 (Θfun g').2) (Θfun_spec (g * g')) ?_
    intro ℓ
    show (Θfun g : MulAut W) * (Θfun g' : MulAut W) * (ℓ : MulAut W) *
        ((Θfun g : MulAut W) * (Θfun g' : MulAut W))⁻¹ =
      ((s1611e3_sixEps θ (g * g') ℓ : ↥L) : MulAut W)
    rw [s1611e3_sixEps_mul_apply θ g g' ℓ]
    rw [show (Θfun g : MulAut W) * (Θfun g' : MulAut W) * (ℓ : MulAut W) *
        ((Θfun g : MulAut W) * (Θfun g' : MulAut W))⁻¹ =
        (Θfun g : MulAut W) * ((Θfun g' : MulAut W) * (ℓ : MulAut W) *
          (Θfun g' : MulAut W)⁻¹) * (Θfun g : MulAut W)⁻¹ by group]
    rw [Θfun_spec g' ℓ, Θfun_spec g (s1611e3_sixEps θ g' ℓ)]
  let Θhom : ↥sixGhat →* ↥M :=
    { toFun := Θfun, map_one' := Θmap_one, map_mul' := Θmap_mul }
  have Θinj : Function.Injective Θhom := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply Subtype.ext
    apply sixGhat_cent_eq_one (g : MulAut (SixE6 × SixE6)) g.2
    intro l hl
    have hgval : (Θfun g : MulAut W) = 1 := by
      have h := congrArg Subtype.val hg
      exact h
    have hε : ∀ ℓ : ↥L, ((s1611e3_sixEps θ g ℓ : ↥L) : MulAut W) = (ℓ : MulAut W) := by
      intro ℓ
      have h1 := Θfun_spec g ℓ
      rw [hgval] at h1
      simpa using h1.symm
    have hfix : s1611e3_sixConj g ⟨l, hl⟩ = ⟨l, hl⟩ := by
      apply θ.injective
      have h1 := hε (θ ⟨l, hl⟩)
      rw [s1611e3_sixEps_apply] at h1
      exact Subtype.ext h1
    have h2 : (g : MulAut (SixE6 × SixE6)) * (l : MulAut (SixE6 × SixE6)) *
        (g : MulAut (SixE6 × SixE6))⁻¹ = l := congrArg Subtype.val hfix
    calc (g : MulAut (SixE6 × SixE6)) * l
        = ((g : MulAut (SixE6 × SixE6)) * l * (g : MulAut (SixE6 × SixE6))⁻¹) *
            (g : MulAut (SixE6 × SixE6)) := by group
      _ = l * (g : MulAut (SixE6 × SixE6)) := by rw [h2]
  have Θsurj : Function.Surjective Θhom := by
    intro m
    let ε : MulAut ↥L := s1611e3_mConj h (m : MulAut W) m.2
    let εhat : MulAut ↥sixLhat := θ.trans (ε.trans θ.symm)
    obtain ⟨g, hg, hgc⟩ := sixGhat_exists_conj εhat
    refine ⟨⟨g, hg⟩, ?_⟩
    apply Subtype.ext
    refine huniq (g := ⟨g, hg⟩) (m := (Θhom ⟨g, hg⟩ : MulAut W)) (m' := (m : MulAut W))
      (Θhom ⟨g, hg⟩).2 m.2 (Θfun_spec ⟨g, hg⟩) ?_
    intro ℓ
    have hε : s1611e3_sixEps θ ⟨g, hg⟩ ℓ = ε ℓ := by
      rw [s1611e3_sixEps_apply']
      have h1 : s1611e3_sixConj ⟨g, hg⟩ (θ.symm ℓ) = εhat (θ.symm ℓ) := by
        apply Subtype.ext
        exact hgc (θ.symm ℓ)
      rw [h1]
      show θ (θ.symm (ε (θ (θ.symm ℓ)))) = ε ℓ
      simp only [MulEquiv.apply_symm_apply]
    have hmε : (↑m : MulAut W) * (ℓ : MulAut W) * ((↑m : MulAut W))⁻¹ =
        ((ε ℓ : ↥L) : MulAut W) := rfl
    rw [hmε, hε]
  have hbij : Function.Bijective Θhom := ⟨Θinj, Θsurj⟩
  refine ⟨MulEquiv.ofBijective Θhom hbij, ?_⟩
  intro g u
  exact Θfun_comp g u

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
