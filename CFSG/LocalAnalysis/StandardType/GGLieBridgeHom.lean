module

public import CFSG.Assembly.Defs
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Open

@[expose] def GGLiePartner {G : Type} [Group G] {Y : Type} [Group Y] (G₀ : Subgroup G)
    (θ : ↥G₀ →* Y) (d : G) (a : Y) : Prop :=
  ∀ x : ↥G₀, ∀ h : d * (x : G) * d⁻¹ ∈ G₀, θ ⟨_, h⟩ = a * θ x * a⁻¹

theorem GGLiePartner.unique {G Y : Type} [Group G] [Group Y] {G₀ : Subgroup G}
    {θ : ↥G₀ →* Y} {Φ : Subgroup Y}
    (hcent : ∀ z ∈ Φ, (∀ x : ↥G₀, z * θ x = θ x * z) → z = 1) {d : G}
    (hdN : d ∈ Subgroup.normalizer (G₀ : Set G)) {a a' : Y} (ha : a ∈ Φ) (ha' : a' ∈ Φ)
    (h : GGLiePartner G₀ θ d a) (h' : GGLiePartner G₀ θ d a') : a = a' := by
  have key : ∀ x : ↥G₀, (a'⁻¹ * a) * θ x = θ x * (a'⁻¹ * a) := by
    intro x
    have hx : d * (x : G) * d⁻¹ ∈ G₀ := (Subgroup.mem_normalizer_iff.mp hdN (x : G)).mp x.2
    have heq : a * θ x * a⁻¹ = a' * θ x * a'⁻¹ := (h x hx).symm.trans (h' x hx)
    have hc := congrArg (fun t => a'⁻¹ * t * a) heq
    simpa [mul_assoc] using hc
  have hmem : a'⁻¹ * a ∈ Φ := mul_mem (inv_mem ha') ha
  exact (inv_mul_eq_one.mp (hcent _ hmem key)).symm

theorem GGLiePartner.mul {G Y : Type} [Group G] [Group Y] {G₀ : Subgroup G}
    {θ : ↥G₀ →* Y} {d d' : G} (hdN : d ∈ Subgroup.normalizer (G₀ : Set G))
    (hdN' : d' ∈ Subgroup.normalizer (G₀ : Set G)) {a a' : Y} (h : GGLiePartner G₀ θ d a)
    (h' : GGLiePartner G₀ θ d' a') : GGLiePartner G₀ θ (d * d') (a * a') := by
  intro x hx
  have hx' : d' * (x : G) * d'⁻¹ ∈ G₀ :=
    (Subgroup.mem_normalizer_iff.mp hdN' (x : G)).mp x.2
  have hmem : d * (d' * (x : G) * d'⁻¹) * d⁻¹ ∈ G₀ :=
    (Subgroup.mem_normalizer_iff.mp hdN (d' * (x : G) * d'⁻¹)).mp hx'
  have h1 := h ⟨d' * (x : G) * d'⁻¹, hx'⟩ hmem
  have h2 := h' x hx'
  have hsub : (⟨d * (d' * (x : G) * d'⁻¹) * d⁻¹, hmem⟩ : ↥G₀)
      = ⟨d * d' * (x : G) * (d * d')⁻¹, hx⟩ := by
    apply Subtype.ext
    group
  rw [hsub] at h1
  calc θ ⟨d * d' * (x : G) * (d * d')⁻¹, hx⟩
      = a * θ ⟨d' * (x : G) * d'⁻¹, hx'⟩ * a⁻¹ := h1
    _ = a * (a' * θ x * a'⁻¹) * a⁻¹ := by rw [h2]
    _ = (a * a') * θ x * (a * a')⁻¹ := by group

theorem GGLiePartner.one {G Y : Type} [Group G] [Group Y] {G₀ : Subgroup G}
    {θ : ↥G₀ →* Y} : GGLiePartner G₀ θ (1 : G) (1 : Y) := by
  intro x hx
  have hx' : (⟨(1 : G) * (x : G) * (1 : G)⁻¹, hx⟩ : ↥G₀) = x := by
    apply Subtype.ext
    simp
  rw [hx']
  simp

theorem GGLiePartner.inv {G Y : Type} [Group G] [Group Y] {G₀ : Subgroup G}
    {θ : ↥G₀ →* Y} {d : G} (hdN : d ∈ Subgroup.normalizer (G₀ : Set G)) {a : Y}
    (h : GGLiePartner G₀ θ d a) : GGLiePartner G₀ θ d⁻¹ a⁻¹ := by
  intro x hx
  have hy : d * (d⁻¹ * (x : G) * (d⁻¹)⁻¹) * d⁻¹ ∈ G₀ :=
    (Subgroup.mem_normalizer_iff.mp hdN (d⁻¹ * (x : G) * (d⁻¹)⁻¹)).mp hx
  have h1 := h ⟨d⁻¹ * (x : G) * (d⁻¹)⁻¹, hx⟩ hy
  have hsub : (⟨d * (d⁻¹ * (x : G) * (d⁻¹)⁻¹) * d⁻¹, hy⟩ : ↥G₀) = x := by
    apply Subtype.ext
    group
  rw [hsub] at h1
  rw [h1]
  group

theorem GGLiePartner.zpow {G Y : Type} [Group G] [Group Y] {G₀ : Subgroup G}
    {θ : ↥G₀ →* Y} {d : G} (hdN : d ∈ Subgroup.normalizer (G₀ : Set G)) {a : Y}
    (h : GGLiePartner G₀ θ d a) (n : ℤ) : GGLiePartner G₀ θ (d ^ n) (a ^ n) := by
  induction n using Int.induction_on with
  | zero => simpa using GGLiePartner.one
  | succ n ih =>
    have hdn : d ^ (n : ℤ) ∈ Subgroup.normalizer (G₀ : Set G) :=
      (Subgroup.normalizer (G₀ : Set G)).zpow_mem hdN (n : ℤ)
    have hm := GGLiePartner.mul hdn hdN ih h
    simpa [zpow_add_one] using hm
  | pred n ih =>
    have hdn : d ^ (-(n : ℤ)) ∈ Subgroup.normalizer (G₀ : Set G) :=
      (Subgroup.normalizer (G₀ : Set G)).zpow_mem hdN (-(n : ℤ))
    have hdi : d⁻¹ ∈ Subgroup.normalizer (G₀ : Set G) := inv_mem hdN
    have hm := GGLiePartner.mul hdn hdi ih (GGLiePartner.inv hdN h)
    simpa [zpow_sub_one] using hm

theorem GGLiePartner.comp {G Y Z : Type} [Group G] [Group Y] [Group Z]
    {G₀ : Subgroup G} {θ : ↥G₀ →* Y} {d : G} {a : Y}
    (h : GGLiePartner G₀ θ d a) (φ : Y →* Z) :
    GGLiePartner G₀ (φ.comp θ) d (φ a) := by
  intro x hx
  simpa using congrArg φ (h x hx)

theorem GGLiePartner.of_mem {G Y : Type} [Group G] [Group Y] {G₀ : Subgroup G}
    {θ : ↥G₀ →* Y} (d : ↥G₀) : GGLiePartner G₀ θ (d : G) (θ d) := by
  intro x hx
  have hsub : (⟨(d : G) * (x : G) * (d : G)⁻¹, hx⟩ : ↥G₀) = d * x * d⁻¹ :=
    Subtype.ext rfl
  rw [hsub]
  simp

theorem centralizes_of_trivial_bridge_action {G Y : Type} [Group G] [Group Y] {G₀ : Subgroup G}
    (θ : ↥G₀ →* Y) (hperf : commutator ↥G₀ = ⊤) (hker : θ.ker = Subgroup.center ↥G₀) {d : G}
    (hdN : d ∈ Subgroup.normalizer (G₀ : Set G))
    (h : ∀ x : ↥G₀, ∀ hx : d * (x : G) * d⁻¹ ∈ G₀, θ ⟨_, hx⟩ = θ x) :
    d ∈ Subgroup.centralizer (G₀ : Set G) := by
  have hmemd : ∀ x : ↥G₀, d * (x : G) * d⁻¹ ∈ G₀ :=
    fun x => (Subgroup.mem_normalizer_iff.mp hdN (x : G)).mp x.2
  let φ₀ : ↥G₀ → ↥G₀ := fun x => x⁻¹ * ⟨d * (x : G) * d⁻¹, hmemd x⟩
  have hmem : ∀ x : ↥G₀, φ₀ x ∈ Subgroup.center ↥G₀ := by
    intro x
    rw [← hker, MonoidHom.mem_ker]
    show θ (x⁻¹ * ⟨d * (x : G) * d⁻¹, hmemd x⟩) = 1
    rw [map_mul, map_inv, h x (hmemd x)]
    group
  have hmul : ∀ x y : ↥G₀, φ₀ (x * y) = φ₀ x * φ₀ y := by
    intro x y
    show (x * y)⁻¹ * ⟨d * ((x * y : ↥G₀) : G) * d⁻¹, hmemd (x * y)⟩
        = (x⁻¹ * ⟨d * (x : G) * d⁻¹, hmemd x⟩)
          * (y⁻¹ * ⟨d * (y : G) * d⁻¹, hmemd y⟩)
    have hψ : (⟨d * ((x * y : ↥G₀) : G) * d⁻¹, hmemd (x * y)⟩ : ↥G₀)
        = ⟨d * (x : G) * d⁻¹, hmemd x⟩ * ⟨d * (y : G) * d⁻¹, hmemd y⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      group
    rw [hψ, mul_inv_rev]
    have hc : y⁻¹ * (x⁻¹ * ⟨d * (x : G) * d⁻¹, hmemd x⟩)
        = (x⁻¹ * ⟨d * (x : G) * d⁻¹, hmemd x⟩) * y⁻¹ :=
      (Subgroup.mem_center_iff.mp (hmem x)) y⁻¹
    calc y⁻¹ * x⁻¹ * (⟨d * (x : G) * d⁻¹, hmemd x⟩ * ⟨d * (y : G) * d⁻¹, hmemd y⟩)
        = (y⁻¹ * (x⁻¹ * ⟨d * (x : G) * d⁻¹, hmemd x⟩))
            * ⟨d * (y : G) * d⁻¹, hmemd y⟩ := by group
      _ = ((x⁻¹ * ⟨d * (x : G) * d⁻¹, hmemd x⟩) * y⁻¹)
            * ⟨d * (y : G) * d⁻¹, hmemd y⟩ := by rw [hc]
      _ = (x⁻¹ * ⟨d * (x : G) * d⁻¹, hmemd x⟩)
            * (y⁻¹ * ⟨d * (y : G) * d⁻¹, hmemd y⟩) := by group
  let φ : ↥G₀ →* ↥(Subgroup.center ↥G₀) :=
    MonoidHom.mk' (fun x => ⟨φ₀ x, hmem x⟩) (by
      intro x y
      apply Subtype.ext
      show φ₀ (x * y) = φ₀ x * φ₀ y
      exact hmul x y)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hle : commutator ↥G₀ ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [hperf] at hle
  have hφ1 : φ ⟨x, hx⟩ = 1 := MonoidHom.mem_ker.mp (hle (Subgroup.mem_top _))
  have hval : x⁻¹ * (d * x * d⁻¹) = 1 := by
    have h1 : ((φ ⟨x, hx⟩ : ↥(Subgroup.center ↥G₀)) : ↥G₀) = 1 := by
      rw [hφ1]; rfl
    have h2 : (((φ ⟨x, hx⟩ : ↥(Subgroup.center ↥G₀)) : ↥G₀) : G) = 1 := by
      rw [h1]; rfl
    simpa [φ, φ₀, Subgroup.coe_mul, Subgroup.coe_inv] using h2
  have hdx : d * x * d⁻¹ = x := by
    have h2 : x * (x⁻¹ * (d * x * d⁻¹)) = x * 1 := by rw [hval]
    simpa using h2
  exact (mul_inv_eq_iff_eq_mul.mp hdx).symm

private theorem l10b1_elem_map {p : ℕ} {G Y : Type} [Group G] [Group Y] {D : Subgroup G}
    (hel : IsElemAbelian p D) (lam : ↥D →* Y) : IsElemAbelian p lam.range := by
  constructor
  · refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp a.2
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp b.2
    apply Subtype.ext
    show (a : Y) * (b : Y) = (b : Y) * (a : Y)
    rw [← hx, ← hy, ← map_mul, ← map_mul, hel.1.is_comm.comm x y]
  · intro a ha
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp ha
    rw [← map_pow]
    have hx : x ^ p = 1 := Subtype.ext (by simpa [Subgroup.coe_pow] using hel.2 (↑x) x.2)
    rw [hx, map_one]

private theorem l10b1_exists_lam {G Y : Type} [Group G] [Group Y] {G₀ D : Subgroup G}
    {Φ : Subgroup Y} {θ : ↥G₀ →* Y}
    (hcent : ∀ z ∈ Φ, (∀ x : ↥G₀, z * θ x = θ x * z) → z = 1)
    (hDN : D ≤ Subgroup.normalizer (G₀ : Set G))
    (hpart : ∀ d ∈ D, ∃ a ∈ Φ, GGLiePartner G₀ θ d a) :
    ∃ lam : ↥D →* Y, ∀ d : ↥D, lam d ∈ Φ ∧ GGLiePartner G₀ θ (d : G) (lam d) := by
  classical
  choose f hfΦ hfp using fun d : ↥D => hpart d d.2
  have hmul : ∀ d d' : ↥D, f (d * d') = f d * f d' := by
    intro d d'
    refine GGLiePartner.unique hcent (hDN (d * d').2) (hfΦ (d * d'))
      (mul_mem (hfΦ d) (hfΦ d')) ?_ ?_
    · exact hfp (d * d')
    · rw [Subgroup.coe_mul]
      exact GGLiePartner.mul (hDN d.2) (hDN d'.2) (hfp d) (hfp d')
  exact ⟨MonoidHom.mk' f hmul, fun d => ⟨hfΦ d, hfp d⟩⟩

private theorem l10b1_lam_injective {G Y : Type} [Group G] [Group Y] {G₀ D : Subgroup G}
    {θ : ↥G₀ →* Y} (hperf : commutator ↥G₀ = ⊤) (hker : θ.ker = Subgroup.center ↥G₀)
    (hDN : D ≤ Subgroup.normalizer (G₀ : Set G))
    (hDC : D ⊓ Subgroup.centralizer (G₀ : Set G) = ⊥) {lam : ↥D →* Y}
    (hlam : ∀ d : ↥D, GGLiePartner G₀ θ (d : G) (lam d)) : Function.Injective lam := by
  rw [injective_iff_map_eq_one]
  intro d hd
  have htriv : ∀ x : ↥G₀, ∀ hx : (d : G) * (x : G) * (d : G)⁻¹ ∈ G₀,
      θ ⟨_, hx⟩ = θ x := by
    intro x hx
    have hh := hlam d x hx
    rw [hd] at hh
    simpa using hh
  have hcent := centralizes_of_trivial_bridge_action θ hperf hker (hDN d.2) htriv
  have hmem : (d : G) ∈ D ⊓ Subgroup.centralizer (G₀ : Set G) := ⟨d.2, hcent⟩
  rw [hDC] at hmem
  exact Subtype.ext (by simpa using (Subgroup.mem_bot.mp hmem))

theorem ggLieBridge_partner_hom {G : Type} [Group G] {Y : Type} [Group Y] {p : ℕ}
    (G₀ D : Subgroup G) (Φ : Subgroup Y) (θ : ↥G₀ →* Y)
    (hperf : commutator ↥G₀ = ⊤) (hker : θ.ker = Subgroup.center ↥G₀)
    (hDN : D ≤ Subgroup.normalizer (G₀ : Set G)) (hel : IsElemAbelian p D)
    (hDC : D ⊓ Subgroup.centralizer (G₀ : Set G) = ⊥)
    (hcent : ∀ z ∈ Φ, (∀ x : ↥G₀, z * θ x = θ x * z) → z = 1)
    (hpart : ∀ d ∈ D, ∃ a ∈ Φ, GGLiePartner G₀ θ d a) :
    ∃ A : Subgroup Y, A ≤ Φ ∧ IsElemAbelian p A ∧ Nat.card A = Nat.card D ∧
      (∀ d ∈ D, ∃ a ∈ A, GGLiePartner G₀ θ d a) ∧
      (∀ a ∈ A, ∃ d ∈ D, GGLiePartner G₀ θ d a) := by
  obtain ⟨lam, hlam⟩ := l10b1_exists_lam hcent hDN hpart
  have hinj := l10b1_lam_injective hperf hker hDN hDC fun d => (hlam d).2
  refine ⟨lam.range, ?_, l10b1_elem_map hel lam, ?_, ?_, ?_⟩
  · rintro _ ⟨d, rfl⟩
    exact (hlam d).1
  · exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  · intro d hd
    exact ⟨lam ⟨d, hd⟩, ⟨_, rfl⟩, (hlam ⟨d, hd⟩).2⟩
  · rintro _ ⟨d, rfl⟩
    exact ⟨d, d.2, (hlam d).2⟩

end CFSG.StandardType.LieCore
