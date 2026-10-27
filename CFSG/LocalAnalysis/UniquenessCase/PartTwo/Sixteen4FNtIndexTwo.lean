module

public import CFSG.Quasithin.Background.JonesParshallBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup CFSG.Quasithin.JonesParshall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

private def w183_conjFun {G G' N : Type} [Group G] [Group G'] [AddCommGroup N]
    [Module (ZMod 2) N] (e : G' ≃* G) : (G' → N) ≃ₗ[ZMod 2] (G → N) where
  toFun f := fun g => f (e.symm g)
  invFun f := fun g' => f (e g')
  left_inv f := by funext g'; simp
  right_inv f := by funext g; simp
  map_add' f f' := by funext g; rfl
  map_smul' c f := by funext g; rfl

private theorem w183_conjFun_mem_Z1 {G G' : Type} [Group G] [Group G'] {N : Type}
    [AddCommGroup N] [Module (ZMod 2) N] (e : G' ≃* G)
    (ρ : Representation (ZMod 2) G N) {f : G' → N} :
    w183_conjFun e f ∈ Z1 ρ ↔ f ∈ Z1 (ρ.comp e.toMonoidHom) := by
  constructor
  · intro hf a b
    have h := hf (e a) (e b)
    simpa [w183_conjFun, MonoidHom.comp_apply] using h
  · intro hf x y
    have h := hf (e.symm x) (e.symm y)
    simpa [w183_conjFun, MonoidHom.comp_apply] using h

private theorem w183_conjFun_mem_B1 {G G' : Type} [Group G] [Group G'] {N : Type}
    [AddCommGroup N] [Module (ZMod 2) N] (e : G' ≃* G)
    (ρ : Representation (ZMod 2) G N) {f : G' → N} :
    w183_conjFun e f ∈ B1 ρ ↔ f ∈ B1 (ρ.comp e.toMonoidHom) := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, funext fun g' => ?_⟩
    have h := congrFun hv (e g')
    simpa [coboundary, w183_conjFun, MonoidHom.comp_apply] using h
  · rintro ⟨v, hv⟩
    refine ⟨v, funext fun g => ?_⟩
    have h := congrFun hv (e.symm g)
    simpa [coboundary, w183_conjFun, MonoidHom.comp_apply] using h

private def w183_conjZ1 {G G' : Type} [Group G] [Group G'] {N : Type} [AddCommGroup N]
    [Module (ZMod 2) N] (e : G' ≃* G) (ρ : Representation (ZMod 2) G N) :
    ↥(Z1 (ρ.comp e.toMonoidHom)) ≃ₗ[ZMod 2] ↥(Z1 ρ) where
  toFun f := ⟨w183_conjFun e f.1, (w183_conjFun_mem_Z1 e ρ).mpr f.2⟩
  invFun f := ⟨(w183_conjFun e).symm f.1, (w183_conjFun_mem_Z1 e ρ).mp (by
    rw [LinearEquiv.apply_symm_apply]
    exact f.2)⟩
  left_inv f := Subtype.ext ((w183_conjFun e).symm_apply_apply f.1)
  right_inv f := Subtype.ext ((w183_conjFun e).apply_symm_apply f.1)
  map_add' f f' := by ext g; rfl
  map_smul' c f := by ext g; rfl

private theorem w183_conjZ1_map_comap {G G' : Type} [Group G] [Group G'] {N : Type}
    [AddCommGroup N] [Module (ZMod 2) N] (e : G' ≃* G)
    (ρ : Representation (ZMod 2) G N) :
    ((B1 (ρ.comp e.toMonoidHom)).comap (Z1 (ρ.comp e.toMonoidHom)).subtype).map
        (w183_conjZ1 e ρ).toLinearMap =
      (B1 ρ).comap (Z1 ρ).subtype := by
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_map] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have hy' : y.1 ∈ B1 (ρ.comp e.toMonoidHom) := Submodule.mem_comap.mp hy
    have hxy' : ((w183_conjZ1 e ρ) y).1 = x.1 := congrArg Subtype.val hxy
    change x.1 ∈ B1 ρ
    rw [← hxy']
    exact (w183_conjFun_mem_B1 e ρ).mpr hy'
  · intro hx
    rw [Submodule.mem_map]
    refine ⟨(w183_conjZ1 e ρ).symm x, ?_, (w183_conjZ1 e ρ).apply_symm_apply x⟩
    change ((w183_conjZ1 e ρ).symm x).1 ∈ B1 (ρ.comp e.toMonoidHom)
    refine (w183_conjFun_mem_B1 e ρ).mp ?_
    have hx' : w183_conjFun e ((w183_conjZ1 e ρ).symm x).1 ∈ B1 ρ := by
      have h := congrArg (fun z : ↥(Z1 ρ) => z.1) ((w183_conjZ1 e ρ).apply_symm_apply x)
      change w183_conjFun e ((w183_conjZ1 e ρ).symm x).1 = x.1 at h
      rw [h]
      exact hx
    exact hx'

theorem s16nt_h1_congr {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G'] {N : Type}
    [AddCommGroup N] [Module (ZMod 2) N] [Finite N] (e : G' ≃* G)
    (ρ : Representation (ZMod 2) G N) :
    Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1 (ρ.comp e.toMonoidHom)) =
      Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1 ρ) := by
  exact (Submodule.Quotient.equiv _ _ (w183_conjZ1 e ρ)
    (w183_conjZ1_map_comap e ρ)).finrank_eq

private def w183_conjH {G : Type} [Group G] {H : Subgroup G} [H.Normal] (s : G) : H ≃* H :=
  MulAut.conjNormal s

private lemma w183_conjH_apply {G : Type} [Group G] {H : Subgroup G} [H.Normal]
    (s : G) (h : H) : ((w183_conjH s h : H) : G) = s * h * s⁻¹ :=
  MulAut.conjNormal_apply s h

private lemma w183_inv_eq_self {G : Type} [Group G] {s : G} (hs : s ^ 2 = 1) : s⁻¹ = s := by
  have h : s * s = 1 := by simpa [pow_two] using hs
  exact (eq_inv_of_mul_eq_one_right h).symm

private lemma w183_conjH_apply_s {G : Type} [Group G] {H : Subgroup G} [H.Normal]
    (s : G) (hs : s ^ 2 = 1) (h : H) :
    ((w183_conjH s h : H) : G) = s * h * s := by
  rw [w183_conjH_apply, w183_inv_eq_self hs]

private lemma w183_s_mul_conjH {G : Type} [Group G] {H : Subgroup G} [H.Normal]
    (s : G) (hs : s ^ 2 = 1) (h : H) :
    s * ((w183_conjH s h : H) : G) = (h : G) * s := by
  have hss : s * s = 1 := by simpa [pow_two] using hs
  rw [w183_conjH_apply_s s hs h]
  group
  rw [hss, one_mul]

private def w183_tauFun {G : Type} [Group G] {H : Subgroup G} [H.Normal] {N : Type}
    [AddCommGroup N] [Module (ZMod 2) N] (ρ : Representation (ZMod 2) G N) (s : G) :
    (H → N) → (H → N) :=
  fun f h => ρ s (f (w183_conjH s h))

private def w183_tauLin {G : Type} [Group G] {H : Subgroup G} [H.Normal] {N : Type}
    [AddCommGroup N] [Module (ZMod 2) N] (ρ : Representation (ZMod 2) G N) (s : G) :
    (H → N) →ₗ[ZMod 2] (H → N) where
  toFun := w183_tauFun ρ s
  map_add' f g := by funext h; simp [w183_tauFun, map_add]
  map_smul' c f := by funext h; simp [w183_tauFun, map_smul]

private lemma w183_tauLin_mem_Z1 {G : Type} [Group G] {H : Subgroup G} [H.Normal]
    {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    (ρ : Representation (ZMod 2) G N) (s : G) (hs : s ^ 2 = 1) {f : H → N}
    (hf : f ∈ Z1 (ρ.comp H.subtype)) :
    w183_tauLin ρ s f ∈ Z1 (ρ.comp H.subtype) := by
  intro h1 h2
  change ρ s (f (w183_conjH s (h1 * h2))) =
    ρ s (f (w183_conjH s h1)) + ρ (h1 : G) (ρ s (f (w183_conjH s h2)))
  rw [map_mul]
  have h := hf (w183_conjH s h1) (w183_conjH s h2)
  change f (w183_conjH s h1 * w183_conjH s h2) =
    f (w183_conjH s h1) + ρ ((w183_conjH s h1 : H) : G) (f (w183_conjH s h2)) at h
  rw [h, map_add]
  congr 1
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  rw [w183_s_mul_conjH s hs h1]

private lemma w183_add_self {M : Type} [AddCommGroup M] [Module (ZMod 2) M] (x : M) :
    x + x = 0 := by
  calc x + x = 2 • x := (two_nsmul x).symm
    _ = (2 : ZMod 2) • x := (Nat.cast_smul_eq_nsmul (R := ZMod 2) 2 x).symm
    _ = 0 := by rw [show (2 : ZMod 2) = 0 by decide, zero_smul]

private lemma w183_tauLin_comp_self {G : Type} [Group G] {H : Subgroup G} [H.Normal]
    {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    (ρ : Representation (ZMod 2) G N) (s : G) (hs : s ^ 2 = 1) :
    (w183_tauLin (H := H) ρ s).comp (w183_tauLin (H := H) ρ s) = LinearMap.id := by
  ext f h
  change ρ s (ρ s (f (w183_conjH s (w183_conjH s h)))) = f h
  have hss : s * s = 1 := by simpa [pow_two] using hs
  have hconj : w183_conjH s (w183_conjH s h) = h := by
    have h1 : w183_conjH (H := H) s * w183_conjH (H := H) s = 1 := by
      change MulAut.conjNormal s * MulAut.conjNormal s = 1
      rw [← map_mul, hss, map_one]
    have := congrArg (fun e : H ≃* H => e h) h1
    simpa using this
  rw [hconj]
  rw [← Module.End.mul_apply, ← map_mul, hss, map_one]
  rfl

private lemma w183_tauLin_coboundary {G : Type} [Group G] {H : Subgroup G} [H.Normal]
    {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    (ρ : Representation (ZMod 2) G N) (s : G) (hs : s ^ 2 = 1) (n : N) :
    w183_tauLin ρ s (coboundary (ρ.comp H.subtype) n) =
      coboundary (ρ.comp H.subtype) (ρ s n) := by
  funext h
  change ρ s (ρ (w183_conjH s h : G) n - n) = ρ (h : G) (ρ s n) - ρ s n
  rw [map_sub]
  congr 1
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  rw [w183_s_mul_conjH s hs h]

private def w183_tauZ {G : Type} [Group G] {H : Subgroup G} [H.Normal] {N : Type}
    [AddCommGroup N] [Module (ZMod 2) N] (ρ : Representation (ZMod 2) G N) (s : G)
    (hs : s ^ 2 = 1) : ↥(Z1 (ρ.comp H.subtype)) →ₗ[ZMod 2] ↥(Z1 (ρ.comp H.subtype)) where
  toFun f := ⟨w183_tauLin ρ s f.1, w183_tauLin_mem_Z1 (H := H) ρ s hs f.2⟩
  map_add' f g := by
    apply Subtype.ext
    funext h
    simp [w183_tauLin, w183_tauFun, map_add]
  map_smul' c f := by
    apply Subtype.ext
    funext h
    simp [w183_tauLin, w183_tauFun, map_smul]

private lemma w183_tauZ_comp_self {G : Type} [Group G] {H : Subgroup G} [H.Normal]
    {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    (ρ : Representation (ZMod 2) G N) (s : G) (hs : s ^ 2 = 1) :
    (w183_tauZ (H := H) ρ s hs).comp (w183_tauZ (H := H) ρ s hs) = LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext h
  change w183_tauLin ρ s (w183_tauLin ρ s f.1) h = f.1 h
  have := congrFun (congrArg (fun L : (H → N) →ₗ[ZMod 2] (H → N) => L f.1)
    (w183_tauLin_comp_self (H := H) ρ s hs)) h
  simpa using this

private lemma w183_tauZ_coboundary {G : Type} [Group G] {H : Subgroup G} [H.Normal]
    {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    (ρ : Representation (ZMod 2) G N) (s : G) (hs : s ^ 2 = 1) (n : N) :
    w183_tauZ ρ s hs ⟨coboundary (ρ.comp H.subtype) n, (B1_le_Z1 _) ⟨n, rfl⟩⟩ =
      ⟨coboundary (ρ.comp H.subtype) (ρ s n), (B1_le_Z1 _) ⟨ρ s n, rfl⟩⟩ := by
  apply Subtype.ext
  exact w183_tauLin_coboundary (H := H) ρ s hs n

private def w183_B1H {G : Type} [Group G] (H : Subgroup G) {N : Type} [AddCommGroup N]
    [Module (ZMod 2) N] (ρ : Representation (ZMod 2) G N) :
    Submodule (ZMod 2) ↥(Z1 (ρ.comp H.subtype)) :=
  (B1 (ρ.comp H.subtype)).comap (Z1 (ρ.comp H.subtype)).subtype

private lemma w183_tauZ_mem_B1H {G : Type} [Group G] {H : Subgroup G} [H.Normal]
    {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    (ρ : Representation (ZMod 2) G N) (s : G) (hs : s ^ 2 = 1)
    {f : ↥(Z1 (ρ.comp H.subtype))} (hf : f ∈ w183_B1H H ρ) :
    w183_tauZ ρ s hs f ∈ w183_B1H H ρ := by
  change f.1 ∈ B1 (ρ.comp H.subtype) at hf
  change (w183_tauZ ρ s hs f).1 ∈ B1 (ρ.comp H.subtype)
  obtain ⟨n, hn⟩ := LinearMap.mem_range.mp hf
  have h1 : (w183_tauZ ρ s hs f).1 = coboundary (ρ.comp H.subtype) (ρ s n) := by
    change w183_tauLin ρ s f.1 = coboundary (ρ.comp H.subtype) (ρ s n)
    rw [← hn]
    exact w183_tauLin_coboundary (H := H) ρ s hs n
  rw [h1]
  exact ⟨ρ s n, rfl⟩

private lemma w183_neg_eq_self {M : Type} [AddCommGroup M] [Module (ZMod 2) M] (x : M) :
    -x = x := (eq_neg_of_add_eq_zero_right (w183_add_self x)).symm

private lemma w183_sub_eq_add {M : Type} [AddCommGroup M] [Module (ZMod 2) M] (x y : M) :
    x - y = x + y := by
  rw [sub_eq_add_neg, w183_neg_eq_self]

private lemma w183_rho_mul_apply {G : Type} [Group G] {N : Type} [AddCommGroup N]
    [Module (ZMod 2) N] (ρ : Representation (ZMod 2) G N) (a b : G) (x : N) :
    ρ (a * b) x = ρ a (ρ b x) := by
  rw [map_mul, Module.End.mul_apply]

private lemma w183_conj_mul {G : Type} [Group G] {s : G} (hs : s ^ 2 = 1) (a b : G) :
    (a * s) * (s * b) = a * b := by
  rw [mul_assoc, ← mul_assoc s s b, show s * s = 1 by simpa [pow_two] using hs, one_mul]

private lemma w183_conj_mul_s {G : Type} [Group G] {s : G} (hs : s ^ 2 = 1) (a b : G) :
    (a * s) * (s * b * s) = a * b * s := by
  rw [show (a * s) * (s * b * s) = (a * s) * (s * (b * s)) by group]
  rw [w183_conj_mul hs a (b * s)]
  group

private lemma w183_mul_s_s {G : Type} [Group G] {s : G} (hs : s ^ 2 = 1) (a : G) :
    a * s * s = a := by
  rw [mul_assoc, show s * s = 1 by simpa [pow_two] using hs, mul_one]

private lemma w183_eq_mul_s_s {G : Type} [Group G] {s : G} (hs : s ^ 2 = 1) (a : G) :
    a = (a * s) * s := (w183_mul_s_s hs a).symm

private noncomputable def w183_extendFun {G : Type} [Group G] {H : Subgroup G} [H.Normal]
    {N : Type} [AddCommGroup N] [Module (ZMod 2) N] (ρ : Representation (ZMod 2) G N) (s : G)
    (hG : ∀ g : G, g ∈ H ∨ g * s ∈ H) (f : H → N) (b : N) : G → N := by
  classical
  exact fun g => if hg : g ∈ H then f ⟨g, hg⟩
    else f ⟨g * s, (hG g).resolve_left hg⟩ + ρ (g * s) b

private lemma w183_extendFun_of_mem {G : Type} [Group G] {H : Subgroup G} [H.Normal]
    {N : Type} [AddCommGroup N] [Module (ZMod 2) N] (ρ : Representation (ZMod 2) G N) (s : G)
    (hG : ∀ g : G, g ∈ H ∨ g * s ∈ H) (f : H → N) (b : N) {g : G} (hg : g ∈ H) :
    w183_extendFun ρ s hG f b g = f ⟨g, hg⟩ := by
  classical
  simp only [w183_extendFun, dif_pos hg]

private lemma w183_extendFun_of_not_mem {G : Type} [Group G] {H : Subgroup G} [H.Normal]
    {N : Type} [AddCommGroup N] [Module (ZMod 2) N] (ρ : Representation (ZMod 2) G N) (s : G)
    (hG : ∀ g : G, g ∈ H ∨ g * s ∈ H) (f : H → N) (b : N) {g : G} (hg : g ∉ H) :
    w183_extendFun ρ s hG f b g =
      f ⟨g * s, (hG g).resolve_left hg⟩ + ρ (g * s) b := by
  classical
  simp only [w183_extendFun, dif_neg hg]

private theorem w183_extend_cocycle {G : Type} [Group G] {H : Subgroup G} [H.Normal]
    {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    (ρ : Representation (ZMod 2) G N) {s : G} (hs : s ^ 2 = 1)
    (hG : ∀ g : G, g ∈ H ∨ g * s ∈ H) {f : H → N}
    (hf : f ∈ Z1 (ρ.comp H.subtype)) {b : N}
    (hb : ∀ h : H, ρ s (f (w183_conjH s h)) = f h + (ρ (h : G) b + b))
    (hsb : ρ s b = b) :
    w183_extendFun ρ s hG f b ∈ Z1 ρ := by
  have hss : s * s = 1 := by simpa [pow_two] using hs
  intro g₁ g₂
  by_cases h1 : g₁ ∈ H
  · by_cases h2 : g₂ ∈ H
    · have h12 : g₁ * g₂ ∈ H := H.mul_mem h1 h2
      rw [w183_extendFun_of_mem ρ s hG f b h12,
          w183_extendFun_of_mem ρ s hG f b h1,
          w183_extendFun_of_mem ρ s hG f b h2]
      have hmul : (⟨g₁, h1⟩ * ⟨g₂, h2⟩ : H) = ⟨g₁ * g₂, h12⟩ :=
        Subtype.ext (by rw [Subgroup.coe_mul])
      have h := hf ⟨g₁, h1⟩ ⟨g₂, h2⟩
      rw [hmul] at h
      exact h
    · have h2s : g₂ * s ∈ H := (hG g₂).resolve_left h2
      have h12 : g₁ * g₂ ∉ H := by
        intro hc
        apply h2
        have hg : g₂ = g₁⁻¹ * (g₁ * g₂) := by group
        rw [hg]
        exact H.mul_mem (H.inv_mem h1) hc
      have h12s : (g₁ * g₂) * s ∈ H := (hG (g₁ * g₂)).resolve_left h12
      rw [w183_extendFun_of_not_mem ρ s hG f b h12,
          w183_extendFun_of_mem ρ s hG f b h1,
          w183_extendFun_of_not_mem ρ s hG f b h2]
      have hmul : (⟨g₁, h1⟩ * ⟨g₂ * s, h2s⟩ : H) = ⟨(g₁ * g₂) * s, h12s⟩ :=
        Subtype.ext (by rw [Subgroup.coe_mul]; group)
      have hcoc : f ⟨(g₁ * g₂) * s, h12s⟩ =
          f ⟨g₁, h1⟩ + ρ g₁ (f ⟨g₂ * s, h2s⟩) := by
        have h := hf ⟨g₁, h1⟩ ⟨g₂ * s, h2s⟩
        rwa [hmul] at h
      rw [hcoc, map_add]
      rw [show ρ ((g₁ * g₂) * s) b = ρ g₁ (ρ (g₂ * s) b) by
        rw [show (g₁ * g₂) * s = g₁ * (g₂ * s) by group]
        exact w183_rho_mul_apply ρ g₁ (g₂ * s) b]
      abel
  · by_cases h2 : g₂ ∈ H
    · have h1s : g₁ * s ∈ H := (hG g₁).resolve_left h1
      have h12 : g₁ * g₂ ∉ H := by
        intro hc
        apply h1
        have hg : g₁ = (g₁ * g₂) * g₂⁻¹ := by group
        rw [hg]
        exact H.mul_mem hc (H.inv_mem h2)
      have h12s : (g₁ * g₂) * s ∈ H := (hG (g₁ * g₂)).resolve_left h12
      rw [w183_extendFun_of_not_mem ρ s hG f b h12,
          w183_extendFun_of_not_mem ρ s hG f b h1,
          w183_extendFun_of_mem ρ s hG f b h2]
      have hmul : (⟨g₁ * s, h1s⟩ * w183_conjH s ⟨g₂, h2⟩ : H) =
          ⟨(g₁ * g₂) * s, h12s⟩ :=
        Subtype.ext (by
          rw [Subgroup.coe_mul, w183_conjH_apply_s s hs]
          calc (g₁ * s) * (s * g₂ * s)
              = (g₁ * (s * s)) * g₂ * s := by group
            _ = (g₁ * 1) * g₂ * s := by rw [hss]
            _ = (g₁ * g₂) * s := by rw [mul_one])
      have hcoc : f ⟨(g₁ * g₂) * s, h12s⟩ =
          f ⟨g₁ * s, h1s⟩ + ρ (g₁ * s) (f (w183_conjH s ⟨g₂, h2⟩)) := by
        have h := hf ⟨g₁ * s, h1s⟩ (w183_conjH s ⟨g₂, h2⟩)
        rwa [hmul] at h
      have hconj : w183_conjH s (w183_conjH s ⟨g₂, h2⟩) = ⟨g₂, h2⟩ := by
        have h1' : w183_conjH (H := H) s * w183_conjH (H := H) s = 1 := by
          change MulAut.conjNormal s * MulAut.conjNormal s = 1
          rw [← map_mul, hss, map_one]
        have := congrArg (fun e : H ≃* H => e ⟨g₂, h2⟩) h1'
        simpa using this
      have hkey : f (w183_conjH s ⟨g₂, h2⟩) +
            ρ ((w183_conjH s ⟨g₂, h2⟩ : H) : G) b = b + ρ s (f ⟨g₂, h2⟩) := by
        have hb' := hb (w183_conjH s ⟨g₂, h2⟩)
        rw [hconj] at hb'
        have hfh : f (w183_conjH s ⟨g₂, h2⟩) =
            ρ s (f ⟨g₂, h2⟩) + (ρ ((w183_conjH s ⟨g₂, h2⟩ : H) : G) b + b) := by
          rw [hb']
          rw [show (f (w183_conjH s ⟨g₂, h2⟩) +
                (ρ ((w183_conjH s ⟨g₂, h2⟩ : H) : G) b + b)) +
                (ρ ((w183_conjH s ⟨g₂, h2⟩ : H) : G) b + b) =
              f (w183_conjH s ⟨g₂, h2⟩) +
                ((ρ ((w183_conjH s ⟨g₂, h2⟩ : H) : G) b + b) +
                  (ρ ((w183_conjH s ⟨g₂, h2⟩ : H) : G) b + b)) by abel,
            w183_add_self (ρ ((w183_conjH s ⟨g₂, h2⟩ : H) : G) b + b), add_zero]
        calc f (w183_conjH s ⟨g₂, h2⟩) +
              ρ ((w183_conjH s ⟨g₂, h2⟩ : H) : G) b
            = (ρ s (f ⟨g₂, h2⟩) +
                (ρ ((w183_conjH s ⟨g₂, h2⟩ : H) : G) b + b)) +
                ρ ((w183_conjH s ⟨g₂, h2⟩ : H) : G) b := by rw [hfh]
          _ = b + ρ s (f ⟨g₂, h2⟩) := by
              rw [show (ρ s (f ⟨g₂, h2⟩) +
                    (ρ ((w183_conjH s ⟨g₂, h2⟩ : H) : G) b + b)) +
                    ρ ((w183_conjH s ⟨g₂, h2⟩ : H) : G) b =
                  (ρ s (f ⟨g₂, h2⟩) + b) +
                    (ρ ((w183_conjH s ⟨g₂, h2⟩ : H) : G) b +
                      ρ ((w183_conjH s ⟨g₂, h2⟩ : H) : G) b) by abel,
                w183_add_self (ρ ((w183_conjH s ⟨g₂, h2⟩ : H) : G) b), add_zero]
              rw [add_comm]
      calc f ⟨(g₁ * g₂) * s, h12s⟩ + ρ ((g₁ * g₂) * s) b
          = (f ⟨g₁ * s, h1s⟩ + ρ (g₁ * s) (f (w183_conjH s ⟨g₂, h2⟩))) +
              ρ ((g₁ * g₂) * s) b := by rw [hcoc]
        _ = (f ⟨g₁ * s, h1s⟩ + ρ (g₁ * s) (f (w183_conjH s ⟨g₂, h2⟩))) +
              ρ (g₁ * s) (ρ ((w183_conjH s ⟨g₂, h2⟩ : H) : G) b) := by
              rw [show ρ ((g₁ * g₂) * s) b =
                  ρ (g₁ * s) (ρ ((w183_conjH s ⟨g₂, h2⟩ : H) : G) b) by
                rw [show (g₁ * g₂) * s =
                      (g₁ * s) * ((w183_conjH s ⟨g₂, h2⟩ : H) : G) by
                  rw [w183_conjH_apply_s s hs]
                  exact (w183_conj_mul_s hs g₁ g₂).symm]
                exact w183_rho_mul_apply ρ (g₁ * s)
                  ((w183_conjH s ⟨g₂, h2⟩ : H) : G) b]
        _ = f ⟨g₁ * s, h1s⟩ + ρ (g₁ * s)
              (f (w183_conjH s ⟨g₂, h2⟩) +
                ρ ((w183_conjH s ⟨g₂, h2⟩ : H) : G) b) := by
              rw [map_add]; abel
        _ = f ⟨g₁ * s, h1s⟩ + ρ (g₁ * s) (b + ρ s (f ⟨g₂, h2⟩)) := by rw [hkey]
        _ = (f ⟨g₁ * s, h1s⟩ + ρ (g₁ * s) b) + ρ (g₁ * s) (ρ s (f ⟨g₂, h2⟩)) := by
              rw [map_add]; abel
        _ = (f ⟨g₁ * s, h1s⟩ + ρ (g₁ * s) b) + ρ g₁ (f ⟨g₂, h2⟩) := by
              rw [show ρ g₁ (f ⟨g₂, h2⟩) = ρ (g₁ * s) (ρ s (f ⟨g₂, h2⟩)) by
                conv_lhs => rw [w183_eq_mul_s_s hs g₁]
                exact w183_rho_mul_apply ρ (g₁ * s) s (f ⟨g₂, h2⟩)]
    · have h1s : g₁ * s ∈ H := (hG g₁).resolve_left h1
      have h2s : g₂ * s ∈ H := (hG g₂).resolve_left h2
      have hconj : ((w183_conjH s ⟨g₂ * s, h2s⟩ : H) : G) = s * g₂ := by
        rw [w183_conjH_apply_s s hs]
        calc s * (g₂ * s) * s = (s * g₂) * (s * s) := by group
          _ = (s * g₂) * 1 := by rw [hss]
          _ = s * g₂ := by rw [mul_one]
      have h12 : g₁ * g₂ ∈ H := by
        have hg : g₁ * g₂ = (g₁ * s) * (w183_conjH s ⟨g₂ * s, h2s⟩) := by
          rw [hconj]
          rw [show (g₁ * s) * (s * g₂) = (g₁ * (s * s)) * g₂ by group, hss, mul_one]
        rw [hg]
        exact H.mul_mem h1s (w183_conjH s ⟨g₂ * s, h2s⟩).2
      have hmem : w183_conjH s (w183_conjH s ⟨g₂ * s, h2s⟩) = ⟨g₂ * s, h2s⟩ := by
        have h1' : w183_conjH (H := H) s * w183_conjH (H := H) s = 1 := by
          change MulAut.conjNormal s * MulAut.conjNormal s = 1
          rw [← map_mul, hss, map_one]
        have := congrArg (fun e : H ≃* H => e ⟨g₂ * s, h2s⟩) h1'
        simpa using this
      have hsgs : s * g₂ = (s * g₂ * s) * s := by
        rw [show (s * g₂ * s) * s = s * g₂ * (s * s) by group, hss, mul_one]
      have hsb' : ρ (s * g₂) b = ρ (s * g₂ * s) b := by
        conv_lhs => rw [hsgs]
        rw [w183_rho_mul_apply ρ (s * g₂ * s) s b, hsb]
      have hkey : f (w183_conjH s ⟨g₂ * s, h2s⟩) =
          b + ρ s (f ⟨g₂ * s, h2s⟩) + ρ (s * g₂ * s) b := by
        have hb' := hb (w183_conjH s ⟨g₂ * s, h2s⟩)
        rw [hmem, hconj, hsb'] at hb'
        have hfh : f (w183_conjH s ⟨g₂ * s, h2s⟩) =
            ρ s (f ⟨g₂ * s, h2s⟩) + (ρ (s * g₂ * s) b + b) := by
          rw [hb']
          rw [show (f (w183_conjH s ⟨g₂ * s, h2s⟩) + (ρ (s * g₂ * s) b + b)) +
                (ρ (s * g₂ * s) b + b) =
              f (w183_conjH s ⟨g₂ * s, h2s⟩) +
                ((ρ (s * g₂ * s) b + b) + (ρ (s * g₂ * s) b + b)) by abel,
            w183_add_self (ρ (s * g₂ * s) b + b), add_zero]
        rw [hfh]
        abel
      have hρs : ρ s (f ⟨g₂ * s, h2s⟩ + ρ (g₂ * s) b) =
          ρ s (f ⟨g₂ * s, h2s⟩) + ρ (s * g₂ * s) b := by
        rw [map_add, show ρ s (ρ (g₂ * s) b) = ρ (s * g₂ * s) b by
          rw [← w183_rho_mul_apply ρ s (g₂ * s) b,
            show s * (g₂ * s) = s * g₂ * s by group]]
      have hρg1 : ρ g₁ (f ⟨g₂ * s, h2s⟩ + ρ (g₂ * s) b) =
          ρ (g₁ * s) (ρ s (f ⟨g₂ * s, h2s⟩) + ρ (s * g₂ * s) b) := by
        calc ρ g₁ (f ⟨g₂ * s, h2s⟩ + ρ (g₂ * s) b)
            = ρ ((g₁ * s) * s) (f ⟨g₂ * s, h2s⟩ + ρ (g₂ * s) b) := by
                conv_lhs => rw [w183_eq_mul_s_s hs g₁]
          _ = ρ (g₁ * s) (ρ s (f ⟨g₂ * s, h2s⟩ + ρ (g₂ * s) b)) :=
                w183_rho_mul_apply ρ (g₁ * s) s _
          _ = ρ (g₁ * s) (ρ s (f ⟨g₂ * s, h2s⟩) + ρ (s * g₂ * s) b) := by rw [hρs]
      have hmul : (⟨g₁ * s, h1s⟩ * w183_conjH s ⟨g₂ * s, h2s⟩ : H) = ⟨g₁ * g₂, h12⟩ :=
        Subtype.ext (by
          rw [Subgroup.coe_mul, hconj]
          calc (g₁ * s) * (s * g₂) = (g₁ * (s * s)) * g₂ := by group
            _ = (g₁ * 1) * g₂ := by rw [hss]
            _ = g₁ * g₂ := by rw [mul_one])
      have hcoc : f ⟨g₁ * g₂, h12⟩ =
          f ⟨g₁ * s, h1s⟩ + ρ (g₁ * s) (f (w183_conjH s ⟨g₂ * s, h2s⟩)) := by
        have h := hf ⟨g₁ * s, h1s⟩ (w183_conjH s ⟨g₂ * s, h2s⟩)
        rwa [hmul] at h
      calc w183_extendFun ρ s hG f b (g₁ * g₂)
          = f ⟨g₁ * g₂, h12⟩ := w183_extendFun_of_mem ρ s hG f b h12
        _ = f ⟨g₁ * s, h1s⟩ + ρ (g₁ * s) (f (w183_conjH s ⟨g₂ * s, h2s⟩)) := by
              rw [hcoc]
        _ = f ⟨g₁ * s, h1s⟩ + ρ (g₁ * s) (b + ρ s (f ⟨g₂ * s, h2s⟩) +
              ρ (s * g₂ * s) b) := by rw [hkey]
        _ = (f ⟨g₁ * s, h1s⟩ + ρ (g₁ * s) b) +
              ρ g₁ (f ⟨g₂ * s, h2s⟩ + ρ (g₂ * s) b) := by
              rw [hρg1]
              simp only [map_add]
              abel
        _ = w183_extendFun ρ s hG f b g₁ + ρ g₁ (w183_extendFun ρ s hG f b g₂) := by
              rw [w183_extendFun_of_not_mem ρ s hG f b h1,
                  w183_extendFun_of_not_mem ρ s hG f b h2]

private lemma w183_rho_s_b_eq {G : Type} [Group G] {H : Subgroup G} [H.Normal]
    {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    (ρ : Representation (ZMod 2) G N) (s : G) (hs : s ^ 2 = 1)
    (hfix : ∀ n : N, (∀ h : H, ρ h n = n) → n = 0)
    {f : ↥(Z1 (ρ.comp H.subtype))} {b : N}
    (hb : w183_tauZ (H := H) ρ s hs f - f =
      ⟨coboundary (ρ.comp H.subtype) b, (B1_le_Z1 _) ⟨b, rfl⟩⟩) :
    ρ s b = b := by
  have hττ : w183_tauZ (H := H) ρ s hs (w183_tauZ (H := H) ρ s hs f) = f := by
    have := congrArg (fun L : ↥(Z1 (ρ.comp H.subtype)) →ₗ[ZMod 2]
      ↥(Z1 (ρ.comp H.subtype)) => L f) (w183_tauZ_comp_self (H := H) ρ s hs)
    simpa using this
  have hτ : w183_tauZ (H := H) ρ s hs
      (w183_tauZ (H := H) ρ s hs f - f) =
      w183_tauZ (H := H) ρ s hs
        ⟨coboundary (ρ.comp H.subtype) b, (B1_le_Z1 _) ⟨b, rfl⟩⟩ := by
    rw [hb]
  have hleft : w183_tauZ (H := H) ρ s hs
      (w183_tauZ (H := H) ρ s hs f - f) =
      w183_tauZ (H := H) ρ s hs f - f := by
    rw [map_sub, hττ, w183_sub_eq_add, w183_sub_eq_add, add_comm]
  have hright : w183_tauZ (H := H) ρ s hs
      ⟨coboundary (ρ.comp H.subtype) b, (B1_le_Z1 _) ⟨b, rfl⟩⟩ =
      ⟨coboundary (ρ.comp H.subtype) (ρ s b), (B1_le_Z1 _) ⟨ρ s b, rfl⟩⟩ :=
    w183_tauZ_coboundary (H := H) ρ s hs b
  have hδ : w183_tauZ (H := H) ρ s hs f - f =
      ⟨coboundary (ρ.comp H.subtype) (ρ s b), (B1_le_Z1 _) ⟨ρ s b, rfl⟩⟩ := by
    rw [← hleft, hτ, hright]
  have hb' : coboundary (ρ.comp H.subtype) b = (w183_tauZ (H := H) ρ s hs f - f).1 :=
    (congrArg Subtype.val hb).symm
  have hδ' : (w183_tauZ (H := H) ρ s hs f - f).1 =
      coboundary (ρ.comp H.subtype) (ρ s b) := congrArg Subtype.val hδ
  have hδ'' : coboundary (ρ.comp H.subtype) b =
      coboundary (ρ.comp H.subtype) (ρ s b) := hb'.trans hδ'
  have hzero : coboundary (ρ.comp H.subtype) (b - ρ s b) = 0 := by
    rw [map_sub, hδ'', sub_self]
  have hinv : ∀ h : H, ρ h (b - ρ s b) = b - ρ s b := by
    intro h
    have := congrFun hzero h
    change ρ h (b - ρ s b) - (b - ρ s b) = 0 at this
    exact sub_eq_zero.mp this
  have hfix' : b - ρ s b = 0 := hfix (b - ρ s b) hinv
  rw [w183_sub_eq_add] at hfix'
  have : b = -ρ s b := eq_neg_of_add_eq_zero_left hfix'
  rw [w183_neg_eq_self] at this
  exact this.symm

private def w183_tauBar {G : Type} [Group G] {H : Subgroup G} [H.Normal] {N : Type}
    [AddCommGroup N] [Module (ZMod 2) N] (ρ : Representation (ZMod 2) G N) (s : G)
    (hs : s ^ 2 = 1) :
    CFSG.Quasithin.JonesParshall.H1 (ρ.comp H.subtype) →ₗ[ZMod 2]
      CFSG.Quasithin.JonesParshall.H1 (ρ.comp H.subtype) :=
  (w183_B1H H ρ).mapQ (w183_B1H H ρ) (w183_tauZ ρ s hs)
    (fun x hx => w183_tauZ_mem_B1H ρ s hs hx)

private lemma w183_tauBar_comp_self {G : Type} [Group G] {H : Subgroup G} [H.Normal]
    {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    (ρ : Representation (ZMod 2) G N) (s : G) (hs : s ^ 2 = 1) :
    (w183_tauBar (H := H) ρ s hs).comp (w183_tauBar (H := H) ρ s hs) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on (p := w183_B1H H ρ) x ?_
  intro f
  change Submodule.Quotient.mk (w183_tauZ ρ s hs (w183_tauZ ρ s hs f)) =
    Submodule.Quotient.mk f
  have hf : w183_tauZ ρ s hs (w183_tauZ ρ s hs f) = f := by
    have := congrArg (fun L : ↥(Z1 (ρ.comp H.subtype)) →ₗ[ZMod 2]
      ↥(Z1 (ρ.comp H.subtype)) => L f) (w183_tauZ_comp_self (H := H) ρ s hs)
    simpa using this
  rw [hf]

private def w183_B1G {G : Type} [Group G] {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    (ρ : Representation (ZMod 2) G N) : Submodule (ZMod 2) ↥(Z1 ρ) :=
  (B1 ρ).comap (Z1 ρ).subtype

private def w183_resZ {G : Type} [Group G] (H : Subgroup G) {N : Type} [AddCommGroup N]
    [Module (ZMod 2) N] (ρ : Representation (ZMod 2) G N) :
    ↥(Z1 ρ) →ₗ[ZMod 2] ↥(Z1 (ρ.comp H.subtype)) where
  toFun F := ⟨fun h => F.1 (h : G), by
    intro a b
    have h := F.2 (a : G) (b : G)
    change F.1 ((a : G) * (b : G)) = F.1 (a : G) + ρ (a : G) (F.1 (b : G))
    exact h⟩
  map_add' F F' := by ext h; rfl
  map_smul' c F := by ext h; rfl

private lemma w183_resZ_mem_B1H {G : Type} [Group G] {H : Subgroup G} [H.Normal] {N : Type}
    [AddCommGroup N] [Module (ZMod 2) N] (ρ : Representation (ZMod 2) G N)
    {F : ↥(Z1 ρ)} (hF : F ∈ w183_B1G ρ) :
    w183_resZ H ρ F ∈ w183_B1H H ρ := by
  obtain ⟨n, hn⟩ := LinearMap.mem_range.mp (Submodule.mem_comap.mp hF)
  refine ⟨n, funext fun h => ?_⟩
  have hh := congrFun hn (h : G)
  change ρ (h : G) n - n = F.1 (h : G)
  exact hh

private def w183_resBar {G : Type} [Group G] {H : Subgroup G} [H.Normal] {N : Type}
    [AddCommGroup N] [Module (ZMod 2) N] (ρ : Representation (ZMod 2) G N) :
    CFSG.Quasithin.JonesParshall.H1 ρ →ₗ[ZMod 2]
      CFSG.Quasithin.JonesParshall.H1 (ρ.comp H.subtype) :=
  (w183_B1G ρ).mapQ (w183_B1H H ρ) (w183_resZ H ρ)
    (fun x hx => w183_resZ_mem_B1H ρ hx)

private lemma w183_Z1_tau_restrict {G : Type} [Group G] {H : Subgroup G} [H.Normal] {N : Type}
    [AddCommGroup N] [Module (ZMod 2) N] (ρ : Representation (ZMod 2) G N) (s : G)
    (hs : s ^ 2 = 1) {F : G → N} (hF : F ∈ Z1 ρ) (h : H) :
    ρ s (F (w183_conjH s h)) - F (h : G) = ρ (h : G) (F s) - F s := by
  have hss : s * s = 1 := by simpa [pow_two] using hs
  have hF1 : F 1 = 0 := by
    have h := hF 1 1
    simp only [one_mul, map_one, Module.End.one_apply] at h
    have h' : F 1 + 0 = F 1 + F 1 := by rw [add_zero]; exact h
    exact (add_left_cancel h').symm
  have hFs : ρ s (F s) = F s := by
    have h := hF s s
    rw [← pow_two, hs, hF1] at h
    have h3 : ρ s (F s) = -F s := eq_neg_of_add_eq_zero_right h.symm
    rwa [w183_neg_eq_self] at h3
  have hr1 : F (s * (h : G)) = F s + ρ s (F (h : G)) := by
    have := hF s (h : G)
    simpa using this
  have hr3 : F (w183_conjH s h) = F (s * (h : G)) + ρ (s * (h : G)) (F s) := by
    have hh := hF (s * (h : G)) s
    rw [← w183_conjH_apply_s s hs h] at hh
    exact hh
  have hstep : ρ s (F (w183_conjH s h)) = ρ s (F s) + F (h : G) + ρ (h : G) (F s) := by
    rw [hr3, hr1]
    simp only [map_add]
    rw [show ρ s (ρ s (F (h : G))) = F (h : G) by
          rw [← Module.End.mul_apply, ← map_mul, hss, map_one, Module.End.one_apply]]
    rw [show ρ s (ρ (s * (h : G)) (F s)) = ρ (h : G) (F s) by
          rw [← Module.End.mul_apply, ← map_mul, show s * (s * (h : G)) = (h : G) by
                rw [← mul_assoc, hss, one_mul]]]
  calc ρ s (F (w183_conjH s h)) - F (h : G)
      = (ρ s (F s) + F (h : G) + ρ (h : G) (F s)) - F (h : G) := by rw [hstep]
    _ = ρ (h : G) (F s) - F s := by
        rw [w183_sub_eq_add, w183_sub_eq_add, hFs]
        rw [show (F s + F (h : G) + ρ (h : G) (F s)) + F (h : G) =
              F s + ρ (h : G) (F s) + (F (h : G) + F (h : G)) by abel,
            w183_add_self (F (h : G)), add_zero]
        abel

private lemma w183_resBar_tauBar {G : Type} [Group G] {H : Subgroup G} [H.Normal] {N : Type}
    [AddCommGroup N] [Module (ZMod 2) N] (ρ : Representation (ZMod 2) G N) (s : G)
    (hs : s ^ 2 = 1) :
    (w183_tauBar (H := H) ρ s hs).comp (w183_resBar (H := H) ρ) =
      w183_resBar (H := H) ρ := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply]
  refine Submodule.Quotient.induction_on (p := w183_B1G ρ) x ?_
  intro F
  have hdelta : w183_tauZ (H := H) ρ s hs (w183_resZ H ρ F) - w183_resZ H ρ F =
      ⟨coboundary (ρ.comp H.subtype) (F.1 s), (B1_le_Z1 _) ⟨F.1 s, rfl⟩⟩ := by
    apply Subtype.ext
    funext h
    change ρ s (F.1 (w183_conjH s h)) - F.1 (h : G) =
      coboundary (ρ.comp H.subtype) (F.1 s) h
    exact w183_Z1_tau_restrict ρ s hs F.2 h
  change Submodule.Quotient.mk (w183_tauZ (H := H) ρ s hs (w183_resZ H ρ F)) =
    Submodule.Quotient.mk (w183_resZ H ρ F)
  rw [Submodule.Quotient.eq]
  rw [hdelta]
  exact ⟨F.1 s, rfl⟩

private lemma w183_tauBar_sub_one_comp_self {G : Type} [Group G] {H : Subgroup G} [H.Normal]
    {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    (ρ : Representation (ZMod 2) G N) (s : G) (hs : s ^ 2 = 1) :
    ((w183_tauBar (H := H) ρ s hs) - 1).comp
        ((w183_tauBar (H := H) ρ s hs) - 1) = 0 := by
  apply LinearMap.ext
  intro x
  change (w183_tauBar (H := H) ρ s hs - 1)
      ((w183_tauBar (H := H) ρ s hs - 1) x) = 0
  have hT : w183_tauBar (H := H) ρ s hs (w183_tauBar (H := H) ρ s hs x) = x := by
    have := congrArg (fun L : CFSG.Quasithin.JonesParshall.H1 (ρ.comp H.subtype) →ₗ[ZMod 2]
      CFSG.Quasithin.JonesParshall.H1 (ρ.comp H.subtype) => L x)
      (w183_tauBar_comp_self (H := H) ρ s hs)
    simpa using this
  have hinner : (w183_tauBar (H := H) ρ s hs - 1) x =
      w183_tauBar (H := H) ρ s hs x - x := by
    rw [LinearMap.sub_apply, Module.End.one_apply]
  rw [hinner, LinearMap.sub_apply, Module.End.one_apply, map_sub, hT]
  simp only [w183_sub_eq_add]
  rw [show (x + w183_tauBar (H := H) ρ s hs x) +
        (w183_tauBar (H := H) ρ s hs x + x) =
      (x + x) + (w183_tauBar (H := H) ρ s hs x + w183_tauBar (H := H) ρ s hs x)
      by abel,
    w183_add_self x, w183_add_self (w183_tauBar (H := H) ρ s hs x), zero_add]

private lemma w183_mem_range_resBar {G : Type} [Group G] {H : Subgroup G} [H.Normal]
    {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    (ρ : Representation (ZMod 2) G N) (s : G) (hs : s ^ 2 = 1)
    (hG : ∀ g : G, g ∈ H ∨ g * s ∈ H)
    (hfix : ∀ n : N, (∀ h : H, ρ h n = n) → n = 0)
    {f : ↥(Z1 (ρ.comp H.subtype))}
    (hf : w183_tauZ (H := H) ρ s hs f - f ∈ w183_B1H H ρ) :
    Submodule.Quotient.mk f ∈ LinearMap.range (w183_resBar (H := H) ρ) := by
  obtain ⟨b, hb⟩ := LinearMap.mem_range.mp (Submodule.mem_comap.mp hf)
  have hb_eq : w183_tauZ (H := H) ρ s hs f - f =
      ⟨coboundary (ρ.comp H.subtype) b, (B1_le_Z1 _) ⟨b, rfl⟩⟩ :=
    Subtype.ext hb.symm
  have hsb : ρ s b = b := w183_rho_s_b_eq (H := H) ρ s hs hfix hb_eq
  have hb_fun : ∀ h : H, ρ s (f.1 (w183_conjH s h)) = f.1 h + (ρ (h : G) b + b) := by
    intro h
    have hlin : w183_tauLin ρ s f.1 - f.1 = coboundary (ρ.comp H.subtype) b := by
      have h := congrArg Subtype.val hb_eq
      change w183_tauLin ρ s f.1 - f.1 = coboundary (ρ.comp H.subtype) b at h
      exact h
    have h' : ρ s (f.1 (w183_conjH s h)) - f.1 h = ρ (h : G) b - b := by
      have hh := congrFun hlin h
      change w183_tauLin ρ s f.1 h - f.1 h =
        coboundary (ρ.comp H.subtype) b h at hh
      change ρ s (f.1 (w183_conjH s h)) - f.1 h = ρ (h : G) b - b at hh
      exact hh
    have h'' : ρ s (f.1 (w183_conjH s h)) + f.1 h = ρ (h : G) b + b := by
      rw [w183_sub_eq_add, w183_sub_eq_add] at h'
      exact h'
    calc ρ s (f.1 (w183_conjH s h))
        = (ρ s (f.1 (w183_conjH s h)) + f.1 h) + f.1 h := by
            rw [add_assoc, w183_add_self, add_zero]
      _ = (ρ (h : G) b + b) + f.1 h := by rw [h'']
      _ = f.1 h + (ρ (h : G) b + b) := by abel
  have hF : w183_extendFun ρ s hG f.1 b ∈ Z1 ρ :=
    w183_extend_cocycle ρ hs hG f.2 hb_fun hsb
  refine ⟨Submodule.Quotient.mk ⟨w183_extendFun ρ s hG f.1 b, hF⟩, ?_⟩
  change Submodule.Quotient.mk (w183_resZ H ρ ⟨w183_extendFun ρ s hG f.1 b, hF⟩) =
    Submodule.Quotient.mk f
  congr 1
  apply Subtype.ext
  funext h
  change w183_extendFun ρ s hG f.1 b (h : G) = f.1 h
  rw [w183_extendFun_of_mem ρ s hG f.1 b h.2]

private lemma w183_range_resBar_eq_ker {G : Type} [Group G] {H : Subgroup G} [H.Normal]
    {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    (ρ : Representation (ZMod 2) G N) (s : G) (hs : s ^ 2 = 1)
    (hG : ∀ g : G, g ∈ H ∨ g * s ∈ H)
    (hfix : ∀ n : N, (∀ h : H, ρ h n = n) → n = 0) :
    LinearMap.ker ((w183_tauBar (H := H) ρ s hs) - 1) =
      LinearMap.range (w183_resBar (H := H) ρ) := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    revert hx
    refine Submodule.Quotient.induction_on
      (p := (B1 (ρ.comp H.subtype)).comap (Z1 (ρ.comp H.subtype)).subtype) x ?_
    intro f hx
    rw [LinearMap.sub_apply, Module.End.one_apply] at hx
    have hTf : w183_tauBar (H := H) ρ s hs (Submodule.Quotient.mk f) =
        Submodule.Quotient.mk f := sub_eq_zero.mp hx
    have hmem : w183_tauZ (H := H) ρ s hs f - f ∈ w183_B1H H ρ := by
      rw [← Submodule.Quotient.eq]
      exact hTf
    exact w183_mem_range_resBar ρ s hs hG hfix hmem
  · intro x hx
    rw [LinearMap.mem_range] at hx
    obtain ⟨y, hy⟩ := hx
    rw [LinearMap.mem_ker]
    rw [← hy]
    have hTR : w183_tauBar (H := H) ρ s hs (w183_resBar (H := H) ρ y) =
        w183_resBar (H := H) ρ y := by
      rw [← LinearMap.comp_apply, w183_resBar_tauBar (H := H) ρ s hs]
    rw [LinearMap.sub_apply, Module.End.one_apply, hTR, sub_self]

theorem s16nt_h1_index_two {G : Type} [Group G] [Finite G] {N : Type} [AddCommGroup N]
    [Module (ZMod 2) N] [Finite N] (ρ : Representation (ZMod 2) G N) (H : Subgroup G)
    [H.Normal] {s : G} (hs : s ^ 2 = 1) (hG : ∀ g : G, g ∈ H ∨ g * s ∈ H)
    (hfix : ∀ n : N, (∀ h : H, ρ h n = n) → n = 0) :
    Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1 (ρ.comp H.subtype)) ≤
      2 * Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1 ρ) := by
  haveI hfinZH : Finite ↥(Z1 (ρ.comp H.subtype)) := Subtype.finite
  haveI hfinZG : Finite ↥(Z1 ρ) := Subtype.finite
  haveI hH1H : Module.Finite (ZMod 2)
      (CFSG.Quasithin.JonesParshall.H1 (ρ.comp H.subtype)) :=
    Module.finite_iff_finite.mpr (Finite.of_surjective _
      (Submodule.Quotient.mk_surjective
        ((B1 (ρ.comp H.subtype)).comap (Z1 (ρ.comp H.subtype)).subtype)))
  haveI hH1G : Module.Finite (ZMod 2) (CFSG.Quasithin.JonesParshall.H1 ρ) :=
    Module.finite_iff_finite.mpr (Finite.of_surjective _
      (Submodule.Quotient.mk_surjective ((B1 ρ).comap (Z1 ρ).subtype)))
  set T : CFSG.Quasithin.JonesParshall.H1 (ρ.comp H.subtype) →ₗ[ZMod 2]
      CFSG.Quasithin.JonesParshall.H1 (ρ.comp H.subtype) :=
    w183_tauBar (H := H) ρ s hs with hT
  set R : CFSG.Quasithin.JonesParshall.H1 ρ →ₗ[ZMod 2]
      CFSG.Quasithin.JonesParshall.H1 (ρ.comp H.subtype) :=
    w183_resBar (H := H) ρ with hR
  have hsq : (T - 1).comp (T - 1) = 0 := by
    rw [hT]
    exact w183_tauBar_sub_one_comp_self (H := H) ρ s hs
  have hker : LinearMap.ker (T - 1) = LinearMap.range R := by
    rw [hT, hR]
    exact w183_range_resBar_eq_ker (H := H) ρ s hs hG hfix
  have hmono : LinearMap.range (T - 1) ≤ LinearMap.ker (T - 1) := by
    intro x hx
    rw [LinearMap.mem_range] at hx
    obtain ⟨y, hy⟩ := hx
    rw [LinearMap.mem_ker, ← hy]
    rw [← LinearMap.comp_apply, hsq, LinearMap.zero_apply]
  have hrn := LinearMap.finrank_range_add_finrank_ker (T - 1)
  have hle : Module.finrank (ZMod 2) (LinearMap.range (T - 1)) ≤
      Module.finrank (ZMod 2) (LinearMap.ker (T - 1)) := Submodule.finrank_mono hmono
  have hrange : Module.finrank (ZMod 2) (LinearMap.range R) ≤
      Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1 ρ) :=
    LinearMap.finrank_range_le R
  have hker' : Module.finrank (ZMod 2) (LinearMap.ker (T - 1)) =
      Module.finrank (ZMod 2) (LinearMap.range R) := by rw [hker]
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
