module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829S9Mat

public section

namespace CFSG.Quasithin.H13.L829N

open Matrix
open scoped MatrixGroups

theorem s9c_conj_P1 {R : Type*} [Ring R] (u v x : R) (huv : u * v = 1) (hvu : v * u = 1) :
    s9P1 (u * x * v) = u * s9P1 x * v := by
  unfold s9P1
  have h3 : u * x * v * (u * x * v) = u * (x * x) * v := by
    calc u * x * v * (u * x * v) = u * x * (v * u) * x * v := by noncomm_ring
      _ = u * (x * x) * v := by rw [hvu]; noncomm_ring
  have h4 : u * x * v * (u * x * v) * (u * x * v) = u * (x * x * x) * v := by
    calc u * x * v * (u * x * v) * (u * x * v) = u * (x * x) * v * (u * x * v) := by rw [h3]
      _ = u * (x * x) * (v * u) * x * v := by noncomm_ring
      _ = u * (x * x * x) * v := by rw [hvu]; noncomm_ring
  rw [h4]
  calc u * (x * x * x) * v + u * x * v + 1 = u * (x * x * x) * v + u * x * v + u * v := by
        rw [huv]
    _ = u * (x * x * x + x + 1) * v := by noncomm_ring

theorem s9c_conj_P2 {R : Type*} [Ring R] (u v x : R) (huv : u * v = 1) (hvu : v * u = 1) :
    s9P2 (u * x * v) = u * s9P2 x * v := by
  unfold s9P2
  have h3 : u * x * v * (u * x * v) = u * (x * x) * v := by
    calc u * x * v * (u * x * v) = u * x * (v * u) * x * v := by noncomm_ring
      _ = u * (x * x) * v := by rw [hvu]; noncomm_ring
  have h4 : u * x * v * (u * x * v) * (u * x * v) = u * (x * x * x) * v := by
    calc u * x * v * (u * x * v) * (u * x * v) = u * (x * x) * v * (u * x * v) := by rw [h3]
      _ = u * (x * x) * (v * u) * x * v := by noncomm_ring
      _ = u * (x * x * x) * v := by rw [hvu]; noncomm_ring
  rw [h4, h3]
  calc u * (x * x * x) * v + u * (x * x) * v + 1
        = u * (x * x * x) * v + u * (x * x) * v + u * v := by rw [huv]
    _ = u * (x * x * x + x * x + 1) * v := by noncomm_ring

theorem s9c_map_P2 {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (x : R) :
    s9P2 (f x) = f (s9P2 x) := by
  simp [s9P2, map_add, map_mul, map_one]

theorem s9c_SL_mul_inv (A : SL(3, ZMod 2)) :
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * ((A⁻¹ : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem s9c_SL_inv_mul (A : SL(3, ZMod 2)) :
    ((A⁻¹ : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem s9c_ker_of_conj {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (X u v : Module.End (ZMod 2) W) (huv : u * v = 1) (hvu : v * u = 1)
    (h : LinearMap.ker (u * X * v) = ⊥) : LinearMap.ker X = ⊥ := by
  rw [LinearMap.ker_eq_bot'] at h ⊢
  intro m hm
  have hvum : v (u m) = m := by
    have := congrArg (fun f : Module.End (ZMod 2) W => f m) hvu
    simpa [Module.End.mul_apply] using this
  have h1 : (u * X * v) (u m) = 0 := by
    rw [Module.End.mul_apply, Module.End.mul_apply, hvum, hm, map_zero]
  have h2 : u m = 0 := h (u m) h1
  calc m = v (u m) := hvum.symm
    _ = 0 := by rw [h2, map_zero]

theorem s9c_conj_hom {G : Type} [Group G] (K₀ : Subgroup G) (τ : G)
    (hτK : ∀ k ∈ K₀, τ * k * τ⁻¹ ∈ K₀) :
    ∃ c : K₀ →* K₀, ∀ x : K₀, (c x : G) = τ * x * τ⁻¹ :=
  ⟨MonoidHom.mk' (fun x : K₀ => (⟨τ * x * τ⁻¹, hτK x x.2⟩ : K₀)) (fun a b => by
    apply Subtype.ext
    simp [mul_assoc]), fun _ => rfl⟩

theorem s9c_normalizes_ker {G : Type} [Group G] [Finite G] (K₀ : Subgroup G)
    {Ks : Type} [Group Ks] (σ : K₀ →* Ks) (hσ : Function.Surjective σ)
    (hnt : ∃ a b : Ks, a * b ≠ b * a)
    (hker : ∀ M : Subgroup K₀, M.Normal → M ≠ ⊤ → M ≤ σ.ker)
    (c : K₀ →* K₀) (hcinj : Function.Injective c) :
    ∀ m ∈ σ.ker, c m ∈ σ.ker := by
  have hcsurj : Function.Surjective c := Finite.surjective_of_injective hcinj
  have hne : σ.ker ≠ ⊤ := by
    intro htop
    obtain ⟨a, b, hab⟩ := hnt
    have hall : ∀ k : Ks, k = 1 := by
      intro k
      obtain ⟨x, rfl⟩ := hσ k
      have hx : x ∈ σ.ker := by
        rw [htop]
        exact Subgroup.mem_top x
      exact MonoidHom.mem_ker.mp hx
    exact hab (by rw [hall a, hall b])
  have hPn : (Subgroup.map c σ.ker).Normal := Subgroup.Normal.map inferInstance c hcsurj
  have hPne : Subgroup.map c σ.ker ≠ ⊤ := by
    intro hP
    apply hne
    have h1 : Nat.card (Subgroup.map c σ.ker) = Nat.card σ.ker :=
      Subgroup.card_map_of_injective hcinj
    have h2 : Nat.card (Subgroup.map c σ.ker) = Nat.card K₀ := by
      rw [hP, Subgroup.card_top]
    exact (Subgroup.card_eq_iff_eq_top σ.ker).mp (h1.symm.trans h2)
  have hPle := hker _ hPn hPne
  intro m hm
  exact hPle (Subgroup.mem_map.mpr ⟨m, hm, rfl⟩)

theorem s9c_mulAut_of_hom {K S : Type} [Group K] [Group S] [Finite S] (θ : K →* S)
    (hθ : Function.Surjective θ) (c : K →* K) (hc : Function.Surjective c)
    (hker : ∀ x : K, θ x = 1 → θ (c x) = 1) :
    ∃ α : MulAut S, ∀ x : K, α (θ x) = θ (c x) := by
  have hle : θ.ker ≤ (θ.comp c).ker := fun x hx => by
    rw [MonoidHom.mem_ker] at hx ⊢
    exact hker x hx
  let q : K ⧸ θ.ker →* S := QuotientGroup.lift θ.ker (θ.comp c) hle
  let e : K ⧸ θ.ker ≃* S := QuotientGroup.quotientKerEquivOfSurjective θ hθ
  let β : S →* S := q.comp e.symm.toMonoidHom
  have hβ : ∀ x : K, β (θ x) = θ (c x) := by
    intro x
    have h1 : e.symm (θ x) = (x : K ⧸ θ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    have h2 : q (x : K ⧸ θ.ker) = θ (c x) := QuotientGroup.lift_mk θ.ker hle x
    show q (e.symm (θ x)) = θ (c x)
    rw [h1, h2]
  have hsurj : Function.Surjective β := by
    intro s
    obtain ⟨x, rfl⟩ := hθ s
    obtain ⟨x', hx'⟩ := hc x
    exact ⟨θ x', by rw [hβ, hx']⟩
  have hbij : Function.Bijective β := ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  exact ⟨MulEquiv.ofBijective β hbij, fun x => hβ x⟩

theorem s9c_range_hker {G H Ks : Type} [Group G] [Group H] [Group Ks]
    (σ : G →* Ks) (hσ : Function.Surjective σ) (ψ : G →* H) (hψ : Function.Injective ψ)
    (hker : ∀ M : Subgroup G, M.Normal → M ≠ ⊤ → M ≤ σ.ker) :
    Function.Surjective (σ.comp (MonoidHom.ofInjective hψ).symm.toMonoidHom) ∧
      ∀ M : Subgroup ψ.range, M.Normal → M ≠ ⊤ →
        M ≤ (σ.comp (MonoidHom.ofInjective hψ).symm.toMonoidHom).ker := by
  refine ⟨?_, ?_⟩
  · intro k
    obtain ⟨x, rfl⟩ := hσ k
    refine ⟨MonoidHom.ofInjective hψ x, ?_⟩
    simp
  · intro M hMn hMtop
    have hPn : (M.map (MonoidHom.ofInjective hψ).symm.toMonoidHom).Normal :=
      Subgroup.Normal.map hMn _ (MulEquiv.surjective _)
    have hPtop : M.map (MonoidHom.ofInjective hψ).symm.toMonoidHom ≠ ⊤ := by
      intro hP
      apply hMtop
      rw [Subgroup.eq_top_iff']
      intro x
      have hx : (MonoidHom.ofInjective hψ).symm x ∈
          M.map (MonoidHom.ofInjective hψ).symm.toMonoidHom := by
        rw [hP]
        exact Subgroup.mem_top _
      obtain ⟨m, hm, hme⟩ := Subgroup.mem_map.mp hx
      have hmx : m = x := (MulEquiv.injective _) hme
      rw [← hmx]
      exact hm
    have hle := hker _ hPn hPtop
    intro m hm
    have hm' : (MonoidHom.ofInjective hψ).symm m ∈
        M.map (MonoidHom.ofInjective hψ).symm.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨m, hm, rfl⟩
    exact MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp (hle hm'))

theorem s9c_closure_transfer {G H : Type} [Group G] [Group H] {Gg : Subgroup G}
    (φ : Gg →* H) {K₀ : Subgroup G} (hK₀G : K₀ ≤ Gg) {v : G} (hvG : v ∈ Gg)
    {C : Subgroup H}
    (hC : ∀ k : K₀, φ (Subgroup.inclusion hK₀G k) * φ ⟨v, hvG⟩ *
      (φ (Subgroup.inclusion hK₀G k))⁻¹ ∈ C)
    (hK₀v : K₀ ≤ Subgroup.closure {x | ∃ k ∈ K₀, x = k * v * k⁻¹}) :
    ∀ k : K₀, φ (Subgroup.inclusion hK₀G k) ∈ C := by
  let Q : Subgroup G := (C.comap φ).map Gg.subtype
  have hQ : ∀ w : G, w ∈ Q ↔ ∃ hw : w ∈ Gg, φ ⟨w, hw⟩ ∈ C := by
    intro w
    constructor
    · intro hw
      obtain ⟨y, hy, hyw⟩ := Subgroup.mem_map.mp hw
      subst hyw
      exact ⟨y.2, hy⟩
    · rintro ⟨hw, hmem⟩
      exact Subgroup.mem_map.mpr ⟨⟨w, hw⟩, hmem, rfl⟩
  have hS : {x | ∃ k ∈ K₀, x = k * v * k⁻¹} ⊆ (Q : Set G) := by
    rintro x ⟨k, hk, rfl⟩
    rw [SetLike.mem_coe, hQ]
    have hkG : k ∈ Gg := hK₀G hk
    have hxG : k * v * k⁻¹ ∈ Gg := Gg.mul_mem (Gg.mul_mem hkG hvG) (Gg.inv_mem hkG)
    refine ⟨hxG, ?_⟩
    have hk' := hC ⟨k, hk⟩
    have heq : (⟨k * v * k⁻¹, hxG⟩ : Gg) =
        Subgroup.inclusion hK₀G ⟨k, hk⟩ * ⟨v, hvG⟩ * (Subgroup.inclusion hK₀G ⟨k, hk⟩)⁻¹ :=
      Subtype.ext rfl
    rw [heq, map_mul, map_mul, map_inv]
    exact hk'
  have hcl : Subgroup.closure {x | ∃ k ∈ K₀, x = k * v * k⁻¹} ≤ Q :=
    Subgroup.closure_le Q |>.mpr hS
  intro k
  obtain ⟨_, hmem⟩ := (hQ _).mp (hcl (hK₀v k.2))
  exact hmem

theorem s9c_alg_graph {G : Type} [Group G] [Finite G] (K₀ : Subgroup G) (τ : G)
    {Ks : Type} [Group Ks] (σ : K₀ →* Ks) (hσ : Function.Surjective σ)
    (hnt : ∃ a b : Ks, a * b ≠ b * a)
    (hker : ∀ M : Subgroup K₀, M.Normal → M ≠ ⊤ → M ≤ σ.ker)
    (c : K₀ →* K₀) (hc : ∀ x : K₀, (c x : G) = τ * x * τ⁻¹)
    (θ : K₀ →* SL(3, ZMod 2)) (hθ : Function.Surjective θ) (hθker : θ.ker = σ.ker)
    (hout : ∀ y : K₀, ∃ x : K₀, σ (c x) ≠ σ (y * x * y⁻¹)) :
    ∃ g : K₀, ((θ g : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = s9M1 ∧
      s9P2 ((θ (c g) : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0 := by
  have hcinj : Function.Injective c := by
    intro x y hxy
    apply Subtype.ext
    have h1 : (c x : G) = (c y : G) := congrArg Subtype.val hxy
    rw [hc, hc] at h1
    exact mul_left_cancel (mul_right_cancel h1)
  have hcsurj : Function.Surjective c := Finite.surjective_of_injective hcinj
  have hθc : ∀ x : K₀, θ x = 1 → θ (c x) = 1 := by
    intro x hx
    have hxσ : x ∈ σ.ker := by
      rw [← hθker]
      exact MonoidHom.mem_ker.mpr hx
    have hcσ := s9c_normalizes_ker K₀ σ hσ hnt hker c hcinj x hxσ
    rw [← hθker] at hcσ
    exact MonoidHom.mem_ker.mp hcσ
  obtain ⟨α, hα⟩ := s9c_mulAut_of_hom θ hθ c hcsurj hθc
  have hθσ : ∀ a b : K₀, θ a = θ b → σ a = σ b := by
    intro a b hab
    have hmem : a⁻¹ * b ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
    rw [hθker, MonoidHom.mem_ker, map_mul, map_inv] at hmem
    exact inv_mul_eq_one.mp hmem
  let M1 : SL(3, ZMod 2) := ⟨s9M1, s9M1_det⟩
  have hM1 : ((M1 : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = s9M1 := rfl
  rcases s9_aut_form α with ⟨A, hA⟩ | ⟨A, hA⟩
  ·
    exfalso
    obtain ⟨y, hy⟩ := hθ A
    obtain ⟨x, hx⟩ := hout y
    apply hx
    apply hθσ
    have h1 : θ (c x) = α (θ x) := (hα x).symm
    rw [h1, map_mul, map_mul, map_inv, hy]
    apply Subtype.ext
    rw [hA (θ x), Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ·
    obtain ⟨g, hg⟩ := hθ M1
    refine ⟨g, ?_, ?_⟩
    · rw [hg]
    · have h1 : θ (c g) = α (θ g) := (hα g).symm
      rw [h1, hg, hA M1, hM1, s9c_conj_P2 _ _ _ (s9c_SL_mul_inv A) (s9c_SL_inv_mul A),
        s9_P2_of_P1 s9M1 s9M1_det s9P1_M1]
      simp

end CFSG.Quasithin.H13.L829N
