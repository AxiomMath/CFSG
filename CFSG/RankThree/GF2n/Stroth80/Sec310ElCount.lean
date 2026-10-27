module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.GroupTheory.Index
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem elation_count_card {G N : Type} [Group G] [Group N] (φ : G →* N) :
    Nat.card G = Nat.card φ.ker * Nat.card φ.range := by
  rw [← Subgroup.index_ker, Subgroup.card_mul_index]

theorem elation_dual_data {K : Type} [Field K] [Finite K] {U : Type} [AddCommGroup U]
    [Module K U] [Module.Finite K U] {b : U} (hb : b ≠ 0) {Γ : Type} [Group Γ] [Finite Γ]
    (θ : Γ →* (U ≃ₗ[K] U)) (hfix : ∀ g, θ g b = b)
    (hel : ∀ g u, ∃ c : K, θ g u = u + c • b)
    (hcard : Nat.card Γ = Nat.card θ.ker * Nat.card K ^ (Module.finrank K U - 1)) :
    ∃ Fd : Γ → Module.Dual K U, (∀ g u, θ g u = u + Fd g u • b) ∧
      (∀ g h, Fd (g * h) = Fd g + Fd h) ∧ Fd 1 = 0 ∧
      (∀ g, Fd g ∈ (Submodule.span K {b}).dualAnnihilator) ∧
      (∀ φ : Module.Dual K U, φ ∈ (Submodule.span K {b}).dualAnnihilator →
        ∃ g, Fd g = φ) := by
  choose F hF using hel
  have huniq : ∀ g u c, θ g u = u + c • b → c = F g u := fun g u c h =>
    smul_left_injective K hb (add_left_cancel (h.symm.trans (hF g u)))
  have hFb : ∀ g, F g b = 0 := fun g =>
    (huniq g b 0 (by rw [hfix g, zero_smul, add_zero])).symm
  have hadd : ∀ g u v, F g (u + v) = F g u + F g v := by
    intro g u v
    refine (huniq g (u + v) (F g u + F g v) ?_).symm
    rw [map_add, hF g u, hF g v, add_smul]
    abel
  have hsmul : ∀ g (r : K) u, F g (r • u) = r * F g u := by
    intro g r u
    refine (huniq g (r • u) (r * F g u) ?_).symm
    rw [map_smul, hF g u, smul_add, smul_smul]
  have hsmul' : ∀ g (r : K) u, F g (r • u) = (RingHom.id K) r • F g u := fun g r u => by
    rw [hsmul g r u, RingHom.id_apply, smul_eq_mul]
  obtain ⟨Fd, hFd⟩ : ∃ Fd : Γ → Module.Dual K U, ∀ g u, Fd g u = F g u :=
    ⟨fun g => { toFun := F g, map_add' := hadd g, map_smul' := hsmul' g }, fun _ _ => rfl⟩
  have hmulapp : ∀ g h u, θ (g * h) u = θ g (θ h u) := by
    intro g h u
    have h' := congrArg (fun e : U ≃ₗ[K] U => e u) (map_mul θ g h)
    exact h'
  have hmul : ∀ g h, Fd (g * h) = Fd g + Fd h := by
    intro g h
    refine LinearMap.ext fun u => ?_
    rw [LinearMap.add_apply, hFd, hFd, hFd]
    refine (huniq (g * h) u (F g u + F h u) ?_).symm
    rw [hmulapp, hF h u, map_add, map_smul, hfix g, hF g u, add_smul]
    abel
  have hθ1 : ∀ u, θ 1 u = u := by
    intro u
    have h := congrArg (fun e : U ≃ₗ[K] U => e u) (map_one θ)
    exact h
  have hFd1 : Fd 1 = 0 := by
    refine LinearMap.ext fun u => ?_
    rw [hFd, LinearMap.zero_apply]
    refine (huniq 1 u 0 ?_).symm
    rw [zero_smul, add_zero]
    exact hθ1 u
  have hFvan : ∀ g, ∀ x ∈ Submodule.span K {b}, Fd g x = 0 := by
    intro g x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, hFd, hFb, smul_zero]
  obtain ⟨W, hW⟩ : ∃ W : Submodule K (Module.Dual K U),
      W = (Submodule.span K {b}).dualAnnihilator := ⟨_, rfl⟩
  have hWmem : ∀ φ : Module.Dual K U, φ ∈ W ↔ ∀ x ∈ Submodule.span K {b}, φ x = 0 := by
    intro φ
    rw [hW, Submodule.mem_dualAnnihilator]
  have hFW : ∀ g, Fd g ∈ W := fun g => (hWmem (Fd g)).mpr (hFvan g)
  have hWcard : Nat.card W = Nat.card K ^ (Module.finrank K U - 1) := by
    have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq (Submodule.span K {b})
    rw [finrank_span_singleton (K := K) hb] at h1
    rw [hW, Module.natCard_eq_pow_finrank (K := K)]
    congr 1
    omega
  haveI : Finite W := Module.finite_of_finite K
  haveI : Finite (Multiplicative W) := inferInstanceAs (Finite W)
  have hzΦ : (⟨Fd 1, hFW 1⟩ : W) = 0 := Subtype.ext hFd1
  have honeΦ : Multiplicative.ofAdd (⟨Fd 1, hFW 1⟩ : W) = 1 := congrArg Multiplicative.ofAdd hzΦ
  have hmulΦ : ∀ g h, Multiplicative.ofAdd (⟨Fd (g * h), hFW (g * h)⟩ : W) =
      Multiplicative.ofAdd (⟨Fd g, hFW g⟩ : W) * Multiplicative.ofAdd (⟨Fd h, hFW h⟩ : W) := by
    intro g h
    have hz : (⟨Fd (g * h), hFW (g * h)⟩ : W) = (⟨Fd g, hFW g⟩ : W) + ⟨Fd h, hFW h⟩ :=
      Subtype.ext (hmul g h)
    exact congrArg Multiplicative.ofAdd hz
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Γ →* Multiplicative W,
      ∀ g, Φ g = Multiplicative.ofAdd (⟨Fd g, hFW g⟩ : W) :=
    ⟨MonoidHom.mk (OneHom.mk (fun g => Multiplicative.ofAdd (⟨Fd g, hFW g⟩ : W)) honeΦ)
      hmulΦ, fun g => rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : Subgroup (Multiplicative W),
      R = MonoidHom.range (G := Γ) (N := Multiplicative W) Φ := ⟨_, rfl⟩
  have hone1 : ∀ g, Multiplicative.ofAdd (⟨Fd g, hFW g⟩ : W) = 1 ↔ Fd g = 0 := by
    intro g
    constructor
    · intro h
      have h' := ofAdd_eq_one.mp h
      exact congrArg Subtype.val h'
    · intro h
      exact ofAdd_eq_one.mpr (Subtype.ext h)
  have hker : Φ.ker = θ.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hΦ, hone1 g]
    constructor
    · intro h0
      refine LinearEquiv.ext fun u => ?_
      have h1 : F g u = 0 := by
        have h2 := LinearMap.congr_fun h0 u
        rw [hFd, LinearMap.zero_apply] at h2
        exact h2
      have h3 : θ g u = u := by
        rw [hF g u, h1, zero_smul, add_zero]
      exact h3
    · intro h1
      refine LinearMap.ext fun u => ?_
      have h4 : θ g u = u := by
        rw [h1]
        try rfl
      rw [hFd, LinearMap.zero_apply]
      refine (huniq g u 0 ?_).symm
      rw [h4, zero_smul, add_zero]
  have hΦcard : Nat.card R = Nat.card W := by
    have h1 := elation_count_card (G := Γ) (N := Multiplicative W) Φ
    rw [hker, ← hR] at h1
    have h2 : Nat.card θ.ker * Nat.card R = Nat.card θ.ker * Nat.card W := by
      rw [← h1, hcard, hWcard]
    have hpos : 0 < Nat.card θ.ker := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  have hΦrange : R = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    exact hΦcard
  have hΦsurj : ∀ w : W, ∃ g, Fd g = (w : Module.Dual K U) := by
    intro w
    have hmem : Multiplicative.ofAdd w ∈ R := by
      rw [hΦrange]
      exact Subgroup.mem_top _
    rw [hR] at hmem
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hmem
    rw [hΦ] at hg
    exact ⟨g, congrArg Subtype.val (Multiplicative.ofAdd.injective hg)⟩
  refine ⟨Fd, fun g u => ?_, hmul, hFd1, fun g => ?_, fun φ hφ => ?_⟩
  · rw [hFd]
    exact hF g u
  · rw [← hW]
    exact hFW g
  · obtain ⟨g, hg⟩ := hΦsurj ⟨φ, by rw [hW]; exact hφ⟩
    exact ⟨g, hg⟩

theorem elation_count {K : Type} [Field K] [Finite K] {U : Type} [AddCommGroup U] [Module K U]
    [Module.Finite K U] {b : U} (hb : b ≠ 0) {Γ : Type} [Group Γ] [Finite Γ]
    (θ : Γ →* (U ≃ₗ[K] U)) (hfix : ∀ g, θ g b = b)
    (hel : ∀ g u, ∃ c : K, θ g u = u + c • b)
    (hcard : Nat.card Γ = Nat.card θ.ker * Nat.card K ^ (Module.finrank K U - 1))
    (Y : Submodule K U) (hbY : b ∈ Y) (S : Subgroup Γ)
    (hS : ∀ g, g ∈ S ↔ ∀ y ∈ Y, θ g y = y) :
    Nat.card Γ = Nat.card S * Nat.card K ^ (Module.finrank K Y - 1) := by
  obtain ⟨Fd, hFdrep, hmul, hFd1, hFW0, hsurjW⟩ := elation_dual_data hb θ hfix hel hcard
  have hFy : ∀ g u, Fd g u = 0 ↔ θ g u = u := by
    intro g u
    constructor
    · intro h0
      rw [hFdrep g u, h0, zero_smul, add_zero]
    · intro h1
      have h2 : u + Fd g u • b = u + (0 : K) • b := by
        rw [zero_smul, add_zero, ← hFdrep g u, h1]
      exact smul_left_injective K hb (add_left_cancel h2)
  have hDR : ∀ g, Y.dualRestrict (Fd g) = 0 ↔ ∀ y ∈ Y, θ g y = y := by
    intro g
    constructor
    · intro h y hy
      have h2 := LinearMap.congr_fun h ⟨y, hy⟩
      rw [LinearMap.zero_apply, Submodule.dualRestrict_apply] at h2
      exact (hFy g y).mp h2
    · intro h
      refine LinearMap.ext fun w => ?_
      rw [LinearMap.zero_apply, Submodule.dualRestrict_apply]
      exact (hFy g (w : U)).mpr (h (w : U) w.2)
  have hY0 : (⟨b, hbY⟩ : Y) ≠ 0 := fun h => hb (congrArg Subtype.val h)
  obtain ⟨A, hA⟩ : ∃ A : Submodule K (Module.Dual K Y),
      A = (Submodule.span K {(⟨b, hbY⟩ : Y)}).dualAnnihilator := ⟨_, rfl⟩
  have hAmem : ∀ φ : Module.Dual K Y,
      φ ∈ A ↔ ∀ w ∈ Submodule.span K {(⟨b, hbY⟩ : Y)}, φ w = 0 := by
    intro φ
    rw [hA, Submodule.mem_dualAnnihilator]
  have hAcard : Nat.card A = Nat.card K ^ (Module.finrank K Y - 1) := by
    have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq
      (Submodule.span K {(⟨b, hbY⟩ : Y)})
    rw [finrank_span_singleton (K := K) hY0] at h1
    rw [hA, Module.natCard_eq_pow_finrank (K := K)]
    congr 1
    omega
  have hdr : ∀ g, Y.dualRestrict (Fd g) ∈ A := by
    intro g
    rw [hAmem]
    intro w hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    have hmemb : ((a • (⟨b, hbY⟩ : Y) : Y) : U) ∈ Submodule.span K {b} :=
      Submodule.mem_span_singleton.mpr ⟨a, rfl⟩
    have hF0 := hFW0 g
    rw [Submodule.mem_dualAnnihilator] at hF0
    rw [Submodule.dualRestrict_apply]
    exact hF0 _ hmemb
  have hzΨ : (⟨Y.dualRestrict (Fd 1), hdr 1⟩ : A) = 0 := by
    apply Subtype.ext
    show Y.dualRestrict (Fd 1) = 0
    rw [hFd1, map_zero]
  have honeΨ : Multiplicative.ofAdd (⟨Y.dualRestrict (Fd 1), hdr 1⟩ : A) = 1 :=
    congrArg Multiplicative.ofAdd hzΨ
  have hmulΨ : ∀ g h, Multiplicative.ofAdd (⟨Y.dualRestrict (Fd (g * h)), hdr (g * h)⟩ : A) =
      Multiplicative.ofAdd (⟨Y.dualRestrict (Fd g), hdr g⟩ : A) *
        Multiplicative.ofAdd (⟨Y.dualRestrict (Fd h), hdr h⟩ : A) := by
    intro g h
    have hz : (⟨Y.dualRestrict (Fd (g * h)), hdr (g * h)⟩ : A) =
        (⟨Y.dualRestrict (Fd g), hdr g⟩ : A) + ⟨Y.dualRestrict (Fd h), hdr h⟩ := by
      apply Subtype.ext
      show Y.dualRestrict (Fd (g * h)) = Y.dualRestrict (Fd g) + Y.dualRestrict (Fd h)
      rw [hmul, map_add]
    exact congrArg Multiplicative.ofAdd hz
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Γ →* Multiplicative A, ∀ g,
      Ψ g = Multiplicative.ofAdd (⟨Y.dualRestrict (Fd g), hdr g⟩ : A) :=
    ⟨MonoidHom.mk (OneHom.mk
      (fun g => Multiplicative.ofAdd (⟨Y.dualRestrict (Fd g), hdr g⟩ : A)) honeΨ) hmulΨ,
      fun g => rfl⟩
  have hone2 : ∀ g, Ψ g = 1 ↔ Y.dualRestrict (Fd g) = 0 := by
    intro g
    rw [hΨ g]
    constructor
    · intro h
      have h' := ofAdd_eq_one.mp h
      exact congrArg Subtype.val h'
    · intro h
      exact ofAdd_eq_one.mpr (Subtype.ext h)
  have hkerΨ : Ψ.ker = S := by
    ext g
    rw [MonoidHom.mem_ker, hone2 g, hDR g, hS g]
  have hΨsurj : ∀ (f : Module.Dual K Y) (hf : f ∈ A),
      ∃ g, Ψ g = Multiplicative.ofAdd (⟨f, hf⟩ : A) := by
    intro f hf
    obtain ⟨Ft, hFt⟩ := (Subspace.dualRestrict_surjective (W := Y)) f
    have hFtW : Ft ∈ (Submodule.span K {b}).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      have h0 : Ft b = 0 := by
        have h1 := (hAmem f).mp hf ⟨b, hbY⟩ (Submodule.mem_span_singleton_self _)
        rw [← hFt, Submodule.dualRestrict_apply] at h1
        exact h1
      rw [map_smul, h0, smul_zero]
    obtain ⟨g, hg⟩ := hsurjW Ft hFtW
    refine ⟨g, ?_⟩
    rw [hΨ g]
    refine congrArg Multiplicative.ofAdd (Subtype.ext ?_)
    show Y.dualRestrict (Fd g) = f
    rw [hg]
    exact hFt
  have hsurjΨ : Function.Surjective Ψ := by
    intro x
    obtain ⟨g, hg⟩ := hΨsurj (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2
    exact ⟨g, hg⟩
  obtain ⟨RΨ, hRΨ⟩ : ∃ T : Subgroup (Multiplicative A),
      T = MonoidHom.range (G := Γ) (N := Multiplicative A) Ψ := ⟨_, rfl⟩
  have hΨrange : RΨ = ⊤ := by
    rw [hRΨ]
    exact (MonoidHom.range_eq_top (G := Γ) (N := Multiplicative A) (f := Ψ)).mpr hsurjΨ
  have hfinal := elation_count_card (G := Γ) (N := Multiplicative A) Ψ
  rw [hkerΨ, ← hRΨ, hΨrange, Subgroup.card_top] at hfinal
  rw [hfinal]
  exact congrArg (fun n => Nat.card S * n) hAcard

theorem elation_exists {K : Type} [Field K] [Finite K] {U : Type} [AddCommGroup U] [Module K U]
    [Module.Finite K U] {b : U} (hb : b ≠ 0) {Γ : Type} [Group Γ] [Finite Γ]
    (θ : Γ →* (U ≃ₗ[K] U)) (hfix : ∀ g, θ g b = b)
    (hel : ∀ g u, ∃ c : K, θ g u = u + c • b)
    (hcard : Nat.card Γ = Nat.card θ.ker * Nat.card K ^ (Module.finrank K U - 1))
    (Y : Submodule K U) (hbY : b ∈ Y) (f : Module.Dual K Y) (hf : f ⟨b, hbY⟩ = 0) :
    ∃ g : Γ, ∀ y : Y, (θ g (y : U) : U) = (y : U) + f y • b := by
  obtain ⟨Fd, hFdrep, -, -, -, hsurjW⟩ := elation_dual_data hb θ hfix hel hcard
  obtain ⟨φ, hφ⟩ := (Subspace.dualRestrict_surjective (W := Y)) f
  have hφW : φ ∈ (Submodule.span K {b}).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have h0 : φ b = 0 := by
      have h1 := hf
      rw [← hφ, Submodule.dualRestrict_apply] at h1
      exact h1
    rw [map_smul, h0, smul_zero]
  obtain ⟨g, hg⟩ := hsurjW φ hφW
  refine ⟨g, fun y => ?_⟩
  have hy : φ (y : U) = f y := by
    rw [← hφ, Submodule.dualRestrict_apply]
  rw [hFdrep g (y : U), hg, hy]

end CFSG.RankThree.GF2n.Stroth80
