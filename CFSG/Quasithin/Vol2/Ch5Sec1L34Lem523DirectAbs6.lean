module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectAbs5
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectAbs2
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectAbs3

public section

namespace CFSG.Quasithin.H13.Abs523

variable {V : Type} [CommGroup V] [Finite V]

theorem card_le_perm {𝒦V : Subgroup (MulAut V)} [IsSimpleGroup ↥𝒦V] {Y : Subgroup V}
    (hY : ∀ k ∈ 𝒦V, ∀ y ∈ Y, k y ∈ Y) (hnt : ∃ k ∈ 𝒦V, ∃ y ∈ Y, k y ≠ y) :
    Nat.card ↥𝒦V ≤ Nat.card (Equiv.Perm ↥Y) := by
  let ρ : ↥𝒦V →* Equiv.Perm ↥Y :=
    { toFun := fun g =>
        { toFun := fun y => ⟨(g : MulAut V) y, hY g g.2 y y.2⟩
          invFun := fun y => ⟨((g⁻¹ : ↥𝒦V) : MulAut V) y, hY _ (inv_mem g.2) y y.2⟩
          left_inv := fun y => by
            apply Subtype.ext
            simp
          right_inv := fun y => by
            apply Subtype.ext
            simp }
      map_one' := by
        ext y
        simp
      map_mul' := by
        intro g h
        ext y
        simp [MulAut.mul_apply] }
  have hker : ρ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨k₀, hk₀, y₀, hy₀, hne⟩ := hnt
      have hmem : (⟨k₀, hk₀⟩ : ↥𝒦V) ∈ ρ.ker := by
        rw [h]
        exact Subgroup.mem_top _
      have hfix : ρ ⟨k₀, hk₀⟩ = 1 := MonoidHom.mem_ker.mp hmem
      have h3 := congrArg (fun σ : Equiv.Perm ↥Y => (σ ⟨y₀, hy₀⟩ : ↥Y).1) hfix
      simp only [Equiv.Perm.one_apply] at h3
      exact hne h3
  exact Nat.card_le_card_of_injective ρ ((MonoidHom.ker_eq_bot_iff ρ).mp hker)

theorem five_le_card_of_nontriv {𝒦V : Subgroup (MulAut V)} [IsSimpleGroup ↥𝒦V]
    (hcard : 25 ≤ Nat.card ↥𝒦V) {Y : Subgroup V} (hY : ∀ k ∈ 𝒦V, ∀ y ∈ Y, k y ∈ Y)
    (hnt : ∃ k ∈ 𝒦V, ∃ y ∈ Y, k y ≠ y) : 5 ≤ Nat.card ↥Y := by
  by_contra h
  push Not at h
  have h1 := card_le_perm hY hnt
  rw [Nat.card_perm] at h1
  have h2 : (Nat.card ↥Y).factorial ≤ (4 : ℕ).factorial := Nat.factorial_le (by omega)
  have h3 : (4 : ℕ).factorial = 24 := by decide
  omega

theorem five_le_cmSub (hH47 : CFSG.ASVolI.H_4_7) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK4 : Nat.card K = 4) {𝒦V : Subgroup (MulAut V)} {vV : MulAut V}
    (hvv : vV * vV = 1) (hvN : vV ∈ Subgroup.normalizer (𝒦V : Set (MulAut V)))
    (hV2 : ∀ x : V, x ^ 2 = 1) [IsSimpleGroup ↥𝒦V] (hab : ¬ IsMulCommutative ↥𝒦V)
    (hiso : Nonempty (↥𝒦V ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K))
    (hcard : 25 ≤ Nat.card ↥𝒦V)
    (hirr : ∀ W : Subgroup V, (∀ k ∈ 𝒦V, ∀ w ∈ W, k w ∈ W) → (∀ w ∈ W, vV w ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (hVne : (⊤ : Subgroup V) ≠ ⊥)
    (hnt : ∃ k ∈ 𝒦V, k ≠ 1) (hvK : ∃ k ∈ 𝒦V, vV * k * vV⁻¹ ≠ k) :
    5 ≤ Nat.card ↥(cmSub vV) := by
  have hvne : vV ≠ 1 := by
    rintro rfl
    obtain ⟨k, hk, hk'⟩ := hvK
    apply hk'
    simp
  have hfix := fixK_eq_bot hvN hirr hnt
  obtain ⟨Y, hYmin⟩ := exists_kmin 𝒦V hVne
  unfold IsKMin at hYmin
  obtain ⟨hYne, hYinv, hYmin'⟩ := hYmin
  have hYnt : ∃ k ∈ 𝒦V, ∃ y ∈ Y, k y ≠ y := by
    by_contra h
    push Not at h
    apply hYne
    rw [eq_bot_iff]
    intro y hy
    have : y ∈ fixK 𝒦V := fun k hk => h k hk y hy
    rw [hfix] at this
    exact this
  have hconj : ∀ k ∈ 𝒦V, vV⁻¹ * k * vV ∈ 𝒦V := fun k hk => conj_mem_of_normalizer hvN k hk
  by_cases hA : ∀ y ∈ Y, vV y ∈ Y
  ·
    have hYtop : Y = ⊤ := by
      rcases hirr Y hYinv hA with h | h
      · exact absurd h hYne
      · exact h
    have hirrK : ∀ U : Subgroup V, (∀ k ∈ 𝒦V, ∀ u ∈ U, k u ∈ U) → U ≠ ⊥ → U = ⊤ := by
      intro U hU hU0
      have hUY := hYmin' U (by rw [hYtop]; exact le_top) hU0 hU
      rw [hUY, hYtop]
    have hrk := rk_ge_three_of_irred hH47 K hK4 hvv hvN hV2 hab hiso hirrK hVne hvne
    have := card_cmSub_of_rk (t := vV) hvv hrk
    omega
  ·
    push Not at hA
    obtain ⟨y₁, hy₁, hvy₁⟩ := hA
    let Yv : Subgroup V := Y.map (vV : V →* V)
    have hmemYv : ∀ w, w ∈ Yv ↔ ∃ y ∈ Y, vV y = w := fun w => by
      simp [Yv, Subgroup.mem_map]
    have hYv_k : ∀ k ∈ 𝒦V, ∀ w ∈ Yv, k w ∈ Yv := by
      intro k hk w hw
      obtain ⟨y, hy, rfl⟩ := (hmemYv w).mp hw
      refine (hmemYv _).mpr ⟨(vV⁻¹ * k * vV) y, hYinv _ (hconj k hk) y hy, ?_⟩
      simp [MulAut.mul_apply]
    have hW_inv : ∀ k ∈ 𝒦V, ∀ w ∈ Y ⊓ Yv, k w ∈ Y ⊓ Yv := by
      intro k hk w hw
      exact ⟨hYinv k hk w hw.1, hYv_k k hk w hw.2⟩
    have hvv' : ∀ x, vV (vV x) = x := fun x => by
      have := congrArg (fun F : MulAut V => F x) hvv
      simpa [MulAut.mul_apply] using this
    have hW_v : ∀ w ∈ Y ⊓ Yv, vV w ∈ Y ⊓ Yv := by
      intro w hw
      obtain ⟨y, hy, rfl⟩ := (hmemYv w).mp hw.2
      refine ⟨?_, (hmemYv _).mpr ⟨vV y, hw.1, rfl⟩⟩
      rw [hvv']
      exact hy
    have hW : Y ⊓ Yv = ⊥ := by
      rcases hirr (Y ⊓ Yv) hW_inv hW_v with h | h
      · exact h
      · exfalso
        have hmem : vV y₁ ∈ Y ⊓ Yv := by
          rw [h]
          exact Subgroup.mem_top _
        exact hvy₁ hmem.1
    let fH : ↥Y →* V :=
      { toFun := fun y => vV (y : V) * (y : V)⁻¹
        map_one' := by simp
        map_mul' := fun a b => by
          simp only [Subgroup.coe_mul, map_mul, mul_inv]
          ac_rfl }
    have hker : fH.ker = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have h1 : vV (y : V) * (y : V)⁻¹ = 1 := MonoidHom.mem_ker.mp hy
      have h2 : vV (y : V) = y := mul_inv_eq_one.mp h1
      have hyYv : (y : V) ∈ Yv := (hmemYv _).mpr ⟨(y : V), y.2, h2⟩
      have hy0 : (y : V) ∈ Y ⊓ Yv := ⟨y.2, hyYv⟩
      rw [hW, Subgroup.mem_bot] at hy0
      rw [Subgroup.mem_bot]
      exact Subtype.ext hy0
    have hinj : Function.Injective fH := (MonoidHom.ker_eq_bot_iff fH).mp hker
    have hcmInj : Function.Injective
        (fun y : ↥Y => (⟨fH y, (mem_cmSub).mpr ⟨(y : V), rfl⟩⟩ : ↥(cmSub vV))) := by
      intro a b hab
      apply hinj
      exact congrArg Subtype.val hab
    have h5 := five_le_card_of_nontriv hcard hYinv hYnt
    have h6 := Nat.card_le_card_of_injective _ hcmInj
    omega

end CFSG.Quasithin.H13.Abs523
