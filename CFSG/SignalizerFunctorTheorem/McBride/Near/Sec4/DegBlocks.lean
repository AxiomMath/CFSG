module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.DegSol
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.DegSS

public section

open CFSG.SignalizerFunctorTheorem.Nonsolvable

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Deg

@[expose] def pointFix {G Ω : Type*} [Group G] (f : G →* Equiv.Perm Ω) (Γ : Set Ω) :
    Subgroup G where
  carrier := {g | ∀ x ∈ Γ, f g x = x}
  one_mem' := fun x _ => by simp
  mul_mem' := fun {a b} ha hb x hx => by
    show f (a * b) x = x
    rw [map_mul, Equiv.Perm.mul_apply, hb x hx, ha x hx]
  inv_mem' := fun {a} ha x hx => by
    have h : f a⁻¹ (f a x) = x := by
      rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    show f a⁻¹ x = x
    rwa [ha x hx] at h

theorem mem_pointFix {G Ω : Type*} [Group G] (f : G →* Equiv.Perm Ω) (Γ : Set Ω) (g : G) :
    g ∈ pointFix f Γ ↔ ∀ x ∈ Γ, f g x = x := Iff.rfl

variable {G Q Ω : Type*} [Group G] [Group Q]

theorem conj_mem_inf_pointFix (f : G →* Equiv.Perm Ω) {K : Subgroup G} {Γ : Set Ω}
    (hinv : ∀ k ∈ K, ∀ x, f k x ∈ Γ ↔ x ∈ Γ) {k : G} (hk : k ∈ K) {x : G}
    (hx : x ∈ K ⊓ pointFix f Γ) : k * x * k⁻¹ ∈ K ⊓ pointFix f Γ := by
  obtain ⟨hxK, hxf⟩ := Subgroup.mem_inf.mp hx
  refine Subgroup.mem_inf.mpr ⟨K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk), fun y hy => ?_⟩
  have h1 : f k⁻¹ y ∈ Γ := (hinv k⁻¹ (inv_mem hk) y).mpr hy
  have h2 : f x (f k⁻¹ y) = f k⁻¹ y := hxf _ h1
  calc f (k * x * k⁻¹) y = f k (f x (f k⁻¹ y)) := by
        rw [map_mul, map_mul]
        rfl
    _ = f k (f k⁻¹ y) := by rw [h2]
    _ = y := by
        rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl

theorem kernel_block_le [Finite G] [Finite Q] (π : G →* Q) (hπ : Function.Surjective π)
    [Group.IsSolvable π.ker] (hQ : IsSS Q) (f : G →* Equiv.Perm Ω) (hf : f.ker ≤ π.ker)
    (K : Subgroup G) [K.Normal] (hRK : π.ker ≤ K) (𝒮 : Set (Set Ω))
    (hinv : ∀ Γ ∈ 𝒮, ∀ k ∈ K, ∀ x, f k x ∈ Γ ↔ x ∈ Γ)
    (hcov : ∀ x, ∃ Γ ∈ 𝒮, x ∈ Γ)
    (htrans : ∀ Γ ∈ 𝒮, ∀ Γ' ∈ 𝒮, ∃ g : G, ∀ x, f g x ∈ Γ' ↔ x ∈ Γ)
    {Γ : Set Ω} (hΓ : Γ ∈ 𝒮) : K ⊓ pointFix f Γ ≤ π.ker := by
  set Kb : Subgroup Q := K.map π with hKb
  have hKbn : Kb.Normal := Subgroup.Normal.map inferInstance π hπ
  have hM : ∀ Γ' ∈ 𝒮, ((K ⊓ pointFix f Γ').map π).Normal := by
    intro Γ' hΓ'
    refine hQ.normal_of_conj_closed (N := Kb) (Subgroup.map_mono inf_le_left) ?_
    rintro _ ⟨k, hk, rfl⟩ _ ⟨x, hx, rfl⟩
    exact ⟨k * x * k⁻¹, conj_mem_inf_pointFix f (hinv Γ' hΓ') hk hx, by simp⟩
  have hMle : ∀ Γ' ∈ 𝒮, ∀ Γ'' ∈ 𝒮, (K ⊓ pointFix f Γ').map π ≤ (K ⊓ pointFix f Γ'').map π := by
    intro Γ' hΓ' Γ'' hΓ''
    obtain ⟨g, hg⟩ := htrans Γ' hΓ' Γ'' hΓ''
    rintro _ ⟨x, ⟨hxK, hxf⟩, rfl⟩
    have hgx : g * x * g⁻¹ ∈ K ⊓ pointFix f Γ'' := by
      refine ⟨Subgroup.Normal.conj_mem inferInstance x hxK g, fun y hy => ?_⟩
      have hy' : f g (f g⁻¹ y) = y := by
        rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      have h1 : f g⁻¹ y ∈ Γ' := (hg _).mp (by rw [hy']; exact hy)
      calc f (g * x * g⁻¹) y = f g (f x (f g⁻¹ y)) := by
            rw [map_mul, map_mul]
            rfl
        _ = f g (f g⁻¹ y) := by rw [hxf _ h1]
        _ = y := hy'
    have h2 := (hM Γ'' hΓ'').conj_mem (π (g * x * g⁻¹)) (Subgroup.mem_map_of_mem π hgx) (π g⁻¹)
    have h3 : π g⁻¹ * π (g * x * g⁻¹) * (π g⁻¹)⁻¹ = π x := by
      simp only [map_mul, map_inv]
      group
    rwa [h3] at h2
  have hperf : ∀ Γ' ∈ 𝒮, Group.IsPerfect ↥((K ⊓ pointFix f Γ').map π) := fun Γ' hΓ' =>
    have := hM Γ' hΓ'
    (hQ.subgroup_of_normal _).isPerfect
  obtain ⟨P, hPdef⟩ : ∃ P : Subgroup G, P = (CFSG.perfectResidual ↥(K ⊓ pointFix f Γ)).map
      (K ⊓ pointFix f Γ).subtype := ⟨_, rfl⟩
  have hP1 : Group.IsPerfect ↥P := hPdef ▸ isPerfect_perfectResidual_map _
  have hP2 : P ≤ K ⊓ pointFix f Γ := hPdef ▸ Subgroup.map_subtype_le _
  have hP3 : P.map π = (K ⊓ pointFix f Γ).map π := by
    rw [hPdef, map_perfectResidual_map π]
    exact perfectResidual_map_eq_of_isPerfect (hperf Γ hΓ)
  have hP4 : ∀ Γ' ∈ 𝒮, P ≤ (K ⊓ pointFix f Γ') ⊔ π.ker := by
    intro Γ' hΓ' x hx
    have h1 : π x ∈ (K ⊓ pointFix f Γ').map π :=
      hMle Γ hΓ Γ' hΓ' (hP3 ▸ Subgroup.mem_map_of_mem π hx)
    obtain ⟨k, hk, hkx⟩ := h1
    have hr : k⁻¹ * x ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkx, inv_mul_cancel]
    have : x = k * (k⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hk hr
  have hP5 : ∀ Γ' ∈ 𝒮, π.ker ≤ Subgroup.normalizer ((K ⊓ pointFix f Γ' : Subgroup G) : Set G) := by
    intro Γ' hΓ' r hr
    have hrK := hRK hr
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => conj_mem_inf_pointFix f (hinv Γ' hΓ') hrK hx, fun hx => by
      have := conj_mem_inf_pointFix f (hinv Γ' hΓ') (inv_mem hrK) hx
      simpa [mul_assoc] using this⟩
  have hP6 : ∀ Γ' ∈ 𝒮, P ≤ K ⊓ pointFix f Γ' := fun Γ' hΓ' =>
    le_of_isPerfect_of_le_sup (hP5 Γ' hΓ') hP1 (hP4 Γ' hΓ')
  have hP7 : P ≤ π.ker := by
    intro x hx
    refine hf ?_
    rw [MonoidHom.mem_ker]
    ext y
    obtain ⟨Γ', hΓ', hy⟩ := hcov y
    exact (hP6 Γ' hΓ' hx).2 y hy
  have hP8 : P = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have := eq_one_of_isPerfect_of_isSolvable (Subgroup.inclusion hP7) ⟨x, hx⟩
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have h9 : (K ⊓ pointFix f Γ).map π = ⊥ := by rw [← hP3, hP8, Subgroup.map_bot]
  exact (Subgroup.map_eq_bot_iff _).mp h9

end CFSG.SignalizerFunctorTheorem.McBride.Near.Deg
