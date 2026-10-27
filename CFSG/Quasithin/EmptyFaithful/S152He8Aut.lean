module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.Quasithin.He8

open CFSG.ComponentClassification.OuterAutomorphisms

section Abstract

variable {Λ : Type} [Group Λ]

theorem conj_injective_of_center_bot (hZ : Subgroup.center Λ = ⊥) :
    Function.Injective (MulAut.conj : Λ →* MulAut Λ) := by
  intro a b hab
  have hc : b⁻¹ * a ∈ Subgroup.center Λ := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun φ : MulAut Λ => φ g) hab
    simp only [MulAut.conj_apply] at h
    calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
      _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [h]
      _ = (b⁻¹ * a) * g := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.mp hc).symm

variable {R : Type} [Group R]

theorem quot_equiv_of_normal_image [Finite R] [Finite Λ] (hs : IsSimpleGroup Λ)
    (hZ : Subgroup.center Λ = ⊥) [Group.IsSolvable (Outer Λ)] [Group.IsPerfect R] [Nontrivial R]
    (α : R →* MulAut Λ) (hnorm : α.range.Normal) (h2 : IsPGroup 2 α.ker) :
    Nonempty ((R ⧸ CFSG.pCore 2 R) ≃* Λ) := by
  classical
  have hinj := conj_injective_of_center_bot hZ
  have hinner : ∀ r : R, ∃ l : Λ, α r = MulAut.conj l := perfect_action_inner α
  choose β hβ using hinner
  let βh : R →* Λ :=
    { toFun := β
      map_one' := hinj (by rw [← hβ 1, map_one, map_one])
      map_mul' := fun x y => hinj (by rw [map_mul, ← hβ, ← hβ, ← hβ, map_mul]) }
  have hβh : ∀ r, α r = MulAut.conj (βh r) := hβ
  have hrange : βh.range.Normal := by
    refine ⟨fun l hl g => ?_⟩
    obtain ⟨r, rfl⟩ := hl
    have h1 : MulAut.conj g * α r * (MulAut.conj g)⁻¹ ∈ α.range :=
      hnorm.conj_mem _ ⟨r, rfl⟩ _
    obtain ⟨r', hr'⟩ := h1
    refine ⟨r', hinj ?_⟩
    rw [← hβh r', hr', hβh r, map_mul, map_mul, map_inv]
  have hker : βh.ker = α.ker := by
    ext r
    simp only [MonoidHom.mem_ker]
    rw [hβh r]
    constructor
    · intro h
      rw [h, map_one]
    · intro h
      exact hinj (by rw [h, map_one])
  have hsurj : Function.Surjective βh := by
    have := hrange
    rcases hs.eq_bot_or_eq_top_of_normal βh.range with hb | ht
    · exfalso
      have hall : ∀ r : R, r ∈ α.ker := by
        intro r
        have : βh r ∈ βh.range := ⟨r, rfl⟩
        rw [hb, Subgroup.mem_bot] at this
        rw [← hker, MonoidHom.mem_ker]
        exact this
      have h2R : IsPGroup 2 R := fun r => by
        obtain ⟨k, hk⟩ := h2 ⟨r, hall r⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
      have : Group.IsNilpotent R := h2R.isNilpotent
      have hsolv : Group.IsSolvable R := inferInstance
      exact Group.IsPerfect.not_isSolvable R hsolv
    · exact MonoidHom.range_eq_top.mp ht
  have hq : CFSG.pCore 2 R = βh.ker := by
    refine le_antisymm ?_ ?_
    · have hQn : (CFSG.pCore 2 R).Normal := CFSG.pCore_normal
      have hmapn : ((CFSG.pCore 2 R).map βh).Normal := hQn.map βh hsurj
      rcases hs.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 R).map βh) with hb | ht
      · intro x hx
        have : βh x ∈ (CFSG.pCore 2 R).map βh := Subgroup.mem_map_of_mem βh hx
        rw [hb, Subgroup.mem_bot] at this
        exact this
      · exfalso
        have hP : IsPGroup 2 ↥((CFSG.pCore 2 R).map βh) := (CFSG.pCore_isPGroup).map βh
        have hΛ : IsPGroup 2 Λ := fun l => by
          obtain ⟨k, hk⟩ := hP ⟨l, ht ▸ Subgroup.mem_top l⟩
          exact ⟨k, by simpa using congrArg Subtype.val hk⟩
        have : Nontrivial Λ := hs.toNontrivial
        have hc := hΛ.center_nontrivial
        rw [hZ] at hc
        exact (Subgroup.nontrivial_iff_ne_bot (⊥ : Subgroup Λ)).mp hc rfl
    · rw [hker]
      exact le_sSup (show α.ker ∈ {K : Subgroup R | K.Normal ∧ IsPGroup 2 K} from
        ⟨inferInstance, h2⟩)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hq).trans
    (QuotientGroup.quotientKerEquivOfSurjective βh hsurj)⟩

end Abstract

end CFSG.Quasithin.He8
