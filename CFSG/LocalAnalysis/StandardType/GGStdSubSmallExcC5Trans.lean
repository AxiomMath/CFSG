module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5Count
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Assembly TableB

section Transport

variable {p : ℕ} {L' G0 : Type} [Group L'] [Group G0]

theorem false_of_count (θ : L' ≃* G0) (hZ : Subgroup.center G0 = ⊥)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, MulAut.congr θ a ∈ Set.range (MulAut.conj : G0 →* MulAut G0))
    (hTwo : ∃ U : Subgroup L', U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ a ∈ A, ∀ u ∈ U, a u ∈ U)
    {a₀ : MulAut L'} (ha₀ : a₀ ∈ A) (ha₀1 : a₀ ≠ 1)
    (hcomp : IsComponentOf (LargeEvenLayer (ggFix a₀)) (ggFix a₀))
    (hcent : ∀ a' ∈ A, ((∀ j ∈ LargeEvenLayer (ggFix a₀), a' j = j) ↔
      a' ∈ Subgroup.zpowers a₀))
    (hsmall : GGStdSubSmallHyp p A a₀)
    (hcount : ∀ B : Subgroup G0, IsElemAbelian p B → Nat.card B = Nat.card A →
      NormalizesTwoGroup B → ∀ x ∈ B, x ≠ 1 → NodeCount p B x) : False := by
  have hinj := conj_injective_of_center_bot hZ
  set Θ : MulAut L' ≃* MulAut G0 := MulAut.congr θ with hΘ
  set B : Subgroup G0 := (A.map Θ.toMonoidHom).comap (MulAut.conj : G0 →* MulAut G0) with hB
  have hmemB : ∀ s : G0, s ∈ B ↔ ∃ a ∈ A, Θ a = MulAut.conj s := by
    intro s
    rw [hB, Subgroup.mem_comap, Subgroup.mem_map]
    exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩⟩
  have hex : ∀ a ∈ A, ∃ s ∈ B, Θ a = MulAut.conj s := by
    intro a ha
    obtain ⟨s, hs⟩ := hAI a ha
    exact ⟨s, (hmemB s).2 ⟨a, ha, hs.symm⟩, hs.symm⟩
  have hAmap : IsElemAbelian p (A.map Θ.toMonoidHom) := TableB.isElemAbelian_map hA _
  have hBel : IsElemAbelian p B :=
    ⟨⟨⟨fun a b => Subtype.ext (hinj (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hAmap a.2 b.2))⟩⟩, fun x hx => hinj (by
      rw [map_pow, map_one]
      exact hAmap.2 _ hx)⟩
  have hBmap : B.map (MulAut.conj : G0 →* MulAut G0) = A.map Θ.toMonoidHom := by
    rw [hB, Subgroup.map_comap_eq, inf_eq_right.mpr]
    rintro _ ⟨a, ha, rfl⟩
    exact hAI a ha
  have hBcard : Nat.card B = Nat.card A := by
    rw [← Subgroup.card_map_of_injective hinj, hBmap, Subgroup.card_map_of_injective Θ.injective]
  have hBTwo : NormalizesTwoGroup B := by
    obtain ⟨U, hU1, hU2, hUA⟩ := hTwo
    have hfwd : ∀ s ∈ B, ∀ x ∈ U.map θ.toMonoidHom, s * x * s⁻¹ ∈ U.map θ.toMonoidHom := by
      intro s hs x hx
      obtain ⟨a, ha, hΘa⟩ := (hmemB s).1 hs
      obtain ⟨u, hu, rfl⟩ := hx
      refine ⟨a u, hUA a ha u hu, ?_⟩
      have h1 : Θ a (θ u) = s * θ u * s⁻¹ := by rw [hΘa, MulAut.conj_apply]
      have h2 : Θ a (θ u) = θ (a u) := by simp [hΘ, MulAut.congr_apply]
      exact h2.symm.trans h1
    refine ⟨U.map θ.toMonoidHom, ?_, hU2.map _, fun s hs => ?_⟩
    · intro h
      apply hU1
      rw [eq_bot_iff]
      intro u hu
      have : θ u ∈ (⊥ : Subgroup G0) := h ▸ ⟨u, hu, rfl⟩
      rw [Subgroup.mem_bot, map_eq_one_iff _ θ.injective] at this
      exact this ▸ Subgroup.one_mem _
    · rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => hfwd s hs x hx, fun hx => ?_⟩
      have := hfwd s⁻¹ (inv_mem hs) _ hx
      simpa [mul_assoc] using this
  obtain ⟨r₀, hr₀B, hΘr₀⟩ := hex a₀ ha₀
  have hr₀1 : r₀ ≠ 1 := by
    rintro rfl
    apply ha₀1
    apply Θ.injective
    rw [hΘr₀, map_one, map_one]
  have hfix : (ggFix a₀).map θ.toMonoidHom = Subgroup.centralizer ({r₀} : Set G0) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : Θ a₀ (θ x) = θ x := by simp [hΘ, MulAut.congr_apply, mem_ggFix.1 hx]
      rw [hΘr₀, MulAut.conj_apply] at h1
      calc θ x * r₀ = r₀ * θ x * r₀⁻¹ * r₀ := by rw [h1]
        _ = r₀ * θ x := by group
    · intro hy
      refine ⟨θ.symm y, ?_, θ.apply_symm_apply y⟩
      rw [SetLike.mem_coe, mem_ggFix]
      apply θ.injective
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 hy
      have h2 : Θ a₀ y = y := by
        rw [hΘr₀, MulAut.conj_apply]
        calc r₀ * y * r₀⁻¹ = y * r₀ * r₀⁻¹ := by rw [h1]
          _ = y := by group
      simpa [hΘ, MulAut.congr_apply] using h2
  have hlayer : LargeEvenLayer (Subgroup.centralizer ({r₀} : Set G0)) =
      (LargeEvenLayer (ggFix a₀)).map θ.toMonoidHom := by
    rw [← hfix]
    exact largeEvenLayer_map_of_injective _ θ.injective _
  have hcomp' : IsComponentOf (LargeEvenLayer (Subgroup.centralizer ({r₀} : Set G0)))
      (Subgroup.centralizer ({r₀} : Set G0)) := by
    rw [hlayer, ← hfix]
    exact isComponentOf_map_of_injective _ θ.injective hcomp
  have hcent' : ∀ s ∈ B, ((∀ j ∈ LargeEvenLayer (Subgroup.centralizer ({r₀} : Set G0)),
      s * j = j * s) ↔ s ∈ Subgroup.zpowers r₀) := by
    intro s hs
    obtain ⟨a', ha', hΘa'⟩ := (hmemB s).1 hs
    have h2 : (∀ j ∈ LargeEvenLayer (Subgroup.centralizer ({r₀} : Set G0)), s * j = j * s) ↔
        (∀ j ∈ LargeEvenLayer (ggFix a₀), a' j = j) := by
      rw [hlayer]
      constructor
      · intro h j hj
        have h1 := h (θ j) ⟨j, hj, rfl⟩
        apply θ.injective
        have e : Θ a' (θ j) = θ j := by
          rw [hΘa', MulAut.conj_apply]
          calc s * θ j * s⁻¹ = θ j * s * s⁻¹ := by rw [h1]
            _ = θ j := by group
        simpa [hΘ, MulAut.congr_apply] using e
      · rintro h _ ⟨j, hj, rfl⟩
        have e : Θ a' (θ j) = θ j := by simp [hΘ, MulAut.congr_apply, h j hj]
        rw [hΘa', MulAut.conj_apply] at e
        calc s * θ j = (s * θ j * s⁻¹) * s := by group
          _ = θ j * s := by rw [e]
    have h3 : s ∈ Subgroup.zpowers r₀ ↔ a' ∈ Subgroup.zpowers a₀ := by
      rw [← mem_zpowers_map_iff (MulAut.conj : G0 →* MulAut G0) hinj s r₀, ← hΘa', ← hΘr₀]
      exact mem_zpowers_map_iff Θ.toMonoidHom Θ.injective a' a₀
    rw [h2, h3]
    exact hcent a' ha'
  have hc := hcount B hBel hBcard hBTwo r₀ hr₀B hr₀1 hcomp' hcent'
  set E : Subgroup L' := (B ⊓ LargeEvenLayer (Subgroup.centralizer ({r₀} : Set G0))).map
    θ.symm.toMonoidHom with hE
  have hEcard : Nat.card E =
      Nat.card (B ⊓ LargeEvenLayer (Subgroup.centralizer ({r₀} : Set G0)) : Subgroup G0) :=
    Subgroup.card_map_of_injective θ.symm.injective
  have hEel : IsElemAbelian p E :=
    TableB.isElemAbelian_map (isElemAbelian_of_le' hBel inf_le_left) _
  have hEle : E ≤ LargeEvenLayer (ggFix a₀) := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := hy.2
    rw [hlayer] at h1
    obtain ⟨j, hj, rfl⟩ := h1
    simpa using hj
  have hEfix : ∀ a' ∈ A, ∀ e ∈ E, a' e = e := by
    rintro a' ha' _ ⟨y, hy, rfl⟩
    obtain ⟨s, hs, hΘs⟩ := hex a' ha'
    have h1 : Θ a' y = y := by
      rw [hΘs, MulAut.conj_apply]
      calc s * y * s⁻¹ = y * s * s⁻¹ := by rw [TableB.IsElemAbelian.comm hBel hs hy.1]
        _ = y := by group
    simpa [hΘ, MulAut.congr_apply] using congrArg θ.symm h1
  have hEalt : ∀ e ∈ E, MulAut.conj e ∈ A := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨a, ha, hΘa⟩ := (hmemB y).1 hy.1
    have h1 : Θ (MulAut.conj (θ.symm y)) = MulAut.conj y := by
      ext x
      simp [hΘ, MulAut.congr_apply, MulAut.conj_apply]
    have h2 : MulAut.conj (θ.symm y) = a := Θ.injective (h1.trans hΘa.symm)
    simpa [h2] using ha
  have hlt := hsmall E hEel hEle hEfix (Or.inl hEalt)
  rw [hEcard] at hlt
  exact absurd hc (not_le.2 hlt)

end Transport

end CFSG.StandardType.SmallExc

end
