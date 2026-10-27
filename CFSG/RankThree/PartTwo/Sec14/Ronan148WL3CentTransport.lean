module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiKind

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG.RankThree.PartTwo.Sec4

variable {X : Type} [Group X] [Finite X] {D E : Subgroup X} {S : Type*} [Group S]

theorem coe_symm_slAct (φ : ↥D ≃* S) (x : Subgroup.normalizer (D : Set X)) (s : S) :
    ((φ.symm (slAct φ x s) : ↥D) : X) = (x : X) * (φ.symm s : X) * (x : X)⁻¹ := by
  rw [slAct_apply, MulEquiv.symm_apply_apply]
  rfl

theorem slAct_of_mem (φ : ↥D ≃* S) {e : X} (heD : e ∈ D)
    (heN : e ∈ Subgroup.normalizer (D : Set X)) :
    slAct φ ⟨e, heN⟩ = MulAut.conj (φ ⟨e, heD⟩) := by
  ext m
  rw [MulAut.conj_apply, ← φ.apply_symm_apply (slAct φ ⟨e, heN⟩ m)]
  have h : φ.symm (slAct φ ⟨e, heN⟩ m) = ⟨e, heD⟩ * φ.symm m * (⟨e, heD⟩ : ↥D)⁻¹ :=
    Subtype.ext (coe_symm_slAct φ _ m)
  rw [h, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem slAct_apply_self_of_commute (φ : ↥D ≃* S) {e : X} (heD : e ∈ D)
    (x : Subgroup.normalizer (D : Set X)) (hxe : (x : X) * e = e * x) :
    slAct φ x (φ ⟨e, heD⟩) = φ ⟨e, heD⟩ := by
  rw [← φ.apply_symm_apply (slAct φ x (φ ⟨e, heD⟩))]
  congr 1
  apply Subtype.ext
  rw [coe_symm_slAct, MulEquiv.symm_apply_apply, hxe, mul_inv_cancel_right]

theorem slAct_eq_self_of_hV (φ : ↥D ≃* S) (hED : E ≤ Subgroup.normalizer (D : Set X))
    (hV : ∀ V : Subgroup X, V ≤ D → ¬ 3 ∣ Nat.card V →
      E ≤ Subgroup.normalizer (V : Set X) → ⁅V, E⁆ = ⊥)
    (W : Subgroup S) (hW3 : ¬ 3 ∣ Nat.card W)
    (hWinv : ∀ (x : X) (hx : x ∈ E), ∀ w ∈ W, slAct φ ⟨x, hED hx⟩ w ∈ W)
    (x : X) (hx : x ∈ E) (w : S) (hw : w ∈ W) : slAct φ ⟨x, hED hx⟩ w = w := by
  set ψ : S →* X := D.subtype.comp φ.symm.toMonoidHom with hψ
  have hψi : Function.Injective ψ := D.subtype_injective.comp φ.symm.injective
  have hkey : ∀ (y : X) (hy : y ∈ E) (m : S), ψ (slAct φ ⟨y, hED hy⟩ m) = y * ψ m * y⁻¹ :=
    fun y hy m => coe_symm_slAct φ ⟨y, hED hy⟩ m
  set V : Subgroup X := W.map ψ with hVdef
  have hVD : V ≤ D := by
    rintro _ ⟨m, -, rfl⟩
    exact (φ.symm m).2
  have hcard : Nat.card V = Nat.card W := Subgroup.card_map_of_injective hψi
  have hEN : E ≤ Subgroup.normalizer (V : Set X) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨_, hWinv y hy m hm, hkey y hy m⟩
    · rintro ⟨m, hm, hmv⟩
      have hy' : y⁻¹ ∈ E := inv_mem hy
      refine ⟨slAct φ ⟨y⁻¹, hED hy'⟩ m, hWinv _ hy' m hm, ?_⟩
      rw [hkey _ hy', hmv]
      group
  have hc := hV V hVD (by rwa [hcard]) hEN
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hc
  have h1 := Subgroup.mem_centralizer_iff.mp (hc ⟨w, hw, rfl⟩) x hx
  apply hψi
  rw [hkey x hx w, h1, mul_inv_cancel_right]

theorem mem_zpowers_of_slAct_fixed (φ : ↥D ≃* S) (hED : E ≤ Subgroup.normalizer (D : Set X))
    (hF3 : ∀ w ∈ Subgroup.centralizer (E : Set X), w ^ 3 = 1 → w ∈ E) {e : X} (heD : e ∈ D)
    (heE : E ⊓ D ≤ Subgroup.zpowers e) (u : S) (hu3 : u ^ 3 = 1)
    (hfix : ∀ (x : X) (hx : x ∈ E), slAct φ ⟨x, hED hx⟩ u = u) :
    u ∈ Subgroup.zpowers (φ ⟨e, heD⟩) := by
  have hwC : ((φ.symm u : ↥D) : X) ∈ Subgroup.centralizer (E : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h := coe_symm_slAct φ ⟨x, hED hx⟩ u
    rw [hfix x hx] at h
    calc x * ((φ.symm u : ↥D) : X) = x * ((φ.symm u : ↥D) : X) * x⁻¹ * x := by group
      _ = ((φ.symm u : ↥D) : X) * x := by rw [← h]
  have hw3 : ((φ.symm u : ↥D) : X) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hu3, map_one, Subgroup.coe_one]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (heE (Subgroup.mem_inf.mpr ⟨hF3 _ hwC hw3, (φ.symm u).2⟩))
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have h1 : (⟨e, heD⟩ : ↥D) ^ k = φ.symm u := Subtype.ext (by rw [Subgroup.coe_zpow, hk])
  rw [← map_zpow, h1, MulEquiv.apply_symm_apply]

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
