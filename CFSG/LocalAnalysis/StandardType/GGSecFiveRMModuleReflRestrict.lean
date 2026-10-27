module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.StandardType

section Module

private abbrev GGU
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (A : Subgroup (V ≃ₗ[ZMod p] V)) : Submodule (ZMod p) V :=
  ggLinCom (A : Set (V ≃ₗ[ZMod p] V))

private lemma move_le_GGU
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (a : ↥A) :
    ggLinMove (a : V ≃ₗ[ZMod p] V) ≤ GGU A :=
  le_biSup (fun b : V ≃ₗ[ZMod p] V => ggLinMove b) a.2

private lemma apply_eq_neg_of_mem_move
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (a : V ≃ₗ[ZMod p] V) (ha : a * a = 1) {w : V} (hw : w ∈ ggLinMove a) :
    (a : V →ₗ[ZMod p] V) w = -w := by
  rcases hw with ⟨v, hv⟩
  rw [← hv]
  have hφφ : (a : V →ₗ[ZMod p] V) ((a : V →ₗ[ZMod p] V) v) = v := by
    have h : (a * a) v = (1 : V ≃ₗ[ZMod p] V) v := congrArg (fun e => e v) ha
    rw [LinearEquiv.mul_apply] at h
    simpa using h
  change (a : V →ₗ[ZMod p] V) ((((a : V →ₗ[ZMod p] V) - LinearMap.id : V →ₗ[ZMod p] V)) v) =
    -((((a : V →ₗ[ZMod p] V) - LinearMap.id : V →ₗ[ZMod p] V)) v)
  rw [LinearMap.sub_apply, LinearMap.id_apply, map_sub, hφφ, neg_sub]

private lemma finrank_move_restrict_eq
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (hp2 : p ≠ 2) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (r : ↥A →* (↥(GGU A) ≃ₗ[ZMod p] ↥(GGU A)))
    (hr : ∀ (a : ↥A) (u : ↥(GGU A)),
      ((r a u : ↥(GGU A)) : V) = (a : V ≃ₗ[ZMod p] V) u)
    (a : ↥A) (ha : (a : V ≃ₗ[ZMod p] V) * (a : V ≃ₗ[ZMod p] V) = 1) :
    Module.finrank (ZMod p) (ggLinMove (r a)) =
      Module.finrank (ZMod p) (ggLinMove (a : V ≃ₗ[ZMod p] V)) := by
  have hprime : p.Prime := Fact.out
  have hpgt : 2 < p := lt_of_le_of_ne hprime.two_le (Ne.symm hp2)
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    exact Nat.not_dvd_of_pos_of_lt (by norm_num) hpgt hdvd
  have hneg2 : (-2 : ZMod p) ≠ 0 := neg_ne_zero.mpr h2
  have hmove_le : ggLinMove (a : V ≃ₗ[ZMod p] V) ≤ GGU A := move_le_GGU A a
  have hcomp :
      (GGU A).subtype.comp ((r a).toLinearMap - LinearMap.id) =
        ((a : V ≃ₗ[ZMod p] V).toLinearMap - LinearMap.id).comp (GGU A).subtype := by
    ext u
    change (((r a) u : ↥(GGU A)) : V) - (u : V) =
      (a : V ≃ₗ[ZMod p] V) (u : V) - (u : V)
    rw [hr a u]
  have hmap : Submodule.map (GGU A).subtype (ggLinMove (r a)) =
      ggLinMove (a : V ≃ₗ[ZMod p] V) := by
    rw [ggLinMove, ggLinMove, ← LinearMap.range_comp, hcomp, LinearMap.range_comp,
      Submodule.range_subtype]
    apply le_antisymm
    · exact LinearMap.map_le_range
    · intro w hw
      rw [Submodule.mem_map]
      refine ⟨(-2 : ZMod p)⁻¹ • w, ?_, ?_⟩
      · exact Submodule.smul_mem _ _ (hmove_le hw)
      · have hwφ : (a : V →ₗ[ZMod p] V) w = -w := apply_eq_neg_of_mem_move _ ha hw
        have hfw : (((a : V →ₗ[ZMod p] V) - LinearMap.id : V →ₗ[ZMod p] V)) w =
            (-2 : ZMod p) • w := by
          simp only [LinearMap.sub_apply, LinearMap.id_apply]
          rw [hwφ, neg_smul, two_smul, neg_add]
          abel
        rw [map_smul, hfw, smul_smul, inv_mul_cancel₀ hneg2, one_smul]
  calc Module.finrank (ZMod p) (ggLinMove (r a))
      = Module.finrank (ZMod p) (Submodule.map (GGU A).subtype (ggLinMove (r a))) :=
        (Submodule.finrank_map_subtype_eq (GGU A) (ggLinMove (r a))).symm
    _ = Module.finrank (ZMod p) (ggLinMove (a : V ≃ₗ[ZMod p] V)) := by rw [hmap]

private lemma involution_iff
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hfaith : ∀ g ∈ A, (∀ u ∈ GGU A, g u = u) → g = 1)
    (r : ↥A →* (↥(GGU A) ≃ₗ[ZMod p] ↥(GGU A)))
    (hr : ∀ (a : ↥A) (u : ↥(GGU A)),
      ((r a u : ↥(GGU A)) : V) = (a : V ≃ₗ[ZMod p] V) u)
    (a : ↥A) :
    (a : V ≃ₗ[ZMod p] V) * (a : V ≃ₗ[ZMod p] V) = 1 ↔ r a * r a = 1 := by
  constructor
  · intro ha
    have h1 : a * a = 1 := by
      apply Subtype.ext
      simpa [Subgroup.coe_mul] using ha
    calc r a * r a = r (a * a) := (map_mul r a a).symm
      _ = r 1 := by rw [h1]
      _ = 1 := map_one r
  · intro hr2
    refine hfaith ((a : V ≃ₗ[ZMod p] V) * (a : V ≃ₗ[ZMod p] V)) (A.mul_mem a.2 a.2) ?_
    intro u hu
    let uu : ↥(GGU A) := ⟨u, hu⟩
    have hru : (r a * r a) uu = uu := by rw [hr2]; rfl
    have hh : ((r (a * a) uu : ↥(GGU A)) : V) =
        ((a : V ≃ₗ[ZMod p] V) * (a : V ≃ₗ[ZMod p] V)) u := by
      have h := hr (a * a) uu
      simpa [map_mul, Subgroup.coe_mul] using h
    have h2 : ((r (a * a) uu : ↥(GGU A)) : V) = u := by
      rw [map_mul r a a, hru]
    rw [← hh, h2]

theorem ggLin_refl_iff_restrict
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (hp2 : p ≠ 2) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hfaith : ∀ g ∈ A, (∀ u ∈ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)), g u = u) → g = 1)
    (r : ↥A →* (↥(ggLinCom (A : Set (V ≃ₗ[ZMod p] V))) ≃ₗ[ZMod p] ↥(ggLinCom (A : Set (V ≃ₗ[ZMod p] V)))))
    (hr : ∀ (a : ↥A) (u : ↥(ggLinCom (A : Set (V ≃ₗ[ZMod p] V)))),
      ((r a u : ↥(ggLinCom (A : Set (V ≃ₗ[ZMod p] V)))) : V) = (a : V ≃ₗ[ZMod p] V) u)
    (a : ↥A) : GGLinRefl (a : V ≃ₗ[ZMod p] V) ↔ GGLinRefl (r a) := by
  have hiff := involution_iff (A := A) hfaith r hr a
  rw [GGLinRefl, GGLinRefl]
  constructor
  · rintro ⟨ha, hfr⟩
    refine ⟨hiff.mp ha, ?_⟩
    rw [finrank_move_restrict_eq hp2 A r hr a ha]
    exact hfr
  · rintro ⟨hr2, hfr⟩
    have ha : (a : V ≃ₗ[ZMod p] V) * (a : V ≃ₗ[ZMod p] V) = 1 := hiff.mpr hr2
    refine ⟨ha, ?_⟩
    rw [← finrank_move_restrict_eq hp2 A r hr a ha]
    exact hfr

end Module

end CFSG.StandardType

end
