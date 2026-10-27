module

public import CFSG.Quasithin.Background.A318PHatCore
public import CFSG.Quasithin.Background.A318PSkel

public section

namespace CFSG.Quasithin

namespace A318P

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

@[expose] noncomputable def hatDescend (S : Type*) [Group S] :
    MulAut S →* MulAut (S ⧸ Subgroup.center S) where
  toFun σ := QuotientGroup.congr _ _ σ (Subgroup.map_center_eq σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

theorem hatDescend_mk {S : Type*} [Group S] (σ : MulAut S) (x : S) :
    hatDescend S σ (x : S ⧸ Subgroup.center S) = ((σ x : S) : S ⧸ Subgroup.center S) :=
  rfl

theorem mulAut_eq_one_of_inv_mul_mem_center {S : Type*} [Group S] [Group.IsPerfect S]
    {α : MulAut S} (h : ∀ s, s⁻¹ * α s ∈ Subgroup.center S) : α = 1 := by
  let z : S →* Subgroup.center S :=
    { toFun := fun s => ⟨s⁻¹ * α s, h s⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun s t => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.mp (h s) (t⁻¹)
        simp only [map_mul, _root_.mul_inv_rev, Subgroup.coe_mul]
        calc (t⁻¹ * s⁻¹) * (α s * α t) = t⁻¹ * (s⁻¹ * α s) * α t := by group
          _ = (s⁻¹ * α s) * t⁻¹ * α t := by rw [hc]
          _ = (s⁻¹ * α s) * (t⁻¹ * α t) := by group }
  have hker : z.ker = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := S)]
    exact Abelianization.commutator_subset_ker z
  ext s
  have h1 : z s = 1 := (MonoidHom.mem_ker).mp (hker ▸ Subgroup.mem_top s)
  have h2 := congrArg Subtype.val h1
  simp only [z, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_one] at h2
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.mp h2).symm

theorem mem_inner_of_cube_of_not_dvd_outer {L : Type} [Group L] [Finite L]
    (hout : ¬ 3 ∣ Nat.card (Outer L)) {α : MulAut L} (hα : α ^ 3 = 1) :
    α ∈ (inner L : Subgroup (MulAut L)) := by
  have : Finite (MulAut L) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut L))
  set φ : Outer L := QuotientGroup.mk' (inner L) α with hφ
  have h1 : orderOf φ ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [hφ, ← map_pow, hα, map_one])
  have h2 : orderOf φ ∣ Nat.card (Outer L) := orderOf_dvd_natCard φ
  have h3 : orderOf φ = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact h
    · exact absurd (h ▸ h2) hout
  rw [orderOf_eq_one_iff, hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem mem_of_centralizes_of_orderOf_three {X : Type} [Group X] [Finite X] {S : Subgroup X}
    (hS2 : 2 ≤ CFSG.Open.pRank 3 S) (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2) {y : X}
    (hy : orderOf y = 3) (hyc : ∀ s ∈ S, y * s = s * y) : y ∈ S := by
  by_contra hyS
  have hrk : CFSG.Open.pRank 3 S = 2 :=
    le_antisymm ((CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt le_top).trans hX) hS2
  obtain ⟨E, hES, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank Nat.prime_three.one_lt S
  rw [hrk] at hEcard
  have h3 := three_le_pRank_of_centralizes (hp := ⟨Nat.prime_three⟩) hy hyS hES hEel hEcard
    (fun e he => hyc e (hES he))
  omega

theorem hat_false {X : Type} [Group X] [Finite X] {S : Subgroup X} [S.Normal]
    (hperf : Group.IsPerfect ↥S) (hZ : Nat.card (Subgroup.center ↥S) = 3)
    (hL : HatData (↥S ⧸ Subgroup.center ↥S)) (hS2 : 2 ≤ CFSG.Open.pRank 3 S)
    (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2) {x : X} (hx : orderOf x = 3) (hxS : x ∉ S) :
    False := by
  classical
  set θ : X →* MulAut ↥S := MulAut.conjNormal with hθ
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hψ3 : (hatDescend ↥S (θ x)) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, hx3, map_one, map_one]
  obtain ⟨l₀, hl₀⟩ := mem_inner_of_cube_of_not_dvd_outer hL.out hψ3
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective l₀
  set y : X := (l : X)⁻¹ * x with hy
  have hconj : hatDescend ↥S (MulAut.conj l) = MulAut.conj (l : ↥S ⧸ Subgroup.center ↥S) := by
    ext t
    induction t using QuotientGroup.induction_on with
    | H t =>
      show ((l * t * l⁻¹ : ↥S) : ↥S ⧸ Subgroup.center ↥S) = _
      simp
  have hψy : hatDescend ↥S (θ y) = 1 := by
    have h1 : θ y = (MulAut.conj l)⁻¹ * θ x := by
      rw [hy, map_mul, map_inv, hθ, MulAut.conjNormal_val]
    rw [h1, map_mul, map_inv, hconj, hl₀, inv_mul_cancel]
  have hθy : θ y = 1 := by
    apply mulAut_eq_one_of_inv_mul_mem_center
    intro s
    have h1 : hatDescend ↥S (θ y) (s : ↥S ⧸ Subgroup.center ↥S) =
        (s : ↥S ⧸ Subgroup.center ↥S) := by
      rw [hψy]
      rfl
    rw [hatDescend_mk] at h1
    exact QuotientGroup.eq.1 h1.symm
  have hyc : ∀ s ∈ S, y * s = s * y := by
    intro s hs
    have h1 := congrArg (fun φ : MulAut ↥S => (φ ⟨s, hs⟩ : X)) hθy
    simp only [hθ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc y * s = y * s * y⁻¹ * y := by group
      _ = s * y := by rw [h1]
  have hxy : x = (l : X) * y := by rw [hy]; group
  have hcomm : Commute (l : X) y := (hyc l l.2).symm
  have h3 : (l : X) ^ 3 * y ^ 3 = 1 := by
    rw [← hcomm.mul_pow, ← hxy, hx3]
  have hl3 : ((l ^ 3 : ↥S) : X) = (y ^ 3)⁻¹ := by
    rw [Subgroup.coe_pow]
    exact eq_inv_of_mul_eq_one_left h3
  by_cases hy1 : y ^ 3 = 1
  · by_cases hyone : y = 1
    · apply hxS
      rw [hxy, hyone, mul_one]
      exact l.2
    · have hyord : orderOf y = 3 := orderOf_eq_prime hy1 hyone
      have hyS := mem_of_centralizes_of_orderOf_three hS2 hX hyord hyc
      apply hxS
      rw [hxy]
      exact mul_mem l.2 hyS
  · have hl3c : l ^ 3 ∈ Subgroup.center ↥S := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hl3]
      have hc : Commute y (g : X) := hyc g g.2
      exact ((hc.pow_left 3).inv_left).eq.symm
    have hl3ne : l ^ 3 ≠ 1 := by
      intro h
      apply hy1
      have h2 : ((l ^ 3 : ↥S) : X) = 1 := by rw [h]; rfl
      rw [hl3] at h2
      exact inv_eq_one.1 h2
    exact no_order_nine hZ hL hl3c hl3ne

end A318P

end CFSG.Quasithin
