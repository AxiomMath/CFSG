module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row6Common
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.A7AutFix
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin

open CFSG.Open
open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC

namespace Stellmacher.L3YC

theorem row6_center_alt7 {X : Type} [Group X] (hX : IsAlt 7 X) {z : X}
    (hz : ∀ a : X, z * a = a * z) : z = 1 := by
  obtain ⟨e⟩ := hX
  have hs : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hnc : ¬ IsMulCommutative (alternatingGroup (Fin 7)) := by
    rw [alternatingGroup.isMulCommutative_iff_card_le_three]
    simp
  have hc : e z ∈ Subgroup.center (alternatingGroup (Fin 7)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg e (hz (e.symm g))
    simpa using this.symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (alternatingGroup (Fin 7)))
    with h | h
  · rw [h, Subgroup.mem_bot] at hc
    exact e.injective (by rw [hc, map_one])
  · exfalso
    apply hnc
    exact ⟨⟨fun a b => (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm⟩⟩

theorem row6_alt7_false {K : Type} [Group K] [Finite K] {N Lb : Subgroup K} [N.Normal]
    (hLb : Lb ≤ N) (hrank : ∀ E : Subgroup K, IsElemAbelian 3 E → Nat.card E ≤ 9)
    (hA7 : IsAlt 7 ↥N) (hLb168 : Nat.card Lb = 168)
    (h6b : ∀ (X : Type) [Group X], IsAlt 7 X → ∀ E : Subgroup X, Nat.card E = 9 →
      ∀ a ∈ E, ∀ b ∈ E, a ≠ 1 → b ∉ Subgroup.zpowers a →
        ∀ n : X, n * a * n⁻¹ = a⁻¹ → n * b * n⁻¹ = b → False)
    {e x p c : K} (he : e ∈ Lb) (he3 : orderOf e = 3) (hx3 : orderOf x = 3)
    (hex : e * x = x * e) (hxL : x ∉ Subgroup.normalizer (Lb : Set K)) (hp : p ∈ Lb)
    (hc : ∀ y ∈ Lb, c * y * c⁻¹ = y) (hse : p * c * e * (p * c)⁻¹ = e⁻¹)
    (hsx : p * c * x * (p * c)⁻¹ = x) : False := by
  classical
  have hZ : ∀ z ∈ N, (∀ a ∈ N, z * a = a * z) → z = 1 := fun z hz hzc =>
    congrArg Subtype.val
      (row6_center_alt7 hA7 (z := ⟨z, hz⟩) (fun a => Subtype.ext (hzc a a.2)))
  have hT2 : ∀ g : K, (∃ m : ℕ, g ^ 3 ^ m = 1) →
      ∃ n ∈ N, ∀ a ∈ N, g * a * g⁻¹ = n * a * n⁻¹ := by
    rintro g ⟨m, hm⟩
    have hτ : (MulAut.conjNormal g : MulAut ↥N) ^ 3 ^ m = 1 := by
      rw [← map_pow, hm, map_one]
    obtain ⟨n, hn⟩ := A7Inner.inner_of_isAlt7_pow_three hA7 _ m hτ
    refine ⟨n.1, n.2, fun a ha => ?_⟩
    have := congrArg Subtype.val (hn ⟨a, ha⟩)
    simpa [MulAut.conjNormal_apply, MulAut.conj_apply] using this
  have hxN : x ∈ N := lemma2_trivial_center hLb hrank hZ hT2 he he3 hx3 hex hxL
  have hτ1 : (MulAut.conjNormal c : MulAut ↥N) = 1 := by
    refine CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.A7AutFix.fixes_imp_one hA7 (Lb.subgroupOf N) ?_ _ ?_
    · exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLb).toEquiv).trans hLb168
    · intro y hy
      apply Subtype.ext
      simpa [MulAut.conjNormal_apply] using hc y.1 hy
  have hcN : ∀ y ∈ N, c * y * c⁻¹ = y := fun y hy => by
    have := congrArg (fun τ : MulAut ↥N => (τ ⟨y, hy⟩ : _).1) hτ1
    simpa [MulAut.conjNormal_apply] using this
  have hpe : p * e * p⁻¹ = e⁻¹ := by
    calc p * e * p⁻¹ = p * (c * e * c⁻¹) * p⁻¹ := by rw [hc e he]
      _ = p * c * e * (p * c)⁻¹ := by group
      _ = e⁻¹ := hse
  have hpx : p * x * p⁻¹ = x := by
    calc p * x * p⁻¹ = p * (c * x * c⁻¹) * p⁻¹ := by rw [hcN x hxN]
      _ = p * c * x * (p * c)⁻¹ := by group
      _ = x := hsx
  have he1 : e ≠ 1 := fun h => by rw [h, orderOf_one] at he3; omega
  have hxe : x ∉ Subgroup.zpowers e := fun h =>
    hxL (Subgroup.le_normalizer ((Subgroup.zpowers_le.mpr he) h))
  obtain ⟨hE, hE9⟩ := row6_exists_E9 he3 hx3 hex hxe
  have hE₀N : Subgroup.zpowers e ⊔ Subgroup.zpowers x ≤ N :=
    sup_le (Subgroup.zpowers_le.mpr (hLb he)) (Subgroup.zpowers_le.mpr hxN)
  have h9 : Nat.card ((Subgroup.zpowers e ⊔ Subgroup.zpowers x).subgroupOf N) = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀N).toEquiv).trans hE9
  refine h6b ↥N hA7 _ h9 ⟨e, hLb he⟩ ?_ ⟨x, hxN⟩ ?_ ?_ ?_ ⟨p, hLb hp⟩ ?_ ?_
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers e)
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  · intro h
    exact he1 (congrArg Subtype.val h)
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    apply hxe
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    simpa using congrArg Subtype.val hk
  · apply Subtype.ext
    simpa using hpe
  · apply Subtype.ext
    simpa using hpx

end Stellmacher.L3YC

end CFSG.Quasithin
