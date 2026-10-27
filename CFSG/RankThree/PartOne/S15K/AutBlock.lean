module

public import CFSG.RankThree.PartOne.S15K.AutLayer
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.RankThree.PartOne.S15K

open scoped commutatorElement
open CFSG CFSG.RankThree.PartOne.KCUnitary

section Block

variable {H T : Type*} [Group H] [Group T]

theorem exists_central_of_fixed {π : H →* T} (hker : π.ker ≤ Subgroup.center H) {a : MulAut H}
    {β : MulAut T} (hπa : ∀ x, π (a x) = β (π x)) {G₀ : H} (hG₀ : β (π G₀) = π G₀) :
    ∃ z ∈ Subgroup.center H, a G₀ = G₀ * z := by
  refine ⟨G₀⁻¹ * a G₀, hker ?_, by group⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hπa, hG₀, inv_mul_cancel]

theorem isComponent_map_block_aut {π : H →* T} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center H) {a : MulAut H} {β : MulAut T}
    (hπa : ∀ x, π (a x) = β (π x)) {B : Subgroup H} (hBq : IsQuasisimple ↥B) (hBfix : B ≤ fixedSub a)
    (hBnorm : ∀ g ∈ fixedSub a, ∀ f ∈ B, g * f * g⁻¹ ∈ B) :
    B.map π ≤ fixedSub β ∧ IsComponent ((B.map π).subgroupOf (fixedSub β)) := by
  have hBnc : ¬ B ≤ π.ker := fun hle => by
    have hperf := hBq.1
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hBq
    have hcomm : commutator ↥B = ⊥ := by
      rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _ y _
      exact Subtype.ext (Subgroup.mem_center_iff.mp (hker (hle x.2)) y)
    have : (⊤ : Subgroup ↥B) = ⊥ := by rw [← hperf.commutator_eq_top, hcomm]
    exact (Subgroup.nontrivial_iff_ne_bot (⊤ : Subgroup ↥B)).mp inferInstance this
  set D₀ : Subgroup T := B.map π with hD₀
  have hD₀q : IsQuasisimple ↥D₀ := CFSG.LocalCores.isQuasisimple_map hBq π hBnc
  set C0 : Subgroup T := (fixedSub a).map π with hC0
  set Cx : Subgroup T := fixedSub β with hCx
  have hC0Cx : C0 ≤ Cx := by
    rintro _ ⟨g, hg, rfl⟩
    change β (π g) = π g
    rw [← hπa, hg]
  have hD₀C0 : D₀ ≤ C0 := Subgroup.map_mono hBfix
  have hconj1 : ∀ g ∈ Cx, ∀ h ∈ C0, g * h * g⁻¹ ∈ C0 := by
    intro g hg h hh
    obtain ⟨G₀, rfl⟩ := hπ g
    obtain ⟨H', hH', rfl⟩ := hh
    refine ⟨G₀ * H' * G₀⁻¹, ?_, by simp [map_mul, map_inv]⟩
    obtain ⟨z, hz, hGz⟩ := exists_central_of_fixed hker hπa (G₀ := G₀) hg
    change a (G₀ * H' * G₀⁻¹) = G₀ * H' * G₀⁻¹
    have hH'a : a H' = H' := hH'
    rw [map_mul, map_mul, map_inv, hGz, hH'a]
    have hzc := Subgroup.mem_center_iff.mp hz
    have e1 : (G₀ * z)⁻¹ = z⁻¹ * G₀⁻¹ := mul_inv_rev G₀ z
    rw [e1]
    calc G₀ * z * H' * (z⁻¹ * G₀⁻¹) = G₀ * (z * H' * z⁻¹) * G₀⁻¹ := by group
      _ = G₀ * H' * G₀⁻¹ := by
        have : z * H' = H' * z := (hzc H').symm
        rw [this, mul_inv_cancel_right]
  have hconj0 : ∀ g ∈ C0, ∀ d ∈ D₀, g * d * g⁻¹ ∈ D₀ := by
    intro g hg d hd
    obtain ⟨H', hH', rfl⟩ := hg
    obtain ⟨b₀, hb₀, rfl⟩ := hd
    exact ⟨H' * b₀ * H'⁻¹, hBnorm _ hH' _ hb₀, by simp [map_mul, map_inv]⟩
  have hCxN : Cx ≤ Subgroup.normalizer (C0 : Set T) := fun g hg =>
    Subgroup.mem_normalizer_iff.mpr fun x => ⟨hconj1 g hg x, fun hx => by
      simpa [mul_assoc] using hconj1 g⁻¹ (Cx.inv_mem hg) _ hx⟩
  have hD₀Cx : D₀ ≤ Cx := hD₀C0.trans hC0Cx
  refine ⟨hD₀Cx, ?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hD₀Cx).symm hD₀q
  · have hD1C1 : D₀.subgroupOf Cx ≤ C0.subgroupOf Cx := fun g hg => hD₀C0 hg
    have hn1 : (C0.subgroupOf Cx).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hC0Cx]
      exact hCxN
    have hn2 : ((D₀.subgroupOf Cx).subgroupOf (C0.subgroupOf Cx)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hD1C1]
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have hgC0 : (g : T) ∈ C0 := hg
      constructor
      · intro hh
        exact hconj0 _ hgC0 _ hh
      · intro hh
        have := hconj0 _ (C0.inv_mem hgC0) _ hh
        exact Subgroup.mem_subgroupOf.mpr (by simpa [mul_assoc] using this)
    exact Subgroup.IsSubnormal.trans hD1C1 hn2.isSubnormal hn1.isSubnormal

theorem le_iSup_map_of_isPerfect {π : H →* T} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center H) {a : MulAut H} {β : MulAut T}
    (hπa : ∀ x, π (a x) = β (π x)) (hkerfix : ∀ k ∈ π.ker, a k = k) {ι : Type*}
    (B : ι → Subgroup H) (hB : ⁅fixedSub a, fixedSub a⁆ ≤ ⨆ i, B i) {Y : Subgroup T}
    (hY : Y ≤ fixedSub β) (hYp : ⁅Y, Y⁆ = Y) : Y ≤ ⨆ i, (B i).map π := by
  set Yt : Subgroup H := Y.comap π with hYt
  have hmapYt : Yt.map π = Y := Subgroup.map_comap_eq_self_of_surjective hπ Y
  have hcomm : ⁅Yt, Yt⁆ ≤ fixedSub a := by
    refine Subgroup.commutator_le.mpr fun u hu v hv => ?_
    obtain ⟨z₁, hz₁, hu'⟩ := exists_central_of_fixed hker hπa (G₀ := u) (hY (hu : π u ∈ Y))
    obtain ⟨z₂, hz₂, hv'⟩ := exists_central_of_fixed hker hπa (G₀ := v) (hY (hv : π v ∈ Y))
    change a ⁅u, v⁆ = ⁅u, v⁆
    rw [map_commutatorElement, hu', hv', commutator_mul_central_left hz₁,
      commutator_mul_central_right hz₂]
  have hdecomp : ∀ u ∈ Yt, ∃ c ∈ ⁅Yt, Yt⁆, ∃ k ∈ π.ker, u = c * k := by
    intro u hu
    have : π u ∈ (⁅Yt, Yt⁆).map π := by
      rw [Subgroup.map_commutator, hmapYt, hYp]
      exact hu
    obtain ⟨c, hc, hcu⟩ := Subgroup.mem_map.mp this
    exact ⟨c, hc, c⁻¹ * u, by rw [MonoidHom.mem_ker, map_mul, map_inv, hcu, inv_mul_cancel],
      by group⟩
  have hYtfix : Yt ≤ fixedSub a := by
    intro u hu
    obtain ⟨c, hc, k, hk, rfl⟩ := hdecomp u hu
    change a (c * k) = c * k
    rw [map_mul, hkerfix k hk]
    exact congrArg (· * k) (hcomm hc)
  have h1 : ⁅Yt, Yt⁆ ≤ ⨆ i, B i := (Subgroup.commutator_mono hYtfix hYtfix).trans hB
  calc Y = ⁅Y, Y⁆ := hYp.symm
    _ = (⁅Yt, Yt⁆).map π := by rw [Subgroup.map_commutator, hmapYt]
    _ ≤ (⨆ i, B i).map π := Subgroup.map_mono h1
    _ = ⨆ i, (B i).map π := Subgroup.map_iSup _ _

end Block

end CFSG.RankThree.PartOne.S15K
