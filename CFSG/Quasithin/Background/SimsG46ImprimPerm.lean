module

public import CFSG.Quasithin.Background.SimsG4Defs
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import CFSG.Quasithin.Background.SimsG4Core

public section

namespace CFSG.Quasithin.SimsG4

namespace G46Imprim

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

noncomputable def sumPerm {r : ℕ} (W : Fin r → Submodule F V) (g : V ≃ₗ[F] V) (i : Fin r) :
    Fin r := by
  classical
  exact if h : ∃ j, (W i).map (g : V →ₗ[F] V) = W j then h.choose else i

section Summands

variable {r : ℕ} {W : Fin r → Submodule F V} {G₀ : Subgroup (V ≃ₗ[F] V)}

theorem summand_injective (hne : ∀ i, W i ≠ ⊥) (hind : iSupIndep W) : Function.Injective W := by
  intro i j hij
  by_contra h
  have hd : Disjoint (W i) (W j) := hind.pairwiseDisjoint h
  rw [hij, disjoint_self] at hd
  exact hne j hd

theorem map_sumPerm (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j)
    {g : V ≃ₗ[F] V} (hg : g ∈ G₀) (i : Fin r) :
    (W i).map (g : V →ₗ[F] V) = W (sumPerm W g i) := by
  have h := hmap g hg i
  unfold sumPerm
  rw [dif_pos h]
  exact h.choose_spec

theorem apply_mem_sumPerm (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j)
    {g : V ≃ₗ[F] V} (hg : g ∈ G₀) {i : Fin r} {x : V} (hx : x ∈ W i) :
    g x ∈ W (sumPerm W g i) := by
  rw [← map_sumPerm hmap hg i]
  exact Submodule.mem_map_of_mem hx

theorem sumPerm_mul (hW : Function.Injective W)
    (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j) {g h : V ≃ₗ[F] V}
    (hg : g ∈ G₀) (hh : h ∈ G₀) (i : Fin r) :
    sumPerm W (g * h) i = sumPerm W g (sumPerm W h i) := by
  apply hW
  rw [← map_sumPerm hmap (G₀.mul_mem hg hh) i, ← map_sumPerm hmap hg (sumPerm W h i),
    ← map_sumPerm hmap hh i, LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp,
    Submodule.map_comp]

theorem sumPerm_one (hW : Function.Injective W)
    (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j) (i : Fin r) :
    sumPerm W 1 i = i := by
  apply hW
  rw [← map_sumPerm hmap G₀.one_mem i, LinearEquiv.coe_toLinearMap_one, Submodule.map_id]

theorem sumPerm_inv_sumPerm (hW : Function.Injective W)
    (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j) {g : V ≃ₗ[F] V}
    (hg : g ∈ G₀) (i : Fin r) : sumPerm W g⁻¹ (sumPerm W g i) = i := by
  rw [← sumPerm_mul hW hmap (G₀.inv_mem hg) hg, inv_mul_cancel, sumPerm_one hW hmap]

theorem sumPerm_sumPerm_inv (hW : Function.Injective W)
    (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j) {g : V ≃ₗ[F] V}
    (hg : g ∈ G₀) (i : Fin r) : sumPerm W g (sumPerm W g⁻¹ i) = i := by
  rw [← sumPerm_mul hW hmap hg (G₀.inv_mem hg), mul_inv_cancel, sumPerm_one hW hmap]

theorem sumPerm_injective (hW : Function.Injective W)
    (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j) {g : V ≃ₗ[F] V}
    (hg : g ∈ G₀) : Function.Injective (sumPerm W g) := fun i j h => by
  rw [← sumPerm_inv_sumPerm hW hmap hg i, h, sumPerm_inv_sumPerm hW hmap hg j]

theorem sumPerm_eq_of_mapsTo (hne : ∀ i, W i ≠ ⊥) (hind : iSupIndep W)
    (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j) {g : V ≃ₗ[F] V}
    (hg : g ∈ G₀) {i j : Fin r} (h : ∀ x ∈ W i, g x ∈ W j) : sumPerm W g i = j := by
  by_contra hij
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne i)
  have hd : Disjoint (W (sumPerm W g i)) (W j) := hind.pairwiseDisjoint hij
  have h0 := Submodule.disjoint_def.mp hd (g x) (apply_mem_sumPerm hmap hg hx) (h x hx)
  exact hx0 ((LinearEquiv.map_eq_zero_iff g).mp h0)

theorem mapsTo_sup_of_sumPerm (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j)
    {g : V ≃ₗ[F] V} (hg : g ∈ G₀) {i j i' j' : Fin r}
    (hi : sumPerm W g i = i' ∨ sumPerm W g i = j') (hj : sumPerm W g j = i' ∨ sumPerm W g j = j') :
    ∀ x ∈ W i ⊔ W j, g x ∈ W i' ⊔ W j' := by
  have key : ∀ k, (sumPerm W g k = i' ∨ sumPerm W g k = j') → ∀ y ∈ W k, g y ∈ W i' ⊔ W j' := by
    intro k hk y hy
    have hgy := apply_mem_sumPerm hmap hg hy
    rcases hk with h | h <;> rw [h] at hgy
    · exact Submodule.mem_sup_left hgy
    · exact Submodule.mem_sup_right hgy
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  exact Submodule.add_mem _ (key i hi y hy) (key j hj z hz)

theorem disjoint_sup_sup_of_ne (hind : iSupIndep W) {p q p' q' : Fin r} (h1 : p ≠ p')
    (h2 : p ≠ q') (h3 : q ≠ p') (h4 : q ≠ q') : Disjoint (W p ⊔ W q) (W p' ⊔ W q') := by
  classical
  have h := (hind.supIndep' Finset.univ).disjoint_sup_sup (Finset.subset_univ {p, q})
    (Finset.subset_univ {p', q'}) (by
      rw [Finset.disjoint_left]
      intro a ha hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all)
  simpa [Finset.sup_insert, Finset.sup_singleton] using h

theorem exists_sumPerm_eq (hirr : IsIrredOnV G₀) (hne : ∀ i, W i ≠ ⊥) (hind : iSupIndep W)
    (htop : (⨆ i, W i) = ⊤) (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j)
    (i j : Fin r) : ∃ g ∈ G₀, sumPerm W g i = j := by
  by_contra hcon
  push Not at hcon
  set U : Submodule F V := Submodule.span F {v | ∃ g ∈ G₀, ∃ x ∈ W i, v = g x} with hU
  have hUinv : ∀ g ∈ G₀, ∀ w ∈ U, g w ∈ U := by
    intro g hg w hw
    induction hw using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨h, hh, x, hx, rfl⟩ := hv
      exact Submodule.subset_span ⟨g * h, G₀.mul_mem hg hh, x, hx, rfl⟩
    | zero => rw [map_zero]; exact U.zero_mem
    | add a b _ _ ha hb => rw [map_add]; exact U.add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact U.smul_mem c ha
  have hWU : W i ≤ U := fun x hx => Submodule.subset_span ⟨1, G₀.one_mem, x, hx, rfl⟩
  have hUtop : U = ⊤ := by
    rcases hirr U hUinv with h | h
    · rw [h] at hWU
      exact absurd (eq_bot_iff.mpr hWU) (hne i)
    · exact h
  have hUle : U ≤ ⨆ (k) (_ : k ≠ j), W k := by
    rw [Submodule.span_le]
    rintro v ⟨g, hg, x, hx, rfl⟩
    exact (le_iSup₂ (f := fun k (_ : k ≠ j) => W k) (sumPerm W g i) (hcon g hg))
      (apply_mem_sumPerm hmap hg hx)
  apply hne j
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hx' : x ∈ ⨆ (k) (_ : k ≠ j), W k := hUle (by rw [hUtop]; exact Submodule.mem_top)
  exact Submodule.disjoint_def.mp (hind j) x hx hx'

theorem finrank_sumPerm (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j)
    {g : V ≃ₗ[F] V} (hg : g ∈ G₀) (i : Fin r) :
    Module.finrank F (W (sumPerm W g i)) = Module.finrank F (W i) := by
  rw [← map_sumPerm hmap hg i, LinearEquiv.finrank_map_eq]

theorem finrank_eq_sum_summands [FiniteDimensional F V] (hind : iSupIndep W)
    (htop : (⨆ i, W i) = ⊤) : Module.finrank F V = ∑ i, Module.finrank F (W i) := by
  classical
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hint).finrank_eq,
    Module.finrank_directSum]

theorem summands_two_or_four [FiniteDimensional F V] (hdim : Module.finrank F V = 4) (hr : 1 < r)
    (hirr : IsIrredOnV G₀) (hne : ∀ i, W i ≠ ⊥) (hind : iSupIndep W) (htop : (⨆ i, W i) = ⊤)
    (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j) :
    (r = 2 ∧ ∀ i, Module.finrank F (W i) = 2) ∨ (r = 4 ∧ ∀ i, Module.finrank F (W i) = 1) := by
  obtain ⟨i₀⟩ : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank F (W i₀) = m := ⟨_, rfl⟩
  have hall : ∀ i, Module.finrank F (W i) = m := by
    intro i
    obtain ⟨g, hg, rfl⟩ := exists_sumPerm_eq hirr hne hind htop hmap i₀ i
    rw [finrank_sumPerm hmap hg i₀, hm]
  have hsum : r * m = 4 := by
    rw [← hdim, finrank_eq_sum_summands hind htop, Finset.sum_congr rfl fun i _ => hall i]
    simp
  have hpos : 0 < m := by
    rw [Nat.pos_iff_ne_zero]
    intro h
    exact hne i₀ (Submodule.finrank_eq_zero.mp (hm.trans h))
  have hm4 : m ≤ 4 := Nat.le_of_dvd (by norm_num) ⟨r, by rw [← hsum, mul_comm]⟩
  interval_cases m
  · exact Or.inr ⟨by omega, hall⟩
  · exact Or.inl ⟨by omega, hall⟩
  · omega
  · omega

end Summands

theorem not_connected_of_two_blocks {G₀ : Subgroup (V ≃ₗ[F] V)} {U₀ U₁ : Submodule F V}
    (hdisj : Disjoint U₀ U₁) (htop : U₀ ⊔ U₁ = ⊤) (hD : (transvSet G₀).Nonempty)
    (hpres : ∀ d ∈ transvSet G₀, (∀ x ∈ U₀, d x ∈ U₀) ∧ ∀ x ∈ U₁, d x ∈ U₁)
    (hcent : ∀ d ∈ transvSet G₀, (∀ x ∈ U₀, d x = x) ∨ ∀ x ∈ U₁, d x = x)
    {g : V ≃ₗ[F] V} (hg : g ∈ G₀) (hg₀ : ∀ x ∈ U₀, g x ∈ U₁) (hg₁ : ∀ x ∈ U₁, g x ∈ U₀) :
    ¬ (advGraph G₀).Connected := by
  have hsum : ∀ v : V, ∃ x₀ ∈ U₀, ∃ x₁ ∈ U₁, x₀ + x₁ = v := fun v =>
    Submodule.mem_sup.mp (by rw [htop]; exact Submodule.mem_top)
  let S₀ : Set (V ≃ₗ[F] V) := {d | d ∈ transvSet G₀ ∧ ∀ x ∈ U₁, d x = x}
  let S₁ : Set (V ≃ₗ[F] V) := {d | d ∈ transvSet G₀ ∧ ∀ x ∈ U₀, d x = x}
  have hcomm : ∀ a ∈ S₀, ∀ b ∈ S₁, a * b = b * a := by
    rintro a ⟨ha, ha₁⟩ b ⟨hb, hb₀⟩
    apply LinearEquiv.ext
    intro v
    obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := hsum v
    simp only [LinearEquiv.mul_apply, map_add]
    rw [hb₀ x₀ hx₀, ha₁ x₁ hx₁, ha₁ _ ((hpres b hb).2 x₁ hx₁), hb₀ _ ((hpres a ha).1 x₀ hx₀)]
  have hdisjS : ∀ d ∈ S₀, d ∉ S₁ := by
    rintro d ⟨hd, hd₁⟩ ⟨-, hd₀⟩
    apply transv_ne_one d hd.2
    apply LinearEquiv.ext
    intro v
    obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := hsum v
    rw [map_add, hd₀ x₀ hx₀, hd₁ x₁ hx₁]
    rfl
  have hconj : ∀ e ∈ transvSet G₀, g⁻¹ * e * g ∈ transvSet G₀ := fun e he => by
    simpa only [inv_inv] using conj_mem_transvSet (G₀.inv_mem hg) he
  obtain ⟨d, hd⟩ := hD
  obtain ⟨⟨a, haD, ha₁⟩, ⟨b, hbD, hb₀⟩⟩ : S₀.Nonempty ∧ S₁.Nonempty := by
    rcases hcent d hd with h₀ | h₁
    · refine ⟨⟨g⁻¹ * d * g, hconj d hd, fun x hx => ?_⟩, ⟨d, hd, h₀⟩⟩
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, h₀ _ (hg₁ x hx), inv_mul_apply]
    · refine ⟨⟨d, hd, h₁⟩, ⟨g⁻¹ * d * g, hconj d hd, fun x hx => ?_⟩⟩
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, h₁ _ (hg₀ x hx), inv_mul_apply]
  intro hconn
  have key : ∀ y : ↥(transvSet G₀), (advGraph G₀).Reachable ⟨a, haD⟩ y →
      (y : V ≃ₗ[F] V) ∈ S₀ := by
    intro y hy
    rw [SimpleGraph.reachable_iff_reflTransGen] at hy
    induction hy with
    | refl => exact ⟨haD, ha₁⟩
    | @tail c e _ hadj ih =>
      simp only [advGraph, SimpleGraph.fromRel_adj] at hadj
      by_contra he
      have he₁ : (e : V ≃ₗ[F] V) ∈ S₁ := by
        rcases hcent e e.2 with h | h
        · exact ⟨e.2, h⟩
        · exact absurd ⟨e.2, h⟩ he
      have hce := hcomm c ih e he₁
      rcases hadj with ⟨-, h | h⟩
      · exact h hce
      · exact h hce.symm
  exact hdisjS b (key ⟨b, hbD⟩ (hconn.preconnected _ _)) ⟨hbD, hb₀⟩

end G46Imprim

end CFSG.Quasithin.SimsG4
