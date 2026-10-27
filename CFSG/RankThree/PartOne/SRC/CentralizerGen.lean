module

public import CFSG.RankThree.PartOne.SRC.Centralizer

public section

namespace CFSG.RankThree.PartOne.SRC

open Subgroup

theorem rankFourCover_of_cover_ker {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X S : Type} [Group X]
    [Finite X] [Group S]
    (hX : ∀ (W : Type) [Group W] [Finite W] (ρ : W →* X), Function.Surjective ρ →
      IsPGroup p ρ.ker → ∃ (E : Subgroup W) (k : ℕ), 4 ≤ k ∧ IsElementaryAbelian p E ∧
        Nat.card E = p ^ k)
    (ι : X →* S) (hker : ∀ A, ι A = 1 → A ^ 2 = 1) {t : S} (ht : orderOf t = 2)
    (hc : ∀ g, ι g * t = t * ι g) : RankFourCover p S := by
  classical
  intro Y _ _ φ hφ hkerφ
  obtain ⟨t', ht'2, hφt'⟩ := exists_involution_lift φ hp hp2 hkerφ ht (hφ t)
  set W : Subgroup Y := Subgroup.centralizer ({t'} : Set Y) ⊓ ι.range.comap φ with hW
  let Wt : Subgroup (W × X) :=
    MonoidHom.eqLocus (φ.comp (W.subtype.comp (MonoidHom.fst W X))) (ι.comp (MonoidHom.snd W X))
  let ρ : Wt →* X := (MonoidHom.snd W X).comp Wt.subtype
  have hρs : Function.Surjective ρ := by
    intro g
    obtain ⟨y, hy, hyφ⟩ := exists_mem_centralizer_lift φ hp hp2 hkerφ ht'2 (hφ (ι g))
      (by rw [hφt']; exact hc g)
    have hyW : y ∈ W := ⟨hy, ⟨g, hyφ.symm⟩⟩
    exact ⟨⟨(⟨y, hyW⟩, g), hyφ⟩, rfl⟩
  have hρker : IsPGroup p ρ.ker := by
    intro x
    have hx1 : (x : W × X).2 = 1 := MonoidHom.mem_ker.mp x.2
    have hx2 : φ (((x : W × X).1 : W) : Y) = 1 := by
      have := x.1.2
      change φ (((x : W × X).1 : W) : Y) = ι (x : W × X).2 at this
      rw [this, hx1, map_one]
    obtain ⟨k, hk⟩ := hkerφ ⟨(((x : W × X).1 : W) : Y), hx2⟩
    refine ⟨k, Subtype.ext (Subtype.ext (Prod.ext ?_ ?_))⟩
    · have := congrArg (fun z : φ.ker => (z : Y)) hk
      exact Subtype.ext (by simpa using this)
    · simp [Prod.pow_snd, hx1]
  obtain ⟨E, k, hk, hE, hcard⟩ := hX Wt ρ hρs hρker
  let g : Wt →* Y := W.subtype.comp ((MonoidHom.fst W X).comp Wt.subtype)
  have hEp : IsPGroup p E := IsElementaryAbelian.isPGroup p E
  have hinj : Function.Injective (g.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hw : (((x : Wt) : W × X).1 : W) = 1 := Subtype.ext hx
    have hmem := (x : Wt).2
    change φ (((((x : Wt) : W × X).1 : W)) : Y) = ι ((x : Wt) : W × X).2 at hmem
    rw [hw] at hmem
    have hA1 : ι ((x : Wt) : W × X).2 = 1 := by
      rw [← hmem]; simp
    have hA2 := hker _ hA1
    obtain ⟨j, hj⟩ := hEp x
    have hj' : ((x : Wt) : W × X) ^ (p ^ j) = 1 := by
      simpa using congrArg (fun z : Wt => (z : W × X)) (congrArg Subtype.val hj)
    have hAj : (((x : Wt) : W × X).2) ^ (p ^ j) = 1 := by
      have := congrArg Prod.snd hj'
      simpa [Prod.pow_snd] using this
    obtain ⟨m, hm⟩ := (hp.eq_two_or_odd'.resolve_left hp2).pow (n := j)
    have hA : ((x : Wt) : W × X).2 = 1 := by
      rw [hm, pow_succ, pow_mul, hA2, one_pow, one_mul] at hAj
      exact hAj
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hw hA
  have hmap : E.map g = (g.comp E.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have ht'1 : t' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht'2
    omega
  refine ⟨Subgroup.zpowers t', E.map g, k, ?_, ?_, isElementaryAbelian_map' g hE, hk, ?_, ?_⟩
  · intro h
    exact ht'1 (by simpa using (Subgroup.zpowers_eq_bot.mp h))
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht'2]; simp)
  · rw [hmap, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hcard]
  · intro x hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
    have hxc : (g w) ∈ Subgroup.centralizer ((Subgroup.zpowers t' : Subgroup Y) : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hcw : t' * (g w) = (g w) * t' :=
        (Subgroup.mem_centralizer_singleton_iff.mp
          (((w : Wt) : W × X).1.2.1)).symm
      exact ((Commute.zpow_left (show Commute t' (g w) from hcw) m).eq)
    exact Subgroup.centralizer_le_normalizer _ hxc

end CFSG.RankThree.PartOne.SRC
