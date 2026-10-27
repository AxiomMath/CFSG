module

public import CFSG.RankThree.PartOne.SRC.Centralizer

public section

namespace CFSG.RankThree.PartOne.SLBN

open Subgroup CFSG

theorem isCyclic_ker_inf_centralizer {Y S X : Type} [Group Y] [Finite Y] [Group S] [Group X]
    [Finite X] (φ : Y →* S) (hφ : Function.Surjective φ) (hker : IsPGroup 3 φ.ker) (ι : X →* S)
    (hι : ∀ A, ι A = 1 → A ^ 2 = 1) {t : S}
    (hc : ∀ g, ι g * t = t * ι g) {t' : Y} (ht'2 : orderOf t' = 2) (hφt' : φ t' = t)
    (hrank : ∀ E : Subgroup Y, E ≤ Subgroup.centralizer ({t'} : Set Y) →
      IsElementaryAbelian 3 E → Nat.card E ≤ 27)
    (hLL : ∀ (P : Type) [Group P] [Finite P] (ρ : P →* X), Function.Surjective ρ →
      IsPGroup 3 ρ.ker → (∀ E : Subgroup P, IsElementaryAbelian 3 E → Nat.card E ≤ 27) →
        IsCyclic ρ.ker) :
    IsCyclic ↥(φ.ker ⊓ Subgroup.centralizer ({t'} : Set Y)) := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  set W : Subgroup Y := Subgroup.centralizer ({t'} : Set Y) ⊓ ι.range.comap φ with hW
  let Wt : Subgroup (W × X) :=
    MonoidHom.eqLocus (φ.comp (W.subtype.comp (MonoidHom.fst W X))) (ι.comp (MonoidHom.snd W X))
  let ρ : Wt →* X := (MonoidHom.snd W X).comp Wt.subtype
  have hρs : Function.Surjective ρ := by
    intro g
    obtain ⟨y, hy, hyφ⟩ := CFSG.RankThree.PartOne.SRC.exists_mem_centralizer_lift φ hp hp2 hker
      ht'2 (hφ (ι g)) (by rw [hφt']; exact hc g)
    have hyW : y ∈ W := ⟨hy, ⟨g, hyφ.symm⟩⟩
    exact ⟨⟨(⟨y, hyW⟩, g), hyφ⟩, rfl⟩
  have hρker : IsPGroup 3 ρ.ker := by
    intro x
    have hx1 : (x : W × X).2 = 1 := MonoidHom.mem_ker.mp x.2
    have hx2 : φ (((x : W × X).1 : W) : Y) = 1 := by
      have := x.1.2
      change φ (((x : W × X).1 : W) : Y) = ι (x : W × X).2 at this
      rw [this, hx1, map_one]
    obtain ⟨k, hk⟩ := hker ⟨(((x : W × X).1 : W) : Y), hx2⟩
    refine ⟨k, Subtype.ext (Subtype.ext (Prod.ext ?_ ?_))⟩
    · have := congrArg (fun z : φ.ker => (z : Y)) hk
      exact Subtype.ext (by simpa using this)
    · simp [Prod.pow_snd, hx1]
  let g : Wt →* Y := W.subtype.comp ((MonoidHom.fst W X).comp Wt.subtype)
  have hgW : ∀ w : Wt, g w ∈ Subgroup.centralizer ({t'} : Set Y) := fun w => w.1.1.2.1
  have hrankWt : ∀ E : Subgroup Wt, IsElementaryAbelian 3 E → Nat.card E ≤ 27 := by
    intro E hE
    have hEp : IsPGroup 3 E := IsElementaryAbelian.isPGroup 3 E
    have hinj : Function.Injective (g.comp E.subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hw : (((x : Wt) : W × X).1 : W) = 1 := Subtype.ext hx
      have hmem := (x : Wt).2
      change φ (((((x : Wt) : W × X).1 : W)) : Y) = ι ((x : Wt) : W × X).2 at hmem
      rw [hw] at hmem
      have hA1 : ι ((x : Wt) : W × X).2 = 1 := by
        rw [← hmem]; simp
      have hA2 := hι _ hA1
      obtain ⟨j, hj⟩ := hEp x
      have hj' : ((x : Wt) : W × X) ^ (3 ^ j) = 1 := by
        simpa using congrArg (fun z : Wt => (z : W × X)) (congrArg Subtype.val hj)
      have hAj : (((x : Wt) : W × X).2) ^ (3 ^ j) = 1 := by
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
    have hle : E.map g ≤ Subgroup.centralizer ({t'} : Set Y) := by
      rintro _ ⟨w, -, rfl⟩
      exact hgW w
    have := hrank (E.map g) hle (CFSG.RankThree.PartOne.SRC.isElementaryAbelian_map' g hE)
    rwa [hmap, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv] at this
  have hcyc : IsCyclic ρ.ker := hLL Wt ρ hρs hρker hrankWt
  let h : ρ.ker →* ↥(φ.ker ⊓ Subgroup.centralizer ({t'} : Set Y)) :=
    (g.comp ρ.ker.subtype).codRestrict _ (fun x => by
      have hx1 : (x : Wt).1.2 = 1 := MonoidHom.mem_ker.mp x.2
      refine ⟨?_, hgW x⟩
      have := (x : Wt).2
      change φ (((x : Wt) : W × X).1 : W) = ι ((x : Wt) : W × X).2 at this
      show φ (((x : Wt) : W × X).1 : W) = 1
      rw [this, show ((x : Wt) : W × X).2 = 1 from hx1, map_one])
  have hh : Function.Surjective h := by
    rintro ⟨y, hyker, hyC⟩
    have hyW : y ∈ W := ⟨hyC, ⟨1, by rw [map_one]; exact MonoidHom.mem_ker.mp hyker |>.symm⟩⟩
    refine ⟨⟨⟨(⟨y, hyW⟩, 1), ?_⟩, rfl⟩, rfl⟩
    change φ y = ι 1
    rw [map_one]
    exact MonoidHom.mem_ker.mp hyker
  exact isCyclic_of_surjective h hh

end CFSG.RankThree.PartOne.SLBN
