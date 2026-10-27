module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec14.Item1411
public import CFSG.RankThree.PartTwo.Sec14.LBNatural
public import CFSG.RankThree.PartTwo.Sec15.HypR

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Late

theorem exists_fixed_of_cube_eq_id {α : Type*} [Finite α] (f : α → α)
    (hf : ∀ a, f (f (f a)) = a) (hcard : ¬ 3 ∣ Nat.card α) : ∃ a, f a = a := by
  classical
  have := Fintype.ofFinite α
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let σ : Equiv.Perm α :=
    { toFun := f, invFun := fun a => f (f a), left_inv := hf, right_inv := hf }
  have hσ : σ ^ 3 ^ 1 = 1 := by
    ext a
    simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.coe_mul, Function.comp_apply,
      Equiv.Perm.coe_one, id_eq]
    exact hf a
  rw [Nat.card_eq_fintype_card] at hcard
  exact Equiv.Perm.exists_fixed_point_of_prime hcard hσ

section Orbit

variable {G : Type*} [Group G]

open scoped Pointwise in
theorem ncard_conj_dvd [Finite G] (X Q : Subgroup G) :
    {R : Subgroup G | ∃ x ∈ X, R = Q.map (MulAut.conj x).toMonoidHom}.ncard ∣ Nat.card X := by
  let _ : MulAction X (Subgroup G) :=
    MulAction.compHom (Subgroup G) ((MulAut.conj : G →* MulAut G).comp X.subtype)
  have hsmul : ∀ (x : X) (R : Subgroup G), x • R = R.map (MulAut.conj (x : G)).toMonoidHom :=
    fun _ _ => rfl
  have horb : MulAction.orbit X Q =
      {R : Subgroup G | ∃ x ∈ X, R = Q.map (MulAut.conj x).toMonoidHom} := by
    ext R
    simp only [MulAction.mem_orbit_iff, hsmul, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← horb, ← MulAction.index_stabilizer]
  exact Subgroup.index_dvd_card _

theorem mem_normalizer_of_map_conj_eq' {Q : Subgroup G} {g : G}
    (h : Q.map (MulAut.conj g).toMonoidHom = Q) : g ∈ Subgroup.normalizer (Q : Set G) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mpr h

theorem map_conj_mul (Q : Subgroup G) (x y : G) :
    Q.map (MulAut.conj (x * y)).toMonoidHom =
      (Q.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom :=
  (map_conj_map_conj Q x y).symm

theorem inv_mul_mem_normalizer_of_map_conj_eq {Q : Subgroup G} {x y : G}
    (h : Q.map (MulAut.conj x).toMonoidHom = Q.map (MulAut.conj y).toMonoidHom) :
    x⁻¹ * y ∈ Subgroup.normalizer (Q : Set G) := by
  refine mem_normalizer_of_map_conj_eq' ?_
  rw [map_conj_mul, ← h, ← map_conj_mul, inv_mul_cancel, map_conj_one]

theorem conj_mem_normalizer_of_mem_normalizer_map {Q : Subgroup G} {g x : G}
    (h : g ∈ Subgroup.normalizer ((Q.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G)) :
    x⁻¹ * g * x ∈ Subgroup.normalizer (Q : Set G) := by
  refine mem_normalizer_of_map_conj_eq' ?_
  have hg := Late.map_conj_eq_of_mem_normalizer h
  calc Q.map (MulAut.conj (x⁻¹ * g * x)).toMonoidHom =
        ((Q.map (MulAut.conj x).toMonoidHom).map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj x⁻¹).toMonoidHom := by
        rw [map_conj_map_conj, map_conj_map_conj, mul_assoc]
    _ = Q := by rw [hg, map_conj_map_conj, inv_mul_cancel, map_conj_one]

end Orbit

section Glauberman

variable {G : Type*} [Group G] [Finite G]

theorem exists_commute_conj_eq {X Q : Subgroup G} {w x : G} (hw3 : w ^ 3 = 1)
    (hwX : w ∈ Subgroup.normalizer (X : Set G)) (hX3 : ¬ 3 ∣ Nat.card X)
    (hwQ : w ∈ Subgroup.normalizer (Q : Set G)) (hx : x ∈ X)
    (hwQx : w ∈ Subgroup.normalizer ((Q.map (MulAut.conj x).toMonoidHom : Subgroup G) :
      Set G)) :
    ∃ y ∈ X, y * w = w * y ∧ Q.map (MulAut.conj y).toMonoidHom =
      Q.map (MulAut.conj x).toMonoidHom := by
  set C := {y : G // y ∈ X ∧ Q.map (MulAut.conj y).toMonoidHom =
    Q.map (MulAut.conj x).toMonoidHom} with hCdef
  have hQw : Q.map (MulAut.conj w).toMonoidHom = Q := Late.map_conj_eq_of_mem_normalizer hwQ
  have hQw' : Q.map (MulAut.conj w⁻¹).toMonoidHom = Q :=
    Late.map_conj_eq_of_mem_normalizer (inv_mem hwQ)
  have hQxw : (Q.map (MulAut.conj x).toMonoidHom).map (MulAut.conj w).toMonoidHom =
      Q.map (MulAut.conj x).toMonoidHom := Late.map_conj_eq_of_mem_normalizer hwQx
  have hmem : ∀ y : C, w * (y : G) * w⁻¹ ∈ X ∧
      Q.map (MulAut.conj (w * (y : G) * w⁻¹)).toMonoidHom =
        Q.map (MulAut.conj x).toMonoidHom := by
    intro y
    refine ⟨(Subgroup.mem_normalizer_iff.mp hwX y).mp y.2.1, ?_⟩
    rw [map_conj_mul, map_conj_mul, hQw', y.2.2, hQxw]
  let f : C → C := fun y => ⟨w * y * w⁻¹, hmem y⟩
  have hw3' : w * w * w = 1 := by rw [← hw3, pow_three, mul_assoc]
  have hf : ∀ y, f (f (f y)) = y := by
    intro y
    apply Subtype.ext
    change w * (w * (w * (y : G) * w⁻¹) * w⁻¹) * w⁻¹ = y
    calc w * (w * (w * (y : G) * w⁻¹) * w⁻¹) * w⁻¹ = (w * w * w) * y * (w * w * w)⁻¹ := by
          group
      _ = y := by rw [hw3']; group
  have hcard : Nat.card C = Nat.card (X ⊓ Subgroup.normalizer (Q : Set G) : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun y => ⟨x⁻¹ * y, X.mul_mem (X.inv_mem hx) y.2.1,
          inv_mul_mem_normalizer_of_map_conj_eq y.2.2.symm⟩
        invFun := fun n => ⟨x * n, X.mul_mem hx n.2.1, ?_⟩
        left_inv := fun y => Subtype.ext (by simp)
        right_inv := fun n => Subtype.ext (by simp) }
    rw [map_conj_mul, Late.map_conj_eq_of_mem_normalizer n.2.2]
  have hC3 : ¬ 3 ∣ Nat.card C := by
    rw [hcard]
    exact fun h3 => hX3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  obtain ⟨y, hy⟩ := exists_fixed_of_cube_eq_id f hf hC3
  have hy' : w * (y : G) * w⁻¹ = y := congrArg Subtype.val hy
  refine ⟨y, y.2.1, ?_, y.2.2⟩
  calc (y : G) * w = (w * (y : G) * w⁻¹) * w := by rw [hy']
    _ = w * y := by group

end Glauberman

section Data

variable {G : Type} [Group G] [Finite G]

theorem map_conj_mem_qStarTop {A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) {π : Set Nat.Primes} {Q : Subgroup G}
    (hQ : Q ∈ scriptQPiStar A (lB A) ⊤ π) :
    Q.map (MulAut.conj g).toMonoidHom ∈ scriptQPiStar A (lB A) ⊤ π :=
  maximal_map_conj (W := Subgroup.normalizer (A : Set G))
    (fun _ hS _ hw => map_conj_mem_scriptQPi_top (isNaturalFamily_lB A) hw hS) hQ hg

theorem Sec15R.centralizer_le_normalizer_L {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (h3 : 3 ∣ Nat.card L) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro g hg
  have hgc : (MulAut.conj g) c = c := by
    rw [MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
  have hLg : L.map (MulAut.conj g).toMonoidHom ∈ thetaComponentsAt 3 c := by
    have := map_mem_thetaComponentsAt (MulAut.conj g) h.mem_lA.1
    rwa [hgc] at this
  have h3' : 3 ∣ Nat.card (L.map (MulAut.conj g).toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have heq := (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).2 _ hLg h3'
  exact mem_normalizer_of_map_conj_eq' heq

end Data

end CFSG.RankThree.PartTwo.Sec17
