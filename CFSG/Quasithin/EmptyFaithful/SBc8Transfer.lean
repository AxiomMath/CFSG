module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin

namespace SBc8

section Averaging

private theorem exists_coboundary_of_odd_index {X A : Type} [Group X] [Finite X] [Group A]
    [Finite A] (hAc : ∀ a b : A, a * b = b * a) (hA2 : IsPGroup 2 A) (act : X → A →* A)
    {P : Subgroup X} (hodd : ¬ 2 ∣ P.index) (δ : X → A)
    (hδ : ∀ x y : X, δ (x * y) = act x (δ y) * δ x) (hP : ∀ p ∈ P, δ p = 1) :
    ∃ m : A, ∀ x : X, δ x = act x m * m⁻¹ := by
  classical
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA2
  have hcop : (Nat.card A).Coprime P.index := by
    rw [hk]
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).pow_left k
  let _ : CommGroup A := { ‹Group A› with mul_comm := hAc }
  have : Fintype (X ⧸ P) := Fintype.ofFinite _
  have hcard : Fintype.card (X ⧸ P) = P.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hcoset : ∀ x p : X, p ∈ P → δ (x * p) = δ x := fun x p hp => by
    rw [hδ, hP p hp, map_one, one_mul]
  have hperm : ∀ g : X, ∏ i : X ⧸ P, δ (g * i.out) = ∏ i : X ⧸ P, δ i.out := by
    intro g
    have h1 : ∀ i : X ⧸ P, δ (g * i.out) = δ (g • i).out := fun i => by
      have hq : (QuotientGroup.mk (g • i).out : X ⧸ P) = QuotientGroup.mk (g * i.out) := by
        rw [QuotientGroup.out_eq', ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
      calc δ (g * i.out)
          = δ ((g • i).out * ((g • i).out⁻¹ * (g * i.out))) := by rw [mul_inv_cancel_left]
        _ = δ (g • i).out := hcoset _ _ (QuotientGroup.eq.mp hq)
    simp_rw [h1]
    exact Equiv.prod_comp (MulAction.toPerm g) (fun i : X ⧸ P => δ i.out)
  set m₀ : A := ∏ i : X ⧸ P, δ i.out with hm₀
  have hconj : ∀ g : X, act g m₀ * δ g ^ P.index = m₀ := by
    intro g
    have h2 : act g m₀ = ∏ i : X ⧸ P, (δ (g * i.out) * (δ g)⁻¹) := by
      rw [hm₀, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hδ g i.out, mul_inv_cancel_right]
    rw [h2, Finset.prod_mul_distrib, hperm g, Finset.prod_const, Finset.card_univ, hcard, inv_pow,
      inv_mul_cancel_right]
  obtain ⟨m, hm⟩ := (powCoprime hcop).surjective m₀⁻¹
  rw [powCoprime_apply] at hm
  refine ⟨m, fun x => (powCoprime hcop).injective ?_⟩
  have h3 : (act x m * m⁻¹) ^ P.index = (act x m₀)⁻¹ * m₀ := by
    rw [mul_pow, inv_pow, ← map_pow, hm, map_inv, inv_inv]
  rw [powCoprime_apply, powCoprime_apply, h3]
  exact eq_inv_mul_of_mul_eq (hconj x)

end Averaging

section Covering

theorem exists_mul_centralizer_of_cocycle {G : Type} [Group G] [Finite G] {L P W : Subgroup G}
    {d : G} (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hW2 : IsPGroup 2 ↥W)
    (hPL : P ≤ L) (hodd : ¬ 2 ∣ P.relIndex L)
    (hdW : ∀ w ∈ W, d * w * d⁻¹ = w)
    (hd : ∀ l ∈ L, l * d * l⁻¹ * d⁻¹ ∈ W)
    (hP : ∀ p ∈ P, p * d * p⁻¹ * d⁻¹ = 1) :
    ∃ m ∈ W, ∀ l ∈ L, l * (d * m⁻¹) * l⁻¹ = d * m⁻¹ := by
  have _ := hPL
  have hconjW : ∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W := fun l hl w hw =>
    (Subgroup.mem_set_normalizer_iff.mp (hLW hl) w).mp hw
  obtain ⟨m, hm⟩ := exists_coboundary_of_odd_index (X := ↥L) (A := ↥W) (P := P.subgroupOf L)
    (fun a b => Subtype.ext (hWc a a.2 b b.2)) hW2
    (fun l => MonoidHom.mk' (fun w : ↥W => (⟨(l : G) * w * (l : G)⁻¹, hconjW l l.2 w w.2⟩ : ↥W))
      (fun a b => Subtype.ext (by simp [mul_assoc]))) hodd
    (fun l => ⟨(l : G) * d * (l : G)⁻¹ * d⁻¹, hd l l.2⟩)
    (fun x y => Subtype.ext (by simp; group))
    (fun p hp => Subtype.ext (hP p (Subgroup.mem_subgroupOf.mp hp)))
  refine ⟨m, m.2, fun l hl => ?_⟩
  have key : l * d * l⁻¹ * d⁻¹ = l * m * l⁻¹ * (m : G)⁻¹ := congrArg Subtype.val (hm ⟨l, hl⟩)
  have hw : l * m * l⁻¹ ∈ W := hconjW l hl m m.2
  have hdw : d * (l * m * l⁻¹)⁻¹ = (l * m * l⁻¹)⁻¹ * d :=
    mul_inv_eq_iff_eq_mul.mp (hdW _ (W.inv_mem hw))
  have hdm : d * (m : G)⁻¹ = (m : G)⁻¹ * d := mul_inv_eq_iff_eq_mul.mp (hdW _ (W.inv_mem m.2))
  have hwm : l * m * l⁻¹ * (m : G)⁻¹ = (m : G)⁻¹ * (l * m * l⁻¹) :=
    hWc _ hw _ (W.inv_mem m.2)
  calc l * (d * (m : G)⁻¹) * l⁻¹
      = (l * d * l⁻¹ * d⁻¹) * (d * (l * m * l⁻¹)⁻¹) := by group
    _ = (l * m * l⁻¹ * (m : G)⁻¹) * ((l * m * l⁻¹)⁻¹ * d) := by rw [key, hdw]
    _ = ((m : G)⁻¹ * (l * m * l⁻¹)) * ((l * m * l⁻¹)⁻¹ * d) := by rw [hwm]
    _ = (m : G)⁻¹ * d := by group
    _ = d * (m : G)⁻¹ := hdm.symm

end Covering

end SBc8

end CFSG.Quasithin
