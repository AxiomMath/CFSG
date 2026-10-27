module

public import CFSG.RankThree.PartOne.KE.CTMain
public import CFSG.RankThree.PartOne.KE.CTCasesE6Twelve
public import CFSG.RankThree.PartOne.KE.CTCasesE6Nine
public import CFSG.Monster.B.Geometry.CoxeterWords

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne.KE
open CFSG.RankThree.Chevalley (exhaustionPhi)

theorem not_commute_of_cyclicSylow {C : Type} [Group C] {p n₀ d : ℕ}
    (h : CyclicSylowConclusion' C p n₀ d) (h3 : ¬ 3 ∣ n₀) {x y : C} (hx : orderOf x = p)
    (hy : orderOf y = 3) : x * y ≠ y * x := by
  obtain ⟨T, -, hTn, -, -, -, -, hcent⟩ := h
  obtain ⟨g, -, hgc⟩ := hcent x hx
  intro hxy
  have hyc : g * y * g⁻¹ ∈ Subgroup.centralizer {g * x * g⁻¹} := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
      _ = g * (y * x) * g⁻¹ := by rw [hxy]
      _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group
  rw [hgc] at hyc
  have h1 := Subgroup.orderOf_dvd_natCard T hyc
  rw [show orderOf (g * y * g⁻¹) = orderOf y from
    orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y, hy] at h1
  exact h3 (h1.trans hTn)


theorem E6_two_not_commute_order_thirteen {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {R : Type} [Group R] (e : R ≃* adjointGroup .E6 K) {x y : R} (hx : orderOf x = 13)
    (hy : orderOf y = 3) : x * y ≠ y * x := fun hxy =>
  not_commute_of_cyclicSylow (x := e x) (y := e y)
    (E6_twelve_cyclic_sylow cyclic_torus_prime_centralizers K (p := 13) (by norm_num)
      (by norm_num) (by rw [hK]; norm_num [exhaustionPhi])).2.2 (by rw [hK]; norm_num)
    (by rw [← hx]; exact orderOf_injective e.toMonoidHom e.injective x)
    (by rw [← hy]; exact orderOf_injective e.toMonoidHom e.injective y)
    (by rw [← map_mul, ← map_mul, hxy])

theorem E6_two_not_commute_order_seventy_three {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {R : Type} [Group R] (e : R ≃* adjointGroup .E6 K) {x y : R}
    (hx : orderOf x = 73) (hy : orderOf y = 3) : x * y ≠ y * x := fun hxy =>
  not_commute_of_cyclicSylow (x := e x) (y := e y)
    (E6_nine_cyclic_sylow cyclic_torus_prime_centralizers K (p := 73) (by norm_num)
      (by norm_num) (by rw [hK]; norm_num [exhaustionPhi])).2.2 (by rw [hK]; norm_num)
    (by rw [← hx]; exact orderOf_injective e.toMonoidHom e.injective x)
    (by rw [← hy]; exact orderOf_injective e.toMonoidHom e.injective y)
    (by rw [← map_mul, ← map_mul, hxy])

end CFSG.StandardType.SCFourCover

end
