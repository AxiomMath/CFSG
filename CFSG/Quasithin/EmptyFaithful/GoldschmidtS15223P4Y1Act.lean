module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4Y1Cnt
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4D1Norm

public section

namespace CFSG.Quasithin.S15223P4.Y1

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

theorem exists_autOn_eq_zpowers (c : P4Ctx T Mc M H B₀ I X) (hN : D1.P4N1 T Mc M H B₀ I X)
    (h3 : IsThreePrimeGroup (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G))) :
    ∃ e : MulAut ↥(V154 T Mc M), orderOf e = 3 ∧
      autOn (oPrimeResidualOf 3 (M ⊓ I)) (V154 T Mc M) = Subgroup.zpowers e := by
  obtain ⟨y, hy, hyo⟩ := exists_orderOf_three hN
  have hMV := le_normalizer_V154 T Mc M
  set ρ := A4.actionOn (V154 T Mc M) M hMV with hρ
  have hy3 : y ^ 3 = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hyo; omega
  have hyN : y ∈ M ⊓ I := ⟨hy.2, c.X_le_I hy.1⟩
  have hρy : ρ ⟨y, hy.2⟩ ≠ 1 := D1.actionOn_ne_one c hN.toP4N1pre hy hy3 hy1
  have hρy3 : ρ ⟨y, hy.2⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, hy.2⟩ : ↥M) ^ 3 = 1 := Subtype.ext hy3
    rw [this, map_one]
  refine ⟨ρ ⟨y, hy.2⟩, orderOf_eq_prime hρy3 hρy, le_antisymm ?_ ?_⟩
  · set W : Subgroup G := ((Subgroup.zpowers (ρ ⟨y, hy.2⟩)).comap ρ).map M.subtype with hW
    have hYW : oPrimeResidualOf 3 (M ⊓ I) ≤ W := by
      refine oPrimeResidualOf_le_of_forall fun x hx k hk => ?_
      have hx3 := pow_three_of_orderOf c hN (mem_inf_of_orderOf c hN h3 hx hk) hk
      obtain ⟨j, hj⟩ := D1.exists_zpow_of_cube c hyN hx hy3 hx3 hρy
      exact ⟨⟨x, hx.1⟩, Subgroup.mem_comap.mpr (Subgroup.mem_zpowers_iff.mpr ⟨j, hj.symm⟩), rfl⟩
    intro a ha
    obtain ⟨x, hxn, hxY, rfl⟩ := mem_autOn_iff_exists.mp ha
    obtain ⟨m, hm, hmx⟩ := hYW hxY
    subst hmx
    exact hm
  · rw [Subgroup.zpowers_le]
    exact mem_autOn_of_mem (hMV hy.2)
      (mem_oPrimeResidualOf_three hyN (k := 1) (by rw [hyo, pow_one]))

theorem mem_S_of_mem_centralizer (c : P4Ctx T Mc M H B₀ I X) (hN : D1.P4N1 T Mc M H B₀ I X)
    (h3 : IsThreePrimeGroup (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G))) {g : G}
    (hg : g ∈ oPrimeResidualOf 3 (M ⊓ I) ⊔ sOf152 T Mc M B₀)
    (hgC : g ∈ Subgroup.centralizer (V154 T Mc M : Set G)) : g ∈ sOf152 T Mc M B₀ := by
  obtain ⟨e, he3, hYe⟩ := exists_autOn_eq_zpowers c hN h3
  have hMV := le_normalizer_V154 T Mc M
  set ρ := A4.actionOn (V154 T Mc M) M hMV with hρ
  have hSN : sOf152 T Mc M B₀ ≤ M ⊓ I := c.S_le_N
  obtain ⟨y, hyY, s, hsS, rfl⟩ := (mem_sup_iff_of_le_normalizer (S_le_normalizer c)).mp hg
  have hYXM : y ∈ X ⊓ M := oPrimeResidualOf_le_inf c hN h3 hyY
  have hyM : y ∈ M := hYXM.2
  have hsM : s ∈ M := (hSN hsS).1
  have hρg : ρ ⟨y * s, M.mul_mem hyM hsM⟩ = 1 := (A4.actionOn_eq_one_iff hMV _).mpr hgC
  have hρy : ρ ⟨y, hyM⟩ = (ρ ⟨s, hsM⟩)⁻¹ := by
    have : ρ ⟨y, hyM⟩ * ρ ⟨s, hsM⟩ = 1 := by rw [← map_mul]; exact hρg
    exact eq_inv_of_mul_eq_one_left this
  have hmem : ρ ⟨y, hyM⟩ ∈ Subgroup.zpowers e := by
    rw [← hYe]
    exact mem_autOn_of_mem (hMV hyM) hyY
  have h3y : ρ ⟨y, hyM⟩ ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have he : e ^ 3 = 1 := he3 ▸ pow_orderOf_eq_one e
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he, one_zpow]
  obtain ⟨j, hj⟩ := c.sylow.isPGroup ⟨s, hsS⟩
  have hsj : (⟨s, hsM⟩ : ↥M) ^ 2 ^ j = 1 := Subtype.ext (by simpa using congrArg Subtype.val hj)
  have h2y : ρ ⟨y, hyM⟩ ^ 2 ^ j = 1 := by
    rw [hρy, inv_pow, ← map_pow, hsj, map_one, inv_one]
  have hρ1 : ρ ⟨y, hyM⟩ = 1 := C1Pack12.eq_one_of_pow_two_pow_of_pow_three' h2y h3y
  have hyC : y ∈ Subgroup.centralizer (V154 T Mc M : Set G) :=
    (A4.actionOn_eq_one_iff hMV ⟨y, hyM⟩).mp hρ1
  have hyS : y ∈ sOf152 T Mc M B₀ ⊓ X := by
    have h1 : y ∈ X ⊓ (Mc ⊓ I) ⊓ (X ⊓ M) :=
      ⟨⟨hYXM.1, cv_le_inf152 c.setting c.inputs ⟨hyM, hyC⟩⟩, hYXM⟩
    rwa [hN.M0_inf_MX] at h1
  exact (sOf152 T Mc M B₀).mul_mem hyS.1 hsS

end CFSG.Quasithin.S15223P4.Y1
