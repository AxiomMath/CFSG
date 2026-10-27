module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin

namespace S1549D

open CFSG.QuasithinUnique

variable {V : Type*} [CommGroup V]

theorem exists_mul_of_fixV_sylow [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {P S : Subgroup (MulAut V)}
    (hS : IsSylowTwoOf S P) {u : V} (hu : ∀ s ∈ S, s u = u) :
    ∃ w ∈ fixV P, ∃ c ∈ Subgroup.closure {x : V | ∃ p ∈ P, p u * u⁻¹ = x}, u = w * c := by
  classical
  set S' : Subgroup ↥P := S.subgroupOf P with hS'
  have : Finite (↥P ⧸ S') := inferInstance
  have : Fintype (↥P ⧸ S') := Fintype.ofFinite _
  let r : (↥P ⧸ S') → ↥P := fun q => Quotient.out q
  let f : (↥P ⧸ S') → V := fun q => ((r q : ↥P) : MulAut V) u
  have hr : ∀ q, ((r q : ↥P) : ↥P ⧸ S') = q := fun q => Quotient.out_eq' q
  have hshift : ∀ (pp : ↥P) (q : ↥P ⧸ S'), (pp : MulAut V) (f q) = f (pp • q) := by
    intro pp q
    have h1 : ((pp * r q : ↥P) : ↥P ⧸ S') = ((r (pp • q) : ↥P) : ↥P ⧸ S') := by
      rw [hr (pp • q)]
      have : pp • (((r q : ↥P) : ↥P ⧸ S')) = ((pp * r q : ↥P) : ↥P ⧸ S') := rfl
      rw [hr q] at this
      exact this.symm
    have h2 : (r (pp • q))⁻¹ * (pp * r q) ∈ S' := QuotientGroup.eq.mp h1.symm
    have h3 : (((r (pp • q))⁻¹ * (pp * r q) : ↥P) : MulAut V) u = u :=
      hu _ (Subgroup.mem_subgroupOf.mp h2)
    show (pp : MulAut V) (((r q : ↥P) : MulAut V) u) = ((r (pp • q) : ↥P) : MulAut V) u
    calc (pp : MulAut V) (((r q : ↥P) : MulAut V) u)
        = ((pp * r q : ↥P) : MulAut V) u := rfl
      _ = ((r (pp • q) * ((r (pp • q))⁻¹ * (pp * r q)) : ↥P) : MulAut V) u := by
          rw [mul_inv_cancel_left]
      _ = ((r (pp • q) : ↥P) : MulAut V) ((((r (pp • q))⁻¹ * (pp * r q) : ↥P) : MulAut V) u) := rfl
      _ = ((r (pp • q) : ↥P) : MulAut V) u := by rw [h3]
  have hcard : Odd (Fintype.card (↥P ⧸ S')) := by
    have h := hS.2.2
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index]
    exact Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using h)
  refine ⟨∏ q, f q, ?_, (∏ q, (f q * u⁻¹))⁻¹, ?_, ?_⟩
  · intro p hp
    have h1 : (p : MulAut V) (∏ q, f q) = ∏ q, f ((⟨p, hp⟩ : ↥P) • q) := by
      rw [map_prod]
      exact Finset.prod_congr rfl fun q _ => hshift ⟨p, hp⟩ q
    rw [h1]
    exact Fintype.prod_equiv (MulAction.toPerm (⟨p, hp⟩ : ↥P)) (fun q => f ((⟨p, hp⟩ : ↥P) • q)) f
      (fun q => rfl)
  · refine Subgroup.inv_mem _ (Subgroup.prod_mem _ fun q _ => ?_)
    exact Subgroup.subset_closure ⟨((r q : ↥P) : MulAut V), (r q).2, rfl⟩
  · obtain ⟨k, hk⟩ := hcard
    have hpow : (u⁻¹) ^ (Fintype.card (↥P ⧸ S')) = u⁻¹ := by
      rw [hk, pow_succ, pow_mul, inv_pow, hV u, inv_one, one_pow, one_mul]
    have h2 : ∏ q, (f q * u⁻¹) = (∏ q, f q) * u⁻¹ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hpow]
    rw [h2, mul_inv_rev, inv_inv, ← mul_assoc, mul_comm (∏ q, f q) u, mul_assoc, mul_inv_cancel,
      mul_one]

theorem fixV_le_commV_sup_fixV [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X S : Subgroup (MulAut V)}
    (hS : IsSylowTwoOf S X) : fixV S ≤ commV X ⊔ fixV X := by
  intro u hu
  obtain ⟨w, hw, c, hc, huc⟩ := exists_mul_of_fixV_sylow hV hS (fun s hs => hu s hs)
  rw [huc]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_right hw) (Subgroup.mem_sup_left ?_)
  refine (Subgroup.closure_le _).mpr ?_ hc
  rintro _ ⟨p, hp, rfl⟩
  exact Subgroup.subset_closure ⟨p, hp, u, rfl⟩

theorem commV_sup_fixV_eq_top [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X S : Subgroup (MulAut V)}
    (hS : IsSylowTwoOf S X) {z : V} (hz : ∀ s ∈ S, s z = z)
    (hgen : Subgroup.closure {v : V | ∃ g ∈ X, g z = v} = ⊤) : commV X ⊔ fixV X = ⊤ := by
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  have hz' : z ∈ commV X ⊔ fixV X := fixV_le_commV_sup_fixV hV hS hz
  have hcomm : g z * z⁻¹ ∈ commV X ⊔ fixV X :=
    Subgroup.mem_sup_left (Subgroup.subset_closure ⟨g, hg, z, rfl⟩)
  have := Subgroup.mul_mem _ hcomm hz'
  rwa [inv_mul_cancel_right] at this

theorem mem_fixV_of_sylow [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {P S : Subgroup (MulAut V)}
    (hS : IsSylowTwoOf S P) {u : V} (hu : ∀ s ∈ S, s u = u) {Z : Subgroup V}
    (hZ : Z ≤ fixV P) (hPu : ∀ p ∈ P, p u * u⁻¹ ∈ Z) : u ∈ fixV P := by
  obtain ⟨w, hw, c, hc, huc⟩ := exists_mul_of_fixV_sylow hV hS hu
  have hcZ : c ∈ Z := (Subgroup.closure_le Z).mpr (by
    rintro _ ⟨p, hp, rfl⟩
    exact hPu p hp) hc
  rw [huc]
  exact Subgroup.mul_mem _ hw (hZ hcZ)

end S1549D

end CFSG.Quasithin
