module

public import CFSG.RankThree.PartTwo.Sec11.Steps
public import CFSG.RankThree.PartTwo.Sec12.SylowIndependence

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

private theorem map_conj_map_conj {G : Type*} [Group G] (X : Subgroup G) (g x : G) :
    (X.map (MulAut.conj x).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      X.map (MulAut.conj (g * x)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem item114_of (h113 : Item113) : Item114 := by
  intro G _ _ A c L a R Y h g hg
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hAΩ, -⟩ := h113 G A c L a R Y h
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hexp : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set A' := A.map (MulAut.conj g⁻¹).toMonoidHom with hA'
  have hgc : g * c * g⁻¹ ∈ A := hg ⟨c, Subgroup.mem_zpowers c, rfl⟩
  have hA'C : ∀ y' ∈ A', y' * c = c * y' := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := hcomm y hy _ hgc
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * y * g * c = g⁻¹ * (y * (g * c * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * c * g⁻¹) * y) * g := by rw [h1]
      _ = c * (g⁻¹ * y * g) := by group
  have hA'H : A' ≤ H := fun y' hy' => by
    have hc' : Commute y' c := hA'C y' hy'
    rw [hH, Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [(hc'.zpow_right k).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers c k
    · intro hz
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
      have e : z = c ^ k := by
        calc z = y'⁻¹ * (y' * z * y'⁻¹) * y' := by group
          _ = y'⁻¹ * c ^ k * y' := by rw [← hk]
          _ = y'⁻¹ * (y' * c ^ k) := by rw [mul_assoc, ← (hc'.zpow_right k).eq]
          _ = c ^ k := by group
      rw [e]
      exact Subgroup.zpow_mem_zpowers c k
  have hA'3 : IsPGroup 3 A' := hA3.map _
  obtain ⟨P', hP'H, hA'P'⟩ : ∃ P' : Subgroup G, IsSylowOf 3 P' H ∧ A' ≤ P' := by
    have hP : IsPGroup 3 (A'.subgroupOf H) := hA'3.comap_subtype
    obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
    exact ⟨_, ⟨Q, rfl⟩, fun y hy => ⟨⟨y, hA'H hy⟩, hQ (Subgroup.mem_subgroupOf.mpr hy), rfl⟩⟩
  obtain ⟨x, hxH, hP'eq⟩ := Sec12.isSylowOf_exists_conj h.isSylowOf hP'H
  have hA'x : A' ≤ A.map (MulAut.conj x).toMonoidHom := by
    intro y hy
    have hyP : y ∈ R.map (MulAut.conj x).toMonoidHom := hP'eq ▸ hA'P' hy
    obtain ⟨r, hr, hry⟩ := hyP
    have hy3 : y ^ 3 = 1 := by
      obtain ⟨u, hu, rfl⟩ := hy
      rw [← map_pow, hexp u hu, map_one]
    have hr3 : r ^ 3 = 1 := by
      have h1 : (MulAut.conj x).toMonoidHom (r ^ 3) = 1 := by rw [map_pow, hry, hy3]
      exact (map_eq_one_iff _ (MulAut.conj x).injective).mp h1
    refine ⟨r, ?_, hry⟩
    rw [hAΩ]
    exact Subgroup.subset_closure ⟨hr, hr3⟩
  have hcardA' : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hcardAx : Nat.card (A.map (MulAut.conj x).toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hA'eq : A' = A.map (MulAut.conj x).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hA'x (by rw [hcardA', hcardAx])
  refine ⟨g * x, ?_, ?_⟩
  · refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    show A.map (MulAut.conj (g * x)).toMonoidHom = A
    rw [← map_conj_map_conj, ← hA'eq, hA', map_conj_map_conj, mul_inv_cancel]
    ext y
    simp
  · rw [← map_conj_map_conj]
    congr 1
    exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp hxH).symm

end CFSG.RankThree.PartTwo.Sec11
