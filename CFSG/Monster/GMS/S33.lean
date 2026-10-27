module

public import CFSG.Monster.GMS.S31Two
public import CFSG.Monster.GMS.Facts.TableIV
import CFSG.Monster.GMS.NotConj

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G]

private theorem exists_mem_notMem_finset (E : Subgroup G) (S : Finset G)
    (h : S.card < Nat.card E) : ∃ x ∈ E, x ∉ S := by
  by_contra hall
  push Not at hall
  have hsub : (E : Set G) ⊆ (S : Set G) := fun x hx => by exact_mod_cast hall x hx
  have h1 := Set.ncard_le_ncard hsub S.finite_toSet
  rw [Set.ncard_coe_finset] at h1
  have h2 : Nat.card E = (E : Set G).ncard := Nat.card_coe_set_eq (E : Set G)
  omega

private theorem isTwoACls_of_isConj {a b z u z₀ w : G} (hTV : TableV a b z u) (haa : a * a = 1)
    (hnc : ¬ IsConj a z₀) (hz : IsConj z₀ z) (hu : IsConj z₀ u)
    (hwC : w ∈ Subgroup.centralizer ({a} : Set G)) (hw2 : orderOf w = 2) (hwa : w ≠ a)
    (hwA : IsConj a w) (hawA : IsConj a (a * w)) : IsTwoACls a b w := by
  obtain ⟨g, hg, hcase⟩ := hTV.cover w hwC hw2 hwa
  have hgw : IsConj w (g * w * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  rcases hcase with e | e | e | e
  · exact ⟨g, hg, Or.inl e⟩
  · rw [e] at hgw
    exact absurd ((hwA.trans hgw).trans hz.symm) hnc
  · have hgaw : g * (a * w) * g⁻¹ = a * (g * w * g⁻¹) := conj_mul_of_mem_centralizer hg w
    have haaz : a * (a * z) = z := by rw [← mul_assoc, haa, one_mul]
    rw [e, haaz] at hgaw
    exact absurd ((hawA.trans (isConj_iff.mpr ⟨g, hgaw⟩)).trans hz.symm) hnc
  · rw [e] at hgw
    exact absurd ((hwA.trans hgw).trans hu.symm) hnc

private theorem false_of_subgroup {a b z u z₀ : G} (hTV : TableV a b z u)
    (hnc : ¬ IsConj a z₀) (hz : IsConj z₀ z) (hu : IsConj z₀ u) (hP : TableIVProduct a b)
    (E : Subgroup G) (hE : Nat.card E = 8) (hE2 : ∀ x ∈ E, x * x = 1) (haE : a ∈ E)
    (hA : ∀ x ∈ E, x ≠ 1 → IsConj a x) : False := by
  classical
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    mul_comm_of_mul_self_eq_one (hE2 x hx) (hE2 y hy) (hE2 _ (E.mul_mem hx hy))
  have haa : a * a = 1 := hE2 a haE
  obtain ⟨x, hxE, hx⟩ := exists_mem_notMem_finset E {1, a} (by
    have := Finset.card_le_two (a := (1 : G)) (b := a)
    omega)
  obtain ⟨y, hyE, hy⟩ := exists_mem_notMem_finset E {1, a, x, a * x} (by
    have := Finset.card_le_four (a := (1 : G)) (b := a) (c := x) (d := a * x)
    omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx hy
  obtain ⟨hx1, hxa⟩ := hx
  obtain ⟨hy1, hya, hyx, hyax⟩ := hy
  have hxx : x * x = 1 := hE2 x hxE
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have key : ∀ w ∈ E, w ≠ 1 → w ≠ a → IsTwoACls a b w := by
    intro w hwE hw1 hwa
    have hwC : w ∈ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hcomm w hwE a haE)
    have haw1 : a * w ≠ 1 := by
      intro h1
      apply hwa
      rw [eq_inv_of_mul_eq_one_right h1]
      exact inv_eq_of_mul_eq_one_right haa
    exact isTwoACls_of_isConj hTV haa hnc hz hu hwC (orderOf_eq_two_of_mul_self (hE2 w hwE) hw1)
      hwa (hA w hwE hw1) (hA _ (E.mul_mem haE hwE) haw1)
  have hxy1 : x * y ≠ 1 := by
    intro h1
    apply hyx
    rw [eq_inv_of_mul_eq_one_right h1, hxinv]
  have hxya : x * y ≠ a := by
    intro h1
    apply hyax
    calc y = x * (x * y) := by rw [← mul_assoc, hxx, one_mul]
      _ = x * a := by rw [h1]
      _ = a * x := hcomm x hxE a haE
  have hxC : x ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hxE a haE)
  have hyC : y ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hyE a haE)
  refine hP x hxC y hyC (key x hxE hx1 hxa) (key y hyE hy1 hya) (hcomm x hxE y hyE)
    (fun h1 => hyx h1.symm) ?_ (key (x * y) (E.mul_mem hxE hyE) hxy1 hxya)
  intro h1
  apply hyax
  calc y = a * (a * y) := by rw [← mul_assoc, haa, one_mul]
    _ = a * x := by rw [← h1]

theorem s33
    [Finite G] {d₀ : B} (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) (hT4 : TableIVIn G)
    (E : Subgroup G) (hE : Nat.card E = 8) (hE2 : ∀ x ∈ E, x * x = 1) :
    ∃ x ∈ E, x ≠ 1 ∧ ¬ IsConj a x := by
  by_contra hno
  push Not at hno
  obtain ⟨b, z, u, hTVz, -, -, hz₀z, -, -, hz₀u, -, -, -⟩ := s31_two hSLS hTV hL hG
  have hP : TableIVProduct a b := hT4 a b z u (hG.1.isTwoBabyCentralizer hSLS) hTVz
  obtain ⟨a₀, ha₀E, ha₀⟩ := exists_mem_notMem_finset E {1} (by
    have := Finset.card_singleton (1 : G)
    omega)
  have ha₀1 : a₀ ≠ 1 := by simpa using ha₀
  obtain ⟨c, hc⟩ := isConj_iff.mp (hno a₀ ha₀E ha₀1).symm
  have hmap : ∀ x : G, (MulAut.conj c).toMonoidHom x = c * x * c⁻¹ := fun x => rfl
  refine false_of_subgroup hTVz hG.not_isConj hz₀z hz₀u hP (E.map (MulAut.conj c).toMonoidHom) ?_ ?_
    ⟨a₀, ha₀E, by rw [hmap, hc]⟩ ?_
  · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact hE
  · rintro _ ⟨x₀, hx₀, rfl⟩
    rw [hmap]
    calc c * x₀ * c⁻¹ * (c * x₀ * c⁻¹) = c * (x₀ * x₀) * c⁻¹ := by group
      _ = 1 := by rw [hE2 x₀ hx₀]; group
  · rintro _ ⟨x₀, hx₀, rfl⟩ hx
    have hx₀1 : x₀ ≠ 1 := by
      rintro rfl
      exact hx (by rw [hmap]; group)
    rw [hmap]
    exact (hno x₀ hx₀ hx₀1).trans (isConj_iff.mpr ⟨c, rfl⟩)

end CFSG.Monster.GMS
