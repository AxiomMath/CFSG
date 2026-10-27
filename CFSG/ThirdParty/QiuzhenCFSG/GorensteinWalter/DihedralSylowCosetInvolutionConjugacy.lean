module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralOuterInvolutionConjugacy
public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Involution conjugacy in a coset of a normal index-two subgroup -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- If the intersection of a normal index-two subgroup with a fixed
dihedral Sylow `2`-subgroup is a Klein four, then the normal subgroup is
transitive by conjugation on the involutions outside it. -/
public theorem dihedral_sylow_involutions_not_mem_normal_index_two_conjugate
    {G : Type u} [Group G] [Finite G]
    (D : Subgroup G) (hDindex : D.index = 2)
    (P : Sylow 2 G)
    (hHklein : IsKleinFour (D.comap (P : Subgroup G).subtype))
    (eP : P ≃* DihedralGroup 4)
    {a b : G} (ha : IsInvolution a) (hb : IsInvolution b)
    (haD : a ∉ D) (hbD : b ∉ D) :
    ∃ d : G, d ∈ D ∧ d * a * d⁻¹ = b := by
  classical
  let H : Subgroup P := D.comap (P : Subgroup G).subtype
  have hPcard : Nat.card P = 8 := by
    calc
      Nat.card P = Nat.card (DihedralGroup 4) := Nat.card_congr eP.toEquiv
      _ = 8 := by rw [DihedralGroup.nat_card]
  have hHindex : H.index = 2 := by
    have hcard := Subgroup.card_mul_index H
    rw [show Nat.card H = 4 by simpa [H] using hHklein.card_four,
      hPcard] at hcard
    omega
  have hHnoncyclic : ¬ IsCyclic H := by
    let : IsKleinFour H := by simpa [H] using hHklein
    exact IsKleinFour.not_isCyclic
  have conj_involution {x g : G} (hx : IsInvolution x) :
      IsInvolution (g * x * g⁻¹) := by
    constructor
    · intro h1
      apply hx.1
      calc
        x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; simp
    · calc
        (g * x * g⁻¹) ^ 2 = g * (x ^ 2) * g⁻¹ := by
          simp only [pow_two]
          group
        _ = 1 := by rw [hx.2]; simp
  have adjust_conjugator {x y g : G}
      (hx : IsInvolution x) (hxD : x ∉ D)
      (hg : g * x * g⁻¹ = y) :
      ∃ d : G, d ∈ D ∧ d * x * d⁻¹ = y := by
    by_cases hgD : g ∈ D
    · exact ⟨g, hgD, hg⟩
    · refine ⟨g * x, ?_, ?_⟩
      · rw [Subgroup.mul_mem_iff_of_index_two hDindex]
        exact iff_of_false hgD hxD
      · have hx2 : x * x = 1 := by simpa [pow_two] using hx.2
        calc
          (g * x) * x * (g * x)⁻¹ = g * x * g⁻¹ := by
            rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx2]
            calc
              (g * x) * x * (x * g⁻¹) = g * (x * x) * x * g⁻¹ := by group
              _ = g * x * g⁻¹ := by rw [hx2]; simp
          _ = y := hg
  have conjugate_into_P {x : G} (hx : IsInvolution x) (hxD : x ∉ D) :
      ∃ d : G, d ∈ D ∧ ∃ xP : P, d * x * d⁻¹ = (xP : G) := by
    let X : Subgroup G := Subgroup.zpowers x
    have hxOrder : orderOf x = 2 := orderOf_eq_prime hx.2 hx.1
    have hXcard : Nat.card X = 2 := by
      simp [X, Nat.card_zpowers, hxOrder]
    have hXp : IsPGroup 2 X := IsPGroup.of_card (n := 1) (by
      rw [hXcard]
      norm_num)
    obtain ⟨Q, hXQ⟩ := hXp.exists_le_sylow
    obtain ⟨g, hgQP⟩ := MulAction.exists_smul_eq G Q P
    have hxQ : x ∈ (Q : Subgroup G) :=
      hXQ (Subgroup.mem_zpowers x)
    have hxP : g * x * g⁻¹ ∈ (P : Subgroup G) := by
      rw [← hgQP]
      rw [Sylow.coe_subgroup_smul]
      exact Set.mem_smul_set.mpr ⟨x, hxQ, by
        simp [MulAut.conj_apply]⟩
    obtain ⟨d, hdD, hd⟩ :=
      adjust_conjugator hx hxD (g := g) (y := g * x * g⁻¹) rfl
    exact ⟨d, hdD, ⟨⟨g * x * g⁻¹, hxP⟩, hd⟩⟩
  obtain ⟨da, hdaD, aP, haP⟩ := conjugate_into_P ha haD
  obtain ⟨db, hdbD, bP, hbP⟩ := conjugate_into_P hb hbD
  have haPambI : IsInvolution (aP : G) := by
    have h := conj_involution (g := da) ha
    rwa [haP] at h
  have hbPambI : IsInvolution (bP : G) := by
    have h := conj_involution (g := db) hb
    rwa [hbP] at h
  have haPI : IsInvolution aP := by
    constructor
    · intro h
      exact haPambI.1 (congrArg Subtype.val h)
    · apply Subtype.ext
      exact haPambI.2
  have hbPI : IsInvolution bP := by
    constructor
    · intro h
      exact hbPambI.1 (congrArg Subtype.val h)
    · apply Subtype.ext
      exact hbPambI.2
  have haPH : aP ∉ H := by
    intro haPH
    apply haD
    have haPD : (aP : G) ∈ D := by
      change (aP : G) ∈ D at haPH
      exact haPH
    have hmem : da⁻¹ * (aP : G) * da ∈ D :=
      D.mul_mem (D.mul_mem (D.inv_mem hdaD) haPD) hdaD
    have heq : a = da⁻¹ * (aP : G) * da := by
      rw [← haP]
      group
    rwa [heq]
  have hbPH : bP ∉ H := by
    intro hbPH
    apply hbD
    have hbPD : (bP : G) ∈ D := by
      change (bP : G) ∈ D at hbPH
      exact hbPH
    have hmem : db⁻¹ * (bP : G) * db ∈ D :=
      D.mul_mem (D.mul_mem (D.inv_mem hdbD) hbPD) hdbD
    have heq : b = db⁻¹ * (bP : G) * db := by
      rw [← hbP]
      group
    rwa [heq]
  have habP : IsConj aP bP :=
    dihedral_involutions_not_mem_noncyclic_index_two_isConj
      (m := 2) (by omega) eP H hHindex hHnoncyclic
        haPI hbPI haPH hbPH
  obtain ⟨q, hq⟩ := isConj_iff.mp habP
  have hqamb : (q : G) * (aP : G) * (q : G)⁻¹ = (bP : G) :=
    congrArg Subtype.val hq
  have haPnotD : (aP : G) ∉ D := by
    intro haPD
    apply haPH
    change (aP : G) ∈ D
    exact haPD
  obtain ⟨qD, hqDD, hqD⟩ :=
    adjust_conjugator haPambI haPnotD
      (g := (q : G)) (y := (bP : G)) hqamb
  refine ⟨db⁻¹ * qD * da,
    D.mul_mem (D.mul_mem (D.inv_mem hdbD) hqDD) hdaD, ?_⟩
  calc
    (db⁻¹ * qD * da) * a * (db⁻¹ * qD * da)⁻¹ =
        db⁻¹ * (qD * (aP : G) * qD⁻¹) * db := by rw [← haP]; group
    _ = db⁻¹ * (bP : G) * db := by rw [hqD]
    _ = b := by rw [← hbP]; group

end CFSG.GorensteinWalter
