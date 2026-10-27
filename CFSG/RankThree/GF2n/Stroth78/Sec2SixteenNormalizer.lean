module

public import CFSG.RankThree.GF2n.Stroth78.Sec2Conj
public import CFSG.RankThree.GF2n.Stroth78.Sec2Lbar

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem exists_commutator_eq_z (S : Setting z E F) {a : G} (haQ : a ∈ Q z)
    (haZ : a ∉ ZQ z) : ∃ x ∈ Q z, ⁅x, a⁆ = z := by
  by_contra h
  have h' : ∀ x ∈ Q z, ⁅x, a⁆ ≠ z := fun x hx hxz => h ⟨x, hx, hxz⟩
  refine haZ (Subgroup.mem_inf.mpr ⟨haQ, ?_⟩)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rcases eq_one_or_z_of_mem_zpowers S (commutator_mem_zpowers_of_mem_Q S hy haQ) with h1 | h1
  · exact commutatorElement_eq_one_iff_mul_comm.mp h1
  · exact absurd h1 (h' y hy)

theorem exists_conj_eq_mul_z (S : Setting z E F) {a : G} (haQ : a ∈ Q z)
    (haZ : a ∉ ZQ z) : ∃ x ∈ Q z, x * a * x⁻¹ = a * z := by
  obtain ⟨x, hxQ, hx⟩ := exists_commutator_eq_z S haQ haZ
  have haz : a * z = z * a :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (z_mem_ZQ S)).2 a haQ
  refine ⟨x, hxQ, ?_⟩
  calc x * a * x⁻¹ = ⁅x, a⁆ * a := by rw [commutatorElement_def]; group
    _ = z * a := by rw [hx]
    _ = a * z := haz.symm

theorem isConj_mul_z (S : Setting z E F) {a : G} (haQ : a ∈ Q z) (haZ : a ∉ ZQ z) :
    IsConj a (a * z) := by
  obtain ⟨x, -, hx⟩ := exists_conj_eq_mul_z S haQ haZ
  exact isConj_iff.mpr ⟨x, hx⟩

theorem map_conj_QaOf (a g : G) :
    (QaOf a).map (MulAut.conj g).toMonoidHom = QaOf (g * a * g⁻¹) := by
  show (fStar (Subgroup.centralizer ({a} : Set G))).map (MulAut.conj g).toMonoidHom =
    fStar (Subgroup.centralizer ({g * a * g⁻¹} : Set G))
  rw [← fStar_map_conj (Subgroup.centralizer ({a} : Set G)) g, centralizer_map_conj a g]

theorem zpow_eq_one_or_self_of_orderOf_eq_two {g : G} (hg : orderOf g = 2) (k : ℤ) :
    g ^ k = 1 ∨ g ^ k = g := by
  have h2 : g ^ (2 : ℤ) = 1 := by
    have h : (2 : ℤ) = (orderOf g : ℤ) := by rw [hg]; norm_num
    rw [h, zpow_natCast, pow_orderOf_eq_one]
  have h := zpow_eq_zpow_emod (x := g) k h2
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left; rw [h, hk]; simp
  · right; rw [h, hk]; norm_num

theorem map_conj_CQ_eq_centerIn_QaOf {a g : G}
    (hgz : g * z * g⁻¹ = a) (hga : g * a * g⁻¹ = z) :
    ((Q z ⊓ Subgroup.centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom) =
      QaOf a ⊓ Subgroup.centralizer ({z} : Set G) := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, map_conj_QaOf z g, hgz,
    ← centralizer_map_conj a g, hga]

end CFSG.RankThree.GF2n.Stroth78
