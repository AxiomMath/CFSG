module

public import CFSG.LocalAnalysis.StandardType.GGSignedCoordSwaps
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
import CFSG.LocalAnalysis.StandardType.GGLemmaThreeThirteen

public section

namespace CFSG.StandardType

open CFSG.Assembly SpCoord
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem isComponentOf_subgroupOf {P H : Subgroup G} (hP : IsComponentOf P H) :
    CFSG.IsComponent (P.subgroupOf H) :=
  (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hP.1).mp hP

private theorem eq_or_commute_of_isComponentOf [Finite G] {P Q H : Subgroup G}
    (hP : IsComponentOf P H) (hQ : IsComponentOf Q H) : P = Q ∨ ⁅P, Q⁆ = ⊥ := by
  rcases CFSG.LocalCores.distinct_components_commute (isComponentOf_subgroupOf hP)
    (isComponentOf_subgroupOf hQ) with he | hc
  · left
    rw [Subgroup.subgroupOf_inj, inf_eq_left.2 hP.1, inf_eq_left.2 hQ.1] at he
    exact he
  · right
    have := congrArg (Subgroup.map H.subtype) hc
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hP.1,
      Subgroup.map_subgroupOf_eq_of_le hQ.1, Subgroup.map_bot] at this

theorem ggAutomizer_commute_of_isComponentOf_ne [Finite G] {H Bs P Q : Subgroup G}
    (hP : IsComponentOf P H) (hQ : IsComponentOf Q H) (hPQ : P ≠ Q) {u v : MulAut ↥Bs}
    (hu : u ∈ ggAutomizer P Bs) (hv : v ∈ ggAutomizer Q Bs) : u * v = v * u := by
  obtain ⟨g, hgP, -, hgu⟩ := mem_ggAutomizer_iff.mp hu
  obtain ⟨h, hhQ, -, hhv⟩ := mem_ggAutomizer_iff.mp hv
  have hgh : g * h = h * g := by
    have hc : ⁅P, Q⁆ = ⊥ := (eq_or_commute_of_isComponentOf hP hQ).resolve_left hPQ
    have hmem : ⁅g, h⁆ ∈ ⁅P, Q⁆ := Subgroup.commutator_mem_commutator hgP hhQ
    rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  refine MulEquiv.ext fun b => Subtype.ext ?_
  have h1 : ((u (v b) : ↥Bs) : G) = g * (h * (b : G) * h⁻¹) * g⁻¹ := by
    rw [hgu (v b), hhv b]
  have h2 : ((v (u b) : ↥Bs) : G) = h * (g * (b : G) * g⁻¹) * h⁻¹ := by
    rw [hhv (u b), hgu b]
  rw [MulAut.mul_apply, MulAut.mul_apply, h1, h2]
  have hinv : h⁻¹ * g⁻¹ = g⁻¹ * h⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, hgh]
  calc g * (h * (b : G) * h⁻¹) * g⁻¹ = (g * h) * (b : G) * (h⁻¹ * g⁻¹) := by group
    _ = (h * g) * (b : G) * (g⁻¹ * h⁻¹) := by rw [hgh, hinv]
    _ = h * (g * (b : G) * g⁻¹) * h⁻¹ := by group

theorem eq_of_isComponentOf_of_hasSignedSwap [Finite G] {p n : ℕ} (hp : p.Prime)
    {H Bs P Q : Subgroup G} (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hP : IsComponentOf P H) (hQ : IsComponentOf Q H) {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c)
    (hPs : HasSignedSwap ((ggAutomizer P Bs).map (MulAut.congr eta).toMonoidHom) a b)
    (hQs : HasSignedSwap ((ggAutomizer Q Bs).map (MulAut.congr eta).toMonoidHom) a c) :
    P = Q := by
  by_contra hPQ
  obtain ⟨u, hu, v, hv, huv⟩ :=
    exists_not_commute_of_hasSignedSwap hp hab hac hbc hPs hQs
  obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.mp hu
  obtain ⟨v', hv', rfl⟩ := Subgroup.mem_map.mp hv
  refine huv ?_
  calc MulAut.congr eta u' * MulAut.congr eta v'
      = MulAut.congr eta (u' * v') := (map_mul _ _ _).symm
    _ = MulAut.congr eta (v' * u') := by
        rw [ggAutomizer_commute_of_isComponentOf_ne hP hQ hPQ hu' hv']
    _ = MulAut.congr eta v' * MulAut.congr eta u' := map_mul _ _ _

theorem eq_of_isComponentOf_of_hasSignedSwap_on [Finite G] {p n : ℕ} (hp : p.Prime) (hn : 5 ≤ n)
    {H Bs P Q : Subgroup G} (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hP : IsComponentOf P H) (hQ : IsComponentOf Q H) {I I' : Finset (Fin n)}
    (hI : n ≤ I.card + 2) (hI' : n ≤ I'.card + 2)
    (hPs : ∀ a ∈ I, ∀ b ∈ I, a ≠ b →
      HasSignedSwap ((ggAutomizer P Bs).map (MulAut.congr eta).toMonoidHom) a b)
    (hQs : ∀ a ∈ I', ∀ b ∈ I', a ≠ b →
      HasSignedSwap ((ggAutomizer Q Bs).map (MulAut.congr eta).toMonoidHom) a b) :
    P = Q := by
  have hI3 : 3 ≤ I.card := by omega
  have hI'3 : 3 ≤ I'.card := by omega
  have hne : (I ∩ I').Nonempty := by
    rw [← Finset.card_pos]
    have hu : (I ∪ I').card ≤ n := by simpa using Finset.card_le_univ (I ∪ I')
    have hc := Finset.card_union_add_card_inter I I'
    omega
  obtain ⟨a, ha⟩ := hne
  rw [Finset.mem_inter] at ha
  obtain ⟨b, hbI, hbnot⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a} : Finset (Fin n))) (t := I) (by rw [Finset.card_singleton]; omega)
  rw [Finset.mem_singleton] at hbnot
  obtain ⟨c, hcI', hcnot⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b} : Finset (Fin n))) (t := I') (by
      rw [Finset.card_pair_eq_two_iff.mpr (Ne.symm hbnot)]; omega)
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hcnot
  exact eq_of_isComponentOf_of_hasSignedSwap hp eta hP hQ (Ne.symm hbnot) (Ne.symm hcnot.1)
    (Ne.symm hcnot.2) (hPs a ha.1 b hbI (Ne.symm hbnot)) (hQs a ha.2 c hcI' (Ne.symm hcnot.1))

theorem exists_ggConjAut_eq_of_mem_map_sup {Bs L K : Subgroup G} {V : Type*} [Group V]
    (eta : ↥Bs ≃* V) {u : MulAut V}
    (hu : u ∈ (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom) :
    ∃ g ∈ L ⊔ K, ∃ hg : g ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs hg) = u := by
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hu
  have hle : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer (L ⊔ K) Bs :=
    sup_le (ggAutomizer_mono Bs le_sup_left) (ggAutomizer_mono Bs le_sup_right)
  obtain ⟨g, hg, hgN, hgw⟩ := mem_ggAutomizer_iff.mp (hle hw)
  refine ⟨g, hg, hgN, ?_⟩
  have hweg : w = ggConjAut Bs hgN := by
    ext b
    rw [ggConjAut_apply]
    exact hgw b
  exact congrArg (MulAut.congr eta) hweg.symm

end CFSG.StandardType

end
