module

public import CFSG.RankThree.PartOne.KC.LinearNoninnerPlaneGeneral
public import CFSG.RankThree.PartOne.KC.LinearNonsplitSubfieldFixedGroup
public import CFSG.RankThree.PartOne.KC.LinearCommutatorNodes
public import CFSG.RankThree.PartOne.KC.ThetaCoreSimpleFixedGroup

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.RankThree.GroupTheory.SteinbergBY (mulAut_conj_apply_eq)

namespace KCLinPlane

theorem nonsplit_linear_prime_field_actor_solvable_core_trivial {ℓ p f n : ℕ} (hℓ : ℓ.Prime)
    (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) (hf : 1 ≤ f) (hn : 3 ≤ n)
    {K : Type} [Field K] [CharP K ℓ] (hK : Nat.card K = ℓ ^ f) (hpq : ¬ p ∣ ℓ ^ f - 1)
    (B : Subgroup (MulAut (projectiveSL n K)))
    (hB : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ B)
    {a : MulAut (projectiveSL n K)} (haE : a ∈ semilinearAutGroup n K)
    (haD : a ∉ linearAutGroup n K) (hord : orderOf a = p) :
    inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({a} : Set (MulAut (projectiveSL n K)))) = ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hℓ.ne_zero)
  obtain ⟨-, -, -, -, -, -, -, hdesc⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent hℓ hf hn hK
  obtain ⟨-, σ, hσ, ⟨h, -, hah⟩, -⟩ := hdesc p hp hpℓ a haE haD hord
  obtain ⟨-, -, hfix, ⟨hsimple, hnonab⟩, -, -, -, -, hstab, -, -⟩ :=
    nonsplit_linear_prime_subfield_fixed_group_and_full_centralizer hℓ hp hp3 hpℓ hf hn hK hpq σ hσ
  have hconjinj := CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (k := K) hn
  have key : ∀ B' : Subgroup (MulAut (projectiveSL n K)),
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ B' →
      inSubgroup (aschbacherSolvableCore p)
        (B' ⊓ Subgroup.centralizer ({fieldAut n K σ} : Set (MulAut (projectiveSL n K)))) = ⊥ :=
    fun B' hB' => inSubgroup_theta_centralizer_eq_bot_of_simple_fixed_group hp hconjinj
      (a := fieldAut n K σ) (by rw [KCLinearSubfield.orderOf_fieldAut hn, hσ])
      (H := (linearSubfieldInclusion n (semilinearFixedSubfield σ)).range)
      (fun x => by
        have := Set.ext_iff.mp hfix x
        exact this.symm)
      hsimple hnonab
      (fun s hs => by
        rw [← hstab]
        exact (mem_fixingSubgroup_iff (MulAut (projectiveSL n K))).mpr fun y hy => hs y hy)
      hB'
  set φ : MulAut (MulAut (projectiveSL n K)) := MulAut.conj h⁻¹ with hφ
  have hφapp : ∀ x, φ.toMonoidHom x = h⁻¹ * x * h := fun x => by
    simp [hφ]
  have hφa : φ a = fieldAut n K σ := by
    show φ.toMonoidHom a = _
    rw [hφapp, hah]
    group
  set B' : Subgroup (MulAut (projectiveSL n K)) := B.map φ.toMonoidHom with hB'
  have hB'conj : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ B' := by
    rintro _ ⟨x, rfl⟩
    refine Subgroup.mem_map.mpr ⟨MulAut.conj (h x), hB ⟨h x, rfl⟩, ?_⟩
    rw [hφapp, mulAut_conj_apply_eq h x]
    group
  have h1 := map_inSubgroup_theta_centralizer_mulEquiv hp φ B a
  rw [hφa, key B' hB'conj] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h1

end KCLinPlane

theorem nonsplit_linear_noninner_plane_local_core_product_odd :
    NonsplitLinearNoninnerPlaneLocalCoreOdd := by
  intro p ℓ f n K _ hp hp3 hℓ hℓp hf hn hK hpq B hB A hAB hAel hAcard hAH
  have : IsElementaryAbelian p A := hAel
  have hp2 : p ≠ 2 := by omega
  have hCharP : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have hcop : Nat.Coprime p (Nat.gcd n (Nat.card K - 1)) := by
    rw [hK]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr
      (fun h => hpq (h.trans (Nat.gcd_dvd_right _ _)))
  exact KCLinPlane.noninner_plane_data hp hp2 hℓ hℓp hf hn hK hcop B A hAB hAcard hAH
    (fun a _ haE haD hord => KCLinPlane.nonsplit_linear_prime_field_actor_solvable_core_trivial
      hℓ hp hp3 hℓp.symm hf hn hK hpq B hB haE haD hord)
    (fun hq t ht htp A' hA' hA'p =>
      (nonsplit_linear_inner_actor_local_core_commutators_odd hp hp3 hℓ hℓp hf hn hK hq hpq B hB
        ht htp).1 A' hA' hA'p)

end CFSG.RankThree.PartOne
