module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65SylowCenter
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65InversionG2General

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint.Chevalley

theorem sylowCenterInverted_of_lieModel_g2
    {Y : Type} [Group Y] [Finite Y] {r f : ℕ} (hr3 : r ≠ 3)
    (hY : CFSG.Blueprint.LieModel Y .G2 0 r f) : SylowCenterInverted Y := by
  classical
  obtain ⟨hr, -, -, h3le⟩ := hY.admissible
  intro Q z hzQ hzc hz3
  have hc : CFSG.Blueprint.ChevalleyExceptionalModel Y .G2 r f :=
    CFSG.Blueprint.LieModel.chevalleyExceptionalModel hY (by decide)
  have hm : CFSG.Blueprint.UntwistedChevalleyModel Y .G2 (r ^ f) := hc.2
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨eX⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup (τ := .G2) hm
  let _ : Field K := hKfield
  let _ : Finite K := hKfinite
  have hKq : Nat.card K = r ^ f := hKcard
  have hq3 : 3 ≤ Nat.card K := by rw [hKq]; exact h3le
  have h3 : ¬ 3 ∣ Nat.card K := by
    rw [hKq]
    intro h
    have h3r : 3 ∣ r := Nat.prime_three.dvd_of_dvd_pow h
    exact hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1 h3r).symm
  let Q' : Sylow 3 (adjointGroup .G2 K) :=
    Sylow.mapSurjective (f := eX.toMonoidHom) eX.surjective Q
  let z' : adjointGroup .G2 K := eX z
  have hQ' : (Q' : Subgroup (adjointGroup .G2 K)) =
      (Q : Subgroup Y).map eX.toMonoidHom := by
    simp [Q']
  have hzQ' : z' ∈ (Q' : Subgroup (adjointGroup .G2 K)) := by
    rw [hQ']
    exact Subgroup.mem_map_of_mem eX.toMonoidHom hzQ
  have hzc' : z' ∈ Subgroup.centralizer
      ((Q' : Subgroup (adjointGroup .G2 K)) : Set (adjointGroup .G2 K)) := by
    rw [Subgroup.mem_centralizer_iff] at hzc ⊢
    intro y hy
    rw [hQ'] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    simpa only [map_mul, z', MulEquiv.coe_toMonoidHom] using congrArg eX.toMonoidHom
      (Subgroup.mem_centralizer_iff.mp hzc q hq)
  have hz3' : orderOf z' = 3 := by
    simpa [z'] using (MulEquiv.orderOf_eq eX z).trans hz3
  obtain ⟨t', -, ht'inv⟩ :=
    g2_sylow_inversion_of_not_dvd h3 hq3 Q' z' hzQ' hzc' hz3'
  refine ⟨eX.symm t', ?_⟩
  apply eX.injective
  rw [map_mul, map_mul, map_inv, eX.apply_symm_apply, map_inv]
  exact ht'inv

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
