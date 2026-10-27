module

public import CFSG.Quasithin.EmptyFaithful.E22PL2PglA
import CFSG.Dihedral.PerfectDihedralFourgroupAction

public section

namespace CFSG.Quasithin.E22L2

open CFSG.GorensteinWalter
open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 (pslRange)

theorem e22pl2pgl_surjective_of_le {G : Type*} [Group G] {J V : Subgroup G} (hVJ : V ≤ J)
    (h : Function.Surjective (V.subgroupOf J).normalizerMonoidHom) :
    Function.Surjective V.normalizerMonoidHom := by
  intro σ
  let e : ↥(V.subgroupOf J) ≃* ↥V := Subgroup.subgroupOfEquivOfLe hVJ
  obtain ⟨n, hn⟩ := h (MulAut.congr e.symm σ)
  have hn' := Subgroup.mem_normalizer_iff.mp n.2
  have hnorm : (((n : ↥J)) : G) ∈ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 := (hn' ⟨x, hVJ hx⟩).mp (Subgroup.mem_subgroupOf.mpr hx)
      exact Subgroup.mem_subgroupOf.mp h1
    · intro hx
      have hxJ : x ∈ J := by
        have h2 : (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) * (n : G) ∈ J :=
          J.mul_mem (J.mul_mem (J.inv_mem (n : ↥J).2) (hVJ hx)) (n : ↥J).2
        simpa [mul_assoc] using h2
      have h3 : (⟨x, hxJ⟩ : ↥J) ∈ V.subgroupOf J := by
        rw [hn' ⟨x, hxJ⟩]
        exact Subgroup.mem_subgroupOf.mpr hx
      exact Subgroup.mem_subgroupOf.mp h3
  refine ⟨⟨((n : ↥J) : G), hnorm⟩, ?_⟩
  ext x
  have h1 := congrArg (fun φ : MulAut ↥(V.subgroupOf J) => ((φ (e.symm x) : ↥(V.subgroupOf J)) : G))
    hn
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.congr_apply] at h1
  simpa [e] using h1

theorem e22pl2pgl_isKleinFour_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [IsKleinFour Y]
    (e : X ≃* Y) : IsKleinFour X :=
  ⟨by rw [Nat.card_congr e.toEquiv]; exact IsKleinFour.card_four,
    by rw [Monoid.exponent_eq_of_mulEquiv e]; exact IsKleinFour.exponent_two⟩

theorem e22pl2pgl_normalizer_surjective_q {K : Type} [Field K] [Finite K]
    (hodd : IsOddPrimePower (Nat.card K)) (hq8 : Nat.card K % 8 = 1 ∨ Nat.card K % 8 = 7)
    (hq7 : 7 ≤ Nat.card K) {V : Subgroup (PGL2 K)} (hVJ : V ≤ pslRange K)
    (hV : IsKleinFour ↥V) : Function.Surjective V.normalizerMonoidHom := by
  have := e22pl2pgl_finite K
  have hcard : 3 < Nat.card K := by omega
  refine e22pl2pgl_surjective_of_le hVJ ?_
  have hV'' : IsKleinFour ↥(V.subgroupOf (pslRange K)) :=
    e22pl2pgl_isKleinFour_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hVJ)
  have h2 : IsPGroup 2 ↥(V.subgroupOf (pslRange K)) :=
    IsPGroup.of_card (n := 2) (by rw [hV''.card_four]; norm_num)
  obtain ⟨S, hS⟩ := h2.exists_le_sylow
  obtain ⟨m, hm, ⟨e⟩⟩ := e22pl2pgl_sylow_dihedral_J_q hodd hq8 S
  have := e22pl2pgl_perfect_J hcard
  exact perfect_dihedral_fourgroup_normalizer_surjective S hm e _ hS hV''

end CFSG.Quasithin.E22L2
