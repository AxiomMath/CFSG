module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFourOrthA
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFourOrthB
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFourOrthC
public import CFSG.RankThree.OrthogonalInvolutions.Witt
public import CFSG.LocalAnalysis.WeakClosure81.CentralInSylowIndexReverse

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Module QuadraticMap Subgroup
open CFSG.RankThree.OrthogonalInvolutions renaming commSpace → orthCommSpace

section Orth

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem odd_finrank_commSpace_of_normalClosure_eq_top [Nontrivial V] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) (d : ↥(TauCeti.QuadraticMap.orthogonalGroup Q))
    (hcl : Subgroup.normalClosure ({d} : Set ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) = ⊤) :
    Odd (finrank K (orthCommSpace (d : V ≃ₗ[K] V))) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have hcast : ((finrank K (orthCommSpace (d : V ≃ₗ[K] V)) : ℕ) : ZMod 2) = 0 :=
    ZMod.natCast_eq_zero_iff_even.mpr hodd
  set D := CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ with hD
  have hdker : d ∈ D.ker := by
    rw [MonoidHom.mem_ker, hD, CFSG.RankThree.OrthogonalInvolutions.dicksonHom_apply, hcast]
    rfl
  have hle : Subgroup.normalClosure ({d} : Set ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) ≤
      D.ker := by
    refine Subgroup.normalClosure_le_normal ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rwa [hx]
  have htop : D.ker = ⊤ := top_le_iff.mp (hcl ▸ hle)
  have hsub : (CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup Q) = ⊤ := by
    rw [← CFSG.RankThree.OrthogonalInvolutions.dicksonHom_ker Q hQ, ← hD]
    exact htop
  have hle_orth : TauCeti.QuadraticMap.orthogonalGroup Q ≤
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ :=
    (Subgroup.subgroupOf_eq_top (H := CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ)
      (K := TauCeti.QuadraticMap.orthogonalGroup Q)).mp hsub
  have hrel := CFSG.RankThree.OrthogonalInvolutions.relIndex_omegaGroup Q hQ
  rw [Subgroup.relIndex_eq_one.mpr hle_orth] at hrel
  omega

theorem exists_polar_sq_eq {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate)
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgg : g * g = 1) :
    ∃ u : V, ∀ x : V, (polar Q x u) ^ 2 = Q (g x - x) := by
  exact w85g_exists_polar_sq_eq hQ hg hgg

theorem map_eq_natCast_finrank_commSpace {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgg : g * g = 1) {u : V}
    (hu : ∀ x : V, (polar Q x u) ^ 2 = Q (g x - x)) :
    Q u = (finrank K (orthCommSpace g) : K) := by
  exact w85g_map_eq_natCast_finrank_commSpace hQ hg hgg hu

theorem apply_eq_of_polar_sq_eq {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate)
    {g : V ≃ₗ[K] V} {u : V} (hu : ∀ x : V, (polar Q x u) ^ 2 = Q (g x - x))
    {h : V ≃ₗ[K] V} (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hhg : h * g = g * h) :
    h u = u := by
  exact w85g_apply_eq_of_polar_sq_eq hQ hu hh hhg

theorem exists_orthogonalGroup_apply_eq_of_map_eq_one {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) (hd : 4 ≤ finrank K V) {x y : V} (hx : Q x = 1)
    (hy : Q y = 1) : ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g x = y := by
  have hx0 : x ≠ 0 := by rintro rfl; simpa using hx
  have hy0 : y ≠ 0 := by rintro rfl; simpa using hy
  obtain ⟨g, hg, hgx⟩ :=
    CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq hQ
      (u := fun _ : Fin 1 => x) (u' := fun _ : Fin 1 => y)
      (by rw [linearIndependent_unique_iff]; simpa using hx0)
      (by rw [linearIndependent_unique_iff]; simpa using hy0)
      (fun i => hy.trans hx.symm)
      (fun i j => by rw [CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero,
        CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero])
  exact ⟨g, hg, by simpa using hgx 0⟩

theorem even_card_map_eq_one {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate)
    (hd : 4 ≤ finrank K V) : Even (Nat.card {x : V // Q x = 1}) := by
  exact w85g_even_card_map_eq_one hQ hd

theorem exists_fixed_map_eq_one {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate)
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgg : g * g = 1)
    (hodd : Odd (finrank K (orthCommSpace g))) :
    ∃ w : V, Q w = 1 ∧ ∀ h ∈ TauCeti.QuadraticMap.orthogonalGroup Q, h * g = g * h → h w = w := by
  obtain ⟨u, hu⟩ := exists_polar_sq_eq hQ hg hgg
  refine ⟨u, ?_, fun h hh hhg => apply_eq_of_polar_sq_eq hQ hu hh hhg⟩
  rw [map_eq_natCast_finrank_commSpace hQ hg hgg hu]
  exact natCast_eq_one_of_odd_of_two_eq_zero hodd (CharP.cast_eq_zero K 2)

theorem not_centralInSylow_orth [Nontrivial V] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) (hd4 : 4 ≤ finrank K V)
    (d : ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) (hdd : d * d = 1)
    (hcl : Subgroup.normalClosure ({d} : Set ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) = ⊤) :
    ¬ CentralInSylow ↥(TauCeti.QuadraticMap.orthogonalGroup Q) (Subgroup.zpowers d) := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun f : V ≃ₗ[K] V => (f : V → V)) DFunLike.coe_injective
  haveI : Finite ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := inferInstance
  intro hc
  have hodd := (centralInSylow_zpowers_iff_odd_index d hdd).1 hc
  have hgg : (d : V ≃ₗ[K] V) * d = 1 := by
    have := congrArg (fun x : ↥(TauCeti.QuadraticMap.orthogonalGroup Q) => (x : V ≃ₗ[K] V)) hdd
    simpa using this
  obtain ⟨w, hw, hfix⟩ := exists_fixed_map_eq_one hQ d.2 hgg
    (odd_finrank_commSpace_of_normalClosure_eq_top hQ d hcl)
  have hle : Subgroup.centralizer ({d} : Set ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) ≤
      MulAction.stabilizer ↥(TauCeti.QuadraticMap.orthogonalGroup Q) w := by
    intro h hh
    have hcomm := (Subgroup.mem_centralizer_iff.1 hh) d (Set.mem_singleton d)
    have hcomm' : (h : V ≃ₗ[K] V) * d = d * h := by
      have := congrArg (fun x : ↥(TauCeti.QuadraticMap.orthogonalGroup Q) => (x : V ≃ₗ[K] V))
        hcomm.symm
      simpa using this
    exact hfix h h.2 hcomm'
  have horbit : MulAction.orbit ↥(TauCeti.QuadraticMap.orthogonalGroup Q) w =
      {x : V | Q x = 1} := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 g.2 w).trans hw
    · intro hx
      obtain ⟨g, hg, hgx⟩ := exists_orthogonalGroup_apply_eq_of_map_eq_one hQ hd4 hw hx
      exact ⟨⟨g, hg⟩, hgx⟩
  have hindex : (MulAction.stabilizer ↥(TauCeti.QuadraticMap.orthogonalGroup Q) w).index =
      Nat.card {x : V // Q x = 1} := by
    rw [MulAction.index_stabilizer, horbit]
    exact (Nat.card_coe_set_eq {x : V | Q x = 1}).symm
  have h2 : 2 ∣ (MulAction.stabilizer ↥(TauCeti.QuadraticMap.orthogonalGroup Q) w).index := by
    rw [hindex]
    exact even_iff_two_dvd.1 (even_card_map_eq_one hQ hd4)
  exact hodd.not_two_dvd_nat (h2.trans (Subgroup.index_dvd_of_le hle))

end Orth

end CFSG.LocalAnalysis.WeakClosure81

end
