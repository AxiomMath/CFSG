module

public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.GLTwoSL
import CFSG.LocalAnalysis.SectionRank.Ccomm.LinearTwo

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

private theorem res1CentSL2_ker_le {X : Type*} [Group X] [Group.IsPerfect X] {N : Subgroup X}
    [N.Normal] (hN : Group.IsSolvable N) (hsimple : IsSimpleGroup (X ⧸ N)) {M : Type*} [Monoid M]
    (ρ : X →* M) (hρ : ∃ x, ρ x ≠ 1) : ρ.ker ≤ N := by
  by_contra hK
  have hnorm : (ρ.ker.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map ρ.normal_ker _ (QuotientGroup.mk'_surjective N)
  have hsup : ρ.ker ⊔ N = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.ker.map (QuotientGroup.mk' N)) with h | h
    · exact absurd (by rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h) hK
    · rw [← QuotientGroup.ker_mk' N, ← Subgroup.comap_map_eq, h, Subgroup.comap_top]
  have hg : Function.Surjective ((QuotientGroup.mk' ρ.ker).comp N.subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ρ.ker q
    obtain ⟨k, hk, n, hn, rfl⟩ :=
      Subgroup.mem_sup_of_normal_left.1 (hsup ▸ Subgroup.mem_top x)
    refine ⟨⟨n, hn⟩, ?_⟩
    simp [(QuotientGroup.eq_one_iff k).2 hk]
  haveI : Group.IsSolvable N := hN
  haveI : Group.IsSolvable (X ⧸ ρ.ker) := Group.isSolvable_of_surjective hg
  haveI : Nontrivial (X ⧸ ρ.ker) := by
    obtain ⟨x, hx⟩ := hρ
    refine ⟨⟨QuotientGroup.mk' ρ.ker x, 1, fun h => hx ?_⟩⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, MonoidHom.mem_ker] at h
    exact h
  exact Group.IsPerfect.not_isSolvable (X ⧸ ρ.ker) inferInstance

private theorem res1CentSL2_eq_one {L : Type*} [Group L] {N : Subgroup L} (hN3 : ¬ 3 ∣ Nat.card N)
    {g : L} (hgN : g ∈ N) (hg3 : g ^ 3 = 1) : g = 1 := by
  rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hg3) with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd (h ▸ Subgroup.orderOf_dvd_natCard N hgN) hN3

theorem res1Cent_rho_eq_one_of_finrank_le_two {L : Type*} [Group L] [Finite L]
    [Group.IsPerfect L] {N : Subgroup L} [N.Normal] (hN : Group.IsSolvable N)
    (hN3 : ¬ 3 ∣ Nat.card N) (hsimple : IsSimpleGroup (L ⧸ N)) {E : Subgroup L}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) {K : Type*} [Field K]
    (h3 : (3 : K) ≠ 0) {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hV : Module.finrank K V ≤ 2) (ρ : L →* (V →ₗ[K] V)) : ∀ l, ρ l = 1 := by
  by_contra hne
  have hker : ρ.ker ≤ N := res1CentSL2_ker_le hN hsimple ρ (not_forall.1 hne)
  let ρ' : L →* (V ≃ₗ[K] V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).toMonoidHom.comp ρ.toHomUnits
  have hdet : ∀ l, LinearEquiv.det (ρ' l) = 1 := fun l =>
    CFSG.SectionRank.Ccomm.perfect_hom_eq_one (LinearEquiv.det.comp ρ') l
  haveI := hE.1
  let φ : E →* (V ≃ₗ[K] V) := ρ'.comp E.subtype
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxker : (x : L) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      refine LinearMap.ext fun v => ?_
      have h1 : ρ' (x : L) v = v := congrArg (fun f : V ≃ₗ[K] V => f v) hx
      exact h1
    exact Subtype.ext (res1CentSL2_eq_one hN3 (hker hxker) (hE.2 x x.2))
  have hcard : Nat.card φ.range = 9 := by
    rw [← hE9]
    exact (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm
  have hle : Nat.card φ.range ≤ 3 := by
    refine CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.card_le_three_of_det_eq_one h3 hV
      φ.range ?_ ?_ ?_
    · rintro _ ⟨x, rfl⟩
      have hx3 : x ^ 3 = 1 := Subtype.ext (hE.2 x x.2)
      rw [← map_pow, hx3, map_one]
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      rw [← map_mul, ← map_mul, mul_comm' x y]
    · rintro _ ⟨x, rfl⟩
      exact hdet x
  omega

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
