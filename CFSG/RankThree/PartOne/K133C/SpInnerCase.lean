module

public import CFSG.RankThree.PartOne.K133C.SpModel
public import CFSG.RankThree.PartOne.K133C.SpInner
public import CFSG.RankThree.PartOne.N143X.Weights

public section

namespace CFSG.RankThree.PartOne.K133C

open Matrix CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.K133
  CFSG.RankThree.PartOne.N143X

set_option linter.unusedSectionVars false

variable {r : ℕ} {K : Type} [Field K] [CharP K 2]

theorem goodAction_sp_inner [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : 1 ≤ r)
    (hinj : Function.Injective (proj r K))
    (hZ : Subgroup.center (StatedProj (StatedSp r K)) = ⊥)
    {Ē : Subgroup (MulAut (StatedProj (StatedSp r K)))} (hE : IsElementaryAbelian p Ē)
    (hc : Nat.card Ē = p ^ 3) (hin : Ē ≤ inner (StatedProj (StatedSp r K))) :
    GoodAction p (StatedProj (StatedSp r K)) Ē := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, hr⟩⟩
  obtain ⟨A, hAe, hAc, hĒA⟩ := exists_pullback_inner hZ hE hin
  let ψ : StatedSp r K ≃* StatedProj (StatedSp r K) :=
    MulEquiv.ofBijective (proj r K) ⟨hinj, proj_surjective⟩
  let ι₁ : StatedProj (StatedSp r K) →* GL (Fin r ⊕ Fin r) K :=
    (StatedSp r K).subtype.comp ψ.symm.toMonoidHom
  have hι₁ : Function.Injective ι₁ := (StatedSp r K).subtype_injective.comp ψ.symm.injective
  have hι₁mem : ∀ t, ι₁ t ∈ isoGrp (formJ r K) := fun t =>
    mem_statedSp_iff_isoGrp.1 (ψ.symm t).2
  set AG : Subgroup (GL (Fin r ⊕ Fin r) K) := A.map ι₁ with hAG
  have hAGc : Nat.card AG = p ^ 3 := by
    rw [hAG, Subgroup.card_map_of_injective hι₁, hAc, hc]
  have hAGfin : Finite AG :=
    Nat.finite_of_card_ne_zero (by rw [hAGc]; exact pow_ne_zero 3 hp.ne_zero)
  have hAGe : IsElementaryAbelian p AG :=
    isElementaryAbelian_of_equiv (A.equivMapOfInjective ι₁ hι₁) hAe
  have hpK : (p : K) ≠ 0 := by
    intro h
    have h2 : (2 : ℕ) ∣ p := (CharP.cast_eq_zero_iff K 2 p).1 h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2).symm
  obtain ⟨P, hPAG, hPc, v, hv0, hPv⟩ := exists_plane_fixed hp hpK AG hAGe hAGc
  have hPJ : P ≤ isoGrp (formJ r K) := by
    intro h hh
    obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.1 (hPAG hh)
    exact hι₁mem t
  have hpow : ∀ h ∈ P, h ^ p = 1 := by
    intro h hh
    have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p AG)
      ⟨h, hPAG hh⟩
    simpa using congrArg Subtype.val this
  have hP1 : ∃ h ∈ P, h ≠ 1 := by
    by_contra hno
    push Not at hno
    have : P = ⊥ := (Subgroup.eq_bot_iff_forall P).2 hno
    rw [this, Subgroup.card_bot] at hPc
    have := Nat.one_lt_pow (n := 2) (by norm_num) hp.one_lt
    omega
  obtain ⟨S, hSJ, hS2, hSst, h, hh, s, hs, hne⟩ :=
    exists_moving_isoGrp hpK (formJ r K) formJ_transpose_two formJ_alt formJ_nondeg hv0 P hPJ hpow
      hPv hP1
  have hPrange : P ≤ ι₁.range := by
    intro h hh
    obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.1 (hPAG hh)
    exact ⟨t, rfl⟩
  have hPmap : (P.comap ι₁).map ι₁ = P := Subgroup.map_comap_eq_self hPrange
  have hPTc : Nat.card (P.comap ι₁) = p ^ 2 := by
    have h1 : Nat.card ((P.comap ι₁).map ι₁) = Nat.card (P.comap ι₁) :=
      Subgroup.card_map_of_injective hι₁
    rw [hPmap] at h1
    rw [← h1, hPc]
  have hPTA : P.comap ι₁ ≤ A := by
    intro t ht
    obtain ⟨a, haA, hat⟩ := Subgroup.mem_map.1 (hPAG ht)
    have : a = t := hι₁ hat
    rw [← this]
    exact haA
  have hconj : Function.Injective (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))) :=
    conj_injective_of_center_bot hZ
  right
  refine ⟨(P.comap ι₁).map (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))),
    ?_, ?_, S.comap ι₁, hS2.comap_of_injective ι₁ hι₁, ?_, ?_⟩
  · rw [hĒA]
    exact Subgroup.map_mono hPTA
  · rw [Subgroup.card_map_of_injective hconj, hPTc]
  · rintro _ ⟨t, ht, rfl⟩ u hu
    show ι₁ (t * u * t⁻¹) ∈ S
    rw [map_mul, map_mul, map_inv]
    exact hSst _ ht _ hu
  · obtain ⟨t, ht⟩ : ∃ t, ι₁ t = h := by
      obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.1 (hPAG hh)
      exact ⟨t, rfl⟩
    obtain ⟨u, hu⟩ : ∃ u, ι₁ u = s := by
      have hsJ := hSJ hs
      refine ⟨proj r K ⟨s, mem_statedSp_iff_isoGrp.2 hsJ⟩, ?_⟩
      show (((ψ.symm (proj r K ⟨s, mem_statedSp_iff_isoGrp.2 hsJ⟩) : StatedSp r K)) : GL _ K) = s
      have : ψ.symm (proj r K ⟨s, mem_statedSp_iff_isoGrp.2 hsJ⟩) =
          ⟨s, mem_statedSp_iff_isoGrp.2 hsJ⟩ := ψ.symm_apply_apply _
      rw [this]
    refine ⟨MulAut.conj t, Subgroup.mem_map_of_mem _ (by rw [Subgroup.mem_comap, ht]; exact hh), u,
      by rw [Subgroup.mem_comap, hu]; exact hs, ?_⟩
    intro heq
    apply hne
    have h1 : t * u * t⁻¹ = u := heq
    have h2 := congrArg ι₁ h1
    rw [map_mul, map_mul, map_inv, ht, hu] at h2
    exact h2

end CFSG.RankThree.PartOne.K133C
