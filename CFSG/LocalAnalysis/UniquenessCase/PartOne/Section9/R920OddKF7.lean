module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddStrong
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddSigma
public import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7Use

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem exists_perfect_map_eq_top {A S : Type} [Group A] [Finite A] [Group S] [Group.IsPerfect S]
    (f : A →* S) (hf : Function.Surjective f) :
    ∃ P : Subgroup A, ⁅P, P⁆ = P ∧ P.map f = ⊤ := by
  obtain ⟨P, hP, hmin⟩ := Set.exists_min_image {P : Subgroup A | P.map f = ⊤}
    (fun P => Nat.card P) (Set.toFinite _)
    ⟨⊤, show (⊤ : Subgroup A).map f = ⊤ by rw [Subgroup.map_top, MonoidHom.range_eq_top.2 hf]⟩
  have hP' : P.map f = ⊤ := hP
  have hc : (⁅P, P⁆ : Subgroup A).map f = ⊤ := by
    rw [Subgroup.map_commutator, hP']
    exact Group.IsPerfect.commutator_eq_top (G := S)
  have hle : ⁅P, P⁆ ≤ P := Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem h₁ h₂) (P.inv_mem h₁)) (P.inv_mem h₂)
  exact ⟨P, Subgroup.eq_of_le_of_card_ge hle (hmin _ hc), hP'⟩

namespace SliceCore

variable {D : Data G} {L D₃ Y H : Subgroup G}

theorem isPerfect_bar2_opp (S : SliceCore D L D₃ Y H) : Group.IsPerfect (Bar2 (Opp 3 Y)) := by
  obtain ⟨e⟩ := S.nonempty_bar2_L_opp_equiv
  haveI : Group.IsPerfect (Bar2 L) := Group.isPerfect_def.mpr S.L_mem.2.2.1
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

theorem false_of_kf7Use (hKF7 : KF7Use D) (hSg : UC6S846.SigmaStd D) (S : SliceCore D L D₃ Y H)
    {p : ℕ} (hp : p ∈ D.sig) (hpX : p ∣ Nat.card (Bar2 (Opp 3 Y)))
    (hrank : 2 ≤ CFSG.Open.pRank p (H ⊓ D.M)) : False := by
  classical
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hXH : Opp 3 Y ≤ H := (opp_le 3 Y).trans S.Y_le_H
  have hKF := hKF7 p hp H
    ⟨hpp, hp2, S.isStronglyPEmbedded_of_mem_sig hSg hp, S.H_ne_top, S.not_H_le_M, by omega⟩
  obtain ⟨f, hf⟩ := exists_surjective_map_pPrimeCore_bar2 hpp hXH S.isSimpleGroup_bar2_opp hpX
  have hle : ((Opp 3 Y).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) ≤
      ((H ⊓ D.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) :=
    Subgroup.map_mono (Subgroup.comap_mono (le_inf hXH S.opp_le_M))
  rcases hKF with hsolv | ⟨-, hquot⟩
  · haveI : Group.IsSolvable ↥(((H ⊓ D.M).subgroupOf H).map
        (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) := hsolv
    haveI : Group.IsSolvable ↥(((Opp 3 Y).subgroupOf H).map
        (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    exact S.not_isSolvable_bar2_opp (solvable_of_surjective hf)
  · haveI := S.isPerfect_bar2_opp
    obtain ⟨P, hPperf, hPmap⟩ := exists_perfect_map_eq_top f hf
    let N := ((Opp 3 Y).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))
    let e := P.equivMapOfInjective N.subtype N.subtype_injective
    refine S.facts_opp.not_alt_five (hquot (P.map N.subtype)
      ((Subgroup.map_subtype_le P).trans hle) ?_ _ S.isSimpleGroup_bar2_opp
      ((f.comp P.subtype).comp e.symm.toMonoidHom) ?_)
    · rw [← Subgroup.map_commutator, hPperf]
    · intro s
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 (hPmap ▸ Subgroup.mem_top s)
      exact ⟨e ⟨a, ha⟩, by simp⟩

end SliceCore

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
