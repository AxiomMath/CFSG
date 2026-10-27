module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
import CFSG.LocalAnalysis.WeakClosure81.SevenKFactsThree
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.SectionRank.AlternatingCover
public import CFSG.Quasithin.Background.A3Structure36AQuasi
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.WeakClosure81.A6Case

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

theorem isPerfect_of_isPerfect_center_quotient {X : Type} [Group X] [Finite X]
    (hperf : Group.IsPerfect (X ⧸ Subgroup.center X))
    (hodd : Odd (Nat.card (Subgroup.center X)))
    {S : Subgroup X} (hS : IsPGroup 2 S)
    (hncl : Subgroup.normalClosure (S : Set X) = ⊤) :
    Group.IsPerfect X := by
  let Z : Subgroup X := Subgroup.center X
  let N : Subgroup X := commutator X
  have hq : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  have hmap : N.map (QuotientGroup.mk' Z) = ⊤ := by
    have h1 : N.map (QuotientGroup.mk' Z) = commutator (X ⧸ Z) := by
      change Subgroup.map (QuotientGroup.mk' Z) ⁅(⊤ : Subgroup X), ⊤⁆ =
        ⁅(⊤ : Subgroup (X ⧸ Z)), ⊤⁆
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hq]
    rw [h1, Group.isPerfect_def.mp hperf]
  have hsup : N ⊔ Z = ⊤ := by
    rw [sup_comm, ← QuotientGroup.comap_map_mk' Z N, hmap, Subgroup.comap_top]
  have hSmap : S.map (QuotientGroup.mk' N) = ⊤ := by
    have h1 : (Subgroup.normalClosure (S : Set X)).map (QuotientGroup.mk' N) = ⊤ := by
      rw [hncl, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
    rw [Subgroup.map_normalClosure (S : Set X) (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N), ← Subgroup.coe_map] at h1
    letI : (S.map (QuotientGroup.mk' N)).Normal := Subgroup.normal_of_isMulCommutative _
    rwa [Subgroup.normalClosure_eq_self] at h1
  have hquot : IsPGroup 2 (X ⧸ N) := by
    have h2 := hS.map (QuotientGroup.mk' N)
    rw [hSmap] at h2
    exact h2.of_equiv Subgroup.topEquiv
  have hdvd : Nat.card (X ⧸ N) ∣ Nat.card Z := by
    refine Subgroup.card_dvd_of_surjective
      (f := (QuotientGroup.mk' N).comp Z.subtype) ?_
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hx : x ∈ N ⊔ Z := by rw [hsup]; exact Subgroup.mem_top x
    obtain ⟨a, ha, z, hz, hxz⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    refine ⟨⟨z, hz⟩, ?_⟩
    rw [← hxz]
    simp [ha]
  have hoddquot : Odd (Nat.card (X ⧸ N)) := Odd.of_dvd_nat hodd hdvd
  have hcard : Nat.card (X ⧸ N) = 1 := by
    obtain ⟨k, hk⟩ := hquot.exists_card_eq
    rw [hk] at hoddquot
    rcases k with _ | k
    · simpa using hk
    · exfalso
      exact hoddquot.not_two_dvd_nat (dvd_pow_self 2 (Nat.succ_ne_zero k))
  have hNtop : N = ⊤ := by
    haveI : Subsingleton (X ⧸ N) := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact QuotientGroup.subsingleton_iff.mp inferInstance
  exact Group.isPerfect_def.mpr hNtop

theorem card_center_eq_one_or_three (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X}
    (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6)) :
    Nat.card (Subgroup.center X) = 1 ∨ Nat.card (Subgroup.center X) = 3 := by
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  have hO2 : CFSG.pCore 2 X = ⊥ := pCore_eq_bot_of_isBarMap hφ
  have hodd : Odd (Nat.card (Subgroup.center X)) := CFSG.Quasithin.A36A.odd_card_center hO2
  let π : X →* alternatingGroup (Fin 6) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hπ : Function.Surjective π :=
    e.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center X))
  have hker : π.ker = Subgroup.center X := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk x) = 1 ↔ x ∈ Subgroup.center X
    rw [e.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hperfZ : Group.IsPerfect (X ⧸ Subgroup.center X) := by
    haveI : Group.IsPerfect (alternatingGroup (Fin 6)) :=
      Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hperf : Group.IsPerfect X :=
    isPerfect_of_isPerfect_center_quotient hperfZ hodd
      (isElemAbelian_barSub h.elemAbelian φ).isPGroup
      (normalClosure_barSub_eq_top h hφ)
  haveI : Group.IsPerfect X := hperf
  have hcov := (CFSG.SectionRank.alternating_small_odd_cover_bound (n := 6)
    (by norm_num) (by norm_num) π hπ (le_of_eq hker)
    (by rw [hker]; exact hodd)).2 (Or.inl rfl)
  rwa [hker] at hcov

theorem exists_isBarMap_alt6 {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X}
    (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6))
    (h1 : Nat.card (Subgroup.center X) = 1) :
    ∃ ψ : ↥(kSub V H E) →* alternatingGroup (Fin 6),
      IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) ψ := by
  have hZ : Subgroup.center X = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
  refine ⟨e.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center X)).comp φ), ?_⟩
  constructor
  · exact e.surjective.comp ((QuotientGroup.mk'_surjective _).comp hφ.surjective)
  · intro k
    change e (QuotientGroup.mk (φ k)) = 1 ↔ (k : G) ∈ pCoreOf 2 (kSub V H E)
    rw [e.map_eq_one_iff, QuotientGroup.eq_one_iff, hZ, Subgroup.mem_bot]
    exact hφ.ker_iff k

end CFSG.LocalAnalysis.WeakClosure81.A6Case

end
