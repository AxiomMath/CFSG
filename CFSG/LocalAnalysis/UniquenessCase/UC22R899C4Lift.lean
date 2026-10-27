module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BBar
import CFSG.LocalAnalysis.UniquenessCase.UC6S846a
import CFSG.RankThree.PartOne.S12.Sec1511Y2Quot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22r899c4_exists_normalizing_copy {M X : Subgroup G} {p r : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hr : r.Prime) (hr2 : r ≠ 2) (hXM : X ≤ M) (hX : IsPGroup r X)
    {D : Subgroup (Bar2 M)} (hD : IsElemAbelian p D)
    (hDN : D ≤ normalizer (barImage M X : Set (Bar2 M))) :
    ∃ A : Subgroup G, A ≤ M ⊓ normalizer (X : Set G) ∧ IsElemAbelian p A ∧
      Nat.card A = Nat.card D ∧ ∀ a : ↥M, (a : G) ∈ A → uc22p21cPi M a ∈ D := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hPn : (CFSG.pCore 2 ↥M).Normal := CFSG.pCore_normal
  have hT : IsPGroup r (X.subgroupOf M) := hX.comap_of_injective M.subtype M.subtype_injective
  have hO : ¬ r ∣ Nat.card (CFSG.pCore 2 ↥M) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hk]
    exact fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  set Y : Subgroup ↥M := normalizer ((X.subgroupOf M : Subgroup ↥M) : Set ↥M) ⊓
    D.comap (uc22p21cPi M) with hY
  let f : ↥Y →* ↥D := ((uc22p21cPi M).comp Y.subtype).codRestrict D fun y => y.2.2
  have hf : Function.Surjective f := by
    rintro ⟨d, hd⟩
    obtain ⟨n, hn, hnd⟩ := CFSG.RankThree.PartOne.Sec1511.exists_lift_normalizer hT hO (hDN hd)
    exact ⟨⟨n, hn, show uc22p21cPi M n ∈ D by rw [← hnd] at hd; exact hd⟩, Subtype.ext hnd⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p ↥Y))
  have hPD : (P : Subgroup ↥Y).map f = ⊤ :=
    ((P.mapSurjective hf).is_maximal' (hD.isPGroup.to_subgroup ⊤) le_top).symm
  set Q : Subgroup ↥M := (P : Subgroup ↥Y).map Y.subtype with hQ
  have hQY : Q ≤ Y := Subgroup.map_subtype_le _
  have hdisj : Disjoint Q (uc22p21cPi M).ker := by
    refine Subgroup.disjoint_def.2 fun {x} hxQ hxk => ?_
    obtain ⟨k, hk⟩ := (P.isPGroup'.map Y.subtype) ⟨x, hxQ⟩
    exact uc22r8100b_eq_one_of_mem_pCore
      ((QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hxk)) (hp.odd_of_ne_two hp2).pow
      (by simpa using congrArg Subtype.val hk)
  have hQD : Q.map (uc22p21cPi M) = D := by
    refine le_antisymm ?_ fun d hd => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact (hQY hx).2
    · have hd' : (⟨d, hd⟩ : ↥D) ∈ (P : Subgroup ↥Y).map f := by
        rw [hPD]
        exact Subgroup.mem_top _
      obtain ⟨y, hyP, hy⟩ := hd'
      exact ⟨y, ⟨y, hyP, rfl⟩, congrArg Subtype.val hy⟩
  have hQel : IsElemAbelian p Q :=
    UC6S846.isElemAbelian_of_disjoint_ker (uc22p21cPi M) Q hdisj (by rw [hQD]; exact hD)
  refine ⟨Q.map M.subtype, ?_, hQel.map M.subtype, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxN : x ∈ (normalizer (X : Set G)).subgroupOf M := by
      rw [Subgroup.subgroupOf_normalizer_eq hXM]
      exact (hQY hx).1
    exact Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_subgroupOf.1 hxN⟩
  · rw [Subgroup.card_map_of_injective M.subtype_injective,
      ← UC6S846.card_map_of_disjoint_ker _ Q hdisj, hQD]
  · rintro a ⟨x, hx, hxa⟩
    obtain rfl : x = a := Subtype.ext hxa
    exact (hQY hx).2

end CFSG.LocalAnalysis.UniquenessCase.UC22
