module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65X0Card
public import CFSG.GroupTheory.SupCommute
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup
open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem card_sup_eq_nine_of_card_three_of_ne {X Z : Subgroup G}
    (hXcard : Nat.card X = 3) (hZcard : Nat.card Z = 3) (hXneZ : X ≠ Z)
    (hcomm : ∀ x ∈ X, ∀ z ∈ Z, x * z = z * x) :
    Nat.card ↥(X ⊔ Z) = 9 := by
  have hXZbot : X ⊓ Z = ⊥ := by
    by_contra hne
    haveI : Nontrivial ↥(X ⊓ Z) := (Subgroup.nontrivial_iff_ne_bot (X ⊓ Z)).mpr hne
    have hgt : 1 < Nat.card ↥(X ⊓ Z) := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    have hdvd : Nat.card ↥(X ⊓ Z) ∣ 3 := by
      simpa only [hXcard] using
        Subgroup.card_dvd_of_le (inf_le_left : X ⊓ Z ≤ X)
    have hcard : Nat.card ↥(X ⊓ Z) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · omega
      · exact h
    have hXleZ : X ≤ Z := by
      have hinf : X ⊓ Z = X :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, hXcard])
      rw [← hinf]
      exact inf_le_right
    exact hXneZ (Subgroup.eq_of_le_of_card_ge hXleZ (by rw [hZcard, hXcard]))
  calc Nat.card ↥(X ⊔ Z) = Nat.card X * Nat.card Z :=
        CFSG.card_sup_eq_mul_of_commute X Z hcomm hXZbot
    _ = 9 := by rw [hXcard, hZcard]

theorem psi_mk'_eq_self_of_commutator_eq_bot {L E Q : Subgroup G}
    (hE : E ≤ Subgroup.normalizer (L : Set G))
    (hQE : ⁅Q, E⁆ = ⊥) (e : ↥E) {y : ↥L} (hy : (y : G) ∈ Q) :
    psi hE e (QuotientGroup.mk' (CFSG.pCore 2 ↥L) y) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥L) y := by
  have hQcent : Q ≤ Subgroup.centralizer ((E : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQE
  have hcomm : (e : G) * (y : G) = (y : G) * (e : G) :=
    Subgroup.mem_centralizer_iff.mp (hQcent hy) (e : G) e.2
  have hcoe : ((Subgroup.normalizerMonoidHom L (Subgroup.inclusion hE e) y : ↥L) : G) =
      (y : G) := by
    rw [CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_mk_coe, Subgroup.coe_inclusion,
      hcomm, mul_assoc, mul_inv_cancel, mul_one]
  rw [psi_apply, QuotientGroup.mk'_apply,
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_mk]
  exact congrArg QuotientGroup.mk (Subtype.ext hcoe)

theorem card_range_eq_three_of_conj_mem {L X Z : Subgroup G}
    (hEnorm : X ⊔ Z ≤ Subgroup.normalizer (L : Set G))
    (hXcard : Nat.card X = 3) (hZcard : Nat.card Z = 3) (hXneZ : X ≠ Z)
    (hcomm : ∀ x ∈ X, ∀ z ∈ Z, x * z = z * x)
    {C : Subgroup (Bar2 L)}
    (hCQ : ∀ e : ↥(X ⊔ Z), ∃ g ∈ C, psi hEnorm e = MulAut.conj g)
    (hCcard : Nat.card C = 3)
    (hZnotle : ¬ Z ≤ centralizerBar (X ⊔ Z) L) :
    Nat.card (psi hEnorm).range = 3 := by
  classical
  have hEcard : Nat.card ↥(X ⊔ Z) = 9 :=
    card_sup_eq_nine_of_card_three_of_ne hXcard hZcard hXneZ hcomm
  have hrange_le : (psi hEnorm).range ≤ C.map (MulAut.conj : Bar2 L →* MulAut (Bar2 L)) := by
    rintro y ⟨e, rfl⟩
    obtain ⟨g, hgC, hg⟩ := hCQ e
    exact Subgroup.mem_map.mpr ⟨g, hgC, hg.symm⟩
  have hle3 : Nat.card (psi hEnorm).range ≤ 3 := by
    calc Nat.card (psi hEnorm).range
        ≤ Nat.card (C.map (MulAut.conj : Bar2 L →* MulAut (Bar2 L))) :=
          Subgroup.card_le_of_le hrange_le
      _ ≤ Nat.card C :=
          Nat.le_of_dvd (Nat.card_pos (α := C))
            (Subgroup.card_map_dvd (H := C) (f := MulAut.conj))
      _ = 3 := hCcard
  have hne3 : Nat.card (psi hEnorm).range ≠ 1 := by
    obtain ⟨z, hzZ, hznot⟩ := SetLike.not_le_iff_exists.mp hZnotle
    have hzE : z ∈ X ⊔ Z := Subgroup.mem_sup_right hzZ
    have hzne : psi hEnorm (⟨z, hzE⟩ : ↥(X ⊔ Z)) ≠ 1 := by
      intro h1
      exact hznot ((mem_ker_iff_centralizerBar hEnorm ⟨z, hzE⟩).mp h1)
    intro hcard
    have hbot : (psi hEnorm).range = ⊥ := (Subgroup.card_eq_one).mp hcard
    have hmem : psi hEnorm (⟨z, hzE⟩ : ↥(X ⊔ Z)) ∈ (psi hEnorm).range := ⟨_, rfl⟩
    rw [hbot] at hmem
    exact hzne (Subgroup.mem_bot.mp hmem)
  have hdvd : Nat.card (psi hEnorm).range ∣ 9 := by
    have h := Subgroup.card_range_dvd (psi hEnorm)
    rwa [hEcard] at h
  set n := Nat.card (psi hEnorm).range
  have hnpos : 0 < n := Nat.card_pos
  have hnle : n ≤ 3 := hle3
  have hnne : n ≠ 1 := hne3
  have hndvd : n ∣ 9 := hdvd
  interval_cases n
  · exact absurd rfl hnne
  · norm_num at hndvd
  · rfl

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
