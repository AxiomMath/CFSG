module

public import CFSG.Assembly.OrderReductions.PrimePart
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.StrictThetaGrowth

open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.OrderReductions.PrimePart

universe u

variable {G : Type u} [Group G] [Finite G]

structure Admissible (H : Subgroup G) (z : G) (beta : rightCosetSpace H)
    (p : ℕ) (X A : Subgroup G) (v : G) : Prop where
  subgroup_ne_bot : X ≠ ⊥
  subgroup_le_point : X ≤ H
  distinguished_invariant : rightConjugate X z = X
  flip : v ∈ rightPairFlipFiber H z beta
  flip_normalizes : v ∈ Subgroup.normalizer (X : Set G)
  hull_rank : 2 ≤ CFSG.Open.pRank 2
    (Subgroup.closure (conjugacyWithin (Subgroup.normalizer (X : Set G)) z))
  witness_le : A ≤ Subgroup.normalizer (X : Set G) ⊓ pairOddCore H beta
  witness_prime : IsPGroup p A
  witness_distinguished_invariant : rightConjugate A z = A
  flip_normalizes_witness : v ∈ Subgroup.normalizer (A : Set G)
  witness_noncentral : ¬ A ≤ Subgroup.centralizer ({z} : Set G)

theorem original_sylow_admissible
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime)
    (P : Sylow p ((CFSG.oddCore (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype))
    (hPz : rightConjugate ((P : Subgroup _).map
      ((CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype).subtype) z =
      (P : Subgroup _).map ((CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype).subtype)
    (hnoncentral : ¬ (P : Subgroup _).map
      ((CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype).subtype ≤
      Subgroup.centralizer ({z} : Set G))
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta)
    (htP : t ∈ Subgroup.normalizer ((P : Subgroup _).map
      ((CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype).subtype : Set G))
    (hrank : 2 ≤ CFSG.Open.pRank 2 (Subgroup.closure
      (conjugacyWithin (Subgroup.normalizer ((P : Subgroup _).map
        ((CFSG.oddCore (triplePointStabilizer H z beta)).map
          (triplePointStabilizer H z beta).subtype).subtype : Set G)) z))) :
    let V := (CFSG.oddCore (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype
    let X := (P : Subgroup V).map V.subtype
    Admissible H z beta p X X t := by
  let V := (CFSG.oddCore (triplePointStabilizer H z beta)).map
    (triplePointStabilizer H z beta).subtype
  let X := (P : Subgroup V).map V.subtype
  have hXV : X ≤ V := Subgroup.map_subtype_le _
  have hVE : V ≤ triplePointStabilizer H z beta := Subgroup.map_subtype_le _
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hV : V = pairOddCore H beta ⊓ triplePointStabilizer H z beta :=
    triple_odd_core_eq_pair_intersection h.local_datum S hzS hzcenter beta hbeta
  have hXJ : X ≤ pairOddCore H beta := by
    rw [hV] at hXV
    exact hXV.trans inf_le_left
  have hXne : X ≠ ⊥ := by
    intro hbot
    apply hnoncentral
    rw [show (P : Subgroup V).map V.subtype = X from rfl, hbot]
    exact bot_le
  let : Fact p.Prime := ⟨hp⟩
  exact ⟨hXne, (hXV.trans hVE).trans
    (inf_le_left.trans (pairPointStabilizer_le_point H beta)), hPz, ht, htP, hrank,
    le_inf Subgroup.le_normalizer hXJ, P.isPGroup'.map V.subtype, hPz, htP,
    hnoncentral⟩

theorem exists_maximal_admissible
    (H : Subgroup G) (z : G) (beta : rightCosetSpace H) (p : ℕ)
    (hne : ∃ X A v, Admissible H z beta p X A v) :
    ∃ X A v, Admissible H z beta p X A v ∧
      ∀ X₁ A₁ v₁, Admissible H z beta p X₁ A₁ v₁ →
        primePart p (Nat.card
          (Subgroup.normalizer (X₁ : Set G) ⊓ pairOddCore H beta : Subgroup G)) ≤
          primePart p (Nat.card
            (Subgroup.normalizer (X : Set G) ⊓ pairOddCore H beta : Subgroup G)) := by
  let candidates : Set (Subgroup G × Subgroup G × G) :=
    {d | Admissible H z beta p d.1 d.2.1 d.2.2}
  have hnonempty : candidates.Nonempty := by
    obtain ⟨X, A, v, hmember⟩ := hne
    exact ⟨(X, A, v), hmember⟩
  obtain ⟨d, hd, hmax⟩ := Set.exists_max_image candidates
    (fun d => primePart p (Nat.card
      (Subgroup.normalizer (d.1 : Set G) ⊓ pairOddCore H beta : Subgroup G)))
    (Set.toFinite _) hnonempty
  exact ⟨d.1, d.2.1, d.2.2, hd, fun X₁ A₁ v₁ hmember =>
    hmax (X₁, A₁, v₁) hmember⟩

end CFSG.ShultStronglyClosedTI.StrictThetaGrowth
