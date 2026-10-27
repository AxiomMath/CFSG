module

public import CFSG.RankThree.GF2n.Tim79Main
public import CFSG.Open.StatedDefs
public import CFSG.Foundations
public import Certificates.Certificate43

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

@[expose] def cen (Q : Subgroup G) : Subgroup G := (Subgroup.center ↥Q).map Q.subtype

@[expose] def QB (B : Subgroup G) : Subgroup G :=
  inSubgroup generalizedFitting (Subgroup.normalizer (B : Set G))

@[expose] def LB (M Q B : Subgroup G) : Subgroup G := Q ⊔ (QB B ⊓ M)

@[expose] def Lgen (M L : Subgroup G) : Subgroup G :=
  ⨆ (m : G) (_ : m ∈ M), conjSubgroup m L

@[expose] def IsTIMod (M Q L : Subgroup G) : Prop :=
  ∀ m ∈ M, L ⊓ conjSubgroup m L = Q ∨ L ⊓ conjSubgroup m L = L

@[expose] def Rt (M L : Subgroup G) (t : G) : Subgroup G :=
  ⨆ (m : G) (_ : m ∈ M) (_ : t ∈ conjSubgroup m L), conjSubgroup m L

@[expose] def Nt (M L : Subgroup G) (t : G) : Subgroup G := inSubgroup (pCore 2) (Rt M L t)

@[expose] def H0 (M Z : Subgroup G) : Subgroup G := M ⊓ Subgroup.centralizer (Z : Set G)

@[expose] def QuotIso (S N : Subgroup G) (X : Type) [Group X] : Prop :=
  ∃ _ : (N.subgroupOf S).Normal, Nonempty (↥S ⧸ N.subgroupOf S ≃* X)

@[expose] def CentTrivial (M Q Z S : Subgroup G) : Prop :=
  ∀ h ∈ H0 M Z, (∀ x ∈ S, ⁅h, x⁆ ∈ Q) → h ∈ Q

structure StrothHyp (M Q Z : Subgroup G) : Prop where
  o2 : pCore 2 G = ⊥
  maxLocal : IsMaximalTwoLocal M
  fitting : generalizedFitting M = pCore 2 M
  hQ : Q = inSubgroup (pCore 2) M
  hZ : Z = cen Q
  cp : ∃ n k : ℕ, Nat.card Z = 2 ^ n ∧ Tim79.IsCentralProductOfL3 Q Z n k
  q4 : 4 ≤ Nat.card Z
  maxAb : Maximal (fun U : Subgroup G => U ≤ M ∧ M ≤ Subgroup.normalizer (U : Set G) ∧
    IsMulCommutative U) Z
  ti : IsTI Z
  notWC : ¬ WeaklyClosedIn Z Q
  gen : Q = ⨆ (g : G) (_ : conjSubgroup g Z ≤ Q), conjSubgroup g Z

theorem cen_eq (Q : Subgroup G) : cen Q = Q ⊓ Subgroup.centralizer (Q : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    have := Subgroup.mem_center_iff.mp hy ⟨z, hz⟩
    exact congrArg Subtype.val this
  · rintro ⟨hxQ, hxC⟩
    refine ⟨⟨x, hxQ⟩, Subgroup.mem_center_iff.mpr fun z => ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC z z.2)

theorem stroth_hyp_of_hyp79 [Finite G] {M V Q : Subgroup G}
    (ho : pCore 2 G = ⊥) (H : Tim79.Hyp79 M V Q) : StrothHyp M Q V := by
  obtain ⟨n, k, hn, hcp⟩ := tim79 G M V Q H
  refine ⟨ho, H.maxLocal, H.fitting, H.hQ, ?_, ⟨n, k, hn, hcp⟩, H.q4, H.maxAb, H.ti, ?_, H.gen⟩
  · rw [cen_eq]
    exact H.special.2.1.symm
  · rintro ⟨-, hwc⟩
    obtain ⟨g, hgV, hgQ⟩ := H.exists_opposite
    exact hgV (hwc g hgQ)

open CFSG.GH74.GLS.Bg.TwoGroups in
theorem sq_eq_one_of_cp {Q Z : Subgroup G} {n k : ℕ} (h : Tim79.IsCentralProductOfL3 Q Z n k) :
    ∀ x ∈ Z, x ^ 2 = 1 := by
  obtain ⟨hk, D, hDQ, hDL, hDZ, hDc, hDsup⟩ := h
  intro x hx
  rw [← hDZ ⟨0, hk⟩] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨e⟩ := hDL ⟨0, hk⟩
  have hey : e y ∈ Subgroup.center (UT3 (GaloisField 2 n)) := by
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    obtain ⟨y', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hy y']
  obtain ⟨ha, hb⟩ := (Tim79.ut3_mem_center_iff _).mp hey
  have h2 : e (y ^ 2) = 1 := by
    rw [map_pow, pow_two]
    ext <;> simp [UT3.mul_def, UT3.one_def, ha, hb, CharTwo.add_self_eq_zero]
  have : y ^ 2 = 1 := e.injective (h2.trans (map_one e).symm)
  have := congrArg Subtype.val this
  simpa using this

theorem StrothHyp.toHyp79 [Finite G] {M Q Z : Subgroup G} (H : StrothHyp M Q Z) :
    Tim79.Hyp79 M Z Q := by
  obtain ⟨n, k, -, hcp⟩ := H.cp
  have hZQ : Z ≤ Q := by
    rw [H.hZ]
    exact Subgroup.map_subtype_le _
  refine ⟨H.maxLocal, H.fitting, H.maxAb, sq_eq_one_of_cp hcp, H.ti, H.q4, H.hQ, H.gen, ?_⟩
  intro hQZ
  apply H.notWC
  refine ⟨hZQ, fun g hg => ?_⟩
  rw [hQZ] at hg
  exact Subgroup.eq_of_le_of_card_ge hg (by rw [card_conjSubgroup])

end CFSG.RankThree.GF2n.Stroth80
