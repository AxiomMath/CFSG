module

public import CFSG.Milestones.ASVolI.C31.J4KWP0
public import CFSG.Quasithin.EmptyFaithful.E22NJ4
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocTransport

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

structure burnsideJ4NP_Hyp (R : Subgroup J) : Prop where
  p2 : IsPGroup 2 ↥R
  ne : R ≠ ⊥
  le : R ≤ P0
  syl : ∀ S : Subgroup J, IsPGroup 2 ↥S → S ≤ Subgroup.normalizer (R : Set J) →
    Nat.card ↥S ≤ Nat.card ↥(P0 ⊓ Subgroup.normalizer (R : Set J))
  max : ∀ Y : Subgroup J, IsPGroup 2 ↥Y → Y ≠ ⊥ →
    Subgroup.normalizer (R : Set J) ≤ Subgroup.normalizer (Y : Set J) →
    Subgroup.normalizer (Y : Set J) = Subgroup.normalizer (R : Set J)
  core : ∀ Y : Subgroup J, IsPGroup 2 ↥Y →
    Subgroup.normalizer (R : Set J) ≤ Subgroup.normalizer (Y : Set J) → Y ≤ R
  cent : Subgroup.centralizer (R : Set J) ≤ R
  np : ∀ g : J, ¬ P0.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (R : Set J)

theorem burnsideJ4NP_of_hyp
    (h : ∀ R : Subgroup J, burnsideJ4NP_Hyp R →
      ∃ g : J, Subgroup.normalizer (R : Set J) ≤
        CFSG.Quasithin.KGJ4.M4.map (MulAut.conj g).toMonoidHom) :
    burnsideJ4KW_MaxNonParabolicP0 := by
  intro R h1 h2 h3 h4 h5 h6 h7 h8
  exact h R ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

section Basic

variable {R : Subgroup J}

theorem burnsideJ4NP_z0_mem_cent
    (hR : burnsideJ4NP_Hyp R) :
    CFSG.Quasithin.J4Loc.z0 ∈ R ∧ CFSG.Quasithin.J4Loc.z0 ∈ Subgroup.centralizer (R : Set J) := by
  have hc : CFSG.Quasithin.J4Loc.z0 ∈ Subgroup.centralizer (R : Set J) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h := CFSG.Quasithin.E2P.J4Two.P0_le_centralizer (hR.le hr)
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    rw [CFSG.Quasithin.J4Loc.z0_eq]
    exact h
  exact ⟨hR.cent hc, hc⟩

theorem burnsideJ4NP_z0_sq :
    CFSG.Quasithin.J4Loc.z0 * CFSG.Quasithin.J4Loc.z0 = 1 :=
  eta_sq (elem_uJ j4Facts.mat) 1131

theorem burnsideJ4NP_zpowers_z0 :
    IsPGroup 2 ↥(Subgroup.zpowers CFSG.Quasithin.J4Loc.z0) ∧
      Subgroup.zpowers CFSG.Quasithin.J4Loc.z0 ≠ ⊥ := by
  have hsq := burnsideJ4NP_z0_sq
  have hne : CFSG.Quasithin.J4Loc.z0 ≠ 1 := CFSG.Quasithin.J4Loc.z0_ne_one j4Facts.mat
  have hord : orderOf CFSG.Quasithin.J4Loc.z0 = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]; exact hsq
    · exact hne
  refine ⟨?_, ?_⟩
  · apply IsPGroup.of_card
    rw [Nat.card_zpowers, hord]
    exact (pow_one 2).symm
  · intro h
    apply hne
    have : CFSG.Quasithin.J4Loc.z0 ∈ Subgroup.zpowers CFSG.Quasithin.J4Loc.z0 :=
      Subgroup.mem_zpowers _
    rw [h] at this
    exact (Subgroup.mem_bot.1 this)

theorem burnsideJ4NP_centralizer_le_normalizer_zpowers {G : Type*} [Group G] (x : G) :
    Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have hc : Commute g x := hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hconj : ∀ k : ℤ, g * x ^ k * g⁻¹ = x ^ k := by
    intro k
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, (hconj k).symm⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h2 : g * y * g⁻¹ = g * x ^ k * g⁻¹ := by
      rw [hconj k]
      exact hk.symm
    have h3 : y = x ^ k := mul_left_cancel (mul_right_cancel h2)
    exact h3.symm

end Basic

end CFSG.ASVolI
