module

public import CFSG.Quasithin.Background.RonanF13Defs
public import CFSG.GroupTheory.SolvableHallNodes
public import CFSG.Quasithin.Background.F1Basic

public section

namespace CFSG.Quasithin.RonanF13

universe u

section Index

variable {G : Type u} [Group G]

theorem relIndex_inf_eq_of_normal {Γ : Type u} [Group Γ] [Finite Γ] (N D : Subgroup Γ) [N.Normal] :
    (D ⊓ N).relIndex N = D.relIndex (D ⊔ N) := by
  have h1 : N.relIndex (D ⊔ N) = N.relIndex D := Subgroup.relIndex_sup_right D N
  have h2 : (D ⊓ N).relIndex N * N.relIndex (D ⊔ N) = (D ⊓ N).relIndex (D ⊔ N) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_right
  have h3 : (D ⊓ N).relIndex D * D.relIndex (D ⊔ N) = (D ⊓ N).relIndex (D ⊔ N) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_left
  have h4 : N.relIndex D = (D ⊓ N).relIndex D := (Subgroup.inf_relIndex_left D N).symm
  have hc : (D ⊓ N).relIndex D ≠ 0 := by
    haveI : Finite ↥D := inferInstance
    exact Subgroup.index_ne_zero_of_finite
  rw [h1, h4] at h2
  have h5 : (D ⊓ N).relIndex D * (D ⊓ N).relIndex N = (D ⊓ N).relIndex D * D.relIndex (D ⊔ N) := by
    rw [mul_comm, h2, h3]
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hc) h5

theorem relIndex_inf_dvd {N D B : Subgroup G} [Finite ↥B] (hNB : N ≤ B)
    (hBN : B ≤ Subgroup.normalizer (N : Set G)) :
    (D ⊓ N).relIndex N ∣ D.relIndex B := by
  haveI : (N.subgroupOf B).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNB).mpr hBN
  have h1 := relIndex_inf_eq_of_normal (N.subgroupOf B) (D.subgroupOf B)
  have h2 : ((D.subgroupOf B) ⊓ (N.subgroupOf B)).relIndex (N.subgroupOf B) =
      (D ⊓ N).relIndex N := by
    have : (D.subgroupOf B) ⊓ (N.subgroupOf B) = (D ⊓ N).subgroupOf B := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [this, Subgroup.relIndex_subgroupOf hNB]
  have h3 : (D.subgroupOf B).relIndex (D.subgroupOf B ⊔ N.subgroupOf B) ∣ D.relIndex B := by
    have := Subgroup.relIndex_mul_relIndex (D.subgroupOf B) (D.subgroupOf B ⊔ N.subgroupOf B) ⊤
      le_sup_left le_top
    have h4 : D.relIndex B = (D.subgroupOf B).relIndex ⊤ := by
      rw [Subgroup.relIndex_top_right]; rfl
    rw [h4]
    exact Dvd.intro _ this
  rw [h2] at h1
  rw [h1]
  exact h3

end Index

section Hall

variable {G : Type u} [Group G]

open CFSG.QuasithinUnique

@[expose] def HallTwoPrime (D X : Subgroup G) : Prop :=
  D ≤ X ∧ Odd (Nat.card D) ∧ ∃ k : ℕ, D.relIndex X = 2 ^ k

theorem exists_hallTwoPrime (B : Subgroup G) [Finite ↥B] (hB : Group.IsSolvable ↥B) :
    ∃ D : Subgroup G, HallTwoPrime D B := by
  obtain ⟨H, hH⟩ := CFSG.SolvableHall.solvable_hall_existence (G := ↥B) hB
    {p : Nat.Primes | p.val ≠ 2}
  refine ⟨H.map B.subtype, Subgroup.map_subtype_le H, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective B.subtype_injective]
    by_contra hnot
    have h2 : 2 ∣ Nat.card H := by
      rcases Nat.even_or_odd (Nat.card H) with he | ho
      · exact even_iff_two_dvd.mp he
      · exact absurd ho hnot
    have := hH.p_in_pi_of_p_dvd_card ⟨2, Nat.prime_two⟩ h2
    exact this rfl
  · have hsub : (H.map B.subtype).subgroupOf B = H :=
      Subgroup.comap_map_eq_self_of_injective B.subtype_injective H
    have hidx : (H.map B.subtype).relIndex B = H.index := by
      rw [Subgroup.relIndex, hsub]
    have hne : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    refine ⟨H.index.primeFactorsList.length, ?_⟩
    rw [hidx]
    refine Nat.eq_prime_pow_of_unique_prime_dvd hne (fun {d} hd hdvd => ?_)
    by_contra hne2
    exact hH.p_in_pi_of_p_dvd_index ⟨d, hd⟩ hdvd hne2

theorem HallTwoPrime.inf {B N D : Subgroup G} [Finite ↥B] (hNB : N ≤ B)
    (hBN : B ≤ Subgroup.normalizer (N : Set G)) (hD : HallTwoPrime D B) :
    HallTwoPrime (D ⊓ N) N := by
  obtain ⟨hDB, hodd, k, hk⟩ := hD
  refine ⟨inf_le_right, ?_, ?_⟩
  · exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left)
  · have h1 := relIndex_inf_dvd (D := D) hNB hBN
    rw [hk] at h1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    exact ⟨j, hj⟩

theorem sup_eq_of_hallTwoPrime {T B L D : Subgroup G} (hTB : T ≤ B) (hBL : B ≤ L)
    (hT : ¬ 2 ∣ T.relIndex L) (hD : HallTwoPrime D B) : T ⊔ D = B := by
  obtain ⟨hDB, -, k, hk⟩ := hD
  have hDE : D ≤ T ⊔ D := le_sup_right
  have hEB : T ⊔ D ≤ B := sup_le hTB hDB
  have h1 : (T ⊔ D).relIndex B ∣ 2 ^ k := by
    rw [← hk, ← Subgroup.relIndex_mul_relIndex D (T ⊔ D) B hDE hEB]
    exact dvd_mul_left _ _
  have h2 : (T ⊔ D).relIndex B ∣ T.relIndex L := by
    rw [← Subgroup.relIndex_mul_relIndex T B L hTB hBL,
      ← Subgroup.relIndex_mul_relIndex T (T ⊔ D) B le_sup_left hEB]
    exact ⟨T.relIndex (T ⊔ D) * B.relIndex L, by ring⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rw [hj] at h2
  have hj0 : j = 0 := by
    by_contra hne
    exact hT ((dvd_pow_self 2 hne).trans h2)
  have hone : (T ⊔ D).relIndex B = 1 := by rw [hj, hj0, pow_zero]
  exact le_antisymm hEB (Subgroup.relIndex_eq_one.mp hone)

end Hall

section Setup

variable {G : Type u} [Group G]

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Open

structure F13Setup (L1 L2 S : Subgroup G) : Prop where
  finS : Finite ↥S
  pS : IsPGroup 2 S
  finL1 : Finite ↥L1
  finL2 : Finite ↥L2
  syl1 : IsSylowTwoOf (S ⊓ L1) L1
  syl2 : IsSylowTwoOf (S ⊓ L2) L2
  comm1 : ∀ x ∈ borelOf L1 S, ∀ y ∈ borelOf L1 S, x * y * x⁻¹ * y⁻¹ ∈ S ⊓ L1
  comm2 : ∀ x ∈ borelOf L2 S, ∀ y ∈ borelOf L2 S, x * y * x⁻¹ * y⁻¹ ∈ S ⊓ L2
  b2_le_nL1 : borelOf L2 S ≤ Subgroup.normalizer (L1 : Set G)
  b1_le_nL2 : borelOf L1 S ≤ Subgroup.normalizer (L2 : Set G)
  pcore1 : pCoreOf 2 L1 ≤ S ⊓ L1
  pcore2 : pCoreOf 2 L2 ≤ S ⊓ L2
  b2_le_nb1 : borelOf L2 S ≤ Subgroup.normalizer (borelOf L1 S : Set G)
  b1_le_nb2 : borelOf L1 S ≤ Subgroup.normalizer (borelOf L2 S : Set G)
  s_le_nb1 : S ≤ Subgroup.normalizer (borelOf L1 S : Set G)
  s_le_nb2 : S ≤ Subgroup.normalizer (borelOf L2 S : Set G)
  bigB_le_ns1 : borelOf L1 S ⊔ borelOf L2 S ⊔ S ≤ Subgroup.normalizer ((S ⊓ L1 : Subgroup G) : Set G)
  bigB_le_ns2 : borelOf L1 S ⊔ borelOf L2 S ⊔ S ≤ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G)
  solvable : Group.IsSolvable ↥(borelOf L1 S ⊔ borelOf L2 S ⊔ S)

namespace F13Setup

variable {L1 L2 S : Subgroup G} (h : F13Setup L1 L2 S)

include h

theorem b1_fin : Finite ↥(borelOf L1 S) :=
  have := h.finL1
  Finite.of_injective (Subgroup.inclusion (F1.borelOf_le L1 S)) (Subgroup.inclusion_injective _)

theorem b2_fin : Finite ↥(borelOf L2 S) :=
  have := h.finL2
  Finite.of_injective (Subgroup.inclusion (F1.borelOf_le L2 S)) (Subgroup.inclusion_injective _)

theorem decomp {x : G} (hx : x ∈ borelOf L1 S ⊔ borelOf L2 S ⊔ S) :
    ∃ b1 ∈ borelOf L1 S, ∃ b2 ∈ borelOf L2 S, ∃ s ∈ S, x = b1 * b2 * s := by
  have hS : S ≤ Subgroup.normalizer ((borelOf L1 S ⊔ borelOf L2 S : Subgroup G) : Set G) :=
    F1.le_normalizer_sup h.s_le_nb1 h.s_le_nb2
  obtain ⟨a, ha, s, hs, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hS).mp hx
  obtain ⟨b1, hb1, b2, hb2, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes h.b2_le_nb1).mp ha
  exact ⟨b1, hb1, b2, hb2, s, hs, rfl⟩

theorem fin_bigB : Finite ↥(borelOf L1 S ⊔ borelOf L2 S ⊔ S) := by
  have := h.b1_fin; have := h.b2_fin; have := h.finS
  let f : ↥(borelOf L1 S) × ↥(borelOf L2 S) × ↥S → ↥(borelOf L1 S ⊔ borelOf L2 S ⊔ S) :=
    fun p => ⟨(p.1 : G) * p.2.1 * p.2.2, by
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left p.1.2))
        (Subgroup.mem_sup_left (Subgroup.mem_sup_right p.2.1.2)))
        (Subgroup.mem_sup_right p.2.2.2)⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨b1, hb1, b2, hb2, s, hs, rfl⟩ := h.decomp hx
    exact ⟨(⟨b1, hb1⟩, ⟨b2, hb2⟩, ⟨s, hs⟩), rfl⟩
  exact Finite.of_surjective f hf

end F13Setup

end Setup

section HallSetup

variable {G : Type u} [Group G]

open CFSG.QuasithinUnique CFSG.Quasithin

theorem le_sup_inf_of_decomp {S S1 S2 B B1 B2 D : Subgroup G}
    (hdec : ∀ x ∈ B, ∃ b1 ∈ B1, ∃ b2 ∈ B2, ∃ s ∈ S, x = b1 * b2 * s)
    (hS1 : S1 ≤ S) (hS2 : S2 ≤ S)
    (hN1 : B ≤ Subgroup.normalizer (S1 : Set G)) (hN2 : B ≤ Subgroup.normalizer (S2 : Set G))
    (hB1 : B1 ≤ B) (hB2 : B2 ≤ B) (hDB : D ≤ B) (hSD : S ⊓ D = ⊥)
    (hE1 : B1 = S1 ⊔ (D ⊓ B1)) (hE2 : B2 = S2 ⊔ (D ⊓ B2)) :
    D ≤ (D ⊓ B1) ⊔ (D ⊓ B2) := by
  intro x hx
  obtain ⟨b1, hb1, b2, hb2, s, hs, rfl⟩ := hdec x (hDB hx)
  have hD1N : (D ⊓ B1) ≤ Subgroup.normalizer (S1 : Set G) := fun y hy => hN1 (hB1 hy.2)
  have hD2N : (D ⊓ B2) ≤ Subgroup.normalizer (S2 : Set G) := fun y hy => hN2 (hB2 hy.2)
  have hb1' : b1 ∈ S1 ⊔ (D ⊓ B1) := hE1 ▸ hb1
  have hb2' : b2 ∈ S2 ⊔ (D ⊓ B2) := hE2 ▸ hb2
  obtain ⟨σ1, hσ1, δ1, hδ1, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hD1N).mp hb1'
  obtain ⟨σ2, hσ2, δ2, hδ2, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hD2N).mp hb2'
  have hδ1B : δ1 ∈ B := hB1 hδ1.2
  have hδ2B : δ2 ∈ B := hB2 hδ2.2
  have hxe : σ1 * δ1 * (σ2 * δ2) * s =
      (δ1 * δ2) * ((δ2⁻¹ * δ1⁻¹ * σ1 * δ1 * δ2) * (δ2⁻¹ * σ2 * δ2) * s) := by group
  have hs'S : (δ2⁻¹ * δ1⁻¹ * σ1 * δ1 * δ2) * (δ2⁻¹ * σ2 * δ2) * s ∈ S := by
    have h1 : δ2⁻¹ * δ1⁻¹ * σ1 * δ1 * δ2 ∈ S1 := by
      have hg : (δ1 * δ2)⁻¹ ∈ Subgroup.normalizer (S1 : Set G) :=
        Subgroup.inv_mem _ (hN1 (Subgroup.mul_mem _ hδ1B hδ2B))
      have := (Subgroup.mem_normalizer_iff.mp hg σ1).mp hσ1
      simpa [mul_assoc] using this
    have h2 : δ2⁻¹ * σ2 * δ2 ∈ S2 := by
      have hg : δ2⁻¹ ∈ Subgroup.normalizer (S2 : Set G) := Subgroup.inv_mem _ (hN2 hδ2B)
      have := (Subgroup.mem_normalizer_iff.mp hg σ2).mp hσ2
      simpa [mul_assoc] using this
    exact S.mul_mem (S.mul_mem (hS1 h1) (hS2 h2)) hs
  have heD : δ1 * δ2 ∈ D := D.mul_mem hδ1.1 hδ2.1
  have hs'D : (δ2⁻¹ * δ1⁻¹ * σ1 * δ1 * δ2) * (δ2⁻¹ * σ2 * δ2) * s ∈ D := by
    have : (δ2⁻¹ * δ1⁻¹ * σ1 * δ1 * δ2) * (δ2⁻¹ * σ2 * δ2) * s =
        (δ1 * δ2)⁻¹ * (σ1 * δ1 * (σ2 * δ2) * s) := by group
    rw [this]
    exact D.mul_mem (D.inv_mem heD) hx
  have hs'1 : (δ2⁻¹ * δ1⁻¹ * σ1 * δ1 * δ2) * (δ2⁻¹ * σ2 * δ2) * s = 1 := by
    have : (δ2⁻¹ * δ1⁻¹ * σ1 * δ1 * δ2) * (δ2⁻¹ * σ2 * δ2) * s ∈ S ⊓ D := ⟨hs'S, hs'D⟩
    rw [hSD, Subgroup.mem_bot] at this
    exact this
  rw [hxe, hs'1, mul_one]
  exact Subgroup.mul_mem_sup hδ1 hδ2

theorem hall_setup {L1 L2 S : Subgroup G} (h : F13Setup L1 L2 S) :
    ∃ D : Subgroup G, HallTwoPrime D (borelOf L1 S ⊔ borelOf L2 S ⊔ S) ∧
      HallTwoPrime (D ⊓ borelOf L1 S) (borelOf L1 S) ∧
      HallTwoPrime (D ⊓ borelOf L2 S) (borelOf L2 S) ∧
      borelOf L1 S = (S ⊓ L1) ⊔ (D ⊓ borelOf L1 S) ∧
      borelOf L2 S = (S ⊓ L2) ⊔ (D ⊓ borelOf L2 S) ∧
      D = (D ⊓ borelOf L1 S) ⊔ (D ⊓ borelOf L2 S) ∧
      borelOf L1 S ⊔ borelOf L2 S ⊔ S = S ⊔ (D ⊓ borelOf L1 S) ⊔ (D ⊓ borelOf L2 S) := by
  classical
  haveI := h.fin_bigB
  obtain ⟨D, hD⟩ := exists_hallTwoPrime (borelOf L1 S ⊔ borelOf L2 S ⊔ S) h.solvable
  have hB1B : borelOf L1 S ≤ borelOf L1 S ⊔ borelOf L2 S ⊔ S := le_sup_left.trans le_sup_left
  have hB2B : borelOf L2 S ≤ borelOf L1 S ⊔ borelOf L2 S ⊔ S := le_sup_right.trans le_sup_left
  have hSB : S ≤ borelOf L1 S ⊔ borelOf L2 S ⊔ S := le_sup_right
  have hBN1 : borelOf L1 S ⊔ borelOf L2 S ⊔ S ≤ Subgroup.normalizer (borelOf L1 S : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer h.b2_le_nb1) h.s_le_nb1
  have hBN2 : borelOf L1 S ⊔ borelOf L2 S ⊔ S ≤ Subgroup.normalizer (borelOf L2 S : Set G) :=
    sup_le (sup_le h.b1_le_nb2 Subgroup.le_normalizer) h.s_le_nb2
  have hD1 : HallTwoPrime (D ⊓ borelOf L1 S) (borelOf L1 S) := hD.inf hB1B hBN1
  have hD2 : HallTwoPrime (D ⊓ borelOf L2 S) (borelOf L2 S) := hD.inf hB2B hBN2
  have hE1 : borelOf L1 S = (S ⊓ L1) ⊔ (D ⊓ borelOf L1 S) :=
    (sup_eq_of_hallTwoPrime (F1.sylow_le_borelOf L1 S) (F1.borelOf_le L1 S) h.syl1.2.2 hD1).symm
  have hE2 : borelOf L2 S = (S ⊓ L2) ⊔ (D ⊓ borelOf L2 S) :=
    (sup_eq_of_hallTwoPrime (F1.sylow_le_borelOf L2 S) (F1.borelOf_le L2 S) h.syl2.2.2 hD2).symm
  have hSD : S ⊓ D = ⊥ := inf_eq_bot_of_odd h.pS hD.2.1
  have hDE : D = (D ⊓ borelOf L1 S) ⊔ (D ⊓ borelOf L2 S) :=
    le_antisymm
      (le_sup_inf_of_decomp (S := S) (B := borelOf L1 S ⊔ borelOf L2 S ⊔ S) (fun x hx => h.decomp hx)
        inf_le_left inf_le_left h.bigB_le_ns1 h.bigB_le_ns2 hB1B hB2B hD.1 hSD hE1 hE2)
      (sup_le inf_le_left inf_le_left)
  refine ⟨D, hD, hD1, hD2, hE1, hE2, hDE, ?_⟩
  apply le_antisymm
  · refine sup_le (sup_le ?_ ?_) (le_sup_left.trans le_sup_left)
    · exact le_trans (le_of_eq hE1) (sup_le (inf_le_left.trans (le_sup_left.trans le_sup_left))
        (le_sup_right.trans le_sup_left))
    · exact le_trans (le_of_eq hE2) (sup_le (inf_le_left.trans (le_sup_left.trans le_sup_left))
        le_sup_right)
  · exact sup_le (sup_le hSB (inf_le_right.trans hB1B)) (inf_le_right.trans hB2B)

end HallSetup

end CFSG.Quasithin.RonanF13
