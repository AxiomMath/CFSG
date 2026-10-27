module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutData
public import CFSG.Quasithin.Background.E2TwoProofDefs
public import CFSG.Quasithin.Background.Harris.KFact2d.OddCore
public import CFSG.Quasithin.Vol2.GoldschmidtE217Klein

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin E2P
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Quot

variable (K Q D : Subgroup G) [(Q.subgroupOf K).Normal]

abbrev psi : ↥K →* ↥K ⧸ Q.subgroupOf K := QuotientGroup.mk' (Q.subgroupOf K)

abbrev Dbar : Subgroup (↥K ⧸ Q.subgroupOf K) := (D.subgroupOf K).map (psi K Q)

variable {K Q D}

theorem psi_comm_iff (x y : ↥K) :
    psi K Q x * psi K Q y = psi K Q y * psi K Q x ↔ (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ Q := by
  rw [← commutatorElement_eq_one_iff_mul_comm, commutatorElement_def, ← map_inv, ← map_inv,
    ← map_mul, ← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]
  simp

theorem mem_Dbar {w : ↥K ⧸ Q.subgroupOf K} :
    w ∈ Dbar K Q D ↔ ∃ (d : G) (hd : d ∈ D) (hdK : d ∈ K), psi K Q ⟨d, hdK⟩ = w := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, x.2, rfl⟩
  · rintro ⟨d, hd, hdK, rfl⟩
    exact ⟨⟨d, hdK⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩

theorem psi_mem_Dbar {d : G} (hd : d ∈ D) (hdK : d ∈ K) : psi K Q ⟨d, hdK⟩ ∈ Dbar K Q D :=
  mem_Dbar.mpr ⟨d, hd, hdK, rfl⟩

theorem center_le_J {J : Subgroup G} (hJ : ∀ x, x ∈ J ↔ x ∈ D ∧ ∀ y ∈ D, x * y * x⁻¹ * y⁻¹ ∈ Q)
    (hDK : D ≤ K) (e : ↥(Dbar K Q D)) (he : e ∈ Subgroup.center ↥(Dbar K Q D)) :
    ∃ (j : G) (hj : j ∈ J) (hjK : j ∈ K), psi K Q ⟨j, hjK⟩ = (e : ↥K ⧸ Q.subgroupOf K) := by
  obtain ⟨j, hjD, hjK, hje⟩ := mem_Dbar.mp e.2
  refine ⟨j, (hJ j).mpr ⟨hjD, fun y hy => ?_⟩, hjK, hje⟩
  have h := Subgroup.mem_center_iff.mp he ⟨psi K Q ⟨y, hDK hy⟩, psi_mem_Dbar hy (hDK hy)⟩
  have h' : psi K Q ⟨y, hDK hy⟩ * psi K Q ⟨j, hjK⟩ = psi K Q ⟨j, hjK⟩ * psi K Q ⟨y, hDK hy⟩ := by
    have := congrArg Subtype.val h
    simp only [Subgroup.coe_mul] at this
    rw [← hje] at this
    exact this
  have h2 := (psi_comm_iff ⟨j, hjK⟩ ⟨y, hDK hy⟩).mp h'.symm
  exact h2

theorem psi_mem_center {J : Subgroup G}
    (hJ : ∀ x, x ∈ J ↔ x ∈ D ∧ ∀ y ∈ D, x * y * x⁻¹ * y⁻¹ ∈ Q) (hDK : D ≤ K) {j : G}
    (hj : j ∈ J) (hjK : j ∈ K) :
    (⟨psi K Q ⟨j, hjK⟩, psi_mem_Dbar ((hJ j).mp hj).1 hjK⟩ : ↥(Dbar K Q D)) ∈
      Subgroup.center ↥(Dbar K Q D) := by
  rw [Subgroup.mem_center_iff]
  intro e
  obtain ⟨y, hyD, hyK, hye⟩ := mem_Dbar.mp e.2
  apply Subtype.ext
  show (e : ↥K ⧸ Q.subgroupOf K) * psi K Q ⟨j, hjK⟩ = psi K Q ⟨j, hjK⟩ * (e : ↥K ⧸ Q.subgroupOf K)
  rw [← hye]
  exact (psi_comm_iff ⟨j, hjK⟩ ⟨y, hyK⟩).mpr (((hJ j).mp hj).2 y hyD) |>.symm

theorem psi_pow_eq_one_iff (x : ↥K) (n : ℕ) : psi K Q x ^ n = 1 ↔ (x : G) ^ n ∈ Q := by
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rfl

theorem odd_card_center {J : Subgroup G}
    (hJ : ∀ x, x ∈ J ↔ x ∈ D ∧ ∀ y ∈ D, x * y * x⁻¹ * y⁻¹ ∈ Q) (hDK : D ≤ K)
    (hodd : ∀ y ∈ J, (∃ k : ℕ, y ^ 2 ^ k ∈ Q) → y ∈ Q) :
    Odd (Nat.card (Subgroup.center ↥(Dbar K Q D))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  have h2 : 2 ∣ Nat.card (Subgroup.center ↥(Dbar K Q D)) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hcon)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨j, hj, hjK, hje⟩ := center_le_J hJ hDK x.1 x.2
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have h1 : psi K Q ⟨j, hjK⟩ ^ 2 = 1 := by
    have := congrArg (fun e : ↥(Dbar K Q D) => (e : ↥K ⧸ Q.subgroupOf K))
      (congrArg Subtype.val hx2)
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at this
    rw [hje]
    exact this
  have hj2 : j ^ 2 ∈ Q := (psi_pow_eq_one_iff _ _).mp h1
  have hjQ : j ∈ Q := hodd j hj ⟨1, by simpa using hj2⟩
  have h3 : psi K Q ⟨j, hjK⟩ = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hjQ
  have hx1 : x = 1 := Subtype.ext (Subtype.ext (hje.symm.trans h3))
  rw [hx1, orderOf_one] at hx
  omega

theorem psi_eq_one_of_mem {q : G} (hq : q ∈ Q) (hqK : q ∈ K) : psi K Q ⟨q, hqK⟩ = 1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact hq

theorem commutator_Dbar_eq_top {K0 : Subgroup G} (hK0K : K0 ≤ K) (hperf : ⁅K0, K0⁆ = K0)
    (hD : D = K0 ⊔ Q) (hQK : K ≤ Subgroup.normalizer (Q : Set G)) (hQleK : Q ≤ K) :
    commutator ↥(Dbar K Q D) = ⊤ := by
  let Sc : Subgroup (↥K ⧸ Q.subgroupOf K) :=
    (commutator ↥(Dbar K Q D)).map (Dbar K Q D).subtype
  have hK0D : K0 ≤ D := hD ▸ le_sup_left
  let H : Subgroup G := (Sc.comap (psi K Q)).map K.subtype
  have hgen : ⁅K0, K0⁆ ≤ H := by
    rw [Subgroup.commutator_def]
    refine (Subgroup.closure_le H).mpr ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have haK : a ∈ K := hK0K ha
    have hbK : b ∈ K := hK0K hb
    have habK : ⁅a, b⁆ ∈ K := by
      rw [commutatorElement_def]
      exact K.mul_mem (K.mul_mem (K.mul_mem haK hbK) (K.inv_mem haK)) (K.inv_mem hbK)
    refine ⟨⟨⁅a, b⁆, habK⟩, ?_, rfl⟩
    have e1 : (⟨⁅a, b⁆, habK⟩ : ↥K) = ⁅(⟨a, haK⟩ : ↥K), ⟨b, hbK⟩⁆ := rfl
    show psi K Q _ ∈ Sc
    rw [e1, map_commutatorElement]
    refine ⟨⁅(⟨psi K Q ⟨a, haK⟩, psi_mem_Dbar (hK0D ha) haK⟩ : ↥(Dbar K Q D)),
      ⟨psi K Q ⟨b, hbK⟩, psi_mem_Dbar (hK0D hb) hbK⟩⁆, ?_, rfl⟩
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hK0H : K0 ≤ H := hperf ▸ hgen
  rw [eq_top_iff]
  intro e _
  obtain ⟨d, hd, hdK, hde⟩ := mem_Dbar.mp e.2
  have hcoe : (↑(K0 ⊔ Q) : Set G) = K0 * Q :=
    Subgroup.coe_mul_of_left_le_normalizer_right K0 Q (hK0K.trans hQK)
  have hd' : d ∈ (↑(K0 ⊔ Q) : Set G) := hD ▸ hd
  rw [hcoe] at hd'
  obtain ⟨k, hk, q, hq, rfl⟩ := hd'
  have hkK : k ∈ K := hK0K hk
  have hqK : q ∈ K := hQleK hq
  have hpsi : psi K Q ⟨k * q, hdK⟩ = psi K Q ⟨k, hkK⟩ := by
    have : (⟨k * q, hdK⟩ : ↥K) = ⟨k, hkK⟩ * ⟨q, hqK⟩ := rfl
    rw [this, map_mul, psi_eq_one_of_mem hq hqK, mul_one]
  obtain ⟨y, hy, hyk⟩ := hK0H hk
  obtain ⟨c, hc, hce⟩ := hy
  have hyeq : y = ⟨k, hkK⟩ := Subtype.ext hyk
  have : e = c := by
    apply Subtype.ext
    rw [← hde, hpsi, ← hyeq]
    exact hce.symm
  rw [this]
  exact hc

end Quot

end CFSG.Quasithin.Background.Harris.KFact2d
