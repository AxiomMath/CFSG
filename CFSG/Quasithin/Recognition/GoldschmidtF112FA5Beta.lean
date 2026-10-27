module

public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Frame

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.QuasithinUnique.A5.Delta5 CFSG.Quasithin.H.A5W

namespace FA5

theorem alt5_sq_eq_one_of_two_power {a : Alt5} {k : ℕ} (h : a ^ 2 ^ k = 1) : a ^ 2 = 1 := by
  have h1 : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf a ∣ 60 := by
    rw [← a5_card]
    exact orderOf_dvd_natCard a
  obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hj2 : j ≤ 2 := by
    by_contra hlt
    have h8 : 2 ^ 3 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    rw [← hj'] at h8
    have := h8.trans h2
    norm_num at this
  have h4 : a ^ 4 = 1 := by
    have : orderOf a ∣ 2 ^ 2 := by
      rw [hj']
      exact pow_dvd_pow 2 hj2
    exact orderOf_dvd_iff_pow_eq_one.mp (by simpa using this)
  have key : ∀ b : Alt5, b ^ 4 = 1 → b ^ 2 = 1 := by decide +kernel
  exact key a h4

theorem alt5_eq_one_of_commute_three {y u : Alt5} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hc : u * y = y * u) (hu2 : u ^ 2 = 1) : u = 1 := by
  have key : ∀ y u : Alt5, y ^ 3 = 1 → y ≠ 1 → u * y = y * u → u ^ 2 = 1 → u = 1 := by
    decide +kernel
  exact key y u hy3 hy1 hc hu2

namespace Frame

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G} (F : Frame L1 L2 S D X)
include F

theorem pCore_L2_le_Q2 : pCoreOf 2 L2 ≤ Q2 L1 L2 S := by
  have hN : P2 L1 L2 S ≤ Subgroup.normalizer (pCoreOf 2 L2 : Set G) :=
    le_normalizer_pCoreOf_of_le_normalizer (sup_le Subgroup.le_normalizer F.B_le_normalizer_L2)
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L2).trans le_sup_left) hN
    (pCoreOf_isPGroup 2 L2)

omit F in
theorem inf_Q2_le : L2 ⊓ Q2 L1 L2 S ≤ pCoreOf 2 L2 := by
  have := pCoreOf_inf_le (H := P2 L1 L2 S) (K := L2) le_sup_left
  rwa [inf_comm] at this

omit [Finite G] in
theorem exists_phi : ∃ φ : ↥L2 →* Alt5, Function.Surjective φ ∧
    ∀ l : ↥L2, φ l = 1 ↔ (l : G) ∈ pCoreOf 2 L2 := by
  obtain ⟨e⟩ := F.pair.alt2
  let π : ↥L2 →* oTwoQuot ↥L2 := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L2)
  refine ⟨e.toMonoidHom.comp π, ?_, ?_⟩
  · exact e.surjective.comp (QuotientGroup.mk'_surjective _)
  · intro l
    show e (π l) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    show (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L2) l) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact F1.mem_pCore_iff_coe l

theorem exists_factor {s : G} (hs : s ∈ S) :
    ∃ l ∈ L2, ∃ q ∈ Q2 L1 L2 S, s = l * q ∧ l ∈ S := by
  obtain ⟨l, hl, q, hq, rfl⟩ := F.untw s hs
  refine ⟨l, hl, q, hq, rfl, ?_⟩
  have hqS : q ∈ S := F.Q2_le_S hq
  have : l = (l * q) * q⁻¹ := by group
  rw [this]
  exact S.mul_mem hs (S.inv_mem hqS)

theorem exists_involution {φ : ↥L2 →* Alt5}
    (hφ : ∀ l : ↥L2, φ l = 1 ↔ (l : G) ∈ pCoreOf 2 L2) {s : G} (hs : s ∈ S)
    (hsQ : s ∉ Q2 L1 L2 S) :
    ∃ (l : ↥L2) (q : G), q ∈ Q2 L1 L2 S ∧ s = l * q ∧ (l : G) ∈ S ∧ φ l ≠ 1 ∧ φ l ^ 2 = 1 := by
  obtain ⟨l, hl, q, hq, hsq, hlS⟩ := F.exists_factor hs
  refine ⟨⟨l, hl⟩, q, hq, hsq, hlS, ?_, ?_⟩
  · intro h1
    have h2 : l ∈ pCoreOf 2 L2 := (hφ ⟨l, hl⟩).mp h1
    exact hsQ (hsq ▸ (Q2 L1 L2 S).mul_mem (F.pCore_L2_le_Q2 h2) hq)
  · obtain ⟨k, hk⟩ := F.pair.hyp.hyp.h1.pgroup ⟨l, hlS⟩
    apply alt5_sq_eq_one_of_two_power (k := k)
    rw [← map_pow]
    have : (⟨l, hl⟩ : ↥L2) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]

theorem fpf {d s : G} (hd : d ∈ D) (hd1 : d ≠ 1) (hs : s ∈ S)
    (h : d * s * d⁻¹ * s⁻¹ ∈ Q2 L1 L2 S) : s ∈ Q2 L1 L2 S := by
  by_contra hsQ
  obtain ⟨φ, -, hφ⟩ := F.exists_phi
  obtain ⟨l, q, hq, hsl, hlS, hl1, hl2⟩ := F.exists_involution hφ hs hsQ
  have hdL : d ∈ L2 := F.D_le hd
  have hdP : d ∈ P2 L1 L2 S := (le_sup_left : L2 ≤ P2 L1 L2 S) hdL
  have hlP : (l : G) ∈ P2 L1 L2 S := (le_sup_left : L2 ≤ P2 L1 L2 S) l.2
  have hN := P2_le_normalizer_Q2 L1 L2 S
  have hc : d * (l : G) * d⁻¹ * (l : G)⁻¹ ∈ Q2 L1 L2 S := by
    have h1 : d * q * d⁻¹ ∈ Q2 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (hN hdP) q).mp hq
    have h2 : (d * q * d⁻¹) * q⁻¹ ∈ Q2 L1 L2 S := (Q2 L1 L2 S).mul_mem h1 ((Q2 L1 L2 S).inv_mem hq)
    have h3 : (l : G) * ((d * q * d⁻¹) * q⁻¹) * (l : G)⁻¹ ∈ Q2 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (hN hlP) _).mp h2
    have h4 : d * (l : G) * d⁻¹ * (l : G)⁻¹ =
        (d * s * d⁻¹ * s⁻¹) * ((l : G) * ((d * q * d⁻¹) * q⁻¹) * (l : G)⁻¹)⁻¹ := by
      rw [hsl]
      group
    rw [h4]
    exact (Q2 L1 L2 S).mul_mem h ((Q2 L1 L2 S).inv_mem h3)
  have hcL : d * (l : G) * d⁻¹ * (l : G)⁻¹ ∈ pCoreOf 2 L2 :=
    inf_Q2_le ⟨L2.mul_mem (L2.mul_mem (L2.mul_mem hdL (l.2)) (L2.inv_mem hdL)) (L2.inv_mem l.2),
      hc⟩
  have hφc : φ ⟨d, hdL⟩ * φ l * (φ ⟨d, hdL⟩)⁻¹ * (φ l)⁻¹ = 1 := by
    have := (hφ (⟨d, hdL⟩ * l * ⟨d, hdL⟩⁻¹ * l⁻¹)).mpr (by simpa using hcL)
    simpa [map_mul, map_inv] using this
  have hy1 : φ ⟨d, hdL⟩ ≠ 1 := by
    intro h1
    have h2 : d ∈ pCoreOf 2 L2 := (hφ ⟨d, hdL⟩).mp h1
    have h3 : d ∈ S := F.Q2_le_S (F.pCore_L2_le_Q2 h2)
    have : d ∈ D ⊓ S := ⟨hd, h3⟩
    rw [F.D_inf] at this
    exact hd1 (Subgroup.mem_bot.mp this)
  have hy3 : φ ⟨d, hdL⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨d, hdL⟩ : ↥L2) ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥D) (x := ⟨d, hd⟩)
      rw [F.D_card] at this
      exact Subtype.ext (by simpa using congrArg Subtype.val this)
    rw [this, map_one]
  have hcomm : φ l * φ ⟨d, hdL⟩ = φ ⟨d, hdL⟩ * φ l := by
    have h1 : φ ⟨d, hdL⟩ * φ l * (φ ⟨d, hdL⟩)⁻¹ = φ l := mul_inv_eq_one.mp hφc
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  exact hl1 (alt5_eq_one_of_commute_three hy3 hy1 hcomm hl2)

end Frame

end FA5

end CFSG.Quasithin
