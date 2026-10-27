module

public import CFSG.Quasithin.Vol2.Ch10SecV1O
public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinear
public import CFSG.Quasithin.Vol2.Ch10SecAShapeCard
public import CFSG.Quasithin.EmptyFaithful.T1515dB

public section

namespace CFSG.Quasithin.Vol2.Ch10.V1C

open CFSG.Open (quasithinG2)
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.EmptyFaithfulMultiple

namespace FFOrd

theorem c27Order_sl3 {n : ℕ} (hn : 1 ≤ n) :
    SecB.C10KG.C27Order ((2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨n, hn, ?_⟩))))))))
  have e3 : (2 : ℕ) ^ (3 * n) = (2 ^ n) ^ 3 := by rw [← pow_mul, mul_comm]
  have e4 : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have e8 : (8 : ℕ) ^ n = (2 ^ n) ^ 3 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [e3, e4, e8, mul_assoc]

theorem card_sl4 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 1) :
    Nat.card ↥(StatedSL 4 K) = 20160 := by
  rw [card_statedSL1527d (by norm_num), hK]
  decide

theorem card_sl5 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 1) :
    Nat.card ↥(StatedSL 5 K) = 9999360 := by
  rw [card_statedSL1527d (by norm_num), hK]
  decide

end FFOrd

open FFL FFOrd

variable {V : Type} [CommGroup V]

theorem ffOrd_of_b42 {L : Subgroup (MulAut V)} (hZ : Subgroup.center ↥L = ⊥)
    (h6 : 6 < Nat.card L) (hB : B42ModulePair L (commV L) (fixV L ⊓ commV L)) :
    FFOrd (Nat.card L) := by
  rcases hB with ⟨m, K, _, _, hK, π, hπ⟩ | ⟨m, K, _, _, hK, π, hπ⟩ | ⟨m, K, _, _, hK, π, hπ⟩ |
    ⟨m, K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨π, hπ⟩ | ⟨π, hπ⟩ | ⟨π, hπ⟩ | ⟨α, π, hπ⟩ |
    ⟨K, _, _, Γ₀, -, -, hhat, -, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ |
    ⟨π, hπ⟩ | ⟨π, hπ⟩
  ·
    have : Fintype K := Fintype.ofFinite K
    have h1 := card_eq_of_realizesVia (FFModel.nat_faithful _) hπ
    change Nat.card ↥L = Nat.card ↥(StatedSL 2 K) at h1
    rw [FFL.card_statedSL_two, ← Nat.card_eq_fintype_card, hK] at h1
    have hm := one_le_of_card hK
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · obtain rfl : m = 1 := by omega
      norm_num at h1
      omega
    · refine Or.inl (Or.inl ⟨m, hm2, ?_⟩)
      rw [h1, show (4 : ℕ) ^ m = (2 ^ m) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
  ·
    have : Fintype K := Fintype.ofFinite K
    have h1 := card_eq_of_realizesVia (FFModel.nat_faithful _) hπ
    change Nat.card ↥L = Nat.card ↥(StatedSL 3 K) at h1
    rw [FFL.card_statedSL_three, ← Nat.card_eq_fintype_card, hK] at h1
    rw [h1]
    exact Or.inl (c27Order_sl3 (one_le_of_card hK))
  ·
    have h1 := card_eq_of_realizesVia (FFModel.nat_faithful _) hπ
    change Nat.card ↥L = Nat.card ↥(StatedSp 2 K) at h1
    rw [SecA.card_Sp4_pow hK] at h1
    exact Or.inr (Or.inl ⟨m, one_le_of_card hK, h1⟩)
  ·
    have := charP_two_of_card hK
    have h1 := card_eq_of_realizesVia (zornQ_faithful le_rfl) hπ
    change Nat.card ↥L = Nat.card ↥(quasithinG2 K) at h1
    rw [card_quasithinG2_1527d hK, hK] at h1
    exact Or.inr (Or.inr (Or.inl ⟨m, one_le_of_card hK, h1⟩))
  ·
    have := charP_two_of_card hK
    have hle : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ quasithinG2 K :=
      Subgroup.commutator_le.2 fun x hx y hy => by
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
          (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
    have h1 := card_eq_of_realizesVia (zornQ_faithful hle) hπ
    change Nat.card ↥L = Nat.card ↥⁅quasithinG2 K, quasithinG2 K⁆ at h1
    have h2 := Subgroup.card_dvd_of_le hle
    rw [card_quasithinG2_1527d hK, hK] at h2
    norm_num at h2
    rw [h1]
    exact Or.inr (Or.inr (Or.inr h2))
  ·
    have h1 := card_eq_of_realizesVia (G64.altDn_faithful le_rfl) hπ
    change Nat.card ↥L = Nat.card ↥(alternatingGroup (Fin 5)) at h1
    rw [h1, FFL.card_alt (by norm_num)]
    exact Or.inl (Or.inr (Or.inl (by decide)))
  ·
    have h1 := card_eq_of_realizesVia (G64.altDn_faithful (by norm_num)) hπ
    change Nat.card ↥L = Nat.card ↥(alternatingGroup (Fin 6)) at h1
    rw [h1, FFL.card_alt (by norm_num)]
    exact Or.inl (Or.inr (Or.inr (Or.inl (by decide))))
  ·
    have h1 := card_eq_of_realizesVia (G64.altDn_faithful (by norm_num)) hπ
    change Nat.card ↥L = Nat.card ↥(alternatingGroup (Fin 7)) at h1
    rw [h1, FFL.card_alt (by norm_num)]
    exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  ·
    have h1 := card_eq_of_realizesVia (G64.a7Four_faithful α) hπ
    change Nat.card ↥L = Nat.card ↥(alternatingGroup (Fin 7)) at h1
    rw [h1, FFL.card_alt (by norm_num)]
    exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  ·
    exfalso
    have e : ↥Γ₀ ≃* ↥L := MulEquiv.ofBijective π
      ⟨G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ, hπ.1⟩
    have h1 := Nat.card_congr (Subgroup.centerCongr e).toEquiv
    rw [hhat.2.1, hZ, Subgroup.card_bot] at h1
    omega
  ·
    have h1 := card_eq_of_realizesVia (FFModel.nat_faithful _) hπ
    change Nat.card ↥L = Nat.card ↥(StatedSL 4 K) at h1
    rw [h1, card_sl4 hK]
    exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  ·
    have h1 := card_eq_of_realizesVia (FFModel.nat_faithful _) hπ
    change Nat.card ↥L = Nat.card ↥(StatedSL 5 K) at h1
    rw [h1, card_sl5 hK]
    exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr rfl)))))))))
  ·
    have h1 := card_eq_of_realizesVia (G64.extSq_faithful (by norm_num)) hπ
    change Nat.card ↥L = Nat.card ↥(StatedSL 4 (ZMod 2)) at h1
    rw [h1, FFL.card_statedSL_four]
    exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  ·
    have h1 := card_eq_of_realizesVia (G64.extSq_faithful (by norm_num)) hπ
    change Nat.card ↥L = Nat.card ↥(StatedSL 5 (ZMod 2)) at h1
    rw [h1, FFL.card_statedSL_five]
    exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr rfl)))))))))

theorem ffOrd_of_b51 [Finite V] {G L : Subgroup (MulAut V)} (hZ : Subgroup.center ↥L = ⊥)
    (h6 : 6 < Nat.card L) (h : B51Part1 G L) : FFOrd (Nat.card L) := by
  obtain ⟨-, h⟩ := h
  rcases h with ⟨-, hB, -⟩ | ⟨-, n, K, _, _, hK, I, π, -, -, hreal, -, -⟩ |
    ⟨n, -, hn, π, U₁, U₂, -, h₁, -⟩ | ⟨-, n, hn, k, hk1, -, I, π, -, -, -, hreal⟩
  · exact ffOrd_of_b42 hZ h6 hB
  ·
    have : Fintype K := Fintype.ofFinite K
    have h1 := card_eq_of_realizesVia (FFModel.nat_faithful _) (hreal 0)
    change Nat.card ↥L = Nat.card ↥(StatedSL 3 K) at h1
    rw [FFL.card_statedSL_three, ← Nat.card_eq_fintype_card, hK] at h1
    rw [h1]
    exact Or.inl (c27Order_sl3 (one_le_of_card hK))
  ·
    have h1 := card_eq_of_realizesVia (FFModel.nat_faithful _) h₁
    rcases hn with rfl | rfl
    · change Nat.card ↥L = Nat.card ↥(StatedSL 4 (ZMod 2)) at h1
      rw [h1, FFL.card_statedSL_four]
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · change Nat.card ↥L = Nat.card ↥(StatedSL 5 (ZMod 2)) at h1
      rw [h1, FFL.card_statedSL_five]
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr rfl)))))))))
  ·
    have h1 := card_eq_of_realizesVia (FFModel.nat_faithful _) (hreal ⟨0, hk1⟩)
    rcases hn with rfl | rfl
    · change Nat.card ↥L = Nat.card ↥(StatedSL 4 (ZMod 2)) at h1
      rw [h1, FFL.card_statedSL_four]
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · change Nat.card ↥L = Nat.card ↥(StatedSL 5 (ZMod 2)) at h1
      rw [h1, FFL.card_statedSL_five]
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr rfl)))))))))

end CFSG.Quasithin.Vol2.Ch10.V1C
