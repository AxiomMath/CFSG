module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101U3Fr
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101U3Bar
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UFr
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyFiveStep
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtyEightOq

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem U4P.u81_exists_inv {D : Data G} {L K : Subgroup G}
    {n p : ℕ} (u : U4P D L K n p) {r : ℕ} (hr : r.Prime) (hrp : r ∣ 2 ^ p - 1) {x : Bar2 D.M}
    (hx : x ∈ barImage D.M L) (hxo : orderOf x = r) :
    ∃ s ∈ barImage D.M L, s * x * s⁻¹ = x⁻¹ := by
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv u.hL
  have hyo : orderOf (e.symm ⟨x, hx⟩) = r := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hxo]
  obtain ⟨s, -, hs⟩ :=
    PartTwo.S17.exists_involution_inverts_of_shape u.shape hr (u.r_ne_two hr hrp) hyo
  refine ⟨(e s : Bar2 D.M), (e s).2, ?_⟩
  have h := congrArg (fun y => ((e y : ↥(barImage D.M L)) : Bar2 D.M)) hs
  simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] using h

namespace U81BasisR

variable {D : Data G} {L K B : Subgroup G} {r n p : ℕ} {b : Fin 3 → G}

theorem exists_conj_eq_zpow (hb : U81BasisR D L K r B b) (hr : r.Prime) (hr2 : r ≠ 2)
    (hBM : B ≤ D.M) {m : Bar2 D.M} {k : Fin 3 → ℤ}
    (h : ∀ i (hi : b i ∈ D.M),
      m * uc22p21cPi D.M ⟨b i, hi⟩ * m⁻¹ = uc22p21cPi D.M ⟨b i, hi⟩ ^ k i) :
    ∃ t ∈ normalizer (B : Set G) ⊓ D.M, ∀ i, t * b i * t⁻¹ = b i ^ k i := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBp : IsPGroup r B := hb.frame.elem.isPGroup
  have hbM : ∀ i, b i ∈ D.M := fun i => hBM (hb.frame.mem i)
  have hφ : ∀ i, MulAut.conj m (uc22p21cPi D.M ⟨b i, hbM i⟩) ∈ barImage D.M B := fun i => by
    rw [MulAut.conj_apply, h i (hbM i)]
    exact zpow_mem (uc22p21c_mem_barImage.2 ⟨_, hb.frame.mem i, rfl⟩) _
  have hmN : m ∈ normalizer ((barImage D.M B : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) := by
    refine Subgroup.mem_normalizer_fintype fun q hq => ?_
    obtain ⟨x, hxB, rfl⟩ := uc22p21c_mem_barImage.1 hq
    obtain ⟨a, ha⟩ := hb.frame.span _ hxB
    have hxe : x = (⟨b 0, hbM 0⟩ : ↥D.M) ^ (a 0).val * ⟨b 1, hbM 1⟩ ^ (a 1).val *
        ⟨b 2, hbM 2⟩ ^ (a 2).val :=
      Subtype.ext (by rw [← ha]; simp only [u81Coord, Subgroup.coe_mul, Subgroup.coe_pow])
    rw [← MulAut.conj_apply, hxe]
    simp only [map_mul, map_pow]
    exact mul_mem (mul_mem (pow_mem (hφ 0) _) (pow_mem (hφ 1) _)) (pow_mem (hφ 2) _)
  have hN2 : ¬ r ∣ Nat.card (CFSG.pCore 2 ↥D.M) := by
    intro hd
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M))
    rw [hj] at hd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hd))
  have hlift := CFSG.GroupTheory.normal_coprime_quotient_normalizer r
    (CFSG.pCore 2 ↥D.M) hN2 (B.subgroupOf D.M) hBp.comap_subtype
  have hm' : m ∈ (normalizer ((B.subgroupOf D.M : Subgroup ↥D.M) : Set ↥D.M)).map
      (uc22p21cPi D.M) := by
    rw [hlift]
    exact hmN
  obtain ⟨t, htN, rfl⟩ := hm'
  have htG : (t : G) ∈ normalizer (B : Set G) := by
    have h1 := Subgroup.le_normalizer_map D.M.subtype (Subgroup.mem_map_of_mem D.M.subtype htN)
    rwa [Subgroup.subgroupOf_map_subtype, inf_of_le_left hBM] at h1
  refine ⟨t, ⟨htG, t.2⟩, fun i => ?_⟩
  have h1 : ((t * ⟨b i, hbM i⟩ * t⁻¹ : ↥D.M) : G) ∈ B :=
    (mem_normalizer_iff.1 htG _).1 (hb.frame.mem i)
  have h2 : (((⟨b i, hbM i⟩ : ↥D.M) ^ k i : ↥D.M) : G) ∈ B := zpow_mem (hb.frame.mem i) _
  have e := u81_eq_of_pi_eq hr hr2 hBp h1 h2 (by
    rw [map_mul, map_mul, map_inv, map_zpow]
    exact h i (hbM i))
  exact congrArg Subtype.val e

theorem exists_conj_zero (hb : U81BasisR D L K r B b)
    (u : U4P D L K n p) (hr : r.Prime) (hrp : r ∣ 2 ^ p - 1) (hBM : B ≤ D.M) :
    ∃ t ∈ normalizer (B : Set G) ⊓ D.M,
      ∀ i, t * b i * t⁻¹ = b i ^ (![-1, 1, 1] : Fin 3 → ℤ) i := by
  obtain ⟨hcomm, -, -, -, -, -, -⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  have hr2 := u.r_ne_two hr hrp
  have h0M : b 0 ∈ D.M := hBM (hb.frame.mem 0)
  obtain ⟨s, hs, hsx⟩ := u.u81_exists_inv hr hrp
    (uc22p21c_mem_barImage.2 ⟨⟨b 0, h0M⟩, hb.mem_L, rfl⟩)
    (orderOf_bar_eq_of_prime h0M hr hr2 (hb.orderOf_eq hr 0))
  have e0 : ∀ hi : b 0 ∈ D.M, s * uc22p21cPi D.M ⟨b 0, hi⟩ * s⁻¹ =
      uc22p21cPi D.M ⟨b 0, hi⟩ ^ (-1 : ℤ) := fun _ => hsx.trans (zpow_neg_one _).symm
  have e1 : ∀ hi : b 1 ∈ D.M, s * uc22p21cPi D.M ⟨b 1, hi⟩ * s⁻¹ =
      uc22p21cPi D.M ⟨b 1, hi⟩ ^ (1 : ℤ) := fun hi => by
    rw [zpow_one, hcomm s hs _ (uc22p21c_mem_barImage.2 ⟨⟨b 1, hi⟩, hb.mem_K, rfl⟩),
      mul_inv_cancel_right]
  have e2 : ∀ hi : b 2 ∈ D.M, s * uc22p21cPi D.M ⟨b 2, hi⟩ * s⁻¹ =
      uc22p21cPi D.M ⟨b 2, hi⟩ ^ (1 : ℤ) := fun hi => by
    rw [zpow_one, mem_centralizer_iff.1 (hb.bar_C hi) s (mem_sup_left hs), mul_inv_cancel_right]
  refine hb.exists_conj_eq_zpow hr hr2 hBM (m := s) fun i hi => ?_
  fin_cases i
  · exact e0 hi
  · exact e1 hi
  · exact e2 hi

theorem exists_conj_one (hb : U81BasisR D L K r B b)
    (u : U4P D L K n p) (hr : r.Prime) (hrp : r ∣ 2 ^ p - 1) (hBM : B ≤ D.M) :
    ∃ t ∈ normalizer (B : Set G) ⊓ D.M,
      ∀ i, t * b i * t⁻¹ = b i ^ (![1, -1, 1] : Fin 3 → ℤ) i := by
  obtain ⟨hcomm, -, -, -, -, -, -⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  have hr2 := u.r_ne_two hr hrp
  have h1M : b 1 ∈ D.M := hBM (hb.frame.mem 1)
  obtain ⟨s, hs, hsx⟩ := u.symm.u81_exists_inv hr hrp
    (uc22p21c_mem_barImage.2 ⟨⟨b 1, h1M⟩, hb.mem_K, rfl⟩)
    (orderOf_bar_eq_of_prime h1M hr hr2 (hb.orderOf_eq hr 1))
  have e0 : ∀ hi : b 0 ∈ D.M, s * uc22p21cPi D.M ⟨b 0, hi⟩ * s⁻¹ =
      uc22p21cPi D.M ⟨b 0, hi⟩ ^ (1 : ℤ) := fun hi => by
    rw [zpow_one, ← hcomm _ (uc22p21c_mem_barImage.2 ⟨⟨b 0, hi⟩, hb.mem_L, rfl⟩) s hs,
      mul_inv_cancel_right]
  have e1 : ∀ hi : b 1 ∈ D.M, s * uc22p21cPi D.M ⟨b 1, hi⟩ * s⁻¹ =
      uc22p21cPi D.M ⟨b 1, hi⟩ ^ (-1 : ℤ) := fun _ => hsx.trans (zpow_neg_one _).symm
  have e2 : ∀ hi : b 2 ∈ D.M, s * uc22p21cPi D.M ⟨b 2, hi⟩ * s⁻¹ =
      uc22p21cPi D.M ⟨b 2, hi⟩ ^ (1 : ℤ) := fun hi => by
    rw [zpow_one, mem_centralizer_iff.1 (hb.bar_C hi) s (mem_sup_right hs), mul_inv_cancel_right]
  refine hb.exists_conj_eq_zpow hr hr2 hBM (m := s) fun i hi => ?_
  fin_cases i
  · exact e0 hi
  · exact e1 hi
  · exact e2 hi

end U81BasisR

end CFSG.LocalAnalysis.UniquenessCase.UC22
