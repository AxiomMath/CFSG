module

public import CFSG.RankThree.PartTwo.KFacts.HeringKS12Lift
public import CFSG.RankThree.PartTwo.KFacts.HeringKS12Alt8
public import CFSG.RankThree.PartTwo.KFacts.HeringKS12Central2
public import CFSG.Sporadic.Recognition.McLCentralizerCert
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLModel

public section

namespace CFSG.RankThree.PartTwo.KFacts

theorem exists_involution_of_mulEquiv_mcl
    {T : Type*} [Group T]
    (e : T ≃* CFSG.Blueprint.NativeSporadic.McL) : ∃ t : T, orderOf t = 2 := by
  obtain ⟨hP, h2, -, -, -⟩ := CFSG.Sporadic.SmallOddCore.mclT0_facts
  refine ⟨e.symm (CFSG.Sporadic.Schreier.mclPermEquiv.symm ⟨_, hP⟩), ?_⟩
  rw [MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
  exact h2

theorem three_le_localRank_of_mcl_cover
    {X : Type} [Group X] [Finite X] (hZ3 : Nat.card (Subgroup.center X) = 3)
    (e : X ⧸ Subgroup.center X ≃* CFSG.Blueprint.NativeSporadic.McL) :
    3 ≤ CFSG.Assembly.RankThreeEven.localRank 3 X := by
  obtain ⟨t, ht⟩ := exists_involution_of_mulEquiv_mcl e
  obtain ⟨-, hcen, ⟨φ⟩⟩ :=
    CFSG.Sporadic.Recognition.McLCentralizer.mcl_involution_centralizer_alt8_of_certificate ⟨e⟩ ht
  set C := Subgroup.centralizer ({t} : Set (X ⧸ Subgroup.center X)) with hC
  set N := Subgroup.zpowers
    (⟨t, CFSG.Sporadic.Recognition.McLCentralizer.self_mem_centralizer t⟩ : C) with hN
  have hNc : N ≤ Subgroup.center C := hcen.symm.le
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hN2 : ∀ z ∈ N, z ^ 2 = 1 := by
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    have : (⟨t, CFSG.Sporadic.Recognition.McLCentralizer.self_mem_centralizer t⟩ : C) ^ 2 = 1 :=
      Subtype.ext ht2
    rw [this, one_zpow]
  obtain ⟨x₀, y₀, g₀, h₀, hx3, hy3, hxy, hgx, hgy, hhx, hhy, hdist⟩ := exists_alt8_config
  obtain ⟨x, y, g, h, hx3', hy3', hxy', hgx', hgy', hhx', hhy', hdist'⟩ :=
    exists_config_of_quotient_two N hNc hN2 (x₀ := φ.symm x₀) (y₀ := φ.symm y₀)
      (g₀ := φ.symm g₀) (h₀ := φ.symm h₀)
      (by rw [← map_pow, hx3, map_one]) (by rw [← map_pow, hy3, map_one])
      (by rw [← map_mul, hxy, map_mul])
      (by rw [← map_inv, ← map_mul, ← map_mul, hgx, map_inv])
      (by rw [← map_inv, ← map_mul, ← map_mul, hgy])
      (by rw [← map_inv, ← map_mul, ← map_mul, hhx])
      (by rw [← map_inv, ← map_mul, ← map_mul, hhy, map_inv])
      (fun i j k l hijkl => hdist i j k l (by
        have := congrArg φ hijkl
        simpa only [map_mul, map_pow, MulEquiv.apply_symm_apply] using this))
  have hcomm : ∀ w : C, t * (w : X ⧸ Subgroup.center X) = w * t := fun w =>
    (Subgroup.mem_centralizer_singleton_iff.mp w.2).symm
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hval : ∀ (u v : C), ((u * v : C) : X ⧸ Subgroup.center X) = u * v := fun _ _ => rfl
  refine three_le_localRank_of_quotient_config (Subgroup.center X) le_rfl hZ3 (t := t)
    (x := x) (y := y) (g := g) (h := h) ht1 ht2
    (by rw [← Subgroup.coe_pow, hx3', Subgroup.coe_one])
    (by rw [← Subgroup.coe_pow, hy3', Subgroup.coe_one])
    (by rw [← Subgroup.coe_mul, hxy', Subgroup.coe_mul]) (hcomm x) (hcomm y) ?_
    (by rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hgx', Subgroup.coe_inv])
    (by rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hgy'])
    (by rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hhx'])
    (by rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hhy', Subgroup.coe_inv])
  refine CFSG.RankThree.PartTwo.Sec21.Hering214.card_closure_pair_three
    (by rw [← Subgroup.coe_pow, hx3', Subgroup.coe_one])
    (by rw [← Subgroup.coe_pow, hy3', Subgroup.coe_one])
    (by rw [← Subgroup.coe_mul, hxy', Subgroup.coe_mul]) (fun i j k l hijkl => hdist' i j k l ?_)
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_pow] using hijkl

end CFSG.RankThree.PartTwo.KFacts
