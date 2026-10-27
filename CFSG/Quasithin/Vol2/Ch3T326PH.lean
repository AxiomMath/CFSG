module

public import CFSG.Quasithin.Vol2.Ch3T326PG
public import CFSG.GroupTheory.HallHigmanPiCore

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
  CFSG.Quasithin.SmithD391 CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Open

variable {W : Type} [CommGroup W] [Finite W]

theorem isPSolvable_of_isSolvable {X : Type*} [Group X] {p : ℕ} (hp : p.Prime)
    (hX : Group.IsSolvable X) : CFSG.HallHigman.IsPSolvable p X := by
  intro H _ T _ hs
  have := hX
  have := hs
  have hcomm : ∀ a b : ↥H ⧸ T, a * b = b * a :=
    (IsSimpleGroup.comm_iff_isSolvable).mpr inferInstance
  have : IsMulCommutative (↥H ⧸ T) := ⟨⟨hcomm⟩⟩
  have hq : (Nat.card (↥H ⧸ T)).Prime := Group.is_simple_iff_prime_card.mp hs
  change Nat.card (↥H ⧸ T) = p ∨ Nat.Coprime p (Nat.card (↥H ⧸ T))
  by_cases hpq : Nat.card (↥H ⧸ T) = p
  · exact Or.inl hpq
  · exact Or.inr ((Nat.coprime_primes hp hq).mpr (Ne.symm hpq))

theorem cent_subgroupOf_normal {G : Type*} [Group G] {M N : Subgroup G}
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) :
    ((M ⊓ Subgroup.centralizer (N : Set G)).subgroupOf M).Normal := by
  refine ⟨fun c hc m => ?_⟩
  obtain ⟨hcM, hcC⟩ := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hc)
  refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
  · exact M.mul_mem (M.mul_mem m.2 hcM) (M.inv_mem m.2)
  · rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : (m : G)⁻¹ * x * (m : G) ∈ N := by
      have h1 := (Subgroup.mem_normalizer_iff.1 (hMN (M.inv_mem m.2)) x).1 hx
      simpa using h1
    have h2 := Subgroup.mem_centralizer_iff.1 hcC _ hx'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc x * ((m : G) * (c : G) * (m : G)⁻¹)
        = (m : G) * (((m : G)⁻¹ * x * (m : G)) * (c : G)) * (m : G)⁻¹ := by group
      _ = (m : G) * ((c : G) * ((m : G)⁻¹ * x * (m : G))) * (m : G)⁻¹ := by rw [← h2]
      _ = (m : G) * (c : G) * (m : G)⁻¹ * x := by group

theorem sylow_eq_pCore_of {C : Type*} [Group C] [Finite C] {a b : ℕ}
    (hcard : Nat.card C = 2 ^ a * 5 ^ b) (hO2 : CFSG.pCore 2 C = ⊥) (S : Sylow 5 C)
    (hSab : ∀ x ∈ (S : Subgroup C), ∀ y ∈ (S : Subgroup C), x * y = y * x) :
    (S : Subgroup C) = CFSG.pCore 5 C := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have := Fintype.ofFinite C
  have hsolv : Group.IsSolvable C :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (q := 5)
      Nat.prime_two (by norm_num) (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hps := isPSolvable_of_isSolvable (by norm_num : Nat.Prime 5) hsolv
  have hcore : CFSG.pPrimeCore 5 C = ⊥ := by
    have hcop := CFSG.pPrimeCore_coprime_card (p := 5) (G := C)
    have hdvd : Nat.card ↥(CFSG.pPrimeCore 5 C) ∣ 2 ^ a * 5 ^ b :=
      hcard ▸ Subgroup.card_subgroup_dvd_card _
    have h2 : Nat.card ↥(CFSG.pPrimeCore 5 C) ∣ 2 ^ a :=
      Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right _ hcop.symm) hdvd
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    have hp2 : IsPGroup 2 ↥(CFSG.pPrimeCore 5 C) := IsPGroup.of_card hk
    have hle : CFSG.pPrimeCore 5 C ≤ CFSG.pCore 2 C := le_sSup ⟨CFSG.pPrimeCore_normal, hp2⟩
    rw [hO2] at hle
    exact le_bot_iff.1 hle
  have hchar := CFSG.HallHigman.isCharacteristicP_of_isPSolvable hps hcore
  have hPS : CFSG.pCore 5 C ≤ (S : Subgroup C) := CFSG.pCore_isPGroup.le_sylow_of_normal S
  have hSC : (S : Subgroup C) ≤ Subgroup.centralizer (CFSG.pCore 5 C : Set C) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hSab y (hPS hy) x hx
  exact le_antisymm (hSC.trans hchar) hPS

namespace O2Sit

variable {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
  (h : O2Sit M Mp T L V t)
include h

theorem pCore_cent_eq_bot :
    CFSG.pCore 2 ↥(M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))) = ⊥ := by
  have hO2 := D31.pCoreOf_eq_bot h.hB.hD.hyp
  have hle := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2
    (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))) M inf_le_left
    (cent_subgroupOf_normal h.hB.hD.hyp.Mp_normal)
  rw [hO2, le_bot_iff] at hle
  unfold CFSG.Open.pCoreOf at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp hle

theorem sylow_eq_pCore (S : Sylow 5 ↥(M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))) :
    (S : Subgroup ↥(M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))) =
      CFSG.pCore 5 ↥(M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))) := by
  refine sylow_eq_pCore_of h.card_cent_eq h.pCore_cent_eq_bot S fun x hx y hy => ?_
  obtain ⟨-, hcomm, -⟩ := h.five_subgroup (P := (S : Subgroup _).map (Subgroup.subtype _))
    (Subgroup.map_subtype_le _) (S.2.map _)
  exact Subtype.ext (hcomm _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩)

end O2Sit

end CFSG.Quasithin.H13.T326
