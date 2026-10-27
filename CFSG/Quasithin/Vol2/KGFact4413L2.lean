module

public import CFSG.Quasithin.Vol2.KGFact4413X
public import CFSG.Quasithin.H13.KGFact22TorL2
public import CFSG.RankThree.PartOne.K159.BorelSL
public import CFSG.Quasithin.Vol2.Ch12Sec2E22BorelLift

public section

namespace CFSG.Quasithin.H13.KG4413

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique CFSG.Quasithin.H13.KG22

theorem cartanWeyl_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] {n : ℕ} (h : CartanWeyl Y n)
    (e : Y ≃* Y') : CartanWeyl Y' n := by
  intro S D hS hDN hND hDS
  have hmm : ∀ T : Subgroup Y', (T.map e.symm.toMonoidHom).map e.toMonoidHom = T := by
    intro T
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨e.symm x, ⟨x, hx, rfl⟩, by simp⟩
  have hN : ∀ T : Subgroup Y', Subgroup.normalizer ((T.map e.symm.toMonoidHom : Subgroup Y) :
      Set Y) = (Subgroup.normalizer (T : Set Y')).map e.symm.toMonoidHom :=
    fun T => (Subgroup.map_equiv_normalizer_eq T e.symm).symm
  have h1 := h (S.map e.symm.toMonoidHom) (D.map e.symm.toMonoidHom)
    (isSylowTwoOf_map e.symm.surjective hS) (by rw [hN]; exact Subgroup.map_mono hDN)
    (by rw [hN, ← Subgroup.map_sup]; exact Subgroup.map_mono hND)
    (by rw [← Subgroup.map_inf_eq _ _ _ e.symm.injective, hDS, Subgroup.map_bot])
  have h2 := h1.map e
  rwa [hmm, hmm] at h2

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def dL2 (K : Type) [Field K] [CharP K 2] :
    Subgroup (projectiveSL 2 K) :=
  (tT.range).map (proj 2 K)

omit [Finite K] [CharP K 2] in
theorem units_pow_card_sub_one (a : Kˣ) : a ^ (Nat.card K - 1) = 1 := by
  rw [← Nat.card_units]
  exact pow_card_eq_one'

omit [Finite K] in
theorem pow_eq_one_of_mem_dL2 {d : projectiveSL 2 K} (hd : d ∈ dL2 K) :
    d ^ (Nat.card K - 1) = 1 := by
  obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hd
  rw [← map_pow, ← map_pow, units_pow_card_sub_one, map_one, map_one]

theorem normalizer_projUnitriangular_two :
    Subgroup.normalizer (projUnitriangular 2 K : Set (projectiveSL 2 K)) =
      (upperTriangular 2 K).map (proj 2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [normalizer_projUnitriangular 2]
  rfl

omit [Finite K] in
theorem proj_w2_not_mem : proj 2 K w2 ∉ (upperTriangular 2 K).map (proj 2 K) := by
  intro h
  have h1 : w2 ∈ ((upperTriangular 2 K).map (proj 2 K)).comap (proj 2 K) := h
  rw [Subgroup.comap_map_eq, ker_proj, sup_eq_left.2 (scalars_le_upperTriangular 2 K)] at h1
  exact w2_not_mem_upperTriangular h1

theorem isPGroup_projUnitriangular_two : IsPGroup 2 (projUnitriangular 2 K) := by
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 2) (by norm_num)
  rw [← hP]
  exact P.isPGroup'

theorem dL2_complement :
    dL2 K ≤ Subgroup.normalizer (projUnitriangular 2 K : Set (projectiveSL 2 K)) ∧
      Subgroup.normalizer (projUnitriangular 2 K : Set (projectiveSL 2 K)) ≤
        dL2 K ⊔ projUnitriangular 2 K ∧ dL2 K ⊓ projUnitriangular 2 K = ⊥ := by
  rw [normalizer_projUnitriangular_two]
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact Subgroup.mem_map_of_mem _ (tT_mem_upperTriangular a)
  · have h := Subgroup.map_mono (f := proj 2 K) upperTriangular_le_two
    rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_bot, sup_bot_eq] at h
    exact h
  · rw [eq_bot_iff]
    rintro x ⟨hxD, hxU⟩
    obtain ⟨m, hm⟩ := isPGroup_projUnitriangular_two ⟨x, hxU⟩
    have hm' : x ^ 2 ^ m = 1 := congrArg Subtype.val hm
    have hodd : Odd (orderOf x) := by
      have h1 := orderOf_dvd_of_pow_eq_one (pow_eq_one_of_mem_dL2 hxD)
      exact (RankThree.PartOne.K159.odd_card_sub_one (K := K)).of_dvd_nat h1
    exact Subgroup.mem_bot.mpr (eq_one_of_odd_of_pow_two_pow hodd hm')

theorem index_upperTriangular_two :
    (upperTriangular 2 K).index = Nat.card (Sylow 2 (SpecialLinearGroup (Fin 2) K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := K) 2 (n := 2) (by norm_num)
  rw [Sylow.card_eq_index_normalizer P, ← normalizer_unitriangular, ← hP]
  rfl

theorem not_dvd_index_normalizer_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) :
    ¬ p ∣ (Subgroup.normalizer (projUnitriangular 2 K : Set (projectiveSL 2 K))).index := by
  rw [normalizer_projUnitriangular_two, Subgroup.index_map_eq _ (proj_surjective 2 K)
    (by rw [ker_proj]; exact scalars_le_upperTriangular 2 K), index_upperTriangular_two]
  have hp3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  exact (RankThree.PartOne.K159.borelFactsGrp_specialLinear hp hpq le_rfl hp3).2.1

omit [Finite K] in
theorem proj_w2_conj_dL2 {d : projectiveSL 2 K} (hd : d ∈ dL2 K) :
    proj 2 K w2 * d * (proj 2 K w2)⁻¹ = d⁻¹ := by
  obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hd
  rw [← map_inv, ← map_mul, ← map_mul, w2_conj_tT, map_inv]

theorem weylOut_projectiveSL2 {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    WeylOut (projUnitriangular 2 K) (dL2 K) n := by
  refine ⟨fun p hp hp2 hpq => not_dvd_index_normalizer_two hp hp2 (hK ▸ hpq),
    fun d hd => ?_, proj 2 K w2, ?_, ?_, fun d hd => ⟨fun _ => proj_w2_conj_dL2 hd,
      fun h1 => ?_⟩⟩
  · rw [pow_mul, ← hK, pow_eq_one_of_mem_dL2 hd, one_pow]
  · rw [normalizer_projUnitriangular_two]
    exact proj_w2_not_mem
  · rw [← map_mul, w2_mul_self, map_one]
  · rw [proj_w2_conj_dL2 hd]
    have h2 := pow_eq_one_of_mem_dL2 hd
    rw [hK] at h2
    have h3 : d ^ 2 = 1 := by
      have e : 2 ^ n + 1 = (2 ^ n - 1) + 2 := by
        have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        omega
      rw [e, pow_add, h2, one_mul] at h1
      exact h1
    exact inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h3)

theorem cartanWeyl_projectiveSL2 {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    CartanWeyl (projectiveSL 2 K) n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 2) (by norm_num)
  have hS : IsSylowTwoOf (projUnitriangular 2 K) ⊤ := hP ▸ isSylowTwoOf_of_sylow P
  obtain ⟨h1, h2, h3⟩ := dL2_complement (K := K)
  exact cartanWeyl_of_exists hS h1 h2 h3 (weylOut_projectiveSL2 hK)

theorem cartanWeyl_of_isPSL2 {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n) (hX : IsPSL 2 2 n X) :
    CartanWeyl X n := by
  obtain ⟨-, K', _, _, hK, ⟨e⟩⟩ := hX
  have : CharP K' 2 := finite_field_prime_power_characteristic Nat.prime_two hn hK
  have e' : X ≃* projectiveSL 2 K' := e.trans (Id2519.projectiveSLEquivStatedProj 2 K').symm
  exact cartanWeyl_of_mulEquiv (cartanWeyl_projectiveSL2 hK) e'.symm

end CFSG.Quasithin.H13.KG4413
