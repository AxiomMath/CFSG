module

public import CFSG.Quasithin.Recognition.U33Local
public import CFSG.Quasithin.Recognition.U33Models
public import CFSG.Quasithin.Recognition.U33Bridge

public section

namespace CFSG.Quasithin

open scoped MatrixGroups
open CFSG.Open (WreathedTwoGroup)

private theorem natCard_centralizer_mulEquiv {G M : Type*} [Group G] [Group M] (e : G ≃* M)
    (a : G) : Nat.card (Subgroup.centralizer ({e a} : Set M)) =
      Nat.card (Subgroup.centralizer ({a} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨e.symm x.1, ?_⟩
      invFun := fun x => ⟨e x.1, ?_⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    apply e.injective
    have := (Subgroup.mem_centralizer_iff.mp x.2) (e a) rfl
    simpa using this
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    have := (Subgroup.mem_centralizer_iff.mp x.2) a rfl
    rw [← map_mul, ← map_mul, this]

private theorem natCard_centralizer_conj {G : Type*} [Group G] (z g : G) :
    Nat.card (Subgroup.centralizer ({g * z * g⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({z} : Set G)) :=
  natCard_centralizer_mulEquiv (MulAut.conj g) z

private theorem primePow_eq_three_of_dvd_96 {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hodd : p ^ k % 2 = 1) (hd : p ^ k ∣ 96) : p = 3 ∧ k = 1 := by
  have hmem : p ^ k ∈ Nat.divisors 96 := Nat.mem_divisors.mpr ⟨hd, by norm_num⟩
  have key : ∀ q ∈ Nat.divisors 96, q % 2 = 1 → q = 1 ∨ q = 3 := by decide
  rcases key _ hmem hodd with h | h
  · exact absurd h (Nat.one_lt_pow hk.ne' hp.one_lt).ne'
  · exact (Nat.Prime.pow_eq_iff Nat.prime_three).mp h

theorem u33_recognition_of_wreathed_sylow {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hABG : ABGWreathedRecognition) {z : G} (hz : orderOf z = 2)
    (hQ : Nonempty (CFSG.Open.quasithinGenFitting (Subgroup.centralizer ({z} : Set G)) ≃*
      Z4StarQ8))
    (hHQ : IsSymThreeQuotient ((CFSG.Open.quasithinGenFitting
      (Subgroup.centralizer ({z} : Set G))).subgroupOf (Subgroup.centralizer ({z} : Set G))))
    (hweak : ¬ IsWeaklyClosedIn (Subgroup.zpowers z)
      (CFSG.Open.quasithinGenFitting (Subgroup.centralizer ({z} : Set G))))
    (T : Sylow 2 G) (hT : Nonempty ((T : Subgroup G) ≃* WreathedTwoGroup 2)) :
    Nonempty (G ≃* CFSG.Open.PSU3 3 1) := by
  obtain ⟨hH96, hconj⟩ := u33_local_analysis hz hQ hHQ hweak T hT
  have hnonab : ∃ a b : G, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have : IsMulCommutative G := ⟨⟨hc⟩⟩
    have hprime := Group.is_simple_iff_prime_card.mp ‹IsSimpleGroup G›
    have htop : Subgroup.centralizer ({z} : Set G) = ⊤ :=
      (Subgroup.eq_top_iff' _).mpr fun g =>
        Subgroup.mem_centralizer_iff.mpr fun h hh => hc h g
    have hcard : Nat.card G = 96 := by
      rw [← hH96, htop, Subgroup.card_top]
    rw [hcard] at hprime
    norm_num at hprime
  have key : ∀ {M : Type} [Group M] (e : G ≃* M) (y : M), y * y = 1 → y ≠ 1 →
      Nat.card (Subgroup.centralizer ({y} : Set M)) = 96 := by
    intro M _ e y hy2 hy1
    have hu2 : e.symm y * e.symm y = 1 := by rw [← map_mul, hy2, map_one]
    have hu1 : e.symm y ≠ 1 := fun h => hy1 (by simpa using congrArg e h)
    obtain ⟨g, hg⟩ := hconj _ hu2 hu1
    have h1 := natCard_centralizer_mulEquiv e (e.symm y)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [h1, ← hg, natCard_centralizer_conj, hH96]
  rcases hABG G hnonab T ⟨2, le_rfl, hT⟩ with ⟨p, k, hp, hk, hmod, ⟨e⟩⟩ | ⟨p, k, hp, hk, hmod, ⟨e⟩⟩
  ·
    exfalso
    have hp2 : p ≠ 2 := by
      rintro rfl
      have : 2 ∣ 2 ^ k := dvd_pow_self 2 hk.ne'
      omega
    obtain ⟨y, hy2, hy1, hdvd⟩ := psl3_exists_involution_centralizer_dvd p k hp2 hk
    rw [key e y hy2 hy1] at hdvd
    obtain ⟨rfl, rfl⟩ := primePow_eq_three_of_dvd_96 hp.out hk (by omega) hdvd
    norm_num at hmod
  ·
    have hp2 : p ≠ 2 := by
      rintro rfl
      have : 2 ∣ 2 ^ k := dvd_pow_self 2 hk.ne'
      omega
    obtain ⟨y, hy2, hy1, hdvd⟩ := psu3_exists_involution_centralizer_dvd p k hp2 hk
    rw [key e y hy2 hy1] at hdvd
    obtain ⟨rfl, rfl⟩ := primePow_eq_three_of_dvd_96 hp.out hk (by omega) hdvd
    exact ⟨e⟩

theorem u33_recognition_of_wreathed_sylow_of_centralProduct {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hABG : ABGWreathedRecognition) {z : G} (hz : orderOf z = 2)
    (hQ : IsCentralProductZ4Q8 (CFSG.Open.quasithinGenFitting
      (Subgroup.centralizer ({z} : Set G))))
    (hHQ : IsSymThreeQuotient ((CFSG.Open.quasithinGenFitting
      (Subgroup.centralizer ({z} : Set G))).subgroupOf (Subgroup.centralizer ({z} : Set G))))
    (hweak : ¬ IsWeaklyClosedIn (Subgroup.zpowers z)
      (CFSG.Open.quasithinGenFitting (Subgroup.centralizer ({z} : Set G))))
    (T : Sylow 2 G) (hT : Nonempty ((T : Subgroup G) ≃* WreathedTwoGroup 2)) :
    Nonempty (G ≃* CFSG.Open.PSU3 3 1) :=
  u33_recognition_of_wreathed_sylow hABG hz
    (nonempty_mulEquiv_Z4StarQ8_of_isCentralProductZ4Q8 hQ) hHQ hweak T hT

theorem u33_recognition_of_wreathed_sylow_of_pCore {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hABG : ABGWreathedRecognition) {z : G} (hz : orderOf z = 2)
    (hC : Subgroup.centralizer ({z} : Set G) ⊓
      Subgroup.centralizer (CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) : Set G) ≤
        CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))
    (hQ : IsCentralProductZ4Q8 (CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({z} : Set G))))
    (hHQ : IsSymThreeQuotient ((CFSG.Open.pCoreOf 2
      (Subgroup.centralizer ({z} : Set G))).subgroupOf (Subgroup.centralizer ({z} : Set G))))
    (hweak : ¬ IsWeaklyClosedIn (Subgroup.zpowers z)
      (CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({z} : Set G))))
    (T : Sylow 2 G) (hT : Nonempty ((T : Subgroup G) ≃* WreathedTwoGroup 2)) :
    Nonempty (G ≃* CFSG.Open.PSU3 3 1) := by
  have hF : CFSG.Open.quasithinGenFitting (Subgroup.centralizer ({z} : Set G)) =
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) :=
    (quasithinGenFitting_eq_pCoreOf_iff _ 2).mpr hC
  rw [← hF] at hQ hHQ hweak
  exact u33_recognition_of_wreathed_sylow_of_centralProduct hABG hz hQ hHQ hweak T hT

end CFSG.Quasithin
