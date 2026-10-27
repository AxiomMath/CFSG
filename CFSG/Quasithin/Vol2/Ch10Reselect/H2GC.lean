module

public import CFSG.Quasithin.Vol2.Ch10Reselect.ActML2
public import CFSG.Quasithin.Vol2.Ch10Reselect.Rank
public import CFSG.Quasithin.Vol2.Ch10Reselect.ModelAlgUniq
public import CFSG.Quasithin.Vol2.Ch10Reselect.GaloisDescent

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10 CFSG.Quasithin.Vol2.Ch10.SecA
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {K : Type} [Field K]

theorem false_of_odd_prime_dvd (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I) (hlt : L < fsuL0 T L)
    (hA : Concl326A T L I) [Finite K] [CharP K 2]
    (M : RModel T L I K) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {z : G} (hz : z ∈ fsuML T L) {σ : RingAut K} {B₂ : GL (Fin 2) K}
    (h2 : actML M ⟨t * z * t⁻¹, conj_mem_fsuML h37 h38 hfsu hlt (le_fsuM T L ht) hz⟩ =
      phi K 1 σ B₂)
    (hzm : z ^ orderOf σ ∈ Subgroup.centralizer (fsuVM T L I : Set G))
    {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (hrm : r ∣ orderOf σ) (hrL : r ∣ Nat.card L) : False := by
  obtain ⟨m, hm⟩ : ∃ m, orderOf σ = m := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, orderOf (z ^ m) = s := ⟨_, rfl⟩
  rw [hm] at hzm hrm
  have hmpos : 0 < m := hm ▸ orderOf_pos σ
  have hspos : 0 < s := hs ▸ orderOf_pos (z ^ m)
  have hrpos : 0 < r := (Fact.out : Nat.Prime r).pos
  have hzM : z ∈ fsuM T L := (Subgroup.mem_inf.mp hz).1
  have hzmM : z ^ m ∈ fsuM T L := (fsuM T L).pow_mem hzM m
  have hzms : (z ^ m) ^ s = 1 := by
    rw [← hs]
    exact pow_orderOf_eq_one _
  by_cases hrs : r ∣ s
  ·
    have hsr : s / r ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hspos hrs) hrpos).ne'
    have hdvd : s / r ∣ orderOf (z ^ m) := by
      rw [hs]
      exact Nat.div_dvd_of_dvd hrs
    have hcr : orderOf ((z ^ m) ^ (s / r)) = r := by
      rw [orderOf_pow_of_dvd hsr hdvd, hs, Nat.div_div_self hrs hspos.ne']
    exact false_of_mem_centralizer_of_orderOf_eq h37 h38 hfsu hlt hA hr2 hrL
      ((fsuM T L).pow_mem hzmM _) (Subgroup.pow_mem _ hzm _) hcr
  ·
    obtain ⟨n, hn⟩ : ∃ n, n = (m / r) * s := ⟨_, rfl⟩
    have hdiv : (m / r) * r = m := Nat.div_mul_cancel hrm
    have hmr : 0 < m / r := Nat.div_pos (Nat.le_of_dvd hmpos hrm) hrpos
    have hwL : z ^ n ∉ fsuL0 T L := by
      intro hwL0
      have hzn : z ^ n ∈ fsuML T L := (fsuML T L).pow_mem hz n
      have htw : t * z ^ n * t⁻¹ ∈ fsuL0 T L :=
        (Subgroup.mem_normalizer_iff.mp (le_fsuM T L ht) (z ^ n)).mp hwL0
      obtain ⟨g, hg⟩ := exists_rho_of_mem_fsuL0 h37 h38 hfsu hlt hA M htw
      have htzn : t * z ^ n * t⁻¹ ∈ fsuML T L :=
        conj_mem_fsuML h37 h38 hfsu hlt (le_fsuM T L ht) hzn
      have hEn : (⟨t * z ^ n * t⁻¹, htzn⟩ : ↥(fsuML T L)) =
          (⟨t * z * t⁻¹, conj_mem_fsuML h37 h38 hfsu hlt (le_fsuM T L ht) hz⟩ :
            ↥(fsuML T L)) ^ n := by
        apply Subtype.ext
        simp only [Subgroup.coe_pow, conj_pow]
      have hact : actML M ⟨t * z ^ n * t⁻¹, htzn⟩ = phi K 1 σ B₂ ^ n := by
        rw [hEn, map_pow, h2]
      obtain ⟨B', hB'⟩ := phi_one_pow σ B₂ n
      have heq : phi K 1 (σ ^ n) B' = phi K g 1 1 := by
        rw [← hB', ← hact, hg, rhoSL_eq_phi]
      obtain ⟨-, hσn, -⟩ := phi_inj heq
      have hdvd : m ∣ n := by
        rw [← hm]
        exact orderOf_dvd_of_pow_eq_one hσn
      rw [hn] at hdvd
      have h1 : (m / r) * r ∣ (m / r) * s := by
        rw [hdiv]
        exact hdvd
      exact hrs (Nat.dvd_of_mul_dvd_mul_left hmr h1)
    have hwr1 : (z ^ n) ^ r = 1 := by
      have hnr : n * r = s * m := by
        rw [hn, show (m / r) * s * r = s * ((m / r) * r) by ring, hdiv]
      rw [← pow_mul, hnr, pow_mul', hzms]
    have hw1 : z ^ n ≠ 1 := fun h => hwL (by rw [h]; exact (fsuL0 T L).one_mem)
    have hwr : orderOf (z ^ n) = r := orderOf_eq_prime hwr1 hw1
    exact hwL (mem_fsuL0_of_orderOf_eq h37 h38 hfsu hlt hA hr2 hrL
      ((fsuM T L).pow_mem hzM n) hwr)

end CFSG.Quasithin.Vol2.Ch10Reselect
