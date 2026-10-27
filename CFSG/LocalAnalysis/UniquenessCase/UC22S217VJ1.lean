module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNineteenShapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.JankoOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s217v_not_sq_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 2 ∣ 175560 := by
  intro h
  have hd : p ∣ 2 ^ 3 * (3 * (5 * (7 * (11 * 19)))) := by
    norm_num; exact (dvd_pow_self p two_ne_zero).trans h
  have key : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hpq =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 hpq
  rcases hp.dvd_mul.1 hd with h2 | hd
  · exact hp2 (key 2 Nat.prime_two (hp.dvd_of_dvd_pow h2))
  rcases hp.dvd_mul.1 hd with h3 | hd
  · rw [key 3 Nat.prime_three h3] at h; norm_num at h
  rcases hp.dvd_mul.1 hd with h5 | hd
  · rw [key 5 (by norm_num) h5] at h; norm_num at h
  rcases hp.dvd_mul.1 hd with h7 | hd
  · rw [key 7 (by norm_num) h7] at h; norm_num at h
  rcases hp.dvd_mul.1 hd with h11 | h19
  · rw [key 11 (by norm_num) h11] at h; norm_num at h
  · rw [key 19 (by norm_num) h19] at h; norm_num at h

theorem uc22s217v_centralizesBar_of_isJ1 {L : Subgroup G} {r : ℕ} (hJ1 : IsJ1 (Bar2 L))
    (hr : r.Prime) (hrJ : ¬ r ∣ 175560) {a : G} (ha : a ∈ normalizer (L : Set G))
    (har : a ^ r = 1) : CentralizesBar a L := by
  let m : ↥(normalizer (L : Set G)) := ⟨a, ha⟩
  have hmr : m ^ r = 1 := Subtype.ext (by simp [m, har])
  have hα : UC6S846.rhoL L m ^ r = 1 := by rw [← map_pow, hmr, map_one]
  obtain ⟨hcard, -, hinn⟩ := kJ1_holds (Bar2 L) hJ1
  obtain ⟨x, hx⟩ := hinn (UC6S846.rhoL L m)
  have hN : UC6S846.rhoL L m ^ Nat.card (Bar2 L) = 1 := by
    rw [hx, ← map_pow, pow_card_eq_one', map_one]
  rw [hcard] at hN
  have h1 : orderOf (UC6S846.rhoL L m) ∣ Nat.gcd r 175560 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hα) (orderOf_dvd_of_pow_eq_one hN)
  rw [((Nat.Prime.coprime_iff_not_dvd hr).2 hrJ).gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff]
    at h1
  refine ⟨ha, fun l hl => ?_⟩
  have h2 : UC6S846.rhoL L m (QuotientGroup.mk ⟨l, hl⟩) = QuotientGroup.mk ⟨l, hl⟩ := by
    rw [h1, MulAut.one_apply]
  exact (UC6S846.rhoL_fix_iff L m ⟨l, hl⟩).1 h2

theorem uc22s217v_isJ1_of_mem {M L K : Subgroup G} (hJ1 : IsJ1 (Bar2 L))
    (hK : K ∈ conjSetOf M L) : IsJ1 (Bar2 K) := by
  obtain ⟨g, -, rfl⟩ := hK
  obtain ⟨e⟩ := uc22p20d_bar2_conj g L
  obtain ⟨φ⟩ := hJ1
  exact ⟨e.symm.trans φ⟩

theorem uc22s217v_exists_ne {M L : Subgroup G} (hL : L ∈ calC M)
    (hnN : ¬ (L.subgroupOf M).Normal) : ∃ K ∈ conjSetOf M L, K ≠ L := by
  have hnN' : ¬ M ≤ normalizer (L : Set G) := fun h =>
    hnN ((Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).2 h)
  obtain ⟨m, hmM, hmN⟩ := SetLike.not_le_iff_exists.1 hnN'
  exact ⟨L.map (MulAut.conj m).toMonoidHom, ⟨m, hmM, rfl⟩, fun he =>
    hmN (UC6S846.mem_normalizer_iff_map_conj.2 he)⟩

theorem uc22s217v_mem_uniqueSet (D : Data G) (h8107 : F08.R8107 D) {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hLK : L ≠ K) (hJL : IsJ1 (Bar2 L))
    (hJK : IsJ1 (Bar2 K)) {A : Subgroup G} (hAL : A ≤ L) (hA : Nat.card A = 3) :
    A ∈ uniqueSet D.M :=
  mem_uniqueSet_of_card_eq_three D h8107 hL hK hLK
    (pRank_three_eq_one_and_thin8_or_isU3 (Or.inr (Or.inr (Or.inl hJL))))
    (pRank_three_eq_one_and_thin8_or_isU3 (Or.inr (Or.inr (Or.inl hJK)))) hAL hA

end CFSG.LocalAnalysis.UniquenessCase.UC22
