module

public import CFSG.YGroups.Y443.EdgeIntersection
public import CFSG.YGroups.Y443.Tri.Parabolic2
public import CFSG.YGroups.DCE.B433Y333Check
public import Certificates.Certificate10093
public import Certificates.Certificate10095
public import Certificates.Certificate10098
public import Certificates.Certificate10100
public import Certificates.Certificate10101
public import Certificates.Certificate10102
public import Certificates.Certificate10103
public import Certificates.Certificate10104
public import Certificates.Certificate9355

public section

namespace CFSG.YGroups.Y443Edge

open CFSG.Open (MonsterY443Derived MonsterY443Gen)
open CFSG.YGroups.DCE.B433 (P333)

@[expose] noncomputable def RQ : Subgroup Q343 :=
  Subgroup.closure ((fun c => Q343.π (yGen 3 4 3 c)) '' {c | c < 11 ∧ c ≠ 7})

theorem shiftAt3_ne_four (c : ℕ) : shiftAt 3 c ≠ 4 := by
  unfold shiftAt
  split_ifs <;> omega

theorem y443LetterOfGen_eq_eight_iff {s : MonsterY443Gen} :
    y443LetterOfGen s = 8 ↔ s = y443E2 := by
  constructor
  · intro h
    rw [← y443GenOfLetter_letterOfGen s, h]
    rfl
  · rintro rfl
    rfl

theorem map_RQ_eq :
    RQ.map y443Q343Hom = y443R := by
  rw [RQ, MonoidHom.map_closure, y443R]
  congr 1
  ext m
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨c, ⟨hc, hc7⟩, rfl⟩, rfl⟩
    have hl : shiftAt 3 c < 12 := by unfold shiftAt; split_ifs <;> omega
    refine ⟨y443GenOfLetter (shiftAt 3 c), ⟨?_, ?_⟩, (y443Q343Hom_gen hc).symm⟩
    · intro h
      have h4 := y443LetterOfGen_eq_four_iff.2 h
      rw [y443LetterOfGen_genOfLetter _ hl] at h4
      exact shiftAt3_ne_four c h4
    · intro h
      have h8 := y443LetterOfGen_eq_eight_iff.2 h
      rw [y443LetterOfGen_genOfLetter _ hl] at h8
      unfold shiftAt at h8
      split_ifs at h8 <;> omega
  · rintro ⟨s, ⟨hs4, hs8⟩, rfl⟩
    have hs4' : y443LetterOfGen s ≠ 4 := y443LetterOfGen_eq_four_iff.not.2 hs4
    have hs8' : y443LetterOfGen s ≠ 8 := y443LetterOfGen_eq_eight_iff.not.2 hs8
    have hl := y443LetterOfGen_lt s
    let c := if y443LetterOfGen s ≤ 3 then y443LetterOfGen s else y443LetterOfGen s - 1
    have hc : c < 11 := by simp only [c]; split_ifs <;> omega
    have hc7 : c ≠ 7 := by simp only [c]; split_ifs <;> omega
    have hsh : shiftAt 3 c = y443LetterOfGen s := by
      simp only [c]
      unfold shiftAt
      split_ifs <;> omega
    refine ⟨Q343.π (yGen 3 4 3 c), ⟨c, ⟨hc, hc7⟩, rfl⟩, ?_⟩
    rw [y443Q343Hom_gen hc, y443Tl, hsh, y443GenOfLetter_letterOfGen]

theorem map_beta_RQ :
    RQ.map beta = P333 := by
  rw [RQ, MonoidHom.map_closure, P333]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨c, ⟨hc, hc7⟩, rfl⟩, rfl⟩
    refine ⟨cyc343Letter c, ⟨cyc343Letter_lt c hc, ?_⟩, (beta_gen hc).symm⟩
    interval_cases c <;> simp_all [cyc343Letter]
  · rintro ⟨l, ⟨hl, hl4⟩, rfl⟩
    refine ⟨Q343.π (yGen 3 4 3 (cyc433Letter l)), ⟨cyc433Letter l, ⟨cyc433Letter_lt l hl, ?_⟩,
      rfl⟩, ?_⟩
    · interval_cases l <;> simp_all [cyc433Letter]
    · rw [beta_gen (cyc433Letter_lt l hl), cyc343Letter_cyc433Letter l hl]

theorem qc_mem_RQ : qc ∈ RQ := by
  have hF : Y343.F 1 2 3 = (yGen 3 4 3 0 * yGen 3 4 3 1 * yGen 3 4 3 2 * yGen 3 4 3 3 *
      yGen 3 4 3 4 * yGen 3 4 3 5 * yGen 3 4 3 8) ^ 9 := rfl
  have hmem : ∀ c < 11, c ≠ 7 → Q343.π (yGen 3 4 3 c) ∈ RQ := fun c hc hc7 =>
    Subgroup.subset_closure ⟨c, ⟨hc, hc7⟩, rfl⟩
  rw [qc, hF, map_pow]
  refine RQ.pow_mem ?_ 9
  simp only [map_mul]
  refine RQ.mul_mem (RQ.mul_mem (RQ.mul_mem (RQ.mul_mem (RQ.mul_mem (RQ.mul_mem ?_ ?_) ?_) ?_)
    ?_) ?_) ?_ <;> exact hmem _ (by norm_num) (by norm_num)

variable {G : Type*} [Group G] (f : MonsterY443Derived →* G)

theorem card_RQ
    (hN : Q343N ≤ Nat.card (y443H.map f)) : Nat.card RQ = 2 * Nat.card P333 := by
  have := YGroups.Q343_finite_card_le.1
  have hqc : qc ≠ 1 := by
    intro h1
    have hinj : Function.Injective beta := by
      rw [← MonoidHom.ker_eq_bot_iff, ker_beta, h1, Subgroup.zpowers_one_eq_bot]
    have h2 : Nat.card Q343 ≤ Nat.card B433 := by
      have := YGroups.B433_finite_card_le.1
      exact Nat.card_le_card_of_injective _ hinj
    have h3 : Q343N ≤ Nat.card Q343 := by
      have := Nat.card_le_card_of_surjective _ (rho f).rangeRestrict_surjective
      rw [range_rho] at this
      exact hN.trans this
    have h4 := YGroups.B433_finite_card_le.2
    have hQ : Q343N = 2 * 4154781481226426191177580544000000 := by unfold Q343N; norm_num
    omega
  have h2 : Nat.card (Subgroup.zpowers qc) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two, qc_mul_self]) hqc
  have hker : (beta.domRestrict RQ).ker = (Subgroup.zpowers qc).subgroupOf RQ := by
    rw [MonoidHom.ker_domRestrict, ker_beta]
  have hle : Subgroup.zpowers qc ≤ RQ := (Subgroup.zpowers_le).2 qc_mem_RQ
  have hcardker : Nat.card (beta.domRestrict RQ).ker = 2 := by
    rw [hker, ← h2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hrange : (beta.domRestrict RQ).range = P333 := by
    rw [MonoidHom.domRestrict_range, map_beta_RQ]
  have := Subgroup.card_ker_mul_card_range (beta.domRestrict RQ)
  rw [hcardker, hrange] at this
  exact this.symm

theorem card_map_y443R_ge
    (hN : Q343N ≤ Nat.card (y443H.map f)) :
    306129918735099415756800 ≤ Nat.card (y443R.map f) := by
  have hR : y443R.map f = RQ.map (rho f) := by
    rw [← map_RQ_eq, Subgroup.map_map]
    rfl
  rw [hR, Subgroup.card_map_of_injective (rho_injective f hN), card_RQ f hN]
  have := DCE.B433.card_P333_ge (card_B433_ge f hN)
  omega

end CFSG.YGroups.Y443Edge
