module

public import CFSG.RankThree.PartOne.KF.F122PSU
public import CFSG.RankThree.PartOne.KF.U4Group
public import CFSG.RankThree.PartOne.KF.U4Model

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KFU
  CFSG.RankThree.PartOne.KCUnitaryCoord
open CFSG.Assembly.RankThreeEven (localRank)

section Split

variable {f n : ℕ} {K : Type} [Field K]

noncomputable def blkProj (h : UnitaryFieldData 2 f K) {i j : Fin n} (hij : i ≠ j) :
    ↥(blk h hij) →* StatedProj (StatedSU n (2 ^ f) K) :=
  (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K))).comp
    (Subgroup.inclusion (blk_le_unitarySU hij))

theorem blkProj_injective (h : UnitaryFieldData 2 f K) {i j : Fin n} (hij : i ≠ j) {l : Fin n}
    (hli : l ≠ i) (hlj : l ≠ j) : Function.Injective (blkProj h hij) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : (Subgroup.inclusion (blk_le_unitarySU hij) x : StatedSU n (2 ^ f) K) ∈
      (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K) :=
    (QuotientGroup.eq_one_iff _).mp hx
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp h1
  obtain ⟨X, -, hX⟩ := (mem_blk_iff hij).mp x.2
  have hentry : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) l l = 1 := by
    rw [hX, coordEmbed_apply_of_not_mem_left hli hlj]
    simp
  have hsc : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) l l = (c : K) := by
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) l l) hc
    simpa [Matrix.GeneralLinearGroup.scalar] using this.symm
  have hc1 : c = 1 := Units.ext (hsc.symm.trans hentry)
  rw [hc1, map_one] at hc
  exact Subtype.ext hc.symm

theorem blkProj_comm (h : UnitaryFieldData 2 f K) {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (x : ↥(blk h hij))
    (y : ↥(blk h hkl)) : blkProj h hij x * blkProj h hkl y = blkProj h hkl y * blkProj h hij x := by
  change QuotientGroup.mk _ * QuotientGroup.mk _ = QuotientGroup.mk _ * QuotientGroup.mk _
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (blk_comm_of_disjoint hij hkl hik hil hjk hjl x.2 y.2)

theorem two_le_localRank_statedSU_split [Finite K] (h : UnitaryFieldData 2 f K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1) (hn : 4 ≤ n) :
    2 ≤ localRank p (StatedProj (StatedSU n (2 ^ f) K)) := by
  classical
  have hcard : Nat.card h.fixedField = 2 ^ f := h.card_fixedField
  have : CharP h.fixedField 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hcard
  have : Fintype h.fixedField := Fintype.ofFinite _
  obtain ⟨s⟩ := nonempty_gramSU_two_mulEquiv_SL2 h
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let c : Fin n := ⟨2, by omega⟩
  let d : Fin n := ⟨3, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hcd : c ≠ d := by simp [c, d, Fin.ext_iff]
  have hac : a ≠ c := by simp [a, c, Fin.ext_iff]
  have had : a ≠ d := by simp [a, d, Fin.ext_iff]
  have hbc : b ≠ c := by simp [b, c, Fin.ext_iff]
  have hbd : b ≠ d := by simp [b, d, Fin.ext_iff]
  obtain ⟨e₀⟩ := nonempty_blk_mulEquiv h hab
  obtain ⟨e₁⟩ := nonempty_blk_mulEquiv h hcd
  let ι₀ : SpecialLinearGroup (Fin 2) h.fixedField ≃* ↥(blk h hab) := (e₀.trans s).symm
  let ι₁ : SpecialLinearGroup (Fin 2) h.fixedField ≃* ↥(blk h hcd) := (e₁.trans s).symm
  let φ : Fin 2 → SpecialLinearGroup (Fin 2) h.fixedField →* StatedProj (StatedSU n (2 ^ f) K) :=
    ![(blkProj h hab).comp ι₀.toMonoidHom, (blkProj h hcd).comp ι₁.toMonoidHom]
  have hφ : ∀ i, Function.Injective (φ i) := by
    intro i
    fin_cases i
    · exact (blkProj_injective h hab (l := c) hac.symm hbc.symm).comp ι₀.injective
    · exact (blkProj_injective h hcd (l := a) hac had).comp ι₁.injective
  have hcomm : ∀ i j : Fin 2, i ≠ j → ∀ A B : SpecialLinearGroup (Fin 2) h.fixedField,
      φ i A * φ j B = φ j B * φ i A := by
    intro i j hij A B
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact blkProj_comm h hab hcd hac had hbc hbd (ι₀ A) (ι₁ B)
    · exact (blkProj_comm h hab hcd hac had hbc hbd (ι₀ B) (ι₁ A)).symm
    · exact absurd rfl hij
  have hrq : p ∣ Fintype.card h.fixedField - 1 := by
    rw [← Nat.card_eq_fintype_card, hcard]
    exact hpq
  exact CFSG.RankThree.PartTwo.Census.Exceptional.le_localRank_of_commuting_SL2_even
    (ringChar.eq h.fixedField 2) hp hp2 hrq (by norm_num : 1 ≤ 2) φ hφ hcomm

end Split

theorem kf122Row5_holds : KF122Row 5 := by
  intro G _ _ p L hp hp5 hmodel _ α hαp hαinn hLRA
  obtain ⟨f, -, hpq, hC⟩ := hmodel
  refine psu_aut_false (n := 4) hp hp5 hC (by norm_num) ?_ ?_ hαp hαinn hLRA
  · intro hd
    have := Nat.le_of_dvd (by norm_num) (hd.trans (Nat.gcd_dvd_left _ _))
    omega
  · intro f₀ k _ _ _ h₀ hf
    have hpk : p ∣ 2 ^ f₀ - 1 := dvd_two_pow_sub_one_of_mul hp (hf ▸ hpq)
    exact two_le_localRank_statedSU_split h₀ hp (by omega) hpk (by norm_num)

theorem kf122Row6_holds : KF122Row 6 := by
  intro G _ _ p L hp hp5 hmodel _ α hαp hαinn hLRA
  obtain ⟨f, -, hpq, hC⟩ := hmodel
  refine psu_aut_false (n := 5) hp hp5 hC (by norm_num) ?_ ?_ hαp hαinn hLRA
  · intro hd
    have h2 : p ∣ 2 ^ f + 1 := hd.trans (Nat.gcd_dvd_right _ _)
    have h3 : p ∣ 2 ^ f - 1 := hpq
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have h4 : p ∣ 2 := by
      have := Nat.dvd_sub h2 h3
      have e : 2 ^ f + 1 - (2 ^ f - 1) = 2 := by omega
      rwa [e] at this
    have := Nat.le_of_dvd (by norm_num) h4
    omega
  · intro f₀ k _ _ _ h₀ hf
    have hpk : p ∣ 2 ^ f₀ - 1 := dvd_two_pow_sub_one_of_mul hp (hf ▸ hpq)
    exact two_le_localRank_statedSU_split h₀ hp (by omega) hpk (by norm_num)

end CFSG.RankThree.PartOne
