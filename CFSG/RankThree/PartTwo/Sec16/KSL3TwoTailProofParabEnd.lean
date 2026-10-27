module

public import CFSG.RankThree.PartTwo.Sec16.KSL3TwoTailProofParabDiag
import CFSG.RankThree.PartTwo.Sec16.KSL3TwoTailProofParabTwo

public section

namespace CFSG.RankThree.PartTwo.Sec16

namespace ProofKS1623Parab

open CFSG
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem le_centralizer_map {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') {b : G}
    {P : Subgroup G} (hPC : P ≤ Subgroup.centralizer ({b} : Set G)) :
    P.map e.toMonoidHom ≤ Subgroup.centralizer ({e b} : Set G') := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have := Subgroup.mem_centralizer_singleton_iff.mp (hPC hx)
  change e x * e b = e b * e x
  rw [← map_mul, ← map_mul, this]

theorem parabConcl_one {m : ℕ} (hm : 1 ≤ m) (h31 : 2 ^ m % 3 = 1) (h9 : 2 ^ m % 9 ≠ 1)
    {b : projectiveSL 3 (GaloisField 2 m)} (hb : orderOf b = 3) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {P : Subgroup (projectiveSL 3 (GaloisField 2 m))}
    (hPC : P ≤ Subgroup.centralizer ({b} : Set (projectiveSL 3 (GaloisField 2 m))))
    (hPel : CFSG.Assembly.IsElemAbelian p P) (hPc : Nat.card P = p ^ 2) :
    ParabConcl b P p m := by
  set F := GaloisField 2 m with hFdef
  have hFc : Nat.card F = 2 ^ m := GaloisField.card 2 m (by omega)
  have hm2 : 2 ≤ m := by
    by_contra h
    have : m = 1 := by omega
    subst this
    norm_num at h31
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  obtain ⟨τ, hτ3, hτ1, g, hbg⟩ := exists_conj_dZero (F := F) (by rw [hFc]; exact h31)
    (by rw [hFc]; omega) hb
  set e : projectiveSL 3 F ≃* projectiveSL 3 F := MulAut.conj (proj 3 F g)⁻¹ with he
  have heb : e b = proj 3 F (dZero τ hτ3) := by
    rw [he, hbg, MulAut.conj_apply]
    group
  have hP'C := le_centralizer_map e hPC
  rw [heb] at hP'C
  have hP'el : CFSG.Assembly.IsElemAbelian p (P.map e.toMonoidHom) :=
    isElemAbelian_map e.toMonoidHom hPel
  have hP'c : Nat.card (P.map e.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective e.injective, hPc]
  obtain ⟨X, hXP, hXc, hXlev⟩ := exists_le_leviP hτ3 hτ1 hp hp3 hP'C hP'el hP'c
  have h := parabConcl_of_le_levi hm2 (proj_dZero_mem_leviP τ hτ3) hXP hXc hXlev
  rw [← heb] at h
  exact parabConcl_of_mulEquiv e h

end ProofKS1623Parab

open ProofKS1623Parab
open CFSG.Assembly.RankThreeEven (projSL)

theorem ks1623Parab : KS1623Parab := by
  intro m hm h9 b hb p hp hp3 P hPC hPel hPc
  show ParabConcl b P p m
  set F := GaloisField 2 m with hFdef
  set e := CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 3 F with he
  apply parabConcl_of_mulEquiv e
  have hb' : orderOf (e b) = 3 := by rw [MulEquiv.orderOf_eq, hb]
  have hP'C := le_centralizer_map e hPC
  have hP'el : CFSG.Assembly.IsElemAbelian p (P.map e.toMonoidHom) :=
    isElemAbelian_map e.toMonoidHom hPel
  have hP'c : Nat.card (P.map e.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective e.injective, hPc]
  have hFc : Nat.card F = 2 ^ m := GaloisField.card 2 m (by omega)
  have hmod : 2 ^ m % 3 = 1 ∨ 2 ^ m % 3 = 2 := by
    have h0 : 2 ^ m % 3 ≠ 0 := by
      intro h0
      have h3 : 3 ∣ 2 ^ m := Nat.dvd_of_mod_eq_zero h0
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
      norm_num at this
    omega
  rcases hmod with h31 | h32
  · exact parabConcl_one hm h31 h9 hb' hp hp3 hP'C hP'el hP'c
  · exact (false_of_two (F := F) (by rw [hFc]; exact h32) hb' hp hP'C hP'el hP'c).elim

end CFSG.RankThree.PartTwo.Sec16
