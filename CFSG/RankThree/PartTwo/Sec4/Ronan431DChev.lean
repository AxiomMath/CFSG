module

public import CFSG.RankThree.PartTwo.Sec4.Ronan431Cfg
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieDefs
import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430ClsRed

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan431D

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Ronan431
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple catalogIs PSimple)
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)
open CFSG.LocalAnalysis.GLTheoremA (KDChevDownQ)
open CFSG.LocalAnalysis.GLTheoremA.H1431c (CompOfType)
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem not_isChevSimple_of_card_eq_360 (hb : LieOrderBridge) {q : ℕ} (hq : q.Prime)
    (hq3 : 3 < q) {T : Type} [Group T] (hT : Nat.card T = 360) : ¬ IsChevSimple q T := by
  haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; norm_num)
  by_cases h5 : q = 5
  · subst h5
    exact CFSG.LocalAnalysis.GLTheoremA.I1416QRows.not_isChevSimple_of_card hb hq (by norm_num)
      (a := 1) (m := 72) (by rw [hT]; norm_num) (by norm_num) (by norm_num)
      (fun h => by norm_num at h) (fun _ => by norm_num)
  · have hndvd : ¬ q ∣ 360 := by
      intro h
      have h' : q ∣ 2 ^ 3 * (3 ^ 2 * 5) := by norm_num; exact h
      rcases hq.dvd_mul.mp h' with h2 | h35
      · have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2)
        omega
      · rcases hq.dvd_mul.mp h35 with h3 | h5'
        · have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow h3)
          omega
        · exact h5 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp h5')
    exact CFSG.LocalAnalysis.GLTheoremA.I1416QRows.not_isChevSimple_of_card hb hq (by omega)
      (a := 0) (m := 360) (by rw [hT]; norm_num) hndvd (by norm_num) (fun h => by omega)
      (fun h => absurd h h5)

theorem card_eq_360_of_catalogIs_isA6 (hb : LieOrderBridge) (X : Type) [Group X] [Finite X]
    (h : catalogIs X CFSG.LocalAnalysis.GLTheoremA.S8.isA6) : Nat.card X = 360 :=
  CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed.card_a6 hb h

theorem isChevSimple_projSL_four (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    IsChevSimple p (projSL 4 (GaloisField p 1)) :=
  CFSG.LocalAnalysis.GLTheoremA.chev_isChevSimple_of_mulEquiv
    (CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 4 (GaloisField p 1))
    (CFSG.HardMathSupport.Dickson.DefCharOuter.Export.isChevSimple_projectiveSL (r := 3) (f := 1)
      Fact.out hp2 le_rfl (by norm_num) (by rw [GaloisField.card p 1 one_ne_zero]))

theorem isChevSimple_projSU_four (p : ℕ) [Fact p.Prime] : IsChevSimple p (projSU 4 p 1) :=
  CFSG.HardMathSupport.Dickson.I271.isChevSimple_of_statedPSU
    (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU
      ⟨Fact.out, le_rfl, by norm_num, by simp⟩ (MulEquiv.refl _))

variable {S : Type} [Group S] [Finite S]

theorem pow_three_eq_one_of_cfgS431 {A : Subgroup (MulAut S)} {σ : MulAut S} {K : Subgroup S}
    (hc : CfgS431 S A σ K) : σ ^ 3 = 1 :=
  hc.isE27.1.2 σ hc.mem

theorem noCfgS431_of_isChevSimple (hb : LieOrderBridge) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hD : KDChevDownQ 3 p) {T : TauCeti.CFSGIndex → Prop}
    (hT : ∀ (X : Type) [Group X] [Finite X], catalogIs X T → Nat.card X = 360)
    (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) (hchev : IsChevSimple p S)
    (hB : ∀ (A : Subgroup (MulAut S)) (σ : MulAut S) (K : Subgroup S), CfgS431 S A σ K →
      CompOfType S σ T) :
    NoCfgS431 S := by
  intro A σ K hc
  obtain ⟨J, hJ, hcat⟩ := hB A σ K hc
  exact not_isChevSimple_of_card_eq_360 hb hp hp3 (hT _ hcat)
    (hD S hs hna hchev σ (pow_three_eq_one_of_cfgS431 hc) J hJ)

theorem eq_six_of_factorial_div_two_eq {m : ℕ} (hm : 5 ≤ m) (h : m.factorial / 2 = 360) :
    m = 6 := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have h5 : m = 5 := by omega
    subst h5
    norm_num [Nat.factorial] at h
  · have h7 : Nat.factorial 7 ≤ m.factorial := Nat.factorial_le hgt
    have h7' : (5040 : ℕ) ≤ m.factorial := by simpa [Nat.factorial] using h7
    omega

theorem noCfgS431_alt_of_not_dvd {T : TauCeti.CFSGIndex → Prop}
    (hT : ∀ (X : Type) [Group X] [Finite X], catalogIs X T → Nat.card X = 360) {n : ℕ}
    (hn : 5 ≤ n) (h6 : ¬ 3 ∣ n - 6)
    (hB : ∀ (A : Subgroup (MulAut (alternatingGroup (Fin n))))
      (σ : MulAut (alternatingGroup (Fin n))) (K : Subgroup (alternatingGroup (Fin n))),
      CfgS431 (alternatingGroup (Fin n)) A σ K → CompOfType (alternatingGroup (Fin n)) σ T) :
    NoCfgS431 (alternatingGroup (Fin n)) := by
  intro A σ K hc
  obtain ⟨J, hJ, hcat⟩ := hB A σ K hc
  obtain ⟨m, hm5, -, hdvd, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed.kdAltDown_mod n 3
    hn Nat.prime_three (by norm_num) σ (pow_three_eq_one_of_cfgS431 hc) hc.ne_one J hJ
  have hm5' : 5 ≤ m := le_of_max_le_left hm5
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h360 := hT _ hcat
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at h360
  have hm6 := eq_six_of_factorial_div_two_eq hm5' h360
  subst hm6
  exact h6 hdvd

end CFSG.RankThree.PartTwo.Sec4.Ronan431D
