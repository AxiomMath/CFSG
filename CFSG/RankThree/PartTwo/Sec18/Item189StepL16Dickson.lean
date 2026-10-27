module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import CFSG.Quasithin.Background.F6CatDickson
import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.RankThree.PartTwo.Sec18

open scoped MatrixGroups

theorem false_of_isSimpleGroup_orderOf_fifteen189 {J : Type*} [Group J] [IsSimpleGroup J]
    (hJ : Nat.card J = 60) {g : J} (hg : orderOf g = 15) : False := by
  have : Finite J := Nat.finite_of_card_ne_zero (by omega)
  have hK : Nat.card (Subgroup.zpowers g) = 15 := by rw [Nat.card_zpowers, hg]
  have hidx : (Subgroup.zpowers g).index = 4 := by
    have h := (Subgroup.zpowers g).card_mul_index
    rw [hK, hJ] at h
    omega
  have hdvd := (Subgroup.zpowers g).index_normalCore_dvd_factorial_index
  rw [hidx] at hdvd
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers g).normalCore with h | h
  · rw [h, Subgroup.index_bot, hJ] at hdvd
    exact absurd hdvd (by decide)
  · have htop : Subgroup.zpowers g = ⊤ :=
      top_le_iff.mp (h ▸ (Subgroup.zpowers g).normalCore_le)
    rw [htop, Subgroup.card_top, hJ] at hK
    omega

theorem card_psl2_four189 : Nat.card PSL(2, GaloisField 2 2) = 60 := by
  rw [CFSG.Walter.psl2_even_card (by norm_num)]
  norm_num

theorem card_pgl2_four189 : Nat.card PGL(2, GaloisField 2 2) = 60 := by
  rw [CFSG.GorensteinWalter.pgl2_card_formula, GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem isSimpleGroup_psl2_four189 : IsSimpleGroup PSL(2, GaloisField 2 2) :=
  Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
    (by rw [GaloisField.card 2 2 (by norm_num)]; norm_num)

theorem isSimpleGroup_pgl2_four189 : IsSimpleGroup PGL(2, GaloisField 2 2) := by
  have : Finite PGL(2, GaloisField 2 2) :=
    Nat.finite_of_card_ne_zero (by rw [card_pgl2_four189]; norm_num)
  have := isSimpleGroup_psl2_four189
  exact (MulEquiv.ofBijective _
    (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.bijective_of_nat_card_le
      (card_pgl2_four189.trans card_psl2_four189.symm).le)).symm.isSimpleGroup

theorem eq_top_of_psl2_sixteen189
    (H : Subgroup PSL(2, GaloisField 2 4)) {x y w : PSL(2, GaloisField 2 4)}
    (hx : x ∈ H) (hy : y ∈ H) (hw : w ∈ H) (hx3 : orderOf x = 3) (hy5 : orderOf y = 5)
    (hxy : y * x = x * y) (hw2 : w * w = 1) (hwx : w * x * w⁻¹ = x⁻¹)
    {E : Subgroup PSL(2, GaloisField 2 4)} (hEH : E ≤ H) (hE2 : ∀ e ∈ E, e * e = 1)
    (hE4 : 4 ≤ Nat.card E) : H = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx3' : orderOf (⟨x, hx⟩ : H) = 3 := by rw [Subgroup.orderOf_mk, hx3]
  have hy5' : orderOf (⟨y, hy⟩ : H) = 5 := by rw [Subgroup.orderOf_mk, hy5]
  have h15 : orderOf ((⟨x, hx⟩ : H) * ⟨y, hy⟩) = 15 := by
    rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime (Subtype.ext hxy.symm)
      (by rw [hx3', hy5']; norm_num), hx3', hy5']
  have h3 : 3 ∣ Nat.card H := hx3' ▸ orderOf_dvd_natCard _
  have h5 : 5 ∣ Nat.card H := hy5' ▸ orderOf_dvd_natCard _
  have hEsq : ∀ e : E, e ^ 2 = 1 := fun e => Subtype.ext (by simpa [pow_two] using hE2 e e.2)
  have h4 : 4 ∣ Nat.card H := by
    have : Finite E := Nat.finite_of_card_ne_zero (by omega)
    obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq (p := 2) (G := E) fun e => ⟨1, hEsq e⟩
    have hn2 : 2 ≤ n := by
      by_contra! hlt
      interval_cases n <;> omega
    exact ((pow_dvd_pow 2 hn2).trans (hn ▸ dvd_rfl)).trans (Subgroup.card_dvd_of_le hEH)
  have hq : (2 ^ 4 + 1) / Nat.gcd 2 (2 ^ 4 - 1) = 17 ∧
      (2 ^ 4 - 1) / Nat.gcd 2 (2 ^ 4 - 1) = 15 := by decide
  have h60 : ∀ {T : Type} [Group T] [IsSimpleGroup T], Nonempty (H ≃* T) →
      Nat.card T = 60 → False := by
    rintro T _ _ ⟨e⟩ hT
    have := e.isSimpleGroup
    exact false_of_isSimpleGroup_orderOf_fifteen189 (by rw [Nat.card_congr e.toEquiv, hT]) h15
  rcases CFSG.Quasithin.F6.dicksonPSL2_holds 2 4 (by norm_num) H with
      ⟨-, m, -, hm⟩ | ⟨hc, -⟩ | ⟨z, hz, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨h16, -⟩ | ⟨-, he⟩ |
      ⟨m, t, P, hPn, hPab, -, hPc, -⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  · exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three (hm ▸ h3)) (by norm_num)
  · have := Subgroup.isCyclic_of_le hEH
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
    have := Nat.le_of_dvd (by norm_num) (hg ▸ orderOf_dvd_of_pow_eq_one (hEsq g))
    omega
  · rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at h4
    rw [hq.1, hq.2] at hz
    have h2z : 2 ∣ z := by omega
    rcases hz with hz | hz <;> exact absurd (h2z.trans hz) (by norm_num)
  · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at h5
    exact absurd h5 (by simp [Nat.factorial])
  · exact absurd h16 (by norm_num)
  · exact (h60 he (by rw [nat_card_alternatingGroup]; simp [Nat.factorial])).elim
  · have hab : ∀ a b : H ⧸ P, a * b = b * a := fun a b =>
      (IsCyclic.isMulCommutative (α := H ⧸ P)).is_comm.comm a b
    have key : ∀ u : H ⧸ P, u ^ 3 = 1 → u⁻¹ = u → u = 1 := fun u h3 h1 => by
      calc u = u ^ 3 * (u * u)⁻¹ := by group
        _ = 1 := by rw [h3, mul_eq_one_iff_eq_inv.mpr h1.symm, inv_one, one_mul]
    have hinv : ((⟨x, hx⟩ : H) : H ⧸ P)⁻¹ = ((⟨x, hx⟩ : H) : H ⧸ P) := by
      have h1 : ((⟨w, hw⟩ * ⟨x, hx⟩ * (⟨w, hw⟩ : H)⁻¹ : H) : H ⧸ P) =
          ((⟨x, hx⟩ : H) : H ⧸ P)⁻¹ := by
        rw [show (⟨w, hw⟩ * ⟨x, hx⟩ * (⟨w, hw⟩ : H)⁻¹ : H) = (⟨x, hx⟩ : H)⁻¹ from
          Subtype.ext hwx, QuotientGroup.mk_inv]
      rw [← h1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        hab ((⟨w, hw⟩ : H) : H ⧸ P), mul_inv_cancel_right]
    have hu3 : ((⟨x, hx⟩ : H) : H ⧸ P) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow, ← hx3', pow_orderOf_eq_one, QuotientGroup.mk_one]
    have hxP : (⟨x, hx⟩ : H) ∈ P := (QuotientGroup.eq_one_iff _).mp (key _ hu3 hinv)
    have := orderOf_dvd_of_pow_eq_one (hPab.2 _ hxP)
    rw [hx3'] at this
    exact absurd this (by norm_num)
  · have hc := Nat.card_congr e.toEquiv
    have hm4 : m ≤ 4 := Nat.le_of_dvd (by norm_num) hm
    interval_cases m
    · norm_num at hm
    · rw [hc, CFSG.Walter.psl2_even_card (by norm_num)] at h5
      norm_num at h5
    · have := isSimpleGroup_psl2_four189
      exact (h60 ⟨e⟩ card_psl2_four189).elim
    · norm_num at hm
    · exact Subgroup.eq_top_of_card_eq H hc
  · have hc := Nat.card_congr e.toEquiv
    have hm2 : m ≤ 2 := by
      have := Nat.le_of_dvd (by norm_num) hm
      omega
    interval_cases m
    · norm_num at hm
    · rw [hc, CFSG.GorensteinWalter.pgl2_card_formula, GaloisField.card 2 1 (by norm_num)] at h5
      norm_num at h5
    · have := isSimpleGroup_pgl2_four189
      exact (h60 ⟨e⟩ card_pgl2_four189).elim

end CFSG.RankThree.PartTwo.Sec18
