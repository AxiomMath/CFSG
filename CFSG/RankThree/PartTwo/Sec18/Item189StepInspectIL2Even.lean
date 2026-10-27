module

public import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIDefs
import CFSG.Quasithin.Background.F6CatDickson
import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms
import CFSG.RankThree.PartTwo.Sec18.Item189StepL16Omega
import CFSG.RankThree.PartTwo.Sec18.Item189StepL16SL2
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.Walter.PSL2Facts.Even
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality

public section

namespace CFSG.RankThree.PartTwo.Sec18

open scoped MatrixGroups

theorem alternating_four_inv189 : ∀ σ ρ : Equiv.Perm (Fin 4), Equiv.Perm.sign σ = 1 →
    Equiv.Perm.sign ρ = 1 → ρ * σ * ρ⁻¹ = σ⁻¹ → σ * σ = 1 := by
  decide +kernel

theorem eq_top_of_psl2_even189 {n : ℕ} (hn : 2 ≤ n)
    (H : Subgroup PSL(2, GaloisField 2 n)) {x w : PSL(2, GaloisField 2 n)} (hx : x ∈ H)
    (hw : w ∈ H) (hx3 : orderOf x = 3) (hwx : w * x * w⁻¹ = x⁻¹) (h2 : 2 ^ n ∣ Nat.card H) :
    H = ⊤ := by
  have hx3' : orderOf (⟨x, hx⟩ : H) = 3 := by rw [Subgroup.orderOf_mk, hx3]
  have h3 : 3 ∣ Nat.card H := hx3' ▸ orderOf_dvd_natCard _
  have h4 : 4 ∣ Nat.card H := by simpa using (pow_dvd_pow 2 hn).trans h2
  have hq2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have hq1 : 0 < 2 ^ n := Nat.two_pow_pos n
  have hg : Nat.gcd 2 (2 ^ n - 1) = 1 := Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega))
  have hG : Nat.card PSL(2, GaloisField 2 n) = 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
    CFSG.Walter.psl2_even_card (by omega)
  have key : ∀ m : ℕ, m ≠ 0 → 2 ^ n ∣ 2 ^ m * ((2 ^ m) ^ 2 - 1) → n ≤ m := by
    intro m hm0 hdvd
    have h2m : 2 ∣ (2 ^ m) ^ 2 := dvd_pow (dvd_pow_self 2 hm0) two_ne_zero
    have h1m : 0 < (2 ^ m) ^ 2 := by positivity
    have hcop : Nat.Coprime (2 ^ n) ((2 ^ m) ^ 2 - 1) :=
      Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega)))
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right hdvd)
  rcases CFSG.Quasithin.F6.dicksonPSL2_holds 2 n (by omega) H with
      ⟨-, m, -, hm⟩ | ⟨-, hc⟩ | ⟨z, hz, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨h16, -⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, P, hPn, hPab, -, hPc, -⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  · exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three (hm ▸ h3)) (by norm_num)
  · rw [hg, Nat.div_one, Nat.div_one] at hc
    rcases hc with hc | hc <;> have := h4.trans hc <;> omega
  · rw [hg, Nat.div_one, Nat.div_one] at hz
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at h4
    rcases hz with hz | hz <;> have := (show 2 ∣ z by omega).trans hz <;> omega
  · have hwx' : (⟨w, hw⟩ : H) * ⟨x, hx⟩ * (⟨w, hw⟩ : H)⁻¹ = (⟨x, hx⟩ : H)⁻¹ := Subtype.ext hwx
    have hrel : e ⟨w, hw⟩ * e ⟨x, hx⟩ * (e ⟨w, hw⟩)⁻¹ = (e ⟨x, hx⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, hwx', map_inv]
    have hσ := alternating_four_inv189 (e ⟨x, hx⟩) (e ⟨w, hw⟩)
      (Equiv.Perm.mem_alternatingGroup.mp (e ⟨x, hx⟩).2)
      (Equiv.Perm.mem_alternatingGroup.mp (e ⟨w, hw⟩).2) (congrArg Subtype.val hrel)
    have hxx : (⟨x, hx⟩ : H) ^ 2 = 1 :=
      e.injective (by rw [map_pow, map_one, pow_two]; exact Subtype.ext hσ)
    have := orderOf_dvd_of_pow_eq_one hxx
    rw [hx3'] at this
    exact absurd this (by norm_num)
  · have : 2 ∣ 2 ^ (2 * n) := dvd_pow_self 2 (by omega)
    have : 0 < 2 ^ (2 * n) := Nat.two_pow_pos _
    omega
  · have hc : Nat.card H = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      simp [Nat.factorial]
    have h60 : 2 ^ n ∣ 60 := hc ▸ h2
    have hn2 : n = 2 := by
      by_contra hne
      have := (pow_dvd_pow 2 (show 3 ≤ n by omega)).trans h60
      norm_num at this
    exact Subgroup.eq_top_of_card_eq H (by rw [hc, hG, hn2] <;> norm_num)
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
  · have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_dvd_iff] at hm
      omega
    have hc : Nat.card H = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, CFSG.Walter.psl2_even_card hm0]
    have hmn : m = n := le_antisymm (Nat.le_of_dvd (by omega) hm) (key m hm0 (hc ▸ h2))
    exact Subgroup.eq_top_of_card_eq H (by rw [hc, hG, hmn])
  · have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero, zero_dvd_iff] at hm
      omega
    have hc : Nat.card H = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.pgl2_card_formula,
        GaloisField.card 2 m hm0]
    have := Nat.le_of_dvd (by omega) hm
    have := key m hm0 (hc ▸ h2)
    omega

theorem inspect189L2Even : Inspect189L2Even := by
  intro Y _ _ X Q x n hd hn ⟨e⟩
  have := hd.normal
  obtain ⟨x, rfl⟩ : ∃ x' : X, (x' : Y) = x := ⟨⟨x, hd.mem⟩, rfl⟩
  let ψ : X ≃* PSL(2, GaloisField 2 n) := e.trans (Sec4.projSLEquivPSL _)
  let φ : X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    ψ.trans (CFSG.RankThree.PartOne.KCRootAxis.slEquivPSL _).symm
  set J := (X ⊓ Subgroup.normalizer (Q : Set Y)) ⊔
    (X ⊓ Subgroup.normalizer (Subgroup.zpowers (x : Y) : Set Y)) with hJ
  show X ≤ J
  have hT : CFSG.ABGLocalTools.IsSylowOf 2 (Q ⊓ X) X :=
    hd.sylow.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top])
  obtain ⟨S, hS⟩ := hT.exists_sylow_eq_subgroupOf
  have hSJ : (S : Subgroup X) ≤ J.subgroupOf X := by
    rw [hS]
    exact fun t ht => Subgroup.mem_sup_left ⟨ht.2, Subgroup.le_normalizer ht.1⟩
  have h2 : 2 ^ n ∣ Nat.card (J.subgroupOf X) := by
    refine (S.pow_dvd_card_of_pow_dvd_card ?_).trans (Subgroup.card_dvd_of_le hSJ)
    rw [Nat.card_congr ψ.toEquiv, CFSG.Walter.psl2_even_card (by omega)]
    exact dvd_mul_right _ _
  have hx3 : orderOf x = 3 := by rw [← Subgroup.orderOf_coe, hd.orderOf_eq]
  have hφ3 : φ x ^ 3 = 1 := by rw [← map_pow, ← hx3, pow_orderOf_eq_one, map_one]
  have hφ1 : φ x ≠ 1 := fun h => by
    have := congrArg orderOf h
    rw [MulEquiv.orderOf_eq, hx3, orderOf_one] at this
    omega
  obtain ⟨w, hww, hwx⟩ : ∃ w : X, w * w = 1 ∧ w * x * w⁻¹ = x⁻¹ := by
    obtain ⟨w, hww, hwx⟩ := exists_involution_inv_sl2_189 hφ3 hφ1
    refine ⟨φ.symm w, φ.injective ?_, φ.injective ?_⟩
    · rw [map_mul, map_one, MulEquiv.apply_symm_apply, hww]
    · rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply, hwx]
  have hxJ : (x : Y) ∈ J :=
    Subgroup.mem_sup_right ⟨x.2, Subgroup.le_normalizer (Subgroup.mem_zpowers _)⟩
  have hwJ : (w : Y) ∈ J := by
    have hinv : (w : Y)⁻¹ = w := congrArg Subtype.val (inv_eq_of_mul_eq_one_right hww)
    have hwx' : w * x * w = x⁻¹ := by rw [← hwx, inv_eq_of_mul_eq_one_right hww]
    have hc : (w : Y) * x * w = (x : Y)⁻¹ := congrArg Subtype.val hwx'
    refine Subgroup.mem_sup_right ⟨w.2, mem_normalizer_zpowers189 ?_ ?_⟩ <;>
      rw [hinv, hc] <;> exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  set H' := (J.subgroupOf X).map ψ.toMonoidHom with hH'
  have hmem : ∀ k : X, (k : Y) ∈ J → ψ k ∈ H' := fun k hk =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hk)
  have htop : H' = ⊤ := by
    refine eq_top_of_psl2_even189 hn H' (hmem x hxJ) (hmem w hwJ) ?_ ?_ ?_
    · rw [MulEquiv.orderOf_eq, hx3]
    · rw [← map_inv, ← map_mul, ← map_mul, hwx, map_inv]
    · rw [hH', Subgroup.card_map_of_injective ψ.injective]
      exact h2
  intro k hk
  have hk' : ψ ⟨k, hk⟩ ∈ H' := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [hH', Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at hk'
  exact hk'

end CFSG.RankThree.PartTwo.Sec18
