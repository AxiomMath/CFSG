module

public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofCentAut
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofFieldTools
import CFSG.LieType.SteinbergBRMulEquivCores

public section

namespace CFSG.RankThree.PartTwo.Sec15

namespace Proof15Res5

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

variable {K : Type} [Field K] {m : ℕ} {π : Bool}

theorem not_two_dvd_card_units (hK : PiField π 2 m K) : ¬ 2 ∣ Nat.card Kˣ := by
  have := hK.finite
  rw [Nat.card_units, hK.card]
  have hm := hK.one_le
  have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  cases π
  · change ¬ 2 ∣ (2 ^ m) ^ 2 - 1
    have h4 : 2 ∣ (2 ^ m) ^ 2 := dvd_pow h2 (by norm_num)
    have h5 : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  · change ¬ 2 ∣ 2 ^ m - 1
    omega

theorem not_two_dvd_qSubPi (hm : 1 ≤ m) : ¬ 2 ∣ qSubPi π (2 ^ m) := by
  have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  cases π
  · change ¬ 2 ∣ 2 ^ m + 1
    omega
  · change ¬ 2 ∣ 2 ^ m - 1
    omega

theorem not_two_dvd_qSubPi_div (hm : 1 ≤ m) :
    ¬ 2 ∣ qSubPi π ((2 ^ m) ^ 3) / qSubPi π (2 ^ m) := by
  have hdvd : qSubPi π (2 ^ m) ∣ qSubPi π ((2 ^ m) ^ 3) := by
    cases π
    · change 2 ^ m + 1 ∣ (2 ^ m) ^ 3 + 1
      have := Odd.nat_add_dvd_pow_add_pow (2 ^ m) 1 (n := 3) ⟨1, rfl⟩
      simpa using this
    · change 2 ^ m - 1 ∣ (2 ^ m) ^ 3 - 1
      have := Nat.sub_dvd_pow_sub_pow (2 ^ m) 1 3
      simpa using this
  obtain ⟨c, hc⟩ := hdvd
  have hpos : 0 < qSubPi π (2 ^ m) := by
    have h1 : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    cases π
    · change 0 < 2 ^ m + 1
      omega
    · change 0 < 2 ^ m - 1
      omega
  rw [hc, Nat.mul_div_cancel_left _ hpos]
  intro h2
  have hodd := not_two_dvd_qSubPi (π := π) (m := 3 * m) (by omega)
  rw [pow_mul, ← pow_mul, mul_comm, pow_mul] at hodd
  apply hodd
  rw [hc]
  exact Dvd.dvd.mul_left h2 _

theorem piCard_mod_three {f₀ : ℕ} (hq : ModThree π (2 ^ (3 * f₀))) :
    piCard π (2 ^ f₀) % 3 = 1 := by
  have hcube : 2 ^ (3 * f₀) = (2 ^ f₀) ^ 3 := by rw [← pow_mul, mul_comm]
  have hmod : 2 ^ (3 * f₀) % 3 = 2 ^ f₀ % 3 := by
    rw [hcube]
    exact Sec14.Item148Rank.pow_three_mod_three148 _
  have hne : 2 ^ f₀ % 3 ≠ 0 := by
    intro h0
    have h3 : 3 ∣ 2 ^ f₀ := Nat.dvd_of_mod_eq_zero h0
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  cases π
  · change (2 ^ f₀) ^ 2 % 3 = 1
    rw [Nat.pow_mod]
    have : 2 ^ f₀ % 3 = 1 ∨ 2 ^ f₀ % 3 = 2 := by omega
    rcases this with h | h <;> rw [h]
  · change 2 ^ f₀ % 3 = 1
    change 2 ^ (3 * f₀) % 3 = 1 at hq
    omega

theorem card_centMod_eq (L : Subgroup (GL (Fin 3) K)) (y : GL (Fin 3) K) :
    Nat.card (centMod L y) =
      Nat.card (L ⊓ Subgroup.centralizer {y} : Subgroup (GL (Fin 3) K)) *
        Nat.card (commHom L y).range := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (commHom L y).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (commHom L y)).toEquiv,
    ker_commHom] at h1
  rw [h1, mul_comm]
  congr 1
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (centralizer_le_centMod L y)).toEquiv

theorem not_two_dvd_card_centMod (hK : PiField π 2 m K) {L : Subgroup (GL (Fin 3) K)}
    {y : GL (Fin 3) K}
    (h : ¬ 2 ∣ Nat.card (L ⊓ Subgroup.centralizer {y} : Subgroup (GL (Fin 3) K))) :
    ¬ 2 ∣ Nat.card (centMod L y) := by
  have := hK.finite
  rw [card_centMod_eq]
  intro h2
  have hr : ¬ 2 ∣ Nat.card (commHom L y).range := by
    intro h3
    apply not_two_dvd_card_units hK
    exact h3.trans ((Subgroup.card_subgroup_dvd_card _).trans
      (Subgroup.card_range_dvd (GeneralLinearGroup.scalar (Fin 3) (R := K))))
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h' | h'
  · exact h h'
  · exact hr h'

theorem diagE_mul (c d : Kˣ) : diagE (c * d) = diagE c * diagE d := by
  apply Units.ext
  rw [Units.val_mul, coe_diagE, coe_diagE, coe_diagE, diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

open Sec11.KS11LieProof in
theorem not_two_dvd_card_of_block (hK : PiField π 2 m K) (hq : ModThree π (2 ^ m))
    (hq2 : 2 < 2 ^ m) {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (2 ^ m) K)
    (R : Subgroup (projImage (slPi π 3 (2 ^ m) K)))
    (hRsub : ∀ r ∈ R, ∃ B ∈ glPi π 2 (2 ^ m) K,
      (r : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (g * blockHom B * g⁻¹))
    (hRnorm : ∀ B : slPi π 2 (2 ^ m) K, ∀ r ∈ R,
      blockProj hK hg B * r * (blockProj hK hg B)⁻¹ ∈ R)
    (hRsolv : Group.IsSolvable R) : ¬ 2 ∣ Nat.card R := by
  have := hK.finite
  have hπ : π = false → UnitaryFieldData 2 m K := fun h => by subst h; exact hK.unitary
  set Q := slPi π 2 (2 ^ m) K with hQdef
  set β := blockProj hK hg with hβ
  have hQ := isQuasisimple_slPi_two hK hq hq2
  have hQperf : Group.IsPerfect Q := hQ.1
  set RQ := R.comap β with hRQ
  have hRQn : RQ.Normal := ⟨fun n hn x => by
    change β (x * n * x⁻¹) ∈ R
    rw [map_mul, map_mul, map_inv]
    exact hRnorm x (β n) hn⟩
  have hRQtop : RQ ≠ ⊤ := by
    intro htop
    have hmem : ∀ x : Q, β x ∈ R := fun x => by
      have : x ∈ RQ := htop ▸ Subgroup.mem_top x
      exact this
    set ι : Q →* R := β.codRestrict R hmem with hι
    have hιi : Function.Injective ι := fun x y hxy =>
      blockProj_injective hK hg (congrArg Subtype.val hxy)
    have : Group.IsSolvable R := hRsolv
    have hQs : Group.IsSolvable Q := Group.isSolvable_of_isSolvable_injective hιi
    have : Nontrivial Q := by
      by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      have : Subsingleton (Q ⧸ Subgroup.center Q) := QuotientGroup.mk_surjective.subsingleton
      exact not_nontrivial_iff_subsingleton.mpr this hQ.2.1.toNontrivial
    exact CFSG.LieType.SteinbergBR.not_isSolvable_of_isPerfect hQs
  have hRQc : RQ ≤ Subgroup.center Q :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top
      ⟨hQ.1.commutator_eq_top, hQ.2.1⟩ RQ hRQtop
  have hmkc : ∀ u v : GL (Fin 3) K, ProjGenLinGroup.mk (u * v * u⁻¹) =
      ProjGenLinGroup.mk u * ProjGenLinGroup.mk v * (ProjGenLinGroup.mk u)⁻¹ := fun u v => by
    rw [map_mul, map_mul, map_inv]
  have hcomm : ∀ r ∈ R, ∀ x : Q, r * β x * r⁻¹ = β x := by
    intro r hr
    obtain ⟨Br, hBr, hrv⟩ := hRsub r hr
    have hconjQ : ∀ x : Q, Br * (x : GL (Fin 2) K) * Br⁻¹ ∈ Q := fun x => by
      have hx := (mem_slPi_iff hπ).mp x.2
      refine (mem_slPi_iff hπ).mpr ⟨mul_mem (mul_mem hBr hx.1) (inv_mem hBr), ?_⟩
      rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hx.2, mul_one, ← det_mul,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
    set x' : Q → Q := fun x => ⟨Br * (x : GL (Fin 2) K) * Br⁻¹, hconjQ x⟩ with hx'
    have hfx : ∀ x : Q, r * β x * r⁻¹ = β (x' x) := fun x => by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hrv, hβ, coe_blockProj,
        coe_blockProj, ← hmkc]
      congr 1
      simp only [hx', map_mul, map_inv]
      group
    have hwR : ∀ x : Q, x⁻¹ * x' x ∈ RQ := fun x => by
      change β (x⁻¹ * x' x) ∈ R
      rw [map_mul, ← hfx, map_inv]
      have h1 := hRnorm x⁻¹ r hr
      rw [map_inv, inv_inv] at h1
      have e : (β x)⁻¹ * (r * β x * r⁻¹) = ((β x)⁻¹ * r * β x) * r⁻¹ := by group
      rw [e]
      exact mul_mem h1 (inv_mem hr)
    have hcen : ∀ x : Q, ∀ y : Q, (x⁻¹ * x' x) * y = y * (x⁻¹ * x' x) := fun x y =>
      (Subgroup.mem_center_iff.mp (hRQc (hwR x)) y).symm
    set f : Q →* projImage (slPi π 3 (2 ^ m) K) := (MulAut.conj r).toMonoidHom.comp β with hf
    have hfv : ∀ x : Q, f x = r * β x * r⁻¹ := fun x => rfl
    have hwv : ∀ x : Q, (β x)⁻¹ * f x = β (x⁻¹ * x' x) := fun x => by
      rw [hfv, hfx, map_mul, map_inv]
    intro x
    have key := eq_of_eq_mul_commute hQperf f β (fun x => (β x)⁻¹ * f x)
      (fun x => by rw [mul_inv_cancel_left]) (fun x y => by
        rw [hwv, ← map_mul, ← map_mul, hcen]) (fun x y => by
        rw [hwv, hwv, ← map_mul, ← map_mul, hcen]) x
    rw [← hfv]
    exact key
  have hdiag : ∀ r ∈ R, ∃ c : Kˣ, (r : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (g * diagE c * g⁻¹) := by
    intro r hr
    obtain ⟨Br, hBr, hrv⟩ := hRsub r hr
    set s := g * blockHom Br * g⁻¹ with hs
    have hΦ := eq_of_mk_eq_block hK hq hq2 hg (MulAut.conj s).toMonoidHom (fun B => by
      have h1 := congrArg Subtype.val (hcomm r hr B)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hrv, hβ, coe_blockProj,
        ← hmkc] at h1
      rw [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, coe_blockConj]
      exact h1)
    have hM : ∀ B : Q, blockHom Br * blockHom (B : GL (Fin 2) K) =
        blockHom (B : GL (Fin 2) K) * blockHom Br := fun B => by
      have h2 := hΦ B
      rw [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, coe_blockConj,
        hs] at h2
      have h3 : g * (blockHom Br * blockHom (B : GL (Fin 2) K)) * g⁻¹ =
          g * (blockHom (B : GL (Fin 2) K) * blockHom Br) * g⁻¹ := by
        calc g * (blockHom Br * blockHom (B : GL (Fin 2) K)) * g⁻¹ =
            g * blockHom Br * g⁻¹ * (g * blockHom (B : GL (Fin 2) K) * g⁻¹) *
              (g * blockHom Br * g⁻¹)⁻¹ * (g * blockHom Br * g⁻¹) := by group
          _ = g * blockHom (B : GL (Fin 2) K) * g⁻¹ * (g * blockHom Br * g⁻¹) := by rw [h2]
          _ = g * (blockHom (B : GL (Fin 2) K) * blockHom Br) * g⁻¹ := by group
      have h4 := congrArg (fun u => g⁻¹ * u * g) h3
      simpa only [inv_mul_cancel_left, mul_inv_cancel_right, mul_assoc, inv_mul_cancel, mul_one]
        using h4
    obtain ⟨a, b, hab⟩ := exists_diag_of_commute_block hK hq hq2 hM
    refine ⟨a * b⁻¹, ?_⟩
    rw [hrv, hs, hab, diagUnits_eq_scalar_mul, mul_assoc g, map_mul, map_mul, map_mul,
      mk_eq_one_iff_mem_statedScalars.mpr ⟨b, rfl⟩, one_mul, map_mul, map_mul, mul_assoc]
  have hd1 : diagE (1 : Kˣ) = 1 := by
    have h := diagE_mul (1 : Kˣ) 1
    rw [mul_one] at h
    exact left_eq_mul.mp h
  set ε : Kˣ →* ProjGenLinGroup (Fin 3) K :=
    { toFun := fun c => ProjGenLinGroup.mk (g * diagE c * g⁻¹)
      map_one' := by rw [hd1, mul_one, mul_inv_cancel, map_one]
      map_mul' := fun c d => by
        rw [diagE_mul, ← map_mul]
        congr 1
        group } with hε
  have hle : R.map (projImage (slPi π 3 (2 ^ m) K)).subtype ≤ ε.range := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨c, hc⟩ := hdiag r hr
    exact ⟨c, hc.symm⟩
  have hcard : Nat.card (R.map (projImage (slPi π 3 (2 ^ m) K)).subtype) = Nat.card R :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  intro h2
  apply not_two_dvd_card_units hK
  rw [← hcard] at h2
  exact h2.trans ((Subgroup.card_dvd_of_le hle).trans (Subgroup.card_range_dvd ε))

end Proof15Res5

end CFSG.RankThree.PartTwo.Sec15
