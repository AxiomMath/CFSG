module

public import CFSG.RankThree.PartTwo.KFacts.K71SU3TwoFree
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec8

namespace Hering88D

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank (StatedSU)
open Matrix

theorem eq_one_of_commute_conj_of_order_three {f : ℕ} {K : Type} [Field K]
    (hK : PiField false 2 f K) (hq : ModThree false (2 ^ f)) {v : GL (Fin 3) K}
    (hv : v ∈ StatedSU 3 (2 ^ f) K) (hv3 : v ^ 3 = 1)
    (hvs : ∀ c : K, (v : Matrix (Fin 3) (Fin 3) K) ≠ c • 1) {z : GL (Fin 3) K}
    (hz : z ∈ glPi false 3 (2 ^ f) K) (hz2 : z * z = 1)
    (hc : z * (v * z * v⁻¹) = (v * z * v⁻¹) * z) : z = 1 := by
  have := hK.finite
  have : CharP K 2 := hK.charP
  set h := hK.unitary
  set σ := CFSG.LieType.BorelTits.unitaryInvolution K 2 f
  obtain ⟨g, d, e, hgU, hvg, hde, hd⟩ := exists_unitary_diagonal hK hq hv hv3 hvs
  set D : GL (Fin 3) K := g⁻¹ * v * g with hDdef
  have hDd : (D : Matrix (Fin 3) (Fin 3) K) = diagonal d := by
    rw [hDdef, Units.val_mul, Units.val_mul, Matrix.mul_assoc, hvg, ← Matrix.mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have hDe : ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal e := by
    have hde' : diagonal d * diagonal e = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      exact congrArg diagonal (funext hde)
    calc ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((D : Matrix (Fin 3) (Fin 3) K) *
          diagonal e) := by rw [hDd, hde', Matrix.mul_one]
      _ = diagonal e := by
        rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  set z' : GL (Fin 3) K := g⁻¹ * z * g with hz'def
  have hz'u : z' ∈ glPi false 3 (2 ^ f) K := mul_mem (mul_mem (inv_mem hgU) hz) hgU
  have hz'2 : z' * z' = 1 := by
    calc z' * z' = g⁻¹ * (z * z) * g := by rw [hz'def]; group
      _ = 1 := by rw [hz2]; group
  have hDz : D * z' * D⁻¹ = g⁻¹ * (v * z * v⁻¹) * g := by rw [hDdef, hz'def]; group
  have hmatGL : z' * (D * z' * D⁻¹) = (D * z' * D⁻¹) * z' := by
    rw [hDz, hz'def]
    calc g⁻¹ * z * g * (g⁻¹ * (v * z * v⁻¹) * g) = g⁻¹ * (z * (v * z * v⁻¹)) * g := by group
      _ = g⁻¹ * ((v * z * v⁻¹) * z) * g := by rw [hc]
      _ = g⁻¹ * (v * z * v⁻¹) * g * (g⁻¹ * z * g) := by group
  have hmat : (z' : Matrix (Fin 3) (Fin 3) K) *
      (diagonal d * (z' : Matrix (Fin 3) (Fin 3) K) * diagonal e) =
      (diagonal d * (z' : Matrix (Fin 3) (Fin 3) K) * diagonal e) *
        (z' : Matrix (Fin 3) (Fin 3) K) := by
    have h1 := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hmatGL
    simp only [Units.val_mul, hDd, hDe] at h1
    exact h1
  have hmat2 : (z' : Matrix (Fin 3) (Fin 3) K) * (z' : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have h1 := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hz'2
    simpa using h1
  have hzu : conjTr σ (z' : Matrix (Fin 3) (Fin 3) K) * z' = 1 := by
    have h1 := (mem_glPi_false h).1 hz'u
    rw [← conjTr_unitaryInvolution_eq hK] at h1
    exact h1
  have h1 := eq_one_of_commute_conj_diagonal σ hde hd hzu hmat2 hmat
  have hz'1 : z' = 1 := Units.ext h1
  calc z = g * z' * g⁻¹ := by rw [hz'def]; group
    _ = 1 := by rw [hz'1]; group

theorem pow_three_eq_one_of_mem_unitaryScalars {p f : ℕ} {K : Type} [Field K]
    {hU : UnitaryFieldData p f K} {s : unitarySU p f K 3} (hs : s ∈ unitaryScalars hU 3) :
    s ^ 3 = 1 := by
  obtain ⟨c, -, hc3, hsc⟩ := (mem_unitaryScalars (h := hU)).mp hs
  apply Subtype.ext
  rw [Subgroup.coe_pow, hsc, ← map_pow, hc3, map_one]
  rfl

theorem eq_bot_of_normalizes_psu {f : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData 2 f K)
    (hq : ModThree false (2 ^ f)) {w : unitarySU 2 f K 3} (hw3 : w ^ 3 = 1)
    (hws : ∀ c : K, ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ c • 1)
    {X : Subgroup (unitaryPSU hU 3)} (h2 : IsPGroup 2 X)
    (hXw : ∀ y ∈ X,
      psuConj hU (⟨(w : GL (Fin 3) K), unitarySU_le_unitaryIsom3 w.2⟩ : unitaryIsom3 hU) y ∈ X) :
    X = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hU.finite
  have hK : PiField false 2 f K := ⟨Nat.prime_two, hU.one_le, by
    rw [hU.card]
    show 2 ^ (2 * f) = (2 ^ f) ^ 2
    rw [← pow_mul, mul_comm]⟩
  set Aw : unitaryIsom3 hU := ⟨(w : GL (Fin 3) K), unitarySU_le_unitaryIsom3 w.2⟩ with hAw
  by_contra hne
  have : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).2 hne
  have hZ := h2.center_nontrivial
  have h2Z : IsPGroup 2 (Subgroup.center X) := h2.to_subgroup _
  have hdvd : 2 ∣ Nat.card (Subgroup.center X) := by
    rcases h2Z.card_eq_or_dvd with h1 | h1
    · exact absurd h1 (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne'
    · exact h1
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  set zb : X := (z : X) with hzb
  have hzb2 : zb * zb = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz, sq] at h
    exact congrArg Subtype.val h
  have hzb1 : zb ≠ 1 := by
    intro h1
    have h : z = 1 := Subtype.ext h1
    rw [h, orderOf_one] at hz
    norm_num at hz
  set wb : X := ⟨psuConj hU Aw (zb : unitaryPSU hU 3), hXw _ zb.2⟩ with hwb
  have hzw : zb * wb = wb * zb := (Subgroup.mem_center_iff.1 z.2 wb).symm
  have hzwP : (zb : unitaryPSU hU 3) * psuConj hU Aw (zb : unitaryPSU hU 3) =
      psuConj hU Aw (zb : unitaryPSU hU 3) * (zb : unitaryPSU hU 3) :=
    congrArg Subtype.val hzw
  have hzbP2 : (zb : unitaryPSU hU 3) * (zb : unitaryPSU hU 3) = 1 := congrArg Subtype.val hzb2
  have hzbP1 : (zb : unitaryPSU hU 3) ≠ 1 := fun h1 => hzb1 (Subtype.ext h1)
  obtain ⟨zt, hzt⟩ := unitaryProj_surjective hU 3 (zb : unitaryPSU hU 3)
  obtain ⟨zz, hzzdef⟩ : ∃ zz : unitarySU 2 f K 3, zz = zt ^ 3 := ⟨_, rfl⟩
  have hπzz : unitaryProj hU 3 zz = (zb : unitaryPSU hU 3) := by
    rw [hzzdef, map_pow, hzt]
    calc (zb : unitaryPSU hU 3) ^ 3 = (zb * zb) * zb := by rw [pow_succ, sq]
      _ = zb := by rw [hzbP2, one_mul]
  have hzt2 : zt ^ 2 ∈ unitaryScalars hU 3 := by
    rw [← ker_unitaryProj hU 3, MonoidHom.mem_ker, map_pow, hzt, sq, hzbP2]
  have hzz2 : zz * zz = 1 := by
    have h3 := pow_three_eq_one_of_mem_unitaryScalars hzt2
    calc zz * zz = (zt ^ 2) ^ 3 := by rw [hzzdef]; group
      _ = 1 := h3
  obtain ⟨u, hudef⟩ : ∃ u : unitarySU 2 f K 3, u = w * zz * w⁻¹ := ⟨_, rfl⟩
  have hu2 : u * u = 1 := by
    calc u * u = w * (zz * zz) * w⁻¹ := by rw [hudef]; group
      _ = 1 := by rw [hzz2]; group
  have hπu : unitaryProj hU 3 u = psuConj hU Aw (zb : unitaryPSU hU 3) := by
    rw [← hπzz]
    change ((u : unitarySU 2 f K 3) : unitaryPSU hU 3) =
      psuConj hU Aw ((zz : unitarySU 2 f K 3) : unitaryPSU hU 3)
    rw [psuConj_mk]
    congr 1
  have hcomm : zz * u = u * zz := by
    have hPU : unitaryProj hU 3 (zz * u) = unitaryProj hU 3 (u * zz) := by
      rw [map_mul, map_mul, hπzz, hπu]
      exact hzwP
    obtain ⟨s, hsdef⟩ : ∃ s : unitarySU 2 f K 3, s = (u * zz)⁻¹ * (zz * u) := ⟨_, rfl⟩
    have hs : s ∈ unitaryScalars hU 3 := by
      rw [hsdef, ← ker_unitaryProj hU 3, MonoidHom.mem_ker, map_mul, map_inv, hPU, inv_mul_cancel]
    have hscen : s ∈ Subgroup.center (unitarySU 2 f K 3) := unitaryScalars_le_center hU 3 hs
    have hs3 := pow_three_eq_one_of_mem_unitaryScalars hs
    have hzu : zz * u = u * zz * s := by rw [hsdef]; group
    have hconj : zz * u * zz⁻¹ = u * s := by
      calc zz * u * zz⁻¹ = u * zz * s * zz⁻¹ := by rw [hzu]
        _ = u * (zz * s) * zz⁻¹ := by rw [mul_assoc u zz s]
        _ = u * (s * zz) * zz⁻¹ := by rw [(Subgroup.mem_center_iff.mp hscen zz).symm]
        _ = u * s := by group
    have hs2 : s * s = 1 := by
      have h1 : (zz * u * zz⁻¹) * (zz * u * zz⁻¹) = 1 := by
        calc (zz * u * zz⁻¹) * (zz * u * zz⁻¹) = zz * (u * u) * zz⁻¹ := by group
          _ = 1 := by rw [hu2]; group
      rw [hconj] at h1
      have hus : u * s = s * u := Subgroup.mem_center_iff.mp hscen u
      calc s * s = u * u * (s * s) := by rw [hu2, one_mul]
        _ = u * (u * s) * s := by group
        _ = u * (s * u) * s := by rw [hus]
        _ = (u * s) * (u * s) := by group
        _ = 1 := h1
    have hs1 : s = 1 := by
      calc s = s ^ 3 * (s * s)⁻¹ := by group
        _ = 1 := by rw [hs3, hs2]; group
    rw [hzu, hs1, mul_one]
  have hGL := congrArg (fun x : unitarySU 2 f K 3 => (x : GL (Fin 3) K)) hcomm
  have hzzGL : (zz : GL (Fin 3) K) = 1 := by
    refine eq_one_of_commute_conj_of_order_three hK hq w.2 (by
      rw [← Subgroup.coe_pow, hw3, Subgroup.coe_one]) hws
      (slPi_le_glPi (π := false) (fun _ => hK.unitary) zz.2) (by
        have h1 := congrArg (fun x : unitarySU 2 f K 3 => (x : GL (Fin 3) K)) hzz2
        simpa using h1) ?_
    simpa [hudef] using hGL
  have hzz1 : zz = 1 := Subtype.ext hzzGL
  apply hzbP1
  rw [← hπzz, hzz1, map_one]

end Hering88D

end CFSG.RankThree.PartTwo.Sec8
