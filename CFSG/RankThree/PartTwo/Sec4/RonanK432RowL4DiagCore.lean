module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL4DiagPerm
public import CFSG.RankThree.PartTwo.Sec4.RonanK432DiagThree
public import CFSG.RankThree.PartTwo.Sec4.RonanK432L3HardAbs
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSL4W
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.Open.PGLModelStated
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
public import CFSG.RankThree.PartTwo.Sec11.Item1117ProofSwap
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofTools
public import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
public import CFSG.RankThree.PartTwo.Sec4.Item423ResProof432
public import CFSG.RankThree.PartTwo.Sec4.Item426A6
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Cover
public import Certificates.Certificate8166

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open Matrix CFSG.Open
open CFSG.Assembly.RankThreeEven (projSL)

namespace L4Diag

local notation "pmk" => Matrix.ProjGenLinGroup.mk

variable {K : Type} [Field K]

theorem exists_witness_of_pow_three_det {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : K) ≠ 0)
    {y : GL (Fin 4) K} (hy3 : y ^ 3 = 1) (hdet : GeneralLinearGroup.det y = 1)
    (hy1 : pmk y ≠ 1) :
    ∃ t ∈ StatedSL 4 K,
      (pmk t * pmk y * (pmk t)⁻¹) * pmk y = pmk y * (pmk t * pmk y * (pmk t)⁻¹) ∧
        pmk t * pmk y * (pmk t)⁻¹ ∉ Subgroup.zpowers (pmk y) := by
  have hprim : IsPrimitiveRoot ω 3 := isPrimitiveRoot_three_of_sq_add_add_one hω h3
  have h3y : pmk y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  obtain ⟨g, a, hg⟩ := exists_conj_diagonal_of_pow_three hω h3 hy3
  obtain ⟨E, hEdef⟩ : ∃ E : GL (Fin 4) K, g * y * g⁻¹ = E := ⟨_, rfl⟩
  rw [hEdef] at hg
  have hyE : y = g⁻¹ * E * g := by rw [← hEdef]; group
  have ha : a ≠ 0 := by
    rintro rfl
    apply hy1
    have hE1 : E = 1 := Units.ext (by rw [hg]; simp)
    rw [hyE, hE1]
    simp
  have hsum : ∑ i, a i = 0 := by
    have hdetE' : GeneralLinearGroup.det E = 1 := by
      rw [← hEdef, map_mul, map_mul, map_inv, hdet, mul_one, mul_inv_cancel]
    have hdetE : ((E : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
      rw [← GeneralLinearGroup.val_det_apply, hdetE', Units.val_one]
    rw [hg, det_diagonal, Finset.prod_pow_eq_pow_sum] at hdetE
    have h3dvd : 3 ∣ ∑ i, (a i).val := (hprim.pow_eq_one_iff_dvd _).mp hdetE
    have hz : ((∑ i, (a i).val : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ 3).mpr h3dvd
    push_cast at hz
    simpa only [ZMod.natCast_zmod_val] using hz
  obtain ⟨i, j, hij, hswap⟩ := exists_swap_of_ne_zero a ha hsum
  have hdetP : GeneralLinearGroup.det (signedSwap K i j) = 1 := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, det_signedSwap hij, Units.val_one]
  have ht : g⁻¹ * signedSwap K i j * g ∈ StatedSL 4 K := by
    rw [StatedAPI.statedSL_eq_ker_det, MonoidHom.mem_ker, map_mul, map_mul, map_inv, hdetP,
      mul_one, inv_mul_cancel]
  obtain ⟨F, hFdef⟩ : ∃ F : GL (Fin 4) K, signedSwap K i j * E * (signedSwap K i j)⁻¹ = F :=
    ⟨_, rfl⟩
  have hFm : (F : Matrix (Fin 4) (Fin 4) K) =
      diagonal (fun r => ω ^ (a (Equiv.swap i j r)).val) := by
    rw [← hFdef, Units.val_mul, Units.val_mul, hg, signedSwap_mul_diagonal, mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  have hFE : F * E = E * F := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hFm, hg, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext r
    exact mul_comm _ _
  have hzy : (g⁻¹ * F * g) * y = y * (g⁻¹ * F * g) := by
    calc (g⁻¹ * F * g) * y = g⁻¹ * (F * E) * g := by rw [hyE]; group
      _ = g⁻¹ * (E * F) * g := by rw [hFE]
      _ = y * (g⁻¹ * F * g) := by rw [hyE]; group
  have htyt : (g⁻¹ * signedSwap K i j * g) * y * (g⁻¹ * signedSwap K i j * g)⁻¹ = g⁻¹ * F * g := by
    rw [← hFdef, hyE]
    group
  refine ⟨g⁻¹ * signedSwap K i j * g, ht, ?_⟩
  have hmkt : ∀ w : GL (Fin 4) K,
      pmk (g⁻¹ * signedSwap K i j * g) * pmk w * (pmk (g⁻¹ * signedSwap K i j * g))⁻¹ =
        pmk ((g⁻¹ * signedSwap K i j * g) * w * (g⁻¹ * signedSwap K i j * g)⁻¹) := by
    intro w
    simp only [map_mul, map_inv]
  rw [hmkt y, htyt]
  refine ⟨?_, ?_⟩
  · rw [← map_mul, ← map_mul, hzy]
  · intro hmem
    obtain ⟨m, u, hu⟩ : ∃ (m : ℕ) (u : Kˣ), g⁻¹ * F * g * GeneralLinearGroup.scalar (Fin 4) u = y ^ m := by
      have hinv : y⁻¹ = y ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hy3)
      rcases mem_zpowers_cases_of_pow_three h3y hmem with h | h | h
      · obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp
          (show pmk (g⁻¹ * F * g) = pmk (y ^ 0) by rw [h, pow_zero, map_one])
        exact ⟨0, u, hu⟩
      · obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp
          (show pmk (g⁻¹ * F * g) = pmk (y ^ 1) by rw [h, pow_one])
        exact ⟨1, u, hu⟩
      · obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp
          (show pmk (g⁻¹ * F * g) = pmk (y ^ 2) by rw [h, ← map_inv, hinv])
        exact ⟨2, u, hu⟩
    have hFu : F * GeneralLinearGroup.scalar (Fin 4) u = E ^ m := by
      have hsc : g * GeneralLinearGroup.scalar (Fin 4) u * g⁻¹ =
          GeneralLinearGroup.scalar (Fin 4) u := by
        rw [← GeneralLinearGroup.scalar_commute u g, mul_assoc, mul_inv_cancel, mul_one]
      calc F * GeneralLinearGroup.scalar (Fin 4) u
          = F * (g * GeneralLinearGroup.scalar (Fin 4) u * g⁻¹) := by rw [hsc]
        _ = g * (g⁻¹ * F * g * GeneralLinearGroup.scalar (Fin 4) u) * g⁻¹ := by group
        _ = g * y ^ m * g⁻¹ := by rw [hu]
        _ = E ^ m := by rw [← hEdef, conj_pow]
    have hmat : ((F * GeneralLinearGroup.scalar (Fin 4) u : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = ((E ^ m : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      rw [hFu]
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val, hFm, hg,
      Matrix.scalar_apply, Matrix.diagonal_pow, diagonal_mul_diagonal] at hmat
    have hent : ∀ l, ω ^ (a (Equiv.swap i j l)).val * (u : K) = (ω ^ (a l).val) ^ m := by
      intro l
      exact congrFun (Matrix.diagonal_injective hmat) l
    have hlin : ∀ l, ω ^ (a (Equiv.swap i j l)).val =
        (u : K)⁻¹ * ω ^ ((m : ZMod 3) * a l).val := by
      intro l
      rw [← pow_val_pow hprim (a l) m]
      exact (eq_inv_mul_iff_mul_eq₀ (Units.ne_zero u)).mpr (by rw [mul_comm]; exact hent l)
    obtain ⟨l, l', hne⟩ := hswap (m : ZMod 3)
    exact hne (sub_const_of_pow_eq hprim (b := fun l => a (Equiv.swap i j l))
      (k := (m : ZMod 3)) (c := (u : K)⁻¹) hlin l l')

theorem listRow_projSL_four_of_cube_root {K : Type} [Field K] [Finite K] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : K) ≠ 0) : ListRow (projSL 4 K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (Matrix.ProjGenLinGroup (Fin 4) K) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : Matrix.GeneralLinearGroup (Fin 4) K →* _)
      Matrix.ProjGenLinGroup.mk_surjective
  have hmap : ListRow (CFSG.PGLModel.projImage (StatedSL 4 K)) := by
    refine L3Hard.listRow_map_of_witness Matrix.ProjGenLinGroup.mk (StatedSL 4 K) ?_
    intro x hxL ho
    have hx1 : pmk x ≠ 1 := by
      intro h
      rw [h, orderOf_one] at ho
      omega
    have hx3 : pmk (x ^ 3) = 1 := by
      rw [map_pow]
      have := pow_orderOf_eq_one (pmk x)
      rwa [ho] at this
    have hxdet : GeneralLinearGroup.det x = 1 := by
      have h := hxL
      rw [StatedAPI.statedSL_eq_ker_det, MonoidHom.mem_ker] at h
      exact h
    obtain ⟨c, hc⟩ : ∃ c : Kˣ, GeneralLinearGroup.scalar (Fin 4) c = x ^ 3 := by
      have h := (ProjGenLinGroup.mk_eq_one).mp hx3
      rw [GeneralLinearGroup.center_eq_range_scalar] at h
      exact MonoidHom.mem_range.mp h
    have hc4 : c ^ 4 = 1 := by
      have h := congrArg GeneralLinearGroup.det hc
      rw [GeneralLinearGroup.det_scalar, map_pow, hxdet, one_pow, Fintype.card_fin] at h
      exact h
    have hcomm : Commute (GeneralLinearGroup.scalar (Fin 4) c) x :=
      GeneralLinearGroup.scalar_commute c x
    have hs4 : GeneralLinearGroup.scalar (Fin 4) c ^ 4 = 1 := by
      rw [← map_pow, hc4, map_one]
    have hx'3 : (GeneralLinearGroup.scalar (Fin 4) c * x) ^ 3 = 1 := by
      rw [hcomm.mul_pow, ← hc, ← pow_succ]
      exact hs4
    have hx'det : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 4) c * x) = 1 := by
      rw [map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin, hc4, hxdet, mul_one]
    have hx'mk : pmk (GeneralLinearGroup.scalar (Fin 4) c * x) = pmk x := by
      rw [map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]
    have hx'1 : pmk (GeneralLinearGroup.scalar (Fin 4) c * x) ≠ 1 := by
      rw [hx'mk]
      exact hx1
    obtain ⟨t, ht, hcomm', hnot⟩ :=
      exists_witness_of_pow_three_det hω h3 hx'3 hx'det hx'1
    refine ⟨t, ht, ?_⟩
    rw [hx'mk] at hcomm' hnot
    exact ⟨hcomm', hnot⟩
  exact ListRow.of_mulEquiv (MulEquiv.subgroupCongr (CFSG.PGLModel.projImage_statedSL 4 K)) hmap

theorem exists_cube_root_galoisField {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (hmod : p % 3 = 1) :
    ∃ ω : GaloisField p 1, ω ^ 2 + ω + 1 = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card (GaloisField p 1)ˣ := by
    rw [Nat.card_units, GaloisField.card p 1 (by norm_num), pow_one]
    omega
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := (GaloisField p 1)ˣ) 3 hdvd
  have hu3 : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu
    norm_num at hu
  refine ⟨(u : GaloisField p 1), ?_⟩
  have h3 : (u : GaloisField p 1) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hu3, Units.val_one]
  have hne : (u : GaloisField p 1) ≠ 1 := fun h => hu1 (Units.ext h)
  have hfac : ((u : GaloisField p 1) - 1) *
      ((u : GaloisField p 1) ^ 2 + (u : GaloisField p 1) + 1) = 0 := by
    linear_combination h3
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

theorem listRow_projSL_four_galoisField_of_mod_one {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (hmod : p % 3 = 1) : ListRow (projSL 4 (GaloisField p 1)) := by
  obtain ⟨ω, hω⟩ := exists_cube_root_galoisField hp3 hmod
  exact listRow_projSL_four_of_cube_root hω (three_ne_zero_galoisField_sl4w p hp3)

theorem rowOf_four_SL_of_mod_one : ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 1 →
    RowOf (projSL 4 (GaloisField p 1)) := by
  intro p _ hp hmod S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv e.symm
    ⟨listRow_projSL_four_galoisField_of_mod_one hp hmod, outerRow_projSL_four_sl4w p⟩

end L4Diag

end CFSG.RankThree.PartTwo.Sec4.RonanK432

end
