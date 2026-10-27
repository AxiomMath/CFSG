module

import CFSG.RankThree.PartTwo.Sec4.LThreePiRank
public import CFSG.RankThree.PartTwo.Sec13.Steps
public import CFSG.RankThree.PartTwo.Sec14.Std

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open Matrix (ProjGenLinGroup GeneralLinearGroup)

@[expose] noncomputable def inndiagPi (π : Bool) (q : ℕ) (K : Type) [Field K] :
    Subgroup (MulAut (projImage (slPi π 3 q K))) where
  carrier := {β | ∃ g ∈ glPi π 3 q K, ∀ s : projImage (slPi π 3 q K),
    ((β s : projImage (slPi π 3 q K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk g * s * (ProjGenLinGroup.mk g)⁻¹}
  mul_mem' := by
    rintro β β' ⟨g, hg, hβ⟩ ⟨g', hg', hβ'⟩
    refine ⟨g * g', mul_mem hg hg', fun s => ?_⟩
    rw [MulAut.mul_apply, hβ, hβ', map_mul]
    group
  one_mem' := ⟨1, one_mem _, fun s => by simp⟩
  inv_mem' := by
    rintro β ⟨g, hg, hβ⟩
    refine ⟨g⁻¹, inv_mem hg, fun s => ?_⟩
    have h1 := hβ (β⁻¹ s)
    rw [MulAut.apply_inv_self] at h1
    rw [map_inv, inv_inv]
    calc ((β⁻¹ s : projImage (slPi π 3 q K)) : ProjGenLinGroup (Fin 3) K) =
        (ProjGenLinGroup.mk g)⁻¹ * (ProjGenLinGroup.mk g * ((β⁻¹ s : projImage (slPi π 3 q K)) :
          ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk g)⁻¹) * ProjGenLinGroup.mk g := by
          group
      _ = (ProjGenLinGroup.mk g)⁻¹ * s * ProjGenLinGroup.mk g := by rw [← h1]

@[expose] def KS142InndiagNormal : Prop :=
  ∀ (π : Bool) (p f : ℕ) (K : Type) [Field K], PiField π p f K → ModThree π (p ^ f) →
    2 < p ^ f → (inndiagPi π (p ^ f) K).Normal

@[expose] def Step142PGLKer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → Sec8.IsZ3PGLThreePi (Sec13.lBarA c L A) →
      ∀ V : Subgroup G,
        V ≤ (Subgroup.centralizer ({c} : Set G) ⊓ thetaQuotCentralizer L) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer ({c} : Set G)) →
        ¬ 3 ∣ Nat.card V → A ≤ Subgroup.normalizer (V : Set G) →
          V ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({c} : Set G))

namespace Proof142Res

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_eq_conj_of_mem_inndiagPi (hK : PiField π p f K)
    {β : MulAut (projImage (slPi π 3 (p ^ f) K))} (hβ : β ∈ inndiagPi π (p ^ f) K)
    (hβ3 : Nat.Coprime 3 (orderOf β)) :
    ∃ u : projImage (slPi π 3 (p ^ f) K), β = MulAut.conj u := by
  obtain ⟨g, hg, hβg⟩ := hβ
  have hdet := det_mem_rootsOfUnity hK hg
  have hμ : GeneralLinearGroup.scalar (Fin 3) (GeneralLinearGroup.det g) ∈ glPi π 3 (p ^ f) K :=
    (scalar_mem_glPi_iff hK _).mpr hdet
  have hdet3 : ((g ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      ((GeneralLinearGroup.det g : Kˣ) : K) ^ 3 := by
    rw [Units.val_pow_eq_pow_val, Matrix.det_pow, GeneralLinearGroup.val_det_apply]
  obtain ⟨l, hl, -, hlm⟩ := exists_inner_of_det_eq_cube hK (pow_mem hg 3) hμ hdet3
  set u₀ : projImage (slPi π 3 (p ^ f) K) := ⟨ProjGenLinGroup.mk l, ⟨l, hl, rfl⟩⟩ with hu₀
  have hβ3eq : β ^ 3 = MulAut.conj u₀ := by
    ext s
    have h1 : ∀ n : ℕ, (((β ^ n) s : projImage (slPi π 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (g ^ n) * s * (ProjGenLinGroup.mk (g ^ n))⁻¹ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', MulAut.mul_apply, hβg, ih, pow_succ', map_mul]
        group
    rw [h1 3, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hu₀]
    obtain ⟨m, -, hm⟩ := Subgroup.mem_map.mp s.2
    rw [← hm, ← map_mul, ← map_inv, ← map_mul, hlm m, map_mul, map_mul, map_inv]
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * 3 + b * (orderOf β : ℤ) = 1 := by
    obtain ⟨a, b, h⟩ := Nat.isCoprime_iff_coprime.mpr hβ3
    exact ⟨a, b, by exact_mod_cast h⟩
  have e : β = (β ^ 3) ^ a * (β ^ orderOf β) ^ b := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add,
      show ((3 : ℕ) : ℤ) * a + (orderOf β : ℤ) * b = 1 by push_cast; linarith, zpow_one]
  refine ⟨u₀ ^ a, ?_⟩
  rw [e, pow_orderOf_eq_one, one_zpow, mul_one, hβ3eq, map_zpow]

end Proof142Res

end CFSG.RankThree.PartTwo.Sec14
