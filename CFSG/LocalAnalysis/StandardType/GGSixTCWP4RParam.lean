module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UG3
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Orbit
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6TwoLang
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Upper
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NLift
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UFrameD
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big.Plane

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section Param

variable {L : Type} [Field L]

variable {p : ℕ} {ζ : Lˣ}

theorem tc_exists_exp [NeZero p] (hζ : IsPrimitiveRoot ζ p) (c : Lˣ) (hc : c ^ p = 1) :
    ∃ i : ℕ, i < p ∧ ζ ^ i = c := by
  have hζ' : IsPrimitiveRoot (ζ : L) p := hζ.map_of_injective (f := Units.coeHom L)
    Units.val_injective
  obtain ⟨i, hi, h⟩ := hζ'.eq_pow_of_pow_eq_one (ξ := (c : L)) (by
    have := congrArg Units.val hc
    simpa using this)
  exact ⟨i, hi, Units.ext (by simpa using h)⟩

noncomputable def tcExp [NeZero p] (hζ : IsPrimitiveRoot ζ p) (c : Lˣ) (hc : c ^ p = 1) : ZMod p :=
  ((tc_exists_exp hζ c hc).choose : ℕ)

theorem tcExp_val [NeZero p] (hζ : IsPrimitiveRoot ζ p) (c : Lˣ) (hc : c ^ p = 1) :
    ζ ^ (tcExp hζ c hc).val = c := by
  have h := (tc_exists_exp hζ c hc).choose_spec
  rw [tcExp, ZMod.val_natCast_of_lt h.1]
  exact h.2

theorem tc_pow_eq_iff (hζ : IsPrimitiveRoot ζ p) (m n : ℕ) :
    ζ ^ m = ζ ^ n ↔ (m : ZMod p) = n := by
  rw [pow_eq_pow_iff_modEq, ← hζ.eq_orderOf, ZMod.natCast_eq_natCast_iff]

noncomputable def tcExpVec [NeZero p] (hζ : IsPrimitiveRoot ζ p) {τ : Tag} (a : Fin τ.rank → Lˣ)
    (ha : ∀ j, a j ^ p = 1) : Fin τ.rank → ZMod p :=
  fun j => tcExp hζ (a j) (ha j)

theorem tcRootChar_formula [NeZero p] (hζ : IsPrimitiveRoot ζ p) {τ : Tag}
    (a : Fin τ.rank → Lˣ) (ha : ∀ j, a j ^ p = 1) (γ : Fin τ.rank → ℤ) :
    rootChar a γ = ζ ^ (∑ j, γ j * (((tcExpVec hζ a ha) j).val : ℤ)) := by
  unfold rootChar
  rw [← prod_zpow_eq_zpow_finset_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  have h : a j = ζ ^ (((tcExpVec hζ a ha) j).val : ℤ) := by
    rw [zpow_natCast]
    exact (tcExp_val hζ (a j) (ha j)).symm
  rw [h, ← zpow_mul, mul_comm]

theorem tcExpVec_pow_val [NeZero p] (hζ : IsPrimitiveRoot ζ p) {τ : Tag}
    (a : Fin τ.rank → Lˣ) (ha : ∀ j, a j ^ p = 1) (j : Fin τ.rank) :
    ζ ^ (tcExpVec hζ a ha j).val = a j :=
  tcExp_val hζ (a j) (ha j)

theorem tcRootChar_eq_one_iff [NeZero p] (hζ : IsPrimitiveRoot ζ p) {τ : Tag}
    (a : Fin τ.rank → Lˣ) (ha : ∀ j, a j ^ p = 1) (γ : Fin τ.rank → ℤ) :
    rootChar a γ = 1 ↔ ∑ j, ((γ j : ℤ) : ZMod p) * tcExpVec hζ a ha j = 0 := by
  rw [rootChar_eq_one_iff_dvd_pairing hζ a (fun j => (((tcExpVec hζ a ha) j).val : ℤ))
    (fun j => by rw [zpow_natCast]; exact (tcExpVec_pow_val hζ a ha j).symm) γ,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  simp only [ZMod.natCast_zmod_val]

theorem tc_frobenius
    [IsAlgClosed L] {p₀ : ℕ} [NeZero p]
    (hζ : IsPrimitiveRoot ζ p) {τ : Tag} (S : LangSetup τ L p₀) (a : Fin τ.rank → Lˣ)
    (ha : ∀ j, a j ^ p = 1) (haT : rootDiagUnit τ a ∈ S.D.torus) (j : Fin τ.rank) :
    ∑ k, (((S.ρ (Pi.single j 1)) k : ℤ) : ZMod p) * tcExpVec hζ a ha k =
      ((S.D.q : ℕ) : ZMod p) * tcExpVec hζ a ha j := by
  have h := (rootDiagUnit_mem_langTorus_iff S a).1 haT (Pi.single j 1) (isRoot_single τ j)
  rw [tcRootChar_formula hζ a ha, CFSG.RankThree.PartOne.KE.CTTorus.rootChar_single] at h
  have hj : a j = ζ ^ (((tcExpVec hζ a ha) j).val : ℤ) := by
    rw [zpow_natCast]
    exact (tcExp_val hζ (a j) (ha j)).symm
  rw [hj, ← zpow_natCast, ← zpow_mul] at h
  have h2 : ζ ^ ((∑ k, ((S.ρ (Pi.single j 1)) k) * (((tcExpVec hζ a ha) k).val : ℤ)) -
      (((tcExpVec hζ a ha) j).val : ℤ) * (S.D.q : ℤ)) = 1 := by
    rw [zpow_sub, h, mul_inv_cancel]
  rw [hζ.zpow_eq_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
  push_cast at h2
  simp only [ZMod.natCast_zmod_val] at h2
  rw [sub_eq_zero] at h2
  rw [h2, mul_comm]

end Param

end CFSG.StandardType.TableCRes

end
