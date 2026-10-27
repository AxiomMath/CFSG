module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PSUCoreE
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Fischer.Classification.Unitary.Model
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.GF2n.Stroth78

open Matrix CFSG.SeitzReduction.UnitaryPilot CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.Blueprint.Fischer (K)
open CFSG.Open (IsElemAbelian pCoreOf)

variable {m : ℕ}

namespace Sec4PSU

theorem unitarySU_eq_SUid (m : ℕ) : unitarySU 2 1 K m = SUid frob m :=
  (SUid_eq_statedSU card_K m).symm

noncomputable abbrev suEquiv (m : ℕ) : unitarySU 2 1 K m ≃* SUid frob m :=
  MulEquiv.subgroupCongr (unitarySU_eq_SUid m)

theorem coe_suEquiv (g : unitarySU 2 1 K m) :
    ((suEquiv m g : SUid frob m) : GL (Fin m) K) = (g : GL (Fin m) K) :=
  rfl

theorem herm_tvVec (i j : Fin m) (x : Fin m → K) :
    herm frob (tvVec (K := K) i j) x = x i + x j := by
  have := herm_single_add_single_left i j (1 : K) x
  rw [map_one, one_mul] at this
  exact this

theorem suEquiv_tvTransSU {i j : Fin m} (hij : i ≠ j) :
    suEquiv m (tvTransSU hK hij) = tvU (tvVec i j) := by
  have hv : herm frob (tvVec (K := K) i j) (tvVec i j) = 0 :=
    isotropic_single_add_single hij one_ne_zero
  refine ext_smul frob fun x => ?_
  rw [tvU_smul hv, smul_def, coe_suEquiv, coe_tvTransSU, add_mulVec, one_mulVec, tvNil,
    vecMulVec_mulVec, op_smul_eq_smul, herm_tvVec]
  congr 2
  rw [tvVec, add_dotProduct, single_dotProduct, single_dotProduct, one_mul, one_mul]

end Sec4PSU

open Sec4PSU in
theorem exists_core_centralizer_tqU (hm : 5 ≤ m) {v : Fin m → K} (hv0 : v ≠ 0)
    (hv : herm frob v v = 0) :
    ∃ W : Subgroup (U2 m),
      W ≤ ⁅⁅Subgroup.centralizer {tqU v}, Subgroup.centralizer {tqU v}⁆,
        ⁅Subgroup.centralizer {tqU v}, Subgroup.centralizer {tqU v}⁆⁆ ∧
      CFSG.GroupTheory.oddOrderClosure W = W ∧
      pCoreOf 2 (Subgroup.normalizer (Subgroup.zpowers (tqU v) : Set (U2 m))) ≤ W ∧
      (∀ E : Subgroup (U2 m), IsElemAbelian 2 E → Subgroup.zpowers (tqU v) ≤ E →
        E ≤ Subgroup.centralizer {tqU v} → (∀ x ∈ W, ∀ e ∈ E, x * e * x⁻¹ ∈ E) →
          E = Subgroup.zpowers (tqU v)) ∧
      (∀ s ∈ pCoreOf 2 (Subgroup.normalizer (Subgroup.zpowers (tqU v) : Set (U2 m))),
        (∀ x ∈ W, x⁻¹ * s⁻¹ * x * s ∈ Subgroup.zpowers (tqU v)) →
          s ∈ Subgroup.zpowers (tqU v)) := by
  classical
  set i : Fin m := ⟨0, by omega⟩ with hi
  set j : Fin m := ⟨1, by omega⟩ with hj
  have hij : i ≠ j := by simp [hi, hj, Fin.ext_iff]
  have hv₀ : herm frob (tvVec (K := K) i j) (tvVec i j) = 0 :=
    isotropic_single_add_single hij one_ne_zero
  have hv₀0 : tvVec (K := K) i j ≠ 0 := by
    intro h
    have := congrFun h i
    rw [tvVec_left hij, Pi.zero_apply] at this
    exact one_ne_zero this
  obtain ⟨t, -, ht⟩ := exists_mem_T_smul_eq_of_iso isUnitaryInvolution_frob (by omega : 3 ≤ m)
    hv₀0 hv₀ hv0 hv
  set Φ : unitarySU 2 1 K m →* U2 m :=
    (u2Equiv m).symm.toMonoidHom.comp ((MulAut.conj (QuotientGroup.mk t : PG m)).toMonoidHom.comp
      ((QuotientGroup.mk' (Subgroup.center (SUid frob m))).comp (suEquiv m).toMonoidHom))
    with hΦ
  have hsurj : Function.Surjective Φ :=
    (u2Equiv m).symm.surjective.comp ((MulAut.conj _).surjective.comp
      ((QuotientGroup.mk'_surjective _).comp (suEquiv m).surjective))
  have hΦz : Φ (tvTransSU hK hij) = tqU v := by
    simp only [hΦ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      QuotientGroup.mk'_apply, suEquiv_tvTransSU hij]
    rw [conj_tq t hv₀, ht, tqU_eq]
  have hkerC : ∀ g, Φ g = 1 → suEquiv m g ∈ Subgroup.center (SUid frob m) := by
    intro g hg
    simp only [hΦ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply] at hg
    exact (QuotientGroup.eq_one_iff _).1 hg
  have hker : Φ.ker ≤ Subgroup.center (unitarySU 2 1 K m) := by
    intro g hg
    have hc := hkerC g hg
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro y
    apply (suEquiv m).injective
    rw [map_mul, map_mul]
    exact hc (suEquiv m y)
  have hodd : ∀ ζ ∈ Φ.ker, Odd (orderOf ζ) := by
    intro ζ hζ
    have hc := hkerC ζ hζ
    rw [center_SUid (by omega)] at hc
    obtain ⟨c, hcx⟩ := exists_smul_eq_of_mem_scalars hc
    have hc0 : c ≠ 0 := by
      intro h0
      have h1 := hcx (Pi.single i 1)
      rw [h0, zero_smul] at h1
      have := (smul_eq_zero_iff_eq (suEquiv m ζ)).1 h1
      have := congrFun this i
      rw [Pi.single_eq_same, Pi.zero_apply] at this
      exact one_ne_zero this
    have hc3 : c ^ 3 = 1 := by
      haveI : Fintype K := Fintype.ofFinite K
      have := FiniteField.pow_card_sub_one_eq_one c hc0
      rwa [show Fintype.card K = 4 by rw [← Nat.card_eq_fintype_card, card_K]; rfl] at this
    have h3 : suEquiv m ζ ^ 3 = 1 := ext_smul frob fun x => by
      rw [pow_succ, pow_succ, pow_one, mul_smul, mul_smul, hcx, hcx, hcx, smul_smul, smul_smul,
        one_smul, show c * c * c = c ^ 3 by ring, hc3, one_smul]
    have hζ3 : ζ ^ 3 = 1 := (suEquiv m).injective (by rw [map_pow, h3, map_one])
    exact Odd.of_dvd_nat ⟨1, rfl⟩ (orderOf_dvd_of_pow_eq_one hζ3)
  have hJ : 3 ≤ ({i, j}ᶜ : Finset (Fin m)).card := by
    rw [Finset.card_compl, Finset.card_pair_eq_two_iff.2 hij, Fintype.card_fin]
    omega
  haveI : Finite K := hK.finite
  haveI : Finite (unitarySU 2 1 K m) := inferInstance
  obtain ⟨h1, h2, h3, h4, h5⟩ := coreW_spec hij hJ
  have key := map_coreProperties Φ hsurj hker hodd (tvTransSU_mul_self hij)
    (tvTransSU_ne_one hij) h1 h2 h3 h4 h5
  rw [hΦz] at key
  exact ⟨_, key⟩

end CFSG.RankThree.GF2n.Stroth78
