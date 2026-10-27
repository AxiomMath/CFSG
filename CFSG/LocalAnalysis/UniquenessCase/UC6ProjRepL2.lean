module

public import CFSG.LocalAnalysis.UniquenessCase.UC6ProjRepClauses
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FG2SWeights
public import CFSG.RankThree.PartOne.KF.ClsCover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.Open CFSG.SL2MinimalFaithful CFSG.RankThree.PartOne.SRC
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped MatrixGroups

section Weights

theorem sl2_finrank_of_unipotent_ne_one {F L V : Type*} [Field F] [Finite F] [Field L] [IsAlgClosed L]
    [AddCommGroup V] [Module L V] [FiniteDimensional L V] (hrL : ((ringChar F : ℕ) : L) ≠ 0)
    (R : SL(2, F) →* Module.End L V) (hnt : ∃ t : F, R (unipotent t) ≠ 1) :
    (Nat.card F - 1) / 2 ≤ Module.finrank L V := by
  classical
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf ζ = Nat.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_units]
  have hrF : ((ringChar F : ℕ) : F) = 0 := ringChar.Nat.cast_ringChar
  have hmul : ∀ s t, R (unipotent (s + t)) = R (unipotent s) * R (unipotent t) := by
    intro s t
    rw [unipotent_add, map_mul]
  have hone : R (unipotent (0 : F)) = 1 := by rw [unipotent_zero, map_one]
  have hss : ∀ t : F, (R (unipotent t)).IsSemisimple := by
    intro t
    refine CFSG.UnitaryInvolutionIndex.isSemisimple_of_pow_eq_one hrL ?_
    rw [← map_pow, sl2_unipotent_pow_nsmul, nsmul_eq_mul, hrF, zero_mul, unipotent_zero, map_one]
  have hinj : Function.Injective (R (torus ζ)⁻¹) := by
    intro x y hxy
    have h1 : R (torus ζ) * R (torus ζ)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have := congrArg (R (torus ζ)) hxy
    simpa [← Module.End.mul_apply, h1] using this
  have hc : (ζ : F) ^ 2 ≠ 0 := pow_ne_zero 2 ζ.ne_zero
  have hh : ∀ t : F, R (unipotent t) * R (torus ζ)⁻¹ =
      R (torus ζ)⁻¹ * R (unipotent ((ζ : F) ^ 2 * t)) := by
    intro t
    rw [← map_mul, ← map_mul]
    congr 1
    have h1 := torus_mul_unipotent ζ t
    calc unipotent t * (torus ζ)⁻¹ = (torus ζ)⁻¹ * (torus ζ * unipotent t) * (torus ζ)⁻¹ := by group
      _ = (torus ζ)⁻¹ * (unipotent ((ζ : F) ^ 2 * t) * torus ζ) * (torus ζ)⁻¹ := by rw [h1]
      _ = (torus ζ)⁻¹ * unipotent ((ζ : F) ^ 2 * t) := by group
  have hcm : ∀ k : ℕ, 0 < k → k < (Nat.card F - 1) / 2 → ((ζ : F) ^ 2) ^ k ≠ 1 := by
    intro k hk0 hkm hk1
    have h1 : ζ ^ (2 * k) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, pow_mul]
      simpa using hk1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at h2
    have h3 := Nat.le_of_dvd (by omega) h2
    omega
  exact le_finrank_of_twisted_additive_family (F := F) (L := L) (V := V)
    (fun t => R (unipotent t)) hmul hone hss (R (torus ζ)⁻¹) hinj ((ζ : F) ^ 2) hc hh
    (m := (Nat.card F - 1) / 2) hcm hnt

theorem sl2_unipotent_eq_one_of_lt {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hpF : ringChar F ≠ p) {d : ℕ} (hd : d < (Nat.card F - 1) / 2)
    (ρ : SL(2, F) →* Matrix.GeneralLinearGroup (Fin d) (ZMod p)) (t : F) : ρ (unipotent t) = 1 := by
  by_contra hne
  let L := AlgebraicClosure (ZMod p)
  let Φ : Matrix.GeneralLinearGroup (Fin d) (ZMod p) →* Module.End L (Fin d → L) :=
    (Matrix.toLinAlgEquiv' (R := L) (n := Fin d)).toAlgHom.toRingHom.toMonoidHom.comp
      ((algebraMap (ZMod p) L).mapMatrix.toMonoidHom.comp
        (Units.coeHom (Matrix (Fin d) (Fin d) (ZMod p))))
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    have h1 := Matrix.toLinAlgEquiv'.injective hxy
    have h2 := Matrix.map_injective (algebraMap (ZMod p) L).injective h1
    exact Units.ext h2
  have hrprime : (ringChar F).Prime := CharP.prime_ringChar F
  have hrL : ((ringChar F : ℕ) : L) ≠ 0 := by
    intro h0
    have h1 : p ∣ ringChar F := (CharP.cast_eq_zero_iff L p _).mp h0
    exact hpF ((Nat.prime_dvd_prime_iff_eq Fact.out hrprime).mp h1).symm
  have key := sl2_finrank_of_unipotent_ne_one hrL (Φ.comp ρ)
    ⟨t, fun h => hne (hΦ (by rw [map_one]; exact h))⟩
  rw [Module.finrank_fin_fun] at key
  omega

end Weights

section Lift

open CFSG.SectionRank.EvenCover CFSG.LieType.Steinberg


theorem exists_lift_of_sl2 {F : Type} [Field F] [Finite F] (h5 : 5 ≤ Nat.card F)
    (h9 : Nat.card F ≠ 9) {G : Type*} [Group G] (g : SL(2, F) →* G ⧸ center G) :
    ∃ ρ : SL(2, F) →* G, (QuotientGroup.mk' (center G)).comp ρ = g := by
  have hπ : Function.Surjective (QuotientGroup.mk' (center G)) := QuotientGroup.mk'_surjective _
  have hcen : (QuotientGroup.mk' (center G)).ker ≤ center G := by rw [QuotientGroup.ker_mk']
  obtain ⟨σ, hσ⟩ := CFSG.LieType.Steinberg.CentralExt.SL2Closed.sl2_exists_section_of_central
    h5 h9 (pullbackFst_surjective hπ g) (pullbackFst_ker_le_center hcen g)
  exact ⟨_, comp_snd_section σ hσ⟩

theorem exists_sl2Lower_eq_conj {F : Type*} [Field F] (c : F) :
    ∃ w : SL(2, F), sl2Lower c = w * sl2Upper (-c) * w⁻¹ := by
  refine ⟨(sl2Rels F).w 1, ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Lower,
    coe_sl2Rels_w (one_ne_zero (α := F))]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2_hom_pgl_eq_one {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hpF : ringChar F ≠ p) (h5 : 5 ≤ Nat.card F) (h9 : Nat.card F ≠ 9) {d : ℕ}
    (hd : d < (Nat.card F - 1) / 2)
    (g : SL(2, F) →* Matrix.GeneralLinearGroup (Fin d) (ZMod p) ⧸
      center (Matrix.GeneralLinearGroup (Fin d) (ZMod p))) : g = 1 := by
  obtain ⟨ρ, hρ⟩ := exists_lift_of_sl2 h5 h9 g
  have hU : ∀ c : F, ρ (sl2Upper c) = 1 := fun c => sl2_unipotent_eq_one_of_lt hpF hd ρ c
  have hL : ∀ c : F, ρ (sl2Lower c) = 1 := fun c => by
    obtain ⟨w, hw⟩ := exists_sl2Lower_eq_conj c
    rw [hw, map_mul, map_mul, hU, mul_one, map_inv, mul_inv_cancel]
  have hρ1 : ρ = 1 := sl2_hom_ext (fun c => by rw [hU, MonoidHom.one_apply])
    (fun c => by rw [hL, MonoidHom.one_apply])
  rw [← hρ, hρ1]
  ext x
  simp

end Lift

section Main


theorem kProjRepL2_holds : KProjRepL2 := by
  intro J _ _ hq N _ hN r hr hr5 hL q hq' hqr d hd f
  haveI : Fact q.Prime := ⟨hq'⟩
  have hr2 : r ≠ 2 := by omega
  obtain ⟨F, _, _, e, -, hFq⟩ := CFSG.GH74.GLS.EvenSelP.exists_l2Field_of_lieModel' hr hr2 hL
  haveI : Fintype F := Fintype.ofFinite F
  let φ : J ⧸ N ≃* PSL(2, F) := CFSG.GH74.GLS.IVK.toPSL e
  have hchar : ringChar F = r := by
    obtain ⟨n, hn⟩ := FiniteField.card F (ringChar F)
    have hcp : (ringChar F).Prime := CharP.prime_ringChar F
    have hdvd : ringChar F ∣ r ^ 2 := by
      rw [← hFq, Nat.card_eq_fintype_card, hn.2]
      exact dvd_pow_self _ n.ne_zero
    exact (Nat.prime_dvd_prime_iff_eq hcp hr).1 (hcp.dvd_of_dvd_pow hdvd)
  have h25 : 25 ≤ Nat.card F := by
    rw [hFq]
    nlinarith
  have h9 : Nat.card F ≠ 9 := by omega
  have hdF : d < (Nat.card F - 1) / 2 := by omega
  have hperf : Group.IsPerfect J := ⟨hq.1⟩
  let π : SL(2, F) →* J ⧸ N :=
    (φ.symm : PSL(2, F) →* J ⧸ N).comp (QuotientGroup.mk' (center SL(2, F)))
  have hπs : Function.Surjective π := φ.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπc : π.ker ≤ center SL(2, F) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : QuotientGroup.mk' (center SL(2, F)) x = 1 := (MulEquiv.map_eq_one_iff φ.symm).1 hx
    exact (QuotientGroup.eq_one_iff x).1 h1
  have hSperf : Group.IsPerfect (J ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  have hEperf : Group.IsPerfect SL(2, F) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect
      (CFSG.LieType.Steinberg.CentralExt.SL2Closed.exists_four_of_five_le (by omega))
  obtain ⟨eM⟩ := CFSG.LieType.Steinberg.CentralExt.SL2Closed.sl2_hopfMultiplier_mulEquiv_ker
    (k := F) (by omega) h9 π hπs hπc
  obtain ⟨ρ, -, hρs⟩ := CFSG.RankThree.PartOne.KFU.exists_hom_of_card_multiplier_eq hSperf hEperf π hπs
    hπc (Nat.card_congr eM.toEquiv) (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    (by rw [QuotientGroup.ker_mk']; exact hN)
  have hρsurj : Function.Surjective ρ := hρs hperf
  have hg : f.comp ρ = 1 := sl2_hom_pgl_eq_one (by rw [hchar]; exact hqr.symm) (by omega) h9 hdF (f.comp ρ)
  ext x
  obtain ⟨s, rfl⟩ := hρsurj x
  exact congrArg (fun k : SL(2, F) →* _ => k s) hg

end Main

end CFSG.LocalAnalysis.UniquenessCase.UCK
