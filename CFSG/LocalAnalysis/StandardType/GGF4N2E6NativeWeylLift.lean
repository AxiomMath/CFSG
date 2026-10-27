module

public import CFSG.LocalAnalysis.StandardType.GGF4N2E6NativeDict
public import CFSG.LocalAnalysis.StandardType.GGF4N2E6NativeSignedPerm
public import CFSG.CGT.Timmesfeld75.L2Real
public import CFSG.LocalAnalysis.StandardType.GGF4N2E6NativeA5

public section

namespace CFSG.StandardType.N2E6Native

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE6
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny

section Group

variable {U : Type} [Group U]

theorem eq_of_eq_central_mul_of_pow_five (hZ : ∀ w ∈ Subgroup.center U, w ^ 3 = 1)
    {x x' z : U} (hz : z ∈ Subgroup.center U) (hx : x ^ 5 = 1) (hx' : x' ^ 5 = 1)
    (h : x = z * x') : x = x' := by
  have hcomm : Commute z x' := (Subgroup.mem_center_iff.mp hz x').symm
  have h5 : z ^ 5 = 1 := by
    have h5' : x ^ 5 = (z * x') ^ 5 := by rw [h]
    rwa [hx, hcomm.mul_pow, hx', mul_one, eq_comm] at h5'
  have h1 : orderOf z ∣ Nat.gcd 5 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h5) (orderOf_dvd_of_pow_eq_one (hZ z hz))
  rw [show Nat.gcd 5 3 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h1
  rw [h, h1, one_mul]

end Group

section Native

variable {G : Type} [Group G] (ψ : ↥(e6Data_valid.minGroup (GaloisField 2 2)) →* G)
  (φ : Fin 4 → (SL2 (GaloisField 2 2) →* ↥(e6Data_valid.minGroup (GaloisField 2 2))))
  (hφ : ∀ k s, ((e6Isogeny (GaloisField 2 2) (φ k s) : ↥(adjointGroup Tag.E6 (GaloisField 2 2))) :
    ModGL Tag.E6 (GaloisField 2 2)) = rootSL2 Tag.E6 (GaloisField 2 2) (e6NativeGamma k) s)

include hφ in
theorem exists_conj_perm_rankOne {t : SL2 (GaloisField 2 2)} (ht : t ^ 5 = 1)
    (σ : Equiv.Perm (Fin 4)) :
    ∃ n ∈ ψ.range, ∀ i, n * ψ (φ i t) * n⁻¹ = ψ (φ (σ i) t) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hw⟩ := exists_weyl_perm σ
  obtain ⟨m, hm⟩ := e6Isogeny_surjective (GaloisField 2 2)
    ⟨canonicalRep (coxeterSystem Tag.E6) (GaloisField 2 2) w,
      canonicalRep_mem_adjointGroup (coxeterSystem Tag.E6) (GaloisField 2 2) w⟩
  have hZ : ∀ z ∈ Subgroup.center ↥(e6Data_valid.minGroup (GaloisField 2 2)), z ^ 3 = 1 :=
    fun z hz => CFSG.ClassicalInvolution.ModelFacts.A2Isogeny.center_pow_three_e6 _ hz
  have hpow : ∀ k, φ k t ^ 5 = 1 := fun k => by rw [← map_pow, ht, map_one]
  refine ⟨ψ m, ⟨m, rfl⟩, fun i => ?_⟩
  have hc : m * φ i t * m⁻¹ * (φ (σ i) t)⁻¹ ∈
      Subgroup.center ↥(e6Data_valid.minGroup (GaloisField 2 2)) := by
    refine CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center _ ?_
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hm]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    rw [hφ, hφ, canonicalRep_conj_rootSL2 w (e6NativeGamma_isRoot i), hw i, mul_inv_cancel]
  have heq := eq_of_eq_central_mul_of_pow_five (x := m * φ i t * m⁻¹) hZ hc
    (by rw [conj_pow, hpow, mul_one, mul_inv_cancel]) (hpow (σ i)) (by group)
  have hψ : ψ m * ψ (φ i t) * (ψ m)⁻¹ = ψ (m * φ i t * m⁻¹) := by
    simp only [map_mul, map_inv]
  rw [hψ, heq]

end Native

section Marked

@[expose] noncomputable def markedRankOne
    (rho : SL2 (GaloisField 2 2) →* ↥(e6Data_valid.minGroup (GaloisField 2 2))) :
    Fin 4 → (SL2 (GaloisField 2 2) →* ↥(e6Data_valid.minGroup (GaloisField 2 2))) :=
  ![(CFSG.SeitzReduction.F4Pilot.slToE6Sc (GaloisField 2 2)).comp
      (CFSG.ClassicalInvolution.WeakCT.blockSL2 (GaloisField 2 2) 5 0),
    (CFSG.SeitzReduction.F4Pilot.slToE6Sc (GaloisField 2 2)).comp
      (CFSG.ClassicalInvolution.WeakCT.blockSL2 (GaloisField 2 2) 5 2),
    (CFSG.SeitzReduction.F4Pilot.slToE6Sc (GaloisField 2 2)).comp
      (CFSG.ClassicalInvolution.WeakCT.blockSL2 (GaloisField 2 2) 5 4), rho]

theorem markedRankOne_isogeny
    (rho : SL2 (GaloisField 2 2) →* ↥(e6Data_valid.minGroup (GaloisField 2 2)))
    (hIso : ∀ s, ((e6Isogeny (GaloisField 2 2) (rho s) : ↥(adjointGroup Tag.E6 (GaloisField 2 2))) :
      ModGL Tag.E6 (GaloisField 2 2)) = rootSL2 Tag.E6 (GaloisField 2 2) (e6NativeGamma 3) s) :
    ∀ k s, ((e6Isogeny (GaloisField 2 2) (markedRankOne rho k s) :
      ↥(adjointGroup Tag.E6 (GaloisField 2 2))) : ModGL Tag.E6 (GaloisField 2 2)) =
        rootSL2 Tag.E6 (GaloisField 2 2) (e6NativeGamma k) s := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro k s
  fin_cases k
  · exact e6Isogeny_slToE6Sc_blockSL2_gamma 0 s
  · exact e6Isogeny_slToE6Sc_blockSL2_gamma 1 s
  · exact e6Isogeny_slToE6Sc_blockSL2_gamma 2 s
  · exact hIso s

end Marked

end CFSG.StandardType.N2E6Native

end
