module

public import CFSG.LocalAnalysis.WeakClosure81.W16LPU3Cent
public import CFSG.LocalAnalysis.WeakClosure81.W16LPU3Calc

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.CGT.PushingUpLit.CGT6
open scoped MatrixGroups

variable {s : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 s F)

theorem w16l_isPerfect_Sig01 (hs : 2 ≤ s) : Group.IsPerfect ↥(Sig01 h) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := h.charP
  haveI : Finite F := h.finite
  have hq : 4 ≤ 2 ^ s := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  haveI : Group.IsPerfect ↥(unitarySU 2 s F 2) :=
    CFSG.RankThree.SubgroupLists.isPerfect_statedSU_two (K := F) (r := 2) (f := s)
      h.card_eq_sq hq
  have hperf' : Group.IsPerfect ↥(gramSU h (1 : Matrix (Fin 2) (Fin 2) F)) :=
    Group.IsPerfect.ofSurjective
      (f := (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 2)).toMonoidHom)
      (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 2)).surjective
  haveI : Group.IsPerfect ↥(gramSU h (1 : Matrix (Fin 2) (Fin 2) F)) := hperf'
  exact Group.IsPerfect.range (blkHom h)

theorem w16l_commute_of_map_commute_Sig01 (hs : 2 ≤ s) {Q : Type} [Group Q]
    (π : ↥(unitarySU 2 s F 3) →* Q) (hker : π.ker ≤ Subgroup.center ↥(unitarySU 2 s F 3))
    {g : ↥(unitarySU 2 s F 3)} (hg : ∀ σ ∈ Sig01 h, π g * π σ = π σ * π g) :
    ∀ σ ∈ Sig01 h, g * σ = σ * g := by
  haveI : Group.IsPerfect ↥(Sig01 h) := w16l_isPerfect_Sig01 h hs
  let Z := Subgroup.center ↥(unitarySU 2 s F 3)
  let φ : ↥(Sig01 h) →* Z :=
    MonoidHom.mk'
      (fun σ => ⟨g * (σ : unitarySU 2 s F 3) * g⁻¹ * (σ : unitarySU 2 s F 3)⁻¹,
        hker (MonoidHom.mem_ker.mpr (by
          simp only [map_mul, map_inv]
          rw [hg (σ : unitarySU 2 s F 3) σ.2]
          group))⟩)
      (by
        intro a b
        apply Subtype.ext
        have hc : g * (b : unitarySU 2 s F 3) * g⁻¹ * (b : unitarySU 2 s F 3)⁻¹ ∈ Z :=
          hker (MonoidHom.mem_ker.mpr (by
            simp only [map_mul, map_inv]
            rw [hg (b : unitarySU 2 s F 3) b.2]
            group))
        have hcomm : (g * (b : unitarySU 2 s F 3) * g⁻¹ * (b : unitarySU 2 s F 3)⁻¹)
            * (a : unitarySU 2 s F 3)⁻¹ =
            (a : unitarySU 2 s F 3)⁻¹ *
              (g * (b : unitarySU 2 s F 3) * g⁻¹ * (b : unitarySU 2 s F 3)⁻¹) :=
          (Subgroup.mem_center_iff.mp hc _).symm
        change g * ((a : unitarySU 2 s F 3) * (b : unitarySU 2 s F 3)) * g⁻¹ *
              ((a : unitarySU 2 s F 3) * (b : unitarySU 2 s F 3))⁻¹ =
            (g * (a : unitarySU 2 s F 3) * g⁻¹ * (a : unitarySU 2 s F 3)⁻¹) *
              (g * (b : unitarySU 2 s F 3) * g⁻¹ * (b : unitarySU 2 s F 3)⁻¹)
        calc g * ((a : unitarySU 2 s F 3) * (b : unitarySU 2 s F 3)) * g⁻¹ *
              ((a : unitarySU 2 s F 3) * (b : unitarySU 2 s F 3))⁻¹
            = (g * (a : unitarySU 2 s F 3) * g⁻¹) *
                ((g * (b : unitarySU 2 s F 3) * g⁻¹ * (b : unitarySU 2 s F 3)⁻¹)
                  * (a : unitarySU 2 s F 3)⁻¹) := by group
          _ = (g * (a : unitarySU 2 s F 3) * g⁻¹) *
                ((a : unitarySU 2 s F 3)⁻¹ *
                  (g * (b : unitarySU 2 s F 3) * g⁻¹ * (b : unitarySU 2 s F 3)⁻¹)) := by
                rw [hcomm]
          _ = (g * (a : unitarySU 2 s F 3) * g⁻¹ * (a : unitarySU 2 s F 3)⁻¹) *
                (g * (b : unitarySU 2 s F 3) * g⁻¹ * (b : unitarySU 2 s F 3)⁻¹) := by group)
  have hφ : φ = 1 := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_one_of_commutative φ
  intro σ hσ
  have hval : g * σ * g⁻¹ * σ⁻¹ = 1 := by
    have h := congrArg (fun f : ↥(Sig01 h) →* Z => f ⟨σ, hσ⟩) hφ
    exact congrArg (fun z : Z => (z : unitarySU 2 s F 3)) h
  calc g * σ = g * σ * g⁻¹ * σ⁻¹ * (σ * g) := by group
    _ = 1 * (σ * g) := by rw [hval]
    _ = σ * g := one_mul _

theorem w16l_swap_of_centralizes_Sig01 (hs : 2 ≤ s) {Q : Type} [Group Q]
    (π : ↥(unitarySU 2 s F 3) →* Q) (hsurj : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥(unitarySU 2 s F 3)) {X' : Subgroup Q}
    (hX : X' ≤ Subgroup.centralizer (((Sig01 h).map π : Subgroup Q) : Set Q))
    (hnc : ¬ X' ≤ Subgroup.center Q) :
    ∃ x ∈ X', ∃ k : Q, k⁻¹ * x * k ∈ (Sig01 h).map π ⊔ X' ∧ k⁻¹ * x * k ∉ X' := by
  obtain ⟨x', hx'X, hx'c⟩ := SetLike.not_le_iff_exists.mp hnc
  obtain ⟨xt, hxt'⟩ := hsurj x'
  rw [← hxt'] at hx'X hx'c
  have hcomm : ∀ σ ∈ Sig01 h, xt * σ = σ * xt := by
    intro σ hσ
    exact w16l_commute_of_map_commute_Sig01 h hs π hker (g := xt) (by
      intro τ hτ
      exact ((Subgroup.mem_centralizer_iff.mp (hX hx'X)) (π τ)
        (Subgroup.mem_map_of_mem π hτ)).symm) σ hσ
  obtain ⟨u, w, hu, hw, hdet, hxt⟩ := w16l_eq_diagG_of_commute_Sig01 h hs hcomm
  have hu3 : u ^ 3 ≠ 1 := by
    intro h3
    have hmem : xt ∈ unitaryScalars h 3 := by
      rw [hxt]
      exact (w16l_diagG_mem_unitaryScalars_iff h u w hu hw hdet).mpr h3
    have hcen : xt ∈ Subgroup.center ↥(unitarySU 2 s F 3) :=
      unitaryScalars_le_center h 3 hmem
    apply hx'c
    rw [Subgroup.mem_center_iff] at hcen ⊢
    intro q
    obtain ⟨y, hy⟩ := hsurj q
    rw [← hy]
    simpa only [map_mul] using congrArg π (hcen y)
  have hy : (PG h)⁻¹ * xt * PG h ∈
      Sig01 h ⊔ Subgroup.zpowers (diagG h u u w hu hu hw hdet) := by
    rw [hxt]
    exact w16l_PG_conj_mem h u w hu hw hdet
  have hk : (π (PG h))⁻¹ * π xt * π (PG h) = π ((PG h)⁻¹ * xt * PG h) := by
    rw [map_mul, map_mul, map_inv]
  refine ⟨π xt, hx'X, π (PG h), ?_, ?_⟩
  · rw [hk]
    have h1 : π ((PG h)⁻¹ * xt * PG h) ∈
        (Sig01 h ⊔ Subgroup.zpowers (diagG h u u w hu hu hw hdet)).map π :=
      Subgroup.mem_map_of_mem π hy
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← hxt] at h1
    exact sup_le_sup_left (Subgroup.zpowers_le.mpr hx'X) ((Sig01 h).map π) h1
  · intro hmem
    rw [hk] at hmem
    have hy_comm : ∀ σ ∈ Sig01 h,
        ((PG h)⁻¹ * xt * PG h) * σ = σ * ((PG h)⁻¹ * xt * PG h) :=
      w16l_commute_of_map_commute_Sig01 h hs π hker (g := (PG h)⁻¹ * xt * PG h)
        (fun τ hτ => ((Subgroup.mem_centralizer_iff.mp (hX hmem)) (π τ)
          (Subgroup.mem_map_of_mem π hτ)).symm)
    have hycent : (PG h)⁻¹ * xt * PG h ∈
        Subgroup.centralizer (Sig01 h : Set (unitarySU 2 s F 3)) :=
      Subgroup.mem_centralizer_iff.mpr fun σ hσ => (hy_comm σ hσ).symm
    rw [hxt] at hycent
    exact w16l_PG_conj_not_centralizes h u w hu hw hdet hu3 hycent

end CFSG.LocalAnalysis.WeakClosure81

end
