module

public import CFSG.Quasithin.Background.C35InspLevi
public import CFSG.Quasithin.Background.C35InspL3
public import CFSG.Quasithin.H13.NQCatParabolicSL3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C35Levi

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Matrix C35Pf
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L

section SL3

variable {F : Type} [Field F] [Finite F]

theorem blk3_tv02 (hK4 : ∃ s : Finset F, s.card = 4) (j : Fin 2) :
    blk3 j ⟨H13.NQCat.SL3.tv (show (0 : Fin 3) ≠ 2 by decide) 1,
      H13.NQCat.SL3.unitriangular_le_perfectCore hK4 j
        (H13.NQCat.SL3.tv_mem_unitriangular (show (0 : Fin 3) < 2 by decide) 1)⟩ = 1 := by
  apply Subtype.ext
  rw [blk3_coe, H13.NQCat.SL3.coe_tv]
  ext i k
  fin_cases j <;> fin_cases i <;> fin_cases k <;>
    simp [blkAt, transvection, Matrix.one_apply, Matrix.single_apply]

theorem exists_noncomm_Q3 [CharP F 2] (hK4 : ∃ s : Finset F, s.card = 4) (j : Fin 2) :
    ∃ r x : ↥(perfectCore (Q3 F j)), blk3 j r = 1 ∧ x * r ≠ r * x := by
  obtain ⟨s, hs⟩ := H13.NQCat.exists_unit_ne_one hK4
  refine ⟨_, ⟨embSL j (H13.NQCat.dg2 s), embSL_mem_perfectCore hK4 j _⟩, blk3_tv02 hK4 j, ?_⟩
  intro h
  have h1 := congrArg Subtype.val h
  simp only [Subgroup.coe_mul] at h1
  have h2 : embSL j (H13.NQCat.dg2 s) * H13.NQCat.SL3.tv (show (0 : Fin 3) ≠ 2 by decide) 1 *
      (embSL j (H13.NQCat.dg2 s))⁻¹ = H13.NQCat.SL3.tv (show (0 : Fin 3) ≠ 2 by decide) 1 := by
    rw [h1, mul_inv_cancel_right]
  rw [H13.NQCat.SL3.embSL_dg2_conj_tv] at h2
  have h3 := congrFun (congrFun (congrArg Subtype.val h2) 0) 2
  rw [H13.NQCat.SL3.coe_tv, H13.NQCat.SL3.coe_tv] at h3
  apply hs
  fin_cases j <;> simpa [transvection, H13.NQCat.SL3.dv] using h3

end SL3

theorem levi_l3 {A : Type} [Group A] [Finite A] {K Y : Subgroup A}
    (hZ : IsPGroup 2 ↥(centerOf K)) {f : ℕ} (hf2 : 2 ≤ f)
    (hX : IsPSL 3 2 f (↥K ⧸ Subgroup.center ↥K)) (hpar : IsParabolic2 K Y) (hne : Y ≠ K)
    (hX0 : perfectCore Y ≠ ⊥) : LeviConcl K Y := by
  classical
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hX
  have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : ∃ k : ℕ, Nat.card F = 2 ^ k := ⟨f, hcard⟩
  have hK4 : ∃ s : Finset F, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  let φ : ↥K →* projectiveSL 3 F := (e.trans (statedSLEquivProjectiveSL 3 F)).toMonoidHom.comp
    (QuotientGroup.mk' (Subgroup.center ↥K))
  have hφker : φ.ker = Subgroup.center ↥K := by
    ext x
    rw [MonoidHom.mem_ker]
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := (e.trans (statedSLEquivProjectiveSL 3 F)).surjective y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) x
    exact ⟨k, hx⟩
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 3) (by norm_num)
  have hU : IsSylowTwoOf (projUnitriangular 3 F) ⊤ := hP ▸ isSylowTwoOf_top_of_sylow P
  obtain ⟨g, hNY, hne', hns⟩ := exists_conj_normalizer hZ hpar hne hX0 φ hφker.le hφs hU
  set θ := (MulAut.conj g⁻¹).toMonoidHom.comp φ with hθ
  have hθker : θ.ker = Subgroup.center ↥K := by rw [hθ, ker_conj_comp, hφker]
  have hYK : Y ≤ K := hpar.1
  have hB : upperTriangular 3 F ≤ (img θ Y).comap (proj 3 F) := by
    intro b hb
    show proj 3 F b ∈ img θ Y
    apply hNY
    rw [normalizer_projUnitriangular 2]
    exact ⟨b, hb, rfl⟩
  have hmc : ((img θ Y).comap (proj 3 F)).map (proj 3 F) = img θ Y :=
    Subgroup.map_comap_eq_self_of_surjective (proj_surjective 3 F) _
  have hŶne : (img θ Y).comap (proj 3 F) ≠ ⊤ := by
    intro h
    apply hne'
    rw [← hmc, h, Subgroup.map_top_of_surjective _ (proj_surjective 3 F)]
  have hŶns : ¬ Group.IsSolvable ↥((img θ Y).comap (proj 3 F)) := by
    intro hs
    apply hns
    rw [← hmc]
    exact Group.isSolvable_of_surjective ((proj 3 F).subgroupMap_surjective _)
  obtain ⟨j, hj⟩ := eq_Q3_of_overgroup hK hB hŶne hŶns
  have hYj : img θ Y = (Q3 F j).map (proj 3 F) := by
    rw [← hj, hmc]
  have hMj : img θ (perfectCore Y) = (perfectCore (Q3 F j)).map (proj 3 F) := by
    rw [img_perfectCore θ hYK, hYj, map_perfectCore]
  have hinj : Set.InjOn (proj 3 F)
      (perfectCore (Q3 F j) : Set (SpecialLinearGroup (Fin 3) F)) := by
    intro x hx y hy hxy
    have hz : x⁻¹ * y ∈ (proj 3 F).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    have h1 := blk3_scalars j ⟨x⁻¹ * y, mul_mem (inv_mem hx) hy⟩ (by rw [← ker_proj]; exact hz)
    exact inv_mul_eq_one.mp (congrArg Subtype.val h1)
  have := sl2_isSimple hK4
  obtain ⟨hc, ⟨eT⟩⟩ := levi_of_model hZ hYK θ hθker.le (proj 3 F) hinj hMj (sl2_nonabelian hK4)
    (blk3 j) (blk3_surjective hK4 j) (blk3_ker_isPGroup hK j) (exists_noncomm_Q3 hK4 j)
  exact leviConcl_of_small hc ((smallLevi_sl2 hcard hf2).of_mulEquiv eT.symm)

end CFSG.Quasithin.C35Levi
