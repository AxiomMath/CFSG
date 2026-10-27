module

public import CFSG.Quasithin.H13.NQCatLieOverRank2
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalL2Lie

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def ParConcl (Y : Type) [Group Y] (k : ℕ) (U : Subgroup Y) : Prop :=
  ∃ P : Fin 2 → Subgroup Y, P 0 ≠ P 1 ∧
    (∀ Q : Subgroup Y, Subgroup.normalizer (U : Set Y) ≤ Q → (Q ⋖ ⊤ ↔ ∃ j, Q = P j)) ∧
    (∀ j, Subgroup.normalizer (U : Set Y) ⋖ P j ∧ U ≤ perfectCore (P j) ∧
      IsPSL 2 2 k (ModO2 (perfectCore (P j)))) ∧
    perfectCore (P 0) ⊔ perfectCore (P 1) = ⊤

noncomputable def modO2Congr {Y Y' : Type} [Group Y] [Group Y'] {A : Subgroup Y}
    {A' : Subgroup Y'} (f : ↥A ≃* ↥A') : ModO2 A ≃* ModO2 A' :=
  QuotientGroup.congr _ _ f (CFSG.pCore_map_iso 2 f)

theorem ParConcl.map {Y Y' : Type} [Group Y] [Group Y'] [Finite Y] [Finite Y'] {k : ℕ}
    {U : Subgroup Y} (h : ParConcl Y k U) (e : Y ≃* Y') : ParConcl Y' k (U.map e.toMonoidHom) := by
  obtain ⟨P, hne, hmax, hj, hsup⟩ := h
  have hN : normalizer ((U.map e.toMonoidHom : Subgroup Y') : Set Y') =
      (normalizer (U : Set Y)).map e.toMonoidHom := (map_equiv_normalizer_eq U e).symm
  have hcov : ∀ A B : Subgroup Y, A.map e.toMonoidHom ⋖ B.map e.toMonoidHom ↔ A ⋖ B :=
    fun A B => apply_covBy_apply_iff (MulEquiv.mapSubgroup e)
  have hcore : ∀ A : Subgroup Y, perfectCore (A.map e.toMonoidHom) =
      (perfectCore A).map e.toMonoidHom := fun A => (CFSG.Quasithin.map_perfectCore _ A).symm
  have htop : (⊤ : Subgroup Y).map e.toMonoidHom = ⊤ := map_top_of_surjective _ e.surjective
  refine ⟨fun j => (P j).map e.toMonoidHom, fun h => hne (map_injective e.injective h),
    fun Q' hQ' => ?_, fun j => ⟨?_, ?_, ?_⟩, ?_⟩
  · have hQ : normalizer (U : Set Y) ≤ Q'.map e.symm.toMonoidHom := by
      rw [← Vol2Native.A312L.map_map_symm e (normalizer (U : Set Y))]
      exact map_mono (hN ▸ hQ')
    have hQ'' : (Q'.map e.symm.toMonoidHom).map e.toMonoidHom = Q' := by
      have h2 := Vol2Native.A312L.map_map_symm e.symm Q'
      rwa [MulEquiv.symm_symm] at h2
    rw [← hQ'', ← htop, hcov, hmax _ hQ]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, by rw [hj]⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, map_injective e.injective hj⟩
  · rw [hN, hcov]
    exact (hj j).1
  · rw [hcore]
    exact map_mono (hj j).2.1
  · let f : ↥(perfectCore (P j)) ≃* ↥(perfectCore ((P j).map e.toMonoidHom)) :=
      ((perfectCore (P j)).equivMapOfInjective e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr (hcore (P j)).symm)
    exact IsPSL.of_mulEquiv (modO2Congr f) (hj j).2.2
  · rw [hcore, hcore, ← Subgroup.map_sup, hsup, htop]

theorem parConcl_of_sylow {Y₀ Y : Type} [Group Y₀] [Group Y] [Finite Y] {k : ℕ}
    {U₀ : Subgroup Y₀} (h : ParConcl Y₀ k U₀) (hU₀ : IsSylowTwoOf U₀ ⊤) (e : Y₀ ≃* Y)
    {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) : ParConcl Y k U := by
  have : Finite Y₀ := Finite.of_equiv _ e.symm.toEquiv
  have hU₁ : IsSylowTwoOf (U₀.map e.toMonoidHom) ⊤ := by
    refine ⟨le_top, hU₀.2.1.map _, ?_⟩
    have h1 := hU₀.2.2
    rw [show (U₀.subgroupOf ⊤).index = U₀.index from relIndex_top_right _] at h1
    rwa [show ((U₀.map e.toMonoidHom).subgroupOf ⊤).index = (U₀.map e.toMonoidHom).index from
      relIndex_top_right _, MulEquiv.toMonoidHom_eq_coe, index_map_equiv]
  obtain ⟨g, rfl⟩ := exists_conj_map_eq hU₁ hU
  exact (h.map e).map (MulAut.conj g)

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.A312L

theorem parConcl_of_model {G₀ Y : Type} [Group G₀] [Group Y] [Finite G₀] [Finite Y]
    {K : Type} [Field K] [Finite K] [CharP K 2] {k : ℕ} (hk : 2 ≤ k) (hK : Nat.card K = 2 ^ k)
    (π : G₀ →* Y) (hπ : Function.Surjective π) {V B : Subgroup G₀} {Q : Fin 2 → Subgroup G₀}
    (hres : ResidualOvergroupsAt Y (V.map π) (fun j => (Q j).map π))
    (hN : normalizer ((V.map π : Subgroup Y) : Set Y) = B.map π) (hker : π.ker ≤ B)
    (hcov : ∀ j, B ⋖ Q j) (hV : ∀ j, V ≤ perfectCore (Q j))
    (g : ∀ j, ↥(perfectCore (Q j)) →* SpecialLinearGroup (Fin 2) K)
    (hg : ∀ j, Function.Surjective (g j)) (hgk : ∀ j, IsPGroup 2 (g j).ker)
    (hinj : ∀ j, ∀ x ∈ perfectCore (Q j), ∀ y ∈ perfectCore (Q j), π x = π y → x = y)
    (hsup : perfectCore (Q 0) ⊔ perfectCore (Q 1) = ⊤) :
    ParConcl Y k (V.map π) := by
  have hK4 := exists_finset_card_four_of_card hk hK
  have := sl2_isSimple hK4
  have hnab := sl2_nonabelian hK4
  refine ⟨fun j => (Q j).map π, hres.1, fun Q' hQ' => hres.2.2.1 Q' (le_normalizer.trans hQ'),
    fun j => ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hN]
    exact covBy_map_of_ker_le hπ hker (hcov j)
  · rw [← CFSG.Quasithin.map_perfectCore]
    exact map_mono (hV j)
  · let eN := perfectCoreMapEquiv π (Q j) (hinj j)
    let g' := (g j).comp eN.symm.toMonoidHom
    have hg' : Function.Surjective g' := (hg j).comp eN.symm.surjective
    have hk' : IsPGroup 2 g'.ker := fun z => by
      obtain ⟨m, hm⟩ := hgk j ⟨eN.symm z.1, z.2⟩
      have h1 : (eN.symm z.1) ^ 2 ^ m = 1 := congrArg Subtype.val hm
      refine ⟨m, Subtype.ext ?_⟩
      show z.1 ^ 2 ^ m = 1
      have : eN.symm (z.1 ^ 2 ^ m) = 1 := by rw [map_pow]; exact h1
      exact (map_eq_one_iff _ eN.symm.injective).mp this
    have h4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, K, inferInstance, inferInstance, hK,
      ⟨(modO2EquivOfHom hnab g' hg' hk').trans sl2EquivStatedProj⟩⟩
    · intro h
      have := congrArg Prod.snd h
      simp only at this
      omega
    · intro h
      have := congrArg Prod.snd h
      simp only at this
      omega
  · rw [← CFSG.Quasithin.map_perfectCore, ← CFSG.Quasithin.map_perfectCore, ← Subgroup.map_sup,
      hsup, map_top_of_surjective _ hπ]

variable {K : Type} [Field K] [Finite K] [CharP K 2] {k : ℕ}

theorem parConcl_projectiveSL (hk : 2 ≤ k) (hK : Nat.card K = 2 ^ k) :
    ParConcl (projectiveSL 3 K) k (projUnitriangular 3 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK4 := exists_finset_card_four_of_card hk hK
  refine parConcl_of_model hk hK (LinearFlag.proj 3 K) (proj_surjective 3 K)
    (B := upperTriangular 3 K)
    (linear_three_residual_of_cover ⟨k, hK⟩ (LinearFlag.proj 3 K) (proj_surjective 3 K)
      (ker_proj 3 K).le)
    (normalizer_projUnitriangular 2)
    (by rw [ker_proj]; exact scalars_le_upperTriangular 3 K) covBy_Q3
    (fun j => SL3.unitriangular_le_perfectCore hK4 j) (fun j => blk3 j) (blk3_surjective hK4)
    (blk3_ker_isPGroup ⟨k, hK⟩) (fun j x hx y hy hxy => ?_) (SL3.perfectCore_sup_eq_top hK4)
  have hz : x⁻¹ * y ∈ (LinearFlag.proj 3 K).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  have h1 := blk3_scalars j ⟨x⁻¹ * y, mul_mem (inv_mem hx) hy⟩
    (by rw [← ker_proj 3 K]; exact hz)
  exact inv_mul_eq_one.mp (congrArg Subtype.val h1)

theorem parConcl_specialLinear (hk : 2 ≤ k) (hK : Nat.card K = 2 ^ k) :
    ParConcl (SpecialLinearGroup (Fin 3) K) k
      ((unitriangular 3 K).map (MonoidHom.id (SpecialLinearGroup (Fin 3) K))) := by
  have hK4 := exists_finset_card_four_of_card hk hK
  exact parConcl_of_model hk hK (MonoidHom.id _) Function.surjective_id
    (B := upperTriangular 3 K)
    (linear_three_residual_of_cover ⟨k, hK⟩ (MonoidHom.id _) Function.surjective_id
      (by rw [MonoidHom.ker_id]; exact bot_le))
    (by rw [Subgroup.map_id, Subgroup.map_id]; exact normalizer_unitriangular)
    (by rw [MonoidHom.ker_id]; exact bot_le) covBy_Q3
    (fun j => SL3.unitriangular_le_perfectCore hK4 j) (fun j => blk3 j) (blk3_surjective hK4)
    (blk3_ker_isPGroup ⟨k, hK⟩) (fun _ _ _ _ _ hxy => hxy) (SL3.perfectCore_sup_eq_top hK4)

theorem parConcl_projSp (hk : 2 ≤ k) (hK : Nat.card K = 2 ^ k) :
    ParConcl (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 K)) k
      (projUnipotent 2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK4 := exists_finset_card_four_of_card hk hK
  have hker : (SymplecticFlag.proj 2 K).ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff _).mpr proj_injective_charTwo
  exact parConcl_of_model hk hK (SymplecticFlag.proj 2 K) (QuotientGroup.mk'_surjective _)
    (B := borelSubgroup 2 K) (symplectic_two_residualOvergroupsAt ⟨k, hK⟩)
    (normalizer_projUnipotent 2 (by norm_num)) (by rw [hker]; exact bot_le) covBy_Q2
    (fun j => Sp4.unipotent_le_perfectCore hK4 j) (fun j => blkN j) (blkN_surjective hK4)
    (blkN_ker_isPGroup ⟨k, hK⟩) (fun _ _ _ _ _ hxy => proj_injective_charTwo hxy)
    (Sp4.perfectCore_sup_eq_top ⟨k, hK⟩ hK4)

theorem factL2LieParabolic_holds : FactL2LieParabolic := by
  intro Y _ _ k hk h U hU
  rcases h with (hL | ⟨F, _, _, hcard, ⟨e⟩⟩) | hSp
  · obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ :=
      CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hL
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
    obtain ⟨Q, hQ⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
    have hU₀ : IsSylowTwoOf (projUnitriangular 3 K) ⊤ := hQ ▸ isSylowTwoOf_top_of_sylow Q
    exact parConcl_of_sylow (parConcl_projectiveSL hk hcard) hU₀
      (e.trans (statedSLEquivProjectiveSL 3 K)).symm hU
  · have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
    obtain ⟨Q, hQ⟩ := exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
    have hU₀ : IsSylowTwoOf ((unitriangular 3 F).map
        (MonoidHom.id (SpecialLinearGroup (Fin 3) F))) ⊤ := by
      rw [Subgroup.map_id]
      exact hQ ▸ isSylowTwoOf_top_of_sylow Q
    exact parConcl_of_sylow (parConcl_specialLinear hk hcard) hU₀ e.symm hU
  · obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ :=
      CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hSp
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
    obtain ⟨Q, hQ⟩ := exists_sylow_projUnipotent (K := K) 2 (r := 2) (by norm_num)
    have hU₀ : IsSylowTwoOf (projUnipotent 2 K) ⊤ := hQ ▸ isSylowTwoOf_top_of_sylow Q
    exact parConcl_of_sylow (parConcl_projSp hk hcard) hU₀ e.symm hU

end CFSG.Quasithin.H13.NQCat
