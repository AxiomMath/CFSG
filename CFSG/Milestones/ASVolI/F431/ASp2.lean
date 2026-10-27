module

public import CFSG.Milestones.ASVolI.F4TISets

public section

namespace CFSG.ASVolI

section Mat

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.ASVolI.ChF

variable {K : Type} [Field K]

theorem burnsideF4m_isUnitriangular_N :
    IsUnitriangular (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all
  · fin_cases i <;> rfl

theorem burnsideF4m_ctr_unipotent [CharP K 2] {y : StatedSp 2 K} (hy : y ∈ ctr (unipotent 2 K)) :
    ∃ s t : K, y = burnsideF4gSpInv_xl s * burnsideF4gSpInv_xs t := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨hyU, hyC⟩ := hy
  obtain ⟨A, C, hA, hC, hyM⟩ := mem_unipotent.1 hyU
  have hc := Subgroup.mem_centralizer_iff.1 hyC
  obtain ⟨a, hAa, hAi⟩ := burnsideF4gSpInv_unitriangular_two hA
  obtain ⟨u1, hu1, hu1M⟩ := exists_mem_unipotent (r := 2) (K := K) (A := 1)
    (C := Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : K)) isUnitriangular_one (by simp)
  have e1 := congrArg (fun g : StatedSp 2 K =>
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) (hc u1 hu1)
  simp only [Subgroup.coe_mul, Units.val_mul, hyM, hu1M] at e1
  rw [blockMat, blockMat, fromBlocks_multiply, fromBlocks_multiply] at e1
  have e1b := (fromBlocks_inj.1 e1).2.1
  have ha : a = 0 := by
    have h := congrFun (congrFun e1b 0) 1
    rw [hAi, hAa] at h
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.vecMul,
      dotProduct] at h
    linear_combination h
  rw [ha] at hAa
  have hA1 : A = 1 := by
    rw [hAa]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  subst hA1
  obtain ⟨b, hNb, hNi⟩ := burnsideF4gSpInv_unitriangular_two
    (burnsideF4m_isUnitriangular_N (K := K))
  obtain ⟨u2, hu2, hu2M⟩ := exists_mem_unipotent (r := 2) (K := K)
    (A := !![1, 1; 0, 1]) (C := 0) burnsideF4m_isUnitriangular_N transpose_zero
  have e2 := congrArg (fun g : StatedSp 2 K =>
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) (hc u2 hu2)
  simp only [Subgroup.coe_mul, Units.val_mul, hyM, hu2M] at e2
  rw [blockMat, blockMat, fromBlocks_multiply, fromBlocks_multiply] at e2
  have e2b := (fromBlocks_inj.1 e2).2.1
  have hb1 : b = 1 := by
    have h := congrFun (congrFun hNb 0) 1
    simpa using h.symm
  have hC11 : C 1 1 = 0 := by
    have h := congrFun (congrFun e2b 0) 1
    rw [hNi, hb1] at h
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at h
    linear_combination h
  have hC10 : C 1 0 = C 0 1 := by
    have := congrFun (congrFun hC 0) 1
    simpa using this
  refine ⟨C 0 0, C 0 1, Subtype.ext (Units.ext ?_)⟩
  rw [hyM, Subgroup.coe_mul, Units.val_mul, burnsideF4gSpInv_xl_val, burnsideF4gSpInv_xs_val,
    blockMat, fromBlocks_multiply]
  simp only [inv_one, transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply, hC10, hC11]

theorem burnsideF4m_centralizer_mixed_le_Q0 [CharP K 2] :
    Subgroup.centralizer ({burnsideF4gSpInv_xl (1 : K) * burnsideF4gSpInv_xs 1} :
      Set (StatedSp 2 K)) ≤ Q2 K 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set m : StatedSp 2 K := burnsideF4gSpInv_xl (1 : K) * burnsideF4gSpInv_xs 1 with hm
  have key : ∀ g : StatedSp 2 K, g * m = m * g →
      ∃ c : K, burnsideF4gSpInv_mv g (Pi.single (Sum.inl 0) 1) =
        c • (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) := by
    intro g hg
    have hmf : burnsideF4gSpInv_mv m (Pi.single (Sum.inr 1) 1) =
        Pi.single (Sum.inr 1) 1 + Pi.single (Sum.inl 0) 1 := by
      rw [hm, burnsideF4gSpInv_mixed_mv]
      ext i
      rcases i with i | i <;> fin_cases i <;> simp [Pi.single_apply]
    obtain ⟨w, hw⟩ : ∃ w, w = burnsideF4gSpInv_mv g (Pi.single (Sum.inr 1) 1) := ⟨_, rfl⟩
    have hmw : burnsideF4gSpInv_mv m w =
        w + burnsideF4gSpInv_mv g (Pi.single (Sum.inl 0) 1) := by
      rw [hw, ← burnsideF4gSpInv_mv_mul, ← hg, burnsideF4gSpInv_mv_mul, hmf,
        burnsideF4gSpInv_mv_add]
    have hform : burnsideF4gSpInv_form w (burnsideF4gSpInv_mv m w) = 0 := by
      have e : burnsideF4gSpInv_mv m w =
          burnsideF4gSpInv_mv g (burnsideF4gSpInv_mv m (Pi.single (Sum.inr 1) 1)) := by
        rw [hw, ← burnsideF4gSpInv_mv_mul, ← burnsideF4gSpInv_mv_mul, hg]
      rw [e, hw, burnsideF4gSpInv_form_mv, hmf]
      simp [burnsideF4gSpInv_form, Pi.single_apply]
    rw [hm, burnsideF4gSpInv_mixed_mv] at hform
    simp only [burnsideF4gSpInv_form, Pi.add_apply, Pi.smul_apply, Pi.single_apply,
      smul_eq_mul] at hform
    simp at hform
    have hsq : w (Sum.inr 0) ^ 2 = 0 := by
      linear_combination -hform - (w (Sum.inr 0) * w (Sum.inr 1)) * h2
    have hw0 : w (Sum.inr 0) = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 hsq
    refine ⟨w (Sum.inr 1), ?_⟩
    have hge : burnsideF4gSpInv_mv g (Pi.single (Sum.inl 0) 1) =
        burnsideF4gSpInv_mv m w - w := by
      rw [hmw]
      abel
    rw [hge, hm, burnsideF4gSpInv_mixed_mv]
    ext i
    rcases i with i | i <;> fin_cases i <;> simp [Pi.single_apply, hw0]
  have hfwd : ∀ g' : StatedSp 2 K, g' * m = m * g' →
      ∀ v, v ∈ flag 2 K 1 → burnsideF4gSpInv_mv g' v ∈ flag 2 K 1 := by
    intro g' hg' v hv
    obtain ⟨c, rfl⟩ := (burnsideF4gSpInv_mem_flag_one_iff v).1 hv
    obtain ⟨d, hd⟩ := key g' hg'
    rw [burnsideF4gSpInv_mem_flag_one_iff]
    exact ⟨c * d, by rw [burnsideF4gSpInv_mv_smul, hd, smul_smul]⟩
  intro g hg
  have hg' := Subgroup.mem_centralizer_singleton_iff.1 hg
  have hginv := Subgroup.mem_centralizer_singleton_iff.1
    ((Subgroup.centralizer ({m} : Set (StatedSp 2 K))).inv_mem hg)
  rw [burnsideF4gSpInv_mem_Q2_zero]
  intro v
  constructor
  · intro h
    have := hfwd g⁻¹ hginv _ h
    rwa [burnsideF4gSpInv_mv_mv_inv] at this
  · exact hfwd g hg' v

end Mat

section AntiSp

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b CFSG.RankThree.PartOne.KCRootAxis
  CFSG.QuasithinUnique.Borel252 CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.SpModel

theorem burnsideF4m_shape_antiSp_one {F : Type} [Field F] [Finite F] [CharP F 2]
    (hB : BorelData (antiSp F) (antiUnipotent F) (radA1 F) (radA2 F)) :
    SpShape (antiUnipotent F) (Rrad F) where
  Q_le j := by
    fin_cases j
    · exact radA1_le_antiUnipotent
    · exact radA2_le_antiUnipotent
  Q_norm j := by
    fin_cases j
    · exact Subgroup.le_normalizer.trans hB.lt₁.le
    · exact Subgroup.le_normalizer.trans hB.lt₂.le
  Q_abel j := by
    fin_cases j
    · exact fun x hx y hy => radA1_comm hx hy
    · exact fun x hx y hy => radA2_comm hx hy
  Z_le j := by
    intro x hx
    rw [centerOf_antiUnipotent] at hx
    fin_cases j
    · exact antiUnipotentCenter_le_radA1 hx
    · exact antiUnipotentCenter_le_radA2 hx
  Z_sq := by
    intro z hz
    rw [centerOf_antiUnipotent] at hz
    rw [sq]
    exact mul_self_of_mem_radA1 (antiUnipotentCenter_le_radA1 hz)
  inv_mem := by
    intro x hx hx2
    rw [sq] at hx2
    rcases (mul_self_eq_one_iff hx).mp hx2 with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  cen := by
    intro j x hx hxZ y hy hxy
    rw [centerOf_antiUnipotent] at hxZ
    fin_cases j
    · obtain ⟨b, c, d, rfl⟩ := hx
      have hd : d ≠ 0 := by
        rintro rfl
        exact hxZ ⟨b, c, rfl⟩
      exact mem_radA1_of_commute_uElt hy hd hxy
    · obtain ⟨a, b, c, rfl⟩ := hx
      have ha : a ≠ 0 := by
        rintro rfl
        exact hxZ ⟨b, c, rfl⟩
      exact mem_radA2_of_commute_uElt hy ha hxy
  ex := by
    intro j
    fin_cases j
    · refine ⟨uElt 0 0 0 1, ⟨0, 0, 1, rfl⟩, ?_, by
        rw [sq]
        exact mul_self_of_mem_radA1 ⟨0, 0, 1, rfl⟩⟩
      rw [centerOf_antiUnipotent]
      rintro ⟨b, c, h⟩
      exact one_ne_zero (uElt_inj h).2.2.2
    · refine ⟨uElt 1 0 0 0, ⟨1, 0, 0, rfl⟩, ?_, by
        rw [sq]
        exact mul_self_of_mem_radA2 ⟨1, 0, 0, rfl⟩⟩
      rw [centerOf_antiUnipotent]
      rintro ⟨b, c, h⟩
      exact one_ne_zero (uElt_inj h).1

end AntiSp

section ShapeMap

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431 CFSG.ASVolI.ChF

theorem burnsideF4m_spShape_map {D G : Type} [Group D] [Group G] (Φ : D ≃* G)
    {T : Subgroup D} {Q : Fin 2 → Subgroup D} (hS : SpShape T Q) :
    SpShape (T.map Φ.toMonoidHom) (fun j => (Q j).map Φ.toMonoidHom) := by
  have hZ : centerOf (T.map Φ.toMonoidHom) = (centerOf T).map Φ.toMonoidHom :=
    burnsideF4j_ctr_map Φ.toMonoidHom Φ.injective T
  have hmem : ∀ (X : Subgroup D) (x : D), Φ x ∈ X.map Φ.toMonoidHom ↔ x ∈ X :=
    fun X x => Subgroup.mem_map_iff_mem Φ.injective
  refine ⟨fun j => Subgroup.map_mono (hS.Q_le j), fun j => ?_, fun j => ?_, fun j => ?_, ?_, ?_,
    fun j => ?_, fun j => ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    obtain ⟨y, rfl⟩ := Φ.surjective x
    have h1 := (Subgroup.mem_normalizer_iff.mp (hS.Q_norm j ht)) y
    have e : Φ.toMonoidHom t * Φ y * (Φ.toMonoidHom t)⁻¹ = Φ (t * y * t⁻¹) := by
      simp [map_mul, map_inv]
    rw [e, hmem, hmem]
    exact h1
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hS.Q_abel j x hx y hy]
  · rw [hZ]
    exact Subgroup.map_mono (hS.Z_le j)
  · intro z hz
    rw [hZ] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_pow, hS.Z_sq z' hz', map_one]
  · rintro _ ⟨x, hx, rfl⟩ hx2
    have hx2' : x ^ 2 = 1 := Φ.injective (by simpa [map_pow] using hx2)
    obtain ⟨j, hj⟩ := hS.inv_mem x hx hx2'
    exact ⟨j, ⟨x, hj, rfl⟩⟩
  · rintro _ ⟨x, hx, rfl⟩ hxZ _ ⟨y, hy, rfl⟩ hcomm
    have hx' : x ∉ centerOf T := fun h => hxZ (by rw [hZ]; exact ⟨x, h, rfl⟩)
    have hcomm' : y * x = x * y := Φ.injective (by simpa [map_mul] using hcomm)
    exact ⟨y, hS.cen j x hx hx' y hy hcomm', rfl⟩
  · obtain ⟨x, hxQ, hxZ, hx2⟩ := hS.ex j
    refine ⟨Φ x, ⟨x, hxQ, rfl⟩, fun h => hxZ ?_, by rw [← map_pow, hx2, map_one]⟩
    rw [hZ] at h
    exact (hmem _ x).mp h

end ShapeMap

end CFSG.ASVolI
