module

public import CFSG.LocalAnalysis.SteinbergCDEvenLinearThreeRadicals

public section

namespace CFSG.LocalAnalysis.SteinbergCD

open Matrix Module CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification

variable {K : Type*} [Field K]

theorem coordImage_finrank (σ : K ≃+* K) (W : Submodule K (Fin 3 → K)) :
    finrank K (coordImage σ W) = finrank K W := by
  let j : W ≃+ coordImage σ W :=
    { toFun := fun w => ⟨fun i => σ (w.1 i), coord_mem_coordImage w.2⟩
      invFun := fun v => ⟨fun i => σ.symm (v.1 i), v.2⟩
      left_inv := fun w => by ext i; simp
      right_inv := fun v => by ext i; simp
      map_add' := fun v w => by ext i; simp }
  have h := rank_eq_of_equiv_equiv (σ : K → K) j σ.bijective (fun r w => by ext i; simp [j])
  rw [finrank, finrank, h]

@[expose] noncomputable def graphSemilinearAut (h : GL (Fin 3) K) (σ : K ≃+* K) :
    MulAut (SpecialLinearGroup (Fin 3) K) :=
  CatalogueBHigherLinearAction.slConjugation 3 K h⁻¹ * CatalogueBGraphForm.slGraphAut 3 K *
    CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ

theorem descendAut_graphSemilinearAut (h : GL (Fin 3) K) (σ : K ≃+* K) :
    descendAut 3 K (graphSemilinearAut h σ) = conjAut 3 K h⁻¹ * dualAut 3 K * fieldAut 3 K σ := by
  rw [graphSemilinearAut, map_mul, map_mul]
  rfl

theorem slFieldAut_mem_radical (σ : K ≃+* K) {A : Submodule K (Fin 3 → K)}
    {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ radical A) :
    CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ g ∈ radical (coordImage σ A) := by
  set N := (g : Matrix (Fin 3) (Fin 3) K) - 1
  have hN : IsRadicalMatrix A N := hg
  have hmat : ((CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ g :
      SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) - 1 = N.map σ := by
    ext i j
    change σ ((g : Matrix (Fin 3) (Fin 3) K) i j) - (1 : Matrix (Fin 3) (Fin 3) K) i j =
      σ ((g : Matrix (Fin 3) (Fin 3) K) i j - (1 : Matrix (Fin 3) (Fin 3) K) i j)
    rw [map_sub, one_apply]
    split_ifs <;> simp
  have hkey : ∀ v, N.map σ *ᵥ v = fun i => σ ((N *ᵥ fun j => σ.symm (v j)) i) := by
    intro v
    funext i
    have h1 := RingHom.map_mulVec (σ : K →+* K) N (fun j => σ.symm (v j)) i
    simp only [RingEquiv.coe_toRingHom] at h1
    rw [h1]
    congr 2
    funext j
    simp
  rw [mem_radical, hmat]
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · rw [hkey, mem_coordImage]
    simpa using hN.1 _
  · rw [hkey, hN.2 _ (mem_coordImage.1 hv)]
    funext i
    simp

theorem slGraphAut_mem_radical {B : Submodule K (Fin 3 → K)} {g : SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ radical B) : CatalogueBGraphForm.slGraphAut 3 K g ∈ radical (dotOrth B) := by
  set N := (g : Matrix (Fin 3) (Fin 3) K) - 1
  have hN : IsRadicalMatrix B N := hg
  have hmat : ((CatalogueBGraphForm.slGraphAut 3 K g : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) - 1 = -Nᵀ := by
    rw [CatalogueBGraphForm.slGraphAut_matrix]
    have e : (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))ᵀ - 1 =
        (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) - 1)ᵀ := by
      rw [transpose_sub, transpose_one]
    rw [e, coe_inv_sub_one hN, transpose_neg]
  rw [mem_radical, hmat]
  refine IsRadicalMatrix.neg ⟨fun v => ?_, fun v hv => ?_⟩
  · rw [mem_dotOrth]
    intro w hw
    rw [mulVec_transpose, ← dotProduct_mulVec, hN.2 w hw, dotProduct_zero]
  · funext j
    rw [mulVec_transpose, Pi.zero_apply]
    have := (mem_dotOrth.1 hv) _ (hN.1 (Pi.single j 1))
    rwa [dotProduct_mulVec, dotProduct_single_one] at this

theorem slConjugation_mem_radical (P : GL (Fin 3) K) {C : Submodule K (Fin 3 → K)}
    {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ radical C) :
    CatalogueBHigherLinearAction.slConjugation 3 K P g ∈
      radical (C.map (mulVecLin (P : Matrix (Fin 3) (Fin 3) K))) := by
  rw [mem_radical, coe_slConjugation]
  have hPP : (P : Matrix (Fin 3) (Fin 3) K) * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e : (P : Matrix (Fin 3) (Fin 3) K) * g * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) -
      1 = (P : Matrix (Fin 3) (Fin 3) K) * ((g : Matrix (Fin 3) (Fin 3) K) - 1) *
        ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [mul_sub, sub_mul, mul_one, hPP]
  rw [e]
  exact (mem_radical.1 hg).conj (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])

theorem finrank_graphImage (h : GL (Fin 3) K) (σ : K ≃+* K) (A : Submodule K (Fin 3 → K)) :
    finrank K ((dotOrth (coordImage σ A)).map
      (mulVecLin ((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) = 3 - finrank K A := by
  have hinj : Function.Injective
      (mulVecLin ((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
    have hhh : (h : Matrix (Fin 3) (Fin 3) K) * ((h⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    intro v w hvw
    have := congrArg (mulVecLin (h : Matrix (Fin 3) (Fin 3) K)) hvw
    simp only [mulVecLin_apply, mulVec_mulVec, hhh, one_mulVec] at this
    exact this
  rw [← (Submodule.equivMapOfInjective _ hinj _).finrank_eq, finrank_dotOrth,
    coordImage_finrank]

theorem scalars_pow_three {z : SpecialLinearGroup (Fin 3) K} (hz : z ∈ scalars 3 K) :
    z ^ 3 = 1 := by
  obtain ⟨c, hc, hz⟩ := mem_scalars.1 hz
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, hz, Matrix.SpecialLinearGroup.coe_one, ← map_pow,
    ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one]

section Main

variable [CharP K 2] [Finite K]

theorem map_radical_graphSemilinearAut (h : GL (Fin 3) K) (σ : K ≃+* K)
    {A : Submodule K (Fin 3 → K)} (hA : finrank K A = 1 ∨ finrank K A = 2) :
    (radical A).map (graphSemilinearAut h σ).toMonoidHom =
      radical ((dotOrth (coordImage σ A)).map
        (mulVecLin ((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) := by
  have hle : (radical A).map (graphSemilinearAut h σ).toMonoidHom ≤
      radical ((dotOrth (coordImage σ A)).map
        (mulVecLin ((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) := by
    rintro _ ⟨x, hx, rfl⟩
    exact slConjugation_mem_radical h⁻¹ (slGraphAut_mem_radical (slFieldAut_mem_radical σ hx))
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (f := (graphSemilinearAut h σ).toMonoidHom)
    (graphSemilinearAut h σ).injective, card_radical hA,
    card_radical (by rw [finrank_graphImage]; omega)]

theorem map_graphSemilinearAut_ne (h : GL (Fin 3) K) (σ : K ≃+* K)
    {E : Subgroup (SpecialLinearGroup (Fin 3) K)} [IsElementaryAbelian 2 E]
    (hcard : Nat.card E = Nat.card K ^ 2) :
    E.map (graphSemilinearAut h σ).toMonoidHom ≠ E := by
  obtain ⟨A, hA, rfl⟩ := exists_eq_radical hcard
  rw [map_radical_graphSemilinearAut h σ hA]
  intro heq
  have hdim := finrank_graphImage h σ A
  have := eq_of_radical_eq (by omega) (by omega) heq
  rw [this] at hdim
  omega

omit [CharP K 2] in
theorem projective_elementary (Ebar : Subgroup (projectiveSL 3 K))
    [hE : IsElementaryAbelian 2 Ebar] :
    ∃ E : Subgroup (SpecialLinearGroup (Fin 3) K),
      (∀ S : Sylow 2 (Ebar.comap (proj 3 K)),
        (S : Subgroup (Ebar.comap (proj 3 K))).map (Ebar.comap (proj 3 K)).subtype = E) ∧
      E.map (proj 3 K) = Ebar ∧ (∀ x ∈ E, ∀ y ∈ E, proj 3 K x = proj 3 K y → x = y) ∧
      (∀ x ∈ Ebar.comap (proj 3 K), (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ E) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := Ebar.comap (proj 3 K)
  let f : P →* Ebar := ((proj 3 K).comp P.subtype).codRestrict Ebar fun x => x.2
  have hf : Function.Surjective f := fun a => by
    obtain ⟨s, hs⟩ := proj_surjective 3 K (a : projectiveSL 3 K)
    refine ⟨⟨s, ?_⟩, Subtype.ext hs⟩
    change proj 3 K s ∈ Ebar
    rw [hs]
    exact a.2
  obtain ⟨S₀⟩ : Nonempty (Sylow 2 P) := inferInstance
  set E := (S₀ : Subgroup P).map P.subtype with hEdef
  have hE2 : IsPGroup 2 E := S₀.isPGroup'.map _
  have hZ2 : ∀ z ∈ scalars 3 K, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1 := fun z hz k hk => by
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk)
      (orderOf_dvd_of_pow_eq_one (scalars_pow_three hz)))
  have hinjE : ∀ x ∈ E, ∀ y ∈ E, proj 3 K x = proj 3 K y → x = y := by
    intro x hx y hy hxy
    have hm : x⁻¹ * y ∈ E := E.mul_mem (E.inv_mem hx) hy
    obtain ⟨k, hk⟩ := hE2 ⟨_, hm⟩
    have hk' : (x⁻¹ * y) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact inv_mul_eq_one.1 (hZ2 _ (proj_eq_proj_iff.1 hxy) k hk')
  have hA2 : IsPGroup 2 Ebar := IsElementaryAbelian.isPGroup 2 Ebar
  have hEmap : E.map (proj 3 K) = Ebar := by
    have hQ := (S₀.mapSurjective hf).card_eq_multiplicity
    rw [Sylow.coe_mapSurjective] at hQ
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hA2
    have htop : (S₀ : Subgroup P).map f = ⊤ := by
      refine Subgroup.eq_top_of_card_eq _ ?_
      rw [hQ, hn, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
        Nat.Prime.factorization_self Nat.prime_two, mul_one]
    apply le_antisymm
    · rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
      exact x.2
    · intro y hy
      have hy' : (⟨y, hy⟩ : Ebar) ∈ (S₀ : Subgroup P).map f := htop ▸ Subgroup.mem_top _
      obtain ⟨x, hx, hxy⟩ := hy'
      exact ⟨x, ⟨x, hx, rfl⟩, congrArg Subtype.val hxy⟩
  have h2el : ∀ x ∈ P, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ E := by
    rintro x hx ⟨k, hk⟩
    have hxE : proj 3 K x ∈ E.map (proj 3 K) := by
      rw [hEmap]
      exact hx
    obtain ⟨e, he, hex⟩ := hxE
    have hz : e⁻¹ * x ∈ scalars 3 K := proj_eq_proj_iff.1 hex
    have hzc : e⁻¹ * x ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
      rw [← scalars_eq_center]
      exact hz
    obtain ⟨m, hm⟩ := hE2 ⟨e, he⟩
    have hm' : e ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hcomm : Commute e⁻¹ x := by
      have h1 := Subgroup.mem_center_iff.1 hzc e
      calc e⁻¹ * x = e⁻¹ * x * e * e⁻¹ := by group
        _ = e * (e⁻¹ * x) * e⁻¹ := by rw [← h1]
        _ = x * e⁻¹ := by group
    have h1 : e⁻¹ ^ 2 ^ (k + m) = 1 := by
      rw [inv_pow, pow_add, pow_mul', hm', one_pow, inv_one]
    have h2 : x ^ 2 ^ (k + m) = 1 := by rw [pow_add, pow_mul, hk, one_pow]
    have h3 : (e⁻¹ * x) ^ 2 ^ (k + m) = 1 := by rw [hcomm.mul_pow, h1, h2, one_mul]
    have h4 := inv_mul_eq_one.1 (hZ2 _ hz _ h3)
    rw [← h4]
    exact he
  refine ⟨E, fun S => ?_, hEmap, hinjE, h2el⟩
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨x, hx⟩
    exact h2el _ x.2 ⟨k, by simpa using congrArg (fun y : (S : Subgroup P) => ((y : P) :
      SpecialLinearGroup (Fin 3) K)) hk⟩
  · rw [hEdef, Subgroup.card_map_of_injective P.subtype_injective,
      Subgroup.card_map_of_injective P.subtype_injective, S.card_eq_multiplicity,
      S₀.card_eq_multiplicity]

omit [CharP K 2] [Finite K] in
theorem isElementaryAbelian_of_injOn (Ebar : Subgroup (projectiveSL 3 K))
    [hE : IsElementaryAbelian 2 Ebar] {E : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hEmap : E.map (proj 3 K) = Ebar)
    (hinj : ∀ x ∈ E, ∀ y ∈ E, proj 3 K x = proj 3 K y → x = y) :
    IsElementaryAbelian 2 E ∧ Nat.card E = Nat.card Ebar := by
  have hmem : ∀ x ∈ E, proj 3 K x ∈ Ebar := fun x hx => hEmap ▸ ⟨x, hx, rfl⟩
  have hcomm : ∀ x y : E, x * y = y * x := fun x y => by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    refine hinj _ (E.mul_mem x.2 y.2) _ (E.mul_mem y.2 x.2) ?_
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hE.is_comm.comm ⟨_, hmem _ x.2⟩ ⟨_, hmem _ y.2⟩)
  have hexp : ∀ x : E, x ^ 2 = 1 := fun x => by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    refine hinj _ (E.pow_mem x.2 2) _ E.one_mem ?_
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := Ebar) _ (hmem _ x.2)
  refine ⟨{ is_comm := ⟨hcomm⟩, exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hexp },
    ?_⟩
  rw [← hEmap]
  refine Nat.card_congr (Equiv.ofBijective ((proj 3 K).subgroupMap E) ⟨fun x y hxy => ?_,
    (proj 3 K).subgroupMap_surjective E⟩)
  exact Subtype.ext (hinj _ x.2 _ y.2 (congrArg Subtype.val hxy))

theorem map_descendAut_ne (h : GL (Fin 3) K) (σ : K ≃+* K) (Ebar : Subgroup (projectiveSL 3 K))
    [IsElementaryAbelian 2 Ebar] (hcard : Nat.card Ebar = Nat.card K ^ 2) :
    Ebar.map (descendAut 3 K (graphSemilinearAut h σ)).toMonoidHom ≠ Ebar := by
  intro heq
  obtain ⟨E, -, hEmap, hinj, h2el⟩ := projective_elementary Ebar
  obtain ⟨hEel, hEcard⟩ := isElementaryAbelian_of_injOn Ebar hEmap hinj
  have hE2 : IsPGroup 2 E := IsElementaryAbelian.isPGroup 2 E
  have hle : E.map (graphSemilinearAut h σ).toMonoidHom ≤ E := by
    rintro _ ⟨e, he, rfl⟩
    refine h2el _ ?_ ?_
    · change proj 3 K (graphSemilinearAut h σ e) ∈ Ebar
      rw [← descendAut_proj, ← heq]
      exact ⟨_, hEmap ▸ ⟨e, he, rfl⟩, rfl⟩
    · obtain ⟨k, hk⟩ := hE2 ⟨e, he⟩
      refine ⟨k, ?_⟩
      have hk' : e ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [MulEquiv.coe_toMonoidHom, ← map_pow, hk', map_one]
  exact map_graphSemilinearAut_ne h σ (hEcard.trans hcard)
    (Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (f := (graphSemilinearAut h σ).toMonoidHom)
        (graphSemilinearAut h σ).injective]))

end Main

end CFSG.LocalAnalysis.SteinbergCD
