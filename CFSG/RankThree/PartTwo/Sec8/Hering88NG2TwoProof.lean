module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofG2
public import CFSG.RankThree.PartTwo.Sec8.Hering88NG2TwoCayley
public import CFSG.Quasithin.Background.SmithB42G2Id
import CFSG.Quasithin.Background.FFC2G2
import CFSG.LieType.Chevalley.NoncentralNormalSolvable
import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88N.G2Two

open Matrix CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Open
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2Id
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof CFSG.LieType.HighestRoot

section Field

variable {F F' : Type} [Field F] [Field F'] (e : F ≃+* F')

theorem zornConj_g2A (A : SL3 F) :
    zornConj e ((g2A A : ↥(cayleyGroup F)) : quasithinZorn F ≃ₗ[F] quasithinZorn F) =
      ((g2A (Matrix.SpecialLinearGroup.map e.toRingHom A) : ↥(cayleyGroup F')) :
        quasithinZorn F' ≃ₗ[F'] quasithinZorn F') := by
  refine LinearEquiv.ext fun y => ?_
  rw [zornConj_apply, g2A_apply, g2A_apply]
  change zornMap e (gAFun (A : Matrix (Fin 3) (Fin 3) F) (zornMap e.symm y)) =
    gAFun ((A : Matrix (Fin 3) (Fin 3) F).map e) y
  have hadj : ((adjugate (A : Matrix (Fin 3) (Fin 3) F))ᵀ).map e =
      (adjugate ((A : Matrix (Fin 3) (Fin 3) F).map e))ᵀ := by
    rw [Matrix.transpose_map]
    congr 1
    exact RingHom.map_adjugate e.toRingHom (A : Matrix (Fin 3) (Fin 3) F)
  have hu : (⇑e ∘ fun j => e.symm (y.2.1 j)) = y.2.1 := funext fun j => by simp
  have hv : (⇑e ∘ fun j => e.symm (y.2.2.1 j)) = y.2.2.1 := funext fun j => by simp
  simp only [gAFun, zornMap, RingEquiv.apply_symm_apply, Prod.mk.injEq, true_and, and_true]
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · have h : e (((A : Matrix (Fin 3) (Fin 3) F) *ᵥ fun j => e.symm (y.2.1 j)) i) =
        (((A : Matrix (Fin 3) (Fin 3) F).map e) *ᵥ (⇑e ∘ fun j => e.symm (y.2.1 j))) i :=
      RingHom.map_mulVec e.toRingHom (A : Matrix (Fin 3) (Fin 3) F) (fun j => e.symm (y.2.1 j)) i
    rw [h, hu]
  · have h : e (((adjugate (A : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ fun j => e.symm (y.2.2.1 j)) i) =
        ((((adjugate (A : Matrix (Fin 3) (Fin 3) F))ᵀ).map e) *ᵥ
          (⇑e ∘ fun j => e.symm (y.2.2.1 j))) i :=
      RingHom.map_mulVec e.toRingHom (adjugate (A : Matrix (Fin 3) (Fin 3) F))ᵀ
        (fun j => e.symm (y.2.2.1 j)) i
    rw [h, hadj, hv]

variable [CharP F 2] [CharP F' 2]

theorem zornConj_g2X (a : Fin 3 → F) :
    zornConj e ((g2X a : ↥(cayleyGroup F)) : quasithinZorn F ≃ₗ[F] quasithinZorn F) =
      ((g2X (fun i => e (a i)) : ↥(cayleyGroup F')) :
        quasithinZorn F' ≃ₗ[F'] quasithinZorn F') := by
  refine LinearEquiv.ext fun y => ?_
  rw [zornConj_apply, g2X_apply, g2X_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  all_goals first
    | (simp [xaFun, zmk, zornMap]; done)
    | (funext i; fin_cases i <;> simp [xaFun, zmk, zornMap])

theorem zornConj_g2Y (b : Fin 3 → F) :
    zornConj e ((g2Y b : ↥(cayleyGroup F)) : quasithinZorn F ≃ₗ[F] quasithinZorn F) =
      ((g2Y (fun i => e (b i)) : ↥(cayleyGroup F')) :
        quasithinZorn F' ≃ₗ[F'] quasithinZorn F') := by
  refine LinearEquiv.ext fun y => ?_
  rw [zornConj_apply, g2Y_apply, g2Y_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  all_goals first
    | (simp [ybFun, zmk, zornMap]; done)
    | (funext i; fin_cases i <;> simp [ybFun, zmk, zornMap])

end Field

section Words

theorem gens8_zero : gens8 0 = g2X ![1, 0, 0] := rfl

theorem gens8_one : gens8 1 = g2Y ![0, 1, 0] := rfl

theorem gens8_three : gens8 3 = g2A (tv 0 2 (by decide) (1 : ZMod 2)) := rfl

theorem gens8_five : gens8 5 = g2A (tv 1 2 (by decide) (1 : ZMod 2)) := rfl

theorem gens8_six : gens8 6 = g2A (tv 2 0 (by decide) (1 : ZMod 2)) := rfl

theorem gens8_seven : gens8 7 = g2A (tv 2 1 (by decide) (1 : ZMod 2)) := rfl

theorem g2A_tv_inv (i j : Fin 3) (hij : i ≠ j) :
    (g2A (tv i j hij (1 : ZMod 2)))⁻¹ = g2A (tv i j hij 1) := by
  rw [← map_inv]
  congr 1
  exact inv_eq_of_mul_eq_one_right (tv_mul_self i j hij 1)

theorem g2X_e2_eq : (g2X ![0, 0, 1] : ↥(cayleyGroup (ZMod 2))) = sB := by
  have h1 : g2A (tv 2 0 (by decide) (1 : ZMod 2)) * g2X ![1, 0, 0] =
      g2X ![1, 0, 1] * g2A (tv 2 0 (by decide) (1 : ZMod 2)) := by
    rw [g2A_mul_g2X]
    congr 2
    decide
  have h2 : g2A (tv 0 2 (by decide) (1 : ZMod 2)) * g2X ![1, 0, 1] =
      g2X ![0, 0, 1] * g2A (tv 0 2 (by decide) (1 : ZMod 2)) := by
    rw [g2A_mul_g2X]
    congr 2
    decide
  have e1 := eq_mul_inv_of_mul_eq h1.symm
  have e2 := eq_mul_inv_of_mul_eq h2.symm
  rw [g2A_tv_inv] at e1 e2
  rw [e2, e1, sB]
  simp only [wordEval, gens8_zero, gens8_three, gens8_six, mul_one, mul_assoc]

theorem g2Y_e2_eq : (g2Y ![0, 0, 1] : ↥(cayleyGroup (ZMod 2))) = sA := by
  have h1 : g2A (tv 1 2 (by decide) (1 : ZMod 2)) * g2Y ![0, 1, 0] =
      g2Y ![0, 1, 1] * g2A (tv 1 2 (by decide) (1 : ZMod 2)) := by
    rw [g2A_mul_g2Y]
    congr 2
    rw [show ((tv 1 2 (by decide) (1 : ZMod 2) : SL3 (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      Matrix.transvection 1 2 1 from rfl, adj_transvection_two (by decide : (1 : Fin 3) ≠ 2)]
    decide
  have h2 : g2A (tv 2 1 (by decide) (1 : ZMod 2)) * g2Y ![0, 1, 1] =
      g2Y ![0, 0, 1] * g2A (tv 2 1 (by decide) (1 : ZMod 2)) := by
    rw [g2A_mul_g2Y]
    congr 2
    rw [show ((tv 2 1 (by decide) (1 : ZMod 2) : SL3 (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      Matrix.transvection 2 1 1 from rfl, adj_transvection_two (by decide : (2 : Fin 3) ≠ 1)]
    decide
  have e1 := eq_mul_inv_of_mul_eq h1.symm
  have e2 := eq_mul_inv_of_mul_eq h2.symm
  rw [g2A_tv_inv] at e1 e2
  rw [e2, e1, sA]
  simp only [wordEval, gens8_one, gens8_five, gens8_seven, mul_one, mul_assoc]

end Words

theorem eq_zero_or_one_of_card_two {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2)
    (c : k) : c = 0 ∨ c = 1 := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have hF : Fintype.card k = 2 := by rw [← Nat.card_eq_fintype_card, hk]
  let ε : k ≃+* ZMod 2 := (ZMod.ringEquivOfPrime k Nat.prime_two hF).symm
  have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h2 (ε c) with h | h
  · exact Or.inl (ε.injective (by rw [h, map_zero]))
  · exact Or.inr (ε.injective (by rw [h, map_one]))

theorem g2e0_eq_hexRoot : (g2e0 : Fin 2 → ℤ) = CFSG.Timmesfeld.RankTwo.hexRoot 5 := by
  funext j
  fin_cases j <;> decide

theorem g2δ_eq_hexRoot : (g2δ : Fin 2 → ℤ) = CFSG.Timmesfeld.RankTwo.hexRoot 2 := by
  funext j
  fin_cases j <;> decide

theorem zPsi_neg_g2e0 {F : Type} [Field F] [CharP F 2] (c : F) :
    zPsi ((-g2e0 : Fin Tag.G2.rank → ℤ)) c = zNeg 5 c := by
  have h : ((-g2e0 : Fin Tag.G2.rank → ℤ)) = -CFSG.Timmesfeld.RankTwo.hexRoot 5 := by
    funext j
    fin_cases j <;> decide
  rw [h]
  exact zPsi_neg 5 c

theorem zPsi_neg_g2δ {F : Type} [Field F] [CharP F 2] (c : F) :
    zPsi ((-g2δ : Fin Tag.G2.rank → ℤ)) c = zNeg 2 c := by
  have h : ((-g2δ : Fin Tag.G2.rank → ℤ)) = -CFSG.Timmesfeld.RankTwo.hexRoot 2 := by
    funext j
    fin_cases j <;> decide
  rw [h]
  exact zPsi_neg 2 c

section Iso

theorem injective_of_surjective_cayley {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2)
    (ψ : adjointGroup .G2 k →* ↥(cayleyGroup k)) (hsurj : Function.Surjective ψ) :
    Function.Injective ψ := by
  have : CharP k 2 := charP_two_of_card (f := 1) (by rw [hk, pow_one])
  have hQC := CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup (K := k)
  obtain ⟨hs, ⟨a, b, hab⟩, -⟩ := CFSG.Quasithin.FFC.commutator_data_g2 hk
    (MulEquiv.refl ↥(CFSG.Open.quasithinG2 k))
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hne
  have hnc : ¬ ψ.ker ≤ Subgroup.center (adjointGroup .G2 k) := by
    rw [center_adjointGroup_eq_bot_field, le_bot_iff]
    exact hne
  have hsol := (noncentral_normal_solvable_quotient .G2 k ψ.ker hnc).2.1
  have hC : Group.IsSolvable ↥(cayleyGroup k) :=
    Group.isSolvable_of_surjective
      (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).surjective
  have hC' : Group.IsSolvable ↥(CFSG.Open.quasithinG2 k) := by
    rw [hQC]
    exact hC
  have hle : ⁅CFSG.Open.quasithinG2 k, CFSG.Open.quasithinG2 k⁆ ≤ CFSG.Open.quasithinG2 k := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  have hD : Group.IsSolvable ↥⁅CFSG.Open.quasithinG2 k, CFSG.Open.quasithinG2 k⁆ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hD) a b)

theorem exists_mulEquiv_cayley_two {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2) :
    ∃ φ : adjointGroup .G2 k ≃* ↥(cayleyGroup (ZMod 2)),
      φ (xPar (rootOperatorFamily .G2) g2e0 1) = mA ∧
      φ (xPar (rootOperatorFamily .G2) (-g2e0) 1) = mB ∧
      φ (xPar (rootOperatorFamily .G2) g2δ 1) = sA ∧
      φ (xPar (rootOperatorFamily .G2) (-g2δ) 1) = sB := by
  classical
  have : CharP k 2 := charP_two_of_card (f := 1) (by rw [hk, pow_one])
  have : Fintype k := Fintype.ofFinite k
  have hF : Fintype.card k = 2 := by rw [← Nat.card_eq_fintype_card, hk]
  let ε : k ≃+* ZMod 2 := (ZMod.ringEquivOfPrime k Nat.prime_two hF).symm
  obtain ⟨ψ, hψ, hsurj⟩ := exists_surjective_adjointGroup_hom_cayleyGroup (F := k)
  let Ψ : adjointGroup .G2 k ≃* ↥(cayleyGroup k) :=
    MulEquiv.ofBijective ψ ⟨injective_of_surjective_cayley hk ψ hsurj, hsurj⟩
  let Θ : ↥(cayleyGroup k) ≃* ↥(cayleyGroup (ZMod 2)) :=
    ((zornConj ε).subgroupMap _).trans (MulEquiv.subgroupCongr (map_cayleyGroup ε))
  have hΘ : ∀ g : ↥(cayleyGroup k), ((Θ g : ↥(cayleyGroup (ZMod 2))) :
      quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) =
      zornConj ε (g : quasithinZorn k ≃ₗ[k] quasithinZorn k) := fun _ => rfl
  have hε1 : ε 1 = 1 := map_one ε
  have htv : ∀ (i j : Fin 3) (hij : i ≠ j),
      Matrix.SpecialLinearGroup.map ε.toRingHom (tv i j hij (1 : k)) = tv i j hij 1 := by
    intro i j hij
    apply Subtype.ext
    change (Matrix.transvection i j (1 : k)).map ε = Matrix.transvection i j 1
    ext a b
    simp only [Matrix.map_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply]
    split_ifs <;> simp
  have hvec : (fun i => ε ((![0, 0, 1] : Fin 3 → k) i)) = ![0, 0, 1] := by
    funext i
    fin_cases i <;> simp
  refine ⟨Ψ.trans Θ, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    change ((Θ (ψ (xPar (rootOperatorFamily .G2) g2e0 1)) : ↥(cayleyGroup (ZMod 2))) :
      quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) = _
    rw [hψ _ (isRoot_single .G2 g2l), hΘ,
      show zPsi (g2e0 : Fin 2 → ℤ) (1 : k) = zPos 5 1 by rw [g2e0_eq_hexRoot, zPsi_pos]]
    rw [show zPos 5 (1 : k) = g2A (tv 1 0 (by decide) 1) from rfl, zornConj_g2A, htv]
    rfl
  · apply Subtype.ext
    change ((Θ (ψ (xPar (rootOperatorFamily .G2) (-g2e0) 1)) : ↥(cayleyGroup (ZMod 2))) :
      quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) = _
    rw [hψ _ (isRoot_neg_single .G2 g2l), hΘ, zPsi_neg_g2e0]
    rw [show zNeg 5 (1 : k) = g2A (tv 0 1 (by decide) 1) from rfl, zornConj_g2A, htv]
    rfl
  · apply Subtype.ext
    change ((Θ (ψ (xPar (rootOperatorFamily .G2) g2δ 1)) : ↥(cayleyGroup (ZMod 2))) :
      quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) = _
    rw [hψ _ isRoot_g2δ, hΘ,
      show zPsi (g2δ : Fin 2 → ℤ) (1 : k) = zPos 2 1 by rw [g2δ_eq_hexRoot, zPsi_pos]]
    rw [show zPos 2 (1 : k) = g2Y ![0, 0, 1] from rfl, zornConj_g2Y, hvec, g2Y_e2_eq]
  · apply Subtype.ext
    change ((Θ (ψ (xPar (rootOperatorFamily .G2) (-g2δ) 1)) : ↥(cayleyGroup (ZMod 2))) :
      quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) = _
    rw [hψ _ (CFSG.LieType.Chevalley.IsRoot.neg isRoot_g2δ), hΘ, zPsi_neg_g2δ]
    rw [show zNeg 2 (1 : k) = g2X ![0, 0, 1] from rfl, zornConj_g2X, hvec, g2X_e2_eq]

end Iso

section RootSL2

theorem subgroupOf_rootSubgroup_G2 {K : Type} [Field K] {γ : Fin Tag.G2.rank → ℤ}
    (hγ : IsRoot .G2 γ) :
    (rootSubgroup .G2 K γ).subgroupOf (adjointGroup .G2 K) =
      rootGroup (rootOperatorFamily .G2) K γ := by
  rw [rootGroup_of_isRoot hγ]
  exact (rootOperatorFamily .G2).subgroupOf_rootSubgroup_eq K ⟨γ, hγ⟩

theorem g2LongSL2_eq_sup (K : Type) [Field K] :
    g2LongSL2 K = rootGroup (rootOperatorFamily .G2) K g2e0 ⊔
      rootGroup (rootOperatorFamily .G2) K (-g2e0) := by
  change (rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0)).subgroupOf (adjointGroup .G2 K) = _
  rw [Subgroup.subgroupOf_sup (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _),
    subgroupOf_rootSubgroup_G2 (isRoot_single .G2 g2l),
    subgroupOf_rootSubgroup_G2 (isRoot_neg_single .G2 g2l)]

theorem g2ShortSL2_eq_sup (K : Type) [Field K] :
    g2ShortSL2 K = rootGroup (rootOperatorFamily .G2) K g2δ ⊔
      rootGroup (rootOperatorFamily .G2) K (-g2δ) := by
  change (rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ)).subgroupOf (adjointGroup .G2 K) = _
  rw [Subgroup.subgroupOf_sup (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _),
    subgroupOf_rootSubgroup_G2 isRoot_g2δ,
    subgroupOf_rootSubgroup_G2 (CFSG.LieType.Chevalley.IsRoot.neg isRoot_g2δ)]

theorem eq_one_or_of_mem_rootGroup {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2)
    {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot .G2 γ) {g : adjointGroup .G2 k}
    (hg : g ∈ rootGroup (rootOperatorFamily .G2) k γ) :
    g = 1 ∨ g = xPar (rootOperatorFamily .G2) γ 1 := by
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ g).mp hg
  rcases eq_zero_or_one_of_card_two hk c with rfl | rfl
  · exact Or.inl (xPar_zero γ)
  · exact Or.inr rfl

theorem map_mem_closure_of_mem_sup {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2)
    {G' : Type*} [Group G'] (φ : adjointGroup .G2 k ≃* G') {γ γ' : Fin Tag.G2.rank → ℤ}
    (hγ : IsRoot .G2 γ) (hγ' : IsRoot .G2 γ') {a b : G'}
    (ha : φ (xPar (rootOperatorFamily .G2) γ 1) = a)
    (hb : φ (xPar (rootOperatorFamily .G2) γ' 1) = b) {z : adjointGroup .G2 k}
    (hz : z ∈ rootGroup (rootOperatorFamily .G2) k γ ⊔ rootGroup (rootOperatorFamily .G2) k γ') :
    φ z ∈ Subgroup.closure ({a, b} : Set G') := by
  have hle : rootGroup (rootOperatorFamily .G2) k γ ⊔ rootGroup (rootOperatorFamily .G2) k γ' ≤
      (Subgroup.closure ({a, b} : Set G')).comap φ.toMonoidHom := by
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · rw [Subgroup.mem_comap]
      rcases eq_one_or_of_mem_rootGroup hk hγ hg with rfl | rfl
      · rw [map_one]
        exact Subgroup.one_mem _
      · change φ _ ∈ _
        rw [ha]
        exact Subgroup.subset_closure (by simp)
    · rw [Subgroup.mem_comap]
      rcases eq_one_or_of_mem_rootGroup hk hγ' hg with rfl | rfl
      · rw [map_one]
        exact Subgroup.one_mem _
      · change φ _ ∈ _
        rw [hb]
        exact Subgroup.subset_closure (by simp)
  exact hle hz

end RootSL2

section Main

theorem card_cayley_two {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2)
    (φ : adjointGroup .G2 k ≃* ↥(cayleyGroup (ZMod 2))) :
    Nat.card ↥(cayleyGroup (ZMod 2)) = 12096 := by
  rw [← Nat.card_congr φ.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hk]
  rfl

theorem g2TwoThreeConjSL2_holds :
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
      ∀ z : adjointGroup .G2 K, z ^ 3 = 1 → z ≠ 1 →
        ∃ g : adjointGroup .G2 K, g * z * g⁻¹ ∈ g2ShortSL2 K ∨ g * z * g⁻¹ ∈ g2LongSL2 K := by
  intro k _ _ hk z hz3 hz1
  obtain ⟨φ, h1, h2, h3, h4⟩ := exists_mulEquiv_cayley_two hk
  have hcard := card_cayley_two hk φ
  have hφ3 : φ z ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
  have hφ1 : φ z ≠ 1 := fun h => hz1 (φ.injective (by rw [h, map_one]))
  obtain ⟨g, hg⟩ := exists_conj_mem_rootSL2 hcard (φ z) hφ3 hφ1
  refine ⟨φ.symm g, ?_⟩
  have e : φ.symm g * z * (φ.symm g)⁻¹ = φ.symm (g * φ z * g⁻¹) := by
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  rw [e]
  rcases hg with hg | hg
  · right
    have hle : Subgroup.closure ({mA, mB} : Set ↥(cayleyGroup (ZMod 2))) ≤
        (g2LongSL2 k).map φ.toMonoidHom := by
      rw [Subgroup.closure_le, g2LongSL2_eq_sup]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨_, Subgroup.mem_sup_left (xPar_mem (isRoot_single .G2 g2l) 1), h1⟩
      · exact ⟨_, Subgroup.mem_sup_right (xPar_mem (isRoot_neg_single .G2 g2l) 1), h2⟩
    obtain ⟨w, hw, hwe⟩ := hle hg
    rw [← hwe]
    simpa using hw
  · left
    have hle : Subgroup.closure ({sA, sB} : Set ↥(cayleyGroup (ZMod 2))) ≤
        (g2ShortSL2 k).map φ.toMonoidHom := by
      rw [Subgroup.closure_le, g2ShortSL2_eq_sup]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨_, Subgroup.mem_sup_left (xPar_mem isRoot_g2δ 1), h3⟩
      · exact ⟨_, Subgroup.mem_sup_right
          (xPar_mem (CFSG.LieType.Chevalley.IsRoot.neg isRoot_g2δ) 1), h4⟩
    obtain ⟨w, hw, hwe⟩ := hle hg
    rw [← hwe]
    simpa using hw

theorem g2TwoLongCentThree_holds :
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
      ∀ z : adjointGroup .G2 K, z ∈ g2LongSL2 K → z ^ 3 = 1 → z ≠ 1 →
        (Nat.card (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)))).factorization 3 = 2 := by
  intro k _ _ hk z hz hz3 hz1
  obtain ⟨φ, h1, h2, -, -⟩ := exists_mulEquiv_cayley_two hk
  have hcard := card_cayley_two hk φ
  have hmem : φ z ∈ Subgroup.closure ({mA, mB} : Set ↥(cayleyGroup (ZMod 2))) := by
    rw [g2LongSL2_eq_sup] at hz
    exact map_mem_closure_of_mem_sup hk φ (isRoot_single .G2 g2l) (isRoot_neg_single .G2 g2l)
      h1 h2 hz
  have hφ3 : φ z ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
  have hφ1 : φ z ≠ 1 := fun h => hz1 (φ.injective (by rw [h, map_one]))
  rw [← card_centralizer_mulEquiv φ z]
  rcases eq_m0_of_mem hmem hφ3 hφ1 with h | h
  · rw [h]
    exact factorization_card_centralizer_m0 hcard
  · rw [h, m0_sq, centralizer_inv_singleton]
    exact factorization_card_centralizer_m0 hcard

theorem g2TwoShortCentThree_holds :
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
      ∀ z : adjointGroup .G2 K, z ∈ g2ShortSL2 K → z ^ 3 = 1 → z ≠ 1 →
        (Nat.card (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)))).factorization 3 = 3 := by
  intro k _ _ hk z hz hz3 hz1
  obtain ⟨φ, -, -, h3, h4⟩ := exists_mulEquiv_cayley_two hk
  have hcard := card_cayley_two hk φ
  have hmem : φ z ∈ Subgroup.closure ({sA, sB} : Set ↥(cayleyGroup (ZMod 2))) := by
    rw [g2ShortSL2_eq_sup] at hz
    exact map_mem_closure_of_mem_sup hk φ isRoot_g2δ
      (CFSG.LieType.Chevalley.IsRoot.neg isRoot_g2δ) h3 h4 hz
  have hφ3 : φ z ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
  have hφ1 : φ z ≠ 1 := fun h => hz1 (φ.injective (by rw [h, map_one]))
  rw [← card_centralizer_mulEquiv φ z]
  rcases eq_s0_of_mem hmem hφ3 hφ1 with h | h
  · rw [h]
    exact factorization_card_centralizer_s0 hcard
  · rw [h, s0_sq, centralizer_inv_singleton]
    exact factorization_card_centralizer_s0 hcard

end Main

end CFSG.RankThree.PartTwo.Sec8.Hering88N.G2Two

end
