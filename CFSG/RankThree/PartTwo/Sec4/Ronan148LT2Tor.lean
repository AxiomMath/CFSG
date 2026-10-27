module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LNA
public import CFSG.RankThree.PartTwo.Sec21.Item233TablesSp64
public import CFSG.RankThree.PartTwo.KFacts.KS21FusionU58
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL44
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSp64
public import CFSG.LieType.Steinberg.CentralExt.GriessUnitaryOdd
public import CFSG.HardMathSupport.Solomon.Coordinator.I10_21Hopf
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1A11

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (NoThreeCover)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Open (StatedClassicalModel StatedProj StatedSL StatedSU StatedSp)
open CFSG.Blueprint.Multiplier (generic exceptional genericOrders exceptionalOrders)
open Matrix

theorem E27Move.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : E27Move Y) :
    E27Move X := by
  intro E hE s hs hs1
  obtain ⟨n, hn, hns⟩ := h (E.map e.toMonoidHom)
    ⟨isElemAbelian_map _ hE.1, by rw [Subgroup.card_map_of_injective e.injective, hE.2]⟩ (e s)
    ⟨s, hs, rfl⟩ (by rw [Ne, map_eq_one_iff _ e.injective]; exact hs1)
  rw [← Subgroup.map_equiv_normalizer_eq] at hn
  obtain ⟨m, hm, rfl⟩ := hn
  refine ⟨m, hm, fun hm' => hns ?_⟩
  have hZ : (Subgroup.zpowers s).map e.toMonoidHom = Subgroup.zpowers (e s) :=
    MonoidHom.map_zpowers _ s
  rw [← hZ, ← Subgroup.map_equiv_normalizer_eq]
  exact ⟨m, hm', rfl⟩

theorem e27Move_of_conj {X : Type} [Group X] {E₀ : Subgroup X}
    (hconj : ∀ E : Subgroup X, Late.IsE27 E → ∃ x : X, E.map (MulAut.conj x).toMonoidHom = E₀)
    (hmv : ∀ s ∈ E₀, s ≠ 1 → ∃ n ∈ Subgroup.normalizer (E₀ : Set X),
      n ∉ Subgroup.normalizer (Subgroup.zpowers s : Set X)) :
    E27Move X := by
  intro E hE s hs hs1
  obtain ⟨x, hx⟩ := hconj E hE
  have hcomp : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
      MonoidHom.id X := by
    ext z
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  have hEeq : E = E₀.map (MulAut.conj x⁻¹).toMonoidHom := by
    rw [← hx, Subgroup.map_map, hcomp, Subgroup.map_id]
  rw [hEeq] at hs ⊢
  exact Ronan148R.moves_map (MulAut.conj x⁻¹) hmv s hs hs1

theorem mover_of_conj {X : Type} [Group X] {E : Subgroup X} {n s : X}
    (hE : E.map (MulAut.conj n).toMonoidHom = E) (hs : n * s * n⁻¹ ∉ Subgroup.zpowers s) :
    n ∈ Subgroup.normalizer (E : Set X) ∧
      n ∉ Subgroup.normalizer (Subgroup.zpowers s : Set X) :=
  ⟨Subgroup.mem_normalizer_iff_map_conj_eq.mpr hE, fun h =>
    hs ((Subgroup.mem_normalizer_iff.mp h s).mp (Subgroup.mem_zpowers s))⟩

theorem toAdd_zpow_zmod {ι : Type} (v : Multiplicative (ι → ZMod 3)) (k : ℤ) :
    Multiplicative.toAdd (v ^ k) = (k : ZMod 3) • Multiplicative.toAdd v := by
  rw [toAdd_zpow, Int.cast_smul_eq_zsmul]

theorem noThreeCover_of_hopf {X A : Type} [Group X] [Group A] [Finite A]
    (e : CFSG.Open.griessHopfMultiplier X ≃* A) (h3 : ¬ 3 ∣ Nat.card A) : NoThreeCover X := by
  intro Y _ _ hY ⟨f⟩ h3Y
  let π : Y →* X := f.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))
  have hπs : Function.Surjective π := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center Y := by
    ext y
    rw [MonoidHom.mem_ker]
    change f (QuotientGroup.mk' (Subgroup.center Y) y) = 1 ↔ _
    rw [map_eq_one_iff f f.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hd := HardMathSupport.Solomon.Coordinator.i1021_card_ker_dvd π hπs hker.le hY.1 e
  rw [hker] at hd
  exact h3 (h3Y.trans hd)

theorem card_multiplicative_zmod (n : ℕ) : Nat.card (Multiplicative (ZMod n)) = n := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod n) ≃ ZMod n), Nat.card_zmod]

theorem noThreeCover_of_table {X : Type} [Group X] {t : CFSG.Open.StatedLieTag} {n p f : ℕ}
    (hg : genericOrders t n p f = (1, 1)) (he : exceptionalOrders t n p f = (1, 1))
    (h : Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic t n p f × exceptional t n p f)) :
    NoThreeCover X := by
  obtain ⟨e⟩ := h
  have hcard : Nat.card (generic t n p f × exceptional t n p f) = 1 := by
    simp only [generic, exceptional, Nat.card_prod, card_multiplicative_zmod, hg, he]
  haveI : Finite (generic t n p f × exceptional t n p f) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact noThreeCover_of_hopf e (by rw [hcard]; norm_num)

section U58


theorem noThreeCover_projSU_five_eight : NoThreeCover (projSU 5 2 3) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e₀ : projSU 5 2 3 ≃* StatedProj (StatedSU 5 (2 ^ 3) (GaloisField 2 (2 * 3))) :=
    ((Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
      (MulEquiv.subgroupCongr (CFSG.RankThree.PartOne.projImage_statedSU_eq_projSU 5 2 3))).symm
  have hSU : StatedClassicalModel (projSU 5 2 3) .PSU 5 2 3 :=
    ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide⟩, GaloisField 2 (2 * 3), inferInstance,
      inferInstance, by rw [GaloisField.card 2 (2 * 3) (by norm_num)]; norm_num, ⟨e₀⟩⟩
  exact noThreeCover_of_table (by simp [genericOrders]) rfl
    (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_odd_row hSU (by decide)).2

end U58

theorem exists_e81_projSU :
    ∃ E : Subgroup (projSU 5 2 3), CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 81 := by
  obtain ⟨ζ, hζ⟩ := KFacts.KS21.U58.exists_zeta
  have hζ9 : ζ ^ 9 = 1 := by
    have := pow_orderOf_eq_one ζ
    rwa [hζ] at this
  have hτS : ∀ v, KFacts.KS21.U58.emb5 (KFacts.KS21.DFT.tau9 hζ9 v) ∈ KFacts.KS21.U58.SUI := by
    intro v
    obtain ⟨⟨u, d⟩, rfl⟩ := Multiplicative.ofAdd.surjective v
    rw [KFacts.KS21.DFT.tau9_apply]
    refine KFacts.KS21.U58.emb5_mem (KFacts.KS21.U58.unitary_diagGL fun i => ?_)
      (KFacts.KS21.U58.pow_eight_mul_self ?_)
    · rw [← pow_mul, mul_comm _ 9, pow_mul, hζ9, one_pow]
    · rw [← pow_mul, mul_comm _ 9, pow_mul, hζ9, one_pow]
  let τ₂ : Multiplicative ((Fin 3 → ZMod 9) × ZMod 9) →* KFacts.KS21.U58.SUI :=
    (KFacts.KS21.U58.emb5.comp (KFacts.KS21.DFT.tau9 hζ9)).codRestrict _ hτS
  have hτ₂ : Function.Injective τ₂ := fun x y h =>
    KFacts.KS21.DFT.tau9_injective hζ9 hζ
      (KFacts.KS21.U58.emb5_injective (congrArg Subtype.val h))
  refine ⟨(KFacts.KS21.torusOmega τ₂).map KFacts.KS21.U58.equivSUI.symm.toMonoidHom,
    isElemAbelian_map _ (KFacts.KS21.isElemAbelian_torusOmega τ₂), ?_⟩
  rw [Subgroup.card_map_of_injective KFacts.KS21.U58.equivSUI.symm.injective,
    KFacts.KS21.card_torusOmega hτ₂, KFacts.KS21.card_V9_three]
  norm_num

section U58Row


theorem kT2_eight_SU5_8 : RowOf425 (projSU 5 2 3) := fun S _ _ _ _ ⟨e⟩ => by
  obtain ⟨E, hE, hE81⟩ := exists_e81_projSU
  exact row425_of_e81
    (HardMathSupport.Solomon.Coordinator.LieComp.NoThreeCover.of_mulEquiv e
      noThreeCover_projSU_five_eight)
    ⟨E.map e.symm.toMonoidHom, isElemAbelian_map _ hE, by
      rw [Subgroup.card_map_of_injective e.symm.injective, hE81]⟩

end U58Row

section L44

open CFSG.RankThree.PartTwo.KFacts.KS21.L44 (F4 M)

theorem exists_conj_eq_reindexSL (σ : Equiv.Perm (Fin 4)) :
    ∃ n : M, MulAut.conj n = Sec21.Tables.reindexSL σ := by
  have hdet : (σ.toPEquiv.toMatrix : Matrix (Fin 4) (Fin 4) F4).det = 1 := by
    have h := Matrix.det_permutation (R := F4) σ
    rw [Equiv.Perm.permMatrix] at h
    rw [h]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> rw [h1]
    · simp
    · simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
      exact Sec21.TablesSp64.neg_one_F4
  let n : M := ⟨σ.toPEquiv.toMatrix, hdet⟩
  refine ⟨n, ?_⟩
  ext g : 1
  rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change (σ.toPEquiv.toMatrix : Matrix (Fin 4) (Fin 4) F4) * (g : Matrix (Fin 4) (Fin 4) F4) =
    (g : Matrix (Fin 4) (Fin 4) F4).submatrix σ σ * σ.toPEquiv.toMatrix
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp

theorem move_L44 : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ∃ σ : Equiv.Perm (Fin 4),
    ∀ c : ZMod 3, Sec21.TablesL44.res (Sec21.TablesL44.ext v ∘ σ) ≠ c • v := by
  decide

theorem e27Move_M : E27Move M := by
  refine e27Move_of_conj (E₀ := Sec21.TablesL44.A0)
    (fun E hE => Sec21.TablesL44.exists_map_conj_eq_A0 hE.1 (by rw [hE.2]; norm_num)) ?_
  rintro _ ⟨v, rfl⟩ hv1
  have hv : Multiplicative.toAdd v ≠ 0 := fun h => hv1 (by
    rw [show v = 1 from Multiplicative.toAdd.injective h, map_one])
  obtain ⟨σ, hσ⟩ := move_L44 _ hv
  obtain ⟨n, hn⟩ := exists_conj_eq_reindexSL σ
  have hconj : n * Sec21.TablesL44.δ v * n⁻¹ = Sec21.TablesL44.δ (Multiplicative.ofAdd
      (Sec21.TablesL44.res (Sec21.TablesL44.ext (Multiplicative.toAdd v) ∘ σ))) := by
    rw [← MulAut.conj_apply, hn]
    exact Sec21.TablesL44.reindexSL_δ σ _
  have hA : Sec21.TablesL44.A0.map (MulAut.conj n).toMonoidHom = Sec21.TablesL44.A0 := by
    rw [hn]
    exact Sec21.TablesL44.map_reindexSL_A0 σ
  have hns : n * Sec21.TablesL44.δ v * n⁻¹ ∉ Subgroup.zpowers (Sec21.TablesL44.δ v) := by
    rw [hconj]
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← map_zpow] at hk
    have h2 := congrArg Multiplicative.toAdd (Sec21.TablesL44.δ_injective hk)
    rw [toAdd_zpow_zmod, toAdd_ofAdd] at h2
    exact hσ (k : ZMod 3) h2.symm
  exact ⟨n, (mover_of_conj hA hns).1, (mover_of_conj hA hns).2⟩

theorem exists_e27_M : ∃ E : Subgroup M, Late.IsE27 E :=
  ⟨Sec21.TablesL44.A0, Sec21.TablesL44.isElemAbelian_A0, by
    rw [Sec21.TablesL44.card_A0]; norm_num⟩

end L44

section L44Row


theorem noThreeCover_projSL_four_four : NoThreeCover (projSL 4 (GaloisField 2 2)) := by
  have e₀ : projSL 4 (GaloisField 2 2) ≃* StatedProj (StatedSL 4 (GaloisField 2 2)) :=
    ((Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
      (MulEquiv.subgroupCongr
        (CFSG.RankThree.PartOne.projImage_statedSL_eq_projSL 4 (GaloisField 2 2)))).symm
  have hSL : StatedClassicalModel (projSL 4 (GaloisField 2 2)) .PSL 4 2 2 :=
    ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, GaloisField 2 2,
      inferInstance, inferInstance, GaloisField.card 2 2 (by norm_num), ⟨e₀⟩⟩
  exact noThreeCover_of_table (by simp [genericOrders]) rfl
    (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row hSL).2

theorem kT2_eight_SL4 : RowOf425 (projSL 4 (GaloisField 2 2)) := fun S _ _ _ _ ⟨e⟩ => by
  let φ : S ≃* KFacts.KS21.L44.M := e.trans KFacts.KS21.L44.equivSL
  obtain ⟨E, hE⟩ := exists_e27_M
  refine row425_of_e27Move
    (HardMathSupport.Solomon.Coordinator.LieComp.NoThreeCover.of_mulEquiv e
      noThreeCover_projSL_four_four)
    (cubeInner_of_mulEquiv e (cubeInner_of_not_three_dvd_card_outer
      RonanK432.not_three_dvd_card_outer_projSL4))
    ⟨E.map φ.symm.toMonoidHom, isElemAbelian_map _ hE.1, by
      rw [Subgroup.card_map_of_injective φ.symm.injective, hE.2]⟩
    (e27Move_M.of_mulEquiv φ)

end L44Row

section Sp64

open CFSG.RankThree.PartTwo.KFacts.KS21.Sp64 (F4 Sp Mat6 mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (mem_statedSp_iff)

theorem exists_conj_eq_reindexSp (π : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (hπ : Sec21.TablesSp64.Jm.submatrix π π = Sec21.TablesSp64.Jm) :
    ∃ n : Sp, MulAut.conj n = Sec21.TablesSp64.reindexSp π hπ := by
  let P : Mat6 := π.toPEquiv.toMatrix
  let P' : Mat6 := π.symm.toPEquiv.toMatrix
  have hPP' : P * P' = 1 := by
    change π.toPEquiv.toMatrix * π.symm.toPEquiv.toMatrix = (1 : Mat6)
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  have hP'P : P' * P = 1 := by
    change π.symm.toPEquiv.toMatrix * π.toPEquiv.toMatrix = (1 : Mat6)
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  let g₀ : GL (Fin 3 ⊕ Fin 3) F4 := ⟨P, P', hPP', hP'P⟩
  have hmem : g₀ ∈ Sp := by
    rw [mem_statedSp_iff]
    change Pᵀ * Sec21.TablesSp64.Jm * P = Sec21.TablesSp64.Jm
    have hT : Pᵀ = P' := by
      change (π.toPEquiv.toMatrix : Mat6)ᵀ = π.symm.toPEquiv.toMatrix
      rw [← PEquiv.toMatrix_symm, Equiv.toPEquiv_symm]
    rw [hT]
    change π.symm.toPEquiv.toMatrix * Sec21.TablesSp64.Jm * π.toPEquiv.toMatrix = Sec21.TablesSp64.Jm
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
    exact Sec21.TablesSp64.Jm_symm hπ
  refine ⟨⟨g₀, hmem⟩, ?_⟩
  ext g : 1
  rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
  apply mat_injective
  rw [KFacts.KS21.Sp64.mat_mul, KFacts.KS21.Sp64.mat_mul, Sec21.TablesSp64.mat_reindexSp]
  change (π.toPEquiv.toMatrix : Mat6) * mat g = (mat g).submatrix π π * π.toPEquiv.toMatrix
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp

theorem move_Sp64 : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ∃ σ : Equiv.Perm (Fin 3),
    ∃ s : Fin 3 → Bool, ∀ c : ZMod 3, Sec21.TablesSp64.flipVec s (v ∘ σ) ≠ c • v := by
  decide

theorem e27Move_Sp : E27Move Sp := by
  refine e27Move_of_conj (E₀ := Sec21.TablesSp64.A0)
    (fun E hE => Sec21.TablesSp64.exists_map_conj_eq_A0 hE.1 (by rw [hE.2]; norm_num)) ?_
  rintro _ ⟨v, rfl⟩ hv1
  have hv : Multiplicative.toAdd v ≠ 0 := fun h => hv1 (by
    rw [show v = 1 from Multiplicative.toAdd.injective h, map_one])
  obtain ⟨σ, s, hσ⟩ := move_Sp64 _ hv
  obtain ⟨n₁, hn₁⟩ := exists_conj_eq_reindexSp _ (Sec21.TablesSp64.Jm_permE σ)
  obtain ⟨n₂, hn₂⟩ := exists_conj_eq_reindexSp _ (Sec21.TablesSp64.Jm_flipE s)
  have hconj : (n₂ * n₁) * Sec21.TablesSp64.δ v * (n₂ * n₁)⁻¹ = Sec21.TablesSp64.δ
      (Multiplicative.ofAdd (Sec21.TablesSp64.flipVec s (Multiplicative.toAdd v ∘ σ))) := by
    rw [← MulAut.conj_apply, map_mul, MulAut.mul_apply, hn₁, hn₂]
    rw [show Sec21.TablesSp64.δ v = Sec21.TablesSp64.δ (Multiplicative.ofAdd
      (Multiplicative.toAdd v)) from rfl,
      Sec21.TablesSp64.reindexSp_δ _ (Sec21.TablesSp64.ext_comp_permE σ _),
      Sec21.TablesSp64.reindexSp_δ _ (Sec21.TablesSp64.ext_comp_flipE s _)]
  have hA : Sec21.TablesSp64.A0.map (MulAut.conj (n₂ * n₁)).toMonoidHom = Sec21.TablesSp64.A0 := by
    have e : (MulAut.conj (n₂ * n₁)).toMonoidHom =
        (Sec21.TablesSp64.reindexSp _ (Sec21.TablesSp64.Jm_flipE s)).toMonoidHom.comp
          (Sec21.TablesSp64.reindexSp _ (Sec21.TablesSp64.Jm_permE σ)).toMonoidHom := by
      rw [map_mul, hn₁, hn₂]
      rfl
    rw [e, ← Subgroup.map_map,
      Sec21.TablesSp64.map_reindexSp_A0 _ fun v => ⟨_, Sec21.TablesSp64.ext_comp_permE σ v⟩,
      Sec21.TablesSp64.map_reindexSp_A0 _ fun v => ⟨_, Sec21.TablesSp64.ext_comp_flipE s v⟩]
  have hns : (n₂ * n₁) * Sec21.TablesSp64.δ v * (n₂ * n₁)⁻¹ ∉
      Subgroup.zpowers (Sec21.TablesSp64.δ v) := by
    rw [hconj]
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← map_zpow] at hk
    have h2 := congrArg Multiplicative.toAdd (Sec21.TablesSp64.δ_injective hk)
    rw [toAdd_zpow_zmod, toAdd_ofAdd] at h2
    exact hσ (k : ZMod 3) h2.symm
  exact ⟨n₂ * n₁, (mover_of_conj hA hns).1, (mover_of_conj hA hns).2⟩

theorem exists_e27_Sp : ∃ E : Subgroup Sp, Late.IsE27 E :=
  ⟨Sec21.TablesSp64.A0, Sec21.TablesSp64.isElemAbelian_A0, by
    rw [Sec21.TablesSp64.card_A0]; norm_num⟩

end Sp64

section Sp64Row


theorem noThreeCover_projSp_three_four : NoThreeCover (projSp 3 (GaloisField 2 2)) := by
  have e₀ : projSp 3 (GaloisField 2 2) ≃* StatedProj (StatedSp 3 (GaloisField 2 2)) :=
    ((Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
      (MulEquiv.subgroupCongr
        (CFSG.RankThree.PartOne.projImage_statedSp_eq_projSp 3 (GaloisField 2 2)))).symm
  have hSp : StatedClassicalModel (projSp 3 (GaloisField 2 2)) .PSp 3 2 2 :=
    ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide⟩, GaloisField 2 2,
      inferInstance, inferInstance, GaloisField.card 2 2 (by norm_num), ⟨e₀⟩⟩
  exact noThreeCover_of_table (by simp [genericOrders]) rfl
    (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psp_row hSp (Or.inr (Or.inl rfl))).2

theorem kT2_eight_Sp6_4 : RowOf425 (projSp 3 (GaloisField 2 2)) := fun S _ _ _ _ ⟨e⟩ => by
  let φ : S ≃* KFacts.KS21.Sp64.Sp := e.trans KFacts.KS21.Sp64.equivSp
  obtain ⟨E, hE⟩ := exists_e27_Sp
  refine row425_of_e27Move
    (HardMathSupport.Solomon.Coordinator.LieComp.NoThreeCover.of_mulEquiv e
      noThreeCover_projSp_three_four)
    (cubeInner_of_mulEquiv e (cubeInner_of_not_three_dvd_card_outer
      RonanK432.not_three_dvd_card_outer_projSp6))
    ⟨E.map φ.symm.toMonoidHom, isElemAbelian_map _ hE.1, by
      rw [Subgroup.card_map_of_injective φ.symm.injective, hE.2]⟩
    (e27Move_Sp.of_mulEquiv φ)

end Sp64Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
