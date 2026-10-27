module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenRTransfer
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTBIrred
public import CFSG.LocalAnalysis.StandardType.GGF4TwoNTMain
public import CFSG.LocalAnalysis.StandardType.GGF4TwoThreeCCentHolds
public import CFSG.LocalAnalysis.StandardType.GGF4AutWeyl
public import CFSG.LocalAnalysis.StandardType.GGFieldNbrTableB
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerGroup
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HF4Comp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGF4Comp
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264X1ExcF4Conj
public import CFSG.LieType.Chevalley.ParabolicSylowSubsystem
public import CFSG.Quasithin.EmptyFaithful.S146zMListCl
import CFSG.GroupTheory.ConjClassGeneration
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.CompSLOB

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley TableB

theorem E6TwoTB.SecEltAt.closure_conj_normalizer_eq {p : ℕ} {R : Type} [Group R] [Finite R]
    {E S : Subgroup R} (hE : E6TwoTB.SecEltAt p E) (hSE : S ≤ E) (hS : S ≠ ⊥) :
    Subgroup.closure (⋃ n ∈ (Subgroup.normalizer (E : Set R) : Set R),
      (fun s => n * s * n⁻¹) '' (S : Set R)) = E := by
  obtain ⟨k, τ, W, hτE, hsec, hWE, hirr, hne, hschur⟩ := hE
  let N : Subgroup R := Subgroup.normalizer (E : Set R)
  let H : Subgroup R := Subgroup.closure (⋃ n ∈ N, (fun s => n * s * n⁻¹) '' (S : Set R))
  change H = E
  have hH_le_E : H ≤ E := by
    change Subgroup.closure (⋃ n ∈ N, (fun s => n * s * n⁻¹) '' (S : Set R)) ≤ E
    rw [Subgroup.closure_le]
    rintro u hu
    simp only [Set.mem_iUnion, Set.mem_image] at hu
    obtain ⟨n, hn, s, hs, rfl⟩ := hu
    exact (Subgroup.mem_normalizer_iff.mp hn s).mp (hSE hs)
  have hS_le_H : S ≤ H := by
    intro s hs
    have hmem : s ∈ (fun s => 1 * s * 1⁻¹) '' (S : Set R) := by
      simpa only [one_mul, inv_one, mul_one] using
        Set.mem_image_of_mem (fun a => a) hs
    exact Subgroup.subset_closure (Set.mem_iUnion₂.mpr ⟨1, Subgroup.one_mem N, hmem⟩)
  have hH_ne_bot : H ≠ ⊥ := by
    intro hbot
    apply hS
    rw [eq_bot_iff]
    intro s hs
    have h1 : s ∈ H := hS_le_H hs
    rw [hbot] at h1
    simpa using h1
  have hW_nrm : W ⊆ N := fun w hw =>
    GGL48TW.Cent.mem_normalizer_of_conj_mem (H := E) (g := w) (fun y hy => hWE w hw y hy)
  have hconj : ∀ n ∈ N, ∀ h ∈ H, n * h * n⁻¹ ∈ H :=
    fun n hn h hh => CFSG.GroupTheory.conj_mem_closure_iUnion_conj N (S : Set R) hn hh
  rcases hirr H hH_le_E (fun w hw e he => hconj w (hW_nrm hw) e he) with h | h
  · exfalso
    exact hH_ne_bot h
  · exact h

namespace TableBF4TwoTB

section Centralizer


private theorem conj_adjointMap_mem_torusGroup_of_mem_centralizer {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 2) {ω : (FiniteField.Extension K 2 2)ˣ}
    (hωo : orderOf ω = 3) {c : adjointGroup .F4 K}
    (hc : c ∈ Subgroup.centralizer ((tE K).range : Set (adjointGroup .F4 K))) :
    (((ExcFrameIso.langEltF4 hωo)⁻¹ *
        TableBExcTwo.adjointMap .F4 (algebraMap K (FiniteField.Extension K 2 2)) c *
          ExcFrameIso.langEltF4 hωo : adjointGroup .F4 (FiniteField.Extension K 2 2)) :
        ModGL .F4 (FiniteField.Extension K 2 2)) ∈
      CFSG.LieType.Chevalley.torusGroup .F4 (FiniteField.Extension K 2 2) := by
  classical
  have hpk : 3 ∣ Nat.card (FiniteField.Extension K 2 2)ˣ := by
    rw [Nat.card_units, TableBExcTwoFusion.natCard_ext hK]
  have hCV := F4AutWeyl.F4_adjointGroup_inf_centralizer_torusPow_of_ne_two
    (k := FiniteField.Extension K 2 2) Nat.prime_three (by norm_num) hpk
  set G : adjointGroup .F4 (FiniteField.Extension K 2 2) :=
    ExcFrameIso.langEltF4 hωo with hG
  set ι : adjointGroup .F4 K →* adjointGroup .F4 (FiniteField.Extension K 2 2) :=
    TableBExcTwo.adjointMap .F4 (algebraMap K (FiniteField.Extension K 2 2)) with hι
  set V := TableBExc.torusPow .F4 (FiniteField.Extension K 2 2) 3 with hV
  have hTV : ((tE K).range.map ι).map (MulAut.conj G⁻¹).toMonoidHom = V := by
    rw [hG, hι, hV]
    exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1F4Conj.map_conj_range_tE_eq_torusPow hK hωo
  have hcent : ((G⁻¹ * ι c * G : adjointGroup .F4 (FiniteField.Extension K 2 2)) :
        ModGL .F4 (FiniteField.Extension K 2 2)) ∈
      Subgroup.centralizer {h : ModGL .F4 (FiniteField.Extension K 2 2) |
        h ∈ CFSG.LieType.Chevalley.torusGroup .F4 (FiniteField.Extension K 2 2) ∧ h ^ 3 = 1} := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hhV : (⟨h, CFSG.RankThree.Chevalley.torusGroup_le_adjointGroup_F4 hh.1⟩ :
        adjointGroup .F4 (FiniteField.Extension K 2 2)) ∈ V := by
      rw [hV, TableBExc.mem_torusPow]
      exact ⟨hh.1, Subtype.ext (by simpa using hh.2)⟩
    rw [← hTV] at hhV
    obtain ⟨_, ⟨y, hy, rfl⟩, hhy⟩ := hhV
    have hGy : (MulAut.conj G⁻¹).toMonoidHom (ι y) = G⁻¹ * ι y * G := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hcomm : (⟨h, CFSG.RankThree.Chevalley.torusGroup_le_adjointGroup_F4 hh.1⟩ :
        adjointGroup .F4 (FiniteField.Extension K 2 2)) * (G⁻¹ * ι c * G) =
        (G⁻¹ * ι c * G) *
          ⟨h, CFSG.RankThree.Chevalley.torusGroup_le_adjointGroup_F4 hh.1⟩ := by
      rw [← hhy, hGy]
      calc G⁻¹ * ι y * G * (G⁻¹ * ι c * G) = G⁻¹ * ι (y * c) * G := by
            rw [map_mul]; group
        _ = G⁻¹ * ι (c * y) * G := by rw [hc y hy]
        _ = G⁻¹ * ι c * G * (G⁻¹ * ι y * G) := by rw [map_mul]; group
    simpa using congrArg Subtype.val hcomm
  have hmem : ((G⁻¹ * ι c * G : adjointGroup .F4 (FiniteField.Extension K 2 2)) :
        ModGL .F4 (FiniteField.Extension K 2 2)) ∈
      adjointGroup .F4 (FiniteField.Extension K 2 2) ⊓
        Subgroup.centralizer {h : ModGL .F4 (FiniteField.Extension K 2 2) |
          h ∈ CFSG.LieType.Chevalley.torusGroup .F4
            (FiniteField.Extension K 2 2) ∧ h ^ 3 = 1} :=
    ⟨(G⁻¹ * ι c * G).2, hcent⟩
  rw [hCV] at hmem
  exact hmem

theorem centralizer_tE_F4 {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    Subgroup.centralizer ((tE K).range : Set (adjointGroup .F4 K)) = (tE K).range := by
  classical
  refine le_antisymm ?_ fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  swap
  · obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    rw [← map_mul, ← map_mul, mul_comm]
  · intro c hc
    have h3 := TableBExcTwoFusion.three_dvd_natCard_ext_sub_one hK
    obtain ⟨ω, hωo⟩ :=
      @TableBSymp.exists_orderOf_eq_of_dvd (FiniteField.Extension K 2 2) _ _
        3 (Fact.mk Nat.prime_three) h3
    set G : adjointGroup .F4 (FiniteField.Extension K 2 2) :=
      ExcFrameIso.langEltF4 hωo with hG
    set ι : adjointGroup .F4 K →* adjointGroup .F4 (FiniteField.Extension K 2 2) :=
      TableBExcTwo.adjointMap .F4 (algebraMap K (FiniteField.Extension K 2 2)) with hι
    set x : adjointGroup .F4 (FiniteField.Extension K 2 2) := G⁻¹ * ι c * G with hx
    have hxT : (x : ModGL .F4 (FiniteField.Extension K 2 2)) ∈
        CFSG.LieType.Chevalley.torusGroup .F4 (FiniteField.Extension K 2 2) := by
      simpa [hx, hG, hι] using
        conj_adjointMap_mem_torusGroup_of_mem_centralizer (K := K) hK hωo hc
    have hx3 : x ^ 3 = 1 := by
      have h := CFSG.LieType.Chevalley.ParSylow.torusGroup_pow_card_units
        (τ := .F4) (K := FiniteField.Extension K 2 2) hxT
      rw [show Nat.card (FiniteField.Extension K 2 2)ˣ = 3 by
        rw [Nat.card_units, TableBExcTwoFusion.natCard_ext hK]] at h
      exact Subtype.ext (by simpa using h)
    have hxV : x ∈ TableBExc.torusPow .F4 (FiniteField.Extension K 2 2) 3 := by
      rw [TableBExc.mem_torusPow]
      exact ⟨hxT, hx3⟩
    obtain ⟨y, hy, hxy⟩ :=
      (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1F4Conj.mem_torusPow_iff_exists hK hωo).1 hxV
    have hconj : G⁻¹ * ι y * G = G⁻¹ * ι c * G := by
      simpa [hG, hι] using hxy.symm.trans hx
    have hιeq : ι y = ι c := mul_left_cancel (mul_right_cancel hconj)
    have hyc : y = c := TableBExcTwo.adjointMap_injective (τ := .F4)
      (algebraMap K (FiniteField.Extension K 2 2)) (by simpa [hι] using hιeq)
    simpa [hyc] using hy

end Centralizer

section Gen


theorem mem_normalizer_component_F4Two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {x : adjointGroup .F4 K} (hx : orderOf x = 3) {J : Subgroup (adjointGroup .F4 K)}
    (hJ : IsComponentOf J (Subgroup.centralizer {x})) {g : adjointGroup .F4 K}
    (hg : g ∈ Subgroup.centralizer {x}) :
    g ∈ Subgroup.normalizer (J : Set (adjointGroup .F4 K)) := by
  have hcomp := CFSG.HardMathSupport.Dickson.Bal207.FamF42.compShape_conj_F4_two hK x hx
  have hJopen : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x)) := by
    rw [CFSG.LocalAnalysis.GLTheoremA.fixSubgroup_conj_eq_centralizer']
    exact (CFSG.Assembly.isComponentOf_iff_open).mp hJ
  have hcomm : MulAut.conj g * MulAut.conj x = MulAut.conj x * MulAut.conj g := by
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hg]
  exact CFSG.HardMathSupport.Dickson.Bal207.mem_normalizer_of_map_conj_eq
    (hcomp.norm (MulAut.conj g) hcomm J hJopen)

theorem three_dvd_card_component_F4Two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {x : adjointGroup .F4 K} (hx : orderOf x = 3) {J : Subgroup (adjointGroup .F4 K)}
    (hJ : IsComponentOf J (Subgroup.centralizer {x})) : 3 ∣ Nat.card J := by
  have hJopen : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x)) := by
    rw [CFSG.LocalAnalysis.GLTheoremA.fixSubgroup_conj_eq_centralizer']
    exact (CFSG.Assembly.isComponentOf_iff_open).mp hJ
  have hle : ∀ J' : Subgroup (adjointGroup .F4 K),
      CFSG.Open.IsComponentOf J'
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x)) → J' ≤ J := by
    intro J' hJ'
    exact le_of_eq (CFSG.LocalAnalysis.GLTheoremA.CatB.I2610.eq_of_isComponentOf_fixSubgroup_conj
      hK hx hJ' hJopen)
  have hmodel : CFSG.Open.StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSp 3 2 1 :=
    CFSG.LocalAnalysis.GLTheoremA.S265.SG.model_of_le_component_F4 (F := K) (f := 1)
      (by simpa using hK) (by norm_num) x hx hJopen hle
  exact dvd_trans (CFSG.Quasithin.three_dvd_card_psp_model hmodel)
    (Subgroup.card_quotient_dvd_card (Subgroup.center ↥J))

private theorem exists_gen_of_conj_frame_tE {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian 3 E)
    (hsc : ∀ g : adjointGroup .F4 K, (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E)
    {x : adjointGroup .F4 K} (hx : x ∈ E) (hx1 : x ≠ 1)
    {J : Subgroup (adjointGroup .F4 K)} (hJ : IsComponentOf J (Subgroup.centralizer {x}))
    {c : adjointGroup .F4 K} (hc : c ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K)))
    {c₀ : adjointGroup .F4 K}
    (hEeq : E = (tE K).range.map (MulAut.conj c₀).toMonoidHom) :
    ∃ (S : Subgroup (adjointGroup .F4 K)) (W : Set (adjointGroup .F4 K)),
      IsPGroup 3 S ∧ S ≤ Subgroup.centralizer (E : Set (adjointGroup .F4 K)) ∧ S ≤ J ∧
        W ⊆ (Subgroup.normalizer (E : Set (adjointGroup .F4 K)) :
          Set (adjointGroup .F4 K)) ∧
        c ∈ Subgroup.closure
          (⋃ n ∈ W, (fun s => n * s * n⁻¹) '' (S : Set (adjointGroup .F4 K))) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (adjointGroup .F4 K) := CFSG.LieType.Chevalley.generated_group_finite .F4 K
  have hx3 : x ^ 3 = 1 := hE.2 x hx
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hEx : E ≤ Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hE.1.is_comm.comm ⟨g, hg⟩ ⟨x, hx⟩))
  have hEN : E ≤ Subgroup.normalizer (J : Set (adjointGroup .F4 K)) := fun g hg =>
    mem_normalizer_component_F4Two hK hxord hJ (hEx hg)
  have hSp : IsPGroup 3 E := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hE.2 g g.2⟩
  have hSC : ∀ g ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K)), g ^ 3 = 1 → g ∈ E :=
    fun g hg hg3 =>
      hsc g (fun e he => (Subgroup.mem_centralizer_iff.mp hg e he).symm) hg3
  obtain ⟨b, hb, hb1, -⟩ :=
    exists_mem_inf_ne_one_of_dvd Nat.prime_three hEN hSp hSC
      (three_dvd_card_component_F4Two hK hxord hJ)
  have hne : J ⊓ E ≠ ⊥ := by
    intro hbot
    have hb' : b ∈ J ⊓ E := Subgroup.mem_inf.mpr ⟨hb.2, hb.1⟩
    rw [hbot, Subgroup.mem_bot] at hb'
    exact hb1 hb'
  have hCE : Subgroup.centralizer (E : Set (adjointGroup .F4 K)) = E := by
    rw [hEeq, centralizer_map_conj, centralizer_tE_F4 hK]
  have hcE : c ∈ E := by
    rw [hCE] at hc
    exact hc
  have hsec : E6TwoTB.SecEltAt 3 E := by
    rw [hEeq]
    exact TableBExcTwoTB.secEltAt_map_conj (secEltAt_F4 hK) c₀
  refine ⟨J ⊓ E, Subgroup.normalizer (E : Set (adjointGroup .F4 K)), ?_, ?_, inf_le_left,
    subset_rfl, ?_⟩
  · intro g
    exact ⟨1, by
      apply Subtype.ext
      simpa using hE.2 g.1 g.2.2⟩
  · intro s hs
    exact Subgroup.mem_centralizer_iff.mpr fun e he =>
      congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨s, hs.2⟩)
  · have hclos := hsec.closure_conj_normalizer_eq (S := J ⊓ E) inf_le_right hne
    rw [hclos]
    exact hcE

theorem ggTorusGenR_adjoint_F4Two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (hS : GGF4TwoNonToralSolv K) :
    GGTorusGenR 3 3 (adjointGroup .F4 K) := by
  intro E hE hcard hsc x hx hx1 J hJ c hc hcp
  by_cases hconj : ∃ c₀ : adjointGroup .F4 K,
      E = (tE K).range.map (MulAut.conj c₀).toMonoidHom
  · obtain ⟨c₀, hEeq⟩ := hconj
    exact exists_gen_of_conj_frame_tE hK hE hsc hx hx1 hJ hc hEeq
  · exfalso
    exact CFSG.StandardType.Line63.H5.false_of_isComponentOf_of_isSolvable
      (hS E hE hcard (fun g hg3 hcomm => hsc g hcomm hg3) hconj x hx hx1) hJ

theorem ggTorusGenR_F4Two {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (hS : GGF4TwoNonToralSolv K) : GGTorusGenR 3 3 (TableBF4.RecipeGroup K) :=
  ggTorusGenR_of_mulEquiv (TableBF4.recipeEquiv K) (ggTorusGenR_adjoint_F4Two hK hS)

theorem ggTorusGenTableB_F4Two {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (hS : GGF4TwoNonToralSolv K) :
    GGTorusGenTableB 3 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) :=
  ggTorusGenTableB_of_torusGenR Nat.prime_three
    (fun φ hφ _ => TableBF4.idImage_subset_inn K hφ)
    (TableBF4.center_recipeGroup_eq_bot K)
    (ExcSplitL.ggCenterPrime_recipe_F4 Nat.prime_three (by norm_num))
    (ggTorusGenR_F4Two hK hS)

theorem largeEvenLabelAll_torusGenTableB_f4TwoThree (hS : GGF4TwoNonToralSolvInput) {p : ℕ}
    {lab : LargeEvenLabel} (h : GGTableBF4TwoLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hn, rfl⟩ := h
  dsimp only at htag hn
  subst htag
  subst hn
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK])
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  exact ⟨K, inferInstance, inferInstance, hK, hQ', ggTorusGenTableB_F4Two hK2 (hS K hK2)⟩

theorem largeEvenLabelAll_torusGenTableB_f4TwoThree_holds
    {p : ℕ} {lab : LargeEvenLabel} (h : GGTableBF4TwoLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I :=
  largeEvenLabelAll_torusGenTableB_f4TwoThree
    (F4TwoNonToral.ggF4TwoNonToralSolvInput_of_cent
      SmallExc.F4Two.ggF4TwoThreeCCentInput_holds) h

end Gen

end TableBF4TwoTB

end CFSG.StandardType

end
