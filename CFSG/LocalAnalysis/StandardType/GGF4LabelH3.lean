module

public import CFSG.LocalAnalysis.StandardType.GGF4LabelPieces
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestOriginalWeyl
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLang
public import Mathlib.GroupTheory.Coxeter.Inversion
import CFSG.LocalAnalysis.StandardType.GGAutomizerJoinInduced
import CFSG.LocalAnalysis.StandardType.GGF4A3Residual
import CFSG.LocalAnalysis.StandardType.GGF4CoxeterSystem
import CFSG.LocalAnalysis.StandardType.GGF4EndpointType
import CFSG.LocalAnalysis.StandardType.GGSecFiveBFixLine
import CFSG.LocalAnalysis.StandardType.GGSecFiveBMaxToPair
import CFSG.LocalAnalysis.StandardType.GGF4SmallBook
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSpJoinReflAlgebra
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosWeylSys
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallE8
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggF4_presentation_family {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    {J : Subgroup (MulAut ↥Bs)} {cs : CoxeterSystem CoxeterMatrix.F₄ ↥J}
    (hcs : ∀ a : ↥J, cs.IsReflection a ↔ GGIsReflection p (a : MulAut ↥Bs))
    {M : CoxeterMatrix (Fin 3)} {X : Subgroup (MulAut ↥Bs)} (hXJ : X ≤ J)
    {eX : M.Group ≃* ↥X} (hP : GGCoxeterPres p X M eX) :
    ∃ f : Fin 3 → ↥J,
      (∀ i, cs.IsReflection (f i)) ∧
      (∀ i j, orderOf (f i * f j) = M.M i j) ∧
      (Subgroup.closure (Set.range f)).map J.subtype = X := by
  let f : Fin 3 → ↥J := fun i => Subgroup.inclusion hXJ (eX (M.simple i))
  let F : M.Group →* ↥J := (Subgroup.inclusion hXJ).comp eX.toMonoidHom
  have hFsimple : ∀ i, F (M.simple i) = f i := fun i => rfl
  have hFrange : F.range = Subgroup.closure (Set.range f) := by
    rw [MonoidHom.range_eq_map, ← M.toCoxeterSystem.subgroup_closure_range_simple,
      MonoidHom.map_closure, ← Set.range_comp]
    congr 1
  have hGrange : (J.subtype.comp F).range = X := by
    have hcomp : J.subtype.comp F = X.subtype.comp eX.toMonoidHom := by
      ext x
      simp [F]
    rw [hcomp]
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eX.surjective, Subgroup.map_top,
      Subgroup.range_subtype]
  have hf_refl : ∀ i, cs.IsReflection (f i) := by
    intro i
    rw [hcs]
    simpa [f] using hP.2 i
  have hord : ∀ i j, orderOf (f i * f j) = M.M i j := by
    intro i j
    have h1 : f i * f j = Subgroup.inclusion hXJ (eX (M.simple i * M.simple j)) := by
      simp [f, map_mul]
    rw [h1, orderOf_injective (Subgroup.inclusion hXJ) (Subgroup.inclusion_injective hXJ),
      MulEquiv.orderOf_eq eX]
    simpa using M.toCoxeterSystem.orderOf_simple_mul_simple i j
  have hclo : (Subgroup.closure (Set.range f)).map J.subtype = X := by
    rw [← hFrange]
    rw [MonoidHom.map_range J.subtype F]
    exact hGrange
  exact ⟨f, hf_refl, hord, hclo⟩

theorem ggF4_exists_family_of_typeA3B3 {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    {J : Subgroup (MulAut ↥Bs)} {cs : CoxeterSystem CoxeterMatrix.F₄ ↥J}
    (hcs : ∀ a : ↥J, cs.IsReflection a ↔ GGIsReflection p (a : MulAut ↥Bs))
    {X : Subgroup (MulAut ↥Bs)} (hXJ : X ≤ J)
    (hX : GGWeylOfType p (CoxeterMatrix.A 3) X ∨ GGWeylOfType p (CoxeterMatrix.B 3) X) :
    ∃ b : Fin 3 → ↥J,
      (∀ i, cs.IsReflection (b i)) ∧
      orderOf (b 0 * b 1) = 3 ∧
      (orderOf (b 1 * b 2) = 3 ∨ orderOf (b 1 * b 2) = 4) ∧
      orderOf (b 0 * b 2) = 2 ∧
      (Subgroup.closure (Set.range b)).map J.subtype = X ∧
      (orderOf (b 1 * b 2) = 4 → GGWeylOfType p (CoxeterMatrix.B 3) X) := by
  rcases hX with ⟨eA, hPA_refl⟩ | ⟨eB, hPB_refl⟩
  · have hPA : GGCoxeterPres p X (CoxeterMatrix.A 3) eA :=
      ⟨CFSG.TwoNodeSmall.pws_ggIsWeylMatrix_A 3 (by norm_num), hPA_refl⟩
    obtain ⟨b, hb_refl, hb_ord, hb_clo⟩ := ggF4_presentation_family hcs hXJ hPA
    have h01 : orderOf (b 0 * b 1) = 3 := by
      simpa [CoxeterMatrix.A, CoxeterMatrix.B] using hb_ord 0 1
    have h12 : orderOf (b 1 * b 2) = 3 := by
      simpa [CoxeterMatrix.A, CoxeterMatrix.B] using hb_ord 1 2
    have h02 : orderOf (b 0 * b 2) = 2 := by
      simpa [CoxeterMatrix.A, CoxeterMatrix.B] using hb_ord 0 2
    exact ⟨b, hb_refl, h01, Or.inl h12, h02, hb_clo,
      by intro h; rw [h12] at h; norm_num at h⟩
  · have hPB : GGCoxeterPres p X (CoxeterMatrix.B 3) eB :=
      ⟨CFSG.TwoNodeSmall.pws_ggIsWeylMatrix_B 3 (by norm_num), hPB_refl⟩
    obtain ⟨b, hb_refl, hb_ord, hb_clo⟩ := ggF4_presentation_family hcs hXJ hPB
    have h01 : orderOf (b 0 * b 1) = 3 := by
      simpa [CoxeterMatrix.A, CoxeterMatrix.B] using hb_ord 0 1
    have h12 : orderOf (b 1 * b 2) = 4 := by
      simpa [CoxeterMatrix.A, CoxeterMatrix.B] using hb_ord 1 2
    have h02 : orderOf (b 0 * b 2) = 2 := by
      simpa [CoxeterMatrix.A, CoxeterMatrix.B] using hb_ord 0 2
    exact ⟨b, hb_refl, h01, Or.inr h12, h02, hb_clo, by intro _; exact ⟨eB, hPB_refl⟩⟩

theorem ggF4_closure_union_eq_top_iff {G : Type} [Group G] {Bs : Subgroup G}
    {J : Subgroup (MulAut ↥Bs)} (A B : Subgroup (MulAut ↥Bs))
    (a b : Fin 3 → ↥J) (ha : (Subgroup.closure (Set.range a)).map J.subtype = A)
    (hb : (Subgroup.closure (Set.range b)).map J.subtype = B) :
    Subgroup.closure (Set.range a ∪ Set.range b) = ⊤ ↔ A ⊔ B = J := by
  constructor
  · intro h
    have hmap : (Subgroup.closure (Set.range a ∪ Set.range b)).map J.subtype = A ⊔ B := by
      rw [Subgroup.closure_union, Subgroup.map_sup, ha, hb]
    rw [h, Subgroup.map_top, Subgroup.range_subtype] at hmap
    exact hmap.symm
  · intro h
    apply Subgroup.map_injective (f := J.subtype) J.subtype_injective
    rw [Subgroup.closure_union, Subgroup.map_sup, ha, hb, h,
      Subgroup.map_top, Subgroup.range_subtype]

private theorem closure_union3_eq_top_iff {G : Type} [Group G] {Bs : Subgroup G}
    {J : Subgroup (MulAut ↥Bs)} (A B C : Subgroup (MulAut ↥Bs))
    (a b c : Fin 3 → ↥J)
    (ha : (Subgroup.closure (Set.range a)).map J.subtype = A)
    (hb : (Subgroup.closure (Set.range b)).map J.subtype = B)
    (hc : (Subgroup.closure (Set.range c)).map J.subtype = C) :
    Subgroup.closure (Set.range a ∪ Set.range b ∪ Set.range c) = ⊤ ↔ A ⊔ B ⊔ C = J := by
  constructor
  · intro h
    have hmap : (Subgroup.closure (Set.range a ∪ Set.range b ∪ Set.range c)).map J.subtype =
        A ⊔ B ⊔ C := by
      rw [Subgroup.closure_union, Subgroup.map_sup, Subgroup.closure_union,
        Subgroup.map_sup, ha, hb, hc]
    rw [h, Subgroup.map_top, Subgroup.range_subtype] at hmap
    exact hmap.symm
  · intro h
    apply Subgroup.map_injective (f := J.subtype) J.subtype_injective
    rw [Subgroup.closure_union, Subgroup.map_sup, Subgroup.closure_union,
      Subgroup.map_sup, ha, hb, hc, h, Subgroup.map_top, Subgroup.range_subtype]

theorem GGSecFiveRouteCfg.eq_bstar_of_F4 {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (h𝒦 : 𝒦.Nonempty) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hF : GGIsWeylMatrixF4 M) : B = Bs := by
  obtain ⟨K, hK⟩ := h𝒦
  obtain ⟨y, hN⟩ := hR.2.2.2.1.2 K hK
  have hfix : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizerJoin L Bs 𝒦, ψ b = b) → b = 1 := by
    intro b hb
    have hle : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 :=
      sup_le (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl))
        (ggAutomizer_le_ggAutomizerJoin (Or.inr hK))
    exact GGSecFiveRestHyp.eq_one_of_fix_pair hTBF hWI hR.1 hR.2.1 hN b
      (fun φ hφ => hb φ (hle hφ))
  have hW4 : GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizerJoin L Bs 𝒦) :=
    ggF4Small_weylOfType_F4 e hP hF
  have hcard_le : Nat.card Bs ≤ p ^ 4 := by
    simpa using SpJoinRefl.card_le_pow_of_weylOfType hW4 hfix
  obtain ⟨hp, -, -, -, -⟩ := hR.1.1.tableB_facts
  have hcardB : Nat.card B = p ^ LargeEvenTwoLocalRank p G :=
    hR.1.1.1.2.2.2.2.2.2.1.1.2.1
  have h4rank : 4 ≤ LargeEvenTwoLocalRank p G :=
    hR.1.1.1.2.2.2.2.2.1.2.2.2
  have hlow : p ^ 4 ≤ Nat.card B := by
    rw [hcardB]
    exact Nat.pow_le_pow_right hp.pos h4rank
  have hBBs : B ≤ Bs := hR.1.1.2.1.1
  exact Subgroup.eq_of_le_of_card_ge hBBs (hcard_le.trans hlow)

theorem GGSecFiveRouteCfg.nbr_typeA3B3_of_F4
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hTPn : GGNbrTablePNbrInputNarrow)
    (hA8 : GGForkA8NotReflInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hF : GGIsWeylMatrixF4 M)
    {K : Subgroup G} (hK : K ∈ 𝒦) :
    GGWeylOfType p (CoxeterMatrix.A 3) (ggAutomizer K Bs) ∨
      GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs) := by
  have hB : B = Bs := hR.eq_bstar_of_F4 hTBF hWI ⟨K, hK⟩ hP hF
  obtain ⟨y, hN⟩ := hR.2.2.2.1.2 K hK
  have hfl : GGFixLineComp Bs y K :=
    GGSecFiveRestHyp.fixLineComp_nbr hFC hR.1 hR.2.1 hB hN
  have hy1 : y ≠ 1 := hN.1.2.2.1
  have hfixJ : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizerJoin L Bs 𝒦, ψ b = b) → b = 1 := by
    intro b hb
    have hle : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 :=
      sup_le (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl))
        (ggAutomizer_le_ggAutomizerJoin (Or.inr hK))
    exact GGSecFiveRestHyp.eq_one_of_fix_pair hTBF hWI hR.1 hR.2.1 hN b
      (fun φ hφ => hb φ (hle hφ))
  obtain ⟨hp, hBs, -, -, h4⟩ := hR.1.1.tableB_facts
  obtain ⟨-, hp2, -⟩ :=
    (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have hNT : GGNoTransvection p Bs := hR.1.2.2.2.1
  have hA : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 :=
    ggAutomizer_le_ggAutomizerJoin (Or.inr hK)
  have hW : GGWeylReflectionGroup p (ggAutomizer K Bs) :=
    GGSecFiveRestHyp.weylReflectionGroup_nbr hX hTCJ hRig hTPn hA8 hraw hiso hR.1 hR.2.1 hN
  have : Fact p.Prime := ⟨hp⟩
  exact ggF4_weylOfType_A3_or_B3 hp2 hBs h4 hNT
    (fun _ hφ => ggAutomizerJoin_le_ggInduced_top L 𝒦 hφ) hP hF hfixJ hA hW hfl.mem hy1
    hfl.fix_iff

theorem ggF4LabelH3_holds
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hTPn : GGNbrTablePNbrInputNarrow)
    (hA8 : GGForkA8NotReflInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) : GGF4LabelH3 := by
  classical
  intro G _ _ p B Bs x L D J ks hS
  obtain ⟨hR, -, hPres, hA3, hspan⟩ := hS
  obtain ⟨ι, M, e, hP, hF⟩ := hPres
  have hW4 : GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizerJoin L Bs ks) :=
    ggF4Small_weylOfType_F4 e hP hF
  have hne : ks.Nonempty := ggF4Small_ks_nonempty hW4 hA3
  have hcard_le : ks.card ≤ 2 := hR.2.2.2.1.1
  have hcard_ne1 : ks.card ≠ 1 := by
    rintro hcard1
    obtain ⟨K, rfl⟩ := Finset.card_eq_one.mp hcard1
    exact hspan K (Finset.mem_singleton_self K) (by simp [ggAutomizerJoin])
  have hcard2 : ks.card = 2 := by have := Finset.card_pos.mpr hne; omega
  obtain ⟨K₁, K₂, hne12, hks_eq⟩ := Finset.card_eq_two.mp hcard2
  obtain ⟨hp, hBs, -, -, h4⟩ := hR.1.1.tableB_facts
  obtain ⟨-, hp2, -⟩ :=
    (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  obtain ⟨cs, hcs⟩ := ggF4_exists_coxeterSystem hp hp2 hBs hR.1.2.2.2.1
    (ggAutomizerJoin_le_ggInduced_top L ks) hP hF
  obtain ⟨eA, hPA_refl⟩ := hA3
  have hPA : GGCoxeterPres p (ggAutomizer L Bs) (CoxeterMatrix.A 3) eA :=
    ⟨CFSG.TwoNodeSmall.pws_ggIsWeylMatrix_A 3 (by norm_num), hPA_refl⟩
  obtain ⟨a, ha_refl, ha_ord, ha_clo⟩ := ggF4_presentation_family hcs le_sup_left hPA
  have ha01 : orderOf (a 0 * a 1) = 3 := by simpa [CoxeterMatrix.A] using ha_ord 0 1
  have ha12 : orderOf (a 1 * a 2) = 3 := by simpa [CoxeterMatrix.A] using ha_ord 1 2
  have ha02 : orderOf (a 0 * a 2) = 2 := by simpa [CoxeterMatrix.A] using ha_ord 0 2
  have hK1_mem : K₁ ∈ ks := by rw [hks_eq]; exact Finset.mem_insert_self _ _
  have hK2_mem : K₂ ∈ ks := by rw [hks_eq]; simp
  have hK1_type := hR.nbr_typeA3B3_of_F4 hX hTCJ hRig hTBF hWI hTPn hA8 hraw hiso hFC hP hF hK1_mem
  have hK2_type := hR.nbr_typeA3B3_of_F4 hX hTCJ hRig hTBF hWI hTPn hA8 hraw hiso hFC hP hF hK2_mem
  have hK1J : ggAutomizer K₁ Bs ≤ ggAutomizerJoin L Bs ks :=
    ggAutomizer_le_ggAutomizerJoin (Or.inr hK1_mem)
  have hK2J : ggAutomizer K₂ Bs ≤ ggAutomizerJoin L Bs ks :=
    ggAutomizer_le_ggAutomizerJoin (Or.inr hK2_mem)
  obtain ⟨b, hb_refl, hb01, hb12, hb02, hb_clo, hbB⟩ :=
    ggF4_exists_family_of_typeA3B3 hcs hK1J hK1_type
  obtain ⟨c, hc_refl, hc01, hc12, hc02, hc_clo, hcB⟩ :=
    ggF4_exists_family_of_typeA3B3 hcs hK2J hK2_type
  have hab : Subgroup.closure (Set.range a ∪ Set.range b) ≠ ⊤ := fun h =>
    hspan K₁ hK1_mem ((ggF4_closure_union_eq_top_iff (ggAutomizer L Bs)
      (ggAutomizer K₁ Bs) a b ha_clo hb_clo).mp h)
  have hac : Subgroup.closure (Set.range a ∪ Set.range c) ≠ ⊤ := fun h =>
    hspan K₂ hK2_mem ((ggF4_closure_union_eq_top_iff (ggAutomizer L Bs)
      (ggAutomizer K₂ Bs) a c ha_clo hc_clo).mp h)
  have hjoin : ggAutomizerJoin L Bs ks =
      ggAutomizer L Bs ⊔ ggAutomizer K₁ Bs ⊔ ggAutomizer K₂ Bs := by
    simp [hks_eq, ggAutomizerJoin, iSup_or, iSup_sup_eq, sup_assoc]
  have habc : Subgroup.closure (Set.range a ∪ Set.range b ∪ Set.range c) = ⊤ :=
    (closure_union3_eq_top_iff (ggAutomizer L Bs) (ggAutomizer K₁ Bs)
      (ggAutomizer K₂ Bs) a b c ha_clo hb_clo hc_clo).mpr hjoin.symm
  have hend := ggF4A3Residual_endpoints cs ha_refl hb_refl hc_refl ha01 ha12 ha02
    hb01 hb12 hb02 hc01 hc12 hab hac habc
  have hK1_B : GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K₁ Bs) := hbB hend.1
  have hK2_B : GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K₂ Bs) := hcB hend.2.1
  have hjoinBC : ggAutomizer K₁ Bs ⊔ ggAutomizer K₂ Bs = ggAutomizerJoin L Bs ks :=
    (ggF4_closure_union_eq_top_iff (ggAutomizer K₁ Bs) (ggAutomizer K₂ Bs)
      b c hb_clo hc_clo).mp hend.2.2
  refine ⟨K₁, K₂, ?_, hne12, hK1_B, hK2_B, hjoinBC⟩
  intro K
  rw [hks_eq]
  simp [Finset.mem_insert, Finset.mem_singleton]

end CFSG.StandardType

end
