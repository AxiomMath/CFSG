module

public import CFSG.RankThree.PartTwo.Sec15.Ronan152SixBigDefs
public import CFSG.RankThree.PartTwo.Sec15.Item153TwinProofTools
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec15

variable {G : Type} [Group G]

theorem IsJ2Type.big152 {Y : Subgroup G} (h : IsJ2Type Y) : Big152 Y := by
  obtain ⟨e⟩ := h
  unfold Big152
  rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_nativeJ2]
  norm_num

theorem IsJ2Type.map_conj {Y : Subgroup G} (h : IsJ2Type Y) (g : G) :
    IsJ2Type (Y.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨e⟩ := h
  let φ : ↥Y ≃* ↥(Y.map (MulAut.conj g).toMonoidHom) :=
    Y.equivMapOfInjective _ (MulAut.conj g).injective
  exact ⟨(QuotientGroup.congr _ _ φ (CFSG.pCore_map_iso 2 φ)).symm.trans e⟩

end CFSG.RankThree.PartTwo.Sec15

namespace CFSG.RankThree.PartTwo.Sec15.Ronan152Six

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec15.Proof153Twin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Members

variable {A : Subgroup G} {c : G} {L : Subgroup G}

theorem mem_thetaComponentsIn_of_big (h : Sec14Std G A c L) (h152 : Item152Big A (lB A))
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) (hYb : Big152 Y) {M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G)) :
    Y ∈ thetaComponentsIn M := by
  obtain ⟨hYM, -, hM2, hF⟩ := facts_of_mem_maximalTwoLocalsContaining h hM
  obtain ⟨X, hX, hYX, hX0⟩ := h152 Y hY.prop.1 hYb M hM2 hYM hF
  rwa [hY.eq_of_le hX0 hYX]

theorem map_conj_eq_of_hasFaithfulE9_big (h : Sec14Std G A c L) (h152 : Item152Big A (lB A))
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) (hYb : Big152 Y) (hE : HasFaithfulE9 Y)
    {M : Subgroup G} (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G))
    {t : G}
    (ht : t ∈ M) : Y.map (MulAut.conj t).toMonoidHom = Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  obtain ⟨hYM, -, -, -⟩ := facts_of_mem_maximalTwoLocalsContaining h hM
  obtain ⟨Y', hY', hYY'⟩ := mem_thetaComponentsIn_of_big h h152 hY hYb hM
  change Y'.map M.subtype = Y at hYY'
  set σ : ↥M ≃* ↥M := MulAut.conj (⟨t, ht⟩ : M) with hσ
  have hσY : (Y'.map σ.toMonoidHom).map M.subtype = Y.map (MulAut.conj t).toMonoidHom := by
    rw [← hYY', Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hY'' : Y'.map σ.toMonoidHom ∈ thetaComponents 3 ↥M :=
    map_mulEquiv_mem_thetaComponents Nat.prime_three σ hY'
  have hne' : Y' ≠ Y'.map σ.toMonoidHom := by
    intro heq
    apply hne
    rw [← hσY, ← heq]
    exact hYY'
  have hcθ := commutator_le_of_mem_thetaComponents hY' hY'' hne'
  obtain ⟨-, hθc, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥M) Nat.prime_three
  have : (aschbacherSolvableCore 3 ↥M).Normal := Subgroup.normal_of_characteristic _
  obtain ⟨E, hEY, hEab, hE9, hEc⟩ := hE
  set E₁ : Subgroup ↥M := E.subgroupOf M with hE₁
  have hE₁map : E₁.map M.subtype = E := by
    rw [hE₁, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hEY.trans hYM)]
  have hE₁Y' : E₁ ≤ Y' := by
    rw [← Subgroup.map_le_map_iff_of_injective M.subtype_injective, hE₁map, hYY']
    exact hEY
  have hE₁card : Nat.card E₁ = 9 := by
    rw [← hE9, ← hE₁map, Subgroup.card_map_of_injective M.subtype_injective]
  have hE₁ab : CFSG.Open.IsElemAbelian 3 E₁ := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · have ha : ((a : ↥M) : G) ∈ E := Subgroup.mem_subgroupOf.mp a.2
      have hb : ((b : ↥M) : G) ∈ E := Subgroup.mem_subgroupOf.mp b.2
      have hab : ((a : ↥M) : G) * ((b : ↥M) : G) = ((b : ↥M) : G) * ((a : ↥M) : G) :=
        congrArg Subtype.val (hEab.1.is_comm.comm (⟨_, ha⟩ : E) ⟨_, hb⟩)
      apply Subtype.ext
      apply Subtype.ext
      exact hab
    · exact Subtype.ext (hEab.2 _ (Subgroup.mem_subgroupOf.mp hx))
  set E₂ : Subgroup ↥M := E₁.map σ.toMonoidHom with hE₂
  have hE₂ab : CFSG.Open.IsElemAbelian 3 E₂ :=
    CFSG.SectionRank.isElemAbelian_map hE₁ab σ.toMonoidHom
  have hE₂card : Nat.card E₂ = 9 := by
    rw [hE₂, Subgroup.card_map_of_injective σ.injective, hE₁card]
  have hE₂Y : E₂ ≤ Y'.map σ.toMonoidHom := Subgroup.map_mono hE₁Y'
  have hc : ⁅E₁, E₂⁆ ≤ aschbacherSolvableCore 3 ↥M :=
    (Subgroup.commutator_mono hE₁Y' hE₂Y).trans hcθ
  have hd : ∀ x ∈ E₁, ∀ y ∈ E₂, x * y⁻¹ ∈ aschbacherSolvableCore 3 ↥M → x = 1 := by
    intro x hx y hy hxy
    have hxz : ∀ z ∈ Y', ⁅x, z⁆ ∈ aschbacherSolvableCore 3 ↥M := by
      intro z hz
      have hyz : ⁅z, y⁆ ∈ aschbacherSolvableCore 3 ↥M :=
        hcθ (Subgroup.commutator_mem_commutator hz (hE₂Y hy))
      have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M) x =
          QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M) y := by
        have h1' : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M) (x * y⁻¹) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr hxy
        rwa [map_mul, map_inv, mul_inv_eq_one] at h1'
      have h2 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M) ⁅z, y⁆ = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hyz
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
      have h3 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M) ⁅x, z⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, h1]
        exact h2.symm
      exact (QuotientGroup.eq_one_iff _).mp h3
    have hxE : ((x : ↥M) : G) ∈ E := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨hθN, hθs, hθ3'⟩ := map_aschbacherSolvableCore_facts M
    have hxG : ((x : ↥M) : G) ∈
        Late.sectionCentralizer E Y ((aschbacherSolvableCore 3 ↥Y).map Y.subtype) := by
      refine ⟨hxE, fun z hz => ?_⟩
      rw [← hYY'] at hz
      obtain ⟨z', hz', rfl⟩ := hz
      have hxY : x ∈ Y' := hE₁Y' hx
      have hmemY : ⁅x, z'⁆ ∈ Y' := by
        rw [commutatorElement_def]
        exact Y'.mul_mem (Y'.mul_mem (Y'.mul_mem hxY hz') (Y'.inv_mem hxY)) (Y'.inv_mem hz')
      have hmem : ((⁅x, z'⁆ : ↥M) : G) ∈
          (aschbacherSolvableCore 3 ↥M).map M.subtype ⊓ Y :=
        ⟨Subgroup.mem_map_of_mem _ (hxz z' hz'), hYY' ▸ Subgroup.mem_map_of_mem _ hmemY⟩
      have := inf_le_map_aschbacherSolvableCore (hYM.trans hθN) hθs hθ3' hmem
      rwa [commutatorElement_def] at this
    have hx1 : ((x : ↥M) : G) = 1 := hEc hxG
    exact Subtype.ext hx1
  have h4 := four_le_pRank_of_commutator_le (aschbacherSolvableCore 3 ↥M) hθ3 hE₁ab hE₂ab
    hE₁card hE₂card hc hd
  have h4' : 4 ≤ CFSG.Open.pRank 3 M := by
    refine h4.trans ?_
    have := CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective 3
      Nat.prime_three M.subtype M.subtype_injective ⊤
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
  have h3 : CFSG.Open.pRank 3 M ≤ 3 :=
    (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) M hM.1.1).trans h.toTheoremFourHyp.evenRank_eq.le
  omega

theorem false_of_four_conj_big (h : Sec14Std G A c L) (h152 : Item152Big A (lB A))
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) (hYb : Big152 Y)
    (hN : HasNonCentralThree Y) {M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G))
    (g : Fin 4 → G) (hgM : ∀ i, g i ∈ M)
    (hdist : ∀ i j : Fin 4, i ≠ j → Y.map (MulAut.conj (g i)).toMonoidHom ≠
      Y.map (MulAut.conj (g j)).toMonoidHom) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hYM, -, -, -⟩ := facts_of_mem_maximalTwoLocalsContaining h hM
  obtain ⟨Y', hY', hYY'⟩ := mem_thetaComponentsIn_of_big h h152 hY hYb hM
  change Y'.map M.subtype = Y at hYY'
  set σ : Fin 4 → (↥M ≃* ↥M) := fun i => MulAut.conj (⟨g i, hgM i⟩ : M) with hσ
  have hσY : ∀ i, (Y'.map (σ i).toMonoidHom).map M.subtype =
      Y.map (MulAut.conj (g i)).toMonoidHom := by
    intro i
    rw [← hYY', Subgroup.map_map, Subgroup.map_map]
    congr 1
  obtain ⟨x, hxY, hx3, y, hyY, hxy⟩ := hN
  have hxY0 := hxY
  have hyY0 := hyY
  rw [← hYY'] at hxY0 hyY0
  obtain ⟨x', hxY', rfl⟩ := hxY0
  obtain ⟨y', hyY', rfl⟩ := hyY0
  obtain ⟨hθN, hθs, hθ3⟩ := map_aschbacherSolvableCore_facts M
  obtain ⟨-, hθc, hθ3', -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥M) Nat.prime_three
  have hxyM : ⁅x', y'⁆ ∉ aschbacherSolvableCore 3 ↥M := by
    intro hmem
    apply hxy
    have hmemG : (x' : G) * y' * (x' : G)⁻¹ * (y' : G)⁻¹ ∈
        (aschbacherSolvableCore 3 ↥M).map M.subtype ⊓ Y := by
      refine ⟨?_, Y.mul_mem (Y.mul_mem (Y.mul_mem hxY hyY) (Y.inv_mem hxY)) (Y.inv_mem hyY)⟩
      have := Subgroup.mem_map_of_mem M.subtype hmem
      rwa [commutatorElement_def] at this
    exact inf_le_map_aschbacherSolvableCore (hYM.trans hθN) hθs hθ3 hmemG
  have h4 := four_le_pRank_of_thetaComponents (fun i => Y'.map (σ i).toMonoidHom)
    (fun i => map_mulEquiv_mem_thetaComponents Nat.prime_three (σ i) hY')
    (fun i j hij he => hdist i j hij (by rw [← hσY i, ← hσY j, he]))
    (fun i => σ i x') (fun i => σ i y')
    (fun i => Subgroup.mem_map_of_mem _ hxY') (fun i => Subgroup.mem_map_of_mem _ hyY')
    (fun i => by
      rw [← map_pow]
      have : x' ^ 3 = 1 := Subtype.ext hx3
      rw [this, map_one])
    (fun i hmem => by
      apply hxyM
      rw [← map_commutatorElement] at hmem
      have hchar : (aschbacherSolvableCore 3 ↥M).map (σ i).toMonoidHom =
          aschbacherSolvableCore 3 ↥M :=
        Subgroup.characteristic_iff_map_eq.mp hθc (σ i)
      have := Subgroup.mem_map_of_mem (σ i).symm.toMonoidHom hmem
      rw [← hchar, Subgroup.map_map] at this
      simpa using this)
  have h4' : 4 ≤ CFSG.Open.pRank 3 M := by
    refine h4.trans ?_
    have := CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective 3
      Nat.prime_three M.subtype M.subtype_injective ⊤
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
  have h3 : CFSG.Open.pRank 3 M ≤ 3 :=
    (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) M hM.1.1).trans h.toTheoremFourHyp.evenRank_eq.le
  omega

theorem le_normalizer_of_isPerfect_of_le_big (h : Sec14Std G A c L)
    (h152 : Item152Big A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) (hYb : Big152 Y)
    {M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G))
    {K : Subgroup G} (hK : Group.IsPerfect ↥K) (hKM : K ≤ M) :
    K ≤ Subgroup.normalizer (Y : Set G) := by
  have hN := hasNonCentralThree_of_mem_scriptY4 hY.prop.1
  set T : Subgroup ↥K := (Subgroup.normalizer (Y : Set G)).subgroupOf K with hT
  suffices hTtop : T = ⊤ by
    intro k hk
    have hkT : (⟨k, hk⟩ : ↥K) ∈ T := hTtop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hkT
  by_contra hTne
  have h4 : 4 ≤ T.index := by
    by_contra hlt
    exact hTne (Subgroup.index_eq_one.mp (index_eq_one_of_isPerfect hK T (by omega)))
  have := Fintype.ofFinite (↥K ⧸ T)
  obtain ⟨f⟩ : Nonempty (Fin 4 ↪ ↥K ⧸ T) := by
    refine Function.Embedding.nonempty_of_card_le ?_
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    exact h4
  set k : Fin 4 → ↥K := fun i => (f i).out with hk
  have hkf : ∀ i, (QuotientGroup.mk (k i) : ↥K ⧸ T) = f i := fun i => QuotientGroup.out_eq' _
  refine false_of_four_conj_big h h152 hY hYb hN hM (fun i => (k i : G)) (fun i => hKM (k i).2) ?_
  intro i j hij heq
  apply hij
  apply f.injective
  have hmem : (k i)⁻¹ * k j ∈ T := by
    rw [hT, Subgroup.mem_subgroupOf]
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    show Y.map (MulAut.conj (((k i)⁻¹ * k j : ↥K) : G)).toMonoidHom = Y
    rw [Subgroup.coe_mul, Subgroup.coe_inv, ← Late.map_conj_map_conj, ← heq,
      Late.map_conj_map_conj, inv_mul_cancel, Late.map_conj_one]
  rw [← hkf i, ← hkf j]
  exact QuotientGroup.eq.mpr hmem

theorem n155_mem_maximalTwoLocalsContaining_j2 (h153 : Item153MainJ2 A (lB A))
    {K : Subgroup G} (hK : K ∈ scriptY0Star A (lB A)) (hKJ : IsJ2Type K) :
    n155 A K ∈ CFSG.maximalTwoLocalsContaining ((K ⊔ A : Subgroup G) : Set G) := by
  rw [(h153 K hK hKJ).1]
  exact Set.mem_singleton _

theorem le_normalizer_of_isPerfect_of_le_n155_j2 (h : Sec14Std G A c L)
    (h152 : Item152Big A (lB A)) (h153 : Item153MainJ2 A (lB A)) {K : Subgroup G}
    (hK : K ∈ scriptY0Star A (lB A)) (hKJ : IsJ2Type K) {J : Subgroup G}
    (hJp : Group.IsPerfect ↥J) (hJN : J ≤ n155 A K) : J ≤ Subgroup.normalizer (K : Set G) :=
  le_normalizer_of_isPerfect_of_le_big h h152 hK (IsJ2Type.big152 hKJ)
    (n155_mem_maximalTwoLocalsContaining_j2 h153 hK hKJ) hJp hJN

end Members

end CFSG.RankThree.PartTwo.Sec15.Ronan152Six
