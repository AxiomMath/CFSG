module

public import CFSG.Quasithin.Vol2.Ch11SecCB51Core
public import CFSG.Quasithin.Vol2.Ch11SecCB51Trans
public import CFSG.Quasithin.Vol2.Ch11SecCB51Sum
public import CFSG.Quasithin.Vol2.Ch11SecCB51Ord
public import CFSG.Quasithin.Vol2.Ch11SecCB51Facts
public import CFSG.Quasithin.Background.InternalSecIso

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.InternalSec CFSG.QuasithinUnique
open CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def SumTwoNatural (L U : Subgroup G) (n : ℕ) : Prop :=
  ∃ W₁ W₂ : Subgroup G, W₁ ≤ U ∧ W₂ ≤ U ∧
    L ≤ Subgroup.normalizer (W₁ : Set G) ∧ L ≤ Subgroup.normalizer (W₂ : Set G) ∧
    W₁ ⊓ W₂ = ⊥ ∧ W₁ ⊔ W₂ = U ∧
    (∃ _ : IsMulCommutative ↥W₁, BinaryNaturalSL (V := ↥W₁) (autOn L W₁) ⊤ ⊥ 3 n) ∧
    (∃ _ : IsMulCommutative ↥W₂, BinaryNaturalSL (V := ↥W₂) (autOn L W₂) ⊤ ⊥ 3 n) ∧
    IsXSectionIso₂ L W₁ ⊥ W₂ ⊥

namespace B51

theorem isMulCommutative_of_le {U W : Subgroup G} [IsMulCommutative ↥W] (hUW : U ≤ W) :
    IsMulCommutative ↥U :=
  IsMulCommutative.of_comm fun a b => Subtype.ext (show (a : G) * b = b * a from
    congrArg Subtype.val (mul_comm (⟨a, hUW a.2⟩ : ↥W) ⟨b, hUW b.2⟩))

theorem inf_subgroupOf_self (Z U : Subgroup G) : (Z ⊓ U).subgroupOf U = Z.subgroupOf U := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩

theorem inf_subgroupOf_eq (A B W : Subgroup G) :
    A.subgroupOf W ⊓ B.subgroupOf W = (A ⊓ B).subgroupOf W :=
  (Subgroup.comap_inf A B W.subtype).symm

theorem kind_cases [Finite G] {T L I : Subgroup G} {n : ℕ} {Y W : Subgroup G}
    (h1102 : Stmt11_0_2) (h : BridgeHyp T L I n Y W) :
    (KindSL3 L (fsuV T I) n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
        Nonempty (↥(autOn L W) ≃* Matrix.SpecialLinearGroup (Fin 3) F)) ∨
      (KindSp4 L (fsuV T I) n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
        Nat.card F = 2 ^ n ∧ Nonempty (↥(autOn L W) ≃* ↥(StatedSp 2 F))) ∨
      (KindG2 L (fsuV T I) n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
        Nat.card F = 2 ^ n ∧ Nonempty (↥(autOn L W) ≃* ↥⁅quasithinG2 F, quasithinG2 F⁆)) := by
  obtain ⟨e₀⟩ := h.nonempty_autOnEquiv h1102
  obtain ⟨_, -, -, -, hk⟩ := h1102 G T L I n h.hyp
  rcases hk with ⟨F, _, _, hF, ⟨e⟩, -⟩ | ⟨F, _, _, hF, ⟨e⟩, -⟩ | ⟨F, _, _, hF, ⟨e⟩, -⟩
  · exact Or.inl ⟨⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩, F, inferInstance, inferInstance,
      hF, ⟨e₀.trans e⟩⟩
  · exact Or.inr (Or.inl ⟨⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩, F, inferInstance,
      inferInstance, hF, ⟨e₀.trans e⟩⟩)
  · exact Or.inr (Or.inr ⟨⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩, F, inferInstance,
      inferInstance, hF, ⟨e₀.trans e⟩⟩)

variable [Finite G] {T L I : Subgroup G} {n : ℕ} {Y W : Subgroup G} [IsMulCommutative ↥W]

omit [IsMulCommutative ↥W] in
theorem not_surjective_L45 (h1102 : Stmt11_0_2) (hG2 : SecA.FactG2DerivedOrder)
    (h : BridgeHyp T L I n Y W) {m : ℕ} (hm : m = 4 ∨ m = 5)
    (π : ↥(StatedSL m (ZMod 2)) →* ↥(autOn L W)) : ¬ Function.Surjective π := by
  intro hπ
  have hn : 2 ≤ n := h.hyp.one_lt
  rcases kind_cases h1102 h with ⟨-, F, _, _, hF, ⟨e⟩⟩ | ⟨-, F, _, _, hF, ⟨e⟩⟩ |
      ⟨-, F, _, _, hF, ⟨e⟩⟩
  · exact not_surjective_L45_SL3 hm hn hF (e.toMonoidHom.comp π) (e.surjective.comp hπ)
  · exact not_surjective_L45_Sp4 hm hn hF (e.toMonoidHom.comp π) (e.surjective.comp hπ)
  · exact not_surjective_L45_G2 hG2 hm hn hF (e.toMonoidHom.comp π) (e.surjective.comp hπ)

theorem not_case1iii (h1102 : Stmt11_0_2) (hG2 : SecA.FactG2DerivedOrder)
    (h : BridgeHyp T L I n Y W) {J : Subgroup (MulAut ↥W)} {m : ℕ}
    (hiii : B51Case1iii J (autOn L W) m) : False := by
  obtain ⟨-, hm, π, U₁, U₂, -, h₁, -⟩ := hiii
  exact not_surjective_L45 h1102 hG2 h hm π h₁.1

theorem not_case1iv (h1102 : Stmt11_0_2) (hG2 : SecA.FactG2DerivedOrder)
    (h : BridgeHyp T L I n Y W) {J : Subgroup (MulAut ↥W)} (hiv : B51Case1iv J (autOn L W)) :
    False := by
  obtain ⟨-, m, hm, k, hk, -, I', π, -, -, -, hreal⟩ := hiv
  exact not_surjective_L45 h1102 hG2 h hm π (hreal ⟨0, by omega⟩).1

theorem natural_of_case1i (h1102 : Stmt11_0_2) (hKF : KindModuleFacts)
    (h : BridgeHyp T L I n Y W) {J : Subgroup (MulAut ↥W)} (hi : B51Case1i J (autOn L W))
    {U : Subgroup G} (hU : ⁅W, L⁆ = U) :
    ∃ _ : IsMulCommutative ↥U,
      (KindSL3 L (fsuV T I) n ∧ BinaryNaturalSL (V := ↥U) (autOn L U) ⊤
          ((Subgroup.centralizer (L : Set G)).subgroupOf U) 3 n) ∨
      (KindSp4 L (fsuV T I) n ∧ BinaryNaturalSp4 (V := ↥U) (autOn L U) ⊤
          ((Subgroup.centralizer (L : Set G)).subgroupOf U) n) ∨
      (KindG2 L (fsuV T I) n ∧ G2Natural (V := ↥U) (autOn L U) ⊤
          ((Subgroup.centralizer (L : Set G)).subgroupOf U) n) := by
  subst hU
  have hn : 2 ≤ n := h.hyp.one_lt
  have hLW := h.le_normW
  have hUW : ⁅W, L⁆ ≤ W := by
    rw [← map_commV_autOn hLW]
    exact Subgroup.map_subtype_le _
  have hLU : L ≤ Subgroup.normalizer ((⁅W, L⁆ : Subgroup G) : Set G) :=
    le_sup_right.trans (A3.sup_le_normalizer_commutator W L)
  have : IsMulCommutative ↥⁅W, L⁆ := isMulCommutative_of_le hUW
  have hW2 : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using h.isElemAbelian.2 w w.2)
  have hB := hi.2.1
  rw [commV_autOn hLW, fixV_autOn hLW, inf_subgroupOf_eq] at hB
  rcases kind_cases h1102 h with ⟨hk, F, _, _, hF, he⟩ | ⟨hk, F, _, _, hF, he⟩ |
      ⟨hk, F, _, _, hF, he⟩
  · refine ⟨this, Or.inl ⟨hk, ?_⟩⟩
    have h2 := binaryNaturalSL_res hLW hLU hUW (hKF.1 F n hn hF ↥W hW2 _ _ _ he hB)
    rwa [inf_subgroupOf_self] at h2
  · refine ⟨this, Or.inr (Or.inl ⟨hk, ?_⟩)⟩
    have h2 := binaryNaturalSp4_res hLW hLU hUW (hKF.2.1 F n hn hF ↥W hW2 _ _ _ he hB)
    rwa [inf_subgroupOf_self] at h2
  · refine ⟨this, Or.inr (Or.inr ⟨hk, ?_⟩)⟩
    have h2 := g2Natural_res hLW hLU hUW (hKF.2.2.1 F n hn hF ↥W hW2 _ _ _ he hB)
    rwa [inf_subgroupOf_self] at h2

theorem sumTwoNatural_of_case1ii (h1102 : Stmt11_0_2) (hKF : KindModuleFacts)
    (h : BridgeHyp T L I n Y W) {J : Subgroup (MulAut ↥W)} (hii : B51Case1ii J (autOn L W))
    {U : Subgroup G} (hU : ⁅W, L⁆ = U) :
    KindSL3 L (fsuV T I) n ∧ U ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
      SumTwoNatural L U n := by
  subst hU
  have hn : 2 ≤ n := h.hyp.one_lt
  have hLW := h.le_normW
  have hUW : ⁅W, L⁆ ≤ W := by
    rw [← map_commV_autOn hLW]
    exact Subgroup.map_subtype_le _
  have hW2 : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using h.isElemAbelian.2 w w.2)
  obtain ⟨-, n', K, _, _, hK, I', π, hind, hsup, hreal, -, -⟩ := hii
  have hπ' : Function.Surjective (π.comp (specialLinearGroupEquivStatedSL 3 K).toMonoidHom) :=
    (hreal 0).1.comp (specialLinearGroupEquivStatedSL 3 K).surjective
  rcases kind_cases h1102 h with ⟨hk, F, _, _, hF, ⟨e⟩⟩ | ⟨-, F, _, _, hF, ⟨e⟩⟩ |
      ⟨-, F, _, _, hF, ⟨e⟩⟩
  · have h01 : I' 0 ⊔ I' 1 = commV (autOn L W) := by
      rw [← hsup]
      refine le_antisymm (sup_le (le_iSup I' 0) (le_iSup I' 1)) (iSup_le fun i => ?_)
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    have hdisj : I' 0 ⊓ I' 1 = ⊥ := disjoint_iff.mp (hind.pairwiseDisjoint (by decide))
    have hinv : ∀ i, ∀ σ ∈ autOn L W, ∀ u ∈ I' i, σ u ∈ I' i :=
      fun i σ hσ u hu => (hreal i).2.2.2.1 ⟨σ, hσ⟩ u hu
    set W₁ : Subgroup G := (I' 0).map W.subtype with hW₁
    set W₂ : Subgroup G := (I' 1).map W.subtype with hW₂
    have hW₁W : W₁ ≤ W := Subgroup.map_subtype_le _
    have hW₂W : W₂ ≤ W := Subgroup.map_subtype_le _
    have hI₁ : W₁.subgroupOf W = I' 0 :=
      Subgroup.comap_map_eq_self_of_injective W.subtype_injective _
    have hI₂ : W₂.subgroupOf W = I' 1 :=
      Subgroup.comap_map_eq_self_of_injective W.subtype_injective _
    have hU : W₁ ⊔ W₂ = ⁅W, L⁆ := by
      rw [hW₁, hW₂, ← Subgroup.map_sup, h01, map_commV_autOn hLW]
    have hLW₁ : L ≤ Subgroup.normalizer (W₁ : Set G) := le_normalizer_map_of_inv hLW (hinv 0)
    have hLW₂ : L ≤ Subgroup.normalizer (W₂ : Set G) := le_normalizer_map_of_inv hLW (hinv 1)
    have hnat : ∀ i : Fin 2, BinaryNaturalSL (autOn L W) (I' i) ⊥ 3 n := fun i =>
      hKF.1 F n hn hF ↥W hW2 _ _ _ ⟨e⟩
        (Or.inr (Or.inl ⟨n', K, inferInstance, inferInstance, hK, π, hreal i⟩))
    have hc₁ : IsMulCommutative ↥W₁ := isMulCommutative_of_le hW₁W
    have hc₂ : IsMulCommutative ↥W₂ := isMulCommutative_of_le hW₂W
    have hnat₁ : BinaryNaturalSL (V := ↥W₁) (autOn L W₁) ⊤ ⊥ 3 n := by
      have h3 : BinaryNaturalSL (autOn L W) (W₁.subgroupOf W) ((⊥ : Subgroup G).subgroupOf W)
          3 n := by
        rw [hI₁, Subgroup.bot_subgroupOf]
        exact hnat 0
      have h4 := binaryNaturalSL_res hLW hLW₁ hW₁W h3
      rwa [Subgroup.bot_subgroupOf] at h4
    have hnat₂ : BinaryNaturalSL (V := ↥W₂) (autOn L W₂) ⊤ ⊥ 3 n := by
      have h3 : BinaryNaturalSL (autOn L W) (W₂.subgroupOf W) ((⊥ : Subgroup G).subgroupOf W)
          3 n := by
        rw [hI₂, Subgroup.bot_subgroupOf]
        exact hnat 1
      have h4 := binaryNaturalSL_res hLW hLW₂ hW₂W h3
      rwa [Subgroup.bot_subgroupOf] at h4
    have hiso : IsXSectionIso₂ L W₁ ⊥ W₂ ⊥ := by
      refine isXSectionIso₂_of_secIsoL hW₁W hW₂W hLW hLW₁ hLW₂ ?_
      rw [hI₁, hI₂]
      exact secIsoL_of_realizesVia (hreal 0) (hreal 1)
    have hinf : W₁ ⊓ W₂ = ⊥ := by
      rw [hW₁, hW₂, ← Subgroup.map_inf_eq _ _ _ W.subtype_injective, hdisj, Subgroup.map_bot]
    have hfix : fixV (autOn L W) ⊓ commV (autOn L W) = ⊥ := by
      rw [← h01]
      exact fixV_inf_sup_eq_bot (hinv 0) (hinv 1) (fixV_inf_eq_bot_of_nat (hreal 0))
        (fixV_inf_eq_bot_of_nat (hreal 1)) hdisj
    refine ⟨hk, ?_, W₁, W₂, le_sup_left.trans hU.le, le_sup_right.trans hU.le, hLW₁, hLW₂,
      hinf, hU, ⟨hc₁, hnat₁⟩, ⟨hc₂, hnat₂⟩, hiso⟩
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hUW hx.1⟩ : ↥W) ∈ fixV (autOn L W) ⊓ commV (autOn L W) := by
      rw [fixV_autOn hLW, commV_autOn hLW]
      exact ⟨hx.2, hx.1⟩
    rw [hfix, Subgroup.mem_bot] at hx'
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hx'
  · exact (not_surjective_SL3_Sp4 hK hn hF (e.toMonoidHom.comp _)
      (e.surjective.comp hπ')).elim
  · exact (not_surjective_SL3_G2 hKF.2.2.2 hK hn hF (e.toMonoidHom.comp _)
      (e.surjective.comp hπ')).elim

end B51

end CFSG.Quasithin.Vol2.Ch11.SecC
