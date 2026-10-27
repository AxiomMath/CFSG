module

public import CFSG.Blueprint.Catalog
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Open.RankThreeDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Blueprint (LieModel)
open CFSG.Open

@[expose] def Pos (K : Type) [Group K] [Finite K] (Z X : Subgroup K) : Prop :=
  Nat.card Z = 3 ∧ Z ≤ X ∧ X ≤ Subgroup.centralizer (Z : Set K) ∧
  (X.subgroupOf (Subgroup.centralizer (Z : Set K))).IsSubnormal ∧
  CFSG.Open.IsQuasisimple ↥X ∧ Nat.card (Subgroup.center ↥X) = 3 ∧
  (LieModel (↥X ⧸ Subgroup.center ↥X) .PSL 3 2 2 ∨ LieModel (↥X ⧸ Subgroup.center ↥X) .PSU 3 2 3)

@[expose] def ClassUnique (K : Type) [Group K] [Finite K] : Prop :=
  ∀ Z₁ X₁ Z₂ X₂ : Subgroup K, Pos K Z₁ X₁ → Pos K Z₂ X₂ → ∃ k : K, rankThreeConj k Z₁ = Z₂

@[expose] def CompUnique (K : Type) [Group K] [Finite K] : Prop :=
  ∀ Z X₁ X₂ : Subgroup K, Pos K Z X₁ → Pos K Z X₂ → X₁ = X₂

@[expose] def Gen (K : Type) [Group K] [Finite K] : Prop :=
  ∃ Z₀ X₀ E₀ : Subgroup K, Pos K Z₀ X₀ ∧ E₀ ≤ X₀ ∧ IsElemAbelian 3 E₀ ∧ Nat.card E₀ = 9 ∧
    ⨆ (F : Subgroup K) (_ : F ≤ E₀) (_ : Nat.card F = 3), Subgroup.centralizer (F : Set K) = ⊤

@[expose] def RowLeaves (K : Type) [Group K] [Finite K] : Prop :=
  ClassUnique K ∧ CompUnique K ∧ Gen K

@[expose] def AssemblyStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), K.Normal → RowLeaves ↥K →
    ∀ Z X P : Subgroup G, Z ≤ K → X ≤ K →
      Pos ↥K (Z.subgroupOf K) (X.subgroupOf K) →
      CFSG.ABGLocalTools.IsSylowOf 3 P X → rankThreeGamma 1 3 P = ⊤

theorem isQuasisimple_of_mulEquiv' {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B := by
  obtain ⟨hcomm, hsimp⟩ := h
  refine ⟨?_, ?_⟩
  · have h1 := Subgroup.map_commutator (⊤ : Subgroup A) ⊤ e.toMonoidHom
    have htop : (⊤ : Subgroup A).map e.toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective _ e.surjective
    rw [htop] at h1
    unfold commutator at hcomm ⊢
    rw [← h1, hcomm, htop]
  · let f := QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e
      (Subgroup.map_center_eq e)
    exact (MulEquiv.isSimpleGroup_congr f).mp hsimp

theorem map_centralizer_eq {A B : Type} [Group A] [Group B] (e : A ≃* B) (Z : Subgroup A) :
    (Subgroup.centralizer (Z : Set A)).map e.toMonoidHom =
      Subgroup.centralizer ((Z.map e.toMonoidHom : Subgroup B) : Set B) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_iff, Subgroup.coe_map,
    Set.mem_image, SetLike.mem_coe, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul, hx z hz]
  · intro hy
    refine ⟨e.symm y, fun z hz => ?_, e.apply_symm_apply y⟩
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hy (e z) ⟨z, hz, rfl⟩

theorem isSubnormal_subgroupOf_map' {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {X C : Subgroup A} (hXC : X ≤ C) (h : (X.subgroupOf C).IsSubnormal) :
    ((X.map e.toMonoidHom).subgroupOf (C.map e.toMonoidHom)).IsSubnormal := by
  let eC : C ≃* C.map e.toMonoidHom := C.equivMapOfInjective e.toMonoidHom e.injective
  have heC : ∀ x : C, ((eC x : C.map e.toMonoidHom) : B) = e x := fun x =>
    Subgroup.coe_equivMapOfInjective_apply C e.toMonoidHom e.injective x
  have hmap := Subgroup.IsSubnormal.map (f := (eC : C →* C.map e.toMonoidHom)) eC.surjective h
  have heq : (X.subgroupOf C).map (eC : C →* C.map e.toMonoidHom) =
      (X.map e.toMonoidHom).subgroupOf (C.map e.toMonoidHom) := by
    ext ⟨y, hy⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.coe_coe]
    constructor
    · rintro ⟨x, hxX, hxy⟩
      refine ⟨x, hxX, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, ← heC x, hxy]
    · rintro ⟨x, hxX, rfl⟩
      refine ⟨⟨x, hXC hxX⟩, hxX, Subtype.ext ?_⟩
      rw [heC]
      rfl
  rw [← heq]
  exact hmap

theorem pos_map {A B : Type} [Group A] [Group B] [Finite A] [Finite B] (e : A ≃* B)
    {Z X : Subgroup A} (h : Pos A Z X) : Pos B (Z.map e.toMonoidHom) (X.map e.toMonoidHom) := by
  obtain ⟨hZ, hZX, hXC, hsub, hqs, hcen, hlie⟩ := h
  let eX : X ≃* X.map e.toMonoidHom := X.equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨?_, Subgroup.map_mono hZX, ?_, ?_, isQuasisimple_of_mulEquiv' eX hqs, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective, hZ]
  · rw [← map_centralizer_eq]
    exact Subgroup.map_mono hXC
  · rw [← map_centralizer_eq]
    exact isSubnormal_subgroupOf_map' e hXC hsub
  · rw [← hcen]
    exact (Nat.card_congr (Subgroup.centerCongr eX).toEquiv).symm
  · let f := QuotientGroup.congr (Subgroup.center X) (Subgroup.center (X.map e.toMonoidHom)) eX
      (Subgroup.map_center_eq eX)
    rcases hlie with hl | hl
    · exact Or.inl (LieModel.of_mulEquiv f hl)
    · exact Or.inr (LieModel.of_mulEquiv f hl)

theorem card_subgroupOf_of_le {G : Type} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem rankThreeConj_rankThreeConj {A : Type} [Group A] (a b : A) (Z : Subgroup A) :
    rankThreeConj b (rankThreeConj a Z) = rankThreeConj (a * b) Z := by
  unfold rankThreeConj
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem rankThreeConj_one {A : Type} [Group A] (Z : Subgroup A) : rankThreeConj 1 Z = Z := by
  unfold rankThreeConj
  ext x
  simp

theorem map_conj_map {A B : Type} [Group A] [Group B] (e : A ≃* B) (a : A) (Z : Subgroup A) :
    (Z.map (MulAut.conj a).toMonoidHom).map e.toMonoidHom =
      (Z.map e.toMonoidHom).map (MulAut.conj (e a)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem rowLeaves_of_mulEquiv {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) (h : RowLeaves B) : RowLeaves A := by
  obtain ⟨hCU, hCompU, Z₀, X₀, E₀, hp, hEX, hel, hc, hs⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro Z₁ X₁ Z₂ X₂ h1 h2
    obtain ⟨k', hk'⟩ := hCU _ _ _ _ (pos_map e h1) (pos_map e h2)
    refine ⟨e.symm k', Subgroup.map_injective (f := e.toMonoidHom) e.injective ?_⟩
    unfold rankThreeConj at hk' ⊢
    rw [map_conj_map, map_inv, MulEquiv.apply_symm_apply]
    exact hk'
  · intro Z X₁ X₂ h1 h2
    exact Subgroup.map_injective (f := e.toMonoidHom) e.injective
      (hCompU _ _ _ (pos_map e h1) (pos_map e h2))
  · refine ⟨Z₀.map e.symm.toMonoidHom, X₀.map e.symm.toMonoidHom, E₀.map e.symm.toMonoidHom,
      pos_map e.symm hp, Subgroup.map_mono hEX, hel.map _, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective e.symm.injective, hc]
    · refine le_antisymm le_top ?_
      have htop : (⊤ : Subgroup A) = (⊤ : Subgroup B).map e.symm.toMonoidHom :=
        (Subgroup.map_top_of_surjective _ e.symm.surjective).symm
      rw [htop, ← hs]
      simp only [Subgroup.map_iSup]
      refine iSup_le fun F => iSup_le fun hF => iSup_le fun hF3 => ?_
      rw [map_centralizer_eq]
      refine le_trans ?_ (le_iSup _ (F.map e.symm.toMonoidHom))
      refine le_trans ?_ (le_iSup _ (Subgroup.map_mono hF))
      refine le_trans le_rfl (le_iSup_of_le ?_ le_rfl)
      rw [Subgroup.card_map_of_injective e.symm.injective, hF3]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
