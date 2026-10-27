module

public import CFSG.OddTranspositions.PartThree.WreathTwo
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
public import CFSG.OddTranspositions.PartThree.Eleven.Plus.Facts
public import CFSG.OddTranspositions.PartThree.Eleven.Plus.Realize

public section

namespace CFSG.OddTranspositions.PartThree


private theorem image_isConj_of_map_eq {G H : Type} [Group G] [Group H] (f : G ≃* H) {a : G}
    {b : H} (h : f a = b) : f '' {x | IsConj a x} = {y | IsConj b y} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : IsConj (f a) (f x) := f.toMonoidHom.map_isConj hx
    rw [h] at hx'
    exact hx'
  · intro hy
    refine ⟨f.symm y, ?_, by simp⟩
    have hb : f.symm b = a := by rw [← h, f.symm_apply_apply]
    simpa [hb] using f.symm.toMonoidHom.map_isConj hy

private theorem card_psl2Model_two : Nat.card (CFSG.Theory.Comparator.PSL2Model 2) = 60 := by
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have : CharP (GaloisField 2 2) 2 := inferInstance
  have hcenter := CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
    (K := GaloisField 2 2) (CharTwo.neg_eq 1)
  have hcard := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center
    (K := GaloisField 2 2)
  rw [hK, hcenter] at hcard
  norm_num at hcard
  exact hcard

private theorem nonempty_psl2Model_two_equiv_alt5 :
    Nonempty (CFSG.Theory.Comparator.PSL2Model 2 ≃* alternatingGroup (Fin 5)) := by
  haveI : IsSimpleGroup (CFSG.Theory.Comparator.PSL2Model 2) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := GaloisField 2 2) (by
      rw [GaloisField.card 2 2 (by norm_num)]
      norm_num)
  exact CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    card_psl2Model_two

theorem plusClass_eq_isConj :
    plusClass = {g | IsConj (⟨plusRefl 0, plusRefl_mem 0⟩ : plusPerm) g} := by
  let r₀ : plusPerm := ⟨plusRefl 0, plusRefl_mem 0⟩
  change plusClass = {g | IsConj r₀ g}
  have hr₀ : r₀ ∈ plusClass := ⟨0, rfl⟩
  have hconj : ∀ c : plusPerm, c * r₀ * c⁻¹ ∈ plusClass := by
    intro c
    refine ⟨(c : Equiv.Perm (Fin 60)) 0, ?_⟩
    have h := conj_plusRefl c.2 0
    simpa [r₀] using h
  have hBsub : {g | IsConj r₀ g} ⊆ plusClass := by
    intro x hx
    obtain ⟨c, hc⟩ := isConj_iff.mp hx
    rw [← hc]
    exact hconj c
  have hBne : ({g | IsConj r₀ g} : Set plusPerm).Nonempty := ⟨r₀, IsConj.refl r₀⟩
  have hBinv : ∀ g : plusPerm,
      (fun y => g * y * g⁻¹) '' {x | IsConj r₀ x} = {x | IsConj r₀ x} := by
    intro g
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy.trans (isConj_iff.mpr ⟨g, rfl⟩)
    · intro hz
      refine ⟨g⁻¹ * z * g, ?_, by group⟩
      exact hz.trans (isConj_iff.mpr ⟨g⁻¹, rfl⟩)
  have hnot : ¬ ({g | IsConj r₀ g} : Set plusPerm).Subsingleton := by
    intro hsub
    obtain ⟨b, -, hbcomm⟩ := o4PlusFacts_plusPerm.noncomm r₀ hr₀
    have h1 : r₀ ∈ {g | IsConj r₀ g} := IsConj.refl r₀
    have h2 : b * r₀ * b⁻¹ ∈ {g | IsConj r₀ g} := isConj_iff.mpr ⟨b, rfl⟩
    have hne : b * r₀ * b⁻¹ ≠ r₀ := by
      intro heq
      apply hbcomm
      have h : b * r₀ = r₀ * b := by
        calc b * r₀ = b * r₀ * b⁻¹ * b := by group
          _ = r₀ * b := by rw [heq]
      exact h.symm
    exact hne (hsub h2 h1)
  have hBeq : ({g | IsConj r₀ g} : Set plusPerm) = plusClass :=
    (o4PlusFacts_plusPerm.primitive _ hBsub hBne (fun g => Or.inl (hBinv g))).resolve_left hnot
  exact hBeq.symm

theorem exists_l2WreathTwoTwo_mulEquiv_plusPerm_of
    (hW : ∀ {A B : Subgroup plusPerm} (_ : CFSG.Theory.Comparator.PSL2Model 2 ≃* A), A ⊓ B = ⊥ →
      (∀ a ∈ A, ∀ b ∈ B, Commute a b) → (A ⊔ B).index = 2 → ∀ {r : plusPerm}, r * r = 1 →
      r ∉ A ⊔ B → A.map (MulAut.conj r).toMonoidHom = B →
      ∃ Ψ : CFSG.Timmesfeld.Bridge.Asc72.L2Wreath 2 2 ≃* plusPerm,
        Ψ (SemidirectProduct.inr (Equiv.swap 0 1)) = r) :
    ∃ Ψ : CFSG.Timmesfeld.Bridge.Asc72.L2Wreath 2 2 ≃* plusPerm,
      Ψ '' {x | IsConj (SemidirectProduct.inr (Equiv.swap 0 1)) x} = plusClass := by
  obtain ⟨A, B, hAB⟩ := o4PlusFacts_plusPerm.factors
  let r : plusPerm := ⟨plusRefl 0, plusRefl_mem 0⟩
  have hrclass : r ∈ plusClass := ⟨0, rfl⟩
  have hcardA : Nat.card A = 60 := hAB.cardA
  haveI : Finite A := (Nat.card_pos_iff.mp (by rw [hcardA]; norm_num)).2
  haveI : IsSimpleGroup A := hAB.simpleA
  obtain ⟨eA⟩ :=
    CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty hcardA
  obtain ⟨eP⟩ := nonempty_psl2Model_two_equiv_alt5
  have eAB : CFSG.Theory.Comparator.PSL2Model 2 ≃* A := eP.trans eA.symm
  have hidx : (A ⊔ B).index = 2 := by
    rw [hAB.sup_eq]
    exact o4PlusFacts_plusPerm.index_two
  have hr2 : r * r = 1 := Subtype.ext (by simpa [r] using plusRefl_mul_self 0)
  have hswap : A.map (MulAut.conj r).toMonoidHom = B := hAB.swap r hrclass
  have hrnot : r ∉ A ⊔ B := by
    intro hr
    have hAnorm : A ≤ Subgroup.normalizer A := by
      rw [Subgroup.le_normalizer_iff]
      intro a ha k hk
      exact A.mul_mem (A.mul_mem ha hk) (A.inv_mem ha)
    have hBnorm : B ≤ Subgroup.normalizer A := by
      rw [Subgroup.le_normalizer_iff]
      intro b hb a ha
      have hc : b * a * b⁻¹ = a := by
        rw [((hAB.commute a ha b hb).eq).symm]
        group
      rw [hc]
      exact ha
    have hsupnorm : A ⊔ B ≤ Subgroup.normalizer A := sup_le hAnorm hBnorm
    have hmapA : A.map (MulAut.conj r).toMonoidHom = A := by
      simpa using Subgroup.mem_normalizer_iff_map_conj_eq.mp (hsupnorm hr)
    have hABeq : A = B := by
      rw [← hswap, hmapA]
    have hbot : A = ⊥ := by
      have hle : A ≤ A ⊓ B := le_inf le_rfl hABeq.le
      rw [hAB.inf_eq] at hle
      exact bot_unique hle
    have hc := hAB.cardA
    rw [hbot, Subgroup.card_bot] at hc
    omega
  obtain ⟨Ψ, hΨeq⟩ := hW (A := A) (B := B) eAB hAB.inf_eq hAB.commute hidx hr2 hrnot hswap
  refine ⟨Ψ, ?_⟩
  rw [image_isConj_of_map_eq Ψ hΨeq]
  exact plusClass_eq_isConj.symm

theorem isFiveReflectionModel_of_l2Wreath_two_two_of
    (hΨ : ∃ Ψ : CFSG.Timmesfeld.Bridge.Asc72.L2Wreath 2 2 ≃* plusPerm,
      Ψ '' {x | IsConj (SemidirectProduct.inr (Equiv.swap 0 1)) x} = plusClass)
    {X : Type} [Group X] {s : X}
    (e : X ≃* CFSG.Timmesfeld.Bridge.Asc72.L2Wreath 2 2)
    (hs : IsConj (e s) (SemidirectProduct.inr (Equiv.swap 0 1))) :
    ∃ π, IsFiveReflectionModel 3 true π {x | IsConj s x} := by
  obtain ⟨Ψ, hΨim⟩ := hΨ
  obtain ⟨eπ, heπ⟩ := exists_plusRealize true
  refine ⟨true, ?_⟩
  change CFSG.Open.fischerCentralQuotientModel {x | IsConj s x}
    (fiveReflectionGroup 3 true true) (fiveReflections 3 true true)
  have he' : eπ.symm '' plusClass = fiveReflectionImage 3 true true := by
    rw [← heπ, Set.image_image]
    simp
  let φ : X ≃* fiveReflectionGroup 3 true true ⧸
      Subgroup.center (fiveReflectionGroup 3 true true) := (e.trans Ψ).trans eπ.symm
  refine ⟨φ, ?_⟩
  intro g
  change IsConj s g ↔ φ g ∈ fiveReflectionImage 3 true true
  have hφg : φ g = eπ.symm (Ψ (e g)) := rfl
  have h1 : φ g ∈ fiveReflectionImage 3 true true ↔ Ψ (e g) ∈ plusClass := by
    rw [hφg, ← he']
    constructor
    · rintro ⟨y, hy, hyeq⟩
      rwa [eπ.symm.injective hyeq] at hy
    · intro hz
      exact ⟨Ψ (e g), hz, rfl⟩
  have h2 : Ψ (e g) ∈ plusClass ↔
      IsConj (SemidirectProduct.inr (Equiv.swap 0 1)) (e g) := by
    rw [← hΨim]
    constructor
    · rintro ⟨x, hx, hxeq⟩
      rwa [Ψ.injective hxeq] at hx
    · intro hx
      exact ⟨e g, hx, rfl⟩
  have h3 : IsConj (SemidirectProduct.inr (Equiv.swap 0 1)) (e g) ↔ IsConj (e s) (e g) :=
    ⟨fun h => hs.trans h, fun h => hs.symm.trans h⟩
  have h4 : IsConj (e s) (e g) ↔ IsConj s g := by
    constructor
    · intro h
      simpa using e.symm.toMonoidHom.map_isConj h
    · intro h
      exact e.toMonoidHom.map_isConj h
  rw [h1, h2, h3, h4]

theorem exists_l2WreathTwoTwo_mulEquiv_plusPerm :
    ∃ Ψ : CFSG.Timmesfeld.Bridge.Asc72.L2Wreath 2 2 ≃* plusPerm,
      Ψ '' {x | IsConj (SemidirectProduct.inr (Equiv.swap 0 1)) x} = plusClass :=
  exists_l2WreathTwoTwo_mulEquiv_plusPerm_of fun α hinf hcomm hindex =>
    exists_mulEquiv_wreathTwo α hinf hcomm hindex

theorem isFiveReflectionModel_of_l2Wreath_two_two {X : Type} [Group X] {s : X}
    (e : X ≃* CFSG.Timmesfeld.Bridge.Asc72.L2Wreath 2 2)
    (hs : IsConj (e s) (SemidirectProduct.inr (Equiv.swap 0 1))) :
    ∃ π, IsFiveReflectionModel 3 true π {x | IsConj s x} :=
  isFiveReflectionModel_of_l2Wreath_two_two_of exists_l2WreathTwoTwo_mulEquiv_plusPerm e hs

end CFSG.OddTranspositions.PartThree
