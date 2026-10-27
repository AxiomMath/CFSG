module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Defs

import CFSG.Quasithin.Vol2.Ch8Sec2L829LN1
import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCF
import CFSG.LocalAnalysis.UniquenessCase.UC22P20a
import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped Pointwise

variable {Y : Type} [Group Y]

structure IsLPair (P : ∀ (X : Type) [Group X], Prop) (T A B : Subgroup Y) : Prop where
  le_left : T ≤ A
  le_right : T ≤ B
  ne_top_left : A ≠ ⊤
  ne_top_right : B ≠ ⊤
  not_left : ¬ HasCompFactor A P
  not_right : ¬ HasCompFactor B P
  sup_eq_top : A ⊔ B = ⊤

theorem hasCompFactor_map_of_injective {Y' : Type} [Group Y'] {P : ∀ (X : Type) [Group X], Prop}
    (f : Y →* Y') (hf : Function.Injective f) (X : Subgroup Y) :
    HasCompFactor (X.map f) P ↔ HasCompFactor X P := by
  have e := X.equivMapOfInjective f hf
  constructor
  · rintro ⟨L, _, h, hP⟩
    exact ⟨L, _, (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr e).2 h, hP⟩
  · rintro ⟨L, _, h, hP⟩
    exact ⟨L, _, (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr e).1 h, hP⟩

namespace IsLPair

variable {P : ∀ (X : Type) [Group X], Prop} {T A B : Subgroup Y}

theorem lGen_eq_top (h : IsLPair P T A B) : lGen P ⊤ T = ⊤ := by
  refine eq_top_iff.2 (le_trans h.sup_eq_top.symm.le (sup_le ?_ ?_))
  · exact le_iSup₂_of_le (f := fun X (_ : X ∈ calLT P ⊤ T) => X) A
      ⟨h.le_left, lt_top_iff_ne_top.2 h.ne_top_left, h.not_left⟩ le_rfl
  · exact le_iSup₂_of_le (f := fun X (_ : X ∈ calLT P ⊤ T) => X) B
      ⟨h.le_right, lt_top_iff_ne_top.2 h.ne_top_right, h.not_right⟩ le_rfl

theorem map {Y' : Type} [Group Y'] (h : IsLPair P T A B) (f : Y ≃* Y') :
    IsLPair P (T.map f.toMonoidHom) (A.map f.toMonoidHom) (B.map f.toMonoidHom) where
  le_left := Subgroup.map_mono h.le_left
  le_right := Subgroup.map_mono h.le_right
  ne_top_left hA := h.ne_top_left (Subgroup.map_injective f.injective
    (hA.trans (Subgroup.map_top_of_surjective _ f.surjective).symm))
  ne_top_right hB := h.ne_top_right (Subgroup.map_injective f.injective
    (hB.trans (Subgroup.map_top_of_surjective _ f.surjective).symm))
  not_left hc := h.not_left ((hasCompFactor_map_of_injective _ f.injective A).1 hc)
  not_right hc := h.not_right ((hasCompFactor_map_of_injective _ f.injective B).1 hc)
  sup_eq_top := by
    rw [← Subgroup.map_sup, h.sup_eq_top, Subgroup.map_top_of_surjective _ f.surjective]

end IsLPair

theorem exists_map_conj_eq_of_isSylowIn {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {S T : Subgroup G} (hS : IsSylowIn p S ⊤) (hT : IsSylowIn p T ⊤) :
    ∃ g : G, S.map (MulAut.conj g).toMonoidHom = T := by
  have hSi : ¬ p ∣ S.index := by
    simpa [Subgroup.relIndex_top_right] using hS.not_dvd_relIndex
  have hTi : ¬ p ∣ T.index := by
    simpa [Subgroup.relIndex_top_right] using hT.not_dvd_relIndex
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (hS.isPGroup.toSylow hSi) (hT.isPGroup.toSylow hTi)
  refine ⟨g, ?_⟩
  have h := congrArg (fun Q : Sylow p G => (Q : Subgroup G)) hg
  simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h
  exact h

theorem isSylowIn_top_map_mulEquiv {Y' : Type} [Group Y'] {p : ℕ} {T : Subgroup Y}
    (hT : IsSylowIn p T ⊤) (f : Y ≃* Y') : IsSylowIn p (T.map f.toMonoidHom) ⊤ := by
  have h := (CFSG.Quasithin.E1.isSylowIn_map_mulEquiv f (P := T) (H := ⊤)).2 hT
  rwa [Subgroup.map_top_of_surjective _ f.surjective] at h

theorem lGen_eq_top_of_isLPair_mulEquiv {C : Type} [Group C] [Finite Y]
    {P : ∀ (X : Type) [Group X], Prop} {T₀ A₀ B₀ : Subgroup C} (hT₀ : IsSylowIn 2 T₀ ⊤)
    (h : IsLPair P T₀ A₀ B₀) (e : C ≃* Y) {T : Subgroup Y} (hT : IsSylowIn 2 T ⊤) :
    lGen P ⊤ T = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_map_conj_eq_of_isSylowIn (isSylowIn_top_map_mulEquiv hT₀ e) hT
  have h' := (h.map e).map (MulAut.conj g)
  rw [hg] at h'
  exact h'.lGen_eq_top

theorem lGen_eq_top_of_normal_pair [Finite Y] {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (X : Type) [Group X] [Finite X], P X → ∃ a b : X, a * b ≠ b * a)
    {L T A B : Subgroup Y} [L.Normal] (hLT : L ⊔ T = ⊤) (hT2 : IsPGroup 2 T)
    (hAL : A ≤ L) (hBL : B ≤ L) (hTA : T ⊓ L ≤ A) (hTB : T ⊓ L ≤ B) (hA : A ≠ L) (hB : B ≠ L)
    (hPA : ¬ HasCompFactor A P) (hPB : ¬ HasCompFactor B P) (hAB : A ⊔ B = L)
    (hNA : T ≤ normalizer (A : Set Y)) (hNB : T ≤ normalizer (B : Set Y)) :
    lGen P ⊤ T = ⊤ := by
  have key : ∀ A : Subgroup Y, A ≤ L → T ⊓ L ≤ A → A ≠ L → ¬ HasCompFactor A P →
      T ≤ normalizer (A : Set Y) → A ⊔ T ≠ ⊤ ∧ ¬ HasCompFactor (A ⊔ T) P := by
    intro A hAL hTA hA hPA hNA
    have hcoe : ((A ⊔ T : Subgroup Y) : Set Y) = (A : Set Y) * (T : Set Y) :=
      Subgroup.coe_mul_of_right_le_normalizer_left A T hNA
    refine ⟨fun htop => hA (le_antisymm hAL fun x hxL => ?_), fun hc => ?_⟩
    ·
      have hx : x ∈ ((A ⊔ T : Subgroup Y) : Set Y) := by rw [htop]; exact Set.mem_univ x
      rw [hcoe] at hx
      obtain ⟨a, ha, t, ht, rfl⟩ := hx
      have htL : t ∈ L := by
        have := L.mul_mem (L.inv_mem (hAL ha)) hxL
        rwa [inv_mul_cancel_left] at this
      exact A.mul_mem ha (hTA ⟨ht, htL⟩)
    ·
      obtain ⟨K, _, hK, hPK⟩ := hc
      have hAK : A ≤ A ⊔ T := le_sup_left
      have hAn : (A.subgroupOf (A ⊔ T)).Normal := by
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer hAK]
        exact sup_le Subgroup.le_normalizer hNA
      rcases isCompositionFactor_of_normal (A.subgroupOf (A ⊔ T)) hK with h1 | h2
      · exact hPA ⟨K, _, (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
          (Subgroup.subgroupOfEquivOfLe hAK)).1 h1, hPK⟩
      ·
        let π := (QuotientGroup.mk' (A.subgroupOf (A ⊔ T))).comp
          (Subgroup.inclusion (le_sup_right : T ≤ A ⊔ T))
        have hπ : Function.Surjective π := by
          intro y
          induction y using QuotientGroup.induction_on with
          | H k =>
            have hk : (k : Y) ∈ (A : Set Y) * (T : Set Y) := by rw [← hcoe]; exact k.2
            obtain ⟨a, ha, t, ht, hat⟩ := hk
            refine ⟨⟨t, ht⟩, ?_⟩
            simp only [π, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
            rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
            have hmem : t⁻¹ * a * t ∈ A := by
              have := (Subgroup.mem_normalizer_iff.1 (hNA (T.inv_mem ht)) a).1 ha
              rwa [inv_inv] at this
            convert hmem using 1
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
            rw [← hat]
            group
        have : Group.IsSolvable (↥(A ⊔ T) ⧸ A.subgroupOf (A ⊔ T)) := by
          have := (hT2.of_surjective π hπ).isNilpotent
          infer_instance
        have : Finite K := isCompositionFactor_finite hK
        obtain ⟨a, b, hab⟩ := hP K hPK
        exact hab (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20a_abelian_of_compositionFactor
          inferInstance h2 a b)
  obtain ⟨hA', hPA'⟩ := key A hAL hTA hA hPA hNA
  obtain ⟨hB', hPB'⟩ := key B hBL hTB hB hPB hNB
  refine IsLPair.lGen_eq_top ⟨le_sup_right, le_sup_right, hA', hB', hPA', hPB', ?_⟩
  refine eq_top_iff.2 (le_trans hLT.symm.le (sup_le ?_ (le_sup_right.trans le_sup_right)))
  rw [← hAB]
  exact sup_le_sup le_sup_left le_sup_left

theorem index_le_card_outer [Finite Y] (L : Subgroup Y) [L.Normal]
    (hC : centralizer (L : Set Y) = ⊥) : L.index ≤ Nat.card (Outer ↥L) := by
  have hinj : Function.Injective (MulAut.conjNormal : Y →* MulAut ↥L) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hC]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun α : MulAut ↥L => ((α ⟨y, hy⟩ : ↥L) : Y)) (MonoidHom.mem_ker.1 hx)
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
    calc y * x = x * y * x⁻¹ * x := by rw [h]
      _ = x * y := by group
  have h1 : Nat.card Y ≤ Nat.card (MulAut ↥L) := Nat.card_le_card_of_injective _ hinj
  have h2 : Nat.card (MulAut ↥L) ≤ Nat.card (Outer ↥L) * Nat.card ↥L := by
    rw [(inner ↥L).card_eq_card_quotient_mul_card_subgroup]
    exact Nat.mul_le_mul le_rfl
      (Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _))
  have h3 := L.card_mul_index
  have hpos : 0 < Nat.card ↥L := Nat.card_pos
  by_contra hlt
  have : Nat.card ↥L * (Nat.card (Outer ↥L) + 1) ≤ Nat.card ↥L * L.index :=
    Nat.mul_le_mul_left _ (not_le.1 hlt)
  nlinarith

theorem sup_eq_top_of_index_le_two [Finite Y] {L T : Subgroup Y} (hL : L.index ≤ 2)
    (hT : IsSylowIn 2 T ⊤) : L ⊔ T = ⊤ := by
  have hTi : ¬ 2 ∣ T.index := by
    simpa [Subgroup.relIndex_top_right] using hT.not_dvd_relIndex
  have h1 : (L ⊔ T).index ∣ L.index := Subgroup.index_dvd_of_le le_sup_left
  have h2 : (L ⊔ T).index ∣ T.index := Subgroup.index_dvd_of_le le_sup_right
  have hpos : 0 < L.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hle : (L ⊔ T).index ≤ 2 := (Nat.le_of_dvd hpos h1).trans hL
  have hpos' : 0 < (L ⊔ T).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rcases (by omega : (L ⊔ T).index = 1 ∨ (L ⊔ T).index = 2) with h | h
  · exact Subgroup.index_eq_one.1 h
  · exact absurd (h ▸ h2) hTi

theorem isSylowIn_subgroupOf_of_normal [Finite Y] {L T : Subgroup Y} [L.Normal]
    (hT : IsSylowIn 2 T ⊤) : IsSylowIn 2 (T.subgroupOf L) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hT.inf_normal (N := L) le_top inferInstance
  have h2 := (CFSG.Quasithin.E1.isSylowIn_subgroupOf_iff inf_le_right le_rfl).2 h
  rwa [Subgroup.inf_subgroupOf_right, Subgroup.subgroupOf_self] at h2

theorem lGen_eq_top_of_isLPair_of_card_outer_eq_one {C : Type} [Group C] [Finite C] [Finite Y]
    {P : ∀ (X : Type) [Group X], Prop} (hOut : Nat.card (Outer C) = 1) {T₀ A₀ B₀ : Subgroup C}
    (hT₀ : IsSylowIn 2 T₀ ⊤) (h : IsLPair P T₀ A₀ B₀) (L : Subgroup Y) [L.Normal]
    (φ : ↥L ≃* C) (hC : centralizer (L : Set Y) = ⊥) {T : Subgroup Y} (hT : IsSylowIn 2 T ⊤) :
    lGen P ⊤ T = ⊤ := by
  have hOutL : Nat.card (Outer ↥L) = 1 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence φ).toEquiv,
      hOut]
  have hLt : L = ⊤ := Subgroup.index_eq_one.1 (le_antisymm
    ((index_le_card_outer L hC).trans hOutL.le)
    (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite))
  exact lGen_eq_top_of_isLPair_mulEquiv hT₀ h
    (φ.symm.trans ((MulEquiv.subgroupCongr hLt).trans Subgroup.topEquiv)) hT

theorem asch54Case_of_isLPair_of_card_outer_eq_one {C : Type} [Group C] [Finite C]
    {P : ∀ (X : Type) [Group X], Prop} (hPC : ∀ (X : Type) [Group X], P X → Nonempty (X ≃* C))
    (hOut : Nat.card (Outer C) = 1) {T₀ A₀ B₀ : Subgroup C} (hT₀ : IsSylowIn 2 T₀ ⊤)
    (h : IsLPair IsCalL0 T₀ A₀ B₀) : Asch54Case P := by
  intro Q _ _ L T _ hLn _ _ hC hPL _ hT _
  obtain ⟨φ⟩ := hPC _ hPL
  exact Or.inl (lGen_eq_top_of_isLPair_of_card_outer_eq_one hOut hT₀ h L φ hC hT)

theorem lGen_eq_top_of_isLPair_of_aut {C : Type} [Group C] [Finite C] [Finite Y]
    {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (X : Type) [Group X] [Finite X], P X → ∃ a b : X, a * b ≠ b * a)
    (hOut : Nat.card (Outer C) ≤ 2) {T₀ A₀ B₀ : Subgroup C} (hT₀ : IsSylowIn 2 T₀ ⊤)
    (h : IsLPair P T₀ A₀ B₀)
    (hAut : ∀ ψ : C ≃* C, T₀.map ψ.toMonoidHom = T₀ →
      A₀.map ψ.toMonoidHom = A₀ ∧ B₀.map ψ.toMonoidHom = B₀)
    (L : Subgroup Y) [L.Normal] (φ₀ : ↥L ≃* C) (hC : centralizer (L : Set Y) = ⊥)
    {T : Subgroup Y} (hT : IsSylowIn 2 T ⊤) : lGen P ⊤ T = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOutL : Nat.card (Outer ↥L) ≤ 2 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence φ₀).toEquiv]
    exact hOut
  have hLT : L ⊔ T = ⊤ :=
    sup_eq_top_of_index_le_two ((index_le_card_outer L hC).trans hOutL) hT
  obtain ⟨g, hg⟩ := exists_map_conj_eq_of_isSylowIn
    (isSylowIn_top_map_mulEquiv (isSylowIn_subgroupOf_of_normal (L := L) hT) φ₀) hT₀
  let φ : ↥L ≃* C := φ₀.trans (MulAut.conj g)
  have hφT : (T.subgroupOf L).map φ.toMonoidHom = T₀ := by
    rw [← hg, Subgroup.map_map]
    rfl
  have hTL : T.subgroupOf L = T₀.map φ.symm.toMonoidHom := by
    rw [← hφT, Subgroup.map_map]
    ext x
    simp
  have htopL : (⊤ : Subgroup ↥L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hnorm : ∀ X₀ : Subgroup C,
      (∀ ψ : C ≃* C, T₀.map ψ.toMonoidHom = T₀ → X₀.map ψ.toMonoidHom = X₀) →
      T ≤ normalizer (((X₀.map φ.symm.toMonoidHom).map L.subtype : Subgroup Y) : Set Y) := by
    intro X₀ hX₀
    have hconj : ∀ τ ∈ T, ∀ x ∈ (X₀.map φ.symm.toMonoidHom).map L.subtype,
        τ * x * τ⁻¹ ∈ (X₀.map φ.symm.toMonoidHom).map L.subtype := by
      intro τ hτ x hx
      obtain ⟨y, ⟨x₀, hx₀, rfl⟩, rfl⟩ := hx
      let ψ : C ≃* C := φ.symm.trans ((MulAut.conjNormal τ).trans φ)
      have hTτ : (T.subgroupOf L).map (MulAut.conjNormal τ).toMonoidHom = T.subgroupOf L := by
        refine le_antisymm ?_ fun y hy => ?_
        · rintro _ ⟨x, hx, rfl⟩
          rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
          rw [Subgroup.mem_subgroupOf]
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply]
          exact T.mul_mem (T.mul_mem hτ hx) (T.inv_mem hτ)
        · rw [Subgroup.mem_subgroupOf] at hy
          refine ⟨(MulAut.conjNormal τ⁻¹) y, ?_, ?_⟩
          · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, MulAut.conjNormal_apply, inv_inv]
            exact T.mul_mem (T.mul_mem (T.inv_mem hτ) hy) hτ
          · apply Subtype.ext
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply, inv_inv]
            group
      have hψT : T₀.map ψ.toMonoidHom = T₀ := by
        conv_rhs => rw [← hφT, ← hTτ, Subgroup.map_map]
        rw [← hφT, Subgroup.map_map]
        congr 1
        ext z
        simp [ψ]
      have hmem : ψ x₀ ∈ X₀ := by
        rw [← hX₀ ψ hψT]
        exact ⟨x₀, hx₀, rfl⟩
      refine ⟨φ.symm (ψ x₀), ⟨ψ x₀, hmem, rfl⟩, ?_⟩
      simp [ψ, MulAut.conjNormal_apply]
    intro τ hτ
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hconj τ hτ x, fun hx => ?_⟩
    have := hconj τ⁻¹ (T.inv_mem hτ) _ hx
    rwa [inv_inv, show τ⁻¹ * (τ * x * τ⁻¹) * τ = x by group] at this
  have hNA := hnorm A₀ fun ψ hψ => (hAut ψ hψ).1
  have hNB := hnorm B₀ fun ψ hψ => (hAut ψ hψ).2
  have hle : ∀ X₀ : Subgroup C, T₀ ≤ X₀ → T ⊓ L ≤ (X₀.map φ.symm.toMonoidHom).map L.subtype := by
    intro X₀ hX₀
    rw [← Subgroup.subgroupOf_map_subtype, hTL]
    exact Subgroup.map_mono (Subgroup.map_mono hX₀)
  have hne : ∀ X₀ : Subgroup C, X₀ ≠ ⊤ → (X₀.map φ.symm.toMonoidHom).map L.subtype ≠ L := by
    intro X₀ hX₀ hX
    have h1 := Subgroup.map_injective L.subtype_injective (hX.trans htopL.symm)
    exact hX₀ (Subgroup.map_injective φ.symm.injective
      (h1.trans (Subgroup.map_top_of_surjective _ φ.symm.surjective).symm))
  have hcf : ∀ X₀ : Subgroup C, ¬ HasCompFactor X₀ P →
      ¬ HasCompFactor ((X₀.map φ.symm.toMonoidHom).map L.subtype) P := fun X₀ hX₀ hc =>
    hX₀ ((hasCompFactor_map_of_injective _ φ.symm.injective X₀).1
      ((hasCompFactor_map_of_injective _ L.subtype_injective _).1 hc))
  refine lGen_eq_top_of_normal_pair hP hLT hT.isPGroup (Subgroup.map_subtype_le _)
    (Subgroup.map_subtype_le _) (hle A₀ h.le_left) (hle B₀ h.le_right) (hne A₀ h.ne_top_left)
    (hne B₀ h.ne_top_right) (hcf A₀ h.not_left) (hcf B₀ h.not_right) ?_ hNA hNB
  rw [← Subgroup.map_sup, ← Subgroup.map_sup, h.sup_eq_top,
    Subgroup.map_top_of_surjective _ φ.symm.surjective, htopL]

theorem asch54Case_of_isLPair_of_aut {C : Type} [Group C] [Finite C]
    {P : ∀ (X : Type) [Group X], Prop} (hPC : ∀ (X : Type) [Group X], P X → Nonempty (X ≃* C))
    (hP0 : ∀ (X : Type) [Group X] [Finite X], IsCalL0 X → ∃ a b : X, a * b ≠ b * a)
    (hOut : Nat.card (Outer C) ≤ 2) {T₀ A₀ B₀ : Subgroup C} (hT₀ : IsSylowIn 2 T₀ ⊤)
    (h : IsLPair IsCalL0 T₀ A₀ B₀)
    (hAut : ∀ ψ : C ≃* C, T₀.map ψ.toMonoidHom = T₀ →
      A₀.map ψ.toMonoidHom = A₀ ∧ B₀.map ψ.toMonoidHom = B₀) : Asch54Case P := by
  intro Q _ _ L T _ hLn _ _ hC hPL _ hT _
  obtain ⟨φ₀⟩ := hPC _ hPL
  exact Or.inl (lGen_eq_top_of_isLPair_of_aut hP0 hOut hT₀ h hAut L φ₀ hC hT)

@[expose] def Asch54SporAt (s : TauCeti.SporadicName) : Prop :=
  Asch54Case fun X _ => CFSG.Models.IsSporadic X s

theorem asch54Spor_of_forall (h : ∀ s, Asch54SporAt s) : Asch54Spor := by
  intro Q _ _ L T hK hLn hLs hLnab hC hPL hnL hT hnu
  obtain ⟨s, hs⟩ := hPL
  exact h s Q L T hK hLn hLs hLnab hC hs hnL hT hnu

@[expose] def Asch54SporGenAt (s : TauCeti.SporadicName) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (L T : Subgroup Q), L.Normal →
    CFSG.Models.IsSporadic ↥L s → Subgroup.centralizer (L : Set Q) = ⊥ → IsSylowIn 2 T ⊤ →
      lGen IsCalL0 ⊤ T = ⊤

@[expose] def Asch54SporThGen : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (L T : Subgroup Q), L.Normal →
    CFSG.Models.IsSporadic ↥L .Th → Subgroup.centralizer (L : Set Q) = ⊥ → IsSylowIn 2 T ⊤ →
      3 < CFSG.Open.pRank 3 (perfectCore (⊤ : Subgroup Q)) ∧
        1 < CFSG.Open.pRank 3 (lGen IsCalL0 ⊤ T)

theorem asch54SporAt_of_gen {s : TauCeti.SporadicName} (h : Asch54SporGenAt s) :
    Asch54SporAt s := by
  intro Q _ _ L T _ hLn _ _ hC hs _ hT _
  exact Or.inl (h Q L T hLn hs hC hT)

theorem asch54SporAt_th_of_gen (h : Asch54SporThGen) : Asch54SporAt .Th := by
  intro Q _ _ L T _ hLn _ _ hC hs _ hT _
  obtain ⟨h1, h2⟩ := h Q L T hLn hs hC hT
  exact Or.inr ⟨3, Nat.prime_three, by norm_num, h1, h2⟩

theorem asch54Spor_of_gen (h : ∀ s, s ≠ .Th → Asch54SporGenAt s) (hTh : Asch54SporThGen) :
    Asch54Spor :=
  asch54Spor_of_forall fun s => by
    by_cases hs : s = .Th
    · subst hs
      exact asch54SporAt_th_of_gen hTh
    · exact asch54SporAt_of_gen (h s hs)

theorem asch54SporGenAt_of_isLPair_of_card_outer_eq_one {s : TauCeti.SporadicName} {C : Type}
    [Group C] [Finite C] (hsC : Nonempty (s.Group ≃* C)) (hOut : Nat.card (Outer C) = 1)
    {T₀ A₀ B₀ : Subgroup C} (hT₀ : IsSylowIn 2 T₀ ⊤) (h : IsLPair IsCalL0 T₀ A₀ B₀) :
    Asch54SporGenAt s := by
  intro Q _ _ L T hLn hs hC hT
  obtain ⟨e⟩ := hs
  obtain ⟨f⟩ := hsC
  exact lGen_eq_top_of_isLPair_of_card_outer_eq_one hOut hT₀ h L (e.trans f) hC hT

theorem asch54SporGenAt_of_isLPair_of_aut {s : TauCeti.SporadicName} {C : Type} [Group C]
    [Finite C] (hsC : Nonempty (s.Group ≃* C))
    (hP0 : ∀ (X : Type) [Group X] [Finite X], IsCalL0 X → ∃ a b : X, a * b ≠ b * a)
    (hOut : Nat.card (Outer C) ≤ 2) {T₀ A₀ B₀ : Subgroup C} (hT₀ : IsSylowIn 2 T₀ ⊤)
    (h : IsLPair IsCalL0 T₀ A₀ B₀)
    (hAut : ∀ ψ : C ≃* C, T₀.map ψ.toMonoidHom = T₀ →
      A₀.map ψ.toMonoidHom = A₀ ∧ B₀.map ψ.toMonoidHom = B₀) : Asch54SporGenAt s := by
  intro Q _ _ L T hLn hs hC hT
  obtain ⟨e⟩ := hs
  obtain ⟨f⟩ := hsC
  exact lGen_eq_top_of_isLPair_of_aut hP0 hOut hT₀ h hAut L (e.trans f) hC hT

end CFSG.LocalAnalysis.WeakClosure81

end
