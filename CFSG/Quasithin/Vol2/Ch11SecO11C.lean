module

public import CFSG.Quasithin.Vol2.Ch11SecSQuot
public import CFSG.Quasithin.Vol2.Ch11SecSFacts4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.O11

open CFSG.Open CFSG.Blueprint

variable {Q : Type} [Group Q]

@[expose] def L24Unique (S : Subgroup Q) : Prop :=
  ∀ B₁ B₂ : Subgroup Q, IsL24Sub S B₁ → IsL24Sub S B₂ → B₁ = B₂

theorem eq_perfectCore_sup [Finite Q] {S B : Subgroup Q} (hS : IsPGroup 2 S) (hB : IsL24Sub S B) :
    perfectCore (B ⊔ S) = B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hS.isNilpotent
  exact perfectCore_sup_eq hB.2.1 inferInstance hB.2.2.1

theorem eq_of_sup_eq [Finite Q] {S B₁ B₂ : Subgroup Q} (hS : IsPGroup 2 S) (h₁ : IsL24Sub S B₁)
    (h₂ : IsL24Sub S B₂) (h : B₁ ⊔ S = B₂ ⊔ S) : B₁ = B₂ := by
  rw [← eq_perfectCore_sup hS h₁, ← eq_perfectCore_sup hS h₂, h]

theorem card_sl2_four {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 60 := by
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, hF]
  rw [Matrix.card_SL_field, Fin.prod_univ_two, hF']
  norm_num

theorem card_of_l24 [Finite Q] {S B : Subgroup Q} (hB : IsL24Sub S B) :
    ∃ a, Nat.card B = 15 * 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, F, _, _, hF, ⟨e⟩⟩ := hB
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥B)).exists_card_eq
  refine ⟨a + 2, ?_⟩
  rw [(CFSG.pCore 2 ↥B).card_eq_card_quotient_mul_card_subgroup, Nat.card_congr e.toEquiv,
    card_sl2_four hF, ha, pow_add]
  ring

theorem card_sup [Finite Q] {S B : Subgroup Q} (hS : IsPGroup 2 S) (hB : IsL24Sub S B) :
    ∃ m, Nat.card ↥(B ⊔ S) = 15 * 2 ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := card_of_l24 hB
  set H := B ⊔ S
  have hBn : (B.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hB.2.2.1)
  have hq : IsPGroup 2 (↥H ⧸ B.subgroupOf H) := by
    intro x
    obtain ⟨⟨h, hh⟩, rfl⟩ := QuotientGroup.mk_surjective x
    have hh' : h ∈ ((S ⊔ B : Subgroup Q) : Set Q) := by rwa [sup_comm]
    rw [Subgroup.coe_mul_of_left_le_normalizer_right S B hB.2.2.1] at hh'
    obtain ⟨s, hs, b, hb, rfl⟩ := hh'
    obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
    refine ⟨k, ?_⟩
    have hsH : s ∈ H := Subgroup.mem_sup_right hs
    have hbH : b ∈ H := Subgroup.mem_sup_left hb
    have he : (QuotientGroup.mk (⟨s * b, H.mul_mem hsH hbH⟩ : ↥H) : ↥H ⧸ B.subgroupOf H) =
        QuotientGroup.mk ⟨s, hsH⟩ := by
      rw [QuotientGroup.eq]
      have h2 : (⟨s * b, H.mul_mem hsH hbH⟩ : ↥H)⁻¹ * ⟨s, hsH⟩ = (⟨b, hbH⟩ : ↥H)⁻¹ :=
        Subtype.ext (by simp)
      rw [h2]
      exact Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.mpr hb)
    rw [he, ← QuotientGroup.mk_pow]
    have : (⟨s, hsH⟩ : ↥H) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this]
    rfl
  obtain ⟨c, hc⟩ := hq.exists_card_eq
  refine ⟨a + c, ?_⟩
  rw [(B.subgroupOf H).card_eq_card_quotient_mul_card_subgroup, hc,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv, ha, pow_add]
  ring

theorem IsL24Sub.map {Q' : Type} [Group Q'] [Finite Q] {S B : Subgroup Q} (hB : IsL24Sub S B)
    (π : Q →* Q') (hinj : Function.Injective (π.comp B.subtype)) :
    IsL24Sub (S.map π) (B.map π) := by
  obtain ⟨hB1, hBp, hSB, F, _, _, hF, ⟨g⟩⟩ := hB
  have hrange : (π.comp B.subtype).range = B.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let f : ↥B ≃* ↥(B.map π) := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  refine ⟨fun h => hB1 ?_, by rw [← Subgroup.map_commutator, hBp],
    (Subgroup.map_mono hSB).trans (Subgroup.le_normalizer_map π),
    F, inferInstance, inferInstance, hF,
    ⟨(QuotientGroup.congr _ _ f.symm (CFSG.pCore_map_iso 2 f.symm)).trans g⟩⟩
  rw [Subgroup.map_eq_bot_iff] at h
  rw [eq_bot_iff]
  intro b hb
  have h1 : (π.comp B.subtype) ⟨b, hb⟩ = 1 := h hb
  exact congrArg Subtype.val (hinj (h1.trans (map_one _).symm))

theorem L24Unique.map_equiv {Q' : Type} [Group Q'] [Finite Q] {S : Subgroup Q}
    (h : L24Unique S) (e : Q ≃* Q') : L24Unique (S.map e.toMonoidHom) := by
  intro B₁ B₂ h₁ h₂
  have hinj : ∀ B : Subgroup Q', Function.Injective (e.symm.toMonoidHom.comp B.subtype) :=
    fun B => e.symm.injective.comp B.subtype_injective
  have hS : (S.map e.toMonoidHom).map e.symm.toMonoidHom = S := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id S
    ext
    simp
  have := Finite.of_equiv Q e.toEquiv
  have h₁' := IsL24Sub.map h₁ e.symm.toMonoidHom (hinj B₁)
  have h₂' := IsL24Sub.map h₂ e.symm.toMonoidHom (hinj B₂)
  rw [hS] at h₁' h₂'
  have := h _ _ h₁' h₂'
  exact Subgroup.map_injective e.symm.injective this

theorem exists_conj_of_sylow [Finite Q] {U T : Subgroup Q}
    (hU : QuasithinUnique.IsSylowTwoOf U ⊤) (hT : QuasithinUnique.IsSylowTwoOf T ⊤) :
    ∃ g : Q, U.map (MulAut.conj g).toMonoidHom = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hi : ∀ V : Subgroup Q, QuasithinUnique.IsSylowTwoOf V ⊤ → ¬ 2 ∣ V.index := fun V hV => by
    have h1 : (V.subgroupOf (⊤ : Subgroup Q)).index = V.index := Subgroup.relIndex_top_right V
    rw [← h1]
    exact hV.2.2
  obtain ⟨g, hg⟩ :=
    MulAction.exists_smul_eq Q (hU.2.1.toSylow (hi U hU)) (hT.2.1.toSylow (hi T hT))
  exact ⟨g, congrArg (fun P : Sylow 2 Q => (P : Subgroup Q)) hg⟩

theorem l24Unique_of_sylow [Finite Q] {S₀ : Subgroup Q} (hS₀ : QuasithinUnique.IsSylowTwoOf S₀ ⊤)
    (h : L24Unique S₀) {S : Subgroup Q} (hS : QuasithinUnique.IsSylowTwoOf S ⊤) : L24Unique S := by
  obtain ⟨g, rfl⟩ := exists_conj_of_sylow hS₀ hS
  exact h.map_equiv (MulAut.conj g)

end CFSG.Quasithin.Vol2.Ch11.SecS.O11
