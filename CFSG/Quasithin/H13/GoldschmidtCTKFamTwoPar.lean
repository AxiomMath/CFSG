module

public import CFSG.Quasithin.H13.GoldschmidtCTKFamTwoLevi
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Rank2Glue

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open CFSG.ABGLocalTools (IsSylowOf.inf_of_le_normalizer)
open CFSG.QuasithinUnique.A5.G3 (perfectCore_parabolic_cases)

theorem NoA5Block.of_mulEquiv {B B' : Type} [Group B] [Group B'] (e : B ≃* B')
    (h : NoA5Block B') : NoA5Block B := by
  intro K V T₁ E hVK hΔ hT₁K hE hT₁E hrel
  refine h (K.map e.toMonoidHom) (V.map e.toMonoidHom) (T₁.map e.toMonoidHom)
    (E.map e.toMonoidHom) (Subgroup.map_mono hVK) ?_ ?_ ?_ (Subgroup.map_mono hT₁E) ?_
  · let eK : ↥K ≃* ↥(K.map e.toMonoidHom) := e.subgroupMap K
    refine IsDelta5Ext.of_mulEquiv eK (fun x => ?_) hΔ
    change (x : B) ∈ V ↔ e (x : B) ∈ V.map e.toMonoidHom
    rw [Subgroup.mem_map_equiv]
    simp
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hT₁K
  · have h1 := (CFSG.QuasithinUnique.Setup.Layer.isSylowTwoOf_map_mulEquiv e (X := E) (Y := ⊤)).2
      hE
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at h1
  · rwa [Subgroup.relIndex_map_map_of_injective _ _ e.injective]

noncomputable def perfectCoreEquivMap {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]
    (f : X →* Y) (hf : Function.Injective f) (P : Subgroup X) :
    ↥(perfectCore P) ≃* ↥(perfectCore (P.map f)) :=
  ((perfectCore P).equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr (map_perfectCore f P))

theorem NoA5Block.perfectCore_map {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]
    (f : X →* Y) (hf : Function.Injective f) {P : Subgroup X} (h : NoA5Block ↥(perfectCore P)) :
    NoA5Block ↥(perfectCore (P.map f)) :=
  NoA5Block.of_mulEquiv (perfectCoreEquivMap f hf P).symm h

theorem NoA5Block.of_perfectCore_map {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]
    (f : X →* Y) (hf : Function.Injective f) {P : Subgroup X}
    (h : NoA5Block ↥(perfectCore (P.map f))) : NoA5Block ↥(perfectCore P) :=
  NoA5Block.of_mulEquiv (perfectCoreEquivMap f hf P) h

section Sylow

variable {S : Type} [Group S] [Finite S]

theorem card_le_of_isSylowTwoOf {X T' T : Subgroup S} (h' : IsSylowTwoOf T' X)
    (h : IsSylowTwoOf T ⊤) : Nat.card T' ≤ Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have c' := CFSG.ABGLocalTools.IsSylowOf.card_eq (isSylowTwoOf_iff_isSylowOf.1 h')
  have c := CFSG.ABGLocalTools.IsSylowOf.card_eq (isSylowTwoOf_iff_isSylowOf.1 h)
  rw [c', c]
  apply Nat.pow_le_pow_right (by norm_num)
  have hdvd : Nat.card X ∣ Nat.card ↥(⊤ : Subgroup S) := by
    rw [Subgroup.card_top]
    exact Subgroup.card_subgroup_dvd_card X
  exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hdvd 2

theorem not_noA5Block_perfectCore {K V T₁ T₂ P' : Subgroup S} (hVK : V ≤ K)
    (hΔ : IsDelta5Ext ↥K (V.subgroupOf K)) (hT₁K : T₁ ≤ Subgroup.normalizer (K : Set S))
    (hT₁P : T₁ ≤ P') (hKP : K ≤ P') (hT₁2 : IsPGroup 2 T₁) (hT₂ : IsSylowTwoOf T₂ ⊤)
    (hT₁T₂ : T₁ ≤ T₂) (hrel : T₁.relIndex T₂ ≤ 2) : ¬ NoA5Block ↥(perfectCore P') := by
  intro hno
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKB : K ≤ perfectCore P' := le_perfectCore_of_perfect hKP hΔ.perfect
  obtain ⟨T₂', hT₂'S, hT₁T₂'⟩ := EscapingLocal.exists_isSylowTwoOf_ge hT₁P hT₁2
  have hrel' : T₁.relIndex T₂' ≤ 2 := by
    have h1 := Subgroup.relIndex_mul_card T₁ T₂'
    have h2 := Subgroup.relIndex_mul_card T₁ T₂
    rw [inf_eq_left.2 hT₁T₂'] at h1
    rw [inf_eq_left.2 hT₁T₂] at h2
    have hpos : 0 < Nat.card T₁ := Nat.card_pos
    have hle : T₁.relIndex T₂' * Nat.card T₁ ≤ T₁.relIndex T₂ * Nat.card T₁ := by
      rw [h1, h2]
      exact card_le_of_isSylowTwoOf hT₂'S hT₂
    exact (Nat.le_of_mul_le_mul_right hle hpos).trans hrel
  have hPn : P' ≤ Subgroup.normalizer (perfectCore P' : Set S) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore P')
  have hEsyl : IsSylowTwoOf ((T₂' ⊓ perfectCore P').subgroupOf (perfectCore P')) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (IsSylowOf.inf_of_le_normalizer (isSylowTwoOf_iff_isSylowOf.1 hT₂'S)
        (perfectCore_le P') hPn))
  refine hno (K.subgroupOf (perfectCore P')) (V.subgroupOf (perfectCore P'))
    ((T₁ ⊓ perfectCore P').subgroupOf (perfectCore P')) _ (fun x hx => hVK hx) ?_ ?_ hEsyl ?_ ?_
  · refine IsDelta5Ext.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKB).symm (fun x => ?_) hΔ
    simp only [Subgroup.mem_subgroupOf]
    rfl
  · intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have ht' : (t : S) ∈ Subgroup.normalizer (K : Set S) := hT₁K (Subgroup.mem_subgroupOf.1 ht).1
    have hmem := Subgroup.mem_normalizer_iff.1 ht' (x : S)
    exact hmem
  · intro x hx
    exact ⟨hT₁T₂' hx.1, hx.2⟩
  · rw [Subgroup.relIndex_subgroupOf (inf_le_right : T₂' ⊓ perfectCore P' ≤ perfectCore P')]
    have h4 : T₁ ⊓ perfectCore P' = T₁ ⊓ (T₂' ⊓ perfectCore P') := by
      ext x
      simp only [Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.1, hT₁T₂' h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [h4, Subgroup.inf_relIndex_right]
    exact (Subgroup.relIndex_le_of_le_right (inf_le_left : T₂' ⊓ perfectCore P' ≤ T₂')
      Subgroup.index_ne_zero_of_finite).trans hrel'

theorem A5Config.false_of_residual (hH : CFSG.LieType.BorelTits.Holds S 2) {U : Subgroup S}
    (hU : IsSylowTwoOf U ⊤) {P : Fin 2 → Subgroup S} (hP : ResidualOvergroupsAt S U P)
    (hno : ∀ j, NoA5Block ↥(perfectCore (P j))) (h : A5Config S) : False := by
  obtain ⟨K, V, T₁, T₂, hVK, hV16, -, hΔ, hT₁K, hNV, hT₁s, hT₂s, hT₁T₂, hrel⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 V := hΔ.isPGroup_of_le hVK
  have hV0 : V ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hV16
    omega
  obtain ⟨S₀, P', hP'top, hNP', -, -, hS₀⟩ := hH V hV0 hV2
  have hpar : IsParabolic2 (⊤ : Subgroup S) P' := by
    refine ⟨le_top, (S₀ : Subgroup S), ⟨le_top, S₀.isPGroup', ?_⟩, fun x hx => hS₀ hx.2⟩
    rw [show ((S₀ : Subgroup S).subgroupOf ⊤).index = (S₀ : Subgroup S).index from
      Subgroup.relIndex_top_right _]
    exact S₀.not_dvd_index
  have hKP : K ≤ P' := (hNV ▸ le_sup_left : K ≤ Subgroup.normalizer (V : Set S)).trans hNP'
  have hT₁P : T₁ ≤ P' := (hNV ▸ le_sup_right : T₁ ≤ Subgroup.normalizer (V : Set S)).trans hNP'
  rcases perfectCore_parabolic_cases hU hP hpar hP'top with h0 | ⟨j, ⟨φ⟩⟩
  · have hKB : K ≤ perfectCore P' := le_perfectCore_of_perfect hKP hΔ.perfect
    rw [h0, le_bot_iff] at hKB
    exact hV0 (le_bot_iff.1 (hKB ▸ hVK))
  · exact not_noA5Block_perfectCore hVK hΔ hT₁K hT₁P hKP hT₁s.2.1 hT₂s hT₁T₂ hrel
      (NoA5Block.of_mulEquiv φ (hno j))

theorem A5Config.false_of_residual_equiv {X : Type} [Group X] [Finite X] (e : S ≃* X)
    (hH : CFSG.LieType.BorelTits.Holds S 2) {U : Subgroup X} (hU : IsSylowTwoOf U ⊤)
    {P : Fin 2 → Subgroup X} (hP : ResidualOvergroupsAt X U P)
    (hno : ∀ j, NoA5Block ↥(perfectCore (P j))) (h : A5Config S) : False := by
  refine A5Config.false_of_residual hH (U := U.map e.symm.toMonoidHom) ?_
    (P := fun j => (P j).map e.symm.toMonoidHom) (hP.map e.symm) (fun j => ?_) h
  · have h1 := (CFSG.QuasithinUnique.Setup.Layer.isSylowTwoOf_map_mulEquiv e.symm (X := U)
      (Y := ⊤)).2 hU
    rwa [Subgroup.map_top_of_surjective _ e.symm.surjective] at h1
  · exact NoA5Block.perfectCore_map e.symm.toMonoidHom e.symm.injective (hno j)

end Sylow

end CFSG.Quasithin.H13.CTK
