module

public import CFSG.Quasithin.H13.NQCatA314L35Sub
public import CFSG.Quasithin.H13.NQCatA314SL3

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open CFSG.Open CFSG.QuasithinUnique Matrix
open CFSG.Adapters.RankTwoModelTransports CFSG.Assembly.LowTwoRank

theorem nonempty_equiv_sl35 {X : Type} [Group X] (hX : IsPSL 3 5 1 X ∨ IsSL3 5 X) :
    Nonempty (X ≃* SpecialLinearGroup (Fin 3) (ZMod 5)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rcases hX with hQ | hQ
  · obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hQ
    obtain ⟨σ⟩ := nonempty_ringEquiv_zmod_five K (by rw [hK, pow_one])
    let e₂ : ProjectiveSpecialLinearGroup (Fin 3) (ZMod 5) ≃*
        SpecialLinearGroup (Fin 3) (ZMod 5) :=
      (QuotientGroup.quotientMulEquivOfEq center_sl35).trans QuotientGroup.quotientBot
    exact ⟨e₀.trans ((projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
      ((projectiveSpecialLinearGroupCongr (Fin 3) σ).trans e₂))⟩
  · obtain ⟨K, _, _, hK, ⟨e₀⟩⟩ := hQ
    obtain ⟨σ⟩ := nonempty_ringEquiv_zmod_five K hK
    exact ⟨e₀.trans
      ((specialLinearGroupEquivStatedSL 3 K).symm.trans (specialLinearGroupCongr (Fin 3) σ))⟩

theorem desc_l3five (G : Type) [Group G] [Finite G] (L T B : Subgroup G)
    (_hT : IsSylowTwoOf T L) (hB : B ∈ lFamily T) (hBL : B ≤ L) (_hne : B ≠ L)
    (hL : IsPSL 3 5 1 ↥L ∨ IsSL3 5 ↥L)
    (hext : IsExt ↥B (fun V _ => IsElemAbelianOfRank 5 2 V) (fun Y _ => IsSL2 5 Y)) :
    ∃ P, IsMaxParabolicOf 5 L P ∧ B = perfectCore P := by
  obtain ⟨φ⟩ := nonempty_equiv_sl35 hL
  obtain ⟨V, hVn, ⟨eV⟩, ⟨eQ⟩⟩ := hext
  have hVc : Nat.card V = 25 := by
    rw [Nat.card_congr (eV.toEquiv.trans Multiplicative.toAdd), Nat.card_fun, Nat.card_zmod,
      Nat.card_fin]
    norm_num
  have hBc : Nat.card B = 3000 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup V
    rw [Nat.card_congr eQ.toEquiv, card_sl25, hVc] at h1
    exact h1
  let g : ↥B →* SpecialLinearGroup (Fin 3) (ZMod 5) := φ.toMonoidHom.comp (Subgroup.inclusion hBL)
  have hg : Function.Injective g := φ.injective.comp (Subgroup.inclusion_injective hBL)
  have hV₀ : Nat.card (V.map g) = 25 := by rw [Subgroup.card_map_of_injective hg, hVc]
  have hB₀V₀ : g.range ≤ Subgroup.normalizer
      ((V.map g : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 5))) :
        Set (SpecialLinearGroup (Fin 3) (ZMod 5))) := by
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨b * v * b⁻¹, hVn.conj_mem v hv b, by rw [map_mul, map_mul, map_inv]⟩
    · rintro ⟨w, hw, hwe⟩
      refine ⟨b⁻¹ * w * b, by simpa using hVn.conj_mem w hw b⁻¹, ?_⟩
      rw [map_mul, map_mul, map_inv, hwe]
      group
  obtain ⟨P₀, hP₀, hBP, hPc⟩ := exists_maxParabolic_sl35 hB₀V₀ hV₀
  let f : SpecialLinearGroup (Fin 3) (ZMod 5) →* G := L.subtype.comp φ.symm.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp φ.symm.injective
  have hfr : f.range = L := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ φ.symm.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hfg : ∀ b : ↥B, f (g b) = b := by
    intro b
    simp [f, g]
  have hBle : B ≤ P₀.map f := by
    intro x hx
    exact ⟨g ⟨x, hx⟩, hBP ⟨⟨x, hx⟩, rfl⟩, hfg _⟩
  have hmax := isMaxParabolicOf_map f hf hP₀
  rw [hfr] at hmax
  refine ⟨P₀.map f, hmax, ?_⟩
  have hBp : ⁅B, B⁆ = B := perfect_of_mem_cComp (show B ∈ cComp (B ⊔ T) from hB)
  have h1 : B ≤ perfectCore (P₀.map f) := le_perfectCore_of_perfect hBle hBp
  have h2 : perfectCore (P₀.map f) ≤ ⁅P₀.map f, P₀.map f⁆ :=
    calc perfectCore (P₀.map f) = ⁅perfectCore (P₀.map f), perfectCore (P₀.map f)⁆ :=
          (perfectCore_perfect _).symm
      _ ≤ ⁅P₀.map f, P₀.map f⁆ := Subgroup.commutator_mono (perfectCore_le _) (perfectCore_le _)
  have h3 : Nat.card ↥⁅P₀.map f, P₀.map f⁆ ≤ 3000 := by
    rw [← Subgroup.map_commutator, Subgroup.card_map_of_injective hf]
    exact hPc
  exact Subgroup.eq_of_le_of_card_ge h1 (by
    calc Nat.card ↥(perfectCore (P₀.map f)) ≤ Nat.card ↥⁅P₀.map f, P₀.map f⁆ :=
          Subgroup.card_le_of_le h2
      _ ≤ 3000 := h3
      _ = Nat.card B := hBc.symm)

end CFSG.Quasithin.H13.NQCat.A314D
