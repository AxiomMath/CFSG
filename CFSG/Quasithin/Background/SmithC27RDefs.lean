module

public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.EmptyFaithful.SBd3Transport

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def IsRadicalParabolic {Γ : Type} [Group Γ] (L : Subgroup Γ) : Prop :=
  ∀ U : Subgroup Γ, U ≤ L → U ≠ ⊥ → IsPGroup 2 U →
    pCoreOf 2 (L ⊓ Subgroup.normalizer (U : Set Γ)) = U →
    IsParabolic2 L (L ⊓ Subgroup.normalizer (U : Set Γ))

@[expose] def MaxParabolicMaximal {Γ : Type} [Group Γ] (L : Subgroup Γ) : Prop :=
  ∀ P : Subgroup Γ, IsParabolic2 L P → ¬ IsBorelIn L P → P ≠ L →
    IsMaxParabolic2 L P ∧ ∀ Y : Subgroup Γ, P ≤ Y → Y ≠ L → Y ≤ L → Y = P

section Transport

variable {A B : Type} [Group A] [Group B]

theorem pCoreOf_map_of_injective' (ι : A →* B) (hι : Function.Injective ι) (P : Subgroup A) :
    pCoreOf 2 (P.map ι) = (pCoreOf 2 P).map ι := by
  let e : P ≃* (P.map ι) := P.equivMapOfInjective ι hι
  have h1 := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e
  unfold pCoreOf
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem map_inf_normalizer_of_injective (ι : A →* B) (hι : Function.Injective ι)
    (L U : Subgroup A) :
    (L ⊓ Subgroup.normalizer (U : Set A)).map ι =
      L.map ι ⊓ Subgroup.normalizer ((U.map ι : Subgroup B) : Set B) := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxL, hxN⟩, rfl⟩
    exact ⟨⟨x, hxL, rfl⟩, (SBd3T.map_mem_normalizer_iff ι hι U x).2 hxN⟩
  · rintro ⟨⟨x, hxL, rfl⟩, hyN⟩
    exact ⟨x, ⟨hxL, (SBd3T.map_mem_normalizer_iff ι hι U x).1 hyN⟩, rfl⟩

theorem isBorelIn_map_iff (ι : A →* B) (hι : Function.Injective ι) (L P : Subgroup A) :
    IsBorelIn (L.map ι) (P.map ι) ↔ IsBorelIn L P := by
  constructor
  · rintro ⟨S', hS', hP⟩
    have hrange : S' ≤ ι.range := hS'.1.trans (Subgroup.map_le_range _ _)
    have hS'e : (S'.comap ι).map ι = S' := Subgroup.map_comap_eq_self hrange
    rw [← hS'e] at hS' hP
    refine ⟨S'.comap ι, (SBd3T.isSylowTwoOf_map_iff ι hι _ _).1 hS', ?_⟩
    rw [← map_inf_normalizer_of_injective ι hι] at hP
    exact Subgroup.map_injective hι hP
  · rintro ⟨S, hS, rfl⟩
    exact ⟨S.map ι, (SBd3T.isSylowTwoOf_map_iff ι hι _ _).2 hS,
      map_inf_normalizer_of_injective ι hι L S⟩

theorem exists_eq_map_of_le_map {ι : A →* B} (hι : Function.Injective ι) {L : Subgroup A}
    {U' : Subgroup B} (hU' : U' ≤ L.map ι) : ∃ U : Subgroup A, U ≤ L ∧ U.map ι = U' := by
  refine ⟨U'.comap ι, fun x hx => (Subgroup.mem_map_iff_mem hι).1 (hU' hx), ?_⟩
  exact Subgroup.map_comap_eq_self (hU'.trans (Subgroup.map_le_range _ _))

theorem isRadicalParabolic_map_iff (ι : A →* B) (hι : Function.Injective ι) (L : Subgroup A) :
    IsRadicalParabolic (L.map ι) ↔ IsRadicalParabolic L := by
  have key : ∀ U : Subgroup A, U ≤ L →
      ((U.map ι ≠ ⊥ ↔ U ≠ ⊥) ∧ (IsPGroup 2 ↥(U.map ι) ↔ IsPGroup 2 ↥U) ∧
        (pCoreOf 2 (L.map ι ⊓ Subgroup.normalizer ((U.map ι : Subgroup B) : Set B)) = U.map ι ↔
          pCoreOf 2 (L ⊓ Subgroup.normalizer (U : Set A)) = U) ∧
        (IsParabolic2 (L.map ι) (L.map ι ⊓ Subgroup.normalizer ((U.map ι : Subgroup B) : Set B)) ↔
          IsParabolic2 L (L ⊓ Subgroup.normalizer (U : Set A)))) := by
    intro U _
    refine ⟨(Subgroup.map_eq_bot_iff_of_injective U hι).not, SBd3T.isPGroup_map_iff ι hι U, ?_, ?_⟩
    · rw [← map_inf_normalizer_of_injective ι hι, pCoreOf_map_of_injective' ι hι]
      exact (Subgroup.map_injective hι).eq_iff
    · rw [← map_inf_normalizer_of_injective ι hι]
      exact SBd3T.isParabolic2_map_iff ι hι _ _
  constructor
  · intro h U hUL hU1 hU2 hUO
    obtain ⟨h1, h2, h3, h4⟩ := key U hUL
    exact h4.1 (h (U.map ι) (Subgroup.map_mono hUL) (h1.2 hU1) (h2.2 hU2) (h3.2 hUO))
  · intro h U' hU'L hU'1 hU'2 hU'O
    obtain ⟨U, hUL, rfl⟩ := exists_eq_map_of_le_map hι hU'L
    obtain ⟨h1, h2, h3, h4⟩ := key U hUL
    exact h4.2 (h U hUL (h1.1 hU'1) (h2.1 hU'2) (h3.1 hU'O))

theorem maxParabolicMaximal_map_iff (ι : A →* B) (hι : Function.Injective ι) (L : Subgroup A) :
    MaxParabolicMaximal (L.map ι) ↔ MaxParabolicMaximal L := by
  have hinj := Subgroup.map_injective hι
  constructor
  · intro h P hP hPB hPL
    obtain ⟨hmax, hY⟩ := h (P.map ι) ((SBd3T.isParabolic2_map_iff ι hι _ _).2 hP)
      (fun hB => hPB ((isBorelIn_map_iff ι hι _ _).1 hB)) (hinj.ne_iff.2 hPL)
    refine ⟨(SBd3T.isMaxParabolic2_map_iff ι hι _ _).1 hmax, fun Y hPY hYL hYle => ?_⟩
    exact hinj (hY (Y.map ι) (Subgroup.map_mono hPY) (hinj.ne_iff.2 hYL) (Subgroup.map_mono hYle))
  · intro h P' hP' hP'B hP'L
    obtain ⟨P, hPL, rfl⟩ := exists_eq_map_of_le_map hι hP'.1
    obtain ⟨hmax, hY⟩ := h P ((SBd3T.isParabolic2_map_iff ι hι _ _).1 hP')
      (fun hB => hP'B ((isBorelIn_map_iff ι hι _ _).2 hB)) (hinj.ne_iff.1 hP'L)
    refine ⟨(SBd3T.isMaxParabolic2_map_iff ι hι _ _).2 hmax, fun Y' hPY' hY'L hY'le => ?_⟩
    obtain ⟨Y, hYL, rfl⟩ := exists_eq_map_of_le_map hι hY'le
    rw [hY Y ((Subgroup.map_le_map_iff_of_injective hι).1 hPY') (hinj.ne_iff.1 hY'L) hYL]

theorem isRadicalParabolic_iff_top (L : Subgroup A) :
    IsRadicalParabolic L ↔ IsRadicalParabolic (⊤ : Subgroup ↥L) := by
  rw [← isRadicalParabolic_map_iff L.subtype L.subtype_injective ⊤, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem maxParabolicMaximal_iff_top (L : Subgroup A) :
    MaxParabolicMaximal L ↔ MaxParabolicMaximal (⊤ : Subgroup ↥L) := by
  rw [← maxParabolicMaximal_map_iff L.subtype L.subtype_injective ⊤, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem isRadicalParabolic_congr {L : Subgroup A} {L' : Subgroup B} (e : ↥L ≃* ↥L') :
    IsRadicalParabolic L ↔ IsRadicalParabolic L' := by
  rw [isRadicalParabolic_iff_top L, isRadicalParabolic_iff_top L',
    ← isRadicalParabolic_map_iff e.toMonoidHom e.injective ⊤, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.2 e.surjective]

theorem maxParabolicMaximal_congr {L : Subgroup A} {L' : Subgroup B} (e : ↥L ≃* ↥L') :
    MaxParabolicMaximal L ↔ MaxParabolicMaximal L' := by
  rw [maxParabolicMaximal_iff_top L, maxParabolicMaximal_iff_top L',
    ← maxParabolicMaximal_map_iff e.toMonoidHom e.injective ⊤, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.2 e.surjective]

end Transport

end CFSG.Quasithin.SmithC27
