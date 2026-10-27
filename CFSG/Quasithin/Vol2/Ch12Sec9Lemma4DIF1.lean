module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF1Syl

public section

namespace CFSG.Quasithin.H13.C1294

theorem factF1_holds : FactF1 := by
  unfold FactF1
  refine ⟨?_, ?_⟩
  · intro I _ _ _ hI B₀ hB hodd
    obtain ⟨p, ℓ, Pl, hp, hℓ, hPl, hpℓ, hℓPl⟩ := exists_std_flag hI
    have hK : Nat.card (stabS p ⊓ stabS ℓ ⊓ stabS Pl : Subgroup (I ≃ₗ[ZMod 2] I)) = 64 :=
      natCard_std_flag hI hp hℓ hPl hpℓ.le hℓPl.le
    have hKp : IsPGroup 2 (stabS p ⊓ stabS ℓ ⊓ stabS Pl : Subgroup (I ≃ₗ[ZMod 2] I)) :=
      (IsPGroup.iff_card (p := 2)).2 ⟨6, hK.trans (by norm_num)⟩
    have hB64 : Nat.card B₀ = 64 := natCard_of_two_group_odd_index (natCard_GL_four hI) hB hodd
    obtain ⟨c, hc⟩ := exists_conj_of_card_64 (natCard_GL_four hI) hB hKp hB64 hK
    refine ⟨p.map (c : I →ₗ[ZMod 2] I), ℓ.map (c : I →ₗ[ZMod 2] I), Pl.map (c : I →ₗ[ZMod 2] I),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [LinearEquiv.finrank_map_eq]
      exact hp
    · rw [LinearEquiv.finrank_map_eq]
      exact hℓ
    · rw [LinearEquiv.finrank_map_eq]
      exact hPl
    · exact flag_lt_of_le_finrank_ne (Submodule.map_mono hpℓ.le)
        (by rw [LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq, hp, hℓ]; norm_num)
    · exact flag_lt_of_le_finrank_ne (Submodule.map_mono hℓPl.le)
        (by rw [LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq, hℓ, hPl]; norm_num)
    · rw [hc, map_flagStab_conj]
  · intro I _ _ _ hI p ℓ Pl hp hℓ hPl hpℓ hℓPl
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := index_flag_values hI hp hℓ hPl hpℓ.le hℓPl.le
    refine ⟨i2, i1, i3, i4, i5, i6, i7, ?_⟩
    intro X hX
    have hmem : X ∈ {X : Subgroup (I ≃ₗ[ZMod 2] I) | stabS p ⊓ stabS ℓ ⊓ stabS Pl ≤ X} := hX
    rw [overgroups_flag_eq hI hp hℓ hPl hpℓ.le hℓPl.le] at hmem
    simpa only [flagSet, Set.mem_insert_iff, Set.mem_singleton_iff] using hmem

end CFSG.Quasithin.H13.C1294
