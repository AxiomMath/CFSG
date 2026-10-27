module

public import CFSG.Quasithin.Background.SmithC27RLieBasic

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

section Image

variable {Γ Γ' : Type} [Group Γ] [Group Γ'] [Finite Γ]

theorem isSylowTwoOf_map_top_of_surjective {f : Γ →* Γ'} (hf : Function.Surjective f)
    {S : Subgroup Γ} (hS : IsSylowTwoOf S ⊤) : IsSylowTwoOf (S.map f) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Γ' := Finite.of_surjective f hf
  obtain ⟨P, rfl⟩ := exists_sylow_two_coe_eq hS
  have h := sylow_two_isSylowTwoOf_top (Sylow.mapSurjective hf P)
  rwa [Sylow.coe_mapSurjective] at h

theorem exists_isSylowTwoOf_map_eq {f : Γ →* Γ'} (hf : Function.Surjective f) {S' : Subgroup Γ'}
    (hS' : IsSylowTwoOf S' ⊤) : ∃ S : Subgroup Γ, IsSylowTwoOf S ⊤ ∧ S.map f = S' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Γ' := Finite.of_surjective f hf
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 Γ))
  obtain ⟨g', hg'⟩ := exists_map_conj_eq_of_sylow
    (isSylowTwoOf_map_top_of_surjective hf (sylow_two_isSylowTwoOf_top P)) hS'
  obtain ⟨g, rfl⟩ := hf g'
  refine ⟨((g • P : Sylow 2 Γ) : Subgroup Γ), sylow_two_isSylowTwoOf_top _, ?_⟩
  rw [← hg', Sylow.coe_subgroup_smul]
  change ((P : Subgroup Γ).map (MulAut.conj g).toMonoidHom).map f = _
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

end Image

theorem le_of_normalizer_le {Γ : Type} [Group Γ] {Z S P : Subgroup Γ}
    (hZ : Z ≤ Subgroup.center Γ) (hSP : Subgroup.normalizer (S : Set Γ) ≤ P) : Z ≤ P :=
  hZ.trans ((Subgroup.center_le_normalizer _).trans hSP)

section Quotient

variable {Γ : Type} [Group Γ] [Finite Γ] (Z : Subgroup Γ) [Z.Normal]

omit [Finite Γ] in
theorem map_normalizer_eq_of_central (hZ : Z ≤ Subgroup.center Γ) (hZo : Odd (Nat.card Z))
    {U : Subgroup Γ} (hU : IsPGroup 2 U) :
    (Subgroup.normalizer (U : Set Γ)).map (QuotientGroup.mk' Z) =
      Subgroup.normalizer (U.map (QuotientGroup.mk' Z) : Set (Γ ⧸ Z)) := by
  rw [normalizer_eq_comap_normalizer_map Z hZ (Nat.coprime_two_right.mpr hZo) hU,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z)]

theorem isRadicalParabolic_top_of_quotient (hZ : Z ≤ Subgroup.center Γ) (hZo : Odd (Nat.card Z))
    (h : IsRadicalParabolic (⊤ : Subgroup (Γ ⧸ Z))) : IsRadicalParabolic (⊤ : Subgroup Γ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZr : Nat.Coprime (Nat.card Z) 2 := Nat.coprime_two_right.mpr hZo
  set π := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  intro U _ hU1 hU2 hUO
  rw [top_inf_eq] at hUO ⊢
  have hN := map_normalizer_eq_of_central Z hZ hZo hU2
  have hU1' : U.map π ≠ ⊥ := by
    intro hbot
    apply hU1
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨n, hn⟩ := hU2 ⟨u, hu⟩
    have hun : u ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hu' : π u ∈ (⊥ : Subgroup Γ).map π := by
      rw [Subgroup.map_bot, ← hbot]
      exact Subgroup.mem_map_of_mem _ hu
    exact mem_of_mk_mem_map Z hZ hZr IsPGroup.of_bot hu' hun
  have hcore : pCoreOf 2 (⊤ ⊓ Subgroup.normalizer (U.map π : Set (Γ ⧸ Z))) = U.map π := by
    rw [top_inf_eq]
    refine le_antisymm ?_ ?_
    · refine (pCoreOf_le_map_pCoreOf_comap Z hZ hZr _).trans ?_
      rw [← normalizer_eq_comap_normalizer_map Z hZ hZr hU2, hUO]
    · rw [← hN]
      calc U.map π = (pCoreOf 2 (Subgroup.normalizer (U : Set Γ))).map π := by rw [hUO]
        _ ≤ pCoreOf 2 ((Subgroup.normalizer (U : Set Γ)).map π) := map_pCoreOf_le π _
  obtain ⟨-, S', hS', hS'N⟩ := h (U.map π) le_top hU1' (hU2.map π) hcore
  obtain ⟨S, hS, rfl⟩ := exists_isSylowTwoOf_map_eq hπ hS'
  refine ⟨le_top, S, hS, ?_⟩
  rw [top_inf_eq, top_inf_eq] at *
  rw [normalizer_eq_comap_normalizer_map Z hZ hZr hS.2.1,
    normalizer_eq_comap_normalizer_map Z hZ hZr hU2]
  exact Subgroup.comap_mono hS'N

theorem maxParabolicMaximal_top_of_quotient (hZ : Z ≤ Subgroup.center Γ)
    (hZo : Odd (Nat.card Z)) (h : MaxParabolicMaximal (⊤ : Subgroup (Γ ⧸ Z))) :
    MaxParabolicMaximal (⊤ : Subgroup Γ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZr : Nat.Coprime (Nat.card Z) 2 := Nat.coprime_two_right.mpr hZo
  set π := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  refine maxParabolicMaximal_of_isCoatom fun P hP hPB hPt => ?_
  obtain ⟨-, S, hS, hSP⟩ := hP
  rw [top_inf_eq] at hSP
  have hZP : π.ker ≤ P := by
    rw [hker]
    exact le_of_normalizer_le hZ hSP
  have hback : (P.map π).comap π = P := Subgroup.comap_map_eq_self hZP
  have hNS := map_normalizer_eq_of_central Z hZ hZo hS.2.1
  have hP' : IsParabolic2 ⊤ (P.map π) := by
    refine ⟨le_top, S.map π, isSylowTwoOf_map_top_of_surjective hπ hS, ?_⟩
    rw [top_inf_eq, ← hNS]
    exact Subgroup.map_mono hSP
  have hPB' : ¬ IsBorelIn ⊤ (P.map π) := by
    rintro ⟨T', hT', hPT'⟩
    obtain ⟨T, hT, rfl⟩ := exists_isSylowTwoOf_map_eq hπ hT'
    apply hPB
    refine ⟨T, hT, ?_⟩
    rw [top_inf_eq] at hPT' ⊢
    rw [← hback, hPT', normalizer_eq_comap_normalizer_map Z hZ hZr hT.2.1]
  have hPt' : P.map π ≠ ⊤ := by
    intro htop
    apply hPt
    rw [← hback, htop, Subgroup.comap_top]
  obtain ⟨-, hY⟩ := h (P.map π) hP' hPB' hPt'
  refine ⟨hPt, fun Y hPY => ?_⟩
  by_contra hYt
  have hYZ : π.ker ≤ Y := hZP.trans hPY.le
  have hYt' : Y.map π ≠ ⊤ := by
    intro htop
    apply hYt
    rw [← Subgroup.comap_map_eq_self hYZ, htop, Subgroup.comap_top]
  have hYP := hY (Y.map π) (Subgroup.map_mono hPY.le) hYt' le_top
  apply hPY.ne
  rw [← hback, ← hYP, Subgroup.comap_map_eq_self hYZ]

end Quotient

section Central

variable {Γ Γ' : Type} [Group Γ] [Group Γ'] [Finite Γ]

noncomputable def topQuotientKerEquiv (f : Γ →* Γ') (hf : Function.Surjective f) :
    ↥(⊤ : Subgroup (Γ ⧸ f.ker)) ≃* ↥(⊤ : Subgroup Γ') :=
  Subgroup.topEquiv.trans ((QuotientGroup.quotientKerEquivOfSurjective f hf).trans
    Subgroup.topEquiv.symm)

end Central

end CFSG.Quasithin.SmithC27
