module

public import CFSG.RankThree.PartTwo.Late.Uniqueness

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item1912 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Sec19Std G → partTwoE G ⊆ partTwoT G

@[expose] def Item1920 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Sec19Std G →
    ∀ P : Sylow 3 G, (scriptM (gammaZero (P : Subgroup G) : Set G)).Nonempty

@[expose] def Item2010 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → partTwoS G = ∅ → Hyp191 G

@[expose] def GammaZeroLemma (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ P M : Subgroup G, IsPGroup 3 P → P ≤ M →
    (∀ V : Subgroup G, IsE27 V → V ≤ M → gamma 2 V ≤ M) →
    (∀ (V : Subgroup G) (g : G), IsE27 V → V ≤ M →
      V.map (MulAut.conj g).toMonoidHom ≤ M → g ∈ M) →
    gammaZero P ≤ M

section Lemmas

variable {G : Type*} [Group G]

theorem map_mem_partTwoE {G' : Type*} [Group G'] {A : Subgroup G} (hA : A ∈ partTwoE G)
    (φ : G ≃* G') : A.map φ.toMonoidHom ∈ partTwoE G' := by
  obtain ⟨hA1, hA2, U, hU, hU2, hAU⟩ := hA
  have hE := IsE27.map ⟨hA1, hA2⟩ φ
  refine ⟨hE.1, hE.2, U.map φ.toMonoidHom,
    fun h => hU ((Subgroup.map_eq_bot_iff_of_injective U φ.injective).mp h), hU2.map _, ?_⟩
  rw [← Subgroup.map_equiv_normalizer_eq]
  exact Subgroup.map_mono hAU

theorem mem_partTwoE_of_le {A M : Subgroup G} (hA : IsE27 A) (hM : IsMaximalTwoLocal M)
    (hAM : A ≤ M) : A ∈ partTwoE G := by
  obtain ⟨R, hR, hR2, hMR⟩ := hM.1
  exact ⟨hA.1, hA.2, R, hR, hR2, hMR ▸ hAM⟩

variable [Finite G]

theorem exists_map_conj_le_sylow {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA : IsPGroup p A)
    (P : Sylow p G) : ∃ g : G, A.map (MulAut.conj g).toMonoidHom ≤ P := by
  obtain ⟨Q, hQ⟩ := hA.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨g, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have hmem : MulAut.conj g • a ∈ ((g • Q : Sylow p G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hQ ha)
  rw [hg] at hmem
  simpa [MulAut.smul_def] using hmem

theorem le_of_isPGroup_of_le (h : Hyp191 G) {A M Q : Subgroup G} (hA : IsE27 A)
    (hM : M ∈ scriptM (gamma 2 A : Set G)) (hQ : IsPGroup 3 Q) (hAQ : A ≤ Q) : Q ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hQM
  have hlt : Q ⊓ M < Q := lt_of_le_of_ne inf_le_left fun heq => hQM (heq ▸ inf_le_right)
  obtain ⟨y, hyQ, hyQM, hyN⟩ := exists_mem_normalizer_not_mem_of_lt hQ hlt
  have hyM : y ∈ M := by
    refine mem_of_map_conj_le h hA hM ?_
    calc A.map (MulAut.conj y).toMonoidHom ≤ (Q ⊓ M).map (MulAut.conj y).toMonoidHom :=
          Subgroup.map_mono (le_inf hAQ (le_of_mem_scriptM_gamma hA hM))
      _ = Q ⊓ M := map_conj_eq_of_mem_normalizer hyN
      _ ≤ M := inf_le_right
  exact hyQM ⟨hyQ, hyM⟩

theorem mem_scriptM_gamma_of_le (h : Hyp191 G) (hET : partTwoE G ⊆ partTwoT G)
    {A M V : Subgroup G} (hA : IsE27 A) (hM : M ∈ scriptM (gamma 2 A : Set G)) (hV : IsE27 V)
    (hVM : V ≤ M) : M ∈ scriptM (gamma 2 V : Set G) := by
  obtain ⟨-, M', hM'⟩ := mem_partTwoT_iff.mp (hET (mem_partTwoE_of_le hV hM.1 hVM))
  rwa [rank3II_19_2 h hV hA hM' hM hVM] at hM'

end Lemmas

theorem rank3II_19_20_of_gammaZeroLemma {G : Type} [Group G] [Finite G] (h : Sec19Std G)
    (hΓ : GammaZeroLemma G) (hET : partTwoE G ⊆ partTwoT G) (P : Sylow 3 G) :
    (scriptM (gammaZero (P : Subgroup G) : Set G)).Nonempty := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨A₀, hA₀⟩ := (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).2
  obtain ⟨g, hg⟩ := exists_map_conj_le_sylow (isE27_of_mem_partTwoE hA₀).isPGroup P
  have hA : A₀.map (MulAut.conj g).toMonoidHom ∈ partTwoE G :=
    map_mem_partTwoE hA₀ (MulAut.conj g)
  have hAE := isE27_of_mem_partTwoE hA
  obtain ⟨-, M, hM⟩ := mem_partTwoT_iff.mp (hET hA)
  have hPM : (P : Subgroup G) ≤ M := le_of_isPGroup_of_le h.hyp191 hAE hM P.isPGroup' hg
  refine ⟨M, hM.1, ?_⟩
  exact hΓ P M P.isPGroup' hPM
    (fun V hV hVM => (mem_scriptM_gamma_of_le h.hyp191 hET hAE hM hV hVM).2)
    (fun V g hV hVM hVg => mem_of_map_conj_le h.hyp191 hV
      (mem_scriptM_gamma_of_le h.hyp191 hET hAE hM hV hVM) hVg)

theorem rank3II_19_20_reduction (hΓ : ∀ (G : Type) [Group G] [Finite G], GammaZeroLemma G)
    (h1912 : Item1912) : Item1920 :=
  fun G _ _ h P => rank3II_19_20_of_gammaZeroLemma h (hΓ G) (h1912 G h) P

theorem rank3II_20_11_reduction (h2010 : Item2010) (h1920 : Item1920) : Item2011 :=
  fun G _ _ hst hS P => h1920 G ⟨hst, hS, h2010 G hst hS⟩ P

theorem item2011_of_items (h2010 : Item2010) (h1912 : Item1912)
    (hΓ : ∀ (G : Type) [Group G] [Finite G], GammaZeroLemma G) : Item2011 :=
  rank3II_20_11_reduction h2010 (rank3II_19_20_reduction hΓ h1912)

end CFSG.RankThree.PartTwo.Late
