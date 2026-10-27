module

public import CFSG.LocalAnalysis.StandardType.GGF4LabelH4Pieces
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggF4Untw_C {p f f' : ℕ} (hpf : p ∣ 2 ^ f - 1) {kk : LargeEvenLabel}
    (hrow : GGTablePRow p ⟨.A, 2, f⟩ kk) (hiso : GGLabelIso kk ⟨.C, 3, f'⟩) :
    kk = ⟨.C, 3, f⟩ := by
  obtain ⟨t, r, n⟩ := kk
  simp [GGTablePRow, hpf] at hrow
  simp [GGLabelIso] at hiso
  simp only [LargeEvenLabel.mk.injEq]
  rcases hiso with ⟨h1, h2, h3⟩ | ⟨h1 | h1, h2, h3⟩ <;> subst_vars <;> simp_all <;> omega

theorem ggF4Untw_twD {p f f' : ℕ} (hpf : p ∣ 2 ^ f - 1) {kk : LargeEvenLabel}
    (hrow : GGTablePRow p ⟨.A, 2, f⟩ kk) (hiso : GGLabelIso kk ⟨.twD, 4, f'⟩) :
    kk = ⟨.twD, 4, f⟩ := by
  obtain ⟨t, r, n⟩ := kk
  simp [GGTablePRow, hpf] at hrow
  simp [GGLabelIso] at hiso
  simp only [LargeEvenLabel.mk.injEq]
  rcases hiso with ⟨h1, h2, h3⟩ <;> subst_vars <;> simp_all <;> omega

theorem ggF4Untw_A {p f r₀ : ℕ} (hpf : p ∣ 2 ^ f - 1) (hr : r₀ = 5 ∨ r₀ = 6) (hp3 : p = 3)
    {kk : LargeEvenLabel} (hrow : GGTablePRow p ⟨.A, 2, f⟩ kk)
    (hiso : GGLabelIso kk ⟨.A, r₀, 1⟩) : f = 2 ∧ kk = ⟨.A, r₀, 1⟩ := by
  obtain ⟨t, r, n⟩ := kk
  simp [GGTablePRow, hpf] at hrow
  simp [GGLabelIso] at hiso
  simp only [LargeEvenLabel.mk.injEq]
  rcases hr with hr | hr <;> subst hr <;> subst hp3 <;>
  rcases hiso with ⟨h1, h2, h3⟩ <;> subst_vars <;> simp_all <;> omega

theorem ggF4Untw_U {p f f' : ℕ} (hpf : p ∣ 2 ^ f - 1) {kk : LargeEvenLabel}
    (hrow : GGTablePRow p ⟨.A, 2, f⟩ kk) (hiso : GGLabelIso kk ⟨.twA, 5, f'⟩) :
    f = 2 * f' ∧ kk = ⟨.twA, 5, f'⟩ := by
  obtain ⟨t, r, n⟩ := kk
  simp [GGTablePRow, hpf] at hrow
  simp [GGLabelIso] at hiso
  simp only [LargeEvenLabel.mk.injEq]
  rcases hiso with ⟨h1, h2, h3⟩ <;> subst_vars <;> simp_all <;> omega

theorem ggF4Untw_A2 {f : ℕ} {jj : LargeEvenLabel} (hiso : GGLabelIso jj ⟨.A, 2, f⟩) :
    jj = ⟨.A, 2, f⟩ := by
  obtain ⟨t, r, n⟩ := jj
  simp [GGLabelIso] at hiso
  simp only [LargeEvenLabel.mk.injEq]
  rcases hiso with ⟨h1, h2, h3⟩ <;> subst_vars <;> simp_all

theorem ggF4H4Untwisted_of_tableP
    (hTPn : GGNbrTablePNbrInputNarrow) (hRig : GGLabelRigidInput) (hpsl : GGF4H4Psl64) :
    GGF4H4Untwisted := by
  intro G _ _ p B Bs x L D J ks hres hB f hf hpf hLlab hJB K hK hlist
  obtain ⟨hJlab, -⟩ := hJB.1 hpf hLlab
  obtain ⟨y, hy⟩ := hres.1.2.2.2.1.2 K hK
  have hcfg : GGConfig p B Bs x L D J := hres.1.1.1
  have hInnL : GGInnerDiagOn Bs L := hres.1.1.2.2.1.1
  have hInnK : GGInnerDiagOn Bs K := hres.1.1.2.2.1.2 y K hy
  have hΛL : LargeEvenInLambda2 (⟨.A, 3, f⟩ : LargeEvenLabel) := by
    refine ⟨by show 1 ≤ f; omega, ?_⟩
    show 1 ≤ 3 ∧ (3 = 1 → 2 ≤ f)
    exact ⟨by norm_num, fun h => by omega⟩
  have hΛJ : LargeEvenInLambda2 (⟨.A, 2, f⟩ : LargeEvenLabel) := by
    refine ⟨by show 1 ≤ f; omega, ?_⟩
    show 1 ≤ 2 ∧ (2 = 1 → 2 ≤ f)
    exact ⟨by norm_num, fun h => by omega⟩
  have tp : ∀ labK : LargeEvenLabel, LargeEvenInLambda2 labK →
      GGHasLabel labK (K ⧸ Subgroup.center K) →
      ∃ labJ' labK' : LargeEvenLabel, LargeEvenInLambda2 labJ' ∧ LargeEvenInLambda2 labK' ∧
        GGTablePRow p labJ' labK' ∧ GGHasLabel labJ' (J ⧸ Subgroup.center J) ∧
        GGHasLabel labK' (K ⧸ Subgroup.center K) := fun labK hΛK hlabK =>
    hTPn.toTypeAL G p B Bs x L D J y K hcfg hInnL hInnK hy ⟨.A, 3, f⟩ ⟨.A, 2, f⟩ labK hΛL hΛJ hΛK
      ⟨rfl, le_rfl, hf, hpf, rfl⟩ hLlab hJlab hlabK
  have hiso : ∀ (labK : LargeEvenLabel) (hΛK : LargeEvenInLambda2 labK)
      (hlabK : GGHasLabel labK (K ⧸ Subgroup.center K)),
      ∃ kk : LargeEvenLabel, GGTablePRow p ⟨.A, 2, f⟩ kk ∧ GGLabelIso kk labK ∧
        GGHasLabel kk (K ⧸ Subgroup.center K) := by
    intro labK hΛK hlabK
    obtain ⟨jj, kk, hjj, hkk, hrow, hjjlab, hkklab⟩ := tp labK hΛK hlabK
    have hjj_eq : jj = ⟨.A, 2, f⟩ := ggF4Untw_A2 (hRig jj ⟨.A, 2, f⟩ _ hjj hΛJ hjjlab hJlab)
    subst hjj_eq
    exact ⟨kk, hrow, hRig kk labK _ hkk hΛK hkklab hlabK, hkklab⟩
  rcases hlist with ⟨f', hf', hdv, hC | hD⟩ | ⟨hp3, hA5 | hA6⟩ | ⟨hp5, hA52, hZ⟩ |
    ⟨f', hf', hdv, hU⟩
  ·
    have hΛK : LargeEvenInLambda2 (⟨.C, 3, f'⟩ : LargeEvenLabel) := by
      refine ⟨hf', ?_⟩
      show 2 ≤ 3 ∧ (3 = 2 → 2 ≤ f')
      exact ⟨by norm_num, fun h => by omega⟩
    obtain ⟨kk, hrow, hkiso, hkklab⟩ := hiso _ hΛK hC
    have hkk := ggF4Untw_C hpf hrow hkiso
    subst hkk
    exact Or.inl ⟨f, hf, hpf, hLlab, hkklab⟩
  ·
    have hΛK : LargeEvenInLambda2 (⟨.twD, 4, f'⟩ : LargeEvenLabel) := by
      refine ⟨hf', ?_⟩
      show 2 ≤ 4
      norm_num
    obtain ⟨kk, hrow, hkiso, hkklab⟩ := hiso _ hΛK hD
    have hkk := ggF4Untw_twD hpf hrow hkiso
    subst hkk
    exact Or.inr (Or.inl ⟨f, hf, hpf, hLlab, hkklab⟩)
  ·
    have hΛK : LargeEvenInLambda2 (⟨.A, 5, 1⟩ : LargeEvenLabel) := by
      refine ⟨le_rfl, ?_⟩
      show 1 ≤ 5 ∧ (5 = 1 → 2 ≤ 1)
      exact ⟨by norm_num, fun h => by omega⟩
    obtain ⟨kk, hrow, hkiso, hkklab⟩ := hiso _ hΛK hA5
    obtain ⟨hf2, hkk⟩ := ggF4Untw_A hpf (Or.inl rfl) hp3 hrow hkiso
    subst hkk
    subst hf2
    subst hp3
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hLlab, hkklab⟩)))))
  ·
    have hΛK : LargeEvenInLambda2 (⟨.A, 6, 1⟩ : LargeEvenLabel) := by
      refine ⟨le_rfl, ?_⟩
      show 1 ≤ 6 ∧ (6 = 1 → 2 ≤ 1)
      exact ⟨by norm_num, fun h => by omega⟩
    obtain ⟨kk, hrow, hkiso, hkklab⟩ := hiso _ hΛK hA6
    obtain ⟨hf2, hkk⟩ := ggF4Untw_A hpf (Or.inr rfl) hp3 hrow hkiso
    subst hkk
    subst hf2
    subst hp3
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hLlab, hkklab⟩)))))
  ·
    exact (hpsl G p B Bs x L D J ks hres hB f hf hpf hLlab hJB K hK hp5 hA52 hZ).elim
  ·
    have hΛK : LargeEvenInLambda2 (⟨.twA, 5, f'⟩ : LargeEvenLabel) := by
      refine ⟨by show 1 ≤ f'; omega, ?_⟩
      show 2 ≤ 5 ∧ (5 = 2 → 2 ≤ f')
      exact ⟨by norm_num, fun h => by omega⟩
    obtain ⟨kk, hrow, hkiso, hkklab⟩ := hiso _ hΛK hU
    obtain ⟨hff, hkk⟩ := ggF4Untw_U hpf hrow hkiso
    subst hkk
    subst hff
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f', hf', hdv, hLlab, hkklab⟩))))

theorem ggF4LabelH4_of_pieces_tableP
    (hTPn : GGNbrTablePNbrInputNarrow) (hRig : GGLabelRigidInput) (hlist : GGF4H4List)
    (hJ : GGF4H4JBlock) (hpsl : GGF4H4Psl64) (htw : GGF4H4Twisted) : GGF4LabelH4 :=
  ggF4LabelH4_of_pieces hlist hJ htw (ggF4H4Untwisted_of_tableP hTPn hRig hpsl)

end CFSG.StandardType

end
