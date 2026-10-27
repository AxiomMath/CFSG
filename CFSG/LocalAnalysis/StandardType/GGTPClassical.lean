module

public import CFSG.LocalAnalysis.StandardType.GGTPAssembly
public import CFSG.LocalAnalysis.StandardType.GGTPWeight
public import CFSG.LocalAnalysis.StandardType.GGTPLift
public import CFSG.LocalAnalysis.StandardType.GGTPRowData

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggTP_charP_two {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) : CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hprime, hm⟩ := FiniteField.card K (ringChar K)
  have hcard : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hK
  rw [hcard] at hm
  have hdvd : ringChar K ∣ 2 ^ n := by
    rw [hm]
    exact dvd_pow_self _ m.pos.ne'
  have hrc : ringChar K = 2 :=
    (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp (Nat.Prime.dvd_of_dvd_pow hprime hdvd)
  exact hrc ▸ ringChar.charP K

private theorem ggTP_natural_rep {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (X : Subgroup (GL ι K)) :
    ∃ ρ : ↥X →* LinearMap.GeneralLinearGroup K (ι → K), Function.Injective ρ :=
  ⟨(Matrix.GeneralLinearGroup.toLin : GL ι K ≃* _).toMonoidHom.comp X.subtype,
    (Matrix.GeneralLinearGroup.toLin : GL ι K ≃* _).injective.comp X.subtype_injective⟩

private theorem ggTP_false_linear {G : Type} [Group G] [Finite G] {J K' : Subgroup G}
    (hJK : J ≤ K') (hJ : CFSG.Assembly.IsQuasisimple ↥J) (hZJ : ¬ 3 ∣ Nat.card (Subgroup.center ↥J))
    {n : ℕ} (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n - 1)
    (hhJ : GGHasLabel ⟨.A, 5, n⟩ (↥J ⧸ Subgroup.center ↥J)) {labK : LargeEvenLabel}
    (hrow : (labK.tag = .A ∧ (labK.rank = 6 ∨ labK.rank = 11 ∨ labK.rank = 12)) ∨
      (labK.tag = .twA ∧ labK.rank = 6) ∨ (labK.tag = .C ∧ labK.rank = 6) ∨
      (labK.tag = .D ∧ (labK.rank = 6 ∨ labK.rank = 7)) ∨ (labK.tag = .twD ∧ labK.rank = 7))
    (h3K : labK.tag = .A → labK.rank = 11 → 3 ∣ 2 ^ labK.n + 1)
    (hhK : GGHasLabel labK (↥K' ⧸ Subgroup.center ↥K')) : False := by
  obtain ⟨ι, _, _, K, _, _, H, ⟨eK⟩, hι, hchar, hZ⟩ := ggTPRowData hrow h3K hhK
  obtain ⟨X, π, hXH, hπ, hker⟩ := ggTPLift H hZ hJK eK hJ hZJ
  obtain ⟨Kf, _, _, hKf, ⟨eJ⟩⟩ := hhJ
  haveI : CharP Kf 2 := ggTP_charP_two hn hKf
  have h3Kf : 3 ∣ Nat.card Kf - 1 := by rw [hKf]; exact h3
  obtain ⟨ρ, hρ⟩ := ggTP_natural_rep X
  have hπ' : Function.Surjective (eJ.toMonoidHom.comp π) := eJ.surjective.comp hπ
  have hker' : ¬ 3 ∣ Nat.card (eJ.toMonoidHom.comp π).ker := by
    have h : (eJ.toMonoidHom.comp π).ker = π.ker := by
      ext g
      simp [MonoidHom.mem_ker]
    rwa [h]
  have h20 := ggTPWeight_PSL6 h3Kf (eJ.toMonoidHom.comp π) hπ' hker' ρ hρ
  rw [Module.finrank_fintype_fun_eq_card] at h20
  omega

private theorem ggTP_false_unitary {G : Type} [Group G] [Finite G] {J K' : Subgroup G}
    (hJK : J ≤ K') (hJ : CFSG.Assembly.IsQuasisimple ↥J) (hZJ : ¬ 3 ∣ Nat.card (Subgroup.center ↥J))
    {n : ℕ} (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1)
    (hhJ : GGHasLabel ⟨.twA, 5, n⟩ (↥J ⧸ Subgroup.center ↥J)) {labK : LargeEvenLabel}
    (hrow : (labK.tag = .A ∧ (labK.rank = 6 ∨ labK.rank = 11 ∨ labK.rank = 12)) ∨
      (labK.tag = .twA ∧ labK.rank = 6) ∨ (labK.tag = .C ∧ labK.rank = 6) ∨
      (labK.tag = .D ∧ (labK.rank = 6 ∨ labK.rank = 7)) ∨ (labK.tag = .twD ∧ labK.rank = 7))
    (h3K : labK.tag = .A → labK.rank = 11 → 3 ∣ 2 ^ labK.n + 1)
    (hhK : GGHasLabel labK (↥K' ⧸ Subgroup.center ↥K')) : False := by
  obtain ⟨ι, _, _, K, _, _, H, ⟨eK⟩, hι, hchar, hZ⟩ := ggTPRowData hrow h3K hhK
  obtain ⟨X, π, hXH, hπ, hker⟩ := ggTPLift H hZ hJK eK hJ hZJ
  obtain ⟨Kf, _, _, hKf, ⟨eJ⟩⟩ := hhJ
  haveI : CharP Kf 2 := by
    refine ggTP_charP_two (n := 2 * n) (by omega) ?_
    rw [hKf, ← pow_mul, Nat.mul_comm]
  obtain ⟨ρ, hρ⟩ := ggTP_natural_rep X
  have hπ' : Function.Surjective (eJ.toMonoidHom.comp π) := eJ.surjective.comp hπ
  have hker' : ¬ 3 ∣ Nat.card (eJ.toMonoidHom.comp π).ker := by
    have h : (eJ.toMonoidHom.comp π).ker = π.ker := by
      ext g
      simp [MonoidHom.mem_ker]
    rwa [h]
  have h20 := ggTPWeight_PSU6 hKf h3 (eJ.toMonoidHom.comp π) hπ' hker' ρ hρ
  rw [Module.finrank_fintype_fun_eq_card] at h20
  omega

theorem ggTPClassicalExcl_of_leaves (hRig : GGLabelRigidInput) (hM : GGE6DepModelKnown)
    (hNI : GGE6DepNonIsoPt) (hX : GGE6DepPerpXNotInL) (hLB : GGLBalanceInput)
    (hJL : GGTPJLayerInput) : GGTPClassicalExcl := by
  intro G _ _ p B Bs x L D J hcfg hop hinn hnt y K hnbr hE y' K' hnbr' labJ labK hJΛ hKΛ hcl
    hhJ hhK hrow
  obtain rfl : p = 3 := hE.1
  have hconj : GGE6DepConjSetting 3 Bs x y L :=
    ggE6DepConj_of_known hRig hM hX hNI G 3 B Bs x L D J hcfg hop hinn hnt y K hnbr hE
  obtain ⟨-, -, -, lab₀, hlab₀, hmL, -⟩ := id hE
  obtain ⟨lab, hΛ₀, hhasL, R₀, -, I₀, F₀, θ₀, hlab_eq⟩ := largeEvenMarking_exists_hasLabel hmL
  rw [hlab_eq] at hΛ₀ hhasL
  obtain ⟨hJlab, hZJ, hJp⟩ := ggTPJLabel_of_config hRig hJL hcfg hinn.1 hnbr hE hconj hlab₀ hmL
  have hJK : J ≤ K' := le_of_ggNbr hLB hcfg.1 hcfg.2.2 hJp hnbr'
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := hcfg.2.2.1.2.2.2.2.2.1.2.2
  have hjΛ : LargeEvenInLambda2 (ggTPJLabel lab₀) := by
    rcases hlab₀ with ⟨ht, -⟩ | ⟨ht, -⟩ <;> simp [ggTPJLabel, ht, LargeEvenInLambda2] <;>
      exact hΛ₀.1
  have hlabJ : ggTPJLabel lab₀ = labJ :=
    ggTPLabelIso_jLabel (hRig (ggTPJLabel lab₀) labJ _ hjΛ hJΛ hJlab hhJ)
  subst hlabJ
  rcases lab₀ with ⟨t₀, r₀, n₀⟩
  rcases hlab₀ with ⟨ht, h3⟩ | ⟨ht, h3⟩
  ·
    dsimp only at ht h3
    subst ht
    obtain ⟨hn₀, hr⟩ : 1 ≤ n₀ ∧ r₀ = 0 := by simpa [LargeEvenInLambda2] using hΛ₀
    subst hr
    have hj : ggTPJLabel ⟨.E6, 0, n₀⟩ = ⟨.A, 5, n₀⟩ := by simp [ggTPJLabel]
    rw [hj] at hrow hhJ
    rcases ggTPTablePRow_A5 h3 hrow with h | h | h | h | h | h
    · subst h
      simp [GGTPClassicalLab] at hcl
    · subst h
      exact ggTP_false_linear hJK hJq hZJ hn₀ h3 hhJ (by simp) (by simp) hhK
    · subst h
      exact ggTP_false_linear hJK hJq hZJ hn₀ h3 hhJ (by simp) (by simp) hhK
    · subst h
      exact ggTP_false_linear hJK hJq hZJ hn₀ h3 hhJ (by simp) (by simp) hhK
    · subst h
      exact ggTP_false_linear hJK hJq hZJ hn₀ h3 hhJ (by simp) (by simp) hhK
    · obtain ⟨htag, hrank, -, h3X⟩ := h
      exact ggTP_false_linear hJK hJq hZJ hn₀ h3 hhJ (Or.inl ⟨htag, by omega⟩)
        (fun _ _ => h3X) hhK
  ·
    dsimp only at ht h3
    subst ht
    obtain ⟨hn₀, hr⟩ : 1 ≤ n₀ ∧ r₀ = 0 := by simpa [LargeEvenInLambda2] using hΛ₀
    subst hr
    have hj : ggTPJLabel ⟨.twE6, 0, n₀⟩ = ⟨.twA, 5, n₀⟩ := by simp [ggTPJLabel]
    rw [hj] at hrow hhJ
    rcases ggTPTablePRow_twA5 h3 hrow with h | h | h | h | h | h
    · subst h
      simp [GGTPClassicalLab] at hcl
    · subst h
      exact ggTP_false_unitary hJK hJq hZJ hn₀ h3 hhJ (by simp) (by simp) hhK
    · subst h
      exact ggTP_false_unitary hJK hJq hZJ hn₀ h3 hhJ (by simp) (by simp) hhK
    · subst h
      exact ggTP_false_unitary hJK hJq hZJ hn₀ h3 hhJ (by simp) (by simp) hhK
    · subst h
      exact ggTP_false_unitary hJK hJq hZJ hn₀ h3 hhJ (by simp) (by simp) hhK
    · obtain ⟨htK, -⟩ := h
      simp [GGTPClassicalLab, htK] at hcl

end CFSG.StandardType

end
