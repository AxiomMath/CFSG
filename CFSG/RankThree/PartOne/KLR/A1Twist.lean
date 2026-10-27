module

public import CFSG.RankThree.PartOne.KLR.A1Pair
public import CFSG.RankThree.PartOne.KLR.SL2Gen
public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersRankOne
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KLR.CoreGroup
public import CFSG.RankThree.PartOne.KLR.TwistClosure
public import CFSG.RankThree.PartOne.KLR.TwistPerm

public section

namespace CFSG.RankThree.PartOne.KLR

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley

section Basic


theorem dualRoot_neg {γ : Fin ReeTag.F4.tag.rank → ℤ} (hγ : IsRoot ReeTag.F4.tag γ) :
    ReeTag.F4.dualRoot (-γ) = -ReeTag.F4.dualRoot γ := by
  funext j
  have hdvd : ReeTag.F4.quadForm γ ∣ 2 * ReeTag.F4.dualMapInt γ j :=
    Int.dvd_of_emod_eq_zero ((ReeTag.rootDualityCheck_spec hγ).2.1 j)
  have h1 : ReeTag.F4.dualMapInt (-γ) j = -ReeTag.F4.dualMapInt γ j := by
    simp [ReeTag.dualMapInt]
  simp only [ReeTag.dualRoot, Pi.neg_apply, h1, ReeTag.quadForm_neg]
  rw [mul_neg, Int.neg_ediv_of_dvd hdvd]

theorem quadForm_dualRoot_of_long {γ : Fin ReeTag.F4.tag.rank → ℤ}
    (hγ : IsRoot ReeTag.F4.tag γ) (h4 : ReeTag.F4.quadForm γ = 4) :
    ReeTag.F4.quadForm (ReeTag.F4.dualRoot γ) = 2 := by
  have hl : ReeTag.F4.lengthParam γ ≠ 1 := fun h => by
    have := ReeTag.lengthParam_eq_one_iff.1 h
    omega
  exact ReeTag.lengthParam_eq_one_iff.1 ((ReeTag.lengthParam_dualRoot_eq_one_iff hγ).2 hl)

theorem quadForm_dualRoot_of_short {γ : Fin ReeTag.F4.tag.rank → ℤ}
    (hγ : IsRoot ReeTag.F4.tag γ) (h2 : ReeTag.F4.quadForm γ = 2) :
    ReeTag.F4.quadForm (ReeTag.F4.dualRoot γ) = 4 := by
  have hl : ReeTag.F4.lengthParam γ = 1 := ReeTag.lengthParam_eq_one_iff.2 h2
  have hnot : ¬ ReeTag.F4.lengthParam (ReeTag.F4.dualRoot γ) = 1 := fun h =>
    (ReeTag.lengthParam_dualRoot_eq_one_iff hγ).1 h hl
  rcases ReeTag.quadForm_eq (ReeTag.isRoot_dualRoot hγ) with hq | hq
  · exact absurd (ReeTag.lengthParam_eq_one_iff.2 hq) hnot
  · simpa [ReeTag.prime] using hq

theorem smul_sign_cases {γ : Fin ReeTag.F4.tag.rank → ℤ} {s : ℤ} (hs : s = 1 ∨ s = -1) :
    s • γ = γ ∨ s • γ = -γ := by
  rcases hs with rfl | rfl
  · exact Or.inl (one_smul ℤ γ)
  · exact Or.inr (neg_one_smul ℤ γ)

theorem quadForm_smul_sign {γ : Fin ReeTag.F4.tag.rank → ℤ} {s : ℤ} (hs : s = 1 ∨ s = -1) :
    ReeTag.F4.quadForm (s • γ) = ReeTag.F4.quadForm γ := by
  rcases smul_sign_cases (γ := γ) hs with h | h <;> rw [h]
  rw [ReeTag.quadForm_neg]

theorem isRoot_smul_sign {γ : Fin ReeTag.F4.tag.rank → ℤ} (hγ : IsRoot ReeTag.F4.tag γ) {s : ℤ}
    (hs : s = 1 ∨ s = -1) : IsRoot ReeTag.F4.tag (s • γ) := by
  rcases smul_sign_cases (γ := γ) hs with h | h <;> rw [h]
  · exact hγ
  · exact IsRoot.neg hγ

theorem dualRoot_smul_sign {γ : Fin ReeTag.F4.tag.rank → ℤ} (hγ : IsRoot ReeTag.F4.tag γ)
    {s : ℤ} (hs : s = 1 ∨ s = -1) :
    ReeTag.F4.dualRoot (s • γ) = s • ReeTag.F4.dualRoot γ := by
  rcases hs with rfl | rfl
  · rw [one_smul, one_smul]
  · rw [neg_one_smul, neg_one_smul, dualRoot_neg hγ]

theorem tau_smul_sign (w : WeylGroup ReeTag.F4.tag) {γ : Fin ReeTag.F4.tag.rank → ℤ}
    (hγ : IsRoot ReeTag.F4.tag γ) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    w • ReeTag.F4.dualRoot (s • γ) = s • (w • ReeTag.F4.dualRoot γ) := by
  rw [dualRoot_smul_sign hγ hs, smul_comm]

end Basic

section Tau

variable {i j : Fin ReeTag.F4.tag.rank}

theorem A1Pair.tau_long (h : A1Pair i j) {w' : WeylGroup ReeTag.F4.tag}
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) :
      Set (Fin ReeTag.F4.tag.rank)),
        w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag
          (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank)))
    {γ : Fin ReeTag.F4.tag.rank → ℤ} (hγ : γ = Pi.single i 1 ∨ γ = -Pi.single i 1) :
    w' • ReeTag.F4.dualRoot γ = Pi.single j 1 ∨ w' • ReeTag.F4.dualRoot γ = -Pi.single j 1 := by
  have hroot : IsRoot ReeTag.F4.tag γ := by
    rcases hγ with rfl | rfl
    · exact isRoot_single _ i
    · exact IsRoot.neg (isRoot_single _ i)
  have h4 : ReeTag.F4.quadForm γ = 4 := by
    rcases hγ with rfl | rfl
    · exact h.long
    · rw [ReeTag.quadForm_neg]
      exact h.long
  have hmem : γ ∈ parabolicRoots ReeTag.F4.tag (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) :
      Set (Fin ReeTag.F4.tag.rank)) := by
    rw [h.parabolicRoots_eq]
    rcases hγ with rfl | rfl <;> simp
  have hst := hstab γ hmem
  rw [h.parabolicRoots_eq] at hst
  have hq : ReeTag.F4.quadForm (w' • ReeTag.F4.dualRoot γ) = 2 := by
    rw [quadForm_smul]
    exact quadForm_dualRoot_of_long hroot h4
  rcases hst with h1 | h1 | h1 | h1
  · rw [h1, h.long] at hq
    omega
  · rw [h1, ReeTag.quadForm_neg, h.long] at hq
    omega
  · exact Or.inl h1
  · exact Or.inr h1

theorem A1Pair.tau_short (h : A1Pair i j) {w' : WeylGroup ReeTag.F4.tag}
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) :
      Set (Fin ReeTag.F4.tag.rank)),
        w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag
          (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank)))
    {γ : Fin ReeTag.F4.tag.rank → ℤ} (hγ : γ = Pi.single j 1 ∨ γ = -Pi.single j 1) :
    w' • ReeTag.F4.dualRoot γ = Pi.single i 1 ∨ w' • ReeTag.F4.dualRoot γ = -Pi.single i 1 := by
  have hroot : IsRoot ReeTag.F4.tag γ := by
    rcases hγ with rfl | rfl
    · exact isRoot_single _ j
    · exact IsRoot.neg (isRoot_single _ j)
  have h2 : ReeTag.F4.quadForm γ = 2 := by
    rcases hγ with rfl | rfl
    · exact h.short
    · rw [ReeTag.quadForm_neg]
      exact h.short
  have hmem : γ ∈ parabolicRoots ReeTag.F4.tag (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) :
      Set (Fin ReeTag.F4.tag.rank)) := by
    rw [h.parabolicRoots_eq]
    rcases hγ with rfl | rfl <;> simp
  have hst := hstab γ hmem
  rw [h.parabolicRoots_eq] at hst
  have hq : ReeTag.F4.quadForm (w' • ReeTag.F4.dualRoot γ) = 4 := by
    rw [quadForm_smul]
    exact quadForm_dualRoot_of_short hroot h2
  rcases hst with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · rw [h1, h.short] at hq
    omega
  · rw [h1, ReeTag.quadForm_neg, h.short] at hq
    omega

theorem A1Pair.sign_data (h : A1Pair i j) {w' : WeylGroup ReeTag.F4.tag}
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) :
      Set (Fin ReeTag.F4.tag.rank)),
        w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag
          (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) :
    ∃ s₁ s₂ : ℤ, (s₁ = 1 ∨ s₁ = -1) ∧ (s₂ = 1 ∨ s₂ = -1) ∧
      w' • ReeTag.F4.dualRoot (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) =
        s₁ • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) ∧
      w' • ReeTag.F4.dualRoot (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) =
        s₂ • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) := by
  obtain ⟨s₁, hs₁, e₁⟩ : ∃ s₁ : ℤ, (s₁ = 1 ∨ s₁ = -1) ∧
      w' • ReeTag.F4.dualRoot (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) =
        s₁ • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) := by
    rcases h.tau_long hstab (Or.inl rfl) with h1 | h1
    · exact ⟨1, Or.inl rfl, by rw [h1, one_smul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h1, neg_one_smul]⟩
  obtain ⟨s₂, hs₂, e₂⟩ : ∃ s₂ : ℤ, (s₂ = 1 ∨ s₂ = -1) ∧
      w' • ReeTag.F4.dualRoot (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) =
        s₂ • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) := by
    rcases h.tau_short hstab (Or.inl rfl) with h1 | h1
    · exact ⟨1, Or.inl rfl, by rw [h1, one_smul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h1, neg_one_smul]⟩
  exact ⟨s₁, s₂, hs₁, hs₂, e₁, e₂⟩

end Tau

section Dyn

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L 2] (D : ReeFrameData K L a)
  {i j : Fin ReeTag.F4.tag.rank}

omit [CharP L 2] in
theorem twistMap_twistMap {n' x : ModGL ReeTag.F4.tag L}
    (hn' : n' ∈ adjointGroup ReeTag.F4.tag L) (hx : x ∈ adjointGroup ReeTag.F4.tag L) :
    twistMap D.F n' (twistMap D.F n' x) =
      (n' * Fext D.F n') * Units.map (entrywiseHom D.Frq) x * (n' * Fext D.F n')⁻¹ := by
  have hmem := Fext_mem D.F hx
  have e : (⟨Fext D.F x, hmem⟩ : adjointGroup ReeTag.F4.tag L) = D.F ⟨x, hx⟩ :=
    Subtype.ext (Fext_of_mem D.F hx)
  have h1 : Fext D.F (Fext D.F x) = Units.map (entrywiseHom D.Frq) x := by
    rw [Fext_of_mem D.F hmem, e]
    exact D.sq ⟨x, hx⟩
  unfold twistMap
  rw [Fext_conj D.F hn' hmem, h1]
  group

theorem rootSL2_uSL_charTwo (β : Fin ReeTag.F4.tag.rank → ℤ) (z : L) :
    rootSL2 ReeTag.F4.tag L β (uSL z) = pinnedX ReeTag.F4.tag L β z := by
  rw [rootSL2_uSL_eq]
  rcases pinnedSign_eq ReeTag.F4.tag β with h | h <;> rw [h]
  · rw [one_smul]
  · rw [neg_smul, one_smul, CharTwo.neg_eq]

theorem rootSL2_vSL_charTwo {β : Fin ReeTag.F4.tag.rank → ℤ} (hβ : IsRoot ReeTag.F4.tag β)
    (z : L) : rootSL2 ReeTag.F4.tag L β (vSL z) = pinnedX ReeTag.F4.tag L (-β) z := by
  obtain ⟨ε, hε, h⟩ := exists_rootSL2_vSL_eq (K := L) hβ
  rw [h z, eq_one_of_mul_self_eq_one_charTwo hε, one_mul]

theorem A1Pair.fp2_pinnedX (h : A1Pair i j) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {n' : ModGL ReeTag.F4.tag L} {w' : WeylGroup ReeTag.F4.tag} (hperm : PermAct n' w')
    {s₁ s₂ : ℤ} (hs₁ : s₁ = 1 ∨ s₁ = -1)
    (e₁ : w' • ReeTag.F4.dualRoot (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) =
      s₁ • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ))
    (e₂ : w' • ReeTag.F4.dualRoot (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) =
      s₂ • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ))
    {s : ℤ} (hs : s = 1 ∨ s = -1) (c : L) :
    twistMap D.F n' (twistMap D.F n'
        (pinnedX ReeTag.F4.tag L (s • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ)) c)) =
      pinnedX ReeTag.F4.tag L ((s * s₁ * s₂) • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ))
        (D.Frq c) := by
  have hα : IsRoot ReeTag.F4.tag (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) :=
    isRoot_single _ i
  have hβ : IsRoot ReeTag.F4.tag (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) :=
    isRoot_single _ j
  have hγ := isRoot_smul_sign hα hs
  have hs₁s : s * s₁ = 1 ∨ s * s₁ = -1 := by
    rcases hs with rfl | rfl <;> rcases hs₁ with rfl | rfl <;> simp
  have hγ' := isRoot_smul_sign hβ hs₁s
  have hq4 : ReeTag.F4.quadForm (s • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ)) = 4 := by
    rw [quadForm_smul_sign hs]
    exact h.long
  have hq2 : ReeTag.F4.quadForm ((s * s₁) • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ)) = 2 := by
    rw [quadForm_smul_sign hs₁s]
    exact h.short
  have step1 : twistMap D.F n'
      (pinnedX ReeTag.F4.tag L (s • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ)) c) =
      pinnedX ReeTag.F4.tag L ((s * s₁) • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ))
        (c ^ 2 ^ a) := by
    unfold twistMap
    rw [D.isFrob.twist_pinnedX hperm hγ c, tau_smul_sign w' hα hs, e₁, smul_smul]
    have : rootExp a (s • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ)) = 2 ^ a := by
      unfold rootExp
      rw [hq4]
      norm_num
    rw [this]
  have step2 : ∀ d : L, twistMap D.F n'
      (pinnedX ReeTag.F4.tag L ((s * s₁) • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ)) d) =
      pinnedX ReeTag.F4.tag L ((s * s₁ * s₂) • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ))
        (d ^ 2 ^ (a + 1)) := by
    intro d
    unfold twistMap
    rw [D.isFrob.twist_pinnedX hperm hγ' d, tau_smul_sign w' hβ hs₁s, e₂, smul_smul]
    have : rootExp a ((s * s₁) • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ)) = 2 ^ (a + 1) := by
      unfold rootExp
      rw [hq2]
      simp
    rw [this]
  rw [step1, step2, ← pow_mul, D.Frq_pow, hK]
  have hexp : 2 ^ a * 2 ^ (a + 1) = 2 ^ (2 * a + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hexp]

open CFSG.RankThree.Classical (conjSL conjSL_one conjSL_mul)


theorem A1Pair.exists_twist [IsAlgClosed L] (h : A1Pair i j) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {n' : ModGL ReeTag.F4.tag L} (hn' : n' ∈ adjointGroup ReeTag.F4.tag L)
    {w' : WeylGroup ReeTag.F4.tag} (hperm : PermAct n' w')
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) :
      Set (Fin ReeTag.F4.tag.rank)),
        w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag
          (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) :
    ∃ P₀ : GL (Fin 2) L, ∀ B : SL2 L,
      (n' * Fext D.F n') * Units.map (entrywiseHom D.Frq)
          (rootSL2 ReeTag.F4.tag L (Pi.single i 1) B) * (n' * Fext D.F n')⁻¹ =
        rootSL2 ReeTag.F4.tag L (Pi.single i 1)
          (conjSL (P₀ * Matrix.GeneralLinearGroup.map D.Frq P₀⁻¹)
            (Matrix.SpecialLinearGroup.map D.Frq B)) := by
  obtain ⟨s₁, s₂, hs₁, hs₂, e₁, e₂⟩ := h.sign_data hstab
  have hε : s₁ * s₂ = 1 ∨ s₁ * s₂ = -1 := by
    rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl <;> simp
  have hα : IsRoot ReeTag.F4.tag (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) :=
    isRoot_single _ i
  let G₂ : SL2 L →* ModGL ReeTag.F4.tag L :=
    (MulAut.conj (n' * Fext D.F n')).toMonoidHom.comp
      ((Units.map (entrywiseHom D.Frq)).comp (rootSL2 ReeTag.F4.tag L (Pi.single i 1)))
  have hG₂ : ∀ B, G₂ B = (n' * Fext D.F n') * Units.map (entrywiseHom D.Frq)
      (rootSL2 ReeTag.F4.tag L (Pi.single i 1) B) * (n' * Fext D.F n')⁻¹ := fun B => rfl
  have hG₂u : ∀ c : L, G₂ (uSL c) =
      pinnedX ReeTag.F4.tag L ((s₁ * s₂) • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ))
        (D.Frq c) := by
    intro c
    have hadj : pinnedX ReeTag.F4.tag L (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) c ∈
        adjointGroup ReeTag.F4.tag L := pinnedX_mem_adjointGroup _ _
    rw [hG₂, rootSL2_uSL_charTwo, ← twistMap_twistMap D hn' hadj]
    have := A1Pair.fp2_pinnedX D h hK hperm hs₁ e₁ e₂ (s := 1) (Or.inl rfl) c
    rw [one_smul] at this
    rw [this, one_mul]
  have hG₂v : ∀ c : L, G₂ (vSL c) =
      pinnedX ReeTag.F4.tag L (-((s₁ * s₂) • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ)))
        (D.Frq c) := by
    intro c
    have hadj : pinnedX ReeTag.F4.tag L (-(Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ)) c ∈
        adjointGroup ReeTag.F4.tag L := pinnedX_mem_adjointGroup _ _
    rw [hG₂, rootSL2_vSL_charTwo hα, ← twistMap_twistMap D hn' hadj]
    have := A1Pair.fp2_pinnedX D h hK hperm hs₁ e₁ e₂ (s := -1) (Or.inr rfl) c
    rw [neg_one_smul] at this
    have e : (-1 * s₁ * s₂ : ℤ) = -(s₁ * s₂) := by ring
    rw [e, neg_smul] at this
    exact this
  rcases hε with hε | hε
  · refine ⟨1, fun B => ?_⟩
    have hEq : G₂ = (rootSL2 ReeTag.F4.tag L (Pi.single i 1)).comp
        (Matrix.SpecialLinearGroup.map D.Frq) := by
      refine hom_eq_of_uSL_vSL _ _ (fun c => ?_) (fun c => ?_)
      · rw [hG₂u, hε, one_smul]
        show _ = rootSL2 ReeTag.F4.tag L (Pi.single i 1)
          (Matrix.SpecialLinearGroup.map D.Frq (uSL c))
        rw [map_uSL, rootSL2_uSL_charTwo]
      · rw [hG₂v, hε, one_smul]
        show _ = rootSL2 ReeTag.F4.tag L (Pi.single i 1)
          (Matrix.SpecialLinearGroup.map D.Frq (vSL c))
        rw [map_vSL, rootSL2_vSL_charTwo hα]
    rw [← hG₂, hEq]
    simp [conjSL_one]
  · obtain ⟨P₀, hP₀⟩ := exists_WSL_twist (K := K) (L := L) D.Frq D.Frq_pow
    refine ⟨P₀, fun B => ?_⟩
    rw [hP₀]
    have hEq : G₂ = (rootSL2 ReeTag.F4.tag L (Pi.single i 1)).comp
        ((conjSL (Matrix.SpecialLinearGroup.toGL (WSL : SL2 L))).comp
          (Matrix.SpecialLinearGroup.map D.Frq)) := by
      refine hom_eq_of_uSL_vSL _ _ (fun c => ?_) (fun c => ?_)
      · rw [hG₂u, hε, neg_one_smul]
        show _ = rootSL2 ReeTag.F4.tag L (Pi.single i 1)
          (conjSL (Matrix.SpecialLinearGroup.toGL (WSL : SL2 L))
            (Matrix.SpecialLinearGroup.map D.Frq (uSL c)))
        rw [map_uSL, conjSL_toGL, WSL_mul_uSL_mul_inv', rootSL2_vSL_charTwo hα,
          CharTwo.neg_eq (D.Frq c)]
      · rw [hG₂v, hε, neg_one_smul, neg_neg]
        show _ = rootSL2 ReeTag.F4.tag L (Pi.single i 1)
          (conjSL (Matrix.SpecialLinearGroup.toGL (WSL : SL2 L))
            (Matrix.SpecialLinearGroup.map D.Frq (vSL c)))
        rw [map_vSL, conjSL_toGL, WSL_mul_vSL_mul_inv', rootSL2_uSL_charTwo,
          CharTwo.neg_eq (D.Frq c)]
    rw [← hG₂, hEq]
    rfl

theorem twistMap_mem_rankOne {n' : ModGL ReeTag.F4.tag L} {w' : WeylGroup ReeTag.F4.tag}
    (hperm : PermAct n' w') {α β : Fin ReeTag.F4.tag.rank → ℤ} (hα : IsRoot ReeTag.F4.tag α)
    (hβ : IsRoot ReeTag.F4.tag β)
    (hroots : ∀ γ, (γ = α ∨ γ = -α) →
      (w' • ReeTag.F4.dualRoot γ = β ∨ w' • ReeTag.F4.dualRoot γ = -β)) :
    ∀ g ∈ rootRankOneGroup ReeTag.F4.tag L α, twistMap D.F n' g ∈
      rootRankOneGroup ReeTag.F4.tag L β := by
  intro g hg
  rw [rankOne_eq_sup hα, Subgroup.sup_eq_closure] at hg
  rw [rankOne_eq_sup hβ]
  refine (twistMap_mem_of_closure
    (s := (rootSubgroup ReeTag.F4.tag L α : Set (ModGL ReeTag.F4.tag L)) ∪
      (rootSubgroup ReeTag.F4.tag L (-α) : Set (ModGL ReeTag.F4.tag L))) ?_ ?_ hg).1
  · rintro x (hx | hx)
    · exact rootSubgroup_le_adjointGroup α hx
    · exact rootSubgroup_le_adjointGroup (-α) hx
  · have key : ∀ γ, IsRoot ReeTag.F4.tag γ → (γ = α ∨ γ = -α) →
        ∀ g ∈ rootSubgroup ReeTag.F4.tag L γ,
          twistMap D.F n' g ∈ rootSubgroup ReeTag.F4.tag L β ⊔
            rootSubgroup ReeTag.F4.tag L (-β) := by
      intro γ hγ hγ' g hg'
      refine twistMap_mem_rootSubgroup γ (fun c => ?_) hg'
      unfold twistMap
      rw [D.isFrob.twist_pinnedX hperm hγ c]
      rcases hroots γ hγ' with h1 | h1 <;> rw [h1]
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, rfl⟩)
      · exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, rfl⟩)
    rintro g (hg' | hg')
    · exact key α hα (Or.inl rfl) g hg'
    · exact key (-α) (IsRoot.neg hα) (Or.inr rfl) g hg'

theorem noSolvableRadical_A1Pair [IsAlgClosed L] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (h : A1Pair i j) {n' : ModGL ReeTag.F4.tag L}
    (hn' : n' ∈ adjointGroup ReeTag.F4.tag L) {w' : WeylGroup ReeTag.F4.tag}
    (hperm : PermAct n' w')
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) :
      Set (Fin ReeTag.F4.tag.rank)),
        w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag
          (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) :
    NoSolvableRadical (rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
      (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) ⊓
        twistedFixed D.F n') := by
  classical
  have hα : IsRoot ReeTag.F4.tag (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) :=
    isRoot_single _ i
  have hβ : IsRoot ReeTag.F4.tag (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) :=
    isRoot_single _ j
  have hAB := h.commute_rankOne (L := L)
  have hdisj := h.disjoint (L := L)
  have hspan := h.rootSpan_eq (L := L)
  set A := rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1) with hA
  set B := rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1) with hB
  have hABle : A ⊔ B ≤ adjointGroup ReeTag.F4.tag L := by
    rw [← hspan]
    exact CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L _
  have hmul : ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B,
      twistMap D.F n' (x * y) = twistMap D.F n' x * twistMap D.F n' y :=
    fun x hx y hy => twistMap_mul n' (hABle hx) (hABle hy)
  have hφA := twistMap_mem_rankOne D hperm hα hβ (fun γ hγ => h.tau_long hstab hγ)
  have hφB := twistMap_mem_rankOne D hperm hβ hα (fun γ hγ => h.tau_short hstab hγ)
  obtain ⟨P₀, hX⟩ := h.exists_twist D hK hn' hperm hstab
  let R : Subgroup (SL2 L) :=
    (Matrix.SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P₀)
  let X : Subgroup (ModGL ReeTag.F4.tag L) :=
    R.map (rootSL2 ReeTag.F4.tag L (Pi.single i 1))
  have hρinj := rootSL2_injective_of_field (K := L) (τ := ReeTag.F4.tag) (Pi.single i 1)
  have hρadj : ∀ B₀ : SL2 L,
      rootSL2 ReeTag.F4.tag L (Pi.single i 1) B₀ ∈ adjointGroup ReeTag.F4.tag L := fun B₀ =>
    (hABle (Subgroup.mem_sup_left ⟨B₀, rfl⟩))
  have hXmem : ∀ x, x ∈ X ↔ x ∈ A ∧ twistMap D.F n' (twistMap D.F n' x) = x := by
    intro x
    constructor
    · rintro ⟨B₀, hB₀, rfl⟩
      refine ⟨⟨B₀, rfl⟩, ?_⟩
      rw [twistMap_twistMap D hn' (hρadj B₀)]
      exact (a1_hS1_of_action D.Frq D.Frq_pow P₀ hX B₀).2 hB₀
    · rintro ⟨⟨B₀, rfl⟩, hfix⟩
      refine ⟨B₀, ?_, rfl⟩
      rw [twistMap_twistMap D hn' (hρadj B₀)] at hfix
      exact (a1_hS1_of_action D.Frq D.Frq_pow P₀ hX B₀).1 hfix
  have hPmem : ∀ g, g ∈ rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
      (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) ⊓
        twistedFixed D.F n' ↔ g ∈ A ⊔ B ∧ twistMap D.F n' g = g := by
    intro g
    rw [hspan]
    constructor
    · rintro ⟨hg, -, hfix⟩
      exact ⟨hg, hfix⟩
    · rintro ⟨hg, hfix⟩
      exact ⟨hg, hABle hg, hfix⟩
  obtain ⟨Θ, hΘinj, hΘr⟩ := fixed_swap hAB hdisj (twistMap D.F n') hmul hφA hφB X hXmem _ hPmem
  have hsimple : IsSimpleGroup (SL2 K) :=
    CFSG.LieType.Ree.LargeReeInvolution.isSimpleGroup_SL2 ha hK
  have hns : ¬ Group.IsSolvable (SL2 K) := by
    obtain ⟨x, y, hxy⟩ := CFSG.LieType.Ree.LargeReeInvolution.exists_SL2_mul_ne_mul (K := K)
    intro hs
    exact hxy ((IsSimpleGroup.comm_iff_isSolvable.2 hs) x y)
  have hSLinj :
      Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap K L)) := by
    intro A₀ B₀ hAB₀
    ext i₀ j₀
    have h1 := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) L =>
      (X : Matrix (Fin 2) (Fin 2) L) i₀ j₀) hAB₀
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] at h1
    exact (algebraMap K L).injective h1
  have hconjinj : Function.Injective (conjSL P₀) := fun A₀ B₀ hAB₀ => by
    have h1 := congrArg (conjSL P₀⁻¹) hAB₀
    rwa [← conjSL_mul, ← conjSL_mul, inv_mul_cancel, conjSL_one, conjSL_one] at h1
  let e1 : SL2 K ≃* R := (MonoidHom.ofInjective hSLinj).trans
    (Subgroup.equivMapOfInjective _ (conjSL P₀) hconjinj)
  let e2 : R ≃* X := Subgroup.equivMapOfInjective R (rootSL2 ReeTag.F4.tag L (Pi.single i 1)) hρinj
  let e3 : X ≃* Θ.range := MonoidHom.ofInjective hΘinj
  let e4 := MulEquiv.subgroupCongr hΘr
  exact noSolvableRadical_of_mulEquiv hns (e1.trans (e2.trans (e3.trans e4))).symm

end Dyn

end CFSG.RankThree.PartOne.KLR
