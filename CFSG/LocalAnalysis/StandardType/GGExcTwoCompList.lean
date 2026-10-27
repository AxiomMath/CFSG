module

public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGKacTable
public import CFSG.LocalAnalysis.StandardType.GGFixSub
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGCompList (lab : LargeEvenLabel) (p : ℕ) (S : LargeEvenLabel → Prop) : Prop :=
  LargeEvenLabelAll lab fun R _ I _ =>
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      ∀ e : MulAut L', e ^ p = 1 → e ≠ 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
        ∀ J : Subgroup L', IsComponentOf J (ggFixSub e) →
          ∃ labJ : LargeEvenLabel, S labJ ∧ GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)

theorem GGCompList.of_basicB {lab : LargeEvenLabel} {p : ℕ} {S : LargeEvenLabel → Prop}
    (h : GGCompList lab p S) (hΛ : LargeEvenInLambda2 lab)
    (hrig : ∀ lab' : LargeEvenLabel, LargeEvenInLambda2 lab' → GGLabelIso lab lab' → lab' = lab)
    {n : ℕ} {T : ℕ → LargeEvenLabel → Prop} {X : Type} [Group X] [Finite X]
    {A Ab : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hd : GGTPNBasicB p n T A Ab σ J) (hX : GGHasLabel lab (X ⧸ Subgroup.center X)) :
    ∃ labJ : LargeEvenLabel, S labJ ∧ GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) := by
  have hcore : GGTPNLocalCore p A σ J := hd.1
  have hmarked : GGTPNMarked p T A := hd.2.2.2.2.2.2.2
  obtain ⟨hcomm, lab', hlab', hraw⟩ := hmarked
  have hHasLabel_lab' : GGHasLabel lab' (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim (fun θ _ => ⟨θ⟩)) hraw
  have hrigid : GGLabelIso lab lab' :=
    ggLabelRigidInput_holds lab lab' (X ⧸ Subgroup.center X) hΛ hlab' hX hHasLabel_lab'
  have hlab'_eq_lab : lab' = lab := hrig lab' hlab' hrigid
  subst lab'
  have hmain := h _ hraw
  obtain ⟨R, _, I, F, hQR⟩ := largeEvenRawDatum_exists hmain
  obtain ⟨hQ, hP⟩ := hQR
  obtain ⟨hsimple, -, htheta⟩ := hQ
  obtain ⟨θ, hT, hHalf, hInd⟩ := htheta
  let ψ : X →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hψ : Function.Surjective ψ := by
    intro r
    obtain ⟨q, hq⟩ := θ.surjective r
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) q
    refine ⟨x, ?_⟩
    show θ (QuotientGroup.mk' (Subgroup.center X) x) = r
    rw [hx]
    exact hq
  have hker_le : ψ.ker ≤ Subgroup.center X := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : θ (QuotientGroup.mk' (Subgroup.center X) x) = 1 := by
      simpa [ψ] using hx
    have hx'' : QuotientGroup.mk' (Subgroup.center X) x = 1 := θ.injective (by simpa using hx')
    exact (QuotientGroup.eq_one_iff x).mp hx''
  have hσpow : σ ^ p = 1 := hcore.1.2 σ hcore.2.1
  have hσne : σ ≠ 1 := hcore.2.2.1
  have hφ_apply : ∀ l : X, ggInducedAut θ σ (ψ l) = ψ (σ l) := by
    intro l
    change ggInducedAut θ σ (θ (l : X ⧸ Subgroup.center X)) =
      θ ((σ l : X) : X ⧸ Subgroup.center X)
    exact ggInducedAut_apply θ σ l
  have hφ_mem : ggInducedAut θ σ ∈ I := hInd σ hcore.2.1
  have hJ : IsComponentOf J (ggFixSub σ) := by
    have hsub : ggFixSub σ = ggAutFixedSubgroup σ := by
      ext x
      simp [ggFixSub, ggAutFixedSubgroup]
    rw [hsub]
    exact hcore.2.2.2.1
  exact hP X ψ hψ hker_le hcomm σ hσpow hσne
    ⟨ggInducedAut θ σ, hφ_mem, hφ_apply⟩ J hJ

theorem GGTablePKnownRK.union {R₁ R₂ : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop}
    (h₁ : GGTablePKnownRK R₁) (h₂ : GGTablePKnownRK R₂) :
    GGTablePKnownRK fun p n labJ labX => R₁ p n labJ labX ∨ R₂ p n labJ labX :=
  fun p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hJ hX hr hhJ hhX =>
    hr.elim (fun h => h₁ p hp hp2 X A Ab σ J n hd hk labJ labX hJ hX h hhJ hhX)
      (fun h => h₂ p hp hp2 X A Ab σ J n hd hk labJ labX hJ hX h hhJ hhX)

theorem GGTablePKnownRK.mono {R R' : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop}
    (h : GGTablePKnownRK R) (hR : ∀ p n labJ labX, R' p n labJ labX → R p n labJ labX) :
    GGTablePKnownRK R' :=
  fun p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hJ hX hr hhJ hhX =>
    h p hp hp2 X A Ab σ J n hd hk labJ labX hJ hX (hR p n labJ labX hr) hhJ hhX

@[expose] def GGKacRE (lab : LargeEvenLabel) (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1) ∧
    ((lab.tag = .F4 ∧ p = 3) ∨ ((lab.tag = .E6 ∨ lab.tag = .twE6) ∧ (p = 3 ∨ p = 5)) ∨
      ((lab.tag = .E7 ∨ lab.tag = .E8) ∧ (p = 3 ∨ p = 5 ∨ p = 7)))

@[expose] def GGK0Comp (Gen : LargeEvenLabel → ℕ → Prop)
    (Valid : LargeEvenLabel → ℕ → GGKacDatum → Prop) : Prop :=
  ∀ p : ℕ, ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → Gen lab p →
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ e : MulAut L', e ^ p = 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
          ∃ D : GGKacDatum, Valid lab p D ∧
            (∀ J : Subgroup L', IsComponentOf J (ggFixSub e) →
              ∃ o ∈ D.orbits, o.qs = true ∧ lab.n ∣ o.lab.n ∧ LargeEvenInLambda2 o.lab ∧
                GGHasLabel o.lab (↥J ⧸ Subgroup.center ↥J)) ∧
            (∀ o ∈ D.orbits, o.qs = true → ∃ J : Subgroup L',
              IsComponentOf J (ggFixSub e) ∧ GGHasLabel o.lab (↥J ⧸ Subgroup.center ↥J)) ∧
            (∀ J : Subgroup L', IsComponentOf J (ggFixSub e) → p ∣ Nat.card J)

@[expose] def GGK0CompRE : Prop := GGK0Comp GGKacRE GGKacValid

@[expose] def GGE6TwoSevenComp : Prop :=
  GGCompList ⟨.E6, 0, 1⟩ 7 (· ∈ [⟨.A, 2, 1⟩, ⟨.triD4, 0, 1⟩])

@[expose] def GGF4TwoThreeComp : Prop :=
  GGCompList ⟨.F4, 0, 1⟩ 3 (· ∈ [⟨.C, 3, 1⟩])

@[expose] def GGE6TwoThreeComp : Prop :=
  GGCompList ⟨.E6, 0, 1⟩ 3 (· ∈ [⟨.A, 5, 1⟩, ⟨.twD, 4, 1⟩, ⟨.A, 2, 2⟩])

@[expose] def GGTwE6TwoThreeComp : Prop :=
  GGCompList ⟨.twE6, 0, 1⟩ 3
    (· ∈ [⟨.twA, 5, 1⟩, ⟨.D, 4, 1⟩, ⟨.twD, 5, 1⟩, ⟨.triD4, 0, 1⟩, ⟨.twA, 4, 1⟩, ⟨.twA, 2, 3⟩])

@[expose] def GGE7TwoThreeComp : Prop :=
  GGCompList ⟨.E7, 0, 1⟩ 3 (· ∈ [⟨.D, 6, 1⟩, ⟨.twA, 5, 1⟩, ⟨.twA, 6, 1⟩, ⟨.twD, 5, 1⟩, ⟨.twE6, 0, 1⟩])

@[expose] def GGE8TwoThreeComp : Prop :=
  GGCompList ⟨.E8, 0, 1⟩ 3 (· ∈ [⟨.twE6, 0, 1⟩, ⟨.twA, 8, 1⟩, ⟨.E7, 0, 1⟩, ⟨.twD, 7, 1⟩])

@[expose] def GGE6TwoCenterBot : Prop :=
  ∀ (K : Type) [Group K] [Finite K], commutator K = ⊤ →
    GGHasLabel ⟨.E6, 0, 1⟩ (K ⧸ Subgroup.center K) → Subgroup.center K = ⊥

@[expose] def GGE6TwoLocalRankThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    GGHasLabel ⟨.E6, 0, 1⟩ (X ⧸ Subgroup.center X) → 4 ≤ LargeEvenTwoLocalRank 3 X

@[expose] def GGRegimeE6TwoSevenOut : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p _ labJ labX => p = 7 ∧ labX = ⟨.E6, 0, 1⟩ ∧ ¬ GGLabelIso labJ ⟨.A, 2, 1⟩ ∧
    ¬ GGLabelIso labJ ⟨.triD4, 0, 1⟩

@[expose] def GGExcTwoLabel (lab : LargeEvenLabel) : Prop :=
  lab.n = 1 ∧ (lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4 ∨
    lab.tag = .triD4 ∨ lab.tag = .G2der ∨ lab.tag = .twF4der)

@[expose] def GGRegimeAm2ExcTwo : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p n labJ labX => GGRegimeAm2 p n labJ labX ∧ GGExcTwoLabel labX

@[expose] def GGRegimeFieldTwoExcTwo : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p n labJ labX => GGRegimeFieldTwo p n labJ labX ∧ GGExcTwoLabel labX

end CFSG.StandardType

end
