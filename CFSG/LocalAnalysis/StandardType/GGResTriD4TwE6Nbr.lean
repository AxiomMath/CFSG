module

public import CFSG.LocalAnalysis.StandardType.GGResTriD4TwE6Defs
public import CFSG.LocalAnalysis.StandardType.GGResTwE6CompNbr
public import CFSG.LocalAnalysis.StandardType.GGResLeaves

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l6wT_largeEvenLabelAll_mono {lab : LargeEvenLabel} {P P' : LargeEvenRawCont}
    (himp : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), P R I F → P' R I F)
    (h : LargeEvenLabelAll lab P) : LargeEvenLabelAll lab P' := by
  intro Q hQ
  exact largeEvenRawDatum_mono (fun R _ I F hh => ⟨hh.1, himp R I F hh.2⟩) (h Q hQ)

theorem ggTriD4_L_false
    {G : Type} [Group G] [Finite G] (hKG : GGTwE6TriD4RankKnown)
    (hRig : GGLabelRigidInput) (hRB : GGTwE6ThreeBstarRankInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hinn : GGInnerDiagOn Bs L) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) {labJ labX : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hΛX : LargeEvenInLambda2 labX) (hJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hX : GGHasLabel labX (↥L ⧸ Subgroup.center ↥L)) (hrow : ggRowTriD4TwE6 p labJ labX) : False := by
  obtain ⟨hJtag, hp, hdvd, hXeq⟩ := hrow
  have hXtag : labX.tag = .twE6 := by rw [hXeq]
  have hXrank : labX.rank = 0 := by simpa [hXtag] using hΛX.2
  have hlabX : labX = (⟨.twE6, 0, labX.n⟩ : LargeEvenLabel) := by
    obtain ⟨tag, rank, n⟩ := labX
    have h1 : tag = .twE6 := by simpa using hXtag
    have h2 : rank = 0 := by simpa using hXrank
    subst h1
    subst h2
    rfl
  have hXn : labX.n = labJ.n := by rw [hXeq]
  have hJrank : labJ.rank = 0 := by simpa [hJtag] using hΛJ.2
  have hlabJ : labJ = (⟨.triD4, 0, labJ.n⟩ : LargeEvenLabel) := by
    obtain ⟨tag, rank, n⟩ := labJ
    have h1 : tag = .triD4 := by simpa using hJtag
    have h2 : rank = 0 := by simpa using hJrank
    subst h1
    subst h2
    rfl
  have hdvdX : 3 ∣ 2 ^ labX.n + 1 := by rw [hXn]; exact hdvd
  have hΛX' : LargeEvenInLambda2 (⟨.twE6, 0, labX.n⟩ : LargeEvenLabel) := by
    rw [← hlabX]; exact hΛX
  let Q : LargeEvenRawCont := fun R _ I _ =>
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      ∀ e : MulAut L', e ^ 3 = 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
        ∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) →
          GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) →
            3 ∣ 2 ^ labX.n + 1 ∧
              ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A → e ∈ A →
                (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → Nat.card A ≤ 3 ^ 4
  have hKG' : LargeEvenLabelAll (⟨.twE6, 0, labX.n⟩ : LargeEvenLabel) Q := by
    refine l6wT_largeEvenLabelAll_mono ?_ (hKG labX.n hΛX' hdvdX)
    refine fun R _ I F h => ?_
    intro L' _ _ ψ hψ hker hperf e he hφ J hJcomp hJlab
    refine ⟨hdvdX, ?_⟩
    exact h L' ψ hψ hker hperf e he hφ J hJcomp
      (by rw [hXn, ← hlabJ]; exact hJlab)
  exact ggTwE6Comp_L_false (labJ := labJ) (labX := labX)
    hRig hRB hcfg hinn hp hnb hΛX hJ hX hXtag hKG'

theorem ggTriD4_K_false
    {G : Type} [Group G] [Finite G] (hKG : GGTwE6TriD4RankKnown) (hRig : GGLabelRigidInput)
    (hI3 : GGNbrSubcomponentInput) (hRk : GGTwE6ThreeNbrRankInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hinn : GGInnerDiagAll p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) {labJ labX : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hΛX : LargeEvenInLambda2 labX) (hJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hX : GGHasLabel labX (↥K ⧸ Subgroup.center ↥K)) (hrow : ggRowTriD4TwE6 p labJ labX) : False := by
  obtain ⟨hJtag, hp, hdvd, hXeq⟩ := hrow
  have hXtag : labX.tag = .twE6 := by rw [hXeq]
  have hXrank : labX.rank = 0 := by simpa [hXtag] using hΛX.2
  have hlabX : labX = (⟨.twE6, 0, labX.n⟩ : LargeEvenLabel) := by
    obtain ⟨tag, rank, n⟩ := labX
    have h1 : tag = .twE6 := by simpa using hXtag
    have h2 : rank = 0 := by simpa using hXrank
    subst h1
    subst h2
    rfl
  have hXn : labX.n = labJ.n := by rw [hXeq]
  have hJrank : labJ.rank = 0 := by simpa [hJtag] using hΛJ.2
  have hlabJ : labJ = (⟨.triD4, 0, labJ.n⟩ : LargeEvenLabel) := by
    obtain ⟨tag, rank, n⟩ := labJ
    have h1 : tag = .triD4 := by simpa using hJtag
    have h2 : rank = 0 := by simpa using hJrank
    subst h1
    subst h2
    rfl
  have hdvdX : 3 ∣ 2 ^ labX.n + 1 := by rw [hXn]; exact hdvd
  have hΛX' : LargeEvenInLambda2 (⟨.twE6, 0, labX.n⟩ : LargeEvenLabel) := by
    rw [← hlabX]; exact hΛX
  let Q : LargeEvenRawCont := fun R _ I _ =>
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      ∀ e : MulAut L', e ^ 3 = 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
        ∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) →
          GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) →
            3 ∣ 2 ^ labX.n + 1 ∧
              ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A → e ∈ A →
                (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → Nat.card A ≤ 3 ^ 4
  have hKG' : LargeEvenLabelAll (⟨.twE6, 0, labX.n⟩ : LargeEvenLabel) Q := by
    refine l6wT_largeEvenLabelAll_mono ?_ (hKG labX.n hΛX' hdvdX)
    refine fun R _ I F h => ?_
    intro L' _ _ ψ hψ hker hperf e he hφ J hJcomp hJlab
    refine ⟨hdvdX, ?_⟩
    exact h L' ψ hψ hker hperf e he hφ J hJcomp
      (by rw [hXn, ← hlabJ]; exact hJlab)
  exact ggTwE6Comp_K_false (labJ := labJ) (labX := labX)
    hRig hI3 hRk hcfg hinn hp hnb hΛX hJ hX hXtag hKG'

end CFSG.StandardType

end
