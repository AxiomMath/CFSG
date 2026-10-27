module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.LocalAnalysis.StandardType.GGCentD4Alpha
public import CFSG.LocalAnalysis.StandardType.GGCentD4Fix

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Lang.D4Three
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley

theorem ntpD4_rident
    
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup .E6 L p₀)
    (a : Fin Tag.E6.rank → Lˣ) (i : KernelComponent (rootCharHom a))
    (hi : ∀ j : KernelComponent (rootCharHom a), j = i)
    (hρker : ∀ γ ∈ rootCharKernel a, S.ρ γ ∈ rootCharKernel a)
    (Y : Subgroup (ModGL .E6 L)) (hY : Y = rootSpan Tag.E6 L (rootCharKernel a))
    (hstepY : ∀ y ∈ Y, S.D.step y ∈ Y)
    (Ξ : ↥Y ≃* ↥(adjointGroup Tag.D4 L)) (Fr : L →+* L) (r : ℕ)
    (hΞ : ∀ (y : ModGL .E6 L) (hy : y ∈ Y) (hy' : S.D.step y ∈ Y),
      (Ξ ⟨S.D.step y, hy'⟩ : ModGL Tag.D4 L) = d4P L ^ r * Units.map (entrywiseHom Fr)
        (Ξ ⟨y, hy⟩ : ModGL Tag.D4 L) * (d4P L ^ r)⁻¹)
    (G₀ : Subgroup (ModGL Tag.D4 L)) (hG₀ : ∀ x : ModGL Tag.D4 L, x ∈ G₀ ↔
      x ∈ adjointGroup Tag.D4 L ∧ d4P L ^ r * Units.map (entrywiseHom Fr) x * (d4P L ^ r)⁻¹ = x)
    (hperf : Group.IsPerfect ↥G₀) :
    rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ Y ∧
      ∀ (y : ModGL .E6 L) (hy : y ∈ Y),
        y ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i ↔ (Ξ ⟨y, hy⟩ : ModGL Tag.D4 L) ∈ G₀ := by
  set Yst : Subgroup (ModGL .E6 L) := Y ⊓ S.D.step.eqLocus (MonoidHom.id _) with hYst
  have mem_Yst : ∀ y : ModGL .E6 L, y ∈ Yst ↔ y ∈ Y ∧ S.D.step y = y := by
    intro y
    rw [hYst, Subgroup.mem_inf]
    exact and_congr Iff.rfl Iff.rfl
  have hcomp : componentRoots (rootCharHom a) i = rootCharKernel a := by
    ext α
    constructor
    · rintro ⟨hα, -⟩
      exact hα
    · intro hα
      exact ⟨hα, hi ⟦⟨α, hα⟩⟧⟩
  have hrat_le : rationalRoots S.ρ (rootCharHom a) i ⊆ rootCharKernel a := by
    rintro γ ⟨k, δ, hδ, rfl⟩
    induction k with
    | zero => simpa [Function.iterate_zero_apply] using (hcomp ▸ hδ)
    | succ k ih => simpa [Function.iterate_succ_apply'] using hρker _ ih
  have hker_le : rootCharKernel a ⊆ rationalRoots S.ρ (rootCharHom a) i := by
    intro γ hγ
    exact ⟨0, γ, hcomp.symm ▸ hγ, by rw [Function.iterate_zero_apply]⟩
  have hrat : rationalRoots S.ρ (rootCharHom a) i = rootCharKernel a :=
    Set.Subset.antisymm hrat_le hker_le
  have hspan : rationalSpan S.ρ S.Γ (rootCharHom a) i = Y ⊓ S.Γ := by
    rw [rationalSpan, hrat, ← hY]
  have hR : rationalComponent S.ρ S.Γ (rootCharHom a) i = ⁅Y ⊓ S.Γ, Y ⊓ S.Γ⁆ := by
    rw [rationalComponent, hspan]
  have hYle : Y ≤ adjointGroup Tag.E6 L := by
    rw [hY]
    exact rootSpan_le_adjointGroup L (rootCharKernel a)
  have hYM : Y ⊓ S.D.model = Yst := by
    rw [hYst]
    show Y ⊓ (adjointGroup Tag.E6 L ⊓ S.D.step.eqLocus (MonoidHom.id _)) =
      Y ⊓ S.D.step.eqLocus (MonoidHom.id _)
    rw [← inf_assoc, inf_eq_left.mpr hYle]
  have hYst_le_M : Yst ≤ S.D.model := by
    rw [← hYM]
    exact inf_le_right
  have hYst_le_Y : Yst ≤ Y := by
    rw [hYst]
    exact inf_le_left
  have hperfYst : Group.IsPerfect ↥Yst := by
    let inc : ↥Yst →* ↥Y := Subgroup.inclusion hYst_le_Y
    let g : ↥Yst →* ↥(adjointGroup Tag.D4 L) := Ξ.toMonoidHom.comp inc
    have hgz : ∀ z : ↥Yst, (g z : ModGL Tag.D4 L) =
        (Ξ ⟨z.1, hYst_le_Y z.2⟩ : ModGL Tag.D4 L) := fun _ => rfl
    have hφmem : ∀ z : ↥Yst, (g z : ModGL Tag.D4 L) ∈ G₀ := by
      intro z
      have hzY : z.1 ∈ Y := hYst_le_Y z.2
      have hzstep : S.D.step z.1 = z.1 := ((mem_Yst z.1).mp z.2).2
      have hfix : (Ξ ⟨S.D.step z.1, hstepY z.1 hzY⟩ : ModGL Tag.D4 L) =
          (Ξ ⟨z.1, hzY⟩ : ModGL Tag.D4 L) :=
        congrArg (fun w : ↥Y => (Ξ w : ModGL Tag.D4 L)) (Subtype.ext hzstep)
      rw [hG₀]
      refine ⟨(g z).2, ?_⟩
      rw [hgz z, ← hΞ z.1 hzY (hstepY z.1 hzY)]
      exact hfix
    let φ : ↥Yst →* ↥G₀ :=
      { toFun := fun z => ⟨(g z : ModGL Tag.D4 L), hφmem z⟩
        map_one' := by
          apply Subtype.ext
          exact congrArg (Subtype.val : ↥(adjointGroup Tag.D4 L) → ModGL Tag.D4 L) (map_one g)
        map_mul' := fun z w => by
          apply Subtype.ext
          exact congrArg (Subtype.val : ↥(adjointGroup Tag.D4 L) → ModGL Tag.D4 L)
            (map_mul g z w) }
    have hinj : Function.Injective φ := by
      intro z w hzw
      have h1 : ((φ z : ↥G₀) : ModGL Tag.D4 L) = ((φ w : ↥G₀) : ModGL Tag.D4 L) :=
        congrArg (Subtype.val : ↥G₀ → ModGL Tag.D4 L) hzw
      have h2 : inc z = inc w := Ξ.injective (Subtype.ext h1)
      exact Subtype.ext (congrArg (Subtype.val : ↥Y → ModGL .E6 L) h2)
    have hsurj : Function.Surjective φ := by
      intro w
      have hwadj : (w.1 : ModGL Tag.D4 L) ∈ adjointGroup Tag.D4 L := ((hG₀ w.1).mp w.2).1
      have hwfix : d4P L ^ r * Units.map (entrywiseHom Fr) (w.1 : ModGL Tag.D4 L) *
          (d4P L ^ r)⁻¹ = w.1 := ((hG₀ w.1).mp w.2).2
      let u : ↥Y := Ξ.symm ⟨w.1, hwadj⟩
      have hu : (Ξ u : ModGL Tag.D4 L) = w.1 :=
        congrArg Subtype.val (MulEquiv.apply_symm_apply Ξ ⟨w.1, hwadj⟩)
      have hufix : S.D.step u.1 = u.1 := by
        have hYstep : S.D.step u.1 ∈ Y := hstepY u.1 u.2
        have huu : (Ξ ⟨u.1, u.2⟩ : ModGL Tag.D4 L) = (Ξ u : ModGL Tag.D4 L) := rfl
        have heq : (Ξ ⟨S.D.step u.1, hYstep⟩ : ModGL Tag.D4 L) = (Ξ u : ModGL Tag.D4 L) := by
          rw [hΞ u.1 u.2 hYstep, huu, hu]
          exact hwfix
        have hsub : (⟨S.D.step u.1, hYstep⟩ : ↥Y) = u := Ξ.injective (Subtype.ext heq)
        exact congrArg Subtype.val hsub
      have huYst : u.1 ∈ Yst := (mem_Yst u.1).mpr ⟨u.2, hufix⟩
      refine ⟨⟨u.1, huYst⟩, ?_⟩
      apply Subtype.ext
      change (Ξ (inc ⟨u.1, huYst⟩) : ModGL Tag.D4 L) = w.1
      rw [show inc ⟨u.1, huYst⟩ = u from Subtype.ext rfl]
      exact hu
    let e : ↥Yst ≃* ↥G₀ := MulEquiv.ofBijective φ ⟨hinj, hsurj⟩
    haveI : Group.IsPerfect ↥G₀ := hperf
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hcomm : ⁅Yst, Yst⁆ = Yst := Subgroup.isPerfect_iff.mp hperfYst
  have hYst_le_Γ : Yst ≤ S.Γ := by
    rw [← hcomm]
    show ⁅Yst, Yst⁆ ≤ ⁅S.D.model, S.D.model⁆
    exact Subgroup.commutator_mono hYst_le_M hYst_le_M
  have hΓ_le_M : S.Γ ≤ S.D.model := by
    show ⁅S.D.model, S.D.model⁆ ≤ S.D.model
    exact Subgroup.commutator_le_self S.D.model
  have hinf_le_Yst : Y ⊓ S.Γ ≤ Yst := by
    rw [← hYM]
    exact inf_le_inf le_rfl hΓ_le_M
  have hYst_eq : Yst = Y ⊓ S.Γ :=
    le_antisymm (le_inf (by rw [hYst]; exact inf_le_left) hYst_le_Γ) hinf_le_Yst
  have hR_eq : rationalComponent S.ρ S.Γ (rootCharHom a) i = Yst := by
    rw [hR, ← hYst_eq, hcomm]
  constructor
  · rw [hR_eq, hYst]
    exact inf_le_left
  · intro y hy
    rw [hR_eq, mem_Yst]
    constructor
    · rintro ⟨-, hstep⟩
      rw [hG₀]
      refine ⟨(Ξ ⟨y, hy⟩).2, ?_⟩
      have hfix : (Ξ ⟨S.D.step y, hstepY y hy⟩ : ModGL Tag.D4 L) =
          (Ξ ⟨y, hy⟩ : ModGL Tag.D4 L) :=
        congrArg (fun w : ↥Y => (Ξ w : ModGL Tag.D4 L)) (Subtype.ext hstep)
      rw [← hΞ y hy (hstepY y hy)]
      exact hfix
    · intro hG
      refine ⟨hy, ?_⟩
      have hGfix : d4P L ^ r * Units.map (entrywiseHom Fr) (Ξ ⟨y, hy⟩ : ModGL Tag.D4 L) *
          (d4P L ^ r)⁻¹ = (Ξ ⟨y, hy⟩ : ModGL Tag.D4 L) := ((hG₀ _).mp hG).2
      have heq : (Ξ ⟨S.D.step y, hstepY y hy⟩ : ModGL Tag.D4 L) =
          (Ξ ⟨y, hy⟩ : ModGL Tag.D4 L) := by
        rw [hΞ y hy (hstepY y hy)]
        exact hGfix
      have hsub : (⟨S.D.step y, hstepY y hy⟩ : ↥Y) = ⟨y, hy⟩ :=
        Ξ.injective (Subtype.ext heq)
      exact congrArg Subtype.val hsub

end CFSG.StandardType.NTPlane

end
