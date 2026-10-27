module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.LocalAnalysis.StandardType.GGCentD4Alpha
public import CFSG.LocalAnalysis.StandardType.GGCentD4Fix
public import CFSG.LocalAnalysis.StandardType.GGCentD4Frob
public import CFSG.LocalAnalysis.StandardType.GGCentD4Lang
public import CFSG.LocalAnalysis.StandardType.GGCentPerm
public import CFSG.LocalAnalysis.StandardType.GGCentFrob

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Lang.D4Three
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz (d4Q)

private theorem ntpD4_Y_eq
    
    {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ)
    (i : KernelComponent (rootCharHom a)) (hi : ∀ j : KernelComponent (rootCharHom a), j = i)
    (Y : Subgroup (ModGL .E6 L)) (hY : Y = rootSpan Tag.E6 L (rootCharKernel a)) :
    Y = componentRootSpan L (rootCharHom a) i := by
  have hcomp_eq : componentRoots (rootCharHom a) i = rootCharKernel a := by
    ext α
    constructor
    · rintro ⟨hα, -⟩; exact hα
    · intro hα
      exact ⟨hα, hi (⟦⟨α, hα⟩⟧ : KernelComponent (rootCharHom a))⟩
  rw [hY]
  change rootSpan Tag.E6 L (rootCharKernel a) =
    rootSpan Tag.E6 L (componentRoots (rootCharHom a) i)
  rw [hcomp_eq]

theorem ntpD4_step_mem
    
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup .E6 L p₀)
    (a : Fin Tag.E6.rank → Lˣ) (hT : rootDiagUnit .E6 a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (hi : ∀ j : KernelComponent (rootCharHom a), j = i)
    (Y : Subgroup (ModGL .E6 L)) (hY : Y = rootSpan Tag.E6 L (rootCharKernel a)) :
    ∀ y ∈ Y, S.D.step y ∈ Y := by
  obtain ⟨ρb, -, hρspan⟩ := ntpS4_frobPerm S a hT
  have hYspan : Y = componentRootSpan L (rootCharHom a) i := ntpD4_Y_eq a i hi Y hY
  intro y hy
  have h1 : S.D.step y ∈ (componentRootSpan L (rootCharHom a) i).map S.D.step :=
    ⟨y, hYspan ▸ hy, rfl⟩
  rw [hρspan i, hi (ρb i)] at h1
  rwa [← hYspan] at h1

theorem ntpD4_nconj_mem
    
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (a : Fin Tag.E6.rank → Lˣ) (n : ModGL .E6 L) (hnA : n ∈ adjointGroup .E6 L)
    (hcomm : rootDiagUnit .E6 a * n = n * rootDiagUnit .E6 a)
    (i : KernelComponent (rootCharHom a)) (hi : ∀ j : KernelComponent (rootCharHom a), j = i)
    (Y : Subgroup (ModGL .E6 L)) (hY : Y = rootSpan Tag.E6 L (rootCharKernel a)) :
    ∀ y ∈ Y, n * y * n⁻¹ ∈ Y := by
  obtain ⟨π, hπ⟩ := ntpS2_perm (L := L) a n hnA hcomm
  have hYspan : Y = componentRootSpan L (rootCharHom a) i := ntpD4_Y_eq a i hi Y hY
  intro y hy
  have h1 : n * y * n⁻¹ ∈
      (componentRootSpan L (rootCharHom a) i).map (MulAut.conj n).toMonoidHom :=
    ⟨y, hYspan ▸ hy, rfl⟩
  rw [hπ i, hi (π i)] at h1
  rwa [← hYspan] at h1

theorem ntpD4_comm
    
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup .E6 L p₀)
    (n : ModGL .E6 L) (hn : n ∈ S.D.model)
    (Y : Subgroup (ModGL .E6 L)) (hstepY : ∀ y ∈ Y, S.D.step y ∈ Y)
    (hnY : ∀ y ∈ Y, n * y * n⁻¹ ∈ Y)
    (Θ : ↥Y ≃* ↥(adjointGroup Tag.D4 L)) (g : ↥(adjointGroup Tag.D4 L)) (ε : ℕ)
    (halpha : ∀ (y : ModGL .E6 L) (hy : y ∈ Y) (hy' : n * y * n⁻¹ ∈ Y),
      Θ ⟨n * y * n⁻¹, hy'⟩ = g * d4Graph L ε (Θ ⟨y, hy⟩) * g⁻¹)
    (Fr : L →+* L) (r s : ℕ) (c : ↥(adjointGroup Tag.D4 L))
    (hfrob : ∀ (y : ModGL .E6 L) (hy : y ∈ Y) (hy' : S.D.step y ∈ Y),
      (Θ ⟨S.D.step y, hy'⟩ : ModGL Tag.D4 L) = (c : ModGL Tag.D4 L) *
        (d4P L ^ r * d4Q L ^ s * Units.map (entrywiseHom Fr) (Θ ⟨y, hy⟩ : ModGL Tag.D4 L) *
          (d4Q L ^ s)⁻¹ * (d4P L ^ r)⁻¹) * (c : ModGL Tag.D4 L)⁻¹) :
    ∀ x ∈ adjointGroup Tag.D4 L,
      (c : ModGL Tag.D4 L) * (d4P L ^ r * d4Q L ^ s * Units.map (entrywiseHom Fr)
        ((g : ModGL Tag.D4 L) * (d4P L ^ ε * x * (d4P L ^ ε)⁻¹) * (g : ModGL Tag.D4 L)⁻¹) *
        (d4Q L ^ s)⁻¹ * (d4P L ^ r)⁻¹) * (c : ModGL Tag.D4 L)⁻¹ =
      (g : ModGL Tag.D4 L) * (d4P L ^ ε * ((c : ModGL Tag.D4 L) * (d4P L ^ r * d4Q L ^ s * Units.map
        (entrywiseHom Fr) x * (d4Q L ^ s)⁻¹ * (d4P L ^ r)⁻¹) * (c : ModGL Tag.D4 L)⁻¹) *
        (d4P L ^ ε)⁻¹) * (g : ModGL Tag.D4 L)⁻¹ := by
  intro x hx
  obtain ⟨⟨y0, hy0⟩, hΘy⟩ := Θ.surjective ⟨x, hx⟩
  have hstn : S.D.step n = n := (S.D.mem_model.mp hn).2
  have hy1 : n * y0 * n⁻¹ ∈ Y := hnY y0 hy0
  have hy2 : S.D.step y0 ∈ Y := hstepY y0 hy0
  have hy3 : S.D.step (n * y0 * n⁻¹) ∈ Y := hstepY _ hy1
  have hy4 : n * S.D.step y0 * n⁻¹ ∈ Y := hnY _ hy2
  have heq : S.D.step (n * y0 * n⁻¹) = n * S.D.step y0 * n⁻¹ := by
    rw [map_mul, map_mul, map_inv, hstn]
  have hE : Θ ⟨S.D.step (n * y0 * n⁻¹), hy3⟩ = Θ ⟨n * S.D.step y0 * n⁻¹, hy4⟩ := by
    congr 1
    exact Subtype.ext heq
  have hA := hfrob (n * y0 * n⁻¹) hy1 hy3
  have hB := halpha (S.D.step y0) hy2 hy4
  have hC := halpha y0 hy0 hy1
  have hD := hfrob y0 hy0 hy2
  rw [hΘy] at hC hD
  have hC' : (Θ ⟨n * y0 * n⁻¹, hy1⟩ : ModGL Tag.D4 L) =
      (g : ModGL Tag.D4 L) * (d4P L ^ ε * x * (d4P L ^ ε)⁻¹) * (g : ModGL Tag.D4 L)⁻¹ := by
    rw [hC]
    rfl
  have hB' : (Θ ⟨n * S.D.step y0 * n⁻¹, hy4⟩ : ModGL Tag.D4 L) =
      (g : ModGL Tag.D4 L) * (d4P L ^ ε * (Θ ⟨S.D.step y0, hy2⟩ : ModGL Tag.D4 L) *
        (d4P L ^ ε)⁻¹) * (g : ModGL Tag.D4 L)⁻¹ := by
    rw [hB]
    rfl
  have hD' : (Θ ⟨S.D.step y0, hy2⟩ : ModGL Tag.D4 L) = (c : ModGL Tag.D4 L) *
      (d4P L ^ r * d4Q L ^ s * Units.map (entrywiseHom Fr) x * (d4Q L ^ s)⁻¹ *
        (d4P L ^ r)⁻¹) * (c : ModGL Tag.D4 L)⁻¹ := hD
  calc (c : ModGL Tag.D4 L) * (d4P L ^ r * d4Q L ^ s * Units.map (entrywiseHom Fr)
        ((g : ModGL Tag.D4 L) * (d4P L ^ ε * x * (d4P L ^ ε)⁻¹) * (g : ModGL Tag.D4 L)⁻¹) *
        (d4Q L ^ s)⁻¹ * (d4P L ^ r)⁻¹) * (c : ModGL Tag.D4 L)⁻¹
      = (Θ ⟨S.D.step (n * y0 * n⁻¹), hy3⟩ : ModGL Tag.D4 L) := by rw [hA, hC']
    _ = (Θ ⟨n * S.D.step y0 * n⁻¹, hy4⟩ : ModGL Tag.D4 L) := by rw [hE]
    _ = _ := by rw [hB', hD']

theorem ntpD4_xi
    
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (n : ModGL .E6 L) (Y : Subgroup (ModGL .E6 L)) (st : ModGL .E6 L →* ModGL .E6 L)
    (Θ : ↥Y ≃* ↥(adjointGroup Tag.D4 L)) (g : ↥(adjointGroup Tag.D4 L)) (ε : ℕ)
    (halpha : ∀ (y : ModGL .E6 L) (hy : y ∈ Y) (hy' : n * y * n⁻¹ ∈ Y),
      Θ ⟨n * y * n⁻¹, hy'⟩ = g * d4Graph L ε (Θ ⟨y, hy⟩) * g⁻¹)
    {f : ℕ} (hf : 1 ≤ f) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ ((2 : ℕ) ^ f)) (r : ℕ)
    (c : ↥(adjointGroup Tag.D4 L))
    (hfrob : ∀ (y : ModGL .E6 L) (hy : y ∈ Y) (hy' : st y ∈ Y),
      (Θ ⟨st y, hy'⟩ : ModGL Tag.D4 L) = (c : ModGL Tag.D4 L) *
        (d4P L ^ r * Units.map (entrywiseHom Fr) (Θ ⟨y, hy⟩ : ModGL Tag.D4 L) * (d4P L ^ r)⁻¹) *
          (c : ModGL Tag.D4 L)⁻¹)
    (hcomm : ∀ x ∈ adjointGroup Tag.D4 L,
      (c : ModGL Tag.D4 L) * (d4P L ^ r * Units.map (entrywiseHom Fr) ((g : ModGL Tag.D4 L) *
        (d4P L ^ ε * x * (d4P L ^ ε)⁻¹) * (g : ModGL Tag.D4 L)⁻¹) * (d4P L ^ r)⁻¹) *
        (c : ModGL Tag.D4 L)⁻¹ =
      (g : ModGL Tag.D4 L) * (d4P L ^ ε * ((c : ModGL Tag.D4 L) * (d4P L ^ r * Units.map
        (entrywiseHom Fr) x * (d4P L ^ r)⁻¹) * (c : ModGL Tag.D4 L)⁻¹) *
        (d4P L ^ ε)⁻¹) * (g : ModGL Tag.D4 L)⁻¹) :
    ∃ (Ξ : ↥Y ≃* ↥(adjointGroup Tag.D4 L)) (g' : ↥(adjointGroup Tag.D4 L)),
      (∀ (y : ModGL .E6 L) (hy : y ∈ Y) (hy' : st y ∈ Y),
        (Ξ ⟨st y, hy'⟩ : ModGL Tag.D4 L) = d4P L ^ r * Units.map (entrywiseHom Fr)
          (Ξ ⟨y, hy⟩ : ModGL Tag.D4 L) * (d4P L ^ r)⁻¹) ∧
      (∀ (y : ModGL .E6 L) (hy : y ∈ Y) (hy' : n * y * n⁻¹ ∈ Y),
        Ξ ⟨n * y * n⁻¹, hy'⟩ = g' * d4Graph L ε (Ξ ⟨y, hy⟩) * g'⁻¹) ∧
      (∀ x ∈ adjointGroup Tag.D4 L,
        d4P L ^ r * Units.map (entrywiseHom Fr) ((g' : ModGL Tag.D4 L) * (d4P L ^ ε * x *
          (d4P L ^ ε)⁻¹) * (g' : ModGL Tag.D4 L)⁻¹) * (d4P L ^ r)⁻¹ =
        (g' : ModGL Tag.D4 L) * (d4P L ^ ε * (d4P L ^ r * Units.map (entrywiseHom Fr) x *
          (d4P L ^ r)⁻¹) * (d4P L ^ ε)⁻¹) * (g' : ModGL Tag.D4 L)⁻¹) := by
  obtain ⟨z, hz⟩ := ntpD4_lang hf Fr hFr r c
  let Ξ : ↥Y ≃* ↥(adjointGroup Tag.D4 L) := Θ.trans (MulAut.conj z)
  have hΞ : ∀ y : ↥Y, ((Ξ y : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) =
      (z : ModGL Tag.D4 L) * (Θ y : ModGL Tag.D4 L) * (z : ModGL Tag.D4 L)⁻¹ := fun y => rfl
  refine ⟨Ξ, z * g * (d4Graph L ε z)⁻¹, ?_, ?_, ?_⟩
  · intro y hy hy'
    rw [hΞ, hΞ, hfrob y hy hy', hz]
    simp only [map_mul, map_inv]
    group
  · intro y hy hy'
    have h1 := halpha y hy hy'
    change (z * Θ ⟨n * y * n⁻¹, hy'⟩ * z⁻¹ : ↥(adjointGroup Tag.D4 L)) =
      (z * g * (d4Graph L ε z)⁻¹) * d4Graph L ε (z * Θ ⟨y, hy⟩ * z⁻¹) *
        (z * g * (d4Graph L ε z)⁻¹)⁻¹
    rw [h1, map_mul, map_mul, map_inv]
    group
  · intro x hx
    have hx0 : (z : ModGL Tag.D4 L)⁻¹ * x * (z : ModGL Tag.D4 L) ∈ adjointGroup Tag.D4 L :=
      mul_mem (mul_mem (inv_mem z.2) hx) z.2
    have h0 := hcomm _ hx0
    rw [hz] at h0
    have hg' : ((z * g * (d4Graph L ε z)⁻¹ : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) =
        (z : ModGL Tag.D4 L) * g * (d4P L ^ ε * (z : ModGL Tag.D4 L) * (d4P L ^ ε)⁻¹)⁻¹ := rfl
    rw [hg']
    simp only [map_mul, map_inv] at h0 ⊢
    have key := congrArg (fun w => (z : ModGL Tag.D4 L) * w * (z : ModGL Tag.D4 L)⁻¹) h0
    convert key using 1 <;> group

end CFSG.StandardType.NTPlane

end
