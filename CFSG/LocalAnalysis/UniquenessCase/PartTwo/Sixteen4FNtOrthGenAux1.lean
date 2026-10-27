module

public import CFSG.Open.StatedDefs
public import CFSG.LieType.BorelTits.OrthogonalModels
public import CFSG.Quasithin.Background.G64NatSec
public import CFSG.Mathlib.Decide.Bounded
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B4ModelsWitness
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LieType.BorelTits CFSG.Open
open scoped CFSG.Decide.Bounded

@[expose] def w183Gen {K : Type} [Field K] {ι : Type} (Q : (ι → K) → K)
    (P : (ι → K) → (ι → K) → K) (S : Set (ι → K)) : Prop :=
  ∀ T : Set (ι → K), S ⊆ T →
    (∀ v ∈ T, ∀ w ∈ T, Q v = 1 → Q w = 1 → P v w = 1 → v + w ∈ T) →
      {v | Q v = 1} ⊆ T

@[expose] def w183StepF {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    [DecidableEq K] (Q : (ι → K) → K) (P : (ι → K) → (ι → K) → K)
    (s : Finset (ι → K)) : Finset (ι → K) :=
  s ∪ (((s ×ˢ s).filter
        (fun p : (ι → K) × (ι → K) => Q p.1 = 1 ∧ Q p.2 = 1 ∧
          P p.1 p.2 = 1)).image (fun p => p.1 + p.2))

theorem w183MemStepF {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    [DecidableEq K] (Q : (ι → K) → K) (P : (ι → K) → (ι → K) → K)
    (s : Finset (ι → K)) (v : ι → K) :
    v ∈ w183StepF Q P s ↔ v ∈ s ∨ ∃ a ∈ s, ∃ b ∈ s,
      Q a = 1 ∧ Q b = 1 ∧ P a b = 1 ∧ a + b = v := by
  simp only [w183StepF, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_product]
  constructor
  · rintro (h | ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, hq1, hq2, hp⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, ha, b, hb, hq1, hq2, hp, rfl⟩
  · rintro (h | ⟨a, ha, b, hb, hq1, hq2, hp, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨(a, b), ⟨⟨ha, hb⟩, hq1, hq2, hp⟩, rfl⟩

theorem w183SubsetIterate {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    [DecidableEq K] (Q : (ι → K) → K) (P : (ι → K) → (ι → K) → K)
    {s : Finset (ι → K)} {T : Set (ι → K)} (hs : ∀ v ∈ s, v ∈ T)
    (hT : ∀ v ∈ T, ∀ w ∈ T, Q v = 1 → Q w = 1 → P v w = 1 → v + w ∈ T)
    (k : ℕ) : ∀ v ∈ (w183StepF Q P)^[k] s, v ∈ T := by
  induction k with
  | zero => simpa using hs
  | succ k ih =>
    intro v hv
    rw [Function.iterate_succ_apply'] at hv
    rw [w183MemStepF] at hv
    rcases hv with hv | ⟨a, ha, b, hb, hq1, hq2, hp, rfl⟩
    · exact ih v hv
    · exact hT a (ih a ha) b (ih b hb) hq1 hq2 hp

@[expose] def w183PiEquiv {K K' : Type} [Semiring K] [Semiring K'] (e : K ≃+* K') (ι : Type) :
    (ι → K) ≃ (ι → K') :=
  Equiv.piCongrRight fun _ => e.toEquiv

@[simp] theorem w183PiEquiv_apply {K K' : Type} [Semiring K] [Semiring K']
    (e : K ≃+* K') {ι : Type} (v : ι → K) (i : ι) :
    w183PiEquiv e ι v i = e (v i) := rfl

theorem w183GenMapRingEquiv {K K' : Type} [Field K] [Field K'] (e : K ≃+* K') {ι : Type}
    (Q : (ι → K) → K) (Q' : (ι → K') → K')
    (P : (ι → K) → (ι → K) → K)
    (P' : (ι → K') → (ι → K') → K')
    (hQ : ∀ v, e (Q v) = Q' (w183PiEquiv e ι v))
    (hP : ∀ v w, e (P v w) = P' (w183PiEquiv e ι v) (w183PiEquiv e ι w))
    {S' : Set (ι → K')} (h : w183Gen Q' P' S') :
    w183Gen Q P ((w183PiEquiv e ι) ⁻¹' S') := by
  intro T hT hcl v hv
  let φ := w183PiEquiv e ι
  let T' : Set (ι → K') := φ '' T
  have hS'T' : S' ⊆ T' := by
    intro s' hs'
    exact ⟨φ.symm s', hT (by rw [Set.mem_preimage, φ.apply_symm_apply]; exact hs'),
      φ.apply_symm_apply s'⟩
  have hT'cl : ∀ v ∈ T', ∀ w ∈ T', Q' v = 1 → Q' w = 1 → P' v w = 1 →
      v + w ∈ T' := by
    rintro v ⟨v₀, hv₀, rfl⟩ w ⟨w₀, hw₀, rfl⟩ qv qw hp
    refine ⟨v₀ + w₀, hcl v₀ hv₀ w₀ hw₀ ?_ ?_ ?_, by
      ext i
      change w183PiEquiv e ι (v₀ + w₀) i =
        w183PiEquiv e ι v₀ i + w183PiEquiv e ι w₀ i
      simp [w183PiEquiv, map_add]⟩
    · have h1 : e (Q v₀) = 1 := by rw [hQ v₀]; exact qv
      exact e.injective (by rw [h1, map_one])
    · have h1 : e (Q w₀) = 1 := by rw [hQ w₀]; exact qw
      exact e.injective (by rw [h1, map_one])
    · have h1 : e (P v₀ w₀) = 1 := by rw [hP v₀ w₀]; exact hp
      exact e.injective (by rw [h1, map_one])
  have hv' : Q' (φ v) = 1 := by rw [← hQ v, hv, map_one]
  obtain ⟨u, huT, hu_eq⟩ := h T' hS'T' hT'cl hv'
  rwa [φ.injective hu_eq] at huT

theorem w183EqZeroOrOne {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (x : K) :
    x = 0 ∨ x = 1 := by
  have h2 : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  rcases h2 (CFSG.Quasithin.G64.ringEquivZModTwo K hK x) with h | h
  · left; exact (CFSG.Quasithin.G64.ringEquivZModTwo K hK).injective (by rw [h, map_zero])
  · right; exact (CFSG.Quasithin.G64.ringEquivZModTwo K hK).injective (by rw [h, map_one])

theorem w183FourEqOne {K : Type} [Field K] (hK : ∀ c : K, c = 0 ∨ c = 1)
    {p q r s : K} (h : p - q - r + s = 1) : p = 1 ∨ q = 1 ∨ r = 1 ∨ s = 1 := by
  by_contra h'
  rw [not_or, not_or, not_or] at h'
  obtain ⟨hp, hq, hr, hs⟩ := h'
  have hp0 : p = 0 := (hK p).resolve_right hp
  have hq0 : q = 0 := (hK q).resolve_right hq
  have hr0 : r = 0 := (hK r).resolve_right hr
  have hs0 : s = 0 := (hK s).resolve_right hs
  rw [hp0, hq0, hr0, hs0] at h
  norm_num at h

theorem w183EqOfClosedAdj {K : Type} [Field K] {ι : Type} {Q : (ι → K) → K}
    {P : (ι → K) → (ι → K) → K}
    {A : Set (ι → K)} {a : ι → K} (ha : a ∈ A)
    (hA : ∀ w ∈ A, ∀ w', Q w' = 1 → P w w' = 1 → w' ∈ A)
    (hN : ∀ w, Q w = 1 → w ≠ a → P a w = 1 ∨ ∃ b, Q b = 1 ∧ P a b = 1 ∧ P b w = 1) :
    ∀ w, Q w = 1 → w ∈ A := by
  intro w hw
  by_cases hwa : w = a
  · rwa [hwa]
  · rcases hN w hw hwa with h | ⟨b, hb, hab, hwb⟩
    · exact hA a ha w hw h
    · exact hA b (hA a ha b hb hab) w hw hwb

theorem w183ExistsCommonNeighbor {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hK : ∀ c : K, c = 0 ∨ c = 1) (Φ : QuadForm K V)
    (h5 : 5 ≤ Module.finrank K V) {u v : V} (hu : Φ.Q u = 1) (hv : Φ.Q v = 1)
    (huv0 : Φ.polar.β u v = 0) (hne : u ≠ v) :
    ∃ w, Φ.Q w = 1 ∧ Φ.polar.β u w = 1 ∧ Φ.polar.β v w = 1 := by
  classical
  have h2 : (2 : K) = 0 := by
    rcases hK 2 with h | h
    · exact h
    · exfalso
      have h1 : (1 : K) = 0 := by
        have hh : (2 : K) = 1 + 1 := by norm_num
        rw [hh] at h
        have h' : (1 : K) + 1 = 1 + 0 := by rw [h, add_zero]
        exact add_left_cancel h'
      exact one_ne_zero h1
  have hu0 : u ≠ 0 := fun h => by rw [h, Φ.Q_zero] at hu; exact zero_ne_one hu
  have hv0 : v ≠ 0 := fun h => by rw [h, Φ.Q_zero] at hv; exact zero_ne_one hv
  let U : Submodule K V := K ∙ u ⊔ K ∙ v
  have hUu : u ∈ Φ.polar.perp U := by
    change u ∈ Φ.polar.perp (K ∙ u ⊔ K ∙ v)
    rw [ReflForm.perp_sup, Submodule.mem_inf]
    exact ⟨(ReflForm.mem_perp_span_singleton (F := Φ.polar)).mpr
        (by rw [QuadForm.polar_self, hu, mul_one, h2]),
      (ReflForm.mem_perp_span_singleton (F := Φ.polar)).mpr
        (by exact (QuadForm.polar_symm Φ v u).trans huv0)⟩
  have hUv : v ∈ Φ.polar.perp U := by
    change v ∈ Φ.polar.perp (K ∙ u ⊔ K ∙ v)
    rw [ReflForm.perp_sup, Submodule.mem_inf]
    exact ⟨(ReflForm.mem_perp_span_singleton (F := Φ.polar)).mpr huv0,
      (ReflForm.mem_perp_span_singleton (F := Φ.polar)).mpr
        (by rw [QuadForm.polar_self, hv, mul_one, h2])⟩
  have hUle : U ≤ Φ.polar.perp U := by
    change K ∙ u ⊔ K ∙ v ≤ Φ.polar.perp (K ∙ u ⊔ K ∙ v)
    exact sup_le ((Submodule.span_singleton_le_iff_mem u _).mpr hUu)
      ((Submodule.span_singleton_le_iff_mem v _).mpr hUv)
  have h1u : Module.finrank K (K ∙ u) ≤ 1 := by
    rcases eq_or_ne u 0 with h | h
    · subst h; rw [Submodule.span_singleton_eq_bot.mpr rfl]; simp
    · rw [finrank_span_singleton h]
  have h1v : Module.finrank K (K ∙ v) ≤ 1 := by
    rcases eq_or_ne v 0 with h | h
    · subst h; rw [Submodule.span_singleton_eq_bot.mpr rfl]; simp
    · rw [finrank_span_singleton h]
  have hUfin : Module.finrank K U ≤ 2 := by
    have hle : U ≤ Submodule.span K (({u, v} : Finset V) : Set V) := by
      change K ∙ u ⊔ K ∙ v ≤ Submodule.span K (({u, v} : Finset V) : Set V)
      refine sup_le ?_ ?_
      · exact (Submodule.span_singleton_le_iff_mem u _).mpr
          (Submodule.subset_span (by simp))
      · exact (Submodule.span_singleton_le_iff_mem v _).mpr
          (Submodule.subset_span (by simp))
    calc Module.finrank K U
        ≤ Module.finrank K (Submodule.span K (({u, v} : Finset V) : Set V)) :=
          Submodule.finrank_mono hle
      _ ≤ ({u, v} : Finset V).card := finrank_span_finset_le_card _
      _ = 2 := Finset.card_pair hne
  have hWU : Φ.polar.perp U ≠ U := by
    intro h
    have h1 := Φ.polar.finrank_perp U
    rw [h] at h1
    omega
  have hnot : ¬ (Φ.polar.perp U ≤ Φ.polar.perp (Φ.polar.perp U)) := by
    intro hle
    apply hWU
    rw [ReflForm.perp_perp (F := Φ.polar) (W := U)] at hle
    exact le_antisymm hle hUle
  obtain ⟨z, hzW, hznot⟩ := Set.not_subset.mp hnot
  have hznot' : ¬ (∀ w ∈ Φ.polar.perp U, Φ.polar.β w z = 0) :=
    fun h => hznot ((ReflForm.mem_perp (F := Φ.polar)).mpr h)
  push Not at hznot'
  obtain ⟨z', hz'W, hzz'⟩ := hznot'
  have hzz1 : Φ.polar.β z z' = 1 := by
    have h : Φ.polar.β z' z = Φ.polar.β z z' := QuadForm.polar_symm Φ z' z
    rw [h] at hzz'
    exact (hK _).resolve_left hzz'
  obtain ⟨a, ha⟩ : ∃ a, Φ.polar.β u a = 1 := by
    by_contra h
    apply hu0
    apply Φ.polar.nondeg u
    intro w
    rcases hK (Φ.polar.β u w) with h0 | h1
    · exact h0
    · exact absurd h1 (not_exists.mp h w)
  obtain ⟨b, hb⟩ : ∃ b, Φ.polar.β v b = 1 := by
    by_contra h
    apply hv0
    apply Φ.polar.nondeg v
    intro w
    rcases hK (Φ.polar.β v w) with h0 | h1
    · exact h0
    · exact absurd h1 (not_exists.mp h w)
  have hw0 : ∃ w, Φ.polar.β u w = 1 ∧ Φ.polar.β v w = 1 := by
    rcases hK (Φ.polar.β v a) with hp | hp
    · rcases hK (Φ.polar.β u b) with hq | hq
      · exact ⟨a + b, by simp [ReflForm.add_right, ha, hq],
          by simp [ReflForm.add_right, hp, hb]⟩
      · exact ⟨b, hq, hb⟩
    · exact ⟨a, ha, hp⟩
  obtain ⟨w₀, hw0u, hw0v⟩ := hw0
  have hmain : Φ.Q (w₀ + (z + z')) - Φ.Q (w₀ + z) - Φ.Q (w₀ + z') + Φ.Q w₀ = 1 := by
    have h1 := Φ.Q_add (w₀ + z) z'
    have h2 := Φ.Q_add w₀ z'
    have h3 := Φ.polar.add_left w₀ z z'
    have hsum : w₀ + z + z' = w₀ + (z + z') := by abel
    rw [hsum] at h1
    rw [h1, h2, h3, hzz1]
    ring
  rcases w183FourEqOne hK hmain with h | h | h | h
  · refine ⟨w₀ + (z + z'), h, ?_, ?_⟩
    · rw [ReflForm.add_right, ReflForm.add_right, hw0u,
        ((ReflForm.mem_perp (F := Φ.polar)).mp hzW) u (by
        change u ∈ K ∙ u ⊔ K ∙ v
        exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self u)),
        ((ReflForm.mem_perp (F := Φ.polar)).mp hz'W) u (by
        change u ∈ K ∙ u ⊔ K ∙ v
        exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self u))]
      ring
    · rw [ReflForm.add_right, ReflForm.add_right, hw0v,
        ((ReflForm.mem_perp (F := Φ.polar)).mp hzW) v (by
        change v ∈ K ∙ u ⊔ K ∙ v
        exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)),
        ((ReflForm.mem_perp (F := Φ.polar)).mp hz'W) v (by
        change v ∈ K ∙ u ⊔ K ∙ v
        exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))]
      ring
  · refine ⟨w₀ + z, h, ?_, ?_⟩
    · rw [ReflForm.add_right, hw0u, ((ReflForm.mem_perp (F := Φ.polar)).mp hzW) u (by
        change u ∈ K ∙ u ⊔ K ∙ v
        exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self u)), add_zero]
    · rw [ReflForm.add_right, hw0v, ((ReflForm.mem_perp (F := Φ.polar)).mp hzW) v (by
        change v ∈ K ∙ u ⊔ K ∙ v
        exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)), add_zero]
  · refine ⟨w₀ + z', h, ?_, ?_⟩
    · rw [ReflForm.add_right, hw0u, ((ReflForm.mem_perp (F := Φ.polar)).mp hz'W) u (by
        change u ∈ K ∙ u ⊔ K ∙ v
        exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self u)), add_zero]
    · rw [ReflForm.add_right, hw0v, ((ReflForm.mem_perp (F := Φ.polar)).mp hz'W) v (by
        change v ∈ K ∙ u ⊔ K ∙ v
        exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)), add_zero]
  · refine ⟨w₀, h, hw0u, hw0v⟩

theorem w183ConnQuadForm {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hK : ∀ c : K, c = 0 ∨ c = 1) (Φ : QuadForm K V)
    (h5 : 5 ≤ Module.finrank K V) :
    ∀ u v : V, Φ.Q u = 1 → Φ.Q v = 1 → u ≠ v →
      Φ.polar.β u v = 1 ∨ ∃ w, Φ.Q w = 1 ∧ Φ.polar.β u w = 1 ∧
        Φ.polar.β v w = 1 := by
  intro u v hu hv hne
  by_cases huv : Φ.polar.β u v = 1
  · exact Or.inl huv
  · exact Or.inr (w183ExistsCommonNeighbor hK Φ h5 hu hv
      ((hK _).resolve_right huv) hne)

@[expose] def w183PlusExt (r : ℕ) (K : Type) [Field K] (w : Fin r ⊕ Fin r → K) :
    Fin (r + 1) ⊕ Fin (r + 1) → K :=
  Sum.elim
    (fun i => Fin.lastCases (0 : K) (fun i' => w (Sum.inl i')) i)
    (fun i => Fin.lastCases (0 : K) (fun i' => w (Sum.inr i')) i)

@[expose] def w183PlusX (r : ℕ) (K : Type) [Field K] : Fin (r + 1) ⊕ Fin (r + 1) → K :=
  Pi.single (Sum.inl (Fin.last r)) 1

@[expose] def w183PlusY (r : ℕ) (K : Type) [Field K] : Fin (r + 1) ⊕ Fin (r + 1) → K :=
  Pi.single (Sum.inr (Fin.last r)) 1

@[simp] theorem w183PlusExt_inl {r : ℕ} {K : Type} [Field K] (w : Fin r ⊕ Fin r → K)
    (i : Fin r) : w183PlusExt r K w (Sum.inl (Fin.castSucc i)) = w (Sum.inl i) := by
  simp [w183PlusExt]

@[simp] theorem w183PlusExt_inr {r : ℕ} {K : Type} [Field K] (w : Fin r ⊕ Fin r → K)
    (i : Fin r) : w183PlusExt r K w (Sum.inr (Fin.castSucc i)) = w (Sum.inr i) := by
  simp [w183PlusExt]

@[simp] theorem w183PlusExt_last_inl {r : ℕ} {K : Type} [Field K] (w : Fin r ⊕ Fin r → K) :
    w183PlusExt r K w (Sum.inl (Fin.last r)) = 0 := by
  simp [w183PlusExt]

@[simp] theorem w183PlusExt_last_inr {r : ℕ} {K : Type} [Field K] (w : Fin r ⊕ Fin r → K) :
    w183PlusExt r K w (Sum.inr (Fin.last r)) = 0 := by
  simp [w183PlusExt]

@[simp] theorem w183PlusExt_zero {r : ℕ} {K : Type} [Field K] :
    w183PlusExt r K (0 : Fin r ⊕ Fin r → K) = 0 := by
  ext i
  rcases i with i | i <;> induction i using Fin.lastCases <;> simp

theorem w183PlusExt_injective (r : ℕ) (K : Type) [Field K] :
    Function.Injective (w183PlusExt r K) := by
  intro v w h
  ext p
  rcases p with i | i
  · have := congr_fun h (Sum.inl (Fin.castSucc i))
    simpa using this
  · have := congr_fun h (Sum.inr (Fin.castSucc i))
    simpa using this

theorem w183PlusExt_add {r : ℕ} {K : Type} [Field K] (v w : Fin r ⊕ Fin r → K) :
    w183PlusExt r K (v + w) = w183PlusExt r K v + w183PlusExt r K w := by
  ext i
  rcases i with i | i
  · induction i using Fin.lastCases with
    | last => simp
    | cast i => simp
  · induction i using Fin.lastCases with
    | last => simp
    | cast i => simp

theorem w183PlusForm {r : ℕ} {K : Type} [Field K] (w : Fin r ⊕ Fin r → K) (a b : K) :
    StatedQuadPlus (r + 1) K
        (w183PlusExt r K w + a • w183PlusX r K + b • w183PlusY r K) =
      StatedQuadPlus r K w + a * b := by
  simp only [StatedQuadPlus, Fin.sum_univ_castSucc, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    w183PlusExt_inl, w183PlusExt_inr, w183PlusExt_last_inl, w183PlusExt_last_inr]
  simp [w183PlusX, w183PlusY, Pi.single_apply, add_mul]

theorem w183QuadPlusPolarForm {r : ℕ} {K : Type} [Field K] (a b : Fin r ⊕ Fin r → K)
    (α β γ δ : K) :
    quadPlusPolar (r + 1) K
        (w183PlusExt r K a + α • w183PlusX r K + β • w183PlusY r K)
        (w183PlusExt r K b + γ • w183PlusX r K + δ • w183PlusY r K) =
      quadPlusPolar r K a b + (α * δ + γ * β) := by
  simp only [quadPlusPolar, Fin.sum_univ_castSucc, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    w183PlusExt_inl, w183PlusExt_inr, w183PlusExt_last_inl, w183PlusExt_last_inr]
  simp [w183PlusX, w183PlusY, Pi.single_apply]

theorem w183QuadPlusPolarExt {r : ℕ} {K : Type} [Field K] (v w : Fin r ⊕ Fin r → K) :
    quadPlusPolar (r + 1) K (w183PlusExt r K v) (w183PlusExt r K w) =
      quadPlusPolar r K v w := by
  have h := w183QuadPlusPolarForm (K := K) v w 0 0 0 0
  simpa using h

theorem w183QuadPlusPolarXExt {r : ℕ} {K : Type} [Field K] (v w : Fin r ⊕ Fin r → K) :
    quadPlusPolar (r + 1) K (w183PlusExt r K v + w183PlusX r K) (w183PlusExt r K w) =
      quadPlusPolar r K v w := by
  have h := w183QuadPlusPolarForm (K := K) v w 1 0 0 0
  simpa using h

theorem w183QuadPlusPolarXY {r : ℕ} {K : Type} [Field K] (w : Fin r ⊕ Fin r → K) :
    quadPlusPolar (r + 1) K (w183PlusExt r K w + w183PlusX r K)
      (w183PlusX r K + w183PlusY r K) = 1 := by
  have h := w183QuadPlusPolarForm (K := K) w 0 1 0 1 1
  simp only [one_smul, zero_smul, add_zero, zero_add, w183PlusExt_zero, mul_one, mul_zero] at h
  have hw : StatedQuadPlus r K (0 : Fin r ⊕ Fin r → K) = 0 := by simp [StatedQuadPlus]
  have hq : quadPlusPolar r K w 0 = 0 := by simp [quadPlusPolar]
  rw [h, hq]
  norm_num

theorem w183QuadPlusPolarYX {r : ℕ} {K : Type} [Field K] (v w : Fin r ⊕ Fin r → K) :
    quadPlusPolar (r + 1) K (w183PlusExt r K v + w183PlusX r K)
      (w183PlusExt r K w + w183PlusY r K) = quadPlusPolar r K v w + 1 := by
  have h := w183QuadPlusPolarForm (K := K) v w 1 0 0 1
  simpa using h

theorem w183ExistsNormOnePerp {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hK : ∀ c : K, c = 0 ∨ c = 1) (Φ : QuadForm K V)
    (h3 : 3 ≤ Module.finrank K V) {w : V} (hw : w ≠ 0) :
    ∃ c, Φ.Q c = 1 ∧ Φ.polar.β w c = 0 := by
  have hW' : Module.finrank K (Φ.polar.perp (K ∙ w)) = Module.finrank K V - 1 := by
    have h1 := Φ.polar.finrank_perp (K ∙ w)
    have h2 : Module.finrank K (K ∙ w) = 1 := finrank_span_singleton hw
    omega
  have hex : ∃ c ∈ Φ.polar.perp (K ∙ w), Φ.Q c = 1 := by
    by_contra h
    have hzero : ∀ c ∈ Φ.polar.perp (K ∙ w), Φ.Q c = 0 := by
      intro c hc
      rcases hK (Φ.Q c) with h0 | h1
      · exact h0
      · exact absurd ⟨c, hc, h1⟩ h
    have hle : Φ.polar.perp (K ∙ w) ≤ Φ.polar.perp (Φ.polar.perp (K ∙ w)) := by
      intro x hx
      rw [ReflForm.mem_perp]
      intro y hy
      have h1 := Φ.Q_add x y
      rw [hzero x hx, hzero y hy, hzero (x + y) ((Φ.polar.perp (K ∙ w)).add_mem hx hy)] at h1
      rw [zero_add, zero_add] at h1
      exact (QuadForm.polar_symm Φ x y).symm.trans h1.symm
    rw [ReflForm.perp_perp] at hle
    have h2 : Module.finrank K (Φ.polar.perp (K ∙ w)) ≤ 1 := by
      calc Module.finrank K (Φ.polar.perp (K ∙ w)) ≤ Module.finrank K (K ∙ w) :=
            Submodule.finrank_mono hle
        _ = 1 := finrank_span_singleton hw
    omega
  obtain ⟨c, hc, hcq⟩ := hex
  exact ⟨c, hcq, (ReflForm.mem_perp (F := Φ.polar)).mp hc w
    (Submodule.mem_span_singleton_self w)⟩

theorem w183PlusDecomp {r : ℕ} {K : Type} [Field K] (z : Fin (r + 1) ⊕ Fin (r + 1) → K) :
    z = w183PlusExt r K (fun p => z (Sum.map Fin.castSucc Fin.castSucc p)) +
        z (Sum.inl (Fin.last r)) • w183PlusX r K +
        z (Sum.inr (Fin.last r)) • w183PlusY r K := by
  ext i
  rcases i with i | i <;> induction i using Fin.lastCases with
  | last => simp [w183PlusExt, w183PlusX, w183PlusY, Pi.single_apply]
  | cast i => simp [w183PlusExt, w183PlusX, w183PlusY, Pi.single_apply]

theorem w183Qadd {r : ℕ} {K : Type} [Field K] (a b : Fin r ⊕ Fin r → K) :
    StatedQuadPlus r K (a + b) =
      StatedQuadPlus r K a + StatedQuadPlus r K b + quadPlusPolar r K a b :=
  (quadPlusForm r K).Q_add a b

theorem w183Padd {r : ℕ} {K : Type} [Field K] (a b c : Fin r ⊕ Fin r → K) :
    quadPlusPolar r K a (b + c) = quadPlusPolar r K a b + quadPlusPolar r K a c :=
  (quadPlusForm r K).polar.add_right a b c

theorem w183Pself {r : ℕ} {K : Type} [Field K] (h2 : (2 : K) = 0)
    (a : Fin r ⊕ Fin r → K) : quadPlusPolar r K a a = 0 := by
  have h : quadPlusPolar r K a a = 2 * StatedQuadPlus r K a :=
    QuadForm.polar_self (quadPlusForm r K) a
  rw [h, h2, zero_mul]

theorem w183Psymm {r : ℕ} {K : Type} [Field K] (a b : Fin r ⊕ Fin r → K) :
    quadPlusPolar r K a b = quadPlusPolar r K b a :=
  QuadForm.polar_symm (quadPlusForm r K) a b

theorem w183Qzero {r : ℕ} {K : Type} [Field K] :
    StatedQuadPlus r K (0 : Fin r ⊕ Fin r → K) = 0 :=
  (quadPlusForm r K).Q_zero

theorem w183PlusStep {K : Type} [Field K] (hK : ∀ c : K, c = 0 ∨ c = 1)
    {r : ℕ} (hr : 3 ≤ r) {S : Set (Fin r ⊕ Fin r → K)} (hne : S.Nonempty)
    (hS : ∀ v ∈ S, StatedQuadPlus r K v = 1)
    (hgen : w183Gen (StatedQuadPlus r K) (quadPlusPolar r K) S) :
    ∃ S' : Set (Fin (r + 1) ⊕ Fin (r + 1) → K), S'.ncard ≤ S.ncard + 2 ∧
      (∀ v ∈ S', StatedQuadPlus (r + 1) K v = 1) ∧
      w183Gen (StatedQuadPlus (r + 1) K) (quadPlusPolar (r + 1) K) S' := by
  classical
  obtain ⟨u₀, hu₀S⟩ := hne
  have h2 : (2 : K) = 0 := by
    rcases hK 2 with h | h
    · exact h
    · exfalso
      have h1 : (1 : K) = 0 := by
        have hh : (2 : K) = 1 + 1 := by norm_num
        rw [hh] at h
        have h' : (1 : K) + 1 = 1 + 0 := by rw [h, add_zero]
        exact add_left_cancel h'
      exact one_ne_zero h1
  have h11 : (1 : K) + 1 = 0 := by
    rw [← show (2 : K) = 1 + 1 by norm_num]; exact h2
  have hvvr : ∀ v : Fin r ⊕ Fin r → K, v + v = 0 := fun v => by
    rw [← two_smul K v, h2, zero_smul]
  have hvvR : ∀ v : Fin (r + 1) ⊕ Fin (r + 1) → K, v + v = 0 := fun v => by
    rw [← two_smul K v, h2, zero_smul]
  refine ⟨w183PlusExt r K '' S ∪
    ({w183PlusExt r K u₀ + w183PlusX r K, w183PlusX r K + w183PlusY r K} :
      Set (Fin (r + 1) ⊕ Fin (r + 1) → K)), ?_, ?_, ?_⟩
  · have hpair : Set.ncard ({w183PlusExt r K u₀ + w183PlusX r K,
        w183PlusX r K + w183PlusY r K} : Set (Fin (r + 1) ⊕ Fin (r + 1) → K)) ≤ 2 := by
      calc Set.ncard ({w183PlusExt r K u₀ + w183PlusX r K,
            w183PlusX r K + w183PlusY r K} : Set (Fin (r + 1) ⊕ Fin (r + 1) → K))
          = Set.ncard (insert (w183PlusExt r K u₀ + w183PlusX r K)
              ({w183PlusX r K + w183PlusY r K} : Set (Fin (r + 1) ⊕ Fin (r + 1) → K))) := rfl
        _ ≤ Set.ncard ({w183PlusX r K + w183PlusY r K} :
              Set (Fin (r + 1) ⊕ Fin (r + 1) → K)) + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    calc Set.ncard (w183PlusExt r K '' S ∪
            {w183PlusExt r K u₀ + w183PlusX r K, w183PlusX r K + w183PlusY r K})
        ≤ Set.ncard (w183PlusExt r K '' S) + Set.ncard
            ({w183PlusExt r K u₀ + w183PlusX r K, w183PlusX r K + w183PlusY r K} :
              Set (Fin (r + 1) ⊕ Fin (r + 1) → K)) := Set.ncard_union_le _ _
      _ = Set.ncard S + Set.ncard ({w183PlusExt r K u₀ + w183PlusX r K,
            w183PlusX r K + w183PlusY r K} : Set (Fin (r + 1) ⊕ Fin (r + 1) → K)) := by
            rw [Set.ncard_image_of_injective _ (w183PlusExt_injective r K)]
      _ ≤ Set.ncard S + 2 := by omega
  · intro v hv
    rcases hv with ⟨w, hw, rfl⟩ | hv
    · have h := w183PlusForm w 0 0
      simp only [zero_smul, add_zero, mul_zero] at h
      rw [h, hS w hw]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl
      · have h := w183PlusForm u₀ 1 0
        simp only [one_smul, zero_smul, add_zero, mul_zero] at h
        rw [h, hS u₀ hu₀S]
      · have h := w183PlusForm (r := r) (K := K) (0 : Fin r ⊕ Fin r → K) 1 1
        simp only [w183PlusExt_zero, zero_add, one_smul, mul_one] at h
        simpa [w183Qzero (r := r) (K := K)] using h
  · intro T hT hcl
    have hsub : S ⊆ {w | w183PlusExt r K w ∈ T} :=
      fun w hw => hT (Or.inl ⟨w, hw, rfl⟩)
    have hcl' : ∀ v ∈ {w | w183PlusExt r K w ∈ T},
        ∀ w ∈ {w | w183PlusExt r K w ∈ T},
        StatedQuadPlus r K v = 1 → StatedQuadPlus r K w = 1 →
        quadPlusPolar r K v w = 1 → v + w ∈ {w | w183PlusExt r K w ∈ T} := by
      intro v hv w hw qv qw hp
      change w183PlusExt r K (v + w) ∈ T
      rw [w183PlusExt_add]
      refine hcl (w183PlusExt r K v) hv (w183PlusExt r K w) hw ?_ ?_ ?_
      · have h := w183PlusForm v 0 0
        simp only [zero_smul, add_zero, mul_zero] at h
        rw [h, qv]
      · have h := w183PlusForm w 0 0
        simp only [zero_smul, add_zero, mul_zero] at h
        rw [h, qw]
      · have h := w183QuadPlusPolarExt v w
        rw [h, hp]
    have hNW : ∀ w, StatedQuadPlus r K w = 1 → w183PlusExt r K w ∈ T :=
      hgen {w | w183PlusExt r K w ∈ T} hsub hcl'
    have hfin : 5 ≤ Module.finrank K (Fin r ⊕ Fin r → K) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum]
      simp only [Fintype.card_fin]
      omega
    have hfin3 : 3 ≤ Module.finrank K (Fin r ⊕ Fin r → K) := by omega
    have hconn : ∀ u v, StatedQuadPlus r K u = 1 → StatedQuadPlus r K v = 1 → u ≠ v →
        quadPlusPolar r K u v = 1 ∨ ∃ w, StatedQuadPlus r K w = 1 ∧
          quadPlusPolar r K u w = 1 ∧ quadPlusPolar r K v w = 1 :=
      w183ConnQuadForm hK (quadPlusForm r K) hfin
    let A : Set (Fin r ⊕ Fin r → K) := {w | StatedQuadPlus r K w = 1 ∧
      w183PlusExt r K w + w183PlusX r K ∈ T}
    have hA_mem : u₀ ∈ A := ⟨hS u₀ hu₀S, hT (Or.inr (by simp))⟩
    have hA_closed : ∀ w ∈ A, ∀ w', StatedQuadPlus r K w' = 1 →
        quadPlusPolar r K w w' = 1 → w' ∈ A := by
      intro w hw w' hw' hp
      obtain ⟨hqw, hxw⟩ := hw
      refine ⟨hw', ?_⟩
      have ht : StatedQuadPlus r K (w + w') = 1 := by
        rw [w183Qadd w w', hqw, hw', hp, h11, zero_add]
      have htT : w183PlusExt r K (w + w') ∈ T := hNW (w + w') ht
      have hz : StatedQuadPlus (r + 1) K (w183PlusExt r K w + w183PlusX r K) = 1 := by
        have h := w183PlusForm w 1 0
        simp only [one_smul, zero_smul, add_zero, mul_zero] at h
        rw [h, hqw]
      have hzt : StatedQuadPlus (r + 1) K (w183PlusExt r K (w + w')) = 1 := by
        have h := w183PlusForm (w + w') 0 0
        simp only [zero_smul, add_zero, mul_zero] at h
        rw [h, ht]
      have hpv : quadPlusPolar (r + 1) K (w183PlusExt r K w + w183PlusX r K)
          (w183PlusExt r K (w + w')) = 1 := by
        rw [w183QuadPlusPolarXExt]
        rw [w183Padd w w w', w183Pself h2 w, zero_add, hp]
      have hres := hcl (w183PlusExt r K w + w183PlusX r K) hxw
        (w183PlusExt r K (w + w')) htT hz hzt hpv
      have hsum : (w183PlusExt r K w + w183PlusX r K) + w183PlusExt r K (w + w') =
          w183PlusExt r K w' + w183PlusX r K := by
        rw [show w183PlusExt r K w + w183PlusX r K + w183PlusExt r K (w + w') =
            w183PlusExt r K (w + (w + w')) + w183PlusX r K from by
          rw [show w183PlusExt r K (w + (w + w')) =
              w183PlusExt r K w + w183PlusExt r K (w + w') from w183PlusExt_add w (w + w')]
          abel]
        rw [show w + (w + w') = w' from by rw [← add_assoc, hvvr w, zero_add]]
      rwa [hsum] at hres
    have hN : ∀ w, StatedQuadPlus r K w = 1 → w ≠ u₀ →
        quadPlusPolar r K u₀ w = 1 ∨ ∃ b, StatedQuadPlus r K b = 1 ∧
          quadPlusPolar r K u₀ b = 1 ∧ quadPlusPolar r K b w = 1 := by
      intro w hw hwne
      rcases hconn u₀ w (hS u₀ hu₀S) hw (Ne.symm hwne) with h | ⟨b, hb, hb1, hb2⟩
      · exact Or.inl h
      · exact Or.inr ⟨b, hb, hb1, (w183Psymm b w) ▸ hb2⟩
    have hAall : ∀ w, StatedQuadPlus r K w = 1 → w ∈ A :=
      w183EqOfClosedAdj hA_mem hA_closed hN
    have hxT : ∀ w, StatedQuadPlus r K w = 1 →
        w183PlusX r K + w183PlusExt r K w ∈ T := by
      intro w hw
      have h := (hAall w hw).2
      simpa [add_comm] using h
    have hxy : w183PlusX r K + w183PlusY r K ∈ T := hT (Or.inr (by simp))
    have hyT : ∀ w, StatedQuadPlus r K w = 1 →
        w183PlusY r K + w183PlusExt r K w ∈ T := by
      intro w hw
      have hx := hxT w hw
      have h1 : StatedQuadPlus (r + 1) K (w183PlusX r K + w183PlusExt r K w) = 1 := by
        rw [show w183PlusX r K + w183PlusExt r K w = w183PlusExt r K w + w183PlusX r K
          from add_comm _ _]
        have h := w183PlusForm w 1 0
        simp only [one_smul, zero_smul, add_zero, mul_zero] at h
        rw [h, hw]
      have h2' : StatedQuadPlus (r + 1) K (w183PlusX r K + w183PlusY r K) = 1 := by
        have h := w183PlusForm (r := r) (K := K) (0 : Fin r ⊕ Fin r → K) 1 1
        simp only [w183PlusExt_zero, zero_add, one_smul, mul_one] at h
        simpa [w183Qzero (r := r) (K := K)] using h
      have hp : quadPlusPolar (r + 1) K (w183PlusX r K + w183PlusExt r K w)
          (w183PlusX r K + w183PlusY r K) = 1 := by
        rw [show w183PlusX r K + w183PlusExt r K w = w183PlusExt r K w + w183PlusX r K
          from add_comm _ _]
        exact w183QuadPlusPolarXY w
      have hres := hcl (w183PlusX r K + w183PlusExt r K w) hx
        (w183PlusX r K + w183PlusY r K) hxy h1 h2' hp
      have hsum : (w183PlusX r K + w183PlusExt r K w) + (w183PlusX r K + w183PlusY r K) =
          w183PlusY r K + w183PlusExt r K w := by
        calc (w183PlusX r K + w183PlusExt r K w) + (w183PlusX r K + w183PlusY r K)
            = (w183PlusX r K + w183PlusX r K) + (w183PlusExt r K w + w183PlusY r K) := by abel
          _ = 0 + (w183PlusExt r K w + w183PlusY r K) := by rw [hvvR (w183PlusX r K)]
          _ = w183PlusY r K + w183PlusExt r K w := by rw [zero_add]; exact add_comm _ _
      rwa [hsum] at hres
    have hsingT : ∀ w, StatedQuadPlus r K w = 0 →
        w183PlusX r K + w183PlusY r K + w183PlusExt r K w ∈ T := by
      intro w hw0
      by_cases hw : w = 0
      · subst hw; rw [w183PlusExt_zero, add_zero]; exact hxy
      · obtain ⟨w₁, hw₁q, hw₁p⟩ :=
          w183ExistsNormOnePerp hK (quadPlusForm r K) hfin3 hw
        have hw₁ : StatedQuadPlus r K w₁ = 1 := hw₁q
        have hw₁p' : quadPlusPolar r K w w₁ = 0 := hw₁p
        have hw₂ : StatedQuadPlus r K (w + w₁) = 1 := by
          rw [w183Qadd w w₁, hw0, hw₁, hw₁p', zero_add, add_zero]
        have hp12 : quadPlusPolar r K w₁ (w + w₁) = 0 := by
          rw [w183Padd w₁ w w₁]
          rw [w183Psymm w₁ w, hw₁p', w183Pself h2 w₁, add_zero]
        have h1 : StatedQuadPlus (r + 1) K (w183PlusX r K + w183PlusExt r K w₁) = 1 := by
          rw [show w183PlusX r K + w183PlusExt r K w₁ = w183PlusExt r K w₁ + w183PlusX r K
            from add_comm _ _]
          have h := w183PlusForm w₁ 1 0
          simp only [one_smul, zero_smul, add_zero, mul_zero] at h
          rw [h, hw₁]
        have h2' : StatedQuadPlus (r + 1) K
            (w183PlusY r K + w183PlusExt r K (w + w₁)) = 1 := by
          rw [show w183PlusY r K + w183PlusExt r K (w + w₁) =
            w183PlusExt r K (w + w₁) + w183PlusY r K from add_comm _ _]
          have h := w183PlusForm (w + w₁) 0 1
          simp only [one_smul, zero_smul, add_zero, zero_mul, mul_zero] at h
          rw [h, hw₂]
        have hp : quadPlusPolar (r + 1) K (w183PlusX r K + w183PlusExt r K w₁)
            (w183PlusY r K + w183PlusExt r K (w + w₁)) = 1 := by
          rw [show w183PlusX r K + w183PlusExt r K w₁ = w183PlusExt r K w₁ + w183PlusX r K
            from add_comm _ _]
          rw [show w183PlusY r K + w183PlusExt r K (w + w₁) =
            w183PlusExt r K (w + w₁) + w183PlusY r K from add_comm _ _]
          rw [w183QuadPlusPolarYX, hp12, zero_add]
        have hres := hcl (w183PlusX r K + w183PlusExt r K w₁) (hxT w₁ hw₁)
          (w183PlusY r K + w183PlusExt r K (w + w₁)) (hyT (w + w₁) hw₂)
          h1 h2' hp
        have hsum : (w183PlusX r K + w183PlusExt r K w₁) +
            (w183PlusY r K + w183PlusExt r K (w + w₁)) =
            w183PlusX r K + w183PlusY r K + w183PlusExt r K w := by
          rw [show (w183PlusX r K + w183PlusExt r K w₁) +
              (w183PlusY r K + w183PlusExt r K (w + w₁)) =
              w183PlusX r K + w183PlusY r K + w183PlusExt r K (w₁ + (w + w₁)) from by
            rw [show w183PlusExt r K (w₁ + (w + w₁)) =
                w183PlusExt r K w₁ + w183PlusExt r K (w + w₁) from w183PlusExt_add w₁ (w + w₁)]
            abel]
          rw [show w₁ + (w + w₁) = w from by
            rw [add_comm w₁ (w + w₁), add_assoc, hvvr w₁, add_zero]]
        rwa [hsum] at hres
    intro z hz
    have hzdecomp : z = w183PlusExt r K (fun p => z (Sum.map Fin.castSucc Fin.castSucc p)) +
        z (Sum.inl (Fin.last r)) • w183PlusX r K +
        z (Sum.inr (Fin.last r)) • w183PlusY r K := w183PlusDecomp z
    have hQz : StatedQuadPlus r K (fun p => z (Sum.map Fin.castSucc Fin.castSucc p)) +
        z (Sum.inl (Fin.last r)) * z (Sum.inr (Fin.last r)) = 1 := by
      have h := w183PlusForm (fun p => z (Sum.map Fin.castSucc Fin.castSucc p))
        (z (Sum.inl (Fin.last r))) (z (Sum.inr (Fin.last r)))
      rw [← hzdecomp] at h
      exact h.symm.trans hz
    rw [hzdecomp]
    rcases hK (z (Sum.inl (Fin.last r))) with hα | hα <;>
      rcases hK (z (Sum.inr (Fin.last r))) with hβ | hβ
    · rw [hα, hβ] at hQz
      rw [hα, hβ]
      simp only [zero_smul, add_zero, mul_zero] at hQz ⊢
      exact hNW _ (by simpa using hQz)
    · rw [hα, hβ] at hQz
      rw [hα, hβ]
      simp only [zero_smul, add_zero, one_smul, mul_zero] at hQz ⊢
      rw [show w183PlusExt r K (fun p => z (Sum.map Fin.castSucc Fin.castSucc p)) +
          w183PlusY r K = w183PlusY r K +
          w183PlusExt r K (fun p => z (Sum.map Fin.castSucc Fin.castSucc p)) from add_comm _ _]
      exact hyT _ (by simpa using hQz)
    · rw [hα, hβ] at hQz
      rw [hα, hβ]
      simp only [zero_smul, add_zero, one_smul, mul_zero] at hQz ⊢
      rw [show w183PlusExt r K (fun p => z (Sum.map Fin.castSucc Fin.castSucc p)) +
          w183PlusX r K = w183PlusX r K +
          w183PlusExt r K (fun p => z (Sum.map Fin.castSucc Fin.castSucc p)) from add_comm _ _]
      exact hxT _ (by simpa using hQz)
    · rw [hα, hβ] at hQz
      rw [hα, hβ]
      simp only [one_smul, mul_one] at hQz ⊢
      have hw : StatedQuadPlus r K (fun p => z (Sum.map Fin.castSucc Fin.castSucc p)) = 0 := by
        exact add_right_cancel (by rw [hQz, zero_add])
      simpa [add_comm, add_left_comm, add_assoc] using hsingT _ hw

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
