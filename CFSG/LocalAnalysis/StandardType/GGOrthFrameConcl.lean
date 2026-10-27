module

public import CFSG.LocalAnalysis.StandardType.GGOrthFrameRefl
public import CFSG.LocalAnalysis.StandardType.GGOrthModelInputs
public import CFSG.LocalAnalysis.StandardType.GGNSJoinOutWeakPosDefs
public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylEltOfAutomizer
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj

public section

open Module Multiplicative QuadraticMap

namespace CFSG.StandardType

open CFSG.Assembly

section Concl


theorem ggLabel_n_eq_of_D (hRig : GGLabelRigidInput) {R : Type} [Group R] {b f : ℕ} (hb : 4 ≤ b)
    (hf : 1 ≤ f) (hl : GGHasLabel ⟨.D, b, f⟩ R) {lab' : LargeEvenLabel}
    (hlam' : LargeEvenInLambda2 lab') (hl' : GGHasLabel lab' R) : lab'.n = f := by
  have hlam : LargeEvenInLambda2 (⟨.D, b, f⟩ : LargeEvenLabel) := ⟨hf, show 3 ≤ b by omega⟩
  rcases hRig _ _ R hlam hlam' hl hl' with h | h | h | h | h | h | h | h <;>
    first
    | (subst h; rfl)
    | (exfalso; simp at h; done)
    | (exfalso; simp at h; omega)
    | (obtain ⟨-, h2⟩ := h; subst h2; rfl)

theorem ggLabel_n_eq_of_twD (hRig : GGLabelRigidInput) {R : Type} [Group R] {b f : ℕ} (hb : 4 ≤ b)
    (hf : 1 ≤ f) (hl : GGHasLabel ⟨.twD, b, f⟩ R) {lab' : LargeEvenLabel}
    (hlam' : LargeEvenInLambda2 lab') (hl' : GGHasLabel lab' R) : lab'.n = f := by
  have hlam : LargeEvenInLambda2 (⟨.twD, b, f⟩ : LargeEvenLabel) := ⟨hf, show 2 ≤ b by omega⟩
  rcases hRig _ _ R hlam hlam' hl hl' with h | h | h | h | h | h | h | h <;>
    first
    | (subst h; rfl)
    | (exfalso; simp at h; done)
    | (exfalso; simp at h; omega)
    | (obtain ⟨-, h2⟩ := h; subst h2; rfl)

theorem ggRk1Concl_conj {p : ℕ} {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    {r a : MulAut ↥Bs} (hr : GGRk1Concl p Bs X r) (ha : a ∈ ggAutomizer X Bs) :
    GGRk1Concl p Bs X (a * r * a⁻¹) := by
  obtain ⟨F, hF, hFin, θ, hchar, hinj, hrange, ⟨n, hnS, hnN, hnact⟩, hsplit, hnsplit, hlab⟩ := hr
  obtain ⟨g, hgX, hgN, hg⟩ := mem_ggAutomizer_iff.mp ha
  have hX : X.map (MulAut.conj g).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgX)
  have hconj : (ggRankOneIn X Bs r).map (MulAut.conj g).toMonoidHom =
      ggRankOneIn X Bs (a * r * a⁻¹) := by
    have h := ggRankOneIn_map_conj (X := X) hg r
    rwa [hX] at h
  refine ⟨F, hF, hFin, (MulAut.conj g).toMonoidHom.comp θ, hchar, ?_, ?_,
    ⟨g * n * g⁻¹, ?_, ?_, ?_⟩, hsplit, hnsplit, hlab⟩
  · exact (MulAut.conj g).injective.comp hinj
  · rw [MonoidHom.range_comp, hrange, hconj]
  · rw [← hconj]
    exact Subgroup.mem_map.mpr ⟨n, hnS, by simp [MulAut.conj_apply]⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hnN) (Subgroup.inv_mem _ hgN)
  · intro b
    have h1 := hg (r (a⁻¹ b))
    have h2 := hnact (a⁻¹ b)
    have h3 := inv_apply_of_forall hg b
    show ((a (r (a⁻¹ b)) : ↥Bs) : G) = g * n * g⁻¹ * b * (g * n * g⁻¹)⁻¹
    rw [h1, h2, h3]
    group


namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ClassicalInvolution.Phan

theorem OrthWeakFrame.rk1_swap (hRig : GGLabelRigidInput) (hM2 : OrthRankOneModelInput) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (Φ : OrthWeakFrame p Bs X) (hΦ : Φ.Recognized) (hXns : ¬ GGSplitLie p X) {i j : Fin Φ.r}
    (hij : i ≠ j) : ∃ a ∈ ggAutomizer X Bs, GGIsReflection p a ∧ GGRk1Concl p Bs X a := by
  obtain ⟨a, haA, haR, haS⟩ := Φ.exists_swap_refl hij
  have hr3 : 3 ≤ Φ.r := by have := Φ.hr; omega
  have hq : 4 ≤ Nat.card Φ.F := by
    rw [Φ.hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ Φ.f := Nat.pow_le_pow_right (by norm_num) Φ.hf
  obtain ⟨⟨θm, hθinj, hθrange, -⟩, -⟩ :=
    hM2 Φ.F Φ.V Φ.Q p hp2 Φ.A Φ.hA Φ.r Φ.Δ hr3 hq Φ.hfix i j hij
  have hθΩ : ∀ x, θm x ∈ orthDerived Φ.Q := by
    intro x
    have hx : θm x ∈ θm.range := ⟨x, rfl⟩
    rw [hθrange] at hx
    exact (ggOTwoPrime_le _ hx).2
  let θΩ : Matrix.SpecialLinearGroup (Fin 2) Φ.F →* ↥(orthDerived Φ.Q) :=
    θm.codRestrict (orthDerived Φ.Q) hθΩ
  let θ : Matrix.SpecialLinearGroup (Fin 2) Φ.F →* G := Φ.ψ.comp θΩ
  have hθΩinj : Function.Injective θΩ := fun x y h => hθinj (congrArg Subtype.val h)
  have hΩrange : θΩ.range = (Φ.Δ.rankOne i j).subgroupOf (orthDerived Φ.Q) := by
    ext y
    rw [Subgroup.mem_subgroupOf, ← hθrange]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
  have hrange : θ.range = ggRankOneIn X Bs a := by
    rw [haS]
    change (Φ.ψ.comp θΩ).range = _
    rw [MonoidHom.range_comp, hΩrange]
  refine ⟨a, haA, haR, Φ.F, inferInstance, inferInstance, θ, inferInstance, ?_, hrange, ?_, ?_, ?_, ?_⟩
  · exact Φ.hinj.comp hθΩinj
  · have hr2 : a * a = 1 := by simpa [pow_two] using haR.1
    exact ggExists_weylElt_of_mem_ggAutomizer haA hr2
  · intro hs
    exact absurd hs hXns
  · intro _
    exact Φ.hpq
  · intro lab' hlam' hl'
    have hf1 : 1 ≤ Φ.f := by have := Φ.hf; omega
    have hnn : lab'.n = Φ.f := by
      rcases hΦ.2.2 with ⟨_, hl⟩ | ⟨_, hl⟩
      · exact ggLabel_n_eq_of_D hRig Φ.hr hf1 hl hlam' hl'
      · exact ggLabel_n_eq_of_twD hRig Φ.hr hf1 hl hlam' hl'
    rw [hnn, Φ.hcard]

theorem OrthWeakFrame.le_iSup_rankOne {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hD : PhanDInput2)
    (hM2 : OrthRankOneModelInput) (hM4 : OrthPairModelInput) (hM5 : OrthGenModelInput)
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G} (Φ : OrthWeakFrame p Bs X)
    (hΦ : Φ.Recognized) :
    X ≤ ⨆ r : MulAut ↥Bs, ⨆ (_ : r ∈ ggAutomizer X Bs), ⨆ (_ : GGIsReflection p r),
      ggRankOneIn X Bs r := by
  set T : Subgroup G := ⨆ r : MulAut ↥Bs, ⨆ (_ : r ∈ ggAutomizer X Bs), ⨆ (_ : GGIsReflection p r),
    ggRankOneIn X Bs r with hT
  have hle : ∀ a ∈ ggAutomizer X Bs, GGIsReflection p a → ggRankOneIn X Bs a ≤ T := by
    intro a ha hr
    exact (le_iSup (fun (_ : GGIsReflection p a) => ggRankOneIn X Bs a) hr).trans
      ((le_iSup (fun (_ : a ∈ ggAutomizer X Bs) =>
          ⨆ (_ : GGIsReflection p a), ggRankOneIn X Bs a) ha).trans
        (le_iSup (fun r => ⨆ (_ : r ∈ ggAutomizer X Bs), ⨆ (_ : GGIsReflection p r),
          ggRankOneIn X Bs r) a))
  have hr3 : 3 ≤ Φ.r := by have := Φ.hr; omega
  have hq : 4 ≤ Nat.card Φ.F := by
    rw [Φ.hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ Φ.f := Nat.pow_le_pow_right (by norm_num) Φ.hf
  have hK' : Nat.card (GaloisField 2 (2 * Φ.f)) = (2 ^ Φ.f) ^ 2 := by
    rw [GaloisField.card 2 (2 * Φ.f) (by have := Φ.hf; omega), ← pow_mul, mul_comm]
  have h2 := hM2 Φ.F Φ.V Φ.Q p hp2 Φ.A Φ.hA Φ.r Φ.Δ hr3 hq Φ.hfix
  have h4 := hM4 Φ.F Φ.V Φ.Q p hp2 Φ.A Φ.hA Φ.r Φ.Δ hr3 Φ.hpq Φ.hfix Φ.f Φ.hcard
    (GaloisField 2 (2 * Φ.f)) hK'
  have hgen := hM5 hD Φ.F Φ.V Φ.Q p hp2 Φ.A Φ.hA Φ.r Φ.Δ Φ.hr hq Φ.hpq Φ.hfix Φ.f Φ.hcard
    (GaloisField 2 (2 * Φ.f)) hK' h2 h4 hΦ.1 hΦ.2.1
  set P : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V) := (T.comap Φ.ψ).map (orthDerived Φ.Q).subtype with hP
  have hΩP : orthDerived Φ.Q ≤ P := by
    rw [← hgen]
    refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => sup_le ?_ ?_
    · intro x hx
      obtain ⟨a, haA, haR, haS⟩ := Φ.exists_swap_refl hij
      have hxΩ : x ∈ orthDerived Φ.Q := (ggOTwoPrime_le _ hx).2
      refine ⟨⟨x, hxΩ⟩, ?_, rfl⟩
      have hmem : Φ.ψ ⟨x, hxΩ⟩ ∈ ggRankOneIn X Bs a := by
        rw [haS]
        exact ⟨⟨x, hxΩ⟩, by simpa [Subgroup.mem_subgroupOf] using hx, rfl⟩
      exact hle a haA haR hmem
    · intro x hx
      obtain ⟨a, haA, haR, haS⟩ := Φ.exists_pos_refl hij
      have hxΩ : x ∈ orthDerived Φ.Q := (ggOTwoPrime_le _ hx).2
      refine ⟨⟨x, hxΩ⟩, ?_, rfl⟩
      have hmem : Φ.ψ ⟨x, hxΩ⟩ ∈ ggRankOneIn X Bs a := by
        rw [haS]
        exact ⟨⟨x, hxΩ⟩, by simpa [Subgroup.mem_subgroupOf] using hx, rfl⟩
      exact hle a haA haR hmem
  intro z hz
  rw [← Φ.hrange] at hz
  obtain ⟨y, rfl⟩ := hz
  obtain ⟨y', hy', hyy⟩ := hΩP y.2
  have hy'y : y' = y := Subtype.ext hyy
  rw [hy'y] at hy'
  exact hy'

end OrthTorus

end Concl

end CFSG.StandardType

end
