module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.SignalizerFunctorTheorem

namespace Diagonal

variable {H : Type*} [Group H]

@[expose] def conjHom (T : Subgroup H) (g : H) : T →* H :=
  (MulAut.conj g).toMonoidHom.comp T.subtype

@[simp] theorem conjHom_apply (T : Subgroup H) (g : H) (t : T) :
    conjHom T g t = g * t * g⁻¹ := rfl

theorem conjHom_injective (T : Subgroup H) (g : H) : Function.Injective (conjHom T g) := by
  intro x y h
  apply Subtype.ext
  simpa using h

theorem conj_mem_range {N T : Subgroup H} [N.Normal] (hTnorm : ∀ n ∈ N, ∀ t ∈ T, n * t * n⁻¹ ∈ T)
    (g : H) {n : H} (hn : n ∈ N) {x : H} (hx : x ∈ (conjHom T g).range) :
    n * x * n⁻¹ ∈ (conjHom T g).range := by
  obtain ⟨⟨t, ht⟩, rfl⟩ := hx
  have hgn : g⁻¹ * n * g ∈ N := by simpa using ‹N.Normal›.conj_mem n hn g⁻¹
  refine ⟨⟨(g⁻¹ * n * g) * t * (g⁻¹ * n * g)⁻¹, hTnorm _ hgn t ht⟩, ?_⟩
  simp only [conjHom_apply, mul_inv_rev, inv_inv]
  group

theorem range_conjHom_ne {T : Subgroup H} {g g' : H}
    (h : g⁻¹ * g' ∉ Subgroup.normalizer (T : Set H)) :
    (conjHom T g).range ≠ (conjHom T g').range := by
  intro heq
  apply h
  rw [Subgroup.mem_set_normalizer_iff]
  intro t
  constructor
  · intro ht
    have h1 : g' * t * g'⁻¹ ∈ (conjHom T g).range := heq ▸ ⟨⟨t, ht⟩, rfl⟩
    obtain ⟨s, hs⟩ := h1
    have : g⁻¹ * g' * t * (g⁻¹ * g')⁻¹ = s := by
      simp only [conjHom_apply] at hs
      calc g⁻¹ * g' * t * (g⁻¹ * g')⁻¹ = g⁻¹ * (g' * t * g'⁻¹) * g := by group
        _ = s := by rw [← hs]; group
    rw [this]
    exact s.2
  · intro ht
    have h1 : g' * t * g'⁻¹ ∈ (conjHom T g).range :=
      ⟨⟨g⁻¹ * g' * t * (g⁻¹ * g')⁻¹, ht⟩, by simp only [conjHom_apply]; group⟩
    rw [heq] at h1
    obtain ⟨s, hs⟩ := h1
    have : (s : H) = t := by
      simp only [conjHom_apply] at hs
      simpa using hs
    rw [← this]
    exact s.2

theorem center_eq_bot {T : Type*} [Group T] [IsSimpleGroup T] (h : ∃ x y : T, x * y ≠ y * x) :
    Subgroup.center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h' | h'
  · exact h'
  · obtain ⟨x, y, hxy⟩ := h
    have hx : x ∈ Subgroup.center T := by rw [h']; trivial
    exact absurd ((Subgroup.mem_center_iff.mp hx) y).symm hxy

theorem disjoint_range_centralizer {T : Type*} [Group T] [IsSimpleGroup T]
    (h : ∃ x y : T, x * y ≠ y * x) {ψ : T →* H} (hψ : Function.Injective ψ) :
    Disjoint ψ.range (Subgroup.centralizer (ψ.range : Set H)) := by
  rw [Subgroup.disjoint_def]
  rintro _ ⟨t, rfl⟩ hc
  have ht : t ∈ Subgroup.center T := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply hψ
    rw [map_mul, map_mul]
    exact (Subgroup.mem_centralizer_iff.mp hc (ψ s) ⟨s, rfl⟩)
  rw [center_eq_bot h, Subgroup.mem_bot] at ht
  rw [ht, map_one]

theorem commute_of_ne_range {T : Type*} [Group T] [Finite T] [IsSimpleGroup T] {N : Subgroup H}
    {ψ₁ ψ₂ : T →* H} (h₁ : Function.Injective ψ₁) (h₂ : Function.Injective ψ₂)
    (hN₁ : ∀ x, ψ₁ x ∈ N) (hN₂ : ∀ x, ψ₂ x ∈ N)
    (hn₁ : ∀ n ∈ N, ∀ x ∈ ψ₁.range, n * x * n⁻¹ ∈ ψ₁.range)
    (hn₂ : ∀ n ∈ N, ∀ x ∈ ψ₂.range, n * x * n⁻¹ ∈ ψ₂.range)
    (hne : ψ₁.range ≠ ψ₂.range) (x y : T) : Commute (ψ₁ x) (ψ₂ y) := by
  have : Finite ψ₂.range := Finite.of_surjective _ ψ₂.rangeRestrict_surjective
  let S : Subgroup T := ψ₂.range.comap ψ₁
  have hS : S.Normal := ⟨fun s hs t => by
    show ψ₁ (t * s * t⁻¹) ∈ ψ₂.range
    rw [map_mul, map_mul, map_inv]
    exact hn₂ _ (hN₁ t) _ hs⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S with hbot | htop
  · have hc₂ : ψ₁ x * ψ₂ y * (ψ₁ x)⁻¹ * (ψ₂ y)⁻¹ ∈ ψ₂.range :=
      mul_mem (hn₂ _ (hN₁ x) _ ⟨y, rfl⟩) (inv_mem ⟨y, rfl⟩)
    have hc₁ : ψ₁ x * ψ₂ y * (ψ₁ x)⁻¹ * (ψ₂ y)⁻¹ ∈ ψ₁.range := by
      have h := mul_mem (⟨x, rfl⟩ : ψ₁ x ∈ ψ₁.range)
        (hn₁ _ (hN₂ y) _ (inv_mem (⟨x, rfl⟩ : ψ₁ x ∈ ψ₁.range)))
      simpa [mul_assoc] using h
    obtain ⟨u, hu⟩ := hc₁
    have hu1 : u ∈ S := by
      show ψ₁ u ∈ ψ₂.range
      rw [hu]
      exact hc₂
    rw [hbot, Subgroup.mem_bot] at hu1
    subst hu1
    rw [map_one] at hu
    have h := hu.symm
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
    exact h
  · exfalso
    apply hne
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨t, rfl⟩
      have ht : t ∈ S := by rw [htop]; trivial
      exact ht
    · rw [← Nat.card_congr (MonoidHom.ofInjective h₁).toEquiv,
        ← Nat.card_congr (MonoidHom.ofInjective h₂).toEquiv]

theorem exists_noncommPiCoprod {ι : Type*} [Fintype ι] [DecidableEq ι] {T : Type*} [Group T]
    [IsSimpleGroup T] {N : Subgroup H} (ψ : ι → T →* H) (hψinj : ∀ g, Function.Injective (ψ g))
    (hψN : ∀ g x, ψ g x ∈ N) (hcomm : Pairwise fun g g' => ∀ x y : T, Commute (ψ g x) (ψ g' y))
    (hTnc : ∃ x y : T, x * y ≠ y * x) :
    ∃ E : (ι → T) →* H, (∀ (g : ι) (t : T), E (Pi.mulSingle g t) = ψ g t) ∧ (∀ x, E x ∈ N) ∧
      Function.Injective E := by
  refine ⟨MonoidHom.noncommPiCoprod ψ hcomm, fun g t => MonoidHom.noncommPiCoprod_mulSingle ψ g t,
    fun x => ?_, ?_⟩
  · have hx : MonoidHom.noncommPiCoprod ψ hcomm x ∈ (MonoidHom.noncommPiCoprod ψ hcomm).range :=
      ⟨x, rfl⟩
    rw [MonoidHom.noncommPiCoprod_range] at hx
    refine (iSup_le (fun g => ?_) : _ ≤ N) hx
    rintro _ ⟨t, rfl⟩
    exact hψN g t
  · refine MonoidHom.injective_noncommPiCoprod_of_iSupIndep ψ ?_ hψinj
    intro g
    refine Disjoint.mono_right ?_ (disjoint_range_centralizer hTnc (hψinj g))
    refine iSup₂_le fun g' hg' => ?_
    rintro _ ⟨y, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, rfl⟩
    exact hcomm hg'.symm x y

theorem exists_diagonal_of_conj_ne [Finite H] {a : H} {K : Subgroup H} (ha : a ∈ K)
    {N T : Subgroup H} [N.Normal] (hTN : T ≤ N)
    (hTnorm : ∀ n ∈ N, ∀ t ∈ T, n * t * n⁻¹ ∈ T) [IsSimpleGroup T]
    (hTnc : ∃ x y : T, x * y ≠ y * x)
    (hne : ∀ g g' : K, g ≠ g' → (conjHom T (g : H)).range ≠ (conjHom T (g' : H)).range) :
    ∃ φ : T →* H, Function.Injective φ ∧ (∀ t, φ t ∈ N) ∧ ∀ t, a * φ t * a⁻¹ = φ t := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hψN : ∀ (g : K) (x : T), conjHom T (g : H) x ∈ N := fun g x =>
    ‹N.Normal›.conj_mem _ (hTN x.2) _
  have hcomm : Pairwise fun g g' : K => ∀ x y : T,
      Commute (conjHom T (g : H) x) (conjHom T (g' : H) y) := fun g g' hgg' x y =>
    commute_of_ne_range (conjHom_injective T _) (conjHom_injective T _) (hψN g) (hψN g')
      (fun _ hn _ hx => conj_mem_range hTnorm _ hn hx)
      (fun _ hn _ hx => conj_mem_range hTnorm _ hn hx) (hne g g' hgg') x y
  obtain ⟨E, hEψ, hEN, hEinj⟩ := exists_noncommPiCoprod (fun g : K => conjHom T (g : H))
    (fun g => conjHom_injective T _) hψN hcomm hTnc
  obtain ⟨a', ha'⟩ : ∃ a' : K, (a' : H) = a := ⟨⟨a, ha⟩, rfl⟩
  let σ : (K → T) →* (K → T) :=
    MonoidHom.pi fun h => Pi.evalMonoidHom (fun _ : K => (T : Type _)) (a'⁻¹ * h)
  have hσ : ∀ x h, σ x h = x (a'⁻¹ * h) := fun x h => rfl
  have key : (MulAut.conj a).toMonoidHom.comp E = E.comp σ := by
    apply MonoidHom.pi_ext
    intro g t
    have hσ' : σ (Pi.mulSingle g t) = Pi.mulSingle (a' * g) t := by
      ext h
      rw [hσ]
      by_cases hh : h = a' * g
      · subst hh
        simp
      · have : a'⁻¹ * h ≠ g := fun h' => hh (by rw [← h']; group)
        rw [Pi.mulSingle_eq_of_ne this, Pi.mulSingle_eq_of_ne hh]
    simp only [MonoidHom.comp_apply, hσ', hEψ]
    simp [ha']
    group
  refine ⟨E.comp (Pi.constMonoidHom K T), hEinj.comp ?_, fun t => hEN _, fun t => ?_⟩
  · intro x y hxy
    exact congr_fun hxy 1
  · have h1 : a * E (Pi.constMonoidHom K T t) * a⁻¹ = E (σ (Pi.constMonoidHom K T t)) :=
      DFunLike.congr_fun key (Pi.constMonoidHom K T t)
    exact h1

end Diagonal

theorem exists_diagonal {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime) {a : H}
    (ha : a ^ p = 1) {N T : Subgroup H} [N.Normal] (hTN : T ≤ N)
    (hTnorm : ∀ n ∈ N, ∀ t ∈ T, n * t * n⁻¹ ∈ T) [IsSimpleGroup T]
    (hTnc : ∃ x y : T, x * y ≠ y * x) (hmove : a ∉ Subgroup.normalizer (T : Set H)) :
    ∃ φ : T →* H, Function.Injective φ ∧ (∀ t, φ t ∈ N) ∧ ∀ t, a * φ t * a⁻¹ = φ t := by
  have : Fact p.Prime := ⟨hp⟩
  have ha1 : a ≠ 1 := fun h => hmove (h ▸ one_mem _)
  have hord : orderOf a = p := orderOf_eq_prime ha ha1
  refine Diagonal.exists_diagonal_of_conj_ne (Subgroup.mem_zpowers a) hTN hTnorm hTnc ?_
  intro g g' hgg'
  apply Diagonal.range_conjHom_ne
  intro hmem
  have hu : (g : H)⁻¹ * g' ∈ Subgroup.zpowers a :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ g.2) g'.2
  have hu1 : (g : H)⁻¹ * g' ≠ 1 := fun h => hgg' (Subtype.ext (inv_mul_eq_one.mp h))
  have hordu : orderOf ((g : H)⁻¹ * g') = p := by
    rcases (Nat.dvd_prime hp).mp (hord ▸ orderOf_dvd_of_mem_zpowers hu) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hu1
    · exact h
  have hzeq : Subgroup.zpowers ((g : H)⁻¹ * g') = Subgroup.zpowers a :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hu)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hordu])
  apply hmove
  have : a ∈ Subgroup.zpowers ((g : H)⁻¹ * g') := by
    rw [hzeq]
    exact Subgroup.mem_zpowers a
  exact Subgroup.zpowers_le.mpr hmem this

end CFSG.SignalizerFunctorTheorem
