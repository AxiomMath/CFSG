module

public import CFSG.GroupTheory.LocalCores.Components
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

namespace CFSG.Quasithin.S151S5

open scoped Pointwise

theorem mem_mul_of_le_normalizer {Γ : Type*} [Group Γ] {A B : Subgroup Γ}
    (hB : B ≤ Subgroup.normalizer (A : Set Γ)) {x : Γ} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have h : ((A ⊔ B : Subgroup Γ) : Set Γ) = (A : Set Γ) * (B : Set Γ) :=
    Subgroup.coe_mul_of_right_le_normalizer_left A B hB
  have hx' : x ∈ ((A ⊔ B : Subgroup Γ) : Set Γ) := hx
  rw [h] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem mul_pow_mem_of_mem_normalizer {Γ : Type*} [Group Γ] {N : Subgroup Γ} {p s : Γ}
    (hs : s ∈ Subgroup.normalizer (N : Set Γ)) (hp : p ∈ N) (n : ℕ) :
    ∃ q ∈ N, (p * s) ^ n = q * s ^ n := by
  induction n with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨q, hq, hqe⟩ := ih
    have hsn : s ^ n ∈ Subgroup.normalizer (N : Set Γ) := Subgroup.pow_mem _ hs n
    have h1 : s ^ n * p * (s ^ n)⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hsn p).mp hp
    refine ⟨q * (s ^ n * p * (s ^ n)⁻¹), N.mul_mem hq h1, ?_⟩
    rw [pow_succ, hqe, pow_succ]
    group

theorem pCore_two_quotient_eq_bot {X : Type*} [Group X] :
    CFSG.pCore 2 (X ⧸ CFSG.pCore 2 X) = ⊥ := by
  set Q := CFSG.pCore 2 X with hQdef
  set W := CFSG.pCore 2 (X ⧸ Q) with hWdef
  have hW : IsPGroup 2 W := CFSG.pCore_isPGroup
  have hQ : IsPGroup 2 Q := CFSG.pCore_isPGroup
  have hker : IsPGroup 2 (QuotientGroup.mk' Q).ker := by
    rw [QuotientGroup.ker_mk']
    exact hQ
  have hc : IsPGroup 2 (W.comap (QuotientGroup.mk' Q)) := hW.comap_of_ker_isPGroup _ hker
  have hn : (W.comap (QuotientGroup.mk' Q)).Normal := (CFSG.pCore_normal (p := 2) (G := X ⧸ Q)).comap _
  have hle : W.comap (QuotientGroup.mk' Q) ≤ Q := le_sSup ⟨hn, hc⟩
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
  have hx : x ∈ W.comap (QuotientGroup.mk' Q) := hw
  have := hle hx
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff x).mpr this

theorem eq_one_of_central_of_commuting_simple {Γ : Type*} [Group Γ]
    (F : Finset (Subgroup Γ))
    (hz : ∀ J ∈ F, ∀ x ∈ J, (∀ y ∈ J, y * x = x * y) → x = 1)
    (hc : ∀ J ∈ F, ∀ J' ∈ F, J ≠ J' → ∀ a ∈ J, ∀ b ∈ J', a * b = b * a)
    {z : Γ} (hzK : z ∈ F.sup id) (hcen : ∀ k ∈ F.sup id, z * k = k * z) : z = 1 := by
  classical
  induction F using Finset.induction_on generalizing z with
  | empty =>
    simp only [Finset.sup_empty] at hzK
    exact Subgroup.mem_bot.mp hzK
  | insert J F₀ hJ ih =>
    rw [Finset.sup_insert] at hzK hcen
    simp only [id] at hzK hcen
    have hle : F₀.sup id ≤ Subgroup.centralizer (J : Set Γ) := by
      refine Finset.sup_le fun J' hJ' b hb => ?_
      have hne : J ≠ J' := fun h => hJ (h ▸ hJ')
      exact Subgroup.mem_centralizer_iff.mpr fun a' ha' =>
        hc J (Finset.mem_insert_self J F₀) J' (Finset.mem_insert_of_mem hJ') hne a' ha' b hb
    have hJF₀ : ∀ a ∈ J, ∀ k ∈ F₀.sup id, a * k = k * a := fun a ha k hk =>
      Subgroup.mem_centralizer_iff.mp (hle hk) a ha
    have hBN : F₀.sup id ≤ Subgroup.normalizer (J : Set Γ) :=
      hle.trans (Subgroup.centralizer_le_normalizer _)
    obtain ⟨a, ha, k, hk, rfl⟩ := mem_mul_of_le_normalizer hBN hzK
    have ha1 : a = 1 := by
      refine hz J (Finset.mem_insert_self J F₀) a ha fun y hy => ?_
      have h1 := hcen y (Subgroup.mem_sup_left hy)
      have h2 : k * y = y * k := (hJF₀ y hy k hk).symm
      have h3 : a * y * k = y * a * k := by
        calc a * y * k = a * (y * k) := by rw [mul_assoc]
          _ = a * (k * y) := by rw [← hJF₀ y hy k hk]
          _ = a * k * y := by rw [mul_assoc]
          _ = y * (a * k) := h1
          _ = y * a * k := by rw [mul_assoc]
      exact (mul_right_cancel h3).symm
    subst ha1
    have hk1 : k = 1 := by
      refine ih (fun J' hJ' => hz J' (Finset.mem_insert_of_mem hJ'))
        (fun J' hJ' J'' hJ'' hne => hc J' (Finset.mem_insert_of_mem hJ') J''
          (Finset.mem_insert_of_mem hJ'') hne) hk (fun k' hk' => ?_)
      have h1 := hcen k' (Subgroup.mem_sup_right hk')
      simpa using h1
    rw [hk1]
    simp

theorem component_le_or_normal_eq_bot {Γ : Type*} [Group Γ] [Finite Γ] {J S : Subgroup Γ}
    (hJ : CFSG.IsComponent J) (hJz : ∀ x ∈ J, (∀ y ∈ J, y * x = x * y) → x = 1)
    (hS : IsPGroup 2 ↥S) (hgen : J ⊔ S = ⊤) (hO : CFSG.pCore 2 Γ = ⊥)
    {N : Subgroup Γ} (hN : N.Normal) : J ≤ N ∨ N = ⊥ := by
  classical
  have : Fintype Γ := Fintype.ofFinite Γ
  let cj : Γ → Subgroup Γ := fun g => J.map (MulAut.conj g).toMonoidHom
  have hcjmem : ∀ g x, x ∈ cj g ↔ g⁻¹ * x * g ∈ J := by
    intro g x
    show x ∈ J.map (MulAut.conj g).toMonoidHom ↔ _
    rw [Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  have hcomp : ∀ g, CFSG.IsComponent (cj g) := fun g =>
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hJ
  let F : Finset (Subgroup Γ) := Finset.univ.image cj
  let K : Subgroup Γ := ⨆ g, cj g
  have hKF : F.sup id = K := by
    show (Finset.univ.image cj).sup id = ⨆ g, cj g
    rw [Finset.sup_image, Finset.sup_univ_eq_iSup]
    rfl
  have hJK : J ≤ K := by
    intro x hx
    refine Subgroup.mem_iSup_of_mem 1 ((hcjmem 1 x).mpr ?_)
    simpa using hx
  have hKnorm : K.Normal := by
    refine ⟨fun n hn h => ?_⟩
    have hmap : ∀ g, (cj g).map (MulAut.conj h).toMonoidHom ≤ K := by
      intro g x hx
      obtain ⟨y, hy, rfl⟩ := hx
      refine Subgroup.mem_iSup_of_mem (h * g) ((hcjmem (h * g) _).mpr ?_)
      obtain ⟨w, hw, rfl⟩ := hy
      have : (h * g)⁻¹ * ((MulAut.conj h).toMonoidHom ((MulAut.conj g).toMonoidHom w)) * (h * g) = w := by
        simp [MulAut.conj_apply]
        group
      rw [this]
      exact hw
    have : (K.map (MulAut.conj h).toMonoidHom) ≤ K := by
      rw [Subgroup.map_iSup]
      exact iSup_le hmap
    exact this ⟨n, hn, rfl⟩
  have hSN : S ≤ Subgroup.normalizer (K : Set Γ) := fun s _ =>
    Subgroup.mem_normalizer_iff.mpr fun x =>
      ⟨fun hx => hKnorm.conj_mem x hx s, fun hx => by
        have h := hKnorm.conj_mem _ hx s⁻¹
        have e : s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x := by group
        rwa [e] at h⟩
  have hquot : ∀ γ : Γ, ∃ m : ℕ, γ ^ 2 ^ m ∈ K := by
    intro γ
    have hγ : γ ∈ K ⊔ S := by
      have : γ ∈ J ⊔ S := hgen ▸ Subgroup.mem_top γ
      exact sup_le_sup_right hJK S this
    obtain ⟨p, hp, s, hs, rfl⟩ := mem_mul_of_le_normalizer hSN hγ
    obtain ⟨m, hm⟩ := hS ⟨s, hs⟩
    have hsm : s ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    obtain ⟨q, hq, hqe⟩ := mul_pow_mem_of_mem_normalizer (hSN hs) hp (2 ^ m)
    exact ⟨m, by rw [hqe, hsm, mul_one]; exact hq⟩
  have hZ : ∀ z ∈ K, (∀ k ∈ K, z * k = k * z) → z = 1 := by
    intro z hzK hcen
    refine eq_one_of_central_of_commuting_simple F ?_ ?_ (hKF ▸ hzK) (fun k hk => hcen k (hKF ▸ hk))
    · intro J' hJ' x hx hxc
      obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hJ'
      have h1 : g⁻¹ * x * g ∈ J := (hcjmem g x).mp hx
      have h2 : g⁻¹ * x * g = 1 := by
        refine hJz _ h1 fun y hy => ?_
        have hy' : g * y * g⁻¹ ∈ cj g := (hcjmem g _).mpr (by simpa [mul_assoc] using hy)
        have := hxc _ hy'
        calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
          _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [this]
          _ = (g⁻¹ * x * g) * y := by group
      have : x = 1 := by
        have h3 : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        rw [h3, h2]
        group
      exact this
    · intro J' hJ' J'' hJ'' hne a ha b hb
      obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hJ'
      obtain ⟨g', -, rfl⟩ := Finset.mem_image.mp hJ''
      rcases CFSG.LocalCores.distinct_components_commute (hcomp g) (hcomp g') with h | h
      · exact absurd h hne
      · have hle : cj g ≤ Subgroup.centralizer ((cj g' : Subgroup Γ) : Set Γ) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
        exact (Subgroup.mem_centralizer_iff.mp (hle ha) b hb).symm
  by_cases hJN : J ≤ N
  · exact Or.inl hJN
  right
  have hnoconj : ∀ g, ¬ cj g ≤ N := by
    intro g hg
    apply hJN
    intro x hx
    have h1 : g * x * g⁻¹ ∈ N := hg ⟨x, hx, rfl⟩
    have := hN.conj_mem _ h1 g⁻¹
    simpa [mul_assoc] using this
  have hcomm : ∀ g, cj g ≤ Subgroup.centralizer (N : Set Γ) := by
    intro g
    rcases CFSG.LocalCores.component_normal_subgroup (hcomp g) hN with h | h
    · exact absurd h (hnoconj g)
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have hKc : K ≤ Subgroup.centralizer (N : Set Γ) := iSup_le hcomm
  have hNK : ∀ x ∈ N, x ∈ K → x = 1 := by
    intro x hxN hxK
    refine hZ x hxK fun k hk => ?_
    exact Subgroup.mem_centralizer_iff.mp (hKc hk) x hxN
  have hNp : IsPGroup 2 ↥N := by
    intro n
    obtain ⟨m, hm⟩ := hquot (n : Γ)
    refine ⟨m, Subtype.ext ?_⟩
    have h1 : (n : Γ) ^ 2 ^ m ∈ N := N.pow_mem n.2 _
    have := hNK _ h1 hm
    simpa using this
  have hle : N ≤ CFSG.pCore 2 Γ := le_sSup ⟨hN, hNp⟩
  rw [hO] at hle
  exact le_bot_iff.mp hle

end CFSG.Quasithin.S151S5
