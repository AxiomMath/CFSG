module

public import CFSG.LocalAnalysis.StandardType.GGPGLToralityCaseA
public import CFSG.LocalAnalysis.StandardType.GGPGLToralityCaseB

public section

namespace CFSG.StandardType.TypeA.PGLTor

open Matrix

universe u

variable {K : Type*} [Field K] {p : ℕ}

theorem card_le_of_dichotomy {ι : Type*} [Fintype ι] [DecidableEq ι] [Finite K] (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) {G : Subgroup (GL ι K)} (hG : IsProjElem p G)
    (h : IsToral G ∨ Nat.card G ≤ p ^ (Fintype.card ι / p + 1) * (Nat.card K - 1)) :
    p * Nat.card G ≤ p ^ Fintype.card ι * (Nat.card K - 1) := by
  classical
  have hK1 : 0 < Nat.card K - 1 := by
    have := Finite.one_lt_card (α := K)
    omega
  have hpK' : p ≤ Nat.card K - 1 := Nat.le_of_dvd hK1 hpK
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hsub : Subsingleton G :=
      ⟨fun x y => Subtype.ext (Units.ext (Matrix.ext fun i => isEmptyElim i))⟩
    have h1 : Nat.card G ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
    rw [Fintype.card_eq_zero, pow_zero, one_mul]
    calc p * Nat.card G ≤ p * 1 := Nat.mul_le_mul_left _ h1
      _ ≤ Nat.card K - 1 := by rw [mul_one]; exact hpK'
  have i₀ : ι := hι.some
  have : NeZero p := ⟨hp.ne_zero⟩
  by_cases htor : IsToral G
  · obtain ⟨A, hA⟩ := htor
    have hcount := card_le_of_diag (p := p) A id i₀ (fun x hx => by
      obtain ⟨u, hu⟩ := hG.pow_scalar x hx
      have hdiag := eq_diagonal_of_offDiag_eq_zero (M := conjMatrix A x) (hA x hx)
      refine ⟨fun i => conjMatrix A x i i, hdiag, fun i j hij => by rw [show i = j from hij],
        fun i => ?_⟩
      have h1 := conjMatrix_pow A x p
      rw [hu, conjMatrix_scalar, hdiag, diagonal_pow] at h1
      have h2 := congrFun (congrFun h1 i) i
      have h3 := congrFun (congrFun h1 i₀) i₀
      simp only [diagonal_apply_eq, scalar_apply, Pi.pow_apply] at h2 h3
      show conjMatrix A x i i ^ p = conjMatrix A x i₀ i₀ ^ p
      rw [← h2, ← h3])
    rw [Finset.image_id, Finset.card_univ] at hcount
    have hn : 1 ≤ Fintype.card ι := Fintype.card_pos
    calc p * Nat.card G ≤ p * ((Nat.card K - 1) * p ^ (Fintype.card ι - 1)) :=
          Nat.mul_le_mul_left _ hcount
      _ = p ^ (Fintype.card ι - 1 + 1) * (Nat.card K - 1) := by ring
      _ = p ^ Fintype.card ι * (Nat.card K - 1) := by rw [Nat.sub_add_cancel hn]
  · have hbound := h.resolve_left htor
    have hn2 : 2 ≤ Fintype.card ι := by
      by_contra hlt
      apply htor
      exact ⟨1, fun x _ i j hij => absurd (Fintype.card_le_one_iff.mp (by omega) i j) hij⟩
    have hdiv : Fintype.card ι / p ≤ Fintype.card ι / 3 := Nat.div_le_div_left hp3 (by norm_num)
    calc p * Nat.card G ≤ p * (p ^ (Fintype.card ι / p + 1) * (Nat.card K - 1)) :=
          Nat.mul_le_mul_left _ hbound
      _ = p ^ (Fintype.card ι / p + 2) * (Nat.card K - 1) := by ring
      _ ≤ p ^ Fintype.card ι * (Nat.card K - 1) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp.pos (by omega))

theorem toral_or_card_le_aux [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    (n : ℕ) : ∀ (ι : Type u) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
      ∀ G : Subgroup (GL ι K), IsProjElem p G →
        IsToral G ∨ Nat.card G ≤ p ^ (Fintype.card ι / p + 1) * (Nat.card K - 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ι _ _ hn G hG
  classical
  by_cases hA : ∃ h ∈ G, h ^ p = 1 ∧ ∃ g ∈ G, g * h ≠ h * g
  · right
    obtain ⟨h, hhG, hhp, g, hgG, hgh⟩ := hA
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_dvd hp hpK
    have : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨A₀, hA₀⟩ := exists_conj_diagonal hζ ({h} : Set (GL ι K))
      (fun x hx y hy => by rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy])
      (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact hhp)
    set c := MulAut.conj A₀ with hc
    have hcmat : ∀ x : GL ι K, ((c x : GL ι K) : Matrix ι ι K) =
        (A₀ : Matrix ι ι K) * (x : Matrix ι ι K) * ((A₀⁻¹ : GL ι K) : Matrix ι ι K) := fun x => by
      rw [hc, MulAut.conj_apply, Units.val_mul, Units.val_mul]
    have hh'diag : ((c h : GL ι K) : Matrix ι ι K) =
        diagonal (fun i => ((c h : GL ι K) : Matrix ι ι K) i i) :=
      eq_diagonal_of_offDiag_eq_zero fun i j hij => by
        rw [hcmat]
        exact hA₀ h rfl i j hij
    have hh'p : c h ^ p = 1 := by rw [← map_pow, hhp, map_one]
    have hg'h' : c g * c h ≠ c h * c g := by
      intro heq
      rw [← map_mul, ← map_mul] at heq
      exact hgh (c.injective heq)
    have IH : ∀ (κ : Type u) [Fintype κ] [DecidableEq κ], Fintype.card κ < Fintype.card ι →
        ∀ R : Subgroup (GL κ K), IsProjElem p R →
          p * Nat.card R ≤ p ^ Fintype.card κ * (Nat.card K - 1) := by
      intro κ _ _ hκ R hR
      exact card_le_of_dichotomy hp hp2 hpK hR (ih (Fintype.card κ) (hn ▸ hκ) κ rfl R hR)
    have h1 := card_le_of_noncomm hp (hG.map_conj A₀) ⟨h, hhG, rfl⟩ hh'diag hh'p ⟨g, hgG, rfl⟩
      hg'h' IH
    rwa [card_map_conj] at h1
  · push Not at hA
    exact toral_or_card_le_of_central hp hp2 hpK hG hA

theorem toral_or_card_le [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    {ι : Type u} [Fintype ι] [DecidableEq ι] {G : Subgroup (GL ι K)} (hG : IsProjElem p G) :
    IsToral G ∨ Nat.card G ≤ p ^ (Fintype.card ι / p + 1) * (Nat.card K - 1) :=
  toral_or_card_le_aux hp hp2 hpK _ ι rfl G hG

theorem card_le_of_isProjElem [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    {ι : Type u} [Fintype ι] [DecidableEq ι] {G : Subgroup (GL ι K)} (hG : IsProjElem p G) :
    p * Nat.card G ≤ p ^ Fintype.card ι * (Nat.card K - 1) :=
  card_le_of_dichotomy hp hp2 hpK hG (toral_or_card_le hp hp2 hpK hG)

end CFSG.StandardType.TypeA.PGLTor
