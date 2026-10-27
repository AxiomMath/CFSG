module

public import CFSG.RankThree.PartOne.Q1327Z.Transport
public import CFSG.RankThree.PartOne.S13K.Sp6Ctx
public import CFSG.RankThree.PartOne.Q1327C.BBase
public import CFSG.RankThree.PartOne.S13K.Sp6Lin

public section

namespace CFSG.RankThree.PartOne.Q1327Z

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFQ
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.S13K CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem refl_row10_of_model
    (hN : ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → 5 ≤ p →
      p ∣ Nat.card K + 1 →
      NoncommOK p ((emb10 : torusVec p 4 (Qext K) →*
        (QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))).range.subgroupOf (M10 K)))
    {p : ℕ} {X A₀ F : Subgroup G} (h : Q1327.T123Base p X A₀ F) (hm : RowModel p X 10)
    {t : MulAut ↥F} (ht : t ∈ torusImage F X) (hrefl : IsAutReflection p F t) {c₀ : G}
    (hc₀ : c₀ ∈ autMovedInG F t) (hc₀1 : c₀ ≠ 1) :
    ∃ y ∈ X ⊓ Subgroup.centralizer (autFixedInG F t : Set G), ¬ Commute c₀ (y * c₀ * y⁻¹) := by
  classical
  obtain ⟨f, hf1, hpq, hmod⟩ := hm
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmod
  have hp := h.prime
  have h5 := h.five_le
  have : Fact p.Prime := ⟨hp⟩
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := f)
      (by rw [Fintype.card_eq_nat_card]; exact hK)
  have hpq' : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
  obtain ⟨q, ε, hqbij, hε, hFT₁, hFT₂⟩ :=
    exists_r10frame (Q1327C.T123Base.toCore h) hK hpq e
  let qe : ↥(M10 K) ≃* StatedProj (StatedSp 3 K) := MulEquiv.ofBijective q hqbij
  let ε' : ↥X →* ↥(M10 K) := qe.symm.toMonoidHom.comp ε
  have hε'surj : Function.Surjective ε' := qe.symm.surjective.comp hε.surjective
  have hker : ε'.ker ≤ Subgroup.center ↥X := by
    intro x hx
    apply hε.central
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (map_eq_one_iff qe.symm qe.symm.injective).1 hx
  have hT : (F.subgroupOf X).map ε' = (emb10 : torusVec p 4 (Qext K) →*
      (QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))).range.subgroupOf (M10 K) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨s, hs, hεs⟩ := hFT₂ ⟨(x : G), hx⟩
      have h1 : ε x = q s := hεs
      have : ε' x = s := by
        show qe.symm (ε x) = s
        rw [h1]
        exact qe.symm_apply_eq.2 rfl
      rw [this]
      exact hs
    · intro hy
      obtain ⟨x, hεx⟩ := hFT₁ y hy
      refine ⟨Subgroup.inclusion h.F_le x, x.2, ?_⟩
      show qe.symm (ε (Subgroup.inclusion h.F_le x)) = y
      rw [hεx]
      exact qe.symm_apply_eq.2 rfl
  have hmodel : NoncommOK p ((F.subgroupOf X).map ε') := by
    rw [hT]
    exact hN K p hp h5 hpq'
  exact refl_of_quotient h ε' hε'surj hker hmodel ht hrefl hc₀ hc₀1

end CFSG.RankThree.PartOne.Q1327Z
