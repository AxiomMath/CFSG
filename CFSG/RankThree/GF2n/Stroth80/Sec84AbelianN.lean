module

public import CFSG.RankThree.GF2n.Stroth80.Sec12Defs
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

theorem sq_mul_eq_comm (c c' : G) :
    (c * c') ^ 2 = (c * ⁅c', c⁆ * c⁻¹) * (c ^ 2 * c' ^ 2) := by
  simp only [commutatorElement_def, sq]
  group

theorem le_of_central_isOppDecomp {N Z0 L L' R : Subgroup G}
    (hopp : IsOppDecomp N Z0 L L' (L ⊓ N) (L' ⊓ N)) (hLR : L ≤ R) (hL'R : L' ≤ R)
    (hcZ0 : ∀ ρ ∈ R, ∀ c ∈ N, ⁅ρ, c⁆ ∈ Z0) : N ≤ Z0 := by
  intro c hc'
  have hA1 : c ∈ L ⊓ N := (hopp.2.2.2.2.2.2.2.2.1 c hc').mpr fun l hl => hcZ0 l (hLR hl) c hc'
  have hA2 : c ∈ L' ⊓ N :=
    (hopp.2.2.2.2.2.2.2.2.2 c hc').mpr fun l hl => hcZ0 l (hL'R hl) c hc'
  have : c ∈ (L ⊓ N) ⊓ (L' ⊓ N) := ⟨hA1, hA2⟩
  rw [hopp.2.2.2.2.2.1] at this
  exact this

variable [Finite G]

theorem sq_mem_of_abelian_irred {R N Z0 Q L L' : Subgroup G}
    (hirr : IsIrredModule R N Z0) (hopp : IsOppDecomp N Z0 L L' (L ⊓ N) (L' ⊓ N))
    (hLR : L ≤ R) (hL'R : L' ≤ R) (hQN : Q ≤ N)
    (hQn : ∀ c ∈ N, ∀ t ∈ Q, c * t * c⁻¹ ∈ Q) (hQR : ∀ ρ ∈ R, ∀ t ∈ Q, ρ * t * ρ⁻¹ ∈ Q)
    (hRN : ∀ ρ ∈ R, ∀ c ∈ N, ρ * c * ρ⁻¹ ∈ N) (hNN : ∀ c ∈ N, ∀ c' ∈ N, ⁅c, c'⁆ ∈ Q)
    (hZc : ∀ z ∈ Z0, ∀ ρ ∈ R, ⁅z, ρ⁆ ∈ Q) (hZsq : ∀ z ∈ Z0, z ^ 2 ∈ Q) :
    ∀ c ∈ N, c ^ 2 ∈ Q := by
  classical
  have hZN : Z0 ≤ N := hirr.2.2.1.le
  let Kε : Subgroup G :=
    { carrier := {c | c ∈ N ∧ c ^ 2 ∈ Q}
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨N.mul_mem ha hb, ?_⟩
        rw [sq_mul_eq_comm]
        exact Q.mul_mem (hQn a ha _ (hNN b hb a ha)) (Q.mul_mem ha2 hb2)
      one_mem' := ⟨N.one_mem, by simpa using Q.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        refine ⟨N.inv_mem ha, ?_⟩
        have e : a⁻¹ ^ 2 = (a ^ 2)⁻¹ := by simp only [sq]; group
        rw [e]
        exact Q.inv_mem ha2 }
  have hZK : Z0 ≤ Kε := fun z hz => ⟨hZN hz, hZsq z hz⟩
  have hKN : Kε ≤ N := fun c hc => hc.1
  have hKinv : ∀ ρ ∈ R, conjSubgroup ρ Kε = Kε := by
    intro ρ hρ
    refine conjSubgroup_eq_self_iff.mpr (Subgroup.mem_normalizer_fintype fun c hc => ?_)
    obtain ⟨hcN, hc2⟩ := hc
    refine ⟨hRN ρ hρ c hcN, ?_⟩
    have e : (ρ * c * ρ⁻¹) ^ 2 = ρ * c ^ 2 * ρ⁻¹ := by simp only [sq]; group
    rw [e]
    exact hQR ρ hρ _ hc2
  rcases hirr.2.2.2 Kε hZK hKN hKinv with hK | hK
  · exfalso
    have hcZ0 : ∀ ρ ∈ R, ∀ c ∈ N, ⁅ρ, c⁆ ∈ Z0 := by
      intro ρ hρ c hc'
      have hc2Z : c ^ 2 ∈ Z0 := hirr.2.1 c hc'
      have hd : ⁅ρ, c⁆ ∈ Kε := by
        refine ⟨?_, ?_⟩
        · have e : ⁅ρ, c⁆ = (ρ * c * ρ⁻¹) * c⁻¹ := by simp only [commutatorElement_def]
          rw [e]
          exact N.mul_mem (hRN ρ hρ c hc') (N.inv_mem hc')
        · have e : ⁅ρ, c⁆ = (ρ * c * ρ⁻¹) * c⁻¹ := by simp only [commutatorElement_def]
          rw [e, sq_mul_eq_comm]
          have hconjN : ρ * c * ρ⁻¹ ∈ N := hRN ρ hρ c hc'
          have h1 : (ρ * c * ρ⁻¹) * ⁅c⁻¹, ρ * c * ρ⁻¹⁆ * (ρ * c * ρ⁻¹)⁻¹ ∈ Q :=
            hQn _ hconjN _ (hNN _ (N.inv_mem hc') _ hconjN)
          have h2 : (ρ * c * ρ⁻¹) ^ 2 * c⁻¹ ^ 2 = ⁅ρ, c ^ 2⁆ := by
            simp only [sq, commutatorElement_def]
            group
          have h3 : ⁅ρ, c ^ 2⁆ ∈ Q := by
            rw [← commutatorElement_inv]
            exact Q.inv_mem (hZc _ hc2Z ρ hρ)
          rw [h2]
          exact Q.mul_mem h1 h3
      rw [hK] at hd
      exact hd
    have := le_of_central_isOppDecomp hopp hLR hL'R hcZ0
    exact absurd (lt_of_lt_of_le hirr.2.2.1 this) (lt_irrefl _)
  · intro c hc'
    have : c ∈ Kε := by rw [hK]; exact hc'
    exact this.2

end CFSG.RankThree.GF2n.Stroth80
