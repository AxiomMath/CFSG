module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Vol2.Ch12Sec6Frame

public section

namespace CFSG.Quasithin.H13.S126P31

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits S126 Equiv

section Borel

variable {Y : Type*} [Group Y] [Finite Y]

theorem sylow_inf_eq_pCoreOf_borel (X Ts Ms : Subgroup Y) [X.Normal] (hT : IsSylowTwoOf Ts ⊤)
    (hKM : Ms ⊓ X = X ⊓ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y)) :
    Ts ⊓ X = pCoreOf 2 (Ms ⊓ X) ∧ Ms ≤ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y) ∧
      Ts ⊓ X ≤ pCoreOf 2 Ms := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl : IsSylowTwoOf (Ts ⊓ X) X :=
    A4.isSylowTwoOf_inf_normal hT le_top Subgroup.le_normalizer_of_normal
  have hSle : Ts ⊓ X ≤ Ms ⊓ X := by
    rw [hKM]
    exact le_inf inf_le_right Subgroup.le_normalizer
  have hSyl' : IsSylowTwoOf (Ts ⊓ X) (Ms ⊓ X) :=
    A4.isSylowTwoOf_mono hSyl hSle (inf_le_right)
  have hcore : Ts ⊓ X = pCoreOf 2 (Ms ⊓ X) := by
    refine le_antisymm ?_ (F7.isSylowTwoOf_pCoreOf_le hSyl')
    exact le_pCoreOf_of_le_normalizer 2 hSle (hKM ▸ inf_le_right) hSyl.2.1
  have hBkn : Ms ≤ Subgroup.normalizer ((Ms ⊓ X : Subgroup Y) : Set Y) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxM, hxK⟩
      exact ⟨Ms.mul_mem (Ms.mul_mem hm hxM) (Ms.inv_mem hm),
        Subgroup.Normal.conj_mem inferInstance x hxK m⟩
    · rintro ⟨hxM, hxK⟩
      refine ⟨?_, ?_⟩
      · have := Ms.mul_mem (Ms.mul_mem (Ms.inv_mem hm) hxM) hm
        simpa [mul_assoc] using this
      · have := Subgroup.Normal.conj_mem (inferInstance : X.Normal) _ hxK m⁻¹
        simpa [mul_assoc] using this
  have hMn : Ms ≤ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y) := by
    rw [hcore]
    exact hBkn.trans (normalizer_le_normalizer_pCoreOf 2 _)
  refine ⟨hcore, hMn, ?_⟩
  exact le_pCoreOf_of_le_normalizer 2 (hSle.trans inf_le_left) hMn hSyl.2.1

theorem eq_borel_of_overgroup (X Ts Ms Ls : Subgroup Y) [X.Normal] (m : ℕ)
    (hBM : X ⊓ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y) ≤ Ms) (hXM : ¬ X ≤ Ms)
    (hLM : Ls ≤ Ms) (hLn : Ms ≤ Subgroup.normalizer (Ls : Set Y))
    (hL23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card Ls → p = 2 ∨ p = 3)
    (hov : ∀ N W : Subgroup Y,
      X ⊓ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y) ≤ N → N ≤ X →
      N ≠ X ⊓ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y) → N ≠ X → W ≤ N →
      (W.subgroupOf N).Normal → (∀ p : ℕ, p.Prime → p ∣ Nat.card W → p = 2 ∨ p = 3) →
      ¬ 3 ^ m ∣ Nat.card W)
    (hW : 3 ^ m ∣ Nat.card ↥(Ls ⊓ X)) :
    Ms ⊓ X = X ⊓ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y) := by
  by_contra hne
  have hle : X ⊓ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y) ≤ Ms ⊓ X :=
    le_inf hBM inf_le_left
  have hNX : Ms ⊓ X ≠ X := fun h => hXM (inf_eq_right.1 h)
  refine hov (Ms ⊓ X) (Ls ⊓ X) hle inf_le_right (fun h => hne h) hNX
    (inf_le_inf_right _ hLM) ?_ ?_ hW
  · have hWN : Ms ⊓ X ≤ Subgroup.normalizer ((Ls ⊓ X : Subgroup Y) : Set Y) :=
      (le_inf (inf_le_left.trans hLn)
        (inf_le_right.trans Subgroup.le_normalizer_of_normal)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (inf_le_inf_right _ hLM)).2 hWN
  · intro p hp hpd
    exact hL23 p hp (hpd.trans (Subgroup.card_dvd_of_le inf_le_left))

theorem card_eq_relIndex_mul (X Ls : Subgroup Y) [X.Normal] :
    Nat.card Ls = X.relIndex Ls * Nat.card ↥(Ls ⊓ X) ∧ X.relIndex Ls ∣ X.index := by
  refine ⟨?_, Subgroup.relIndex_dvd_index_of_normal X Ls⟩
  have h : X.relIndex Ls * Nat.card ↥(X ⊓ Ls) = Nat.card Ls := Subgroup.relIndex_mul_card _ _
  rw [inf_comm] at h
  exact h.symm

end Borel

end CFSG.Quasithin.H13.S126P31
