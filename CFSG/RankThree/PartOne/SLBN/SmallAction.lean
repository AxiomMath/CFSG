module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.RankThree.PartOne.SLBN

open CFSG.SectionRank.Ccomm

theorem not_dvd_card_GL_three {d : ℕ} (hd : d ≤ 7) :
    ¬ 25 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 3)) := by
  rw [card_GL_zmod]
  interval_cases d <;> simp [Fin.prod_univ_succ]

theorem not_five_dvd_card_GL_three {d : ℕ} (hd : d ≤ 3) :
    ¬ 5 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 3)) := by
  rw [card_GL_zmod]
  interval_cases d <;> simp [Fin.prod_univ_succ]

theorem mulAut_hom_eq_one_of_small {S Q : Type*} [Group S] [IsSimpleGroup S] [Finite S]
    [Group Q] [Finite Q] (hcomm : ∀ a b : Q, a * b = b * a) (hpow : ∀ a : Q, a ^ 3 = 1)
    (hcard : Nat.card Q ≤ 3 ^ 7) (P : Subgroup S) (hP : Nat.card P = 25) (ρ : S →* MulAut Q) :
    ρ = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hρ
  have hker : ρ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
    · exact h
    · exact absurd (MonoidHom.ext fun s => by
        have : s ∈ ρ.ker := h ▸ Subgroup.mem_top s
        simpa using this) hρ
  have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).1 hker
  have hQ3 : IsPGroup 3 Q := fun x => ⟨1, by simp [hpow x]⟩
  obtain ⟨d, hd⟩ := hQ3.exists_card_eq
  have hd7 : d ≤ 7 := by
    have : 3 ^ d ≤ 3 ^ 7 := hd ▸ hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary (p := 3) hcomm hpow hd
  have h1 : Nat.card (MulAut Q) = Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 3)) :=
    card_mulAut_eq_card_GL e
  have h2 : Nat.card (P.map ρ) = 25 := by
    rw [Subgroup.card_map_of_injective hinj, hP]
  have h3 : 25 ∣ Nat.card (MulAut Q) := h2 ▸ Subgroup.card_subgroup_dvd_card (P.map ρ)
  exact not_dvd_card_GL_three hd7 (h1 ▸ h3)

end CFSG.RankThree.PartOne.SLBN
