module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1CoverAltTenC
public import CFSG.Quasithin.H13.StatementsL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.VolI CFSG.Quasithin.G6

theorem s16c11_v1_cover_alt_ten (V : Type) [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (H : Subgroup (MulAut V)) (Z : Subgroup V) (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤)
    (h : AlternatingNatural H ⊤ Z 10) :
    Z = ⊥ ∨ (Nat.card Z = 2 ∧ Nat.card V = 2 ^ 9 ∧
      FFModel.Realizes (altCoreModel 10) H ⊤ ⊥) := by
  obtain ⟨C, π, hπs, hρ, hβk⟩ := ModelCover.exists_of_realizes hZ hcomm h
  have hker : C.β.ker = Z := by
    ext v
    exact MonoidHom.mem_ker.trans (hβk v)
  have hle := s16c11_v1_cover_ten_bound V hV C
  rw [hker] at hle
  have hpos : 0 < Nat.card Z := Nat.card_pos
  rcases (by omega : Nat.card Z = 1 ∨ Nat.card Z = 2) with h1 | h2
  · exact Or.inl (Subgroup.eq_bot_of_card_eq Z h1)
  · right
    have h256 : Nat.card (FFModel.altDn 10).Sec = 256 := s16c11_v1_card_dnQuot_ten
    have hV' : Nat.card V = 2 ^ 9 := by
      rw [C.card_eq, hker, h2, h256]
      norm_num
    refine ⟨h2, hV', ?_⟩
    have : Finite ↥(FFModel.altDn 10).sec := (inferInstance : Finite ↥(coreMod 10))
    obtain ⟨Φ, hΦ⟩ := ModelCover.exists_mulEquiv (D := FFModel.altDn 10) s16c11_v1_act10
      (fun _ _ => rfl) s16c11_v1_act10_ker s16c11_v1_card_ker_ten s16c11_v1_coreMod_ten_gen
      (fun m => Subtype.ext (s16c11_v1_permMod_sq m.1)) s16c11_v1_cover_ten_bound hV C
      (by rw [hker, h2])
    exact realizes_of_mulEquiv (E := altCoreModel 10) rfl π hπs Φ fun γ v =>
      (congrArg (fun w => (Φ w).val)
        (congrArg (fun f : MulAut V => f v) (hρ γ))).symm.trans (congrArg Subtype.val (hΦ γ v))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
