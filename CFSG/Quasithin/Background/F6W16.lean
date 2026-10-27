module

public import CFSG.Quasithin.Background.F6W16Wreath
public import CFSG.LocalAnalysis.RankTwoShapes.SylowShapes
public import CFSG.Walter.TwoRank

public section

namespace CFSG.Quasithin

namespace F6

namespace WreathRes

theorem twoRank_eq_two {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) (P : Sylow 2 S) {H : Subgroup Z4WrZ2}
    (hH : H.index = 2) (e : ↥(P : Subgroup S) ≃* ↥H) : CFSG.Assembly.twoRank S = 2 := by
  have hPcard : Nat.card (P : Subgroup S) = 16 := by
    rw [Nat.card_congr e.toEquiv, card_of_index_two hH]
  refine le_antisymm ?_ (CFSG.Walter.two_le_twoRank S hnonab ?_)
  · unfold CFSG.Assembly.twoRank CFSG.Assembly.pRank
    apply csSup_le'
    rintro k ⟨E, -, ⟨hEcomm, hE2⟩, hEcard⟩
    have hEp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE2 x x.2)⟩
    obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
    obtain ⟨f⟩ := nonempty_sylow_mulEquiv Q P
    let φ : E →* Z4WrZ2 :=
      H.subtype.comp ((e.toMonoidHom.comp f.toMonoidHom).comp (Subgroup.inclusion hEQ))
    have hφ : Function.Injective φ := H.subtype_injective.comp
      ((e.injective.comp f.injective).comp (Subgroup.inclusion_injective hEQ))
    have h4 := card_le_four_of_le_wreath φ.range (fun x hx => by
        obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hx
        rw [← map_mul, show a * a = 1 from Subtype.ext (by simpa [sq] using hE2 a a.2), map_one])
      (fun x hx y hy => by
        obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hx
        obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 hy
        rw [← map_mul, ← map_mul, hEcomm.is_comm.comm a b])
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, hEcard] at h4
    by_contra hk
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · rw [even_iff_two_dvd]
    exact dvd_trans (hPcard ▸ (by norm_num : 2 ∣ 16)) (Subgroup.card_subgroup_dvd_card _)

end WreathRes

theorem wreathIndexTwoSylowFact_holds :
    WreathIndexTwoSylowFact := by
  intro S _ _ _ hnonab P H hH ⟨e⟩
  exfalso
  have hPcard : Nat.card (P : Subgroup S) = 16 := by
    rw [Nat.card_congr e.toEquiv, WreathRes.card_of_index_two hH]
  have hinv : WreathRes.involutionCount (P : Subgroup S) = 3 ∨
      WreathRes.involutionCount (P : Subgroup S) = 7 := by
    rw [WreathRes.involutionCount_congr e]
    exact WreathRes.involutionCount_of_index_two hH
  rcases CFSG.RankTwoShapes.rank_two_sylow_shapes hnonab (WreathRes.twoRank_eq_two hnonab P hH e)
      P with ⟨n, -, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩ | ⟨U', _, U, hU, ⟨f⟩⟩
  ·
    have h8 : 2 ^ (n - 1) = 8 := by
      have h := Nat.card_congr f.toEquiv
      rw [hPcard, DihedralGroup.nat_card] at h
      omega
    rw [h8] at f
    rw [WreathRes.involutionCount_congr f, WreathRes.involutionCount_dihedral_eight] at hinv
    omega
  ·
    have h4 : n = 4 := by
      have h := Nat.card_congr f.toEquiv
      rw [hPcard, CFSG.Semidihedral.card n (by omega)] at h
      exact Nat.pow_right_injective le_rfl (h.symm.trans (by norm_num) : 2 ^ n = 2 ^ 4)
    subst h4
    rw [WreathRes.involutionCount_congr f, WreathRes.involutionCount_semidihedral_four] at hinv
    omega
  ·
    have h := Nat.card_congr f.toEquiv
    rw [hPcard, RegularWreathProduct.card] at h
    have h1 : Nat.card (Multiplicative (ZMod (2 ^ n))) = 2 ^ n := Nat.card_zmod _
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := Nat.card_zmod _
    rw [h1, h2] at h
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    nlinarith
  ·
    have h := Nat.card_congr f.toEquiv
    rw [hPcard, (CFSG.RankTwoShapes.unitaryFour_sylow_card hU U).1] at h
    omega

end F6

end CFSG.Quasithin
