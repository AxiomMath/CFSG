module

public import CFSG.Quasithin.Background.FFC4Zmod
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Fixed
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.Quasithin

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem nl3w_equiv {L : Subgroup (MulAut W)} (hnat : BinaryNaturalSL L ⊤ ⊥ 3 1) :
    Nonempty (W ≃* Multiplicative (Fin 3 → ZMod 2)) := by
  obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod hnat
  obtain ⟨f, hfs, hfk, -⟩ := FFC.exists_natMap hπ
  have hfi : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 := (hfk u).1 hu
    exact Subtype.ext (Subgroup.mem_bot.1 h1)
  exact ⟨Subgroup.topEquiv.symm.trans (MulEquiv.ofBijective f ⟨hfi, hfs⟩)⟩

omit [Finite W] in
theorem nl3w_two_dvd_index {H : Subgroup W} (hW : Nat.card W = 8) (hH : H ≠ ⊤) : 2 ∣ H.index := by
  have h1 : H.index ∣ 2 ^ 3 := by
    have := H.index_dvd_card
    rw [hW] at this
    simpa using this
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hH (Subgroup.index_eq_one.1 (by simpa using hk'))
  rw [hk']
  exact dvd_pow_self 2 hk0

omit [Finite W] in
theorem nl3w_fixV_ne_top {E : Subgroup (MulAut W)} (hE1 : E ≠ ⊥) : fixV E ≠ ⊤ := by
  intro htop
  obtain ⟨⟨g, hg⟩, hne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE1
  apply hne
  apply Subtype.ext
  ext w
  exact (mem_fixV.1 (htop ▸ Subgroup.mem_top w)) g hg

theorem natL3_weight {L E : Subgroup (MulAut W)} (hnat : BinaryNaturalSL L ⊤ ⊥ 3 1)
    (hE : IsElemAbelian2 E) (hE1 : E ≠ ⊥) : rk ↥E ≤ 2 * rkIdx (fixV E) := by
  obtain ⟨e₀⟩ := nl3w_equiv hnat
  have hW : Nat.card W = 8 := by
    rw [Nat.card_congr e₀.toEquiv, Nat.card_eq_fintype_card]
    simp
  let Ψ : MulAut W ≃* CFSG.QuasithinUnique.Setup.Family.GL32 :=
    CFSG.SectionRank.Ccomm.elemAutEquivGL e₀
  have hB1 : E.map Ψ.toMonoidHom ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective E Ψ.injective]
    exact hE1
  have hBc : ∀ a ∈ E.map Ψ.toMonoidHom, ∀ b ∈ E.map Ψ.toMonoidHom, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hE.1 a ha b hb]
  have hBs : ∀ a ∈ E.map Ψ.toMonoidHom, a ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE.2 a ha, map_one]
  have hfix := CFSG.QuasithinUnique.Setup.Family.GL3_elementary_abelian_fixed_codimensions
    hB1 hBc hBs
  have hcard : Nat.card ↥E = Nat.card ↥(E.map Ψ.toMonoidHom) :=
    (Subgroup.card_map_of_injective Ψ.injective).symm
  have hrk : rk ↥E ≤ 2 := by
    unfold rk
    rw [hcard]
    rcases hfix with ⟨h2, -⟩ | ⟨h4, -⟩
    · rw [h2]
      have : padicValNat 2 2 = 1 := padicValNat_self
      omega
    · rw [h4]
      have : padicValNat 2 (2 ^ 2) = 2 := padicValNat.prime_pow 2
      norm_num at this
      omega
  have hidx : 1 ≤ rkIdx (fixV E) := by
    unfold rkIdx
    exact one_le_padicValNat_of_dvd (Subgroup.index_ne_zero_of_finite)
      (nl3w_two_dvd_index hW (nl3w_fixV_ne_top hE1))
  omega

end CFSG.Quasithin
