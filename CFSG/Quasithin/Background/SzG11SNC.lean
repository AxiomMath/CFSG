module

public import CFSG.Quasithin.Background.SzG11SConf
public import CFSG.Quasithin.Background.SzG11NCTwo
public import CFSG.Quasithin.Background.P5Om4Rank
public import CFSG.Quasithin.Background.G10Clifford
public import CFSG.Quasithin.Background.SzG11NCG2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin.SzG11NC

namespace G11

namespace SzG11S

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem isIrr_top_of_conf [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)}
    {v₁ : V} {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)}
    (hs : Conf B Γ v₁ W X X₀ L) (hp : G116Props B Γ v₁ X L ⊤) :
    IsIrr (normalClosure Γ L) ⊤ :=
  ((g10_7 V B Γ v₁ W X X₀ L hs.h108).2.2.2 ⊤ hp.1).1

theorem false_of_natural_conf {ι : Type} [Fintype ι] [DecidableEq ι] (K : Type) [Field K]
    [Finite K] [Algebra (ZMod 2) K] (hK : 8 ≤ Nat.card K) (hι : 2 ≤ Fintype.card ι) [Finite V]
    {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
    {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)}
    (hs : Conf B Γ v₁ W X X₀ L) (hp : G116Props B Γ v₁ X L ⊤)
    {Γ₀ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    (hnat : IsNaturalMatrixModule (normalClosure Γ L) Γ₀) : False := by
  have hhyp := hs.hyp
  have hd : 6 ≤ Module.finrank (ZMod 2) V := by
    have hf := three_le_finrank_of_card hK
    rw [finrank_of_natural hnat]
    nlinarith
  obtain ⟨sc, hsc⟩ := exists_scalars_of_natural hnat
  exact not_three_of_scalars (normalClosure Γ L) Γ (isIrr_top_of_conf hs hp)
    (normalClosure_normal Γ L) K hK hd sc hsc X hhyp.X_le hhyp.X_sq v₁ hhyp.point hhyp.three

theorem false_of_g2_conf (K : Type) [Field K] [Finite K] [Algebra (ZMod 2) K]
    (hK : 8 ≤ Nat.card K) [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)}
    {v₁ : V} {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)}
    (hs : Conf B Γ v₁ W X X₀ L) (hp : G116Props B Γ v₁ X L ⊤)
    {G₀ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)} (hG₀ : G₀ ≤ quasithinG2 K)
    (hnat : IsG2NaturalModule (normalClosure Γ L) G₀) : False := by
  have hhyp := hs.hyp
  have hd : 6 ≤ Module.finrank (ZMod 2) V :=
    le_trans (by norm_num) (twelve_le_finrank_of_g2 K (by omega) hnat)
  obtain ⟨sc, hsc⟩ := exists_scalars_of_g2 K hG₀ hnat
  exact not_three_of_scalars (normalClosure Γ L) Γ (isIrr_top_of_conf hs hp)
    (normalClosure_normal Γ L) K hK hd sc hsc X hhyp.X_le hhyp.X_sq v₁ hhyp.point hhyp.three

theorem false_of_two_conf [Finite V] (K : Type) [Field K] [Finite K] (hK : 4 ≤ Nat.card K)
    {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
    {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)}
    (hs : Conf B Γ v₁ W X X₀ L) (hp : G116Props B Γ v₁ X L ⊤)
    (hd : 8 ≤ Module.finrank (ZMod 2) V) (sc : K →+* Module.End (ZMod 2) V)
    (hsc : ∀ κ, ∀ h ∈ normalClosure Γ L, ∀ v, sc κ (h v) = h (sc κ v))
    (hlin : ∀ x ∈ X, ∀ f ∈ endCommutant (normalClosure Γ L), ∀ v, x (f v) = f (x v)) :
    False :=
  false_of_commutant_four hs.hyp (isIrr_top_of_conf hs hp) (normalClosure_normal Γ L)
    (le_trans hK (CommF.card_le K sc hsc)) hd hlin

theorem noConfigL2 : NoConfigL2 := by
  intro V _ _ _ B Γ v₁ W X X₀ L hs hp n hn hnat
  exact false_of_natural_conf (GaloisField 2 n) (eight_le_card_galoisField n hn) (by simp) hs hp
    hnat

theorem noConfigOm4Plus : NoConfigOm4Plus := by
  intro V _ _ _ B Γ v₁ W X X₀ L hs hp n hn hnat
  exact false_of_natural_conf (GaloisField 2 n) (eight_le_card_galoisField n hn) (by simp) hs hp
    hnat

theorem noConfigSp4_of_two (h : NoConfigSp4Two) : NoConfigSp4 := by
  intro V _ _ _ B Γ v₁ W X X₀ L hs hp n hn hnat
  by_cases h3 : 3 ≤ n
  · exact false_of_natural_conf (GaloisField 2 n) (eight_le_card_galoisField n h3) (by simp) hs hp
      hnat
  · obtain rfl : n = 2 := by omega
    by_cases hex : ∃ x ∈ X, ∃ f ∈ endCommutant (normalClosure Γ L), ∃ v, x (f v) ≠ f (x v)
    · exact h V B Γ v₁ W X X₀ L hs hp hnat hex
    · push Not at hex
      obtain ⟨sc, hsc⟩ := exists_scalars_of_natural hnat
      exact false_of_two_conf (GaloisField 2 2) four_le_card_galoisField_two hs hp
        (eight_le_finrank_of_natural_two (by simp) hnat) sc hsc hex

theorem noConfigOm4Minus_of_two (h : NoConfigOm4MinusTwo) : NoConfigOm4Minus := by
  intro V _ _ _ B Γ v₁ W X X₀ L hs hp a ha b c hbc hnat
  by_cases h3 : 3 ≤ a
  · exact false_of_natural_conf (GaloisField 2 a) (eight_le_card_galoisField a h3) (by simp) hs hp
      hnat
  · obtain rfl : a = 2 := by omega
    by_cases hex : ∃ x ∈ X, ∃ f ∈ endCommutant (normalClosure Γ L), ∃ v, x (f v) ≠ f (x v)
    · exact h V B Γ v₁ W X X₀ L hs hp b c hbc hnat hex
    · push Not at hex
      obtain ⟨sc, hsc⟩ := exists_scalars_of_natural hnat
      exact false_of_two_conf (GaloisField 2 2) four_le_card_galoisField_two hs hp
        (eight_le_finrank_of_natural_two (by simp) hnat) sc hsc hex

theorem noConfigG2_of_two (h : NoConfigG2Two) : NoConfigG2 := by
  intro V _ _ _ B Γ v₁ W X X₀ L hs hp n hn hnat
  by_cases h3 : 3 ≤ n
  · exact false_of_g2_conf (GaloisField 2 n) (eight_le_card_galoisField n h3) hs hp
      commutator_quasithinG2_le hnat
  · obtain rfl : n = 2 := by omega
    by_cases hex : ∃ x ∈ X, ∃ f ∈ endCommutant (normalClosure Γ L), ∃ v, x (f v) ≠ f (x v)
    · exact h V B Γ v₁ W X X₀ L hs hp hnat hex
    · push Not at hex
      obtain ⟨sc, hsc⟩ := exists_scalars_of_g2 (GaloisField 2 2) commutator_quasithinG2_le hnat
      exact false_of_two_conf (GaloisField 2 2) four_le_card_galoisField_two hs hp
        (le_trans (by norm_num)
          (twelve_le_finrank_of_g2 (GaloisField 2 2) four_le_card_galoisField_two
            hnat))
        sc hsc hex

theorem noConfigOm4PlusFour : NoConfigOm4PlusFour := by
  intro V _ _ _ B Γ v₁ W X X₀ L hs _ hnat hXH
  obtain ⟨φ, ψ, hψ⟩ := hnat
  have hhyp := hs.hyp
  have hK4 : 4 ≤ Nat.card (GaloisField 2 2) := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hK : 2 < Nat.card (GaloisField 2 2) := by omega
  have hV : 2 ∣ Nat.card V := by
    rw [Nat.card_congr ψ.toEquiv, Nat.card_fun,
      GaloisField.card 2 2 (by norm_num)]
    simp
  rcases hhyp.three with h1 | ⟨a, haX, hrank, hv₁⟩
  · exact P5.not_fixed_subset_pair hK ψ X hhyp.X_sq
      (fun x => ((φ ⟨x.1, hXH x.2⟩ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) (GaloisField 2 2)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (GaloisField 2 2)))
      (fun x v => hψ ⟨x.1, hXH x.2⟩ v) hV v₁ h1
  · have haH := hXH haX
    have hne : ((φ ⟨a, haH⟩ :
        Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) (GaloisField 2 2))) ≠ 1 := by
      intro h
      have h' : φ ⟨a, haH⟩ = 1 := Subtype.ext h
      have ha1 : a = 1 := congrArg Subtype.val ((φ.map_eq_one_iff).1 h')
      obtain ⟨u, hu⟩ := hv₁
      apply hhyp.point
      rw [← hu, ha1]
      simp
    have hge := P5.finrank_range_sub_one_ge hK4 ψ a (φ ⟨a, haH⟩).2 hne
      (fun v => hψ ⟨a, haH⟩ v)
    rw [GaloisField.finrank 2 (by norm_num)] at hge
    omega

end SzG11S

end G11

end CFSG.Quasithin
