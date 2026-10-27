module

public import CFSG.Quasithin.H13.NQCoreP134X27
public import CFSG.Quasithin.Background.F6CatSetting

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique.Vol2Native

@[expose] def NoX27ConfigQ (F : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L P T : Subgroup A), OddConfig 3 L P T → Nat.card P = 27 →
    (Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = 3) →
    F (↥L ⧸ Subgroup.center ↥L) → False

structure Facts134X27 : Prop where
  alt : ∀ n : ℕ, 5 ≤ n → n ≤ 8 →
    NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* alternatingGroup (Fin n))
  psl2Odd : ∀ r f : ℕ, r.Prime → r ≠ 2 → (f = 1 ∨ f = 2) →
    NoX27ConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSL 2 r f
  psl3Odd : ∀ r : ℕ, r.Prime → r ≠ 2 →
    NoX27ConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 r 1
  psu3Odd : ∀ r : ℕ, r.Prime → r ≠ 2 →
    NoX27ConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 r 1
  psl2Even : ∀ f : ℕ, 2 ≤ f →
    NoX27ConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSL 2 2 f
  psl3Even : ∀ f : ℕ, 1 ≤ f →
    NoX27ConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 2 f
  psu3Even : ∀ f : ℕ, 2 ≤ f →
    NoX27ConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 2 f
  psp4Even : ∀ f : ℕ, 2 ≤ f →
    NoX27ConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSp 2 2 f
  g2Even : ∀ f : ℕ, 2 ≤ f →
    NoX27ConfigQ fun (X : Type) [Group X] => ChevalleyExceptionalModel X .G2 2 f
  d4Even : ∀ f : ℕ, 1 ≤ f →
    NoX27ConfigQ fun (X : Type) [Group X] => ChevalleyExceptionalModel X .trialityD4 2 f
  f4Even : ∀ f : ℕ, Odd f → 3 ≤ f →
    NoX27ConfigQ fun (X : Type) [Group X] => ReeTitsModel X .twistedF4 2 f
  sz : ∀ f : ℕ, Odd f → 3 ≤ f →
    NoX27ConfigQ fun (X : Type) [Group X] => SuzukiModel X 2 f
  tits : NoX27ConfigQ fun (X : Type) [Group X] => ReeTitsModel X .Tits 2 1
  psl45 : ∀ n : ℕ, (n = 4 ∨ n = 5) →
    NoX27ConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSL n 2 1
  m11 : NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M11)
  m12 : NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M12)
  m22 : NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M22)
  m23 : NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M23)
  m24 : NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M24)
  j1 : NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J1)
  j2 : NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J2)
  j4 : NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J4)
  hs : NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .HS)
  he : NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .He)
  ru : NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .Ru)

theorem noThreeExtraspecialConfig_of_facts (hC : F6.NativeTheoremCSection)
    (h36 : A36CoreForSQTKCat) (hF : Facts134X27) : NoThreeExtraspecialConfig := by
  intro A _ _ L P T hcfg h27
  have hq : CFSG.IsQuasisimple ↥L := hcfg.component.1
  have hLc : L ∈ cComp (⊤ : Subgroup A) := mem_cComp_top_of_isComponent hcfg.component
  have hZ := card_center_of_a36Common' hq (h36 A hcfg.hyp L hLc).2.1
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2.1
  have hlist := hC A ⟨hcfg.hyp.sqt, hcfg.hyp.kgroup⟩ L (Subgroup.center ↥L) hq.2.2
  rcases hlist with ⟨n, h5, h8, ⟨e⟩⟩ | ⟨r, hr, hr2, h⟩ | ⟨⟨f, h⟩ | h⟩ | ⟨n, hn, h⟩ | ⟨s, hs, ⟨e⟩⟩
  · exact hF.alt n h5 h8 A L P T hcfg h27 hZ ⟨e⟩
  · rcases h with ⟨f, hf, h⟩ | h | h
    · exact hF.psl2Odd r f hr hr2 hf A L P T hcfg h27 hZ h
    · exact hF.psl3Odd r hr hr2 A L P T hcfg h27 hZ h
    · exact hF.psu3Odd r hr hr2 A L P T hcfg h27 hZ h
  · rcases h with h | h | h | h | h | h | h | h
    · exact hF.psl2Even f h.1 A L P T hcfg h27 hZ h.2
    · exact hF.psl3Even f h.1 A L P T hcfg h27 hZ h.2
    · exact hF.psu3Even f h.1 A L P T hcfg h27 hZ h.2
    · exact hF.psp4Even f h.1 A L P T hcfg h27 hZ h.2
    · exact hF.g2Even f h.1 A L P T hcfg h27 hZ h.2
    · exact hF.d4Even f h.1 A L P T hcfg h27 hZ h.2
    · exact hF.f4Even f h.1 h.2.1 A L P T hcfg h27 hZ h.2.2
    · exact hF.sz f h.1 h.2.1 A L P T hcfg h27 hZ h.2.2
  · exact hF.tits A L P T hcfg h27 hZ h
  · exact hF.psl45 n hn A L P T hcfg h27 hZ h
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hF.m11 A L P T hcfg h27 hZ ⟨e⟩
    · exact hF.m12 A L P T hcfg h27 hZ ⟨e⟩
    · exact hF.m22 A L P T hcfg h27 hZ ⟨e⟩
    · exact hF.m23 A L P T hcfg h27 hZ ⟨e⟩
    · exact hF.m24 A L P T hcfg h27 hZ ⟨e⟩
    · exact hF.j1 A L P T hcfg h27 hZ ⟨e⟩
    · exact hF.j2 A L P T hcfg h27 hZ ⟨e⟩
    · exact hF.j4 A L P T hcfg h27 hZ ⟨e⟩
    · exact hF.hs A L P T hcfg h27 hZ ⟨e⟩
    · exact hF.he A L P T hcfg h27 hZ ⟨e⟩
    · exact hF.ru A L P T hcfg h27 hZ ⟨e⟩

theorem prop134ThreeExtraspecial_of_facts (h36 : A36CoreForSQTKCat) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (hO3 : OutThreeFact) (hOA : OutAbelianFact)
    (hC : F6.NativeTheoremCSection) (hF : Facts134X27) : Prop134ThreeExtraspecial :=
  prop134ThreeExtraspecial_of_noConfig h36 h37 h38 hO3 hOA
    (noThreeExtraspecialConfig_of_facts hC h36 hF)

end CFSG.Quasithin.H13.NQCore
