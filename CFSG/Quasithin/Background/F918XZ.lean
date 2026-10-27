module

public import CFSG.Quasithin.Background.F918X6
public import CFSG.Quasithin.Background.F918R5
public import CFSG.Quasithin.Background.B5B42
public import CFSG.Quasithin.Background.F918N7

public section

namespace CFSG.Quasithin.F918X

open CFSG.Quasithin CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem d35InspOrbit_of_cases (hA21 : AsA21SQTKSection) (hhat : NoOddCoverHatA6)
    (h1 : Case1Twist) (h2 : Case2Twist) (h3one : Case3TwistOne) (h3big : Case3TwistBig)
    (h4one : Case4TwistOne) (h4big : Case4TwistBig) (h5 : Case5Twist) (h6 : Case6Twist)
    (h7 : Case7Twist) (h8 : Case8Twist) (h9 : Case9Twist) (h10 : Case10Twist)
    (h11 : Case11Twist) : D35InspOrbit := by
  intro X _ _ Mb Tb Lb Vb A hZ hML hA hb42
  have hH := z35_b4Hyp hA21 hZ hML
  have hexp : ∀ w : ↥Vb, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hZ.exp])
  have hCT : CentralData (autSub Lb Vb) ∧ TwoClassMod (autSub Lb Vb) := by
    rcases hb42 with c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | c11
    · obtain ⟨hs, hc⟩ := h1 ↥Vb hexp _ _ _ hH c1
      exact ⟨hc, hs.twoClass⟩
    · obtain ⟨ht, hc⟩ := h2 ↥Vb hexp _ _ hH c2
      exact ⟨hc, ht⟩
    · obtain ⟨⟨n, hn, hJL⟩, -⟩ := c3
      have hn1 : 1 ≤ n := B5.one_le_of_binaryNaturalSp4 hn
      rcases Nat.lt_or_ge 1 n with hlt | hle
      · obtain ⟨ht, hc⟩ := h3big ↥Vb hexp _ _ n hlt hH hn (hJL hlt)
        exact ⟨hc, ht⟩
      · have : n = 1 := le_antisymm hle hn1
        subst this
        obtain ⟨ht, hc⟩ := h3one ↥Vb hexp _ _ hH hn
        exact ⟨hc, ht⟩
    · obtain ⟨⟨n, hn, -, hJL⟩, -⟩ := c4
      have hn1 : 1 ≤ n := B5.one_le_of_g2Natural hn
      rcases Nat.lt_or_ge 1 n with hlt | hle
      · obtain ⟨hs, hc⟩ := h4big ↥Vb hexp _ _ n hlt hH hn (hJL hlt)
        exact ⟨hc, hs.twoClass⟩
      · have : n = 1 := le_antisymm hle hn1
        subst this
        obtain ⟨hs, hc⟩ := h4one ↥Vb hexp _ _ hH hn
        exact ⟨hc, hs.twoClass⟩
    · obtain ⟨hs, hc⟩ := h5 ↥Vb hexp _ _ _ hH c5
      exact ⟨hc, hs.twoClass⟩
    · obtain ⟨ht, hc⟩ := h6 ↥Vb hexp _ _ _ hH c6
      exact ⟨hc, ht⟩
    · obtain ⟨ht, hc⟩ := h7 ↥Vb hexp _ _ _ hH c7
      exact ⟨hc, ht⟩
    · obtain ⟨ht, hc⟩ := h8 ↥Vb hexp _ _ _ hH c8
      exact ⟨hc, ht⟩
    · obtain ⟨ht, hc⟩ := h9 ↥Vb hexp _ _ hH c9
      exact ⟨hc, ht⟩
    · obtain ⟨hs, hc⟩ := h10 ↥Vb hexp _ _ _ hH c10
      exact ⟨hc, hs.twoClass⟩
    · obtain ⟨ht, hc⟩ := h11 ↥Vb hexp _ _ _ hH c11
      exact ⟨hc, ht⟩
  have hinj : Function.Injective (rho hZ hML) := rho_injective hA21 hhat hZ hML hCT.1
  have hstable : (B42Case1 (autSub (Lb ⊔ (Tb ⊓ stabSub Vb)) Vb) (autSub Lb Vb) (autSub A Vb) ∨
        B42Case4 (autSub (Lb ⊔ (Tb ⊓ stabSub Vb)) Vb) (autSub Lb Vb) (autSub A Vb) ∨
        B42Case5 (autSub (Lb ⊔ (Tb ⊓ stabSub Vb)) Vb) (autSub A Vb) ∨
        B42Case10 (autSub (Lb ⊔ (Tb ⊓ stabSub Vb)) Vb) (autSub Lb Vb) (autSub A Vb)) →
      StableMod (autSub Lb Vb) := by
    rintro (c1 | c4 | c5 | c10)
    · exact (h1 ↥Vb hexp _ _ _ hH c1).1
    · obtain ⟨⟨n, hn, -, hJL⟩, -⟩ := c4
      have hn1 : 1 ≤ n := B5.one_le_of_g2Natural hn
      rcases Nat.lt_or_ge 1 n with hlt | hle
      · exact (h4big ↥Vb hexp _ _ n hlt hH hn (hJL hlt)).1
      · have : n = 1 := le_antisymm hle hn1
        subst this
        exact (h4one ↥Vb hexp _ _ hH hn).1
    · exact (h5 ↥Vb hexp _ _ _ hH c5).1
    · exact (h10 ↥Vb hexp _ _ _ hH c10).1
  have hA' := two_of_twoClass hZ hML hinj hCT.2
  have hB' := fun hc => iso_of_stable hZ hML hinj (hstable hc)
  subst hML
  exact ⟨hA', hB'⟩

end CFSG.Quasithin.F918X
