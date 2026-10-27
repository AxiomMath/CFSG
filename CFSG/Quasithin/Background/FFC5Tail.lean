module

public import CFSG.Quasithin.Background.FFC5T10
public import CFSG.Quasithin.Background.FFC5Asm
public import CFSG.Quasithin.Background.FFC5T9

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Tail

theorem nonempty_equiv_of_natural_zmod {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : ↥(StatedSL 3 (ZMod 2)) →* ↥H}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia H U Z π) :
    Nonempty (↥H ≃* ↥(StatedSL 3 (ZMod 2))) :=
  ⟨(MulEquiv.ofBijective π ⟨injective_of_faithful_sec (FFModel.nat_faithful _) hπ, hπ.1⟩).symm⟩

theorem b512Tail : B512Tail := by
  intro V _ _ G G₁ G₂ hc h hG₂ hnat hidx hgood
  have hV := hc.hV
  have hG₁ : G₁ ≠ ⊥ := by
    intro hbot
    obtain ⟨e⟩ := (natural3_facts hnat).1
    have h1 : Nat.card ↥(StatedSL 3 (ZMod 2)) = Nat.card ↥G₁ := (Nat.card_congr e.toEquiv).symm
    rw [hbot, Subgroup.card_bot, CFSG.SectionRank.OddCover.card_statedSL_three, Nat.card_zmod] at h1
    norm_num at h1
  have hs3 : S3Elems ↥G₁ := s3Elems_of_natural3 hnat
  have key : B56Case3 G ∨ B56Case5 G := by
    rcases hgood.2 with ⟨hT₀, hmod⟩ | ⟨hT₀, m, K, hK, hf, hcK, hd⟩ | hC
    · have hT := h.hT_of_top hT₀
      rcases hmod with ⟨n, hn⟩ | hS | ⟨m, hm⟩
      · exact Or.inr (h.case5_sl2 hnat hidx hT (h.binaryNaturalSL_transport hn))
      · exact Or.inl (h.case3_of hV hnat hidx hgood
          (h.hu_of_vanishing hidx (h.vanishing_s5 (h.symmetricNatural_transport hS))))
      · have hm' := h.binaryNaturalSL_transport hm
        rcases Nat.lt_trichotomy m 1 with hlt | rfl | hgt
        · exfalso
          obtain ⟨K, hK, hf, hcK, -⟩ := hm'
          have hm0 : m = 0 := by omega
          have := @Finite.one_lt_card K _ _
          rw [hcK, hm0] at this
          norm_num at this
        · exact h.case_a3_one hV hnat hidx hgood hT hm'
        · obtain ⟨K, hK, hf, hcK, hr⟩ := hm'
          exact Or.inl (h.case3_of hV hnat hidx hgood
            (h.hu_of_vanishing hidx (h.vanishing_natK hcK hgt hr)))
    · have hT := h.hT_of_top hT₀
      have hdG := h.directSum_transport hd
      rcases Nat.lt_trichotomy m 1 with hlt | rfl | hgt
      · exfalso
        have hm0 : m = 0 := by omega
        have := @Finite.one_lt_card K _ _
        rw [hcK, hm0] at this
        norm_num at this
      · have hK1 : Nat.card K = 2 := by simpa using hcK
        obtain ⟨I, π, -, -, -, hreal⟩ := DirectSumOfCopies.zmod hK1 hdG
        have hiso := nonempty_equiv_of_natural_zmod (hreal 0)
        have hex := h.exact_two hc hG₁ hG₂ hs3 hiso hT₀ hd
        exact Or.inr (h.case_b_one hnat hidx hT hex hiso hK1 hdG)
      · obtain ⟨I, π, hZ, hind, hsup, hreal⟩ := hdG
        exact Or.inl (h.case3_of hV hnat hidx hgood
          (h.hu_of_vanishing hidx
            (h.vanishing_natK2 hcK hgt (π := π) ⟨I, hZ, hind, hsup, hreal⟩ (hreal 0).1)))
    · obtain ⟨hiso, -, hcard, hindec, hnatM⟩ := h.pieceC_transport hC
      exact Or.inl (h.case3_of hV hnat hidx hgood (h.exists_u_of_c hV hidx hiso hcard hindec hnatM))
  rcases key with k | k
  · exact hc.not_cases (Or.inr (Or.inr (Or.inl k)))
  · exact hc.not_cases (Or.inr (Or.inr (Or.inr (Or.inr k))))

theorem asB5610_of_offenders
    (hP4 : AsB15Part4) (hB51 : AsB51) (hA21 : AsA21SQTKSection)
    (hOff : B510OffendersAll) : AsB5610 :=
  asB5610_of_inputs hP4 hB51 hA21 hOff b512Tail

end Tail

end FFC

end CFSG.Quasithin
