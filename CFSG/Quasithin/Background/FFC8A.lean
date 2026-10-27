module

public import CFSG.Quasithin.Background.FFC4Ext
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.Quasithin.Background.FFC4Pair
public import CFSG.Quasithin.Background.FFC4Zmod
public import CFSG.Quasithin.Background.FFC5Case1
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section List

variable {V : Type} [CommGroup V]

omit [CommGroup V] in
theorem B56QuasisimpleList.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : B56QuasisimpleList Y) : B56QuasisimpleList X := by
  rcases h with ⟨n, K, hK, hf, hc, ⟨e'⟩⟩ | ⟨n, K, hK, hf, hc, ⟨e'⟩⟩ | ⟨n, K, hK, hf, hc, ⟨e'⟩⟩ |
    ⟨n, K, hK, hf, hc, ⟨e'⟩⟩ | h5 | h6 | h7 | ⟨K, hK, hf, hc, ⟨e'⟩⟩ | h9 | h10
  · exact Or.inl ⟨n, K, hK, hf, hc, ⟨e.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨n, K, hK, hf, hc, ⟨e.trans e'⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, K, hK, hf, hc, ⟨e.trans e'⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, K, hK, hf, hc, ⟨e.trans e'⟩⟩)))
  · obtain ⟨e'⟩ := h5
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans e'⟩))))
  · obtain ⟨e'⟩ := h6
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans e'⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (IsHat.of_mulEquiv e.symm h7)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨K, hK, hf, hc, ⟨e.trans e'⟩⟩)))))))
  · obtain ⟨e'⟩ := h9
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨e.trans e'⟩))))))))
  · obtain ⟨e'⟩ := h10
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨e.trans e'⟩))))))))

@[expose] noncomputable def equivOfRealizes {V : Type*} [CommGroup V] {D : FFModel} (hD : D.Faithful)
    {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : D.Gam →* ↥H}
    (h : D.RealizesVia H U Z π) : D.Gam ≃* ↥H :=
  MulEquiv.ofBijective π ⟨injective_of_faithful_sec hD h, h.1⟩

variable {L : Subgroup (MulAut V)} {U Z : Subgroup V}

theorem b56List_sp4 {n : ℕ} (h : BinaryNaturalSp4 L U Z n) : B56QuasisimpleList ↥L := by
  obtain ⟨K, hK, hf, hc, π, hπ⟩ := h
  exact Or.inr (Or.inr (Or.inl ⟨n, K, hK, hf, hc,
    ⟨(equivOfRealizes (FFModel.nat_faithful _) hπ).symm⟩⟩))

theorem b56List_g2 {n : ℕ} (h : G2Natural L U Z n) : B56QuasisimpleList ↥L := by
  obtain ⟨K, hK, hf, hc, π, hπ⟩ := h
  have := charP_two_of_card_pow hc
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, K, hK, hf, hc,
    ⟨(equivOfRealizes (zornQ_faithful _ le_rfl) hπ).symm⟩⟩)))

theorem b56List_g2d (h : G2NaturalDerived L U Z 1) : B56QuasisimpleList ↥L := by
  obtain ⟨K, hK, hf, hc, π, hπ⟩ := h
  have := charP_two_of_card_pow hc
  have hΓ : ⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ ≤ CFSG.Open.quasithinG2 K := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact (CFSG.Open.quasithinG2 K).mul_mem
      ((CFSG.Open.quasithinG2 K).mul_mem ((CFSG.Open.quasithinG2 K).mul_mem ha hb)
        ((CFSG.Open.quasithinG2 K).inv_mem ha)) ((CFSG.Open.quasithinG2 K).inv_mem hb)
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨K, hK, hf,
    by simpa using hc, ⟨(equivOfRealizes (zornQ_faithful _ hΓ) hπ).symm⟩⟩))))))) 

theorem b56List_alt5 (h : AlternatingNatural L U Z 5) : B56QuasisimpleList ↥L := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨e₀, -⟩ := A5Model.exists_mulEquiv_A5_SL2_four
  exact Or.inl ⟨2, GaloisField 2 2, inferInstance, inferInstance, by simpa using A5Model.card_gf4,
    ⟨(equivOfRealizes (altDn_faithful (by norm_num)) hπ).symm.trans (e₀.trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 (GaloisField 2 2)))⟩⟩

theorem b56List_alt6 (h : AlternatingNatural L U Z 6) : B56QuasisimpleList ↥L := by
  obtain ⟨π, hπ⟩ := h
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨(equivOfRealizes (altDn_faithful (by norm_num)) hπ).symm⟩))))

theorem b56List_alt7 (h : AlternatingNatural L U Z 7) : B56QuasisimpleList ↥L := by
  obtain ⟨π, hπ⟩ := h
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨(equivOfRealizes (altDn_faithful (by norm_num)) hπ).symm⟩)))))

theorem b56List_a7Four (h : A7Four L U Z) : B56QuasisimpleList ↥L := by
  obtain ⟨α, π, hπ⟩ := h
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨(equivOfRealizes (a7Four_faithful α) hπ).symm⟩)))))

theorem b56List_tripleA6 (h : TripleA6Six L U Z) : B56QuasisimpleList ↥L := by
  obtain ⟨K, hK, hf, Γ₀, hc, -, hhat, -, π, hπ⟩ := h
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    (IsHat.of_mulEquiv (equivOfRealizes (FFModel.nat_faithful _) hπ) hhat)))))))

theorem b56List_sl4 (h : BinaryNaturalSL L U Z 4 1) : B56QuasisimpleList ↥L := by
  obtain ⟨π, hπ⟩ := BinaryNaturalSL.exists_zmod h
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨(equivOfRealizes (FFModel.nat_faithful _) hπ).symm⟩))))))))

theorem b56List_sl5 (h : BinaryNaturalSL L U Z 5 1) : B56QuasisimpleList ↥L := by
  obtain ⟨π, hπ⟩ := BinaryNaturalSL.exists_zmod h
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨(equivOfRealizes (FFModel.nat_faithful _) hπ).symm⟩))))))))

theorem b56List_ext4 (h : SLExteriorTwo L U Z 4) : B56QuasisimpleList ↥L := by
  obtain ⟨π, hπ⟩ := h
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨(equivOfRealizes (extSq_faithful (by norm_num)) hπ).symm⟩))))))))

theorem b56List_ext5 (h : SLExteriorTwo L U Z 5) : B56QuasisimpleList ↥L := by
  obtain ⟨π, hπ⟩ := h
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨(equivOfRealizes (extSq_faithful (by norm_num)) hπ).symm⟩))))))))

theorem b56List_of_pair (h : B42ModulePair L U Z) : B56QuasisimpleList ↥L := by
  rcases h with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h | h | h | h | h | h | h
  · exact b56List_sl2 h
  · exact b56List_sl3 h
  · exact b56List_sp4 h
  · exact b56List_g2 h
  · exact b56List_g2d h
  · exact b56List_alt5 h
  · exact b56List_alt6 h
  · exact b56List_alt7 h
  · exact b56List_a7Four h
  · exact b56List_tripleA6 h
  · exact b56List_sl4 h
  · exact b56List_sl5 h
  · exact b56List_ext4 h
  · exact b56List_ext5 h

end List

section B51

variable {V : Type} [CommGroup V] [Finite V]

theorem b56List_of_b51 {X K : Subgroup (MulAut V)} (hc : B51Conclusion X K) :
    B56QuasisimpleList ↥K := by
  obtain ⟨⟨-, hcases⟩, -⟩ := hc
  rcases hcases with ⟨-, hpair, -⟩ | hii | ⟨n, hiii⟩ | hiv
  · exact b56List_of_pair hpair
  · obtain ⟨-, n, K', hK', hf, hcard, I, π, -, -, hreal, -⟩ := hii
    exact b56List_sl3 (n := n) ⟨K', hK', hf, hcard, π, hreal 0⟩
  · obtain ⟨-, hn, π, U₁, U₂, -, h1, -⟩ := hiii
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨(equivOfRealizes (FFModel.nat_faithful _) h1).symm⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨(equivOfRealizes (FFModel.nat_faithful _) h1).symm⟩))))))))
  · obtain ⟨-, n, hn, k, hk1, hkn, I, π, -, -, -, hreal⟩ := hiv
    have h1 := hreal ⟨0, by omega⟩
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨(equivOfRealizes (FFModel.nat_faithful _) h1).symm⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨(equivOfRealizes (FFModel.nat_faithful _) h1).symm⟩))))))))

end B51

end FFC

end CFSG.Quasithin
