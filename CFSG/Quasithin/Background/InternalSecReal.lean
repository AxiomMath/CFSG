module

public import CFSG.Quasithin.Background.B5Sec
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.InternalSecBasic

public section

namespace CFSG.Quasithin.InternalSec

open CFSG.Open CFSG.Assembly.LowTwoRank

section Real

variable {V : Type} [CommGroup V] {K : Subgroup (MulAut V)} {C : Subgroup V}
  (hK : K ≤ stabSub C) (hf : K ⊓ centSec ⊤ C = ⊥)

include hK hf

theorem realizesVia_top_of_autSec {D : FFModel} {π' : D.Gam →* ↥(autSec K ⊤ C)}
    (h : D.RealizesVia (autSec K ⊤ C) ⊤ ⊥ π') :
    D.RealizesVia K ⊤ C ((B5.secEquiv K (le_stabSub_top K) hK hf).symm.toMonoidHom.comp π') :=
  B5.realizesVia_of_autSec le_top (le_stabSub_top K) hK hf h

theorem realizes_of_autSec {D : FFModel} (h : D.Realizes (autSec K ⊤ C) ⊤ ⊥) :
    D.Realizes K ⊤ C := by
  obtain ⟨π', hπ'⟩ := h
  exact ⟨_, realizesVia_top_of_autSec hK hf hπ'⟩

theorem binaryNaturalSL_of_autSec {d a : ℕ} (h : BinaryNaturalSL (autSec K ⊤ C) ⊤ ⊥ d a) :
    BinaryNaturalSL K ⊤ C d a := by
  obtain ⟨F, _, _, hc, hR⟩ := h
  exact ⟨F, inferInstance, inferInstance, hc, realizes_of_autSec hK hf hR⟩

theorem binaryNaturalSp4_of_autSec {a : ℕ} (h : BinaryNaturalSp4 (autSec K ⊤ C) ⊤ ⊥ a) :
    BinaryNaturalSp4 K ⊤ C a := by
  obtain ⟨F, _, _, hc, hR⟩ := h
  exact ⟨F, inferInstance, inferInstance, hc, realizes_of_autSec hK hf hR⟩

theorem binaryNaturalSU3_of_autSec {a : ℕ} (h : BinaryNaturalSU3 (autSec K ⊤ C) ⊤ ⊥ a) :
    BinaryNaturalSU3 K ⊤ C a := by
  obtain ⟨F, _, _, hc, hR⟩ := h
  exact ⟨F, inferInstance, inferInstance, hc, realizes_of_autSec hK hf hR⟩

theorem binaryNaturalSz_of_autSec {f : ℕ} (h : BinaryNaturalSz (autSec K ⊤ C) ⊤ ⊥ f) :
    BinaryNaturalSz K ⊤ C f := by
  obtain ⟨a, ha, hfa, F, _, _, hc, hR⟩ := h
  exact ⟨a, ha, hfa, F, inferInstance, inferInstance, hc, realizes_of_autSec hK hf hR⟩

theorem g2Natural_of_autSec {a : ℕ} (h : G2Natural (autSec K ⊤ C) ⊤ ⊥ a) :
    G2Natural K ⊤ C a := by
  obtain ⟨F, _, _, hc, hR⟩ := h
  exact ⟨F, inferInstance, inferInstance, hc, realizes_of_autSec hK hf hR⟩

theorem g2NaturalDerived_of_autSec {a : ℕ} (h : G2NaturalDerived (autSec K ⊤ C) ⊤ ⊥ a) :
    G2NaturalDerived K ⊤ C a := by
  obtain ⟨F, _, _, hc, hR⟩ := h
  exact ⟨F, inferInstance, inferInstance, hc, realizes_of_autSec hK hf hR⟩

theorem alternatingNatural_of_autSec {n : ℕ} (h : AlternatingNatural (autSec K ⊤ C) ⊤ ⊥ n) :
    AlternatingNatural K ⊤ C n :=
  realizes_of_autSec hK hf h

theorem symmetricNatural_of_autSec {n : ℕ} (h : SymmetricNatural (autSec K ⊤ C) ⊤ ⊥ n) :
    SymmetricNatural K ⊤ C n :=
  realizes_of_autSec hK hf h

theorem a7Four_of_autSec (h : A7Four (autSec K ⊤ C) ⊤ ⊥) : A7Four K ⊤ C := by
  obtain ⟨α, hR⟩ := h
  exact ⟨α, realizes_of_autSec hK hf hR⟩

theorem tripleA6Six_of_autSec (h : TripleA6Six (autSec K ⊤ C) ⊤ ⊥) : TripleA6Six K ⊤ C := by
  obtain ⟨F, _, _, Γ₀, hc, hdet, hhat, hcen, hR⟩ := h
  exact ⟨F, inferInstance, inferInstance, Γ₀, hc, hdet, hhat, hcen, realizes_of_autSec hK hf hR⟩

theorem slExteriorTwo_of_autSec {d : ℕ} (h : SLExteriorTwo (autSec K ⊤ C) ⊤ ⊥ d) :
    SLExteriorTwo K ⊤ C d :=
  realizes_of_autSec hK hf h

theorem twistedTensorSL_of_autSec {d a : ℕ} (h : TwistedTensorSL (autSec K ⊤ C) ⊤ ⊥ d a) :
    TwistedTensorSL K ⊤ C d a := by
  obtain ⟨F, _, _, _, hc, hR⟩ := h
  exact ⟨F, inferInstance, inferInstance, inferInstance, hc, realizes_of_autSec hK hf hR⟩

theorem twistedTensorSp4_of_autSec {a : ℕ} (h : TwistedTensorSp4 (autSec K ⊤ C) ⊤ ⊥ a) :
    TwistedTensorSp4 K ⊤ C a := by
  obtain ⟨F, _, _, _, hc, hR⟩ := h
  exact ⟨F, inferInstance, inferInstance, inferInstance, hc, realizes_of_autSec hK hf hR⟩

theorem binaryNineTensor_of_autSec {a : ℕ} (h : BinaryNineTensor (autSec K ⊤ C) ⊤ ⊥ a) :
    BinaryNineTensor K ⊤ C a :=
  twistedTensorSL_of_autSec hK hf h

theorem binaryOrthogonalFour_of_autSec {a : ℕ}
    (h : BinaryOrthogonalFour (autSec K ⊤ C) ⊤ ⊥ a) : BinaryOrthogonalFour K ⊤ C a :=
  twistedTensorSL_of_autSec hK hf h

theorem m12Ten_of_autSec (h : M12Ten (autSec K ⊤ C) ⊤ ⊥) : M12Ten K ⊤ C := by
  obtain ⟨eY, h1, h2, hR⟩ := h
  exact ⟨eY, h1, h2, realizes_of_autSec hK hf hR⟩

theorem mhat22Twelve_of_autSec (h : Mhat22Twelve (autSec K ⊤ C) ⊤ ⊥) : Mhat22Twelve K ⊤ C := by
  obtain ⟨F, _, _, Γ₀, hc, hhat, hB, hR⟩ := h
  exact ⟨F, inferInstance, inferInstance, Γ₀, hc, hhat, hB, realizes_of_autSec hK hf hR⟩

theorem mathieuCode22_of_autSec (h : MathieuCode22 (autSec K ⊤ C) ⊤ ⊥) :
    MathieuCode22 K ⊤ C := by
  obtain ⟨x, y, hxy, hR⟩ := h
  exact ⟨x, y, hxy, realizes_of_autSec hK hf hR⟩

theorem mathieuCocode22_of_autSec (h : MathieuCocode22 (autSec K ⊤ C) ⊤ ⊥) :
    MathieuCocode22 K ⊤ C := by
  obtain ⟨x, y, hxy, hR⟩ := h
  exact ⟨x, y, hxy, realizes_of_autSec hK hf hR⟩

theorem mathieuCode23_of_autSec (h : MathieuCode23 (autSec K ⊤ C) ⊤ ⊥) :
    MathieuCode23 K ⊤ C := by
  obtain ⟨x, hR⟩ := h
  exact ⟨x, realizes_of_autSec hK hf hR⟩

theorem mathieuCocode23_of_autSec (h : MathieuCocode23 (autSec K ⊤ C) ⊤ ⊥) :
    MathieuCocode23 K ⊤ C := by
  obtain ⟨x, hR⟩ := h
  exact ⟨x, realizes_of_autSec hK hf hR⟩

theorem mathieuCode24_of_autSec (h : MathieuCode24 (autSec K ⊤ C) ⊤ ⊥) :
    MathieuCode24 K ⊤ C :=
  realizes_of_autSec hK hf h

theorem mathieuCocode24_of_autSec (h : MathieuCocode24 (autSec K ⊤ C) ⊤ ⊥) :
    MathieuCocode24 K ⊤ C :=
  realizes_of_autSec hK hf h

theorem j2Twelve_of_autSec (h : J2Twelve (autSec K ⊤ C) ⊤ ⊥) : J2Twelve K ⊤ C := by
  obtain ⟨F, _, _, Γ₀, hc, hle, hR⟩ := h
  exact ⟨F, inferInstance, inferInstance, Γ₀, hc, hle, realizes_of_autSec hK hf hR⟩

theorem b42ModulePair_of_autSec (h : B42ModulePair (autSec K ⊤ C) ⊤ ⊥) :
    B42ModulePair K ⊤ C := by
  rcases h with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl ⟨n, binaryNaturalSL_of_autSec hK hf h⟩
  · exact Or.inr (Or.inl ⟨n, binaryNaturalSL_of_autSec hK hf h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, binaryNaturalSp4_of_autSec hK hf h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, g2Natural_of_autSec hK hf h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (g2NaturalDerived_of_autSec hK hf h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (alternatingNatural_of_autSec hK hf h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (alternatingNatural_of_autSec hK hf h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (alternatingNatural_of_autSec hK hf h))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (a7Four_of_autSec hK hf h)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (tripleA6Six_of_autSec hK hf h))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (binaryNaturalSL_of_autSec hK hf h)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl (binaryNaturalSL_of_autSec hK hf h))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl (slExteriorTwo_of_autSec hK hf h)))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (slExteriorTwo_of_autSec hK hf h)))))))))))))

end Real

end CFSG.Quasithin.InternalSec
