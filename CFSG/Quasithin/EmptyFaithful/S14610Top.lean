module

public import CFSG.Quasithin.EmptyFaithful.S14610Facts3
public import CFSG.Quasithin.EmptyFaithful.S14610C4
public import CFSG.Quasithin.EmptyFaithful.S14610Hat6
public import CFSG.Quasithin.EmptyFaithful.S14610Perm
public import CFSG.Quasithin.EmptyFaithful.S14610C12

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem stage14610FiveW_of_named_inputs (h9 : Stage1469W) (hF618 : F6.TheoremF618Cat)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (h1 : Stage1463One) (h2 : Stage1463Two) (h3 : Stage1463Three) (h4 : Stage1463Four)
    (i10 : Input14610Four) (i11 : Input14610List) (i12 : Input14610L32) (i13 : Input14610Hat6)
    (i14 : Input14610G22) (i15 : Input14610Rank4) (i16 : Input14610PermFixed)
    (i17 : Input14610PermTu) : Stage14610FiveW := by
  intro G _ _ T M H u S hH hu I hI hbig hrank I₂ hle hI₂ hs3 hgen hcent
  have c : Hyp14610 T M H u I I₂ :=
    ⟨S, hH, hu, hI, hbig, hrank, hle, hI₂, hs3, hgen, hcent⟩
  have hidx := (h1 G T M S H hH u hu).2.1
  have hN0 := h2 G T M S H hH u hu
  have hNu := (h4 G T M S H hH u hu).1
  obtain ⟨hsyl, hcases⟩ := isIStar_sylow_cases S hu hidx hN0 hNu hI
  have hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T) :=
    h9 G T M H u S hH hu I hI hbig hrank
  have hc1 := S.facts14610_c1 hI hsyl hLT
  have hc2 := S.facts14610_c2 hI hsyl hgen hc1
  have hc3 := fun P hPI hPinv => Setting146.facts14610_c3 h9 h3 c hsyl hLT P hPI hPinv
  have hc4 := Setting146.facts14610_c4 hF618 i10 c hsyl hLT hc2
  let cF : Facts14610 T M H u I I₂ := { c with c1 := hc1, c2 := hc2, c3 := hc3, c4 := hc4 }
  have hT := S.isGoldschmidtTripleIn_14610 c hsyl hLT
  have hF := S.f618Cat_14610 hF618 c hsyl hLT hc2
  obtain ⟨K, hK⟩ := i11 G T M H u I I₂ (hC27 G) cF hT hF
  rcases hK.shape with ⟨hL32, -⟩ | ⟨-, hHat | hG2 | hA6 | hA7⟩
  · exact i12 G T M H u I I₂ K cF hK hL32
  · exact (Setting146.facts14610_hat6 i13 cF hK hHat.1).elim
  · exact i14 G T M H u I I₂ K cF hK hG2.1
  · rcases hA6.2.2 with hW | hW
    · exact i15 G T M H u I I₂ K cF hK (Or.inl hA6.1) hW
    · exact Setting146.facts14610_perm i16 i17 cF hsyl hcases hLT hK (Or.inl ⟨hA6.1, hW⟩)
  · rcases hA7.2.2 with hW | hW
    · exact i15 G T M H u I I₂ K cF hK (Or.inr hA7.1) hW
    · exact Setting146.facts14610_perm i16 i17 cF hsyl hcases hLT hK (Or.inr ⟨hA7.1, hW⟩)

end CFSG.Quasithin
