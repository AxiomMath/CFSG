module

public import CFSG.Quasithin.H13.L32NLem1449h
public import CFSG.Quasithin.H13.L32NItems144d
public import CFSG.Quasithin.H13.L32NItems144e
public import CFSG.Quasithin.H13.L32NLem1449a

public section

namespace CFSG.Quasithin.H13.L1449

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L144B Q1449Cert

theorem lemma1449Big_of_inputs
    (h1447 : Lemma1447Big) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK)
    (hΔ : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
      CFSG.SectionRank.IsSQTKCat X → CFSG.pCore 2 X = ⊥ →
        CFSG.QuasithinUnique.A5.G3.NoDelta5In X) : Lemma1449Big := by
  intro G _ _ T L V h hext hU32 V₂ g hV₂ hgP hgH D h3
  have B := exists_base h1332 h1334 h1222 h12213 (lemma12_8_11_of h1222 h12213)
    (lemma12_8_12_two_of h1222 h12213) h37 h38 h39 h hext hV₂ hgP hgH
  obtain ⟨e, c, C3⟩ := L1447.exists_ctx3 B h3
  have hU := h1447 G T L V h hext hU32
  obtain ⟨_, S⟩ := B.set14
  obtain ⟨z, -, -, hz, hz1, -⟩ := S.exists_basis
  obtain ⟨x₀, hx₀, -⟩ := exists_x0 C3.hc
  obtain ⟨i, x, hi, hii, hxi, hstar⟩ := C3.exists_good hz hz1 hx₀
  have C : Good G T L V V₂ g D e c x₀ i :=
    { base := B
      form := C3.form
      yH := hi
      yy := hii
      yStar := hstar
      full := x0_full C3.hc hx₀
      alt := x0_alt C3.hc hx₀
      hc := C3.hc
      hx₀ := hx₀
      imgH := C3.imgH
      hU := hU }
  exact C.false_of h36 h37 h39 hΔ hz hz1 hxi

end CFSG.Quasithin.H13.L1449
