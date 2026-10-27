module

public import CFSG.Quasithin.Vol2.Ch9L34M64D
public import CFSG.Quasithin.Vol2.Ch9L34NormGen
public import CFSG.Quasithin.Vol2.Ch9L34Ech

public section

namespace CFSG.Quasithin.H13.Ch9.L34N

open CFSG.Fischer Matrix CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.Ch9.Herm9
open CFSG.Quasithin.H13.Ch9.L34M

@[expose] def w0C64 : List ℕ := colsN64 (codes8 (adGL w0GL))

@[expose] def st64 (w : ℕ) : ℕ :=
  stack4 64 (tabX12_64.getD 1 []) (tabX12_64.getD 2 []) (tabX23_64.getD 1 [])
    (tabX23_64.getD 2 []) w

@[expose] def ker64 : List ℕ := echKer 64 st64

@[expose] def orb64 : List ℕ :=
  (List.range 64).map fun p => actM (tabU64.getD p []) (actM w0C64 512)

@[expose] def chkN64 : Bool :=
  (ker64.length == 63) && AllLt 64 ker64 && echOK (ker64.map st64) &&
    (actM (tabX12_64.getD 1 []) 512 == 512) && (actM (tabX12_64.getD 2 []) 512 == 512) &&
    (actM (tabX23_64.getD 1 []) 512 == 512) && (actM (tabX23_64.getD 2 []) 512 == 512) &&
    combOK orb64 (echComb orb64) && pivOK 64 ((echComb orb64).map Prod.fst) &&
    (actM (tabX12_64.getD 1 []) (actM (tabX23_64.getD 1 []) 4) !=
      actM (tabX23_64.getD 1 []) (actM (tabX12_64.getD 1 []) 4))

theorem chkN64_spec (h : chkN64 = true) :
    (ker64.length = 63 ∧ AllLt 64 ker64 = true ∧ echOK (ker64.map st64) = true) ∧
      (actM (tabX12_64.getD 1 []) 512 = 512 ∧ actM (tabX12_64.getD 2 []) 512 = 512 ∧
        actM (tabX23_64.getD 1 []) 512 = 512 ∧ actM (tabX23_64.getD 2 []) 512 = 512) ∧
      combOK orb64 (echComb orb64) = true ∧ pivOK 64 ((echComb orb64).map Prod.fst) = true ∧
      actM (tabX12_64.getD 1 []) (actM (tabX23_64.getD 1 []) 4) ≠
        actM (tabX23_64.getD 1 []) (actM (tabX12_64.getD 1 []) 4) := by
  simp only [chkN64, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6, h7⟩, h8, h9, h10⟩

end CFSG.Quasithin.H13.Ch9.L34N
