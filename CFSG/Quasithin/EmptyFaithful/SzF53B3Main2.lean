module

public import CFSG.Quasithin.EmptyFaithful.SzF53B3NMain
public import CFSG.Quasithin.EmptyFaithful.SzF53B3EMain
public import CFSG.Quasithin.EmptyFaithful.SzF53B3Dich2
public import CFSG.Quasithin.EmptyFaithful.SzF53B3Conj
public import CFSG.Quasithin.EmptyFaithful.SzF53B3O1Main
public import CFSG.Quasithin.EmptyFaithful.SzF53B3O2Main
public import CFSG.Quasithin.EmptyFaithful.SzF53B3O3Final
public import CFSG.Quasithin.EmptyFaithful.SzF53B3O4Main

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53 CFSG.Quasithin.F53Mod
open CFSG.Quasithin.CosetGeom

namespace F53B3

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem no_E_of_dich2 (hA : F53Amalgam H M S) (hd : F53DichAt2 H M) (hb : bMin H M = 3)
    (h1 : bAt (γ₁ (H ⊔ M) H M) = bMin H M) {E : Subgroup G} (hE : F53EData H S E) : False := by
  obtain ⟨hbase, hsec⟩ := base_of_dich2 hA hd hb h1
  rcases hsec with hn | ho
  · have hB : B3Facts H M S := ⟨hbase, isNatSec_all hA vtype_γ₀ hn⟩
    have hBl : B3Block H M S := blockFacts hB
    refine no_E_of_fixed hB hBl (fun β hβ => n37 hB hBl (fun F L X h => h.relIndex_eq)
      (fun F L X h hLX a ha ha1 ha2 => IsNatSec.involution h hLX ha ha1 ha2)
      (fun F L X S₀ h hS U hLU hUX hn h4 => IsNatSec.centralizer_l2 h hS hLU hUX hn h4)
      (fun K U A B hq hUK hUQ hs hnc a ha haQ ha2 haA =>
        two_lt_secIdx_of_A5_involution hq hUK hUQ hs hnc ha haQ ha2 haA) hβ)
      (fun F L X h d hd hd1 hd3 => IsNatSec.no_fixed_of_three h hd hd1 hd3)
      (fun F L X h d hd hd1 hd3 => IsOrthSec.exists_fixed_of_three h hd hd1 hd3) hE
  · have hB : B3FactsO H M S := ⟨hbase, isOrthSec_all hA vtype_γ₀ ho⟩
    have hBl : B3Block H M S := blockFactsO hB
    have hC1 : OrthC1 H M S := orthC1 hB
    have hS4 : OrthS4 H M S := orthS4 hB hBl hC1
    exact no_E_orth hB hBl hC1 (fun β hβ => n37_orth_of_C1_S4 hB hBl hC1 hS4 hβ) hE

end F53B3

end CFSG.Quasithin
