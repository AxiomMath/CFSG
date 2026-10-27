
module

public import Certificates.Data.DcHS
import Certificates.Kernel.HS589206.Facts
import Certificates.Kernel.HS589206.E16Fix

public section

open CFSG.Quasithin.H13.LocDbl.HSLoc CFSG.Quasithin.H13.LocDbl.DcNative

public section

namespace Certificates

open CFSG.KD.HS589206

open CFSG.Quasithin.H13.LocDbl.HSLoc CFSG.Quasithin.H13.LocDbl.DcNative in
theorem certificate589206 :
    subEnumOK 100 B100 11520 12000 mTabs = true ∧ treeOK = true ∧ mPres = true ∧ kCount = true ∧
      kInM = true ∧ kUOK = true ∧ CFSG.Quasithin.H13.LocDbl.HSLoc.centOK = true ∧ centWOK = true ∧
      ∀ E : Subgroup (Equiv.Perm (Fin 100)), E ≤ CFSG.RankThree.Native.hs100P →
        (∀ x ∈ E, x ^ 2 = 1) → Nat.card E = 16 → ∀ y ∈ CFSG.RankThree.Native.hs100P,
        orderOf y = 5 → (∀ x ∈ E, y * x * y⁻¹ ∈ E) → ∃ X ∈ CFSG.RankThree.Native.hs100P,
        ∀ q : Fin 100, (∀ z ∈ E, z q = q) ↔ ∃ f : Fin 100, (f : ℕ) ∈ F0 ∧ X f = q :=
  ⟨E16Tabs.enum_M, Facts.tree_ok, Facts.m_pres, Facts.k_count, Facts.k_in_m, Facts.k_u_ok,
    Facts.cent_ok, Facts.cent_w_ok, E16Fix.e16Fix⟩

end Certificates

end

end
