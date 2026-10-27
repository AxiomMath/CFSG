module

public import CFSG.Blueprint.NativeSporadic
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
import CFSG.LocalAnalysis.QuasithinUnique.Setting
import CFSG.Sporadic.HS
import Certificates.Certificate3167
import Certificates.Certificate4102
import Certificates.Certificate4140

public section

open CFSG.Blueprint CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat

namespace Certificates

theorem certificate7087 : ∀ (T : Sylow 2 CFSG.Blueprint.NativeSporadic.HS)
    (W : Subgroup CFSG.Blueprint.NativeSporadic.HS), (T : Subgroup _) ≤ W →
    Nat.card W ∈ ({512, 1536, 7680, 10752, 44352000} : Finset ℕ) := by
  intro T W hTW
  rcases HS.hs_overgroups (X := NativeSporadic.HS) ⟨MulEquiv.refl _⟩
      (isSylowTwoOf_top_of_sylow T) hTW with h | ⟨m, hm, hc, -, -⟩
  · subst h
    rw [Subgroup.card_top, CFSG.Sporadic.HS.card_HS]
    decide
  · rw [hc]
    simp only [HS.hsMems, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> decide

end Certificates
