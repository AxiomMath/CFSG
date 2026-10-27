module

public import CFSG.Quasithin.Vol2.Ch10SecKL7t
public import CFSG.Quasithin.Vol2.Ch10SecB7Fact
public import CFSG.Quasithin.Vol2.Ch10SecKL7m

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Quasithin CFSG.Assembly.LowTwoRank KL7

theorem fact10_2_7Six_holds : Fact10_2_7Six := by
  intro W _ _ hW Mb L₁ L₂ W₁ W₂ τ hsup hle₁ hle₂ hnorm hcomm hfix₁ hfix₂ hsum hτ hmapL hmapW _ hR
  obtain ⟨c⟩ := nonempty_coord hsum
  have h : Hyp Mb L₁ L₂ W₁ W₂ τ :=
    ⟨hW, hsup, hle₁, hle₂, hnorm, hcomm, hfix₁, hfix₂, ⟨c⟩, hτ, hmapL, hmapW⟩
  have hRH := rHyp_of hnorm hR
  refine ⟨h.rk_W, h.mParam_eq hRH, h.aParam_eq hRH, h.nPrime_eq hRH, ?_, ?_⟩
  · intro x hx hx1 hcd
    obtain ⟨hx2, -, hW'⟩ := h.classify hRH hx hx1 hcd
    refine ⟨orderOf_eq_prime hx2 hx1, ?_⟩
    rcases hW' with ⟨-, h2⟩ | ⟨-, h1⟩
    · exact Or.inr h2
    · exact Or.inl h1
  · intro A hA
    exact ⟨fun a ha w hw => h.map_mem_W₁ (hA.1 ha) (h.aSet_normalizes hA ha) hw,
      fun a ha w hw => h.map_mem_W₂ (hA.1 ha) (h.aSet_normalizes hA ha) hw,
      h.aSet_mQuot_le hRH hA, h.swap.aSet_mQuot_le hRH.swap hA⟩

end CFSG.Quasithin.Vol2.Ch10.SecB
