module

public import CFSG.Quasithin.H13.GoldschmidtU43EMat4

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z) (r : S.Rho)

theorem pow_nine_of_chiN_cube (n : ↥S.Ng) (h : S.chiN r n ^ 3 = 1) : (n : G) ^ 9 = 1 := by
  have h1 : S.chiN r (n ^ 3) = 1 := by
    rw [pow_three, S.chiN_mul, S.chiN_mul, ← pow_three]
    exact h
  have h2 : ((n ^ 3 : ↥S.Ng) : G) ∈ S.Mg := (S.chiN_eq_one_iff r (n ^ 3)).mp h1
  have h3 := S.pow_three_Mg _ h2
  have h4 : ((n ^ 3 : ↥S.Ng) : G) = (n : G) ^ 3 := rfl
  rw [h4, ← pow_mul] at h3
  exact h3

end JWSetup

end CFSG.Quasithin.H13.U43
