module

public import CFSG.Quasithin.Vol2.GoldschmidtF713Two
public import CFSG.Quasithin.Background.F7TwoClaimC

public section

namespace CFSG.Quasithin.H13

theorem f713Two_of_invAutGenSQTK (hP : F7Two.InvAutGenSQTK) : F713Two :=
  f713Two_of_claimCE1 (F7Two.claimCE1_of_invAutGenSQTK hP)

end CFSG.Quasithin.H13
