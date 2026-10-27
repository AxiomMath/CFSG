module

public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersCentralInputs

public section

namespace CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ReeTag

private theorem cert18000_fixedOrbitWord_one_centralRoot44 :
    (F4.fixedOrbitWord ⟨1, by decide⟩).foldr (reflect F4.tag) centralRoot44 = centralRoot44 := by
  decide +kernel

private theorem cert18000_fixedOrbitWord_one_centralRoot47 :
    (F4.fixedOrbitWord ⟨1, by decide⟩).foldr (reflect F4.tag) centralRoot47 = centralRoot47 := by
  decide +kernel

private theorem cert18000_centralZ_weyl_check : ∀ k : Fin F4.fixedWeylOrder,
    F4.fixedRelWord k = [] ∨ F4.fixedRelWord k = [⟨1, by decide⟩] ∨
      height (centralWeylImage k centralRoot44) < 0 ∨
      height (centralWeylImage k centralRoot47) < 0 ∨
      (centralWeylImage k centralRoot44 ≠ centralRoot44 ∧
        centralWeylImage k centralRoot44 ≠ centralRoot47 ∧
        centralWeylImage k centralRoot47 ≠ centralRoot44 ∧
        centralWeylImage k centralRoot47 ≠ centralRoot47) := by
  decide +kernel

private theorem cert18000_fixedOrbitWord_one_centralRootE1 :
    (F4.fixedOrbitWord ⟨1, by decide⟩).foldr (reflect F4.tag) centralRootE1 = centralRootZE1 := by
  decide +kernel

private theorem cert18000_fixedOrbitWord_one_centralRootE4 :
    (F4.fixedOrbitWord ⟨1, by decide⟩).foldr (reflect F4.tag) centralRootE4 = centralRootZE4 := by
  decide +kernel

end CFSG.LieType.Ree.LargeReeInvolution

namespace Certificates

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution in
theorem certificate18000 : (
    (F4.fixedOrbitWord ⟨1, by decide⟩).foldr (reflect F4.tag) centralRoot44 = centralRoot44
  ) ∧ (
    (F4.fixedOrbitWord ⟨1, by decide⟩).foldr (reflect F4.tag) centralRoot47 = centralRoot47
  ) ∧ (
    ∀ k : Fin F4.fixedWeylOrder,
      F4.fixedRelWord k = [] ∨ F4.fixedRelWord k = [⟨1, by decide⟩] ∨
        height (centralWeylImage k centralRoot44) < 0 ∨
        height (centralWeylImage k centralRoot47) < 0 ∨
        (centralWeylImage k centralRoot44 ≠ centralRoot44 ∧
          centralWeylImage k centralRoot44 ≠ centralRoot47 ∧
          centralWeylImage k centralRoot47 ≠ centralRoot44 ∧
          centralWeylImage k centralRoot47 ≠ centralRoot47)
  ) ∧ (
    (F4.fixedOrbitWord ⟨1, by decide⟩).foldr (reflect F4.tag) centralRootE1 = centralRootZE1
  ) ∧ (
    (F4.fixedOrbitWord ⟨1, by decide⟩).foldr (reflect F4.tag) centralRootE4 = centralRootZE4
  ) := by
  exact ⟨CFSG.LieType.Ree.LargeReeInvolution.cert18000_fixedOrbitWord_one_centralRoot44,
    CFSG.LieType.Ree.LargeReeInvolution.cert18000_fixedOrbitWord_one_centralRoot47,
    CFSG.LieType.Ree.LargeReeInvolution.cert18000_centralZ_weyl_check,
    CFSG.LieType.Ree.LargeReeInvolution.cert18000_fixedOrbitWord_one_centralRootE1,
    CFSG.LieType.Ree.LargeReeInvolution.cert18000_fixedOrbitWord_one_centralRootE4⟩

end Certificates
