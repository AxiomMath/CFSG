module

public import CFSG.Quasithin.Background.JonesParshallCurtisHeckeInputs
public import CFSG.Quasithin.Background.JonesParshallBasic

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis Matrix

namespace CertificateChecks.Batch17022

open CFSG CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis Matrix

private theorem Th_Th_checks_0 :  ∀ s : Fin 4,
    IsUpU (toMat (rootBM ([(true, s), (false, s)].reverse ++
      [(false, s), (true, s), (false, s)]))) ∧
    IsUpU (toMat (rootBM ([(false, s)].reverse ++ [(true, s), (false, s), (true, s), (false, s)])))
    ∧ IsUpU (toMat (rootBM (([] : List (Bool × Fin 4)).reverse ++ [(false, s), (false, s)]))) ∧
    IsUpU (toMat (rootBM (([] : List (Bool × Fin 4)).reverse ++
      [(true, s), (false, s), (false, s)])))  := by
  decide +kernel

private theorem comm_checks_1 :  ∀ s t : Fin 4, (s.val + 2 ≤ t.val ∨ t.val + 2 ≤ s.val) →
    rootBM [(false, s), (false, t)] = rootBM [(false, t), (false, s)] ∧
    rootBM [(true, s), (false, s), (false, t)] = rootBM [(false, t), (true, s), (false, s)] ∧
    rootBM [(false, s), (true, t), (false, t)] = rootBM [(true, t), (false, t), (false, s)] ∧
    rootBM [(true, s), (false, s), (true, t), (false, t)] =
      rootBM [(true, t), (false, t), (true, s), (false, s)]  := by
  decide +kernel

private theorem braid_checks_2 :  ∀ s : Fin 3,
    IsUpU (toMat (rootBM (
      [(true, s.succ), (false, s.succ), (false, s.castSucc), (true, s.succ),
        (false, s.succ)].reverse ++
      [(false, s.castSucc), (false, s.succ), (false, s.castSucc)]))) ∧
    IsUpU (toMat (rootBM (
      [(false, s.succ), (true, s.castSucc), (false, s.castSucc), (false, s.succ)].reverse ++
      [(false, s.castSucc), (false, s.succ), (true, s.castSucc),
        (false, s.castSucc)]))) ∧
    IsUpU (toMat (rootBM (
      [(false, s.succ), (false, s.castSucc), (true, s.succ), (false, s.succ)].reverse ++
      [(false, s.castSucc), (true, s.succ), (false, s.succ), (false, s.castSucc)]))) ∧
    IsUpU (toMat (rootBM (
      [(true, s.succ), (false, s.succ), (true, s.castSucc), (false, s.castSucc),
        (false, s.succ)].reverse ++
      [(false, s.castSucc), (true, s.succ), (false, s.succ), (true, s.castSucc),
        (false, s.castSucc)]))) ∧
    IsUpU (toMat (rootBM (
      [(true, s.succ), (false, s.succ), (false, s.castSucc), (false, s.succ)].reverse ++
      [(true, s.castSucc), (false, s.castSucc), (false, s.succ),
        (false, s.castSucc)]))) ∧
    IsUpU (toMat (rootBM (
      [(false, s.succ), (false, s.castSucc), (false, s.succ)].reverse ++
      [(true, s.castSucc), (false, s.castSucc), (false, s.succ),
        (true, s.castSucc), (false, s.castSucc)]))) ∧
    IsUpU (toMat (rootBM (
      [(false, s.succ), (true, s.castSucc), (false, s.castSucc), (true, s.succ),
        (false, s.succ)].reverse ++
      [(true, s.castSucc), (false, s.castSucc), (true, s.succ), (false, s.succ),
        (false, s.castSucc)]))) ∧
    IsUpU (toMat (rootBM (
      [(true, s.succ), (false, s.succ), (true, s.castSucc), (false, s.castSucc),
        (true, s.succ), (false, s.succ)].reverse ++
      [(true, s.castSucc), (false, s.castSucc), (true, s.succ), (false, s.succ),
        (true, s.castSucc), (false, s.castSucc)])))  := by
  decide +kernel

private theorem order_three_checks_3 :  ∀ s : Fin 4,
    (xE s * yE s) * (xE s * yE s) * (xE s * yE s) = 1 ∧ yE s = xE s * sE s * xE s ∧
      xE s * yE s = sE s * xE s  := by
  decide +kernel

end CertificateChecks.Batch17022

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis Matrix in
theorem certificate17022 : (
 ∀ s : Fin 4,
    IsUpU (toMat (rootBM ([(true, s), (false, s)].reverse ++
      [(false, s), (true, s), (false, s)]))) ∧
    IsUpU (toMat (rootBM ([(false, s)].reverse ++ [(true, s), (false, s), (true, s), (false, s)])))
    ∧ IsUpU (toMat (rootBM (([] : List (Bool × Fin 4)).reverse ++ [(false, s), (false, s)]))) ∧
    IsUpU (toMat (rootBM (([] : List (Bool × Fin 4)).reverse ++
      [(true, s), (false, s), (false, s)]))) 
)
    ∧ (
 ∀ s t : Fin 4, (s.val + 2 ≤ t.val ∨ t.val + 2 ≤ s.val) →
    rootBM [(false, s), (false, t)] = rootBM [(false, t), (false, s)] ∧
    rootBM [(true, s), (false, s), (false, t)] = rootBM [(false, t), (true, s), (false, s)] ∧
    rootBM [(false, s), (true, t), (false, t)] = rootBM [(true, t), (false, t), (false, s)] ∧
    rootBM [(true, s), (false, s), (true, t), (false, t)] =
      rootBM [(true, t), (false, t), (true, s), (false, s)] 
)
    ∧ (
 ∀ s : Fin 3,
    IsUpU (toMat (rootBM (
      [(true, s.succ), (false, s.succ), (false, s.castSucc), (true, s.succ),
        (false, s.succ)].reverse ++
      [(false, s.castSucc), (false, s.succ), (false, s.castSucc)]))) ∧
    IsUpU (toMat (rootBM (
      [(false, s.succ), (true, s.castSucc), (false, s.castSucc), (false, s.succ)].reverse ++
      [(false, s.castSucc), (false, s.succ), (true, s.castSucc),
        (false, s.castSucc)]))) ∧
    IsUpU (toMat (rootBM (
      [(false, s.succ), (false, s.castSucc), (true, s.succ), (false, s.succ)].reverse ++
      [(false, s.castSucc), (true, s.succ), (false, s.succ), (false, s.castSucc)]))) ∧
    IsUpU (toMat (rootBM (
      [(true, s.succ), (false, s.succ), (true, s.castSucc), (false, s.castSucc),
        (false, s.succ)].reverse ++
      [(false, s.castSucc), (true, s.succ), (false, s.succ), (true, s.castSucc),
        (false, s.castSucc)]))) ∧
    IsUpU (toMat (rootBM (
      [(true, s.succ), (false, s.succ), (false, s.castSucc), (false, s.succ)].reverse ++
      [(true, s.castSucc), (false, s.castSucc), (false, s.succ),
        (false, s.castSucc)]))) ∧
    IsUpU (toMat (rootBM (
      [(false, s.succ), (false, s.castSucc), (false, s.succ)].reverse ++
      [(true, s.castSucc), (false, s.castSucc), (false, s.succ),
        (true, s.castSucc), (false, s.castSucc)]))) ∧
    IsUpU (toMat (rootBM (
      [(false, s.succ), (true, s.castSucc), (false, s.castSucc), (true, s.succ),
        (false, s.succ)].reverse ++
      [(true, s.castSucc), (false, s.castSucc), (true, s.succ), (false, s.succ),
        (false, s.castSucc)]))) ∧
    IsUpU (toMat (rootBM (
      [(true, s.succ), (false, s.succ), (true, s.castSucc), (false, s.castSucc),
        (true, s.succ), (false, s.succ)].reverse ++
      [(true, s.castSucc), (false, s.castSucc), (true, s.succ), (false, s.succ),
        (true, s.castSucc), (false, s.castSucc)]))) 
)
    ∧ (
 ∀ s : Fin 4,
    (xE s * yE s) * (xE s * yE s) * (xE s * yE s) = 1 ∧ yE s = xE s * sE s * xE s ∧
      xE s * yE s = sE s * xE s 
) := by
  exact ⟨@CertificateChecks.Batch17022.Th_Th_checks_0, @CertificateChecks.Batch17022.comm_checks_1, @CertificateChecks.Batch17022.braid_checks_2, @CertificateChecks.Batch17022.order_three_checks_3⟩

end Certificates
