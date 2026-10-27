module

public import CFSG.Monster.Existence.StdOdd.P5Inputs
public import Certificates.Data.Kernel.WeylE6
import Certificates.Kernel.MonsterExist.P5.Subgroups
import Certificates.Kernel.MonsterExist.P5.Indep
import Certificates.Kernel.MonsterExist.P5.Roots
import Certificates.Kernel.MonsterExist.P5.OrbitRoot
import Certificates.Kernel.MonsterExist.P5.OrbitSing
import Certificates.Kernel.MonsterExist.P5.OrbitNorm
import Certificates.Kernel.MonsterExist.WeylE6.Check
import Certificates.Kernel.MonsterExist.P5.Pmat

public section

open CFSG.Monster.Existence.StdOdd.P5 CertificateChecks.MonsterExist

namespace Certificates

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.StdOdd in
open CFSG.Monster.Existence.StdOdd.P5 in
theorem certificate6040 : (∀ i : Fin 81, pmat (ra i) = pmat i * aMat)
    ∧ (∀ i : Fin 81, pmat (rb i) = pmat i * bMat)
    ∧ (∀ i j : Fin 81, pmat i = pmat j → i = j)
    ∧ (pmat 0 = 1)
    ∧ (∀ j : Fin 81, walk (pw j) 0 = j)
    ∧ (∀ i j : Fin 81, tb i j = walk (pw j) i)
    ∧ (∀ i : Fin 81, ∃ j : Fin 81, tb i j = 0)
    ∧ (latticeClosedB = true)
    ∧ ([0] ∈ lattice)
    ∧ (lattice.length = 50)
    ∧ (elemCheckB = true)
    ∧ (∀ l ∈ lattice, l.Nodup)
    ∧ (∀ c : Fin 5 → ZMod 3, ∑ i, c i • wsT i = 0 → c = 0)
    ∧ (∀ c : Fin 4 → ZMod 3, ∑ i, c i • ws1 i = 0 → c = 0)
    ∧ (cert27CheckB = true)
    ∧ (∀ (i : Fin 6) (v : E5),
      (CFSG.Monster.Existence.StdOdd.P5.refl i).mulVec v = v - bil v (alpha i) • alpha i)
    ∧ (rootVecs.card = 72)
    ∧ (∀ x : E5, x ≠ 0 → rk x = 30 ∨ rk x = 18 ∨ rk x = 24)
    ∧ ((rkFibre 30).card = 72)
    ∧ ((rkFibre 18).card = 80)
    ∧ ((rkFibre 24).card = 90)
    ∧ (∀ x : E5, decV (encV x) = x)
    ∧ (orbitFin 12 vRoot = (rkFibre 30).image encV)
    ∧ (orbitFin 12 vSing = (rkFibre 18).image encV)
    ∧ (orbitFin 12 vNorm = (rkFibre 24).image encV)
    ∧ (rk vRoot = 30)
    ∧ (rk vSing = 18)
    ∧ (rk vNorm = 24)
    ∧ (rkFibre 30 = rootVecs)
    ∧ (∃ T P E s : ℕ, (∀ t : Fin 6, ∀ x : Fin 243,
        CFSG.KC.WeylE6.f8 T (256 * t.val + x.val) = encV (Matrix.vecMul (decV x) (refl t))) ∧
      CFSG.KC.WeylE6.wOK T P E 51840 s = true) :=
  ⟨P5.pmat_ra, P5.pmat_rb, P5.pmat_inj, P5.pmat_zero, P5.walk_pw, P5.tb_eq, P5.tb_inv,
    P5.latticeClosedB_true, P5.lattice_zero, P5.lattice_length, P5.elemCheckB_true,
    P5.latticeNodup, P5.wsT_indep, P5.ws1_indep, P5.cert27CheckB_true, P5.refl_apply,
    P5.card_rootVecs, P5.rk_cases, P5.card_rkFibre_30, P5.card_rkFibre_18, P5.card_rkFibre_24,
    CFSG.KC.WeylE6.decV_encV, P5.orbitFin_root, P5.orbitFin_sing, P5.orbitFin_norm, P5.rk_vRoot,
    P5.rk_vSing, P5.rk_vNorm, P5.rkFibre_30_eq,
    ⟨WeylE6.WT, WeylE6.WP, WeylE6.WE, 21604, WeylE6.tab_ok, WeylE6.w_ok⟩⟩

end Certificates

end
