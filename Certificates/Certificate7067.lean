module

public import CFSG.Quasithin.Background.HSp4A6DataInputs
public import CFSG.Quasithin.Background.HSp4Model
public import CFSG.Quasithin.Background.G6Natural
import Certificates.Kernel.Direct.C7067

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Sp4A6 CFSG.Assembly.LowTwoRank Matrix
open Equiv
open CFSG.QuasithinUnique.Lin2.Five (tauMat)
open scoped Matrix
local notation "ι₀" => (Sum.inl 0 : Fin 2 ⊕ Fin 2)

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelDirect.C7067 in
open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Sp4A6 CFSG.Assembly.LowTwoRank Matrix in
open Equiv in
open CFSG.QuasithinUnique.Lin2.Five (tauMat) in
open scoped Matrix in
theorem certificate7067 :
    (∀ y : Fin 6 → ZMod 2, ∑ i, y i = 0 →
       ∃ t : ZMod 2, y = ∑ c, coord y c • bas c + t • ones)
    ∧ (∀ σ : Perm (Fin 6),
       (psiMat σ)ᵀ * fromBlocks 0 1 (-1) 0 * psiMat σ = fromBlocks 0 1 (-1) 0)
    ∧ (∀ σ : Perm (Fin 6), psiMat σ = 1 → σ = 1)
    ∧ (∀ w : Fin 2 ⊕ Fin 2 → ZMod 2,
       (∀ σ : Perm (Fin 6), Perm.sign σ = 1 → psiMat σ *ᵥ Pi.single ι₀ 1 = Pi.single ι₀ 1 →
         psiMat σ *ᵥ w = w) → w = 0 ∨ w = Pi.single ι₀ 1)
    ∧ (∀ v w : Fin 2 ⊕ Fin 2 → ZMod 2, v ≠ 0 → w ≠ 0 →
       ∃ σ : Perm (Fin 6), Perm.sign σ = 1 ∧ psiMat σ *ᵥ v = w)
    ∧ (Fintype.card {v : Fin 2 ⊕ Fin 2 → ZMod 2 // psiMat cyc345 *ᵥ v = v} = 4 ∧
       Fintype.card {v : Fin 2 ⊕ Fin 2 → ZMod 2 // tauMat (psiMat cyc345) *ᵥ v = v} = 1) :=
  ⟨decomp_0, psiMat_symplectic_1, psiMat_eq_one_2, stab_fix_3, transitive_psiMat_4,
    card_fix_cyc345_5⟩

end Certificates
