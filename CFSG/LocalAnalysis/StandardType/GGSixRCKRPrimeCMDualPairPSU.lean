module

public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUBlock
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeParity
import all CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSU

public section

namespace CFSG.StandardType.RCKRP

open CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.ClassicalPosition
  CFSG.StandardType.TableCRes

theorem rckDP_blockEquiv_PSU {n g : ℕ} {s : GL (Fin n) (PSUF g)} (hsU : s ∈ GUsub (PSUσ g) n)
    (hodd : Odd (orderOf s)) {ε e : Matrix (Fin n) (Fin n) (PSUF g)}
    (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (he : IsPrimIdemIn
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) e)
    (heε : e * ε = e) (hpair : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e ≠ e)
    (hεeq : ε = e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e) :
    ∃ (m : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), 1 ≤ m ∧
      Nonempty (↥(Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓ glFixing (1 - ε) ⊓
        GUsub (PSUσ g) n) ≃* GL (Fin m) K) := by
  classical
  have hS : ∀ a ∈ ({s} : Set (GL (Fin n) (PSUF g))),
      ∀ b ∈ ({s} : Set (GL (Fin n) (PSUF g))), Commute a b := by
    intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    simpa [ha, hb]
  have hoddS : ∀ a ∈ ({s} : Set (GL (Fin n) (PSUF g))), Odd (orderOf a) := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact hodd
  obtain ⟨K, hKfield, hKalg, hKfinite, π, hπsurj, hπker, -⟩ :=
    exists_blockField (F := PSUF g) (S := ({s} : Set (GL (Fin n) (PSUF g)))) hS hoddS he
  letI : Field K := hKfield
  letI : Algebra (PSUF g) K := hKalg
  letI : Finite K := hKfinite
  have hCharK : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap (PSUF g) K).injective 2
  have hSU : ∀ a ∈ ({s} : Set (GL (Fin n) (PSUF g))),
      Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution (PSUF g) 2 (g + 1))
        (a : Matrix (Fin n) (Fin n) (PSUF g)) * Unitary.antidiag n *
        (a : Matrix (Fin n) (Fin n) (PSUF g)) = Unitary.antidiag n := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    simpa [Unitary.conjTr, PSUσ] using mem_GUsub_iff.mp hsU
  obtain ⟨m, hm, ⟨eGL⟩⟩ :=
    fePSU_dualPair_unitBlockCentralizer_equiv_iso (F := PSUF g) (f := g + 1)
      (card_PSUF g) ({s} : Set (GL (Fin n) (PSUF g))) hS hSU hε he heε hpair hεeq K π
      hπsurj hπker
  have hEq : (Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓ glFixing (1 - ε) ⊓
      GUsub (PSUσ g) n) =
      fePSU_dualPair_unitBlockCentralizer (f := g + 1)
        ({s} : Set (GL (Fin n) (PSUF g))) ε := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨hcent, hfix⟩, hGU⟩
      refine ⟨mem_GUsub_iff.mp hGU, ?_, hfix⟩
      intro a ha
      exact (Subgroup.mem_centralizer_iff.mp hcent a ha).symm
    · rintro ⟨hGU, hcomm, hfix⟩
      exact ⟨⟨Subgroup.mem_centralizer_iff.mpr fun a ha => (hcomm a ha).symm, hfix⟩,
        mem_GUsub_iff.mpr hGU⟩
  exact ⟨m, K, hKfield, hKfinite, hCharK, hm,
    ⟨(MulEquiv.subgroupCongr hEq).trans eGL⟩⟩

end CFSG.StandardType.RCKRP
