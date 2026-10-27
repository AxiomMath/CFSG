module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMBlockPSp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMSDBlock
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockGUSesq
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMDualPairPSU
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMCompPSU

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.ClassicalPosition CFSG.StandardType.TableCRes
open CFSG.Open (StatedLieTag)


theorem rckBlockModel_PSU {n g : ℕ} {s : GL (Fin n) (PSUF g)} (hsU : s ∈ GUsub (PSUσ g) n)
    (hodd : Odd (orderOf s)) {ε e : Matrix (Fin n) (Fin n) (PSUF g)}
    (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (he : IsPrimIdemIn
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) e)
    (heε : e * ε = e)
    (hdich : e = ε ∨ (e ≠ ε ∧ formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e ≠ e ∧
      ε = e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e))
    {J' : Subgroup ↥(Unitary.SU (PSUσ g) n)}
    (hJ' : IsComponentOf J' ⁅glBlockCentralizer (PSUj n g) {s} ε,
      glBlockCentralizer (PSUj n g) {s} ε⁆) :
    (∃ (t : StatedLieTag) (m g' : ℕ) (κ : (ggU t m g').K →*
        ↥(Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓ glFixing (1 - ε) ⊓
          GUsub (PSUσ g) n)),
      RCKClassicalTag t ∧ 1 ≤ g' ∧
        RCKModelConverse ((J'.map (PSUj n g)).subgroupOf
          (Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓ glFixing (1 - ε) ⊓
            GUsub (PSUσ g) n)) t m g' κ) ∨
    (∃ (m Q : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2), m ≤ 3 ∧
      Nat.card E = Q ^ 2 ∧
      Nonempty (↥(Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓ glFixing (1 - ε) ⊓
          GUsub (PSUσ g) n) ≃* ↥(ClassicalBlocks.GUFull m Q E))) := by
  classical
  let Gt : Subgroup (GL (Fin n) (PSUF g)) :=
    Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓ glFixing (1 - ε) ⊓
      GUsub (PSUσ g) n
  let C : Subgroup ↥Gt := (J'.map (PSUj n g)).subgroupOf Gt
  have hCo : CFSG.Open.IsComponentOf C ⊤ :=
    rckIsComponentOf_top_of_commutator_map (Subgroup.subtype_injective _)
      (rckPSU_blockGroup_map_normal s ε).1 (rckPSU_blockGroup_map_normal s ε).2 hJ'
  change (∃ (t : StatedLieTag) (m g' : ℕ) (κ : (ggU t m g').K →* ↥Gt),
      RCKClassicalTag t ∧ 1 ≤ g' ∧ RCKModelConverse C t m g' κ) ∨
    (∃ (m Q : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2), m ≤ 3 ∧
      Nat.card E = Q ^ 2 ∧ Nonempty (↥Gt ≃* ↥(ClassicalBlocks.GUFull m Q E)))
  rcases hdich with heq | ⟨hne, hpair, hεeq⟩
  · rw [heq] at he
    have hSpair : ∀ x ∈ ({s} : Set (GL (Fin n) (PSUF g))),
        ∀ y ∈ ({s} : Set (GL (Fin n) (PSUF g))), Commute x y := by
      intro x hx y hy
      rw [Set.mem_singleton_iff] at hx hy
      rw [hx, hy]
    have hSodd : ∀ x ∈ ({s} : Set (GL (Fin n) (PSUF g))), Odd (orderOf x) := by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hodd
    obtain ⟨K, hKfield, hKfin, hKalg, hKmod, hKtower, π, hπ⟩ :=
      rckBlockCoord_exists ({s} : Set (GL (Fin n) (PSUF g))) hSpair hSodd he
    letI : Field K := hKfield
    letI : Finite K := hKfin
    letI : Algebra (PSUF g) K := hKalg
    letI : Module K (LinearMap.range (Matrix.mulVecLin ε)) := hKmod
    letI : IsScalarTower (PSUF g) K (LinearMap.range (Matrix.mulVecLin ε)) := hKtower
    obtain ⟨ρ, B, hρ, hρ1, hBh, hBl, htr⟩ := rckSD_formDescent hsU hε hπ
    haveI : CharP K 2 := charP_of_injective_algebraMap (algebraMap (PSUF g) K).injective 2
    haveI : Finite (LinearMap.range (Matrix.mulVecLin ε)) :=
      Finite.of_injective Subtype.val Subtype.coe_injective
    haveI : Module.Finite K (LinearMap.range (Matrix.mulVecLin ε)) := Module.Finite.of_finite
    obtain ⟨Φ₁⟩ := rckSD_blockEquiv hε hπ htr
    obtain ⟨i, hcard, ⟨Φ₂⟩⟩ :=
      ClassicalBlocks.nonempty_sesqUnitaryGroup_mulEquiv_GUFull ρ hρ hρ1 B hBh hBl
    rcases rckBlockModel_unitaryCase
      (m := Module.finrank K (LinearMap.range (Matrix.mulVecLin ε))) (Q := 2 ^ i)
      hCo hcard (Φ := Φ₁.trans Φ₂) with h | h
    · exact Or.inl h
    · obtain ⟨m', Q', E', hE'f, hE'fin, hE'char, hm'3, hcard', Φ', _⟩ := h
      exact Or.inr ⟨m', Q', E', hE'f, hE'fin, hE'char, hm'3, hcard', ⟨Φ'⟩⟩
  · obtain ⟨m, K, hKfield, hKfin, hKchar, hm1, ⟨Φ⟩⟩ :=
      rckDP_blockEquiv_PSU hsU hodd hε he heε hpair hεeq
    letI : Field K := hKfield
    letI : Finite K := hKfin
    letI : CharP K 2 := hKchar
    exact Or.inl (rckBlockModel_linearCase (m := m) hCo (Φ := Φ))

end CFSG.StandardType.RCKRP
