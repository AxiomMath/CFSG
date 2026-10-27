module

public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUYModel
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUComp
public import CFSG.LocalAnalysis.ComponentClassification.PerfectCentralQuotient
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36L4Twin
import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EForms
import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
import CFSG.Walter.ReeOrder.JT.Defs

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.ClassicalPosition

section PerfectSubgroups

open scoped commutatorElement

theorem tcCentral_conj {U : Type*} [Group U] {z : U} (hz : z ∈ Subgroup.center U) (v : U) :
    z * v * z⁻¹ = v := by
  rw [← Subgroup.mem_center_iff.mp hz v, mul_inv_cancel_right]

theorem tcCommutator_mul_central_left {U : Type*} [Group U] {x v z : U}
    (hz : z ∈ Subgroup.center U) : ⁅x * z, v⁆ = ⁅x, v⁆ := by
  have e : x * z * v * (z⁻¹ * x⁻¹) * v⁻¹ = x * (z * v * z⁻¹) * x⁻¹ * v⁻¹ := by group
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, e, tcCentral_conj hz v]

theorem tcCommutator_mul_central_right {U : Type*} [Group U] {x v z : U}
    (hz : z ∈ Subgroup.center U) : ⁅x, v * z⁆ = ⁅x, v⁆ := by
  have e : x * (v * z) * x⁻¹ * (v * z)⁻¹ = x * v * (z * x⁻¹ * z⁻¹) * v⁻¹ := by group
  rw [commutatorElement_def, commutatorElement_def, e, tcCentral_conj hz x⁻¹]

theorem tcCommutator_mul_central {U : Type*} [Group U] {x v z w : U}
    (hz : z ∈ Subgroup.center U) (hw : w ∈ Subgroup.center U) :
    ⁅x * z, v * w⁆ = ⁅x, v⁆ := by
  rw [tcCommutator_mul_central_left hz, tcCommutator_mul_central_right hw]

theorem tcPerfect_le_of_map_le {U X : Type*} [Group U] [Group X] (ψ : U →* X)
    (hψ : ψ.ker ≤ Subgroup.center U) {A B : Subgroup U} (hA : ⁅A, A⁆ = A)
    (h : A.map ψ ≤ B.map ψ) : A ≤ B := by
  have hdec : ∀ a ∈ A, ∃ b ∈ B, ∃ z ∈ Subgroup.center U, a = b * z := by
    intro a ha
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp (h (Subgroup.mem_map_of_mem ψ ha))
    have hk : b⁻¹ * a ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hba, inv_mul_cancel]
    exact ⟨b, hb, b⁻¹ * a, hψ hk, (mul_inv_cancel_left b a).symm⟩
  have hcomm : ∀ a ∈ A, ∀ a' ∈ A, ⁅a, a'⁆ ∈ B := by
    intro a ha a' ha'
    obtain ⟨b, hb, z, hz, rfl⟩ := hdec a ha
    obtain ⟨b', hb', z', hz', rfl⟩ := hdec a' ha'
    rw [tcCommutator_mul_central hz hz', commutatorElement_def]
    exact B.mul_mem (B.mul_mem (B.mul_mem hb hb') (B.inv_mem hb)) (B.inv_mem hb')
  calc A = ⁅A, A⁆ := hA.symm
    _ ≤ B := Subgroup.commutator_le.mpr fun a ha a' ha' => hcomm a ha a' ha'

theorem tcPerfect_eq_of_map_eq {U X : Type*} [Group U] [Group X] (ψ : U →* X)
    (hψ : ψ.ker ≤ Subgroup.center U) {A B : Subgroup U} (hA : ⁅A, A⁆ = A) (hB : ⁅B, B⁆ = B)
    (h : A.map ψ = B.map ψ) : A = B :=
  le_antisymm (tcPerfect_le_of_map_le ψ hψ hA h.le)
    (tcPerfect_le_of_map_le ψ hψ hB h.ge)

theorem tcCommutator_self_of_isQuasisimple {U : Type*} [Group U] {L : Subgroup U}
    (hL : CFSG.Assembly.IsQuasisimple L) : ⁅L, L⁆ = L := by
  have h := congrArg (Subgroup.map L.subtype) hL.1
  rwa [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h

theorem tcNe_bot_of_isQuasisimple {U : Type*} [Group U] {L : Subgroup U}
    (hL : CFSG.Assembly.IsQuasisimple L) : L ≠ ⊥ := by
  intro h
  have : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hL.2.toNontrivial
  obtain ⟨a, b, hab⟩ := exists_pair_ne (↥L ⧸ Subgroup.center ↥L)
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  have h1 : (a' : U) = 1 := (Subgroup.eq_bot_iff_forall L).mp h _ a'.2
  have h2 : (b' : U) = 1 := (Subgroup.eq_bot_iff_forall L).mp h _ b'.2
  have : a' = b' := Subtype.ext (h1.trans h2.symm)
  rw [this]

end PerfectSubgroups

section AverageY

open CFSG.StandardType.ClassicalPosition.Geo

variable {X : Type} [Group X] {n g p : ℕ} {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} {B : Subgroup X}

theorem PSUYsd_isComponentOf {T : Matrix (Fin n) (Fin n) (PSUF g)}
    (hT : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) T = T)
    {s : GL (Fin n) (PSUF g)} (hsT : (s : Matrix (Fin n) (Fin n) (PSUF g)) * T = T)
    (hTs : T * (s : Matrix (Fin n) (Fin n) (PSUF g)) = T)
    (hTc : ∀ c : GL (Fin n) (PSUF g), c ∈ Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) →
      (c : Matrix (Fin n) (Fin n) (PSUF g)) * T = T * (c : Matrix (Fin n) (Fin n) (PSUF g)))
    (hYq : CFSG.Assembly.IsQuasisimple ↥(PSUYsd n g T)) :
    IsComponentOf (PSUYsd n g T)
      ((Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g)))).comap (PSUj n g)) :=
  have hle := PSUYsd_le_centralizer hT hsT hTs
  ⟨hle, IsSubnormal.step hle (PSUYsd_normal_subgroupOf_centralizer hTc) (IsSubnormal.refl _),
    hYq⟩

theorem lieModel_map_PSUYsd {ψ : ↥(Unitary.SU (PSUσ g) n) →* X}
    (hker : ψ.ker ≤ Subgroup.center ↥(Unitary.SU (PSUσ g) n))
    {T : Matrix (Fin n) (Fin n) (PSUF g)} (hT : IsIdempotentElem T)
    (hTa : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) T = T) (hr : 3 ≤ Matrix.rank T)
    (hrq : (Matrix.rank T, 2 ^ (g + 1)) ≠ (3, 2)) :
    CFSG.Blueprint.LieModel
      (↥((PSUYsd n g T).map ψ) ⧸ Subgroup.center ↥((PSUYsd n g T).map ψ))
      .PSU (Matrix.rank T) 2 (g + 1) := by
  have hYq := isQuasisimple_PSUYsd hT hTa hr hrq
  have : Group.IsPerfect ↥(PSUYsd n g T) := ⟨hYq.1⟩
  let f : ↥(PSUYsd n g T) →* ↥((PSUYsd n g T).map ψ) := ψ.subgroupMap (PSUYsd n g T)
  have hsurj : Function.Surjective f := ψ.subgroupMap_surjective (PSUYsd n g T)
  have hfker : f.ker ≤ Subgroup.center ↥(PSUYsd n g T) := by
    intro u hu
    have hu' : (u : ↥(Unitary.SU (PSUσ g) n)) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker] at hu ⊢
      have := congrArg Subtype.val hu
      exact this
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hker hu')) w.1)
  exact blueprintLieModel_PSU_of_mulEquiv
    (CFSG.ComponentClassification.PerfectCentralQuotient.equivalence f hsurj hfker)
    (lieModel_PSUYsd hT hTa hr hrq)

theorem PSULiftHyp.exists_avgY [Finite X] (hH : PSULiftHyp n g ψ p B)
    (hpq : ¬ p ∣ 2 ^ (g + 1) + 1) (hpF : ¬ p ∣ Nat.card (PSUF g)ˣ)
    {S : Set (GL (Fin n) (PSUF g))} {ε e : Matrix (Fin n) (Fin n) (PSUF g)}
    (hb : PSUBlock ψ B S ε e) {D J : Subgroup X} (hDB : D ≤ B) (hDcard : Nat.card D = p ^ 2)
    (hjc : B ⊓ Subgroup.centralizer (J : Set X) = D)
    (hSD : ∀ d ∈ D, ∀ s ∈ psuE ψ B, IsGLLift (PSUj n g) ψ s d → s ∈ S)
    {J' : Subgroup ↥(Unitary.SU (PSUσ g) n)}
    (hJ'g : IsComponentOf J'
      ⁅glBlockCentralizer (PSUj n g) S ε, glBlockCentralizer (PSUj n g) S ε⁆)
    (hJ'm : J'.map ψ = J)
    (hd : 2 ≤ blockDegree (Algebra.adjoin (PSUF g) (Units.val '' S)) e)
    {y : X} (hyD : y ∈ D)
    (hye : ((hH.lam hpq ⟨y, hDB hyD⟩ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) *
      e = e) :
    ∃ T : Matrix (Fin n) (Fin n) (PSUF g), IsIdempotentElem T ∧
      formAdj (PSUσ g).toRingHom (Unitary.antidiag n) T = T ∧
      (∀ c : GL (Fin n) (PSUF g),
        c * (hH.lam hpq ⟨y, hDB hyD⟩ : GL (Fin n) (PSUF g)) =
          (hH.lam hpq ⟨y, hDB hyD⟩ : GL (Fin n) (PSUF g)) * c →
        (c : Matrix (Fin n) (Fin n) (PSUF g)) * T = T * (c : Matrix (Fin n) (Fin n) (PSUF g))) ∧
      6 ≤ Matrix.rank T ∧ J' ≤ PSUYsd n g T ∧
      IsComponentOf ((PSUYsd n g T).map ψ) (ψ.range ⊓ Subgroup.centralizer ({y} : Set X)) ∧
      J ≤ (PSUYsd n g T).map ψ ∧ CFSG.Assembly.IsQuasisimple ↥(PSUYsd n g T) ∧
      CFSG.Blueprint.LieModel
        (↥((PSUYsd n g T).map ψ) ⧸ Subgroup.center ↥((PSUYsd n g T).map ψ))
        .PSU (Matrix.rank T) 2 (g + 1) := by
  classical
  obtain ⟨-, hTidem, hTadj, hsT, hTs, -, hεT, hrk⟩ := hb.avg_spec hH hpq hDB hSD hyD hye
  set s : GL (Fin n) (PSUF g) := (hH.lam hpq ⟨y, hDB hyD⟩ : GL (Fin n) (PSUF g)) with hs
  set T : Matrix (Fin n) (Fin n) (PSUF g) := avgPow s p with hT
  have hblock := hb.three_mul_blockDegree_le_rank hH hDcard hjc hJ'g hJ'm
  have hrank : 6 ≤ Matrix.rank T := by omega
  have hr3 : 3 ≤ Matrix.rank T := by omega
  have hrq : (Matrix.rank T, 2 ^ (g + 1)) ≠ (3, 2) := by
    intro h
    have := congrArg Prod.fst h
    simp only at this
    omega
  have hYq := isQuasisimple_PSUYsd hTidem hTadj hr3 hrq
  have hTc : ∀ c : GL (Fin n) (PSUF g), c ∈ Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) →
      (c : Matrix (Fin n) (Fin n) (PSUF g)) * T = T * (c : Matrix (Fin n) (Fin n) (PSUF g)) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff] at hc
    have hcs : c * s = s * c := (hc s (Set.mem_singleton s)).symm
    exact commute_avgPow hcs p
  have hY := PSUYsd_isComponentOf hTadj hsT hTs hTc hYq
  have hJ'Y : J' ≤ PSUYsd n g T := by
    have hG : ⁅glBlockCentralizer (PSUj n g) S ε, glBlockCentralizer (PSUj n g) S ε⁆ ≤
        glBlockCentralizer (PSUj n g) S ε :=
      Subgroup.commutator_le.mpr fun a ha b hb' =>
        (glBlockCentralizer (PSUj n g) S ε).mul_mem
          ((glBlockCentralizer (PSUj n g) S ε).mul_mem
            ((glBlockCentralizer (PSUj n g) S ε).mul_mem ha hb')
            ((glBlockCentralizer (PSUj n g) S ε).inv_mem ha))
          ((glBlockCentralizer (PSUj n g) S ε).inv_mem hb')
    exact hJ'g.1.trans (hG.trans (glBlockCentralizer_le_PSUYsd hεT))
  have hmapC := hH.map_centralizer_lam hpq hpF (hDB hyD)
  have hYm : IsComponentOf ((PSUYsd n g T).map ψ)
      (ψ.range ⊓ Subgroup.centralizer ({y} : Set X)) := by
    rw [← hmapC]
    exact CFSG.ComponentClassification.HarrisLit.N36.isComponentOf_map_of_ker_le_center ψ hH.ker hY
  refine ⟨T, hTidem, hTadj, fun c hc => commute_avgPow hc p, hrank, hJ'Y, hYm, ?_, hYq, ?_⟩
  · rw [← hJ'm]
    exact Subgroup.map_mono hJ'Y
  · exact lieModel_map_PSUYsd hH.ker hTidem hTadj hr3 hrq

end AverageY

end CFSG.StandardType.TableCRes
