module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveInputs
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
public import Certificates.Certificate8064
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.StandardType.GGB48OmReduce
import CFSG.LocalAnalysis.StandardType.GGB48OmLift
import CFSG.LocalAnalysis.StandardType.GGB48OmWeyl
import CFSG.LocalAnalysis.StandardType.GGHalfRowData
import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
import CFSG.LocalAnalysis.StandardType.GGSpinInnerAction
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open
open CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal (omegaMinus8)

theorem ggB48_of_omega_minus_eight_four
    (hMp : GGInnerDiagMpInput)
    {G : Type} [Group G] [Finite G] {B Bs N : Subgroup G} (hBs : GGBstar 3 B Bs)
    (hinn : GGInnerDiagOn Bs N) (hlab : GGHasLabel ⟨.twD, 4, 2⟩ (↥N ⧸ Subgroup.center ↥N)) :
    48 ≤ Nat.card (ggAutomizer N Bs) := by
  have hq : CFSG.Assembly.IsQuasisimple ↥N := isQuasisimple_of_largeEvenMarking hinn
  haveI : Group.IsPerfect ↥N := ⟨hq.1⟩
  have hmod := B48Om.statedClassicalModel_of_hasLabel_twD42 hlab
  have hZ : Subgroup.center ↥N = ⊥ := HalfRowData.center_eq_bot_of_pomegaMinus_two hmod
  obtain ⟨φ, hφi, hφr⟩ := B48Om.exists_spinLift hZ hmod
  have hinner := ggSpinMinusInnerAction_of_mp hMp le_rfl (by norm_num) hinn φ hφi hφr
  obtain ⟨K, _, _, _, hK, b, c, hbc, ⟨e⟩⟩ := B48Om.exists_mulEquiv_omegaMinus8 hZ hmod
  let θ : ↥(omegaMinus8 K b c) →* G := N.subtype.comp e.symm.toMonoidHom
  have hθi : Function.Injective θ := fun x y h => e.symm.injective (Subtype.ext h)
  have hθN : ∀ x, θ x ∈ N := fun x => (e.symm x).2
  have hθs : ∀ n ∈ N, ∃ x, θ x = n := fun n hn =>
    ⟨e ⟨n, hn⟩, by
      show ((e.symm (e ⟨n, hn⟩) : ↥N) : G) = n
      rw [MulEquiv.symm_apply_apply]⟩
  let E : Subgroup ↥(omegaMinus8 K b c) := Bs.comap θ
  have hE : IsElemAbelian 3 E := hBs.2.1.comap hθi
  have hself : ∀ g : ↥(omegaMinus8 K b c),
      g ∈ Subgroup.centralizer (E : Set ↥(omegaMinus8 K b c)) → g ^ 3 = 1 → g ∈ E := by
    intro g hg hg3
    have htC : θ g ∈ Subgroup.centralizer ((Bs ⊓ N : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hh' : h ∈ Bs ⊓ N := hh
      obtain ⟨x, rfl⟩ := hθs h (Subgroup.mem_inf.mp hh').2
      have hx : x ∈ E := (Subgroup.mem_inf.mp hh').1
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hg x hx]
    have htp : θ g ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
    exact (Subgroup.mem_inf.mp (B48Om.mem_inf_of_commute hBs hZ hinner (hθN g) htC htp)).1
  obtain ⟨s, hsE, hsd⟩ := B48Om.exists_signedRealizers hK hbc hE hself
  have hsE' : ∀ i, θ (s i) ∈ Subgroup.normalizer ((Bs ⊓ N : Subgroup G) : Set G) := by
    intro i
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨x, rfl⟩ := hθs h (Subgroup.mem_inf.mp hh).2
      have hx : x ∈ E := (Subgroup.mem_inf.mp hh).1
      have hsx : s i * x * (s i)⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hsE i) x).mp hx
      rw [← map_inv, ← map_mul, ← map_mul]
      exact Subgroup.mem_inf.mpr ⟨hsx, hθN _⟩
    · intro hh
      have hhN : h ∈ N := by
        have h1 := N.mul_mem (N.mul_mem (N.inv_mem (hθN (s i))) (Subgroup.mem_inf.mp hh).2)
          (hθN (s i))
        rwa [show (θ (s i))⁻¹ * (θ (s i) * h * (θ (s i))⁻¹) * θ (s i) = h by group] at h1
      obtain ⟨x, rfl⟩ := hθs h hhN
      have hsx : s i * x * (s i)⁻¹ ∈ E := by
        show θ (s i * x * (s i)⁻¹) ∈ Bs
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_inf.mp hh).1
      have hx : x ∈ E := (Subgroup.mem_normalizer_iff.mp (hsE i) x).mpr hsx
      exact Subgroup.mem_inf.mpr ⟨hx, hhN⟩
  have hsd' : ∀ i j, (∀ e' ∈ Bs ⊓ N, θ (s i) * e' * (θ (s i))⁻¹ = θ (s j) * e' * (θ (s j))⁻¹) →
      i = j := by
    intro i j hij
    apply hsd i j
    intro x hx
    apply hθi
    have h := hij (θ x) (Subgroup.mem_inf.mpr ⟨hx, hθN x⟩)
    simpa only [map_mul, map_inv] using h
  have h := B48Om.card_le_ggAutomizer hBs hZ hinner (fun i => θ (s i)) (fun i => hθN (s i))
    hsE' hsd'
  have h48 : Nat.card (Equiv.Perm (Fin 3) × (Fin 3 → (ZMod 3)ˣ)) = 48 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_perm, Fintype.card_fun,
      ZMod.card_units, Fintype.card_fin]
    rfl
  rw [h48] at h
  exact h

theorem ggTableBAut48OmegaInput_of_mp
    (hMp : GGInnerDiagMpInput) :
    GGTableBAut48OmegaInput := by
  intro G _ _ B Bs x L D J _ N hcfg _ hinn _ _ _ _ _ hN _ _ hlabN
  subst hlabN
  exact Or.inr (ggB48_of_omega_minus_eight_four hMp hcfg.2.1 hinn hN)

theorem ggTableBAut48OmegaInput_holds :
    GGTableBAut48OmegaInput :=
  ggTableBAut48OmegaInput_of_mp ggInnerDiagMpInput_holds

end CFSG.StandardType

end
