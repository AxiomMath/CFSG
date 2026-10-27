module

public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.LocalAnalysis.UniquenessCase.UC1ZassAlt
public import CFSG.LocalAnalysis.UniquenessCase.UC1ZassOdd
public import CFSG.LocalAnalysis.UniquenessCase.UC1ZassSL2
import CFSG.ClassicalInvolution.ModelFacts.G2D4SL2TorusFive
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29GWXa

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Zass

open scoped MatrixGroups

theorem exists_sylow_quaternion {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    [Nontrivial G] (hperf : commutator G = ⊤) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Finite V] {ρ : Representation (ZMod p) G V} (hρ : Function.Injective ρ) (hf : Fpf ρ) :
    ∃ P : Sylow 2 G, ∃ r : ℕ, 3 ≤ r ∧
      Nonempty ((P : Subgroup G) ≃* QuaternionGroup (2 ^ (r - 2))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect G := Group.isPerfect_def.mpr hperf
  have hnsol : ¬ Group.IsSolvable G := Group.IsPerfect.not_isSolvable G
  have hnc : ∃ P : Sylow 2 G, ¬ IsCyclic P := by
    by_contra h
    exact hnsol (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.L29GW.isSolvable_of_cyclic_sylow_two
      default (not_not.mp (not_exists.mp h default)))
  obtain ⟨P, hP⟩ := hnc
  rcases hf.sylow_two hρ P with hc | ⟨k, hk, hq, ⟨e⟩⟩
  · exact absurd hc hP
  · haveI : NeZero k := ⟨by omega⟩
    obtain ⟨n, hn⟩ := hq.exists_card_eq
    have hc4 : 4 * k = 2 ^ n := by
      rw [← hn, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have hn3 : 3 ≤ n := by
      by_contra h
      have : 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hkn : k = 2 ^ (n - 2) := by
      have h2 : 2 ^ n = 2 ^ (n - 2) * 2 ^ 2 := by
        rw [← pow_add]
        congr 1
        omega
      omega
    subst hkn
    exact ⟨P, n, hn3, ⟨e⟩⟩

theorem zassenhausPerfect_holds :
    UCK.ZassenhausPerfect := by
  intro p _ G _ _ hperf V _ _ _ ρ hρ hfix hG1
  have hf : Fpf ρ := hfix
  haveI : Nontrivial G :=
    Finite.one_lt_card_iff_nontrivial.mp (by have := Nat.card_pos (α := G); omega)
  haveI : Nontrivial V := nontrivial_of_injective hρ
  haveI : Group.IsPerfect G := Group.isPerfect_def.mpr hperf
  have hnsol : ¬ Group.IsSolvable G := Group.IsPerfect.not_isSolvable G
  have hev : 2 ∣ Nat.card G := by
    by_contra h
    exact hnsol (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.mpr (by omega)))
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hf.not_dvd_card hev
  have hOb : CFSG.oddCore G = ⊥ :=
    oddCore_eq_bot_of_isPerfect hperf fun q _ hq P => hf.isCyclic_sylow hρ hq P
  obtain ⟨P, r, hr, hq⟩ := exists_sylow_quaternion hperf hρ hf
  let eG : G ≃* G ⧸ CFSG.oddCore G :=
    (QuotientGroup.quotientBot (G := G)).symm.trans (QuotientGroup.quotientMulEquivOfEq hOb.symm)
  have hperfQ : commutator (G ⧸ CFSG.oddCore G) = ⊤ :=
    Group.isPerfect_def.mp (inferInstance : Group.IsPerfect (G ⧸ CFSG.oddCore G))
  rcases CFSG.ClassicalInvolution.quaternion_sylow_structure_of_perfect P ⟨r, hr, hq⟩ hperfQ with
    ⟨F, _, _, hF, ⟨eF⟩⟩ | ⟨-, -, ⟨eA⟩⟩
  · let e : G ≃* SL(2, F) := eG.trans eF
    haveI : Group.IsPerfect SL(2, F) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    let ρ' : Representation (ZMod p) SL(2, F) V := ρ.comp e.symm.toMonoidHom
    have hρ' : Function.Injective ρ' := hρ.comp e.symm.injective
    have hf' : Fpf ρ' := fun g hg v hv =>
      hf (e.symm g) (fun h => hg (e.symm.injective (h.trans (map_one e.symm).symm))) v hv
    have h5 : Nat.card F = 5 :=
      card_eq_five_of_fpf_sl2 hp2 hF (Group.isPerfect_def.mp inferInstance) hρ' hf'
    obtain ⟨eR⟩ := CFSG.ClassicalInvolution.G2D4Models.exists_ringEquiv_zmod_five h5
    exact ⟨e.trans (slEquivOfRingEquiv eR)⟩
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    let f : G →* alternatingGroup (Fin 7) :=
      eA.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center (G ⧸ CFSG.oddCore G))).comp
        (QuotientGroup.mk' (CFSG.oddCore G)))
    have hfs : Function.Surjective f :=
      eA.surjective.comp ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
    exact (false_of_surjective_alt7 (fun P => hf.isCyclic_sylow hρ (by norm_num) P) hfs).elim

end CFSG.LocalAnalysis.UniquenessCase.UCK.Zass
