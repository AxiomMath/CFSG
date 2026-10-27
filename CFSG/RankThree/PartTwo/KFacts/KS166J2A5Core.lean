module

public import CFSG.RankThree.PartTwo.KFacts.KS166J2A5Alt5
import CFSG.RankThree.PartTwo.Sec15.Wales154KJ2
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KS155.J2E4
import CFSG.RankThree.PartTwo.KFacts.KS14HJNative
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Sig5
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig.J2

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS166

open Subgroup CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover

theorem pCore_eq_bot
    {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2))
    {K E : Subgroup X} (hKp : Group.IsPerfect ↥K)
    (hKA : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)))
    (hEK : E ≤ normalizer (K : Set X)) (hE9 : Nat.card E = 9) : CFSG.pCore 2 ↥K = ⊥ := by
  classical
  set Q : Subgroup X := CFSG.Open.pCoreOf 2 K with hQdef
  have hQmap : Q = (CFSG.pCore 2 ↥K).map K.subtype := rfl
  by_contra hne
  have hQne : Q ≠ ⊥ := by
    intro hbot
    apply hne
    exact (Subgroup.map_eq_bot_iff_of_injective (CFSG.pCore 2 ↥K) K.subtype_injective).mp
      (by rw [← hQmap]; exact hbot)
  have hKcard : Nat.card K = 60 * Nat.card Q := card_eq_sixty_mul_card_pCoreOf hKA
  have hKne : K ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card K = 1 := by rw [hbot, Subgroup.card_bot]
    rw [h1] at hKcard
    have hpos : 0 < Nat.card Q := Nat.card_pos
    omega
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K
  have hEQ : E ≤ Subgroup.normalizer (Q : Set X) :=
    hEK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) K)
  have hKQ : K ≤ Subgroup.normalizer (Q : Set X) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) K
  have hfour := CFSG.RankThree.PartTwo.Sec15.Wales154.ks154J2Four X hX E K Q
    hE3 (by omega) hKne hKp hEK hQne hQ2 hEQ hKQ
  have hKC : K ≤ Subgroup.centralizer (Q : Set X) :=
    CFSG.RankThree.PartTwo.Sec15.Proof155w3.le_centralizer_of_isPerfect_of_card_four
      hKp hKQ hfour.1
  obtain ⟨φ⟩ := CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.ks155J2CentE4 X hX Q hfour.1 hfour.2
    ⟨K, hKne, hKp, hKC⟩
  have hcardC : Nat.card ↥(Subgroup.centralizer (Q : Set X)) = 240 := by
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2)]
      exact Nat.card_zmod 2
    rw [Nat.card_congr φ.toEquiv, Nat.card_prod, Nat.card_prod, h2,
      nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hcardK : Nat.card K = 240 := by
    rw [hKcard, hfour.1]
  have hKeq : K = Subgroup.centralizer (Q : Set X) :=
    Subgroup.eq_of_le_of_card_ge hKC (by rw [hcardK, hcardC])
  have hperf : Group.IsPerfect
      ((Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) × alternatingGroup (Fin 5)) := by
    haveI : Group.IsPerfect ↥K := hKp
    exact Group.IsPerfect.ofSurjective
      (f := ((MulEquiv.subgroupCongr hKeq).trans φ).toMonoidHom)
      ((MulEquiv.subgroupCongr hKeq).trans φ).surjective
  exact not_isPerfect_klein_prod_alt5 hperf

theorem exists_mulEquiv_E0
    {X : Type} [Group X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) {E : Subgroup X}
    (hE9 : Nat.card E = 9) : ∃ ψ : X ≃* GJ, E.map ψ.toMonoidHom = E0 := by
  obtain ⟨e⟩ := hX
  let ε₀ : X ≃* GJ := e.trans CFSG.ComponentClassification.J2Cover.nativeEquivP
  have hcard : Nat.card (E.map ε₀.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective ε₀.injective, hE9]
  have hE0 : Nat.card E0 = 9 := by rw [card_E0]; norm_num
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.KFacts.KS14.Native.j2_exists_conjugate_of_card_nine
    ⟨CFSG.ComponentClassification.J2Cover.nativeEquivP.symm⟩ hcard hE0
  refine ⟨ε₀.trans (MulAut.conj g⁻¹), ?_⟩
  have e1 : (ε₀.trans (MulAut.conj g⁻¹)).toMonoidHom =
      (MulAut.conj g⁻¹).toMonoidHom.comp ε₀.toMonoidHom := rfl
  rw [e1, ← Subgroup.map_map]
  exact hg.symm

theorem exists_frame
    {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2))
    {K E : Subgroup X} (hKp : Group.IsPerfect ↥K)
    (hKA : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)))
    (hEK : E ≤ normalizer (K : Set X)) (hE9 : Nat.card E = 9) :
    ∃ ψ : X ≃* GJ, E.map ψ.toMonoidHom = E0 ∧
      Nonempty (↥(K.map ψ.toMonoidHom) ≃* alternatingGroup (Fin 5)) ∧
      K.map ψ.toMonoidHom ≤ centralizer ({zJ} : Set GJ) := by
  obtain ⟨ψ, hψE⟩ := exists_mulEquiv_E0 hX hE9
  have hpc : CFSG.pCore 2 ↥K = ⊥ := pCore_eq_bot hX hKp hKA hEK hE9
  obtain ⟨eK⟩ := nonempty_alt5_of_pCore_eq_bot hKA hpc
  have hKA' : Nonempty (↥(K.map ψ.toMonoidHom) ≃* alternatingGroup (Fin 5)) :=
    nonempty_alt5_map ψ ⟨eK⟩
  let φ : ↥(K.map ψ.toMonoidHom) ≃* alternatingGroup (Fin 5) := hKA'.some
  have hEK' : E0 ≤ Subgroup.normalizer ((K.map ψ.toMonoidHom : Subgroup GJ) : Set GJ) := by
    rw [← Subgroup.map_equiv_normalizer_eq K ψ, ← hψE]
    exact Subgroup.map_mono hEK
  have hE09 : Nat.card E0 = 9 := by rw [card_E0]; norm_num
  obtain ⟨e, heE, he1, heC⟩ := exists_ne_one_mem_centralizer φ hEK' hE09
  have hmem : ∀ x ∈ K.map ψ.toMonoidHom,
      x ∈ Subgroup.centralizer ({e} : Set GJ) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp heC) x hx
  refine ⟨ψ, hψE, hKA', ?_⟩
  rcases E0_elt_pow heE he1 with ⟨n, hn⟩ | ⟨k, n, hn⟩
  · intro x hx
    exact CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig.centralizer_le_of_pow hn
      (hmem x hx)
  · exfalso
    have hle : K.map ψ.toMonoidHom ≤ Subgroup.centralizer ({aJ k} : Set GJ) := by
      intro x hx
      exact CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig.centralizer_le_of_pow hn
        (hmem x hx)
    have hdvd : Nat.card (K.map ψ.toMonoidHom) ∣ 36 := by
      have h := Subgroup.card_dvd_of_le hle
      rwa [CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig.card_centralizer_aJ k] at h
    have h60 : Nat.card (K.map ψ.toMonoidHom) = 60 := card_of_alt5 φ
    rw [h60] at hdvd
    omega

end CFSG.RankThree.PartTwo.KFacts.KS166
