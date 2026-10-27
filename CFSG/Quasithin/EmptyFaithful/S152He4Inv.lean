module

public import CFSG.Quasithin.EmptyFaithful.S152He4Count
public import CFSG.Quasithin.EmptyFaithful.S152He4Layer
public import CFSG.LieType.SteinbergBROddLinearThreeInvolution
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.TabBigM11
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentAlt
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinear
public import CFSG.Assembly.OrderReductions.CharacterInflation
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Rank2
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Sporadic.Schreier.M23
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import Certificates.Certificate8026Base

public section

namespace CFSG.Quasithin.He4

open CFSG.Assembly.LowTwoRank

theorem noInvCommNine_l33 {X : Type} [Group X] (h : StatedClassicalModel X .PSL 3 3 1) :
    NoInvCommNine X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK3 : Nat.card K = 3 := by simpa using hK
  refine NoInvCommNine.of_mulEquiv (e.trans (CFSG.QuasithinUnique.K1.statedProjEquivProjectiveSL 3 K)) ?_
  intro P hP t ht hc
  by_contra hne
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht) hne
  have hcent := (CFSG.LieType.unique_odd_linear_three_involution_centralizer_component_or_unique_core_involution
    (K := K) (by rw [hK3]; decide) (by rw [hK3]) t hord).2 hK3
  have hle : P ≤ Subgroup.centralizer ({t} : Set _) := fun p hp =>
    Subgroup.mem_centralizer_singleton_iff.2 (hc p hp)
  have := Subgroup.card_dvd_of_le hle
  rw [hP, hcent.2.1] at this
  omega

theorem noInvCommNine_m11 {X : Type} [Group X]
    (h : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) : NoInvCommNine X := by
  obtain ⟨e⟩ := h
  let e' : X ≃* ↥CFSG.Blueprint.NativeSporadic.M11 := e
  refine NoInvCommNine.of_mulEquiv e' ?_
  intro P hP t ht hc
  by_contra hne
  obtain ⟨g, hg⟩ := CFSG.QuasithinUnique.Vol2Native.L239.M11Insp.exists_conj ht hne
  have hle : P.map (MulAut.conj g⁻¹).toMonoidHom ≤
      Subgroup.centralizer ({CFSG.QuasithinUnique.Unc25G2.gA} : Set _) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : p * t = t * p := hc p hp
    rw [← hg] at h1
    change (g⁻¹ * p * g⁻¹⁻¹) * CFSG.QuasithinUnique.Unc25G2.gA =
      CFSG.QuasithinUnique.Unc25G2.gA * (g⁻¹ * p * g⁻¹⁻¹)
    calc (g⁻¹ * p * g⁻¹⁻¹) * CFSG.QuasithinUnique.Unc25G2.gA
        = g⁻¹ * (p * (g * CFSG.QuasithinUnique.Unc25G2.gA * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * CFSG.QuasithinUnique.Unc25G2.gA * g⁻¹) * p) * g := by rw [h1]
      _ = CFSG.QuasithinUnique.Unc25G2.gA * (g⁻¹ * p * g⁻¹⁻¹) := by group
  have := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
    (MulAut.conj g⁻¹).injective, hP,
    CFSG.QuasithinUnique.DoubleA3.TabBigM11.card_centralizer_gA] at this
  omega


theorem noInvCommNine_alt8 : NoInvCommNine ↥(alternatingGroup (Fin 8)) := by
  intro P hP t ht hc
  by_contra hne
  set σ : Equiv.Perm (Fin 8) := (t : Equiv.Perm (Fin 8)) with hσ
  have hσ2 : σ * σ = 1 := by simpa using congrArg Subtype.val ht
  have hσ1 : σ ≠ 1 := fun h => hne (Subtype.ext h)
  obtain ⟨k, hk1, hkc⟩ := CFSG.QuasithinUnique.Id2519.involution_cycleType hσ2 hσ1
  have h2k : 2 * k ≤ 8 := by
    simpa using CFSG.QuasithinUnique.Id2519.two_mul_le_of_cycleType hkc
  have hsign : Equiv.Perm.sign σ = 1 := Equiv.Perm.mem_alternatingGroup.1 t.2
  rw [CFSG.QuasithinUnique.Id2519.sign_involution hkc] at hsign
  have hkeven : Even k := (neg_one_pow_eq_one_iff_even (by decide)).1 hsign
  have hC := CFSG.QuasithinUnique.Id2519.card_centralizer_involution hk1 hkc
  have hle : P.map (alternatingGroup (Fin 8)).subtype ≤
      Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 8))) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hc p hp)
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hP, hC] at hdvd
  obtain ⟨m, rfl⟩ := hkeven
  have hm : m = 1 ∨ m = 2 := by omega
  rcases hm with rfl | rfl <;> simp [Nat.factorial] at hdvd

theorem nonempty_mulEquiv_alt8 {X : Type} [Group X] (h : StatedClassicalModel X .PSL 4 2 1) :
    Nonempty (X ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hK
  exact ⟨((e.trans (CFSG.GH74.Exceptional.statedProjStatedSLEquivOfCardTwo hK2 4)).trans
    (CFSG.GH74.Exceptional.glEquivZModTwoOfCardTwo hK2 4)).trans
    CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.symm⟩

theorem noInvCommNine_l42 {X : Type} [Group X] (h : StatedClassicalModel X .PSL 4 2 1) :
    NoInvCommNine X := by
  obtain ⟨e⟩ := nonempty_mulEquiv_alt8 h
  exact NoInvCommNine.of_mulEquiv e noInvCommNine_alt8


theorem noInvCommNine_l52 {X : Type} [Group X] (h : StatedClassicalModel X .PSL 5 2 1) :
    NoInvCommNine X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hK
  let e₂ := CFSG.GH74.Exceptional.statedProjStatedSLEquivOfCardTwo hK2 5
  let e₄ := CFSG.GH74.Exceptional.glEquivZModTwoOfCardTwo hK2 5
  let f : X →* GL (Fin 5) (ZMod 2) := e₄.toMonoidHom.comp (e.trans e₂).toMonoidHom
  have hf : Function.Injective f := e₄.injective.comp (e.trans e₂).injective
  exact NoInvCommNine.of_injective f hf (noInvCommNine_gl 5 le_rfl)

end CFSG.Quasithin.He4
