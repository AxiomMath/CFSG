module

public import CFSG.RankThree.PartTwo.Sec17.Item174StarL3
public import CFSG.RankThree.PartTwo.Sec17.Item174StarU3Odd
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
import CFSG.RankThree.PartTwo.Census.Classical.Bridges
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU3Char3Outer

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof174Host

open CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves U3

variable {p f : ℕ} {K : Type} [Field K]

theorem U3.comm_tau_omega (h : UnitaryFieldData p f K) {ω : Kˣ} (hω : orderOf ω = 3)
    (hωb : h.bar (ω : K) = ω) {D : Subgroup (hypSU h 1 1)} (hD : IsPGroup 2 D)
    (hs : sSU h ∈ Subgroup.normalizer (D : Set (hypSU h 1 1)))
    (hT : ∀ x : Kˣ, tau h x ∈ Subgroup.normalizer (D : Set (hypSU h 1 1))) :
    ∀ d ∈ D, d * tau h ω = tau h ω * d := by
  by_cases hp : p = 2
  · subst hp
    rw [eq_bot_of_two h hω hωb hD (hT ω) hs]
    intro d hd
    rw [Subgroup.mem_bot] at hd
    rw [hd, one_mul, mul_one]
  · exact comm_of_odd h hp hω hωb hD hT

theorem U3.starCore_hypSU [Finite K] (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 1)
    (hcyc : ∀ X : Subgroup (hypSU h 1 1), IsPGroup 3 X → IsCyclic X) :
    StarCore (hypSU h 1 1) := by
  intro _ t ht I hI D hDI hD hID hcomm
  exfalso
  apply hcomm
  obtain ⟨ω, hω, hωb⟩ := exists_omega h hq
  set c := tau h ω with hc
  have hoc : orderOf c = 3 := orderOf_tau_omega h hω hωb
  obtain ⟨g, hg⟩ := exists_conj_eq_of_card_eq_three hcyc
    (show Nat.card (Subgroup.zpowers c) = 3 by rw [Nat.card_zpowers, hoc])
    (show Nat.card (Subgroup.zpowers t) = 3 by rw [Nat.card_zpowers, ht])
  set φ := (MulAut.conj g).toMonoidHom with hφ_def
  have hφ : Function.Injective φ := (MulAut.conj g).injective
  have hφs : Function.Surjective φ := (MulAut.conj g).surjective
  have hN : ∀ x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set (hypSU h 1 1)),
      x ∈ Subgroup.normalizer ((D.comap φ : Subgroup (hypSU h 1 1)) : Set (hypSU h 1 1)) :=
    fun x hx => Subgroup.le_normalizer_comap φ (hID (hI (by
      rw [hg, ← Subgroup.map_equiv_normalizer_eq]
      exact ⟨x, hx, rfl⟩)))
  have hsc : sSU h * c * (sSU h)⁻¹ = c⁻¹ := by
    rw [hc, sSU_mul_tau_omega h hω hωb, mul_inv_cancel_right]
  have hsc' : (sSU h)⁻¹ * c * sSU h = c⁻¹ := by
    have := congrArg (fun k => (sSU h)⁻¹ * k⁻¹ * sSU h) hsc
    simp only [inv_inv] at this
    rw [← this]
    group
  have hsN := hN _ (mem_normalizer_zpowers_of (by rw [hsc]; exact inv_mem (Subgroup.mem_zpowers c))
    (by rw [hsc']; exact inv_mem (Subgroup.mem_zpowers c)))
  have hTN : ∀ x : Kˣ, tau h x ∈ Subgroup.normalizer
      ((D.comap φ : Subgroup (hypSU h 1 1)) : Set (hypSU h 1 1)) := fun x =>
    hN _ (mem_normalizer_zpowers_of
      (by rw [hc, tau_comm, mul_inv_cancel_right]; exact Subgroup.mem_zpowers _)
      (by rw [hc, mul_assoc, tau_comm h ω x, inv_mul_cancel_left]; exact Subgroup.mem_zpowers _))
  have key : ⁅D.comap φ, Subgroup.zpowers c⁆ = ⊥ :=
    commutator_zpowers_eq_bot
      (comm_tau_omega h hω hωb (hD.comap_of_injective φ hφ) hsN hTN)
  have := congrArg (Subgroup.map φ) key
  rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hφs, ← hg,
    Subgroup.map_bot] at this
  exact this

theorem starU3_proved : StarU3 := by
  intro H _ _ d q hq hd ⟨e⟩
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hqf : q.p ^ q.exponent % 3 = 1 := by rwa [← TauCeti.PrimePower.card_def]
  have h3 : ¬ 3 ∣ q.p ^ q.exponent + 1 := by omega
  set h := CFSG.RankThree.PartTwo.Sec4.unitaryFieldData_galoisField q.p q.exponent hf
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) h
  have eS : hypSU h 1 1 ≃* CFSG.PGLModel.projSU 3 q.p q.exponent :=
    (hypTransport h hR).trans
      ((CFSG.RankThree.PartTwo.Sec4.RonanK432.U3Char3.unitaryPSUEquivSU_of_not_dvd h h3).trans
        (CFSG.RankThree.PartTwo.Sec4.projSUEquivUnitaryPSU q.p q.exponent h).symm)
  have hcyc : ∀ X : Subgroup (hypSU h 1 1), IsPGroup 3 X → IsCyclic X := by
    intro X hX
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨Q, hQ⟩ := hX.exists_le_sylow
    have := CFSG.RankThree.PartTwo.KFacts.isCyclic_sylow_three_of_mulEquiv_projSU (by omega) hqf
      eS Q
    exact Subgroup.isCyclic_of_le hQ
  exact starFor_of_starCore (starCore_of_mulEquiv
    ((e.trans (CFSG.RankThree.PartTwo.Census.typeTwistedAGroupEquivProjSU 2 q hv)).trans eS.symm)
    (starCore_hypSU h hqf hcyc))

theorem kfactStar_proved
    (hS : CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactThreeRankOneSimple) : KFactStar :=
  kfactStar_of_U3 hS starU3_proved

end CFSG.RankThree.PartTwo.Sec17.Proof174Host
