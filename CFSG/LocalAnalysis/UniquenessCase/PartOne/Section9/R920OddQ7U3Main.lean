module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7U3Core
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7U3Frob
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddModel
import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.AGLEmbeddingD2.McLaughlin.OddIndex CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves (exists_conj_eq_of_card_eq_three)

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)
include hF

theorem genSeven_SU3 [IsSimpleGroup (SU (unitaryInvolution F p f) 3)]
    (hst : CFSG.Open.StatedClassicalModel (SU (unitaryInvolution F p f) 3) .PSU 3 p f)
    (hp2 : p ≠ 2) (hq3 : p ^ f % 3 = 1)
    (hcyc : ∀ P : Subgroup (SU (unitaryInvolution F p f) 3), IsPGroup 3 P → IsCyclic P)
    {X : Subgroup (SU (unitaryInvolution F p f) 3)} (hX : IsL2Odd (Bar2 X) 7) :
    GenSeven (SU (unitaryInvolution F p f) 3) X := by
  intro W hXW hD hA
  obtain ⟨a, d, haX, hdX, ha7, hd3, hda⟩ := exists_frobenius_data hX
  obtain ⟨ω, hω⟩ := exists_unit_orderOf_three hF (two_le_prime_pow_of_card hF) hq3
  have hA0 : Nat.card (Subgroup.zpowers (tSU hF ω)) = 3 := by
    rw [Nat.card_zpowers, orderOf_injective _ (tSU_injective hF) ω, hω]
  have hDc : Nat.card (Subgroup.zpowers d) = 3 := by rw [Nat.card_zpowers, hd3]
  obtain ⟨g, hg⟩ := exists_conj_eq_of_card_eq_three hcyc hDc hA0
  have hord : ∀ c y : SU (unitaryInvolution F p f) 3, orderOf (c * y * c⁻¹) = orderOf y :=
    fun c y => by simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj c) y
  set W' := W.map (MulAut.conj g).toMonoidHom with hW'
  have hmem : ∀ y ∈ W, g * y * g⁻¹ ∈ W' := fun y hy =>
    ⟨y, hy, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  have hNW' : normA0 hF ω ≤ W' := by
    show Subgroup.normalizer ((Subgroup.zpowers (tSU hF ω) : Subgroup _) : Set _) ≤ W'
    rw [hg, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono (hD _ (Subgroup.zpowers_le.2 hdX) hDc)
  have hdA : g * d * g⁻¹ ∈ Subgroup.zpowers (tSU hF ω) := by
    rw [hg]
    exact ⟨d, Subgroup.mem_zpowers d, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  have hda' : (g * d * g⁻¹) * (g * a * g⁻¹) * (g * d * g⁻¹)⁻¹ = (g * a * g⁻¹) ^ 2 := by
    have h1 : (g * d * g⁻¹) * (g * a * g⁻¹) * (g * d * g⁻¹)⁻¹ = g * (d * a * d⁻¹) * g⁻¹ := by group
    rw [h1, hda, pow_two, pow_two]
    group
  have hns : ¬ Group.IsSolvable W' := fun hs => by
    refine not_isSolvable_of_isL2Odd_seven hX hXW ?_
    exact Group.isSolvable_of_isSolvable_injective
      (f := (W.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toMonoidHom)
      (W.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).injective
  have hC : ∀ x ∈ Subgroup.centralizer ({g * a * g⁻¹} : Set (SU (unitaryInvolution F p f) 3)),
      Nat.Coprime (orderOf x) 7 → x ∈ W' := by
    intro x hx hcop
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    have hcomm : a * (g⁻¹ * x * g) = (g⁻¹ * x * g) * a := by
      calc a * (g⁻¹ * x * g) = g⁻¹ * ((g * a * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * a * g⁻¹)) * g := by rw [hx]
        _ = (g⁻¹ * x * g) * a := by group
    have hx' : g⁻¹ * x * g ∈ Subgroup.centralizer
        ((Subgroup.zpowers a : Subgroup (SU (unitaryInvolution F p f) 3)) :
          Set (SU (unitaryInvolution F p f) 3)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨k, rfl⟩
      exact (Commute.zpow_left hcomm k).eq
    have hcop' : Nat.Coprime (orderOf (g⁻¹ * x * g)) 7 := by
      have := hord g⁻¹ x
      rw [inv_inv] at this
      rw [this]
      exact hcop
    have hxW := hA (Subgroup.zpowers a) (Subgroup.zpowers_le.2 haX)
      (by rw [Nat.card_zpowers, ha7]) _ hx' hcop'
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [← e]
    exact hmem _ hxW
  have htop := eq_top_of_normA0_le hF hst hp2 hq3 hω hNW' (hmem a (hXW haX)) (by rw [hord, ha7])
    hdA (by rw [hord, hd3]) hda' hC hns
  rw [eq_top_iff]
  intro y _
  have hy : g * y * g⁻¹ ∈ W' := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨w, hw, hwy⟩ := hy
  have hwy' : w = y := by
    apply (MulAut.conj g).injective
    simpa [MulAut.conj_apply] using hwy
  exact hwy' ▸ hw

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

theorem u3GenSeven_holds :
    ∀ (Q : Type) [Group Q] [Finite Q] (p f : ℕ), p ≠ 2 → p ^ f % 3 = 1 → LieModel Q .PSU 3 p f →
      ∀ X : Subgroup Q, IsL2Odd (Bar2 X) 7 → (∀ P : Subgroup Q, IsPGroup 3 P → IsCyclic P) →
        GenSeven Q X := by
  intro Q _ _ p f hp2 hq3 hLie X hX hcyc
  have hst := hLie.statedClassicalModel_of_ne_zero (by norm_num : (3 : ℕ) ≠ 0)
  obtain ⟨F, _, _, _, _, hF, ⟨e⟩⟩ :=
    CFSG.AGLEmbeddingD2.McLaughlin.OddIndex.exists_mulEquiv_SU3 hst hq3
  have hstG := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e hst
  haveI := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hstG
  refine (genSeven_map_equiv_iff e X).1 (Q7U3.genSeven_SU3 hF hstG hp2 hq3 ?_ ?_)
  · intro P hP
    have h2 := hcyc _ (hP.map e.symm.toMonoidHom)
    have e' := P.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
    exact isCyclic_of_surjective e'.symm.toMonoidHom e'.symm.surjective
  · exact LieModel.of_mulEquiv
      (UC6S846.bar2Equiv (X.equivMapOfInjective e.toMonoidHom e.injective)) hX

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
