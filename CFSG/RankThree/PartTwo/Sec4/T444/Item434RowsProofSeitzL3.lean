module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.RankThree.PartTwo.Sec4.T444.Item434Kit
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (higher_linear_outer_order_divides_field_gcd_bound)

@[expose] def IsLie42GenericL3Vac (X : Type) [Group X] : Prop :=
  ∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 3 ∧ 1 ≤ e ∧ ¬ 3 ∣ e ∧
    ((p ^ e % 3 = 2 ∧ Nonempty (X ≃* projSL 3 (GaloisField p e))) ∨
      (p ^ e % 3 = 1 ∧ Nonempty (X ≃* projSU 3 p e)))

namespace Item434RowsProof

theorem card_le_three_of_cyclic_sylow_of_outer {X S : Type} [Group X] [Finite X] [Group S]
    [Finite S] (hq : IsQuasisimple X) (hZ3 : IsPGroup 3 (Subgroup.center X))
    (θ : X ⧸ Subgroup.center X ≃* S) (hcyc : ∀ Q : Sylow 3 S, IsCyclic (Q : Subgroup S))
    (hout : ¬ 3 ∣ Nat.card (Outer S)) {E : Subgroup (MulAut X)} (hE : ∀ α ∈ E, α ^ 3 = 1) :
    Nat.card E ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect X := hq.1
  set π : X →* S := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)) with hπ
  have hπs : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center X := by
    ext x
    rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hZ : Subgroup.center X = ⊥ := by
    have hkp : IsPGroup 3 π.ker := by rw [hker]; exact hZ3
    have htp : IsPGroup 3 (⊤ : Subgroup π.ker) :=
      hkp.of_equiv (Subgroup.topEquiv).symm
    obtain ⟨C, hC⟩ := htp.exists_le_sylow
    obtain ⟨Q⟩ : Nonempty (Sylow 3 S) := inferInstance
    have hC1 := CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot π hπs
      (by rw [hker]) C Q (hcyc Q)
    rw [← hker, eq_bot_iff]
    intro x hx
    have hxC : (⟨x, hx⟩ : π.ker) ∈ (C : Subgroup π.ker) := hC (Subgroup.mem_top _)
    rw [hC1, Subgroup.mem_bot] at hxC
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hxC)
  set ι : X ≃* S :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans θ
  set E' : Subgroup (MulAut S) := E.map (MulAut.congr ι).toMonoidHom with hE'
  have hE'3 : ∀ α ∈ E', α ^ 3 = 1 := by
    rintro _ ⟨α, hα, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, hE α hα, map_one]
  have hZS : Subgroup.center S = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : ι.symm z ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply ι.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, Subgroup.mem_center_iff.mp hz (ι g)]
    rw [hZ, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    simpa using congrArg ι hz'
  have hinj := Item434Kit.conj_injective_of_center_eq_bot hZS
  have hinn : E' ≤ (MulAut.conj : S →* MulAut S).range := fun α hα =>
    Item434Kit.mem_range_conj_of_pow_three hout (hE'3 α hα)
  set P : Subgroup S := E'.comap (MulAut.conj : S →* MulAut S) with hP
  have hPmap : P.map MulAut.conj = E' := Subgroup.map_comap_eq_self hinn
  have hP3 : ∀ x ∈ P, x ^ 3 = 1 := fun x hx => hinj (by rw [map_pow, map_one]; exact hE'3 _ hx)
  have hexp : Monoid.exponent P ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (by simpa using hP3 x x.2)
  have hPp : IsPGroup 3 P := IsPGroup.of_exponent_dvd_pow (n := 1) (by rwa [pow_one])
  obtain ⟨R, hR⟩ := hPp.exists_le_sylow
  have : IsCyclic (R : Subgroup S) := hcyc R
  have : IsCyclic P := Subgroup.isCyclic_of_le hR
  rw [IsCyclic.exponent_eq_card] at hexp
  have hcardP : Nat.card P ≤ 3 := Nat.le_of_dvd (by norm_num) hexp
  calc Nat.card E = Nat.card E' := (Subgroup.card_map_of_injective (MulAut.congr ι).injective).symm
    _ = Nat.card P := by rw [← hPmap, Subgroup.card_map_of_injective hinj]
    _ ≤ 3 := hcardP

theorem card_le_three_of_L3Vac {X : Type} [Group X] [Finite X] (hq : IsQuasisimple X)
    (hZ3 : IsPGroup 3 (Subgroup.center X)) (hL : IsLie42GenericL3Vac (X ⧸ Subgroup.center X))
    {E : Subgroup (MulAut X)} (hE : ∀ α ∈ E, α ^ 3 = 1) : Nat.card E ≤ 3 := by
  obtain ⟨p, e, hpF, hp3, he, he3, ⟨hq2, ⟨θ⟩⟩ | ⟨hq1, ⟨θ⟩⟩⟩ := hL
  ·
    have hp : p.Prime := Fact.out
    have : Finite (projSL 3 (GaloisField p e)) := Finite.of_equiv _ θ.toEquiv
    have hK : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
    refine card_le_three_of_cyclic_sylow_of_outer hq hZ3 θ
      (fun Q => KFacts.isCyclic_sylow_three_projSL (by rw [hK]; exact hq2) Q) ?_ hE
    intro h3
    have hd := higher_linear_outer_order_divides_field_gcd_bound hp he (le_refl 3) hK
    rw [← Nat.card_congr (equivalence (projSLEquivProjectiveSL 3 (GaloisField p e))).toEquiv]
      at hd
    have hg : Nat.gcd 3 (p ^ e - 1) = 1 := by
      rw [← Nat.Coprime, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      omega
    rw [hg, mul_one] at hd
    have h3' := h3.trans hd
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3' with h | h
    · exact absurd h (by norm_num)
    · exact he3 h
  ·
    have hp : p.Prime := Fact.out
    have : Finite (projSU 3 p e) := Finite.of_equiv _ θ.toEquiv
    refine card_le_three_of_cyclic_sylow_of_outer hq hZ3 θ
      (fun Q => KFacts.isCyclic_sylow_three_of_mulEquiv_projSU (by omega) hq1
        (MulEquiv.refl _) Q) ?_ hE
    intro h3
    have hd := card_outer_projSU_dvd 3 p e he (le_refl 3) (by
      rintro ⟨-, h2⟩
      rw [h2] at hq1
      norm_num at hq1)
    have h3' := h3.trans hd
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3' with h | h
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
      · exact absurd h (by norm_num)
      · exact he3 h
    · omega

end Item434RowsProof

end CFSG.RankThree.PartTwo.Sec4
