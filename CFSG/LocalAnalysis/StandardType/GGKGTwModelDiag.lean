module

public import CFSG.LocalAnalysis.StandardType.GGKGTwDescent
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelKGFrameE
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHolds

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc TableBExc.E6Three
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.E6ThreeModel

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem modelDiag_of_good_cover {R : Type} [Group R] (hAL : GGAbelianLift) (D : FrameData R)
    (hD : D.Good) (hcov : CoverOdd R) {L' : Type} [Group L'] [Finite L'] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {ρ : MulAut L' →* MulAut R}
    (hρ : ∀ a l, ρ a (ψ l) = ψ (a l)) (hρinj : Function.Injective ρ)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A) (hsc : GGTorusSelfCent 3 A)
    (hal : ∀ a ∈ A, ρ a ∈ D.diag.range) :
    ∃ Φ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3), (∀ a : A, D.diag (Φ a) = ρ a) ∧
      ∃ (T : Subgroup L') (w : Fin 6 → L'), Body ψ.ker A Φ T w := by
  classical
  haveI : Finite R := Finite.of_surjective ψ hψ
  have hZ : ψ.ker = Subgroup.center L' := BstarDesc.ker_eq_center hψ hker hD.center
  have hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker) := fun a ha =>
    U63TB.mem_presZ_of_ker hker fun z hz =>
      U63TB.preserves_ker (I := Set.univ) ⟨ρ a, Set.mem_univ _, fun l => hρ a l⟩ hz
  have hψb : Function.Surjective (U63TB.psi1 hker) := U63TB.psi1_surjective hker hψ
  have hkerb := U63TB.psi1_ker_central hker
  have hperfb := U63TB.commutator_quot hker hperf
  have hodd := U63TB.odd_card_ker_psi1 hker
  have hcardb : Nat.card (U63TB.psi1 hker).ker = 1 ∨ Nat.card (U63TB.psi1 hker).ker = 3 := by
    obtain ⟨k, hk⟩ := hcov _ (U63TB.psi1 hker) hψb hkerb hperfb
    have h3 : Nat.card (U63TB.psi1 hker).ker ∣ 3 :=
      (Nat.Coprime.pow_right k hodd.coprime_two_right).dvd_of_dvd_mul_left hk
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    exacts [Or.inl h, Or.inr h]
  have hZb := BstarDesc.ker_eq_center hψb hkerb hD.center
  let ρb := BstarDesc.descAut hψb hZb
  have hρb : ∀ a l, ρb a (U63TB.psi1 hker l) = U63TB.psi1 hker (a l) := fun a l =>
    BstarDesc.descAut_apply hψb hZb a l
  have hρbinj := BstarDesc.descAut_injective hψb hZb hperfb
  have hAb := U63TB.isElemAbelian_range_redSub hker hAle hA
  have hscb := U63TB.selfCent_quot hker hA hAle hsc
  have hab : ∀ a : A, ρb (U63TB.redSub hker hAle a) = ρ a := by
    intro a
    refine MulEquiv.ext fun r => ?_
    obtain ⟨lb, rfl⟩ := hψb r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective lb
    rw [hρb, U63TB.psi1_mk, U63TB.redSub_mk, U63TB.psi1_mk, hρ]
  have halb : ∀ ab ∈ (U63TB.redSub hker hAle).range, ρb ab ∈ D.diag.range := by
    rintro _ ⟨a, rfl⟩
    rw [hab a]
    exact hal a.1 a.2
  obtain ⟨Φb, hΦb, Tb, wb, ⟨hbodyb, hTbodd⟩, -⟩ :=
    model_odd_of_good_diag D hAL hD hψb hkerb hcardb hρb hρbinj hAb hscb halb
  obtain ⟨T, w, hbody⟩ :=
    model_descent_explicit hker hZ hperf hA hAle hbodyb hTbodd
  let Φ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3) :=
    Φb.comp (U63TB.redSub hker hAle).rangeRestrict
  have hΦ : ∀ a : A, D.diag (Φ a) = ρ a := by
    intro a
    have h1 : Φ a = Φb ⟨U63TB.redSub hker hAle a, ⟨a, rfl⟩⟩ := rfl
    rw [h1]
    exact (hΦb ⟨U63TB.redSub hker hAle a, ⟨a, rfl⟩⟩).trans (hab a)
  exact ⟨Φ, hΦ, T, w, hbody⟩

end CFSG.StandardType.KGL

end
