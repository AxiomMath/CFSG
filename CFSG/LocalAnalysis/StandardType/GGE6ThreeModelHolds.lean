module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelAssemble
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelLiftTwo
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelTransport
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDesc

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three

theorem coverOdd_transport {R R' : Type} [Group R] [Group R'] (e : R ≃* R') :
    CoverOdd R → CoverOdd R' := by
  intro h L' _ _ ψ' hψ' hker hperf
  have hψ : Function.Surjective (e.symm.toMonoidHom.comp ψ') := e.symm.surjective.comp hψ'
  have hkerEq : (e.symm.toMonoidHom.comp ψ').ker = ψ'.ker := by
    ext l
    simp [MonoidHom.mem_ker]
  have := h L' (e.symm.toMonoidHom.comp ψ') hψ (hkerEq ▸ hker) hperf
  rwa [hkerEq] at this

theorem exists_align {R : Type} [Group R] {L' : Type} [Group L'] (D : FrameData R) (hD : D.Shape)
    {ρ : MulAut L' →* MulAut R} (hρinj : Function.Injective ρ)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A) (h5 : 3 ^ 5 ≤ Nat.card A)
    (hAH : ∀ a ∈ A, ρ a ∈ D.H) :
    ∃ γ ∈ D.H, ∀ a ∈ A, γ * ρ a * γ⁻¹ ∈ D.diag.range := by
  have hXel : CFSG.Open.IsElemAbelian 3 (A.map ρ) := by
    obtain ⟨hc, hp⟩ := hA
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨_, a, ha, rfl⟩ := x
      obtain ⟨_, b, hb, rfl⟩ := y
      apply Subtype.ext
      have := hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
      have h2 := congrArg (fun z : A => ρ (z : MulAut L')) this
      simpa [map_mul] using h2
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hp a ha, map_one]
  have hcard : Nat.card (A.map ρ) = Nat.card A := Subgroup.card_map_of_injective hρinj
  obtain ⟨γ, hγ, hγX⟩ := hD (A.map ρ) (by rintro _ ⟨a, ha, rfl⟩; exact hAH a ha) hXel
    (by rw [hcard]; exact h5)
  exact ⟨γ, hγ, fun a ha => hγX _ ⟨a, ha, rfl⟩⟩

theorem modelSCr_of_good {R : Type} [Group R] (hAL : GGAbelianLift) (D : FrameData R)
    (hD : D.Good) (hcov : CoverOdd R) (I : Set (MulAut R)) (hI : (D.H : Set (MulAut R)) = I) :
    GGE6ThreeModelSCr R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h5 hsc
  haveI : Finite R := Finite.of_surjective ψ hψ
  have hZ : ψ.ker = Subgroup.center L' := BstarDesc.ker_eq_center hψ hker hD.center
  let ρ : MulAut L' →* MulAut R := BstarDesc.descAut hψ hZ
  have hρ : ∀ a l, ρ a (ψ l) = ψ (a l) := fun a l => BstarDesc.descAut_apply hψ hZ a l
  have hρinj : Function.Injective ρ := BstarDesc.descAut_injective hψ hZ hperf
  have hAH : ∀ a ∈ A, ρ a ∈ D.H := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    have hρφ : ρ a = φ := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨l, rfl⟩ := hψ r
      rw [hρ, hφ]
    have hφH : φ ∈ (D.H : Set (MulAut R)) := by rw [hI]; exact hφI
    rw [hρφ]
    exact hφH
  obtain ⟨γ, -, hγ⟩ := exists_align D hD.shape hρinj hA h5 hAH
  let ψ' : L' →* R := γ.toMonoidHom.comp ψ
  have hψ' : Function.Surjective ψ' := γ.surjective.comp hψ
  have hkerEq : ψ'.ker = ψ.ker := by
    ext l
    simp [ψ', MonoidHom.mem_ker]
  have hker' : ψ'.ker ≤ Subgroup.center L' := hkerEq ▸ hker
  have hZ' : ψ'.ker = Subgroup.center L' := hkerEq ▸ hZ
  let ρ' : MulAut L' →* MulAut R := BstarDesc.descAut hψ' hZ'
  have hρ' : ∀ a l, ρ' a (ψ' l) = ψ' (a l) := fun a l => BstarDesc.descAut_apply hψ' hZ' a l
  have hρ'eq : ∀ a, ρ' a = γ * ρ a * γ⁻¹ := by
    intro a
    refine MulEquiv.ext fun r => ?_
    obtain ⟨l, rfl⟩ := hψ' r
    rw [hρ']
    simp only [ψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.mul_apply,
      MulAut.inv_apply_self, hρ, map_mul]
  have hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ'.ker hker') := fun a ha =>
    U63TB.mem_presZ_of_ker hker' fun z hz =>
      U63TB.preserves_ker (I := Set.univ) ⟨ρ' a, Set.mem_univ _, fun l => hρ' a l⟩ hz
  have hψb : Function.Surjective (U63TB.psi1 hker') := U63TB.psi1_surjective hker' hψ'
  have hkerb := U63TB.psi1_ker_central hker'
  have hperfb := U63TB.commutator_quot hker' hperf
  have hodd := U63TB.odd_card_ker_psi1 hker'
  have hcardb : Nat.card (U63TB.psi1 hker').ker = 1 ∨ Nat.card (U63TB.psi1 hker').ker = 3 := by
    obtain ⟨k, hk⟩ := hcov _ (U63TB.psi1 hker') hψb hkerb hperfb
    have h3 : Nat.card (U63TB.psi1 hker').ker ∣ 3 :=
      (Nat.Coprime.pow_right k hodd.coprime_two_right).dvd_of_dvd_mul_left hk
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    exacts [Or.inl h, Or.inr h]
  have hZb := BstarDesc.ker_eq_center hψb hkerb hD.center
  let ρb := BstarDesc.descAut hψb hZb
  have hρb : ∀ a l, ρb a (U63TB.psi1 hker' l) = U63TB.psi1 hker' (a l) := fun a l =>
    BstarDesc.descAut_apply hψb hZb a l
  have hρbinj := BstarDesc.descAut_injective hψb hZb hperfb
  have hAb := U63TB.isElemAbelian_range_redSub hker' hAle hA
  have hscb := U63TB.selfCent_quot hker' hA hAle hsc
  have halb : ∀ ab ∈ (U63TB.redSub hker' hAle).range, ρb ab ∈ D.diag.range := by
    rintro _ ⟨a, rfl⟩
    have hab : ρb (U63TB.redSub hker' hAle a) = ρ' a.1 := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨lb, rfl⟩ := hψb r
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective lb
      rw [hρb, U63TB.psi1_mk, U63TB.redSub_mk, U63TB.psi1_mk, hρ']
    rw [hab, hρ'eq]
    exact hγ a.1 a.2
  have hbar := model_odd_of_good D hAL hD hψb hkerb hcardb hρb hρbinj hAb hscb halb
  have hmodel := model_descent hker' hZ' hperf hA hAle hbar
  rwa [hkerEq] at hmodel

end CFSG.StandardType.E6ThreeModel
