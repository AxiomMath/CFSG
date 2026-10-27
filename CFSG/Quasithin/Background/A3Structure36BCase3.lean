
module

public import CFSG.Quasithin.Background.A3Structure36BCase3Base

public import CFSG.Quasithin.Background.A3Structure36BElem
public import CFSG.Quasithin.Background.A3Structure36BHeis
public import CFSG.Quasithin.Background.A3Structure36BCaseAux
public import CFSG.Quasithin.Background.A3Structure36BCasesBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.A36B

open scoped commutatorElement
open CFSG.SectionRank CFSG.SectionRank.Ccomm

variable {X : Type} [Group X]

theorem eq_top_of_isElemAbelian_sl2 (hF : A36CaseBFacts) (h : A36BHyp X) {K : Subgroup X}
    (hK : KernelSetup X K) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (D : PrimeData X p)
    (hDK : D.K = K) (hE : IsElemAbelianOfRank p 2 ↥D.P)
    (hFR : CFSG.fittingSubgroup X ≤ CFSG.pCore p X)
    (hs : IsSL2 p (X ⧸ CFSG.fittingSubgroup X)) : D.P = ⊤ := by
  have hfin : Finite X := h.finite
  have hKF : K = CFSG.fittingSubgroup X := kernel_eq_fitting h hK
  obtain ⟨t, ht, ht2, htK⟩ := exists_involution h hK
  obtain ⟨hcommR, -, e, he1, -, hE1, hE2⟩ := elem_case h hK hp D hDK hE ht2 htK
  by_cases he : e = 1
  · exact hE1 he
  · exfalso
    have he2 : 2 ≤ e := by omega
    obtain ⟨T, hTn, hTR, hPT, ⟨φT⟩⟩ := hE2 he2
    have hker : CFSG.fittingSubgroup X ≤
        (MulAut.conjNormal : X →* MulAut ↥T).ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      ext u
      have hxR : x ∈ CFSG.pCore p X := hFR hx
      have hcomm := hcommR ⟨x, hxR⟩ ⟨(u : X), hTR u.2⟩
      have hxu : x * (u : X) = (u : X) * x := congrArg Subtype.val hcomm
      change x * (u : X) * x⁻¹ = (u : X)
      rw [mul_inv_eq_iff_eq_mul]
      exact hxu
    let f' : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* MulAut ↥T :=
      (QuotientGroup.lift (CFSG.fittingSubgroup X) _ hker).comp
        (Classical.choice hs).symm.toMonoidHom
    have hinj : Function.Injective f' := by
      rw [injective_iff_map_eq_one]
      intro s hs1
      obtain ⟨y, rfl⟩ := (Classical.choice hs).surjective s
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      have hf : (MulAut.conjNormal : X →* MulAut ↥T) x = 1 := by
        have : f' ((Classical.choice hs) (x : X ⧸ CFSG.fittingSubgroup X)) =
            (MulAut.conjNormal : X →* MulAut ↥T) x := by
          simp [f']
        rw [← this]
        exact hs1
      have hxD : x ∈ D.K := by
        rw [D.mem_K]
        intro d hd
        have hdT : ((d : ↥(CFSG.pCore p X)) : X) ∈ T := hPT ⟨d, hd, rfl⟩
        have h2 := congrArg (fun φ : MulAut ↥T => ((φ ⟨(d : X), hdT⟩ : ↥T) : X)) hf
        simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
        have h3 : MulAut.conjNormal x d = d := Subtype.ext h2
        rw [h3, inv_mul_cancel]
        exact Subgroup.one_mem _
      have hxF : x ∈ CFSG.fittingSubgroup X := hKF ▸ hDK ▸ hxD
      have : (x : X ⧸ CFSG.fittingSubgroup X) = 1 := (QuotientGroup.eq_one_iff x).2 hxF
      rw [this, map_one]
    exact hF.a130 p hp hp3 ↥T ⟨φT.trans (multFinTwoEquiv (p ^ 2)).symm⟩ f' hinj

theorem case3 (hF : A36CaseBFacts) (h : A36BHyp X) {K : Subgroup X} (hK : KernelSetup X K)
    (h5 : ¬ IsSL2 5 (X ⧸ CFSG.fittingSubgroup X)) : A36Case3 X := by
  have hfin : Finite X := h.finite
  have hKF : K = CFSG.fittingSubgroup X := kernel_eq_fitting h hK
  obtain ⟨p, hp, hπ⟩ := exists_isPi h
  have hfp : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := IsPi.ne_two h hπ
  obtain ⟨D, hDK⟩ := hK.prime p hp hπ
  have hDn : D.K.Normal := D.normal_K
  have hs : IsSL2 p (X ⧸ CFSG.fittingSubgroup X) := by
    rcases D.sl2 with hs | ⟨-, hs⟩
    · exact isSL2_quotient_congr (hDK.trans hKF) hs
    · exact absurd (isSL2_quotient_congr (hDK.trans hKF) hs) h5
  have hFtop : CFSG.fittingSubgroup X ≠ ⊤ := fun htop =>
    radical_ne_top h (eq_top_iff.2 (htop ▸ fitting_le_radical))
  have hp5 : 5 ≤ p := five_le_of_isSL2 h hFtop hp hp2 hs
  have hp5' : p ≠ 5 := fun h' => h5 (h' ▸ hs)
  have hp3 : 3 < p := by omega
  have hall : ∀ q : ℕ, q.Prime → q ∣ Nat.card (CFSG.fittingSubgroup X) → q = p := by
    intro q hq hqF
    have hπq := isPi_of_dvd_card_fitting hF h hK hq hqF
    obtain ⟨Dq, hDqK⟩ := hK.prime q hq hπq
    have hDqn := Dq.normal_K
    have hsq : IsSL2 q (X ⧸ CFSG.fittingSubgroup X) := by
      rcases Dq.sl2 with hs' | ⟨-, hs'⟩
      · exact isSL2_quotient_congr (hDqK.trans hKF) hs'
      · exact absurd (isSL2_quotient_congr (hDqK.trans hKF) hs') h5
    exact eq_of_isSL2 hq hp hsq hs
  have hFp : IsPGroup p ↥(CFSG.fittingSubgroup X) :=
    IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
      (fun {d} hd hdvd => hall d hd hdvd))
  have hFR : CFSG.fittingSubgroup X ≤ CFSG.pCore p X := le_sSup ⟨inferInstance, hFp⟩
  have hRF : CFSG.pCore p X ≤ CFSG.fittingSubgroup X := CFSG.pCore_le_fitting X p
  have hRFeq : CFSG.pCore p X = CFSG.fittingSubgroup X := le_antisymm hRF hFR
  rcases D.iso with hE | hH
  · have hP : D.P = ⊤ := eq_top_of_isElemAbelian_sl2 hF h hK hp hp3 D hDK hE hFR hs
    have hFP' : CFSG.fittingSubgroup X = D.P.map (CFSG.pCore p X).subtype := by
      rw [hP, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hRFeq]
    obtain ⟨eP⟩ := hE
    let eF : ↥(CFSG.fittingSubgroup X) ≃* Multiplicative (Fin 2 → ZMod p) :=
      (MulEquiv.subgroupCongr hFP').trans
        (((D.P.equivMapOfInjective _ (CFSG.pCore p X).subtype_injective).symm).trans eP)
    refine ⟨p, hp, hp3, generalizedFitting_eq_fitting h, ⟨eF⟩,
      naturalSL2Action_of_kernel h hp hs eF ?_⟩
    intro x
    constructor
    · intro hx
      rw [← hKF, ← hDK, D.mem_K]
      intro d hd
      have hdF : ((d : ↥(CFSG.pCore p X)) : X) ∈ CFSG.fittingSubgroup X :=
        hRF (d : ↥(CFSG.pCore p X)).2
      have h2 := congrArg (fun z : ↥(CFSG.fittingSubgroup X) => (z : X))
        (hx ⟨((d : ↥(CFSG.pCore p X)) : X), hdF⟩)
      simp only [MulAut.conjNormal_apply] at h2
      have h3 : MulAut.conjNormal x d = d := Subtype.ext h2
      rw [h3, inv_mul_cancel]
      exact Subgroup.one_mem _
    · intro hx f
      have hc : (⟨x, hx⟩ : ↥(CFSG.fittingSubgroup X)) * f = f * ⟨x, hx⟩ :=
        eF.injective (by rw [map_mul, map_mul, mul_comm])
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, mul_inv_eq_iff_eq_mul]
      exact congrArg Subtype.val hc
  · exfalso
    have hP : D.P = ⊤ := eq_top_of_isPOnePlusTwo h hK hF.l2mult hp D hDK hH
    have hFP' : CFSG.fittingSubgroup X = D.P.map (CFSG.pCore p X).subtype := by
      rw [hP, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hRFeq]
    have hDchar : D.P.Characteristic := D.characteristic
    have hPn : (D.P.map (CFSG.pCore p X).subtype).Normal := inferInstance
    have hex : IsPOnePlusTwo p ↥(D.P.map (CFSG.pCore p X).subtype) :=
      isPOnePlusTwo_of_mulEquiv (D.P.equivMapOfInjective _ (CFSG.pCore p X).subtype_injective) hH
    have hsl : IsSL2 p (X ⧸ D.P.map (CFSG.pCore p X).subtype) := isSL2_quotient_congr hFP' hs
    have h3 := hF.a133 p hp hp3 X (D.P.map (CFSG.pCore p X).subtype) hex hsl
    have h4 := h.rank p hp hp2
    omega

end CFSG.Quasithin.A36B
