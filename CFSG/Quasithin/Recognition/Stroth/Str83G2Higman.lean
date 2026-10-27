module

public import CFSG.Quasithin.Recognition.Stroth.Str86LinearVertex
public import CFSG.GroupTheory.HigmanCommutator
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFourModules

public section

open scoped MatrixGroups commutatorElement
open Matrix
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.Setup.SL2Modules

namespace CFSG.Quasithin.Stroth

variable {G : Type} [Group G] [Finite G]
variable {H U R N : Subgroup G} {m : ℕ}

theorem commutator_le_of_two_natural_chiefSteps
    (hUH : U ≤ H) (hHU : H ≤ Subgroup.normalizer (U : Set G)) (hU2 : IsPGroup 2 U)
    (hstepR : IsChiefStep H U R N) (hstepU : IsChiefStep H U N U)
    (hm : 2 ≤ m)
    (e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 m))
    (hE_R : IsElemAbelian 2 (Ch3z.chiefMod R N))
    (hE_U : IsElemAbelian 2 (Ch3z.chiefMod N U))
    (hnat_R : letI : CommGroup (Ch3z.chiefMod R N) := l2ChiefSectionCommGroup hE_R
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod R N)) := l2ChiefSectionModule hE_R
      CFSG.QuasithinUnique.Setup.SL2Modules.IsNaturalModule
        (l2ChiefSectionRep hstepR hUH hE_R e))
    (hnat_U : letI : CommGroup (Ch3z.chiefMod N U) := l2ChiefSectionCommGroup hE_U
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod N U)) := l2ChiefSectionModule hE_U
      CFSG.QuasithinUnique.Setup.SL2Modules.IsNaturalModule
        (l2ChiefSectionRep hstepU hUH hE_U e)) : ⁅U, U⁆ ≤ R := by
  classical
  have hHR : H ≤ Subgroup.normalizer (R : Set G) := D14.le_normalizer_of_isNormalIn hstepR.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstepR.1
  have hNUle : N ≤ U := hstepR.1.1
  have hRUle : R ≤ N := hstepR.2.2.1.le
  let RU : Subgroup ↥U := R.subgroupOf U
  let NU : Subgroup ↥U := N.subgroupOf U
  have hRUN : RU ≤ NU := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hRUle (Subgroup.mem_subgroupOf.mp hx))
  haveI hRU_normal : RU.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hUH.trans hHR)
  haveI hNU_normal : NU.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hUH.trans hHN)
  let Q : Type := ↥U ⧸ RU
  let M : Subgroup Q := NU.map (QuotientGroup.mk' RU)
  haveI hM_normal : M.Normal := QuotientGroup.map_normal RU NU
  let eQ : Q ⧸ M ≃* ↥U ⧸ NU :=
    QuotientGroup.quotientQuotientEquivQuotient RU NU hRUN
  have hUN : U ≤ Subgroup.normalizer (N : Set G) := hUH.trans hHN
  have hkerU : (Ch3z.chiefIota hUN).ker = NU := by
    ext u
    rw [MonoidHom.mem_ker, Ch3z.chiefIota_eq_one_iff, Subgroup.mem_subgroupOf]
  let eU : (↥U ⧸ NU) ≃* Ch3z.chiefMod N U :=
    (QuotientGroup.quotientMulEquivOfEq hkerU.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (Ch3z.chiefIota hUN)
        (Ch3z.chiefIota_surjective hUN))
  have hNR : N ≤ Subgroup.normalizer (R : Set G) := (hNUle.trans hUH).trans hHR
  haveI hRsubN_normal : (R.subgroupOf N).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hNR
  have hkerN : (Ch3z.chiefIota hNR).ker = R.subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker, Ch3z.chiefIota_eq_one_iff, Subgroup.mem_subgroupOf]
  let eN : (↥N ⧸ R.subgroupOf N) ≃* Ch3z.chiefMod R N :=
    (QuotientGroup.quotientMulEquivOfEq hkerN.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (Ch3z.chiefIota hNR)
        (Ch3z.chiefIota_surjective hNR))
  let psi : ↥N →* ↥M :=
    { toFun := fun n => ⟨QuotientGroup.mk' RU ⟨(n : G), hNUle n.2⟩,
        Subgroup.mem_map_of_mem (QuotientGroup.mk' RU)
          (Subgroup.mem_subgroupOf.mpr n.2)⟩
      map_one' := by
        apply Subtype.ext
        change (QuotientGroup.mk' RU) (1 : ↥U) = 1
        rw [map_one]
      map_mul' := by
        intro a b
        apply Subtype.ext
        change QuotientGroup.mk' RU (⟨(a : G) * (b : G), _⟩ : ↥U) =
          QuotientGroup.mk' RU (⟨(a : G), _⟩ : ↥U) *
            QuotientGroup.mk' RU (⟨(b : G), _⟩ : ↥U)
        rw [← map_mul]
        rfl }
  have hpsi_surj : Function.Surjective psi := by
    intro m
    obtain ⟨x, hx, hxm⟩ := Subgroup.mem_map.mp m.2
    have hxN : (x : G) ∈ N := by
      change x ∈ N.subgroupOf U at hx
      exact Subgroup.mem_subgroupOf.mp hx
    refine ⟨⟨(x : G), hxN⟩, Subtype.ext ?_⟩
    show QuotientGroup.mk' RU ⟨(x : G), hNUle hxN⟩ = (m : Q)
    have hxeq : (⟨(x : G), hNUle hxN⟩ : ↥U) = x := Subtype.ext rfl
    rw [hxeq]
    exact hxm
  have hkerpsi : psi.ker = R.subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : QuotientGroup.mk' RU ⟨(n : G), hNUle n.2⟩ = 1 := congrArg Subtype.val h
      have h2 : (⟨(n : G), hNUle n.2⟩ : ↥U) ∈ RU :=
        (QuotientGroup.eq_one_iff (N := RU) (x := ⟨(n : G), hNUle n.2⟩)).mp h1
      exact Subgroup.mem_subgroupOf.mp h2
    · intro hn
      apply Subtype.ext
      change QuotientGroup.mk' RU ⟨(n : G), hNUle n.2⟩ = 1
      exact (QuotientGroup.eq_one_iff (N := RU) (x := ⟨(n : G), hNUle n.2⟩)).mpr
        (Subgroup.mem_subgroupOf.mpr hn)
  let eM : ↥M ≃* Ch3z.chiefMod R N :=
    ((QuotientGroup.quotientMulEquivOfEq hkerpsi.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective psi hpsi_surj)).symm.trans eN
  letI : CommGroup (Ch3z.chiefMod R N) := l2ChiefSectionCommGroup hE_R
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod R N)) := l2ChiefSectionModule hE_R
  obtain ⟨eB, hB⟩ := hnat_R
  letI : CommGroup (Ch3z.chiefMod N U) := l2ChiefSectionCommGroup hE_U
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod N U)) := l2ChiefSectionModule hE_U
  obtain ⟨eA, hA⟩ := hnat_U
  let phiA : Additive (Q ⧸ M) ≃+ (Fin 2 → GaloisField 2 m) :=
    ((eQ.trans eU).toAdditive).trans eA
  let phiB : Additive ↥M ≃+ (Fin 2 → GaloisField 2 m) :=
    (eM.toAdditive).trans eB
  let actU : MulDistribMulAction ↥H ↥U :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer H U hHU
  letI : MulDistribMulAction ↥H ↥U := actU
  have hRinv : CFSG.IsInvariant ↥H ↥U RU := by
    refine CFSG.SolvableHall.isInvariant_of_forall_smul_mem ?_
    intro h r hr
    rw [Subgroup.mem_subgroupOf] at hr ⊢
    change (h : G) * (r : G) * (h : G)⁻¹ ∈ R
    exact (Subgroup.mem_normalizer_iff.mp (hHR h.2) (r : G)).mp hr
  letI : MulDistribMulAction ↥H Q :=
    CFSG.quotientMulDistribMulAction (A := ↥H) (G := ↥U) RU hRinv
  letI : MulAction.QuotientAction ↥H RU :=
    CFSG.quotientAction_of_isInvariant (A := ↥H) RU hRinv
  let act : ↥H →* MulAut Q := MulDistribMulAction.toMulAut ↥H Q
  have hactM : ∀ γ, ∀ n ∈ M, act γ n ∈ M := by
    intro γ n hn
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hn
    have h1 : act γ (QuotientGroup.mk' RU x) = QuotientGroup.mk' RU (γ • x) := by
      rw [show act γ (QuotientGroup.mk' RU x) = γ • (QuotientGroup.mk' RU x) from by
        rw [MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply]]
      exact MulAction.Quotient.smul_mk (H := RU) γ x
    rw [h1]
    refine Subgroup.mem_map_of_mem (QuotientGroup.mk' RU) ?_
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    change (γ : G) * (x : G) * (γ : G)⁻¹ ∈ N
    exact (Subgroup.mem_normalizer_iff.mp (hHN γ.2) (x : G)).mp hx
  have hcommNU : ⁅N, U⁆ ≤ R :=
    CFSG.Quasithin.F112W.commutator_le_of_isChiefStep hU2 hUH hHU hstepR hstepR.1.1
  have hQN : M ≤ Subgroup.center Q := by
    intro m hm
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hm
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective RU q
    have hnN : (n : G) ∈ N := Subgroup.mem_subgroupOf.mp hn
    have hcommR : ⁅n, u⁆ ∈ RU :=
      Subgroup.mem_subgroupOf.mpr
        (hcommNU (Subgroup.commutator_mem_commutator hnN u.2))
    have h1 : ⁅(QuotientGroup.mk' RU n : Q), (QuotientGroup.mk' RU u : Q)⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff (N := RU) _).mpr hcommR
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  let π : ↥H →* SL(2, GaloisField 2 m) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 ↥H))
  have hπ : Function.Surjective π :=
    e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 ↥H))
  have heQ_mk : ∀ u : ↥U,
      eQ (QuotientGroup.mk (QuotientGroup.mk' RU u) : Q ⧸ M) =
        (QuotientGroup.mk u : ↥U ⧸ NU) := fun u =>
    QuotientGroup.quotientQuotientEquivQuotient_apply_mk RU NU hRUN u
  have heU_mk : ∀ u : ↥U,
      eU (QuotientGroup.mk u : ↥U ⧸ NU) = Ch3z.chiefIota hUN u := by
    intro u
    rfl
  have hphiA_mk : ∀ u : ↥U,
      phiA (Additive.ofMul (QuotientGroup.mk (QuotientGroup.mk' RU u) : Q ⧸ M)) =
        eA (Additive.ofMul (Ch3z.chiefIota hUN u)) := by
    intro u
    change eA (Additive.ofMul (eU (eQ (QuotientGroup.mk (QuotientGroup.mk' RU u))))) = _
    rw [heQ_mk, heU_mk]
  have hact_mk : ∀ (γ : ↥H) (u : ↥U),
      act γ (QuotientGroup.mk' RU u) = QuotientGroup.mk' RU (γ • u) := by
    intro γ u
    rw [show act γ (QuotientGroup.mk' RU u) = γ • (QuotientGroup.mk' RU u) from by
      rw [MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply]]
    exact MulAction.Quotient.smul_mk (H := RU) γ u
  have hφA : ∀ γ x, phiA (Additive.ofMul (QuotientGroup.mk (act γ x) : Q ⧸ M)) =
      ((π γ : SL(2, GaloisField 2 m)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 m)) *ᵥ
        phiA (Additive.ofMul (QuotientGroup.mk x)) := by
    intro γ x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective RU x
    rw [hact_mk γ u, hphiA_mk (γ • u), hphiA_mk u]
    have hgn : (γ : G) * (u : G) * (γ : G)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hHU γ.2) (u : G)).mp u.2
    have hρ : (l2ChiefSectionRep hstepU hUH hE_U e) (e (QuotientGroup.mk γ))
        (Additive.ofMul (Ch3z.chiefIota hUN u)) =
        Additive.ofMul (Ch3z.chiefIota hUN (γ • u)) := by
      rw [l2ChiefSectionRep_apply_mk, l2ChiefSectionAction_eq_chiefPsi]
      rw [Ch3z.chiefPsi_iota hHN hHU hUN γ u hgn]
      congr 1
    rw [← hρ]
    exact hA _ _
  letI : MulDistribMulAction ↥H ↥N :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer H N hHN
  have heψ_mk : ∀ n : ↥N,
      ((QuotientGroup.quotientMulEquivOfEq hkerpsi.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective psi hpsi_surj))
        (QuotientGroup.mk n : ↥N ⧸ R.subgroupOf N) = psi n := by
    intro n
    rfl
  have heM_psi : ∀ n : ↥N, eM (psi n) = Ch3z.chiefIota hNR n := by
    intro n
    change eN (((QuotientGroup.quotientMulEquivOfEq hkerpsi.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective psi hpsi_surj)).symm (psi n)) = _
    rw [← heψ_mk n, MulEquiv.symm_apply_apply]
    rfl
  have hphiB_psi : ∀ n : ↥N,
      phiB (Additive.ofMul (psi n)) =
        eB (Additive.ofMul (Ch3z.chiefIota hNR n)) := by
    intro n
    change eB (Additive.ofMul (eM (psi n))) = _
    rw [heM_psi]
  have hact_psi : ∀ (γ : ↥H) (n : ↥N), act γ (psi n) = psi (γ • n) := by
    intro γ n
    change act γ (QuotientGroup.mk' RU ⟨(n : G), hNUle n.2⟩) =
      QuotientGroup.mk' RU ⟨((γ • n : ↥N) : G), hNUle (γ • n).2⟩
    rw [hact_mk]
    congr 1
  have hφB : ∀ γ (n : M),
      phiB (Additive.ofMul ⟨act γ n, hactM γ n n.2⟩) =
        ((π γ : SL(2, GaloisField 2 m)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 m)) *ᵥ
          phiB (Additive.ofMul n) := by
    intro γ n
    obtain ⟨n₀, rfl⟩ := hpsi_surj n
    have hsub : (⟨act γ (psi n₀), hactM γ (psi n₀) (psi n₀).2⟩ : M) = psi (γ • n₀) :=
      Subtype.ext (hact_psi γ n₀)
    rw [hsub, hphiB_psi (γ • n₀), hphiB_psi n₀]
    have hgn : (γ : G) * (n₀ : G) * (γ : G)⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hHN γ.2) (n₀ : G)).mp n₀.2
    have hρ : (l2ChiefSectionRep hstepR hUH hE_R e) (e (QuotientGroup.mk γ))
        (Additive.ofMul (Ch3z.chiefIota hNR n₀)) =
        Additive.ofMul (Ch3z.chiefIota hNR (γ • n₀)) := by
      rw [l2ChiefSectionRep_apply_mk, l2ChiefSectionAction_eq_chiefPsi]
      rw [Ch3z.chiefPsi_iota hHR hHN hNR γ n₀ hgn]
      congr 1
    rw [← hρ]
    exact hB _ _
  have hK : 2 < Nat.card (GaloisField 2 m) := by
    rw [GaloisField.card 2 m (by omega)]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hQcomm := CFSG.commute_of_natural_central_extension hQN hK act hactM π hπ
    phiA hφA phiB hφB
  rw [Subgroup.commutator_le]
  intro u hu v hv
  have hq := hQcomm (QuotientGroup.mk' RU ⟨u, hu⟩) (QuotientGroup.mk' RU ⟨v, hv⟩)
  have h1 : ⁅(QuotientGroup.mk' RU (⟨u, hu⟩ : ↥U) : Q),
      (QuotientGroup.mk' RU (⟨v, hv⟩ : ↥U) : Q)⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr hq
  have hmem : ⁅(⟨u, hu⟩ : ↥U), (⟨v, hv⟩ : ↥U)⁆ ∈ RU := by
    rw [← map_commutatorElement] at h1
    exact (QuotientGroup.eq_one_iff (N := RU) _).mp h1
  have hcoe : ((⁅(⟨u, hu⟩ : ↥U), (⟨v, hv⟩ : ↥U)⁆ : ↥U) : G) = ⁅u, v⁆ := rfl
  have := Subgroup.mem_subgroupOf.mp hmem
  rw [hcoe] at this
  exact this

end CFSG.Quasithin.Stroth

end
