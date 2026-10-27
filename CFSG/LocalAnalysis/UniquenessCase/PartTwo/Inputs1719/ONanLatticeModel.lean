module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONanLatticeReduction
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicNoncentralONan

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.ONSchreier CFSG.Sporadic.ONOddCore
open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81 (calNIn CFShape)

theorem onl_isL3_onX :
    IsL3 ↥onX 2 :=
  Or.inl ⟨by decide, onX_classicalModel⟩

theorem onl_XR_simple :
    IsSimpleGroup XR := by
  have : IsSimpleGroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
      CFSG.ComponentClassification.PSL3Four.F4) :=
    CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL le_rfl
  exact (XREquiv.trans thetaX.symm).isSimpleGroup

theorem onl_secL3_XR :
    onl_SecL3 ↥XR := by
  have := onl_XR_simple
  intro Λ _ hs hnc
  obtain ⟨e⟩ := uc22p20b_simpSec_simple hnc hs
  exact CFSG.LocalAnalysis.WeakClosure81.isoInvPred_lieModel .PSL 3 2 2 ↥onX Λ
    ⟨XREquiv.symm.trans e⟩ onl_isL3_onX

theorem onl_secL3_RM :
    onl_SecL3 ↥RM := by
  have : Group.IsSolvable (↥RM ⧸ XR) := by
    have h := XR.card_mul_index
    rw [Nat.card_congr XREquiv.toEquiv, card_onX, card_RM] at h
    have h2 : Nat.card (↥RM ⧸ XR) = 2 := by
      rw [← Subgroup.index_eq_card]; omega
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (IsPGroup.of_card (p := 2) (n := 1) (by rw [h2, pow_one])).isNilpotent
    infer_instance
  exact onl_secL3_of_normal XR onl_secL3_XR

theorem onl_secL3_onM :
    onl_SecL3 ↥onM := by
  have : (onQ.subgroupOf onM).Normal := ker_piR ▸ piR.normal_ker
  have : Group.IsSolvable ↥(onQ.subgroupOf onM) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (IsPGroup.of_card (p := 2) (n := 2)
      (by rw [card_onQ_subgroupOf_M]; norm_num)).isNilpotent
    infer_instance
  refine onl_secL3_of_normal' (onQ.subgroupOf onM) ?_
  let ι : (↥onM ⧸ onQ.subgroupOf onM) ≃* ↥RM :=
    (QuotientGroup.quotientMulEquivOfEq ker_piR.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective piR piR_surjective)
  exact onl_secL3_of_surjective ι.symm.toMonoidHom ι.symm.surjective onl_secL3_RM

theorem onl_secL3_C :
    onl_SecL3 ↥(onM.subgroupOf Pv) :=
  onl_secL3_of_surjective (Subgroup.subgroupOfEquivOfLe onM_le).symm.toMonoidHom
    (Subgroup.subgroupOfEquivOfLe onM_le).symm.surjective onl_secL3_onM

theorem onl_fix_z
    (α : MulAut Pv)
    (hα : (onT.subgroupOf Pv).map α.toMonoidHom = onT.subgroupOf Pv) : α zP = zP := by
  have hU : ∀ x : Pv, ((α x : Pv) : Equiv.Perm (Fin N)) ∈ onT ↔ (x : Equiv.Perm (Fin N)) ∈ onT :=
    fun x => by
      rw [← Subgroup.mem_subgroupOf, ← Subgroup.mem_subgroupOf]
      conv_lhs => rw [← hα]
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hzc : ∀ t ∈ onT, t * onz = onz * t := fun t ht => by
    have hz : onz ∈ CFSG.centerIn onT := by
      rw [onT_centerIn]
      exact Subgroup.mem_zpowers _
    exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 t ht
  have hmem : ((α zP : Pv) : Equiv.Perm (Fin N)) ∈ CFSG.centerIn onT := by
    refine Subgroup.mem_inf.2 ⟨(hU zP).2 onz_mem_T, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro t ht
    obtain ⟨x, hx⟩ := α.surjective ⟨t, onT_le ht⟩
    have hxT : (x : Equiv.Perm (Fin N)) ∈ onT := by
      rw [← hU x, hx]
      exact ht
    have hc : x * zP = zP * x := Subtype.ext (hzc _ hxT)
    have := congrArg (fun y : Pv => (y : Equiv.Perm (Fin N))) (congrArg α hc)
    simp only [map_mul, hx, Subgroup.coe_mul] at this
    exact this
  rw [onT_centerIn, mem_zpowers_iff_mem_range_orderOf, orderOf_onz] at hmem
  simp only [Finset.mem_image, Finset.mem_range] at hmem
  obtain ⟨k, hk, hkz⟩ := hmem
  interval_cases k
  · exfalso
    have h1 : α zP = 1 := Subtype.ext (by rw [← hkz, pow_zero]; rfl)
    rw [map_eq_one_iff _ α.injective] at h1
    exact onz_ne_one (congrArg Subtype.val h1)
  · exact Subtype.ext (by rw [← hkz, pow_one]; rfl)

theorem onl_C_inv
    (α : MulAut Pv)
    (hα : (onT.subgroupOf Pv).map α.toMonoidHom = onT.subgroupOf Pv) :
    (onM.subgroupOf Pv).map α.toMonoidHom = onM.subgroupOf Pv := by
  have hz := onl_fix_z α hα
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  conv_rhs => rw [← MulEquiv.apply_symm_apply α y]
  rw [mem_M_map hz]

theorem onl_B_le_C :
    sncon_P ≤ onM.subgroupOf Pv := by
  intro x hx
  rw [sncon_P, Subgroup.mem_subgroupOf] at hx
  rw [Subgroup.mem_subgroupOf]
  obtain ⟨m, -, hm⟩ := hx
  rw [← hm]
  exact m.2

theorem onl_card_C :
    Nat.card ↥(onM.subgroupOf Pv) = 161280 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe onM_le).toEquiv, card_onM]

theorem onl_U_lt_B :
    onT.subgroupOf Pv < sncon_P := by
  refine lt_of_le_of_ne sncon_U_le_P fun h => ?_
  have h1 := sncon_card_P
  rw [← h, card_onT_subgroupOf] at h1
  omega

theorem onl_B_lt_C :
    sncon_P < onM.subgroupOf Pv := by
  refine lt_of_le_of_ne onl_B_le_C fun h => ?_
  have h1 := sncon_card_P
  rw [h, onl_card_C, card_onT_subgroupOf] at h1
  omega

@[expose] def onl_LatFact :
    Prop :=
  ∀ X : Subgroup Pv, onT.subgroupOf Pv ≤ X → X ≤ onM.subgroupOf Pv →
    X = onT.subgroupOf Pv ∨ X = sncon_P ∨ X = onM.subgroupOf Pv

@[expose] def onl_ParFact :
    Prop :=
  ∃ P : Subgroup Pv, onT.subgroupOf Pv ≤ P ∧ Nat.card P = 3 * Nat.card (onT.subgroupOf Pv) ∧
    P ⊔ onM.subgroupOf Pv = ⊤ ∧
    ∀ α : MulAut Pv, (onT.subgroupOf Pv).map α.toMonoidHom = onT.subgroupOf Pv →
      P.map α.toMonoidHom = P

theorem onl_concl_Pv
    (hL : onl_LatFact)
    (hP : onl_ParFact) {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y} [K.Normal]
    (hidx : ∃ a : ℕ, K.index = 2 ^ a) (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤)
    (e : ↥K ≃* ↥Pv) : onl_Concl Y S := by
  obtain ⟨P, hUP, hcP, hgen, hinvP⟩ := hP
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf (onT.subgroupOf Pv) ⊤ :=
    ⟨le_top, onT_isPGroup, by
      rw [show ((onT.subgroupOf Pv).subgroupOf ⊤).index = (onT.subgroupOf Pv).index from
        Subgroup.relIndex_top_right _]
      exact onT_not_dvd_index⟩
  have h3C : 3 ∣ Nat.card ↥(onM.subgroupOf Pv) := by rw [onl_card_C]; norm_num
  exact onl_concl_of_model hU onl_U_lt_B onl_B_lt_C hUP hL h3C hcP hgen onl_secL3_C onl_C_inv
    sncon_P_inv hinvP hidx hS e

open CFSG.Quasithin.RonanE43 in
theorem onl_kONanLattice_of_facts
    (hL : onl_LatFact)
    (hP : onl_ParFact) : K_ONanLattice := by
  intro Y _ _ K S hKY hON
  have hK : K.Normal := hKY.1
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := hKY.2.2.2.2.2
  obtain ⟨e₀⟩ := hON
  have e : (↥K ⧸ Subgroup.center ↥K) ≃* CFSG.Blueprint.NativeSporadic.ON := e₀
  have hq : CFSG.IsQuasisimple ↥K := ⟨⟨hKY.2.1.1⟩, hKY.2.1.2,
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hKY.2.1⟩
  have hdvd := CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.on_center_dvd ↥K hq e
  suffices h : onl_Concl Y S by
    obtain ⟨H₁, H₂, M₁, M₂, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    exact ⟨H₁, H₂, M₁, M₂, h1, h2, h3, h4, h5, h6, h7, h8, onl_cfShape_of_secL3 h9⟩
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
  · have hZ : Subgroup.center ↥K = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    exact onl_concl_Pv hL hP hKY.2.2.2.2.1 hS (((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).symm.trans (e.trans onEquivPv))
  · classical
    set Z : Subgroup Y := (Subgroup.center ↥K).map K.subtype with hZdef
    have hZn : Z.Normal := by
      have : (Subgroup.center ↥K).Characteristic := Subgroup.centerCharacteristic
      exact ConjAct.normal_of_characteristic_of_normal (H := K) (K := Subgroup.center ↥K)
    have hZK : Z ≤ K := by
      rintro _ ⟨c, -, rfl⟩
      exact c.2
    have hZc : ∀ z ∈ Z, ∀ k ∈ K, z * k = k * z := by
      rintro _ ⟨c, hc, rfl⟩ k hk
      have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨k, hk⟩)
      simpa using h1.symm
    have hZcard : Nat.card Z = 3 := (Subgroup.card_subtype K (Subgroup.center ↥K)).trans h3
    have hperf : K ≤ ⁅K, K⁆ := by
      have h := congrArg (Subgroup.map K.subtype) hKY.2.1.1
      rw [commutator, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at h
      exact h.ge
    have hπ : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
    have hS' : CFSG.QuasithinUnique.IsSylowTwoOf (S.map (QuotientGroup.mk' Z)) ⊤ :=
      ⟨le_top, hS.2.1.map _, by
        rw [show ((S.map (QuotientGroup.mk' Z)).subgroupOf ⊤).index =
          (S.map (QuotientGroup.mk' Z)).index from Subgroup.relIndex_top_right _]
        exact isSylowIn_map _ hπ hS⟩
    have : (K.map (QuotientGroup.mk' Z)).Normal := hK.map _ hπ
    let ψ : ↥K →* Y ⧸ Z := (QuotientGroup.mk' Z).comp K.subtype
    have hψker : ψ.ker = Subgroup.center ↥K := by
      ext x
      rw [MonoidHom.mem_ker]
      show QuotientGroup.mk' Z (x : Y) = 1 ↔ _
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have : y = x := Subtype.ext hyx
        rw [← this]
        exact hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    have hψrange : ψ.range = K.map (QuotientGroup.mk' Z) := by
      show ((QuotientGroup.mk' Z).comp K.subtype).range = _
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    let eQ : (↥K ⧸ Subgroup.center ↥K) ≃* ↥ψ.range :=
      (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
        (QuotientGroup.quotientKerEquivRange ψ)
    let e₁ : ↥(K.map (QuotientGroup.mk' Z)) ≃* ↥Pv :=
      (MulEquiv.subgroupCongr hψrange.symm).trans (eQ.symm.trans (e.trans onEquivPv))
    have hidx : ∃ a : ℕ, (K.map (QuotientGroup.mk' Z)).index = 2 ^ a := by
      obtain ⟨a, ha⟩ := hKY.2.2.2.2.1
      refine ⟨a, ?_⟩
      rw [Subgroup.index_map_eq _ hπ (by rw [QuotientGroup.ker_mk']; exact hZK), ha]
    exact onl_concl_of_quot hZK hZc hperf hZcard (onl_concl_Pv hL hP hidx hS' e₁)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
