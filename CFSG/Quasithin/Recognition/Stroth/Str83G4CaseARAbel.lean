module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseABaseXR
import CFSG.Quasithin.Recognition.Stroth.Str83G4S1
import CFSG.Quasithin.Recognition.Stroth.Str83G4Reduction

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin.F112R
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

private theorem caseA_str83R_elemAbelian
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) :
    IsElemAbelian 2 (str83R L1 L2 S) := by
  classical
  obtain ⟨d⟩ := str83G4Data_nonempty hfr
  have ha : 1 ≤ a := hfr.2.2.1
  have hZ : IsElemAbelian 2 (str83X L1 L2 S) :=
    str83G4S1_of_z2Comm str83G4Z2Comm_holds G L1 L2 S a hfr
  have hw : CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S :=
    (str83G4_str83R_le_q1_iff hfr d).mp hA
  have hW : Subgroup.map (MulAut.conj d.w).toMonoidHom
      (CFSG.conjugate (str83X L1 L2 S) d.w) = str83X L1 L2 S := by
    rw [show Subgroup.map (MulAut.conj d.w).toMonoidHom
        (CFSG.conjugate (str83X L1 L2 S) d.w) =
        CFSG.conjugate (CFSG.conjugate (str83X L1 L2 S) d.w) d.w⁻¹ by
      simp only [CFSG.conjugate, inv_inv]]
    rw [CFSG.conjugate_conjugate, mul_inv_cancel, CFSG.conjugate_one]
  have hXWd : ⁅str83X L1 L2 S, conjSub d.w (str83X L1 L2 S)⁆ = ⊥ := by
    have h1 : Subgroup.map (MulAut.conj d.w).toMonoidHom
        ⁅str83X L1 L2 S, CFSG.conjugate (str83X L1 L2 S) d.w⁆ = ⊥ := by
      rw [str83G4_commutator_x_conjugate_eq_bot hfr d hw, Subgroup.map_bot]
    rw [Subgroup.map_commutator, hW] at h1
    have h2 : ⁅conjSub d.w (str83X L1 L2 S), str83X L1 L2 S⁆ = ⊥ := by
      simpa only [conjSub] using h1
    rw [Subgroup.commutator_comm] at h2
    exact h2
  have hR' : Hyp111R L2 L1 S :=
    Hyp111R.symm (Hyp111R.of_hyp111 rankOneListedFacts hfr.1.1)
  have hlt : L2 ⊓ bigB L2 L1 S < L2 := by
    rw [CFSG.Quasithin.F1.inf_bigB_eq_borelOf hR']
    exact CFSG.Quasithin.F1.lt_borelOf hR'
  obtain ⟨g0, hg0L2, hg0B⟩ := SetLike.exists_of_lt hlt
  have hg0B' : g0 ∉ bigB L1 L2 S := fun h => hg0B ⟨hg0L2, by rwa [bigB_comm]⟩
  have hwP2 : d.w ∈ P2 L1 L2 S :=
    (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)) d.hwH2
  have hwNotB : d.w ∉ bigB L1 L2 S := fun h => d.hwNotN (hfr.2.1 h)
  have hwMem := mem_bigB_or_mem_doubleCoset_p2 (L1 := L1) (L2 := L2) (S := S)
    (n := 2 * a + 1) (by omega) hfr.1 hfr.2.2.2.2.1 hg0L2 hg0B' hwP2
  have hwBgB : d.w ∈ bigB L1 L2 S * ({g0} : Set G) * bigB L1 L2 S :=
    hwMem.resolve_left hwNotB
  rw [Set.mem_mul] at hwBgB
  obtain ⟨x0, hx0, b3, hb3, hw_eq⟩ := hwBgB
  rw [Set.mem_mul] at hx0
  obtain ⟨b1, hb1, g1, hg1, hx0_eq⟩ := hx0
  rw [Set.mem_singleton_iff] at hg1
  rw [hg1] at hx0_eq
  have hw_eq' : d.w = b1 * g0 * b3 := by rw [← hw_eq, ← hx0_eq]
  have hg0_eq : g0 = b1⁻¹ * d.w * b3⁻¹ := by rw [hw_eq']; group
  change IsElemAbelian 2 (conjClosure (str83X L1 L2 S) (P2 L1 L2 S))
  refine HypF91.isElemAbelian_conjClosure_of_forall hZ ?_
  intro k hk
  by_cases hkB : k ∈ bigB L1 L2 S
  ·
    have hkP1 : k ∈ P1 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hkB
    have hconj : conjSub k (str83X L1 L2 S) = str83X L1 L2 S := by
      have h := CFSG.conjugate_eq_self_of_mem_normalizer
        (le_normalizer_str83X L1 L2 S ((P1 L1 L2 S).inv_mem hkP1))
      simpa [conjSub, CFSG.conjugate] using h
    rw [hconj]
    exact Subgroup.le_centralizer_iff_isMulCommutative.mpr hZ.1
  ·
    have hkMem := mem_bigB_or_mem_doubleCoset_p2 (L1 := L1) (L2 := L2) (S := S)
      (n := 2 * a + 1) (by omega) hfr.1 hfr.2.2.2.2.1 hg0L2 hg0B' hk
    have hkBgB : k ∈ bigB L1 L2 S * ({g0} : Set G) * bigB L1 L2 S :=
      hkMem.resolve_left hkB
    rw [Set.mem_mul] at hkBgB
    obtain ⟨y0, hy0, c3, hc3, hk_eq⟩ := hkBgB
    rw [Set.mem_mul] at hy0
    obtain ⟨c1, hc1, g1', hg1', hy0_eq⟩ := hy0
    rw [Set.mem_singleton_iff] at hg1'
    rw [hg1'] at hy0_eq
    have hk_eq' : k = c1 * g0 * c3 := by rw [← hk_eq, ← hy0_eq]
    have hk_eq'' : k = (c1 * b1⁻¹) * d.w * (b3⁻¹ * c3) := by
      calc k = c1 * g0 * c3 := hk_eq'
        _ = (c1 * b1⁻¹) * d.w * (b3⁻¹ * c3) := by rw [hg0_eq]; group
    have hcLB : c1 * b1⁻¹ ∈ bigB L1 L2 S :=
      (bigB L1 L2 S).mul_mem hc1 ((bigB L1 L2 S).inv_mem hb1)
    have hcRB : b3⁻¹ * c3 ∈ bigB L1 L2 S :=
      (bigB L1 L2 S).mul_mem ((bigB L1 L2 S).inv_mem hb3) hc3
    have hcL_X : conjSub (c1 * b1⁻¹) (str83X L1 L2 S) = str83X L1 L2 S := by
      have h := CFSG.conjugate_eq_self_of_mem_normalizer
        (le_normalizer_str83X L1 L2 S
          ((P1 L1 L2 S).inv_mem
            ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hcLB)))
      simpa [conjSub, CFSG.conjugate] using h
    have hcR_X : conjSub (b3⁻¹ * c3) (str83X L1 L2 S) = str83X L1 L2 S := by
      have h := CFSG.conjugate_eq_self_of_mem_normalizer
        (le_normalizer_str83X L1 L2 S
          ((P1 L1 L2 S).inv_mem
            ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hcRB)))
      simpa [conjSub, CFSG.conjugate] using h
    have hconj_k : conjSub k (str83X L1 L2 S) =
        conjSub (c1 * b1⁻¹) (conjSub d.w (str83X L1 L2 S)) := by
      rw [hk_eq'', conjSub_mul, conjSub_mul, hcR_X]
    have hcomm : ⁅str83X L1 L2 S, conjSub k (str83X L1 L2 S)⁆ = ⊥ := by
      rw [hconj_k]
      calc ⁅str83X L1 L2 S,
              conjSub (c1 * b1⁻¹) (conjSub d.w (str83X L1 L2 S))⁆
          = ⁅conjSub (c1 * b1⁻¹) (str83X L1 L2 S),
              conjSub (c1 * b1⁻¹) (conjSub d.w (str83X L1 L2 S))⁆ := by rw [hcL_X]
        _ = conjSub (c1 * b1⁻¹)
              ⁅str83X L1 L2 S, conjSub d.w (str83X L1 L2 S)⁆ :=
              (Subgroup.map_commutator (str83X L1 L2 S)
                (conjSub d.w (str83X L1 L2 S))
                (MulAut.conj (c1 * b1⁻¹)).toMonoidHom).symm
        _ = conjSub (c1 * b1⁻¹) (⊥ : Subgroup G) := by rw [hXWd]
        _ = ⊥ := Subgroup.map_bot _
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm

private theorem caseA_R_le_centralizer_γ₁
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) :
    caseAR (f112Gamma1 L1 L2 S) ≤
      Subgroup.centralizer
        (caseAR (f112Gamma1 L1 L2 S) : Set (f112Amalgam L1 L2 S).Ghat) := by
  have hR_ab : IsElemAbelian 2 (str83R L1 L2 S) := caseA_str83R_elemAbelian hfr hA
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hxstab : x ∈ CosetGeom.stab (f112Gamma1 L1 L2 S) :=
    caseA_R_le_stab hfr CosetGeom.vtype_γ₁ hx
  have hystab : y ∈ CosetGeom.stab (f112Gamma1 L1 L2 S) :=
    caseA_R_le_stab hfr CosetGeom.vtype_γ₁ hy
  obtain ⟨hxmem, hxfix⟩ := CosetGeom.mem_stab.mp hxstab
  obtain ⟨hymem, hyfix⟩ := CosetGeom.mem_stab.mp hystab
  let hx' : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S) :=
    ⟨⟨x, hxmem⟩, hxfix⟩
  let hy' : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S) :=
    ⟨⟨y, hymem⟩, hyfix⟩
  have hxR : (f112StabEquiv1 L1 L2 S hx' : G) ∈ str83R L1 L2 S :=
    (caseA_mem_R_γ₁_iff hfr hx').mp hx
  have hyR : (f112StabEquiv1 L1 L2 S hy' : G) ∈ str83R L1 L2 S :=
    (caseA_mem_R_γ₁_iff hfr hy').mp hy
  have hcommG : (f112StabEquiv1 L1 L2 S hx' : G) * (f112StabEquiv1 L1 L2 S hy' : G) =
      (f112StabEquiv1 L1 L2 S hy' : G) * (f112StabEquiv1 L1 L2 S hx' : G) :=
    IsElemAbelian.comm hR_ab hxR hyR
  have heq : hx' * hy' = hy' * hx' := by
    apply (f112StabEquiv1 L1 L2 S).injective
    have h1 : f112StabEquiv1 L1 L2 S hx' * f112StabEquiv1 L1 L2 S hy' =
        f112StabEquiv1 L1 L2 S hy' * f112StabEquiv1 L1 L2 S hx' :=
      Subtype.ext hcommG
    simpa only [map_mul] using h1
  let c : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S) →*
      (f112Amalgam L1 L2 S).Ghat :=
    (Subgroup.subtype ((f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)).comp
      (Subgroup.subtype
        (MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S)))
  have hcx : x = c hx' := rfl
  have hcy : y = c hy' := rfl
  rw [hcx, hcy, ← map_mul c hx' hy', ← map_mul c hy' hx', heq]

private theorem caseA_R_le_centralizer
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S)
    {β : f112Gamma L1 L2 S} (hβ : CosetGeom.vtype β = true) :
    caseAR β ≤ Subgroup.centralizer (caseAR β : Set (f112Amalgam L1 L2 S).Ghat) := by
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₁ hβ
  have hR : caseAR β = conjSub (g : (f112Amalgam L1 L2 S).Ghat)
      (caseAR (f112Gamma1 L1 L2 S)) := by
    rw [hg, caseA_R_smul g (f112Gamma1 L1 L2 S)]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hx' : (g : (f112Amalgam L1 L2 S).Ghat)⁻¹ * x *
      (g : (f112Amalgam L1 L2 S).Ghat) ∈ caseAR (f112Gamma1 L1 L2 S) := by
    rw [hR] at hx
    exact mem_conjSub.mp hx
  have hy' : (g : (f112Amalgam L1 L2 S).Ghat)⁻¹ * y *
      (g : (f112Amalgam L1 L2 S).Ghat) ∈ caseAR (f112Gamma1 L1 L2 S) := by
    rw [hR] at hy
    exact mem_conjSub.mp hy
  have hcomm := Subgroup.mem_centralizer_iff.mp
    (caseA_R_le_centralizer_γ₁ hfr hA hx') _ hy'
  have hconj : (g : (f112Amalgam L1 L2 S).Ghat)⁻¹ * (y * x) *
      (g : (f112Amalgam L1 L2 S).Ghat) =
      (g : (f112Amalgam L1 L2 S).Ghat)⁻¹ * (x * y) *
        (g : (f112Amalgam L1 L2 S).Ghat) := by
    calc (g : (f112Amalgam L1 L2 S).Ghat)⁻¹ * (y * x) *
            (g : (f112Amalgam L1 L2 S).Ghat)
        = ((g : (f112Amalgam L1 L2 S).Ghat)⁻¹ * y *
              (g : (f112Amalgam L1 L2 S).Ghat)) *
            ((g : (f112Amalgam L1 L2 S).Ghat)⁻¹ * x *
              (g : (f112Amalgam L1 L2 S).Ghat)) := by group
      _ = ((g : (f112Amalgam L1 L2 S).Ghat)⁻¹ * x *
              (g : (f112Amalgam L1 L2 S).Ghat)) *
            ((g : (f112Amalgam L1 L2 S).Ghat)⁻¹ * y *
              (g : (f112Amalgam L1 L2 S).Ghat)) := hcomm
      _ = (g : (f112Amalgam L1 L2 S).Ghat)⁻¹ * (x * y) *
              (g : (f112Amalgam L1 L2 S).Ghat) := by group
  have h1 : (g : (f112Amalgam L1 L2 S).Ghat) *
      ((g : (f112Amalgam L1 L2 S).Ghat)⁻¹ * (y * x) *
        (g : (f112Amalgam L1 L2 S).Ghat)) *
      (g : (f112Amalgam L1 L2 S).Ghat)⁻¹ = y * x := by group
  have h2 : (g : (f112Amalgam L1 L2 S).Ghat) *
      ((g : (f112Amalgam L1 L2 S).Ghat)⁻¹ * (x * y) *
        (g : (f112Amalgam L1 L2 S).Ghat)) *
      (g : (f112Amalgam L1 L2 S).Ghat)⁻¹ = x * y := by group
  have hfinal := congrArg (fun z => (g : (f112Amalgam L1 L2 S).Ghat) * z *
    (g : (f112Amalgam L1 L2 S).Ghat)⁻¹) hconj
  rw [h1, h2] at hfinal
  exact hfinal

theorem caseA_commute_X
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S)
    {β α₁ α₃ : f112Gamma L1 L2 S} (hβ : CosetGeom.vtype β = true)
    (h₁ : α₁ ∈ CosetGeom.nbrs β) (h₃ : α₃ ∈ CosetGeom.nbrs β)
    {x y : (f112Amalgam L1 L2 S).Ghat} (hx : x ∈ caseAX α₁) (hy : y ∈ caseAX α₃) :
    Commute x y := by
  have hRβ : caseAR β ≤ Subgroup.centralizer
      (caseAR β : Set (f112Amalgam L1 L2 S).Ghat) :=
    caseA_R_le_centralizer hfr hA hβ
  have hxR : x ∈ caseAR β :=
    le_iSup₂ (f := fun w (_ : w ∈ CosetGeom.nbrs β) => caseAX w) α₁ h₁ hx
  have hyR : y ∈ caseAR β :=
    le_iSup₂ (f := fun w (_ : w ∈ CosetGeom.nbrs β) => caseAX w) α₃ h₃ hy
  have h := Subgroup.mem_centralizer_iff.mp (hRβ hxR) y hyR
  exact h.symm

end CFSG.Quasithin.Stroth

end
