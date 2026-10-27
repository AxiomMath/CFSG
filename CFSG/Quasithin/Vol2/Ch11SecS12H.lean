module

public import CFSG.Quasithin.Background.C2Nine
public import CFSG.Quasithin.Background.G25Setup
public import CFSG.Quasithin.Background.OperatorJordanHolder
public import CFSG.Quasithin.Background.OperatorJordanHolderJH1
public import CFSG.Quasithin.Vol2.Ch11SecS12F

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.SL3Model CFSG.Quasithin.SL2Model
open CFSG.Quasithin.Vol2.Ch11
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.Quasithin.OperatorJH
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G]

section Scalar

variable {F : Type} [Field F]

theorem commute_of_smul_eq {B : SL(3, F)} {c : F} (hB : ∀ w : Fin 3 → F, B • w = c • w)
    (A : SL(3, F)) : B * A = A * B := by
  apply Subtype.ext
  ext i j
  have e1 := smul_single_one (B * A) j i
  have e2 := smul_single_one (A * B) j i
  rw [mul_smul, hB] at e1
  rw [mul_smul, hB, smul_comm A c] at e2
  exact e1.symm.trans e2

theorem ne_zero_of_smul_eq {B : SL(3, F)} {c : F} (hB : ∀ w : Fin 3 → F, B • w = c • w) :
    c ≠ 0 := by
  rintro rfl
  have h1 := congrArg (fun w => B⁻¹ • w) (hB (vE F 0))
  simp only [inv_smul_smul, zero_smul, smul_zero] at h1
  have := congrFun h1 0
  simp [vE] at this

theorem dualHom_smul_of_smul_eq {B : SL(3, F)} {c : F} (hB : ∀ w : Fin 3 → F, B • w = c • w)
    (φ : Fin 3 → F) : CFSG.Quasithin.dualHom F 3 B • φ = c⁻¹ • φ := by
  have hc := ne_zero_of_smul_eq hB
  funext i
  have h := dualHom_smul_dot B φ (vE F i)
  rw [hB, dotProduct_smul, smul_eq_mul] at h
  simp only [vE, dotProduct_single, mul_one] at h
  rw [Pi.smul_apply, smul_eq_mul, ← h, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end Scalar

section Kernel

variable {K C₁ C₂ : Subgroup G} {x : G} {m : ℕ} {F : Type} [Field F]
  {α₀ : ↥K →* ↥(StatedSL m F)} {a : F}

theorem comm_mem_of_isNatEig (h : IsNatEigSection K x α₀ C₁ C₂ a)
    (hKC : K ≤ Subgroup.normalizer (C₂ : Set G)) {k : G} (hk : k ∈ K) (hk1 : α₀ ⟨k, hk⟩ = 1)
    {c : G} (hc : c ∈ C₂) : k * c * k⁻¹ * c⁻¹ ∈ C₁ := by
  obtain ⟨β, -, hβk, hβK, -⟩ := h
  have hc' : k * c * k⁻¹ ∈ C₂ := (Subgroup.mem_normalizer_iff.mp (hKC hk) c).mp hc
  have e := hβK ⟨k, hk⟩ ⟨c, hc⟩ ⟨_, hc'⟩ rfl
  rw [hk1] at e
  simp only [OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec] at e
  have e' : β ⟨_, hc'⟩ = β ⟨c, hc⟩ := Multiplicative.toAdd.injective e
  have h1 : β (⟨_, hc'⟩ * ⟨c, hc⟩⁻¹) = 1 := by rw [map_mul, map_inv, e', mul_inv_cancel]
  exact (hβk _).mp h1

theorem commutator_le_of_isNatEig (h : IsNatEigSection K x α₀ C₁ C₂ a)
    (hKC : K ≤ Subgroup.normalizer (C₂ : Set G)) {P : Subgroup G} (hPK : P ≤ K)
    (hP1 : ∀ p (hp : p ∈ P), α₀ ⟨p, hPK hp⟩ = 1) : ⁅C₂, P⁆ ≤ C₁ := by
  rw [Subgroup.commutator_le]
  intro c hc p hp
  have h1 := comm_mem_of_isNatEig h hKC (hPK hp) (hP1 p hp) hc
  have e : ⁅c, p⁆ = (p * c * p⁻¹ * c⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact C₁.inv_mem h1

end Kernel

namespace L3Setting'

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (St : L3Setting n V V₁ L T H)

@[expose] noncomputable def betaT :
    ↥(conjClosure V H) →* Multiplicative (Fin 2 → GaloisField 2 n) :=
  (MonoidHom.ofInjective (qhom_injective (F := GaloisField 2 n))).symm.toMonoidHom.comp
    (St.betaU.codRestrict _ fun u => by
      rw [qhom_range]
      exact St.betaU_mem_Qv u)

theorem qhom_betaT (u : ↥(conjClosure V H)) : qhom (betaT St u) = St.betaU u := by
  set y : ↥(qhom (F := GaloisField 2 n)).range :=
    ⟨St.betaU u, by rw [qhom_range]; exact St.betaU_mem_Qv u⟩ with hy
  have h : ((MonoidHom.ofInjective (qhom_injective (F := GaloisField 2 n))
      ((MonoidHom.ofInjective (qhom_injective (F := GaloisField 2 n))).symm y) :
        SL(3, GaloisField 2 n))) =
      qhom ((MonoidHom.ofInjective (qhom_injective (F := GaloisField 2 n))).symm y) :=
    MonoidHom.ofInjective_apply _
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem natEig_top (hV₁V : V₁ ≤ V) {x : G} (hxL : x ∈ L) {c : GaloisField 2 n}
    (hxc : ∀ w : Fin 3 → GaloisField 2 n, St.D.θ ⟨x, hxL⟩ • w = c • w) :
    IsNatEigSection (LOf L V₁) x (NatData3'.alpha0 St.D hV₁V)
      (conjClosure V H ⊓ pCoreOf 2 (L ⊔ conjClosure V H)) (conjClosure V H) 1 := by
  refine ⟨betaT St, fun q => ?_, fun u => ?_, fun k u u' hu' => ?_, fun u u' hu' => ?_⟩
  · have hq : qhom q ∈ St.Ubar := by
      rw [St.Ubar_eq_Qv, ← qhom_range]
      exact ⟨q, rfl⟩
    obtain ⟨u, hu⟩ := hq
    exact ⟨u, qhom_injective (by rw [qhom_betaT, hu])⟩
  · have e : betaT St u = 1 ↔ St.betaU u = 1 := by
      rw [← qhom_betaT, ← map_one (qhom (F := GaloisField 2 n))]
      exact qhom_injective.eq_iff.symm
    rw [e, L3Setting.betaU_apply, St.Phi_eq_one_iff_mem_S]
    exact ⟨fun h => ⟨u.2, h⟩, fun h => h.2⟩
  · have hkL : (k : G) ∈ L := NatData3'.lOf_le k.2
    have hk' : (k : G) ∈ L ⊔ conjClosure V H := (le_sup_left : L ≤ L ⊔ conjClosure V H) hkL
    have e1 : (⟨u', (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) u'.2⟩ :
        ↥(L ⊔ conjClosure V H)) =
          ⟨k, hk'⟩ * ⟨u, (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) u.2⟩ *
            ⟨k, hk'⟩⁻¹ := Subtype.ext (by simp [hu'])
    have e2 : St.Phi ⟨k, hk'⟩ = St.D.θ ⟨k, hkL⟩ := St.Phi_of_L ⟨k, hkL⟩
    have hk : (Subgroup.inclusion NatData3'.lOf_le k : ↥L) = ⟨k, hkL⟩ := rfl
    have e3 : qhom (betaT St u') =
        qhom (SL2Model.natAct (levi _ (NatData3'.theta1 St.D hV₁V k)) (betaT St u)) := by
      rw [← conj_qhom, NatData3'.theta1_coe, hk, qhom_betaT, qhom_betaT, L3Setting.betaU_apply,
        L3Setting.betaU_apply, e1, map_mul, map_mul, map_inv, e2]
    rw [qhom_injective e3, SL2Model.natAct_apply, toAdd_ofAdd, NatData3'.alpha0_coe]
    rfl
  · have hxL' : x ∈ L ⊔ conjClosure V H := (le_sup_left : L ≤ L ⊔ conjClosure V H) hxL
    have e1 : (⟨u', (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) u'.2⟩ :
        ↥(L ⊔ conjClosure V H)) =
          ⟨x, hxL'⟩ * ⟨u, (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) u.2⟩ *
            ⟨x, hxL'⟩⁻¹ := Subtype.ext (by simp [hu'])
    have e2 : St.Phi ⟨x, hxL'⟩ = St.D.θ ⟨x, hxL⟩ := St.Phi_of_L ⟨x, hxL⟩
    have e3 : qhom (betaT St u') = qhom (betaT St u) := by
      rw [qhom_betaT, qhom_betaT, L3Setting.betaU_apply, L3Setting.betaU_apply, e1, map_mul,
        map_mul, map_inv, e2, commute_of_smul_eq hxc, mul_inv_cancel_right]
    rw [qhom_injective e3, one_smul]

theorem lOf_le_lOne : LOf L V₁ ≤ lOne L V₁ := by
  have h1 : oTwoUpper (LOf L V₁) = LOf L V₁ :=
    C2Nine.oTwoUpper_eq_of_perfect (perfectCore_perfect _)
  rw [← h1]
  exact oTwoUpper_mono (perfectCore_le _)

include St in
theorem lOf_le_normalizer_U :
    LOf L V₁ ≤ Subgroup.normalizer ((conjClosure V H : Subgroup G) : Set G) :=
  lOf_le_lOne.trans ((le_sup_left : lOne L V₁ ≤ lOne L V₁ ⊔ T).trans
    (St.hyp.base.lOne_sup_le.trans (le_normalizer_conjClosure V H)))

include St in
theorem commutator_le_top (hn : 2 ≤ n) (hV₁V : V₁ ≤ V) :
    ⁅conjClosure V H, pCoreOf 2 (LOf L V₁)⁆ ≤
      conjClosure V H ⊓ pCoreOf 2 (L ⊔ conjClosure V H) := by
  have hO : pCoreOf 2 (LOf L V₁) ≤ LOf L V₁ := Subgroup.map_subtype_le _
  have h1 : ∀ w : Fin 3 → GaloisField 2 n, St.D.θ ⟨1, L.one_mem⟩ • w = (1 : GaloisField 2 n) • w :=
    fun w => by
      rw [one_smul]
      have : (⟨1, L.one_mem⟩ : ↥L) = 1 := rfl
      rw [this, map_one, one_smul]
  refine commutator_le_of_isNatEig (natEig_top St hV₁V L.one_mem h1)
    (lOf_le_normalizer_U St) hO fun p hp => ?_
  have hK : IsPGroup 2 ↥(pCoreOf 2 (L ⊔ T)) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hker := NatData3'.alpha0_ker St.D hn hV₁V hK
  have hmem : (⟨p, hO hp⟩ : ↥(LOf L V₁)) ∈ (NatData3'.alpha0 St.D hV₁V).ker := by
    rw [hker]
    exact hp
  exact hmem

end L3Setting'

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
