module

public import CFSG.Milestones.ASVolI.J1
public import CFSG.Quasithin.Recognition.RuTypeSetting
public import CFSG.Quasithin.Recognition.RuTypeSigma

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK.RuType

@[expose] noncomputable def sylowT {G : Type} [Group G] [Finite G] {L V T : Subgroup G}
    (h : RuType G L V T) : Sylow 2 G :=
  IsPGroup.toSylow (P := T) h.T_sylow.2.1 (by
    have hidx := h.T_sylow.2.2
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at hidx)

theorem coe_sylowT {G : Type} [Group G] [Finite G] {L V T : Subgroup G} (h : RuType G L V T) :
    (h.sylowT : Subgroup G) = T := rfl

namespace BridgeTwo

open CFSG.Open
open scoped MatrixGroups

local notation "F4c" => CFSG.Quasithin.RuType.F4
local notation "SigmaL2" => CFSG.Quasithin.RuType.SigmaL2F4

section Vocabulary

variable {G : Type} [Group G]

theorem centerOf_eq (W : Subgroup G) :
    CFSG.ASVolI.ChIJK.centerOf W = CFSG.Quasithin.centerOf W := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have := Subgroup.mem_center_iff.mp hy ⟨w, hw⟩
    simpa using congrArg Subtype.val this
  · rintro ⟨hxW, hxc⟩
    refine ⟨⟨x, hxW⟩, Subgroup.mem_center_iff.mpr fun w => ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc w w.2)

theorem mem_centerOf_iff {X : Subgroup G} {g : G} :
    g ∈ CFSG.ASVolI.ChIJK.centerOf X ↔ g ∈ X ∧ ∀ x ∈ X, x * g = g * x := by
  rw [centerOf_eq]
  simp only [CFSG.Quasithin.centerOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    SetLike.mem_coe]

theorem conjClosure_eq (L Y : Subgroup G) :
    CFSG.ASVolI.ChIJK.conjClosure L Y = CFSG.Quasithin.conjClosure L Y := by
  apply le_antisymm
  · refine iSup₂_le fun y hy => ?_
    rintro _ ⟨l, hl, rfl⟩
    exact CFSG.Quasithin.mem_conjClosure (Y.inv_mem hy) hl
  · rw [CFSG.Quasithin.conjClosure, Subgroup.closure_le]
    rintro _ ⟨h, hh, z, hz, rfl⟩
    exact (le_iSup₂ (f := fun y (_ : y ∈ Y) => CFSG.conjugate L y) h⁻¹ (Y.inv_mem hh))
      ⟨z, hz, by simp⟩

theorem subgroupOf_pCoreOf (H : Subgroup G) : (pCoreOf 2 H).subgroupOf H = CFSG.pCore 2 ↥H :=
  Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

end Vocabulary

section Basic

variable {G : Type} [Group G] [Finite G] {L V T : Subgroup G}

theorem V_le_S (h : RuType G L V T) : V ≤ SRu L := by
  rw [h.V_eq]
  exact Subgroup.map_subtype_le _

theorem mem_V_iff (h : RuType G L V T) {v : G} :
    v ∈ V ↔ v ∈ SRu L ∧ ∀ s ∈ SRu L, s * v = v * s := by
  rw [h.V_eq]
  exact mem_centerOf_iff

theorem S_le_T (h : RuType G L V T) : SRu L ≤ T := by
  have hTL : IsSylowTwoIn (T ⊓ L) L := by
    have h2 := h.T_choice
    rwa [← h.L_eq] at h2
  obtain ⟨hle, hp, hidx⟩ := hTL
  have hP : IsPGroup 2 ↥((T ⊓ L).subgroupOf L) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  let P : Sylow 2 ↥L := IsPGroup.toSylow hP hidx
  haveI : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  have hcore : CFSG.pCore 2 ↥L ≤ (P : Subgroup ↥L) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥L) 2).le_sylow_of_normal P
  have hmap := Subgroup.map_mono (f := L.subtype) hcore
  have e : (P : Subgroup ↥L).map L.subtype = T ⊓ L := Subgroup.map_subgroupOf_eq_of_le hle
  rw [e] at hmap
  exact hmap.trans inf_le_left

theorem Z_le_V (h : RuType G L V T)
    (hCV : ∀ l ∈ L, (∀ v ∈ V, l * v = v * l) → l ∈ SRu L) : ZRu T ≤ V := by
  intro z hz
  obtain ⟨-, hzc⟩ := mem_centerOf_iff.mp hz
  have hVT : V ≤ T := (V_le_S h).trans (S_le_T h)
  have hzL : z ∈ L := by
    rw [h.L_eq]
    exact Subgroup.centralizer_le_normalizer (V : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun v hv => hzc v (hVT hv))
  have hzS : z ∈ SRu L := hCV z hzL fun v hv => (hzc v (hVT hv)).symm
  exact (mem_V_iff h).mpr ⟨hzS, fun s hs => hzc s (S_le_T h hs)⟩

theorem V_le_H (h : RuType G L V T)
    (hCV : ∀ l ∈ L, (∀ v ∈ V, l * v = v * l) → l ∈ SRu L) : V ≤ HRu T := by
  intro v hv
  refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
  exact ((mem_V_iff h).mp hv).2 z (V_le_S h (Z_le_V h hCV hz))

theorem V_le_URu (h : RuType G L V T) : V ≤ URu V T := by
  rw [URu, conjClosure_eq]
  exact CFSG.Quasithin.le_conjClosure V (HRu T)

end Basic

section Field

open CFSG.Quasithin.RuType (frobF4 frobF4_apply frobF4_frobF4 frobVec)
open CFSG.Quasithin.RuType.Sigma (zmod2_cases)

noncomputable def e4 : F4 ≃+* F4c :=
  haveI : Fintype F4 := Fintype.ofFinite F4
  FiniteField.ringEquivOfCardEq (by
    have h1 : Fintype.card F4 = 4 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
      norm_num
    rw [h1, CFSG.Quasithin.RuType.F4.card])

theorem e4_frobenius (x : F4) : e4 (frobenius F4 2 x) = frobF4 (e4 x) := by
  rw [frobenius_def, map_pow, frobF4_apply, sq]

theorem e4_iterate (i : ℕ) (x : F4) :
    e4 ((frobenius F4 2)^[i] x) = (⇑frobF4)^[i] (e4 x) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', e4_frobenius, ih]

theorem frobF4_iterate (i : ℕ) (y : F4c) :
    (⇑frobF4)^[i] y = if (i : ZMod 2) = 0 then y else frobF4 y := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    rcases zmod2_cases (i : ZMod 2) with h0 | h1
    · have h1' : ((i + 1 : ℕ) : ZMod 2) ≠ 0 := by rw [Nat.cast_succ, h0]; decide
      simp [h0, h1']
    · have h0' : (i : ZMod 2) ≠ 0 := by rw [h1]; decide
      have h1' : ((i + 1 : ℕ) : ZMod 2) = 0 := by rw [Nat.cast_succ, h1]; decide
      simp [h0', h1', frobF4_frobF4]

theorem frobVec_ofAdd (i : ℕ) (w : Fin 2 → F4c) (l : Fin 2) :
    frobVec (Multiplicative.ofAdd (i : ZMod 2)) w l = (⇑frobF4)^[i] (w l) := by
  by_cases hc : (i : ZMod 2) = 0 <;> simp [frobVec, frobF4_iterate, hc]

@[expose] noncomputable def E4 : (Fin 2 → F4) ≃+ (Fin 2 → F4c) :=
  AddEquiv.piCongrRight fun _ => e4.toAddEquiv

@[simp] theorem E4_apply (v : Fin 2 → F4) (i : Fin 2) : E4 v i = e4 (v i) := rfl

end Field

section Sigma

open CFSG.Quasithin.RuType (frobF4 frobVec sigmaAct SigmaL2F4)
open CFSG.Quasithin.RuType.Sigma (sigmaAct_mk sigmaAct_mul sigmaAct_one eq_one_of_sigmaAct_eq)

theorem sigma_transport {g : (Fin 2 → F4) ≃ₗ[ZMod 2] (Fin 2 → F4)} (hg : IsSigmaL24Map g) :
    ∃ y : SigmaL2, ∀ v, sigmaAct y (E4 v) = E4 (g v) := by
  obtain ⟨A, i, hA⟩ := hg
  refine ⟨⟨Matrix.SpecialLinearGroup.map (e4 : F4 →+* F4c) A, Multiplicative.ofAdd (i : ZMod 2)⟩,
    fun v => ?_⟩
  funext j
  rw [sigmaAct_mk]
  simp only [E4_apply, hA, Matrix.mulVec, dotProduct, map_sum, map_mul,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    frobVec_ofAdd, e4_iterate]
  rfl

theorem sigmaAct_injective {x y : SigmaL2} (h : ∀ w, sigmaAct x w = sigmaAct y w) : x = y := by
  have h1 : y⁻¹ * x = 1 := eq_one_of_sigmaAct_eq fun w => by
    rw [sigmaAct_mul, h w, ← sigmaAct_mul, inv_mul_cancel, sigmaAct_one]
  exact (inv_mul_eq_one.mp h1).symm

theorem exists_sigma_hom {K : Type*} [Group K]
    (θ : K →* ((Fin 2 → F4) ≃ₗ[ZMod 2] (Fin 2 → F4))) (hσ : ∀ k, IsSigmaL24Map (θ k)) :
    ∃ φ : K →* SigmaL2, ∀ k v, sigmaAct (φ k) (E4 v) = E4 (θ k v) := by
  choose f hf using fun k => sigma_transport (hσ k)
  refine ⟨MonoidHom.mk' f fun a b => sigmaAct_injective fun w => ?_, hf⟩
  obtain ⟨v, rfl⟩ := E4.surjective w
  rw [sigmaAct_mul, hf b v, hf a, hf (a * b) v, map_mul]
  rfl

end Sigma

section Assembly

open CFSG.Quasithin.RuType (sigmaAct SigmaL2F4)

theorem ruTwo_of_eq {G : Type*} [Group G] {L : Subgroup G} {T : Sylow 2 G}
    {V Z H Q U : Subgroup G}
    (hV : CFSG.Quasithin.centerOf (pCoreOf 2 L) = V)
    (hZ : CFSG.Quasithin.centerOf (T : Subgroup G) = Z)
    (hH : Subgroup.centralizer (Z : Set G) = H)
    (hQ : pCoreOf 2 H = Q)
    (hU : CFSG.Quasithin.conjClosure V H = U)
    (sylow_inf : ¬ 2 ∣ ((T : Subgroup G) ⊓ L).relIndex L)
    (V_le_H : V ≤ H) (Z_le_U : Z ≤ U) (U_le_Q : U ≤ Q)
    (symmetric : ∃ φ : H →* Equiv.Perm (Fin 5), Function.Surjective φ ∧
      φ.ker = Q.subgroupOf H)
    (UZ_elem : ∀ u ∈ U, ∀ u' ∈ U, u * u' * u⁻¹ * u'⁻¹ ∈ Z ∧ u ^ 2 ∈ Z)
    (UZ_central : ∀ q ∈ Q, ∀ u ∈ U, q * u * q⁻¹ * u⁻¹ ∈ Z)
    (natural : ∃ (φ : H →* SigmaL2F4) (ψ : U →* Multiplicative (Fin 2 → F4c)),
      Function.Surjective φ ∧ φ.ker = Q.subgroupOf H ∧ Function.Surjective ψ ∧
      ψ.ker = Z.subgroupOf U ∧
      ∀ (h : H) (u u' : U), (u' : G) = h * u * (h : G)⁻¹ →
        ψ u' = Multiplicative.ofAdd (sigmaAct (φ h) (Multiplicative.toAdd (ψ u))))
    (QU_elem : ∀ q ∈ Q, ∀ q' ∈ Q, q * q' * q⁻¹ * q'⁻¹ ∈ U ∧ q ^ 2 ∈ U)
    (QU_card : U.relIndex Q = 2 ^ 6)
    (QU_indecomposable : ∀ A B : Subgroup G, U ≤ A → U ≤ B → A ≤ Q → B ≤ Q →
      H ≤ Subgroup.normalizer (A : Set G) → H ≤ Subgroup.normalizer (B : Set G) →
      A ⊓ B = U → A ⊔ B = Q → A = U ∨ B = U) :
    CFSG.Quasithin.RuType.RuTwo L T := by
  subst hV hZ hH hQ hU
  exact ⟨sylow_inf, V_le_H, Z_le_U, U_le_Q, symmetric, UZ_elem, UZ_central, natural, QU_elem,
    QU_card, QU_indecomposable⟩

end Assembly

end BridgeTwo

section Main

variable {G : Type} [Group G] [Finite G] {L V T : Subgroup G}

open CFSG.Open
open CFSG.Quasithin.RuType (sigmaAct SigmaL2F4)

local notation "F4c" => CFSG.Quasithin.RuType.F4

theorem V_eq_ruV (h : RuType G L V T) : V = CFSG.Quasithin.RuType.ruV L :=
  h.V_eq.trans (BridgeTwo.centerOf_eq (SRu L))

theorem ZRu_eq_ruZ (h : RuType G L V T) : ZRu T = CFSG.Quasithin.RuType.ruZ h.sylowT :=
  BridgeTwo.centerOf_eq T

theorem HRu_eq_ruH (h : RuType G L V T) : HRu T = CFSG.Quasithin.RuType.ruH h.sylowT :=
  congrArg (fun Z : Subgroup G => Subgroup.centralizer (Z : Set G)) (ZRu_eq_ruZ h)

theorem QRu_eq_ruQ (h : RuType G L V T) : QRu T = CFSG.Quasithin.RuType.ruQ h.sylowT :=
  congrArg (pCoreOf 2) (HRu_eq_ruH h)

theorem URu_eq_ruU (h : RuType G L V T) : URu V T = CFSG.Quasithin.RuType.ruU L h.sylowT :=
  (BridgeTwo.conjClosure_eq V (HRu T)).trans
    (congrArg₂ CFSG.Quasithin.conjClosure (V_eq_ruV h) (HRu_eq_ruH h))

theorem ruTwo (h : RuType G L V T)
    (hCV : ∀ l ∈ L, (∀ v ∈ V, l * v = v * l) → l ∈ SRu L) :
    CFSG.Quasithin.RuType.RuTwo L h.sylowT := by
  obtain ⟨θ, hθi, hθσ, hHU, -, ψ', hψs, hψk, hψe⟩ := h.U_L24
  have hV : CFSG.Quasithin.centerOf (pCoreOf 2 L) = V := (V_eq_ruV h).symm
  have hZ : CFSG.Quasithin.centerOf (h.sylowT : Subgroup G) = ZRu T := (ZRu_eq_ruZ h).symm
  have hH : Subgroup.centralizer (ZRu T : Set G) = HRu T := rfl
  have hQ : pCoreOf 2 (HRu T) = QRu T := rfl
  have hU : CFSG.Quasithin.conjClosure V (HRu T) = URu V T :=
    (BridgeTwo.conjClosure_eq V (HRu T)).symm
  have sylow_inf : ¬ 2 ∣ ((h.sylowT : Subgroup G) ⊓ L).relIndex L := by
    have h2 := h.T_choice.2.2
    rw [← h.L_eq] at h2
    exact h2
  have symmetric : ∃ φ : ↥(HRu T) →* Equiv.Perm (Fin 5), Function.Surjective φ ∧
      φ.ker = (QRu T).subgroupOf (HRu T) := by
    obtain ⟨e⟩ := h.H_star
    refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥(HRu T))),
      e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
    exact (BridgeTwo.subgroupOf_pCoreOf (HRu T)).symm
  have UZ_elem : ∀ u ∈ URu V T, ∀ u' ∈ URu V T, u * u' * u⁻¹ * u'⁻¹ ∈ ZRu T ∧ u ^ 2 ∈ ZRu T := by
    intro u hu u' hu'
    have hker : ∀ w : ↥(URu V T), ψ' w = 1 → (w : G) ∈ ZRu T := fun w hw => by
      have : w ∈ ψ'.ker := hw
      rw [hψk, Subgroup.mem_subgroupOf] at this
      exact this
    refine ⟨hker ⟨u * u' * u⁻¹ * u'⁻¹, (URu V T).mul_mem ((URu V T).mul_mem
      ((URu V T).mul_mem hu hu') ((URu V T).inv_mem hu)) ((URu V T).inv_mem hu')⟩ ?_,
      hker ⟨u ^ 2, (URu V T).pow_mem hu 2⟩ ?_⟩
    · have e : (⟨u * u' * u⁻¹ * u'⁻¹, (URu V T).mul_mem ((URu V T).mul_mem
          ((URu V T).mul_mem hu hu') ((URu V T).inv_mem hu)) ((URu V T).inv_mem hu')⟩ :
          ↥(URu V T)) = ⟨u, hu⟩ * ⟨u', hu'⟩ * ⟨u, hu⟩⁻¹ * ⟨u', hu'⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
      exact (commutatorElement_def (ψ' ⟨u, hu⟩) (ψ' ⟨u', hu'⟩)).symm.trans
        (commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _))
    · have e : (⟨u ^ 2, (URu V T).pow_mem hu 2⟩ : ↥(URu V T)) = (⟨u, hu⟩ : ↥(URu V T)) ^ 2 := rfl
      rw [e, map_pow]
      have h2 : Multiplicative.toAdd (ψ' ⟨u, hu⟩) + Multiplicative.toAdd (ψ' ⟨u, hu⟩) = 0 := by
        funext i
        exact CharTwo.add_self_eq_zero _
      rw [sq]
      exact Multiplicative.toAdd.injective (by simpa [toAdd_mul] using h2)
  have UZ_central : ∀ q ∈ QRu T, ∀ u ∈ URu V T, q * u * q⁻¹ * u⁻¹ ∈ ZRu T := by
    intro q hq u hu
    have hqH : q ∈ HRu T := CFSG.LieType.BorelTits.pCoreOf_le 2 (HRu T) hq
    have hqu : q * u * q⁻¹ ∈ URu V T :=
      (Subgroup.mem_normalizer_iff.mp (hHU hqH) u).mp hu
    have hx : ((⟨q, hqH⟩ : ↥(HRu T)) : ↥(HRu T) ⧸ CFSG.pCore 2 ↥(HRu T)) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      obtain ⟨y, hy, hyq⟩ := hq
      have hy' : y = ⟨q, hqH⟩ := Subtype.ext hyq
      rwa [← hy']
    have e := hψe ⟨q, hqH⟩ ⟨u, hu⟩ ⟨q * u * q⁻¹, hqu⟩ rfl
    simp only [hx, map_one, LinearEquiv.coe_one, id_eq, ofAdd_toAdd] at e
    have hmem : (⟨q * u * q⁻¹ * u⁻¹, (URu V T).mul_mem hqu ((URu V T).inv_mem hu)⟩ :
        ↥(URu V T)) ∈ ψ'.ker := by
      have e2 : (⟨q * u * q⁻¹ * u⁻¹, (URu V T).mul_mem hqu ((URu V T).inv_mem hu)⟩ :
          ↥(URu V T)) = ⟨q * u * q⁻¹, hqu⟩ * ⟨u, hu⟩⁻¹ := rfl
      rw [MonoidHom.mem_ker, e2, map_mul, map_inv, e, mul_inv_cancel]
    rw [hψk, Subgroup.mem_subgroupOf] at hmem
    exact hmem
  have natural : ∃ (φ : ↥(HRu T) →* SigmaL2F4)
      (ψ : ↥(URu V T) →* Multiplicative (Fin 2 → F4c)),
      Function.Surjective φ ∧ φ.ker = (QRu T).subgroupOf (HRu T) ∧ Function.Surjective ψ ∧
      ψ.ker = (ZRu T).subgroupOf (URu V T) ∧
      ∀ (x : ↥(HRu T)) (u u' : ↥(URu V T)), (u' : G) = x * u * (x : G)⁻¹ →
        ψ u' = Multiplicative.ofAdd (sigmaAct (φ x) (Multiplicative.toAdd (ψ u))) := by
    obtain ⟨φq, hφq⟩ := BridgeTwo.exists_sigma_hom θ hθσ
    have hφqi : Function.Injective φq := by
      intro a b hab
      apply hθi
      refine LinearEquiv.ext fun v => BridgeTwo.E4.injective ?_
      rw [← hφq a v, ← hφq b v, hab]
    have hcard : Nat.card (↥(HRu T) ⧸ CFSG.pCore 2 ↥(HRu T)) = 120 := by
      obtain ⟨e⟩ := h.H_star
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have hφqs : Function.Surjective φq :=
      (hφqi.bijective_of_nat_card_le (by
        rw [hcard, CFSG.Quasithin.RuType.Sigma.card_Sigma'])).2
    let ψ : ↥(URu V T) →* Multiplicative (Fin 2 → F4c) :=
      { toFun := fun u => Multiplicative.ofAdd (BridgeTwo.E4 (Multiplicative.toAdd (ψ' u)))
        map_one' := by simp
        map_mul' := fun a b => by simp [map_add] }
    refine ⟨φq.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥(HRu T))), ψ,
      hφqs.comp (QuotientGroup.mk'_surjective _), ?_, ?_, ?_, ?_⟩
    · rw [MonoidHom.ker_comp_of_injective _ _ hφqi, QuotientGroup.ker_mk']
      exact (BridgeTwo.subgroupOf_pCoreOf (HRu T)).symm
    · intro m
      obtain ⟨u, hu⟩ := hψs (Multiplicative.ofAdd (BridgeTwo.E4.symm (Multiplicative.toAdd m)))
      exact ⟨u, by simp [ψ, hu]⟩
    · rw [← hψk]
      ext u
      simp [ψ, MonoidHom.mem_ker]
    · intro x u u' hu'
      have e := hψe x u u' hu'
      show Multiplicative.ofAdd (BridgeTwo.E4 (Multiplicative.toAdd (ψ' u'))) =
        Multiplicative.ofAdd (sigmaAct (φq (x : ↥(HRu T) ⧸ CFSG.pCore 2 ↥(HRu T)))
          (BridgeTwo.E4 (Multiplicative.toAdd (ψ' u))))
      rw [e, toAdd_ofAdd, hφq]
  exact BridgeTwo.ruTwo_of_eq hV hZ hH hQ hU sylow_inf (BridgeTwo.V_le_H h hCV)
    ((BridgeTwo.Z_le_V h hCV).trans (BridgeTwo.V_le_URu h)) h.Q_over_U.1 symmetric UZ_elem
    UZ_central natural
    (fun q hq q' hq' => ⟨h.Q_over_U.2.2.2.1 q hq q' hq', h.Q_over_U.2.2.1 q hq⟩)
    h.Q_over_U.2.1
    (fun A B hUA hUB hAQ hBQ hAn hBn hinf hsup =>
      h.Q_over_U.2.2.2.2 A B hUA hAQ hUB hBQ hAn hBn hsup hinf)

end Main

end CFSG.ASVolI.ChIJK.RuType
