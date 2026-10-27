module

public import CFSG.Quasithin.H13.L32NLem14411a
public import CFSG.Quasithin.H13.L32NItems144c
public import CFSG.Quasithin.H13.L32NLem1444a
public import CFSG.Quasithin.H13.L32NS7Model
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsInst

public section

namespace CFSG.Quasithin.H13.L14411

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Mat8Cert S7Cert L1442M

theorem quadOf_q4 (v : Fin 8 → ZMod 2) : quadOf q4 v = q4V v := by
  simp only [quadOf, q4, q4V, dotProduct, Matrix.mulVec, Fin.sum_univ_eight]
  simp

theorem add_self_zmod2 {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (v : M) : v + v = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem neg_eq_self_zmod2 {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (v : M) : -v = v := by
  rw [neg_eq_iff_add_eq_zero, add_self_zmod2]

section Form

variable {G : Type} [Group G]

@[expose] noncomputable def ind (w : G) : ZMod 2 := by
  classical exact if w = 1 then 0 else 1

theorem ind_eq_zero {w : G} : ind w = 0 ↔ w = 1 := by
  unfold ind
  split_ifs with h
  · simp [h]
  · simp [h]

theorem ind_mul {Z : Subgroup G} (hZ : Nat.card Z = 2) {a b : G} (ha : a ∈ Z) (hb : b ∈ Z) :
    ind (a * b) = ind a + ind b := by
  obtain ⟨y, hy1, hy⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ
  have hcases : ∀ w ∈ Z, w = 1 ∨ w = (y : G) := by
    intro w hw
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · exact Or.inr (congrArg Subtype.val (hy ⟨w, hw⟩ fun he => hw1 (congrArg Subtype.val he)))
  have hy1' : (y : G) ≠ 1 := fun he => hy1 (Subtype.ext he)
  have hyy : (y : G) * y = 1 := by
    rcases hcases _ (Z.mul_mem y.2 y.2) with h | h
    · exact h
    · exact absurd (by simpa using h) hy1'
  have h1 : ind (1 : G) = 0 := ind_eq_zero.mpr rfl
  have hy' : ind (y : G) = 1 := by
    unfold ind
    simp [hy1']
  rcases hcases a ha with rfl | rfl <;> rcases hcases b hb with rfl | rfl
  · simp [h1]
  · simp [h1]
  · simp [h1]
  · rw [hyy, h1, hy']
    decide

theorem form_of_quad {U : Subgroup G} (D : HatModelU U) (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2))
    (hZ : Nat.card (centerOf U) = 2)
    (hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ centerOf U)
    (hq : ∀ u ∈ U, quadOf q4 (e (D.π u)) = 0 ↔ u * u = 1) (x y : D.V) :
    D.B x y = b4V (e x) (e y) := by
  obtain ⟨u, hu, rfl⟩ := D.π_surj x
  obtain ⟨v, hv, rfl⟩ := D.π_surj y
  have hsq : ∀ w ∈ U, w * w ∈ centerOf U := fun w hw => by
    rw [← L128A.HatU.π_eq_zero_iff D (U.mul_mem hw hw), D.π_mul w hw w hw]
    exact add_self_zmod2 _
  have hq' : ∀ w ∈ U, q4V (e (D.π w)) = ind (w * w) := fun w hw =>
    L128A.HatU.zmod_two_eq_of_iff (by rw [← quadOf_q4, hq w hw, ind_eq_zero])
  have hB : D.B (D.π u) (D.π v) = ind (u * v * u⁻¹ * v⁻¹) :=
    L128A.HatU.zmod_two_eq_of_iff (by rw [D.B_spec u hu v hv, ind_eq_zero])
  have hc : u⁻¹ * v * u * v⁻¹ ∈ centerOf U := by
    have := hcomm u⁻¹ (U.inv_mem hu) v hv
    simpa using this
  have hcd : ind (u⁻¹ * v * u * v⁻¹) = ind (u * v * u⁻¹ * v⁻¹) := by
    apply L128A.HatU.zmod_two_eq_of_iff
    rw [ind_eq_zero, ind_eq_zero]
    constructor
    · intro h
      have hvu : v * u = u * v := by
        calc v * u = u * (u⁻¹ * v * u * v⁻¹) * v := by group
          _ = u * v := by rw [h]; group
      calc u * v * u⁻¹ * v⁻¹ = (v * u) * u⁻¹ * v⁻¹ := by rw [hvu]
        _ = 1 := by group
    · intro h
      have huv : u * v = v * u := by
        calc u * v = (u * v * u⁻¹ * v⁻¹) * v * u := by group
          _ = v * u := by rw [h]; group
      calc u⁻¹ * v * u * v⁻¹ = u⁻¹ * (v * u) * v⁻¹ := by group
        _ = u⁻¹ * (u * v) * v⁻¹ := by rw [huv]
        _ = 1 := by group
  have hprod : (u * v) * (u * v) = (u * u) * ((u⁻¹ * v * u * v⁻¹) * (v * v)) := by group
  have hind : ind ((u * v) * (u * v)) =
      ind (u * u) + (ind (u⁻¹ * v * u * v⁻¹) + ind (v * v)) := by
    rw [hprod, ind_mul hZ (hsq u hu) ((centerOf U).mul_mem hc (hsq v hv)),
      ind_mul hZ hc (hsq v hv)]
  rw [hB, b4V, ← map_add, ← D.π_mul u hu v hv, hq' _ (U.mul_mem hu hv), hq' u hu, hq' v hv, hind,
    hcd]
  generalize ind (u * u) = p
  generalize ind (v * v) = r
  generalize ind (u * v * u⁻¹ * v⁻¹) = s
  revert p r s
  decide

end Form

@[expose] noncomputable def linOf (c : GL (Fin 8) (ZMod 2)) :
    (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (c : Matrix (Fin 8) (Fin 8) (ZMod 2)))
    (Matrix.toLin' ((c⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)))
    (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])

theorem linOf_apply (c : GL (Fin 8) (ZMod 2)) (x : Fin 8 → ZMod 2) :
    linOf c x = (c : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec x := rfl

section Coords

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (e : V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2))

theorem matOf_trans (c : GL (Fin 8) (ZMod 2)) (ψ : V ≃ₗ[ZMod 2] V) :
    matOf (e.trans (linOf c)) ψ = c * matOf e ψ * c⁻¹ := by
  rw [matOf_eq_iff]
  intro v
  simp only [LinearEquiv.trans_apply, linOf_apply, Units.val_mul, ← Matrix.mulVec_mulVec]
  rw [Matrix.mulVec_mulVec (e v) ((c⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2))
    (c : Matrix (Fin 8) (Fin 8) (ZMod 2)), ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec, matOf_mulVec]

end Coords

theorem img8_trans {G : Type} [Group G] {U : Subgroup G} (D : HatModelU U)
    (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) (c : GL (Fin 8) (ZMod 2)) (Y : Subgroup G) :
    img8 D (e.trans (linOf c)) Y = (img8 D e Y).map (MulAut.conj c).toMonoidHom := by
  unfold img8
  rw [Subgroup.map_map]
  congr 1
  ext ψ
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [matOf_trans]

theorem exists_conj_of_sylow {Γ : Type*} [Group Γ] [Finite Γ] {S K P : Subgroup Γ}
    (hKS : K ≤ S) (hPS : P ≤ S) (hK2 : IsPGroup 2 K) (hP2 : IsPGroup 2 P)
    (hKi : ¬ 2 ∣ K.relIndex S) (hPi : ¬ 2 ∣ P.relIndex S) :
    ∃ c ∈ S, ∀ x ∈ K, c * x * c⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : IsPGroup 2 ↥(K.subgroupOf S) := hK2.of_equiv (Subgroup.subgroupOfEquivOfLe hKS).symm
  have hP' : IsPGroup 2 ↥(P.subgroupOf S) := hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPS).symm
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥S (hK'.toSylow hKi) (hP'.toSylow hPi)
  refine ⟨c, c.2, fun x hx => ?_⟩
  have hx' : (⟨x, hKS hx⟩ : ↥S) ∈ ((hK'.toSylow hKi : Sylow 2 ↥S) : Subgroup ↥S) :=
    (hK'.mem_toSylow hKi).mpr (Subgroup.mem_subgroupOf.mpr hx)
  have h1 : c * ⟨x, hKS hx⟩ * c⁻¹ ∈ ((c • hK'.toSylow hKi : Sylow 2 ↥S) : Subgroup ↥S) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mpr (by
      rw [MulAut.smul_def, MulAut.conj_inv_apply]
      simpa [mul_assoc] using hx')
  rw [hc] at h1
  have h2 := Subgroup.mem_subgroupOf.mp ((hP'.mem_toSylow hPi).mp h1)
  simpa using h2

theorem le_of_normalizes {Γ : Type*} [Group Γ] [Finite Γ] {T H X : Subgroup Γ}
    (hT : IsSylowTwoOf T H) (hX : IsPGroup 2 X) (hXH : X ≤ H)
    (hTX : T ≤ Subgroup.normalizer (X : Set Γ)) : X ≤ T := by
  have hXT : IsPGroup 2 ↥(X ⊔ T) := hX.to_sup_of_normal_left' hT.2.1 hTX
  exact le_sup_left.trans ((A4.isSylowTwoOf_iff_maximal.mp hT).2.2 (X ⊔ T) (sup_le hXH hT.1) hXT
    le_sup_right)

theorem map_conj_of_mem {Γ : Type*} [Group Γ] {S : Subgroup Γ} {c : Γ} (hc : c ∈ S) :
    S.map (MulAut.conj c).toMonoidHom = S := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact S.mul_mem (S.mul_mem hc hx) (S.inv_mem hc)
  · intro hy
    exact ⟨c⁻¹ * y * c, S.mul_mem (S.mul_mem (S.inv_mem hc) hy) hc, by simp [mul_assoc]⟩

structure Ctx0 (G : Type) [Group G] [Finite G] (T L V V₂ : Subgroup G) (g : G)
    (D : HatModelU (fsuU T V)) (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) : Prop where
  h1332 : Stmt13_3_2
  h1334 : A6.Stmt13_3_4
  h1222 : Stmt12_2_2
  hyp : Hyp14310One G T L V
  ext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)
  plane : IsL32NPlane T V V₂
  gP : g ∈ p128 T L V
  gH : g ∉ l32nH T V
  zU : centerOf (fsuU T V) = fsuV1 T V
  cHat : l32nCHat T V = pCoreOf 2 (l32nH T V)
  s1282 : Setting1282One G T L V 3 (fsuV1 T V) V₂
  abs : L128A.Setting V₂ (fsuV1 T V) (oTwoUpper (p128 T L V)) T
  uA : L128A.uA V₂ (fsuV1 T V) = fsuU T V
  wwE : ⁅l32nW T V V₂, CFSG.conjugate (l32nW T V V₂) g⁆ ≤ l32nE T V V₂ g
  nWg : l32nH T V ⊓ Subgroup.normalizer (V₂ : Set G) ≤
    Subgroup.normalizer ((CFSG.conjugate (l32nW T V V₂) g ⊔ l32nCHat T V : Subgroup G) : Set G)
  cardW : Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) = 2 ^ 3
  imgH : img8 D e (l32nH T V) = s7
  form : ∀ x y : D.V, D.B x y = b4V (e x) (e y)

structure Ctx (G : Type) [Group G] [Finite G] (T L V V₂ : Subgroup G) (g : G)
    (D : HatModelU (fsuU T V)) (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) : Prop
    extends Ctx0 G T L V V₂ g D e where
  imgT : img8 D e T = P7

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}
  {D : HatModelU (fsuU T V)} {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)}

omit [Finite G] in
theorem HN : l32nH T V ≤ Subgroup.normalizer (fsuU T V : Set G) :=
  L14332.l32nH_le_normalizer_fsuU T V

namespace Ctx0

variable (C : Ctx0 G T L V V₂ g D e)
include C


theorem UT : fsuU T V ≤ T := C.uA ▸ C.abs.uA_le_T

theorem TH : T ≤ l32nH T V := C.hyp.le_l32nH (stmtL32NModule_of_inputs C.h1332 C.h1334)

theorem UH : fsuU T V ≤ l32nH T V := C.UT.trans C.TH

theorem comm_center : ∀ a ∈ fsuU T V, ∀ b ∈ fsuU T V, a * b * a⁻¹ * b⁻¹ ∈ centerOf (fsuU T V) :=
  L1444.comm_mem_centerOf C.ext

theorem matOf_eq_one_iff {h : G} (hh : h ∈ l32nH T V) :
    matOf e (D.ρ ⟨h, HN hh⟩) = 1 ↔ h ∈ pCoreOf 2 (l32nH T V) := by
  rw [← C.cHat, ← L14332.rho_eq_one_iff_mem hh (HN hh), ← (matOf e).map_one]
  exact (matOf_injective e).eq_iff

theorem QT : pCoreOf 2 (l32nH T V) ≤ T :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  le_of_normalizes (isSylowTwoOf_of_quasithinIsSylowTwo C.hyp.fsu.sylow C.TH)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _)
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
    (C.TH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))

theorem card_img_eq {Y : Subgroup G} (hYH : Y ≤ l32nH T V) :
    Nat.card (D.img Y) = (pCoreOf 2 (l32nH T V)).relIndex Y := by
  refine L128A.HatU.card_img_eq_relIndex D (hYH.trans HN) fun x hx => ?_
  constructor
  · rintro ⟨hxN, h1⟩
    rw [← C.cHat]
    exact (L14332.rho_eq_one_iff_mem (hYH hx) hxN).mp h1
  · intro hxQ
    refine ⟨HN (hYH hx), ?_⟩
    rw [← C.cHat] at hxQ
    exact (L14332.rho_eq_one_iff_mem (hYH hx) (HN (hYH hx))).mpr hxQ

end Ctx0

section Cert


namespace Ctx0

variable (C : Ctx0 G T L V V₂ g D e)
include C

theorem card_imgT : Nat.card (img8 D e T) = 16 := by
  have hH : (pCoreOf 2 (l32nH T V)).relIndex (l32nH T V) = 5040 := by
    rw [← C.card_img_eq le_rfl, ← card_img8 D e, C.imgH, card_s7]
  have hT : Nat.card (img8 D e T) = (pCoreOf 2 (l32nH T V)).relIndex T := by
    rw [card_img8, C.card_img_eq C.TH]
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 (l32nH T V)) T (l32nH T V) C.QT C.TH
  rw [hH, ← hT] at hmul
  have hodd : ¬ 2 ∣ T.relIndex (l32nH T V) :=
    (isSylowTwoOf_of_quasithinIsSylowTwo C.hyp.fsu.sylow C.TH).2.2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 ↥(img8 D e T) := by
    rw [img8_eq_map]
    exact (C.hyp.fsu.sylow.1.of_equiv
      (Subgroup.subgroupOfEquivOfLe (C.TH.trans HN)).symm).map _
  obtain ⟨m, hm⟩ := h2.exists_card_eq
  rw [hm] at hmul ⊢
  have hm13 : m < 13 := by
    by_contra hc
    have h13 : 2 ^ 13 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpos : 0 < T.relIndex (l32nH T V) := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, mul_zero] at hmul
      omega
    nlinarith
  interval_cases m <;> norm_num at hmul ⊢ <;> omega

end Ctx0

theorem relIndex_s7 {K : Subgroup (GL (Fin 8) (ZMod 2))}
    (hK : K ≤ s7) (h16 : Nat.card K = 16) : K.relIndex s7 = 315 := by
  have h := Subgroup.relIndex_mul_card K s7
  rw [inf_eq_left.mpr hK, h16, card_s7] at h
  omega

theorem exists_ctx (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h12811 : Lemma12_8_11)
    (h12812 : Lemma12_8_12_two) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h : Hyp14310One G T L V) (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V))
    (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V) (hgH : g ∉ l32nH T V)
    (h4 : Case1442Four T V V₂ g D) :
    ∃ e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2), Ctx G T L V V₂ g D e := by
  obtain ⟨e₀, hiso, hW8, -⟩ := h4
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  have hV := stmtL32NModule_of_inputs h1332 h1334
  have hs := h.setting1282One h13322 hV hV₂
  have hZ2 : Nat.card ↥(centerOf (fsuU T V)) = 2 := by
    rw [l32n_card_centerOf]
    exact hext.2.2.2
  have himgH : img8 D e₀ (l32nH T V) = s7 := by
    ext γ
    rw [mem_img8]
    constructor
    · rintro ⟨y, hy, hyN, rfl⟩
      obtain ⟨γ', hγ', hγ'e⟩ := (hiso.img _).mp (L128A.HatU.rho_mem_img D hy hyN)
      rwa [(matOf_eq_iff e₀ _ γ').mpr hγ'e]
    · intro hγ
      have hψ : e₀.trans ((linOf γ).trans e₀.symm) ∈ D.img (l32nH T V) :=
        (hiso.img _).mpr ⟨γ, hγ, fun v => by simp [linOf_apply]⟩
      obtain ⟨y, hy, hyN, hye⟩ := (L128A.HatU.mem_img D).mp hψ
      refine ⟨y, hy, hyN, ?_⟩
      rw [hye, matOf_eq_iff]
      intro v
      simp [linOf_apply]
  have hform₀ := form_of_quad D e₀ hZ2 (L1444.comm_mem_centerOf hext) hiso.quad
  have C₀ : Ctx0 G T L V V₂ g D e₀ :=
    { h1332 := h1332, h1334 := h1334, h1222 := h1222, hyp := h, ext := hext, plane := hV₂,
      gP := hgP, gH := hgH, zU := L1444.zU_eq h1332 h1334 h1222 h12213 h hext,
      cHat := L1444.cHat_eq h1332 h1334 h1222 h12213 h37 h38 h39 h hext, s1282 := hs,
      abs := L128P.setting128A h1222 h12213 hs, uA := (lemma12_8_8_six h1222 hs).symm,
      wwE := (h12811 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgH).1,
      nWg := (h12812 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgH).1, cardW := hW8,
      imgH := himgH, form := hform₀ }
  have hKs : img8 D e₀ T ≤ s7 := himgH ▸ img8_mono D e₀ C₀.TH
  have hK16 := C₀.card_imgT
  have hK2 : IsPGroup 2 ↥(img8 D e₀ T) :=
    IsPGroup.of_card (n := 4) (by rw [hK16]; norm_num)
  have hP2 : IsPGroup 2 ↥P7 := IsPGroup.of_card (n := 4) (by rw [card_P7]; norm_num)
  obtain ⟨c, hcs, hc⟩ := exists_conj_of_sylow hKs P7_le_s7 hK2 hP2
    (by rw [relIndex_s7 hKs hK16]; decide) (by rw [relIndex_s7 P7_le_s7 card_P7]; decide)
  obtain ⟨y, hyH, hyN, hyc⟩ := (mem_img8 D e₀).mp (himgH ▸ hcs)
  have hce : ∀ x : D.V, (c : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e₀ x) =
      e₀ (D.ρ ⟨y, hyN⟩ x) := fun x => by rw [← hyc, matOf_mulVec]
  refine ⟨e₀.trans (linOf c), { C₀ with imgH := ?_, form := ?_, imgT := ?_ }⟩
  · rw [img8_trans, himgH, map_conj_of_mem hcs]
  · intro x y'
    simp only [LinearEquiv.trans_apply, linOf_apply, hce]
    rw [← hform₀, L128A.HatU.B_rho]
  · have hle : img8 D (e₀.trans (linOf c)) T ≤ P7 := by
      rw [img8_trans]
      rintro _ ⟨x, hx, rfl⟩
      exact hc x hx
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_P7, img8_trans, Subgroup.card_map_of_injective (MulEquiv.injective _), hK16]

end Cert

end CFSG.Quasithin.H13.L14411
