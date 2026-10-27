module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513Sub
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem512FFProof
public import CFSG.Quasithin.Vol2.Ch5ModulesOrthA5
public import CFSG.Quasithin.Vol2.Ch10SecAShapeB45
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Background.InternalSecFF
public import CFSG.Quasithin.Background.InternalSecReal

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped IsMulCommutative

theorem l2Order_ne_sz {f n : ℕ} (hf : 1 ≤ f) (hn : 1 ≤ n) :
    (2 ^ f) ^ 2 * (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) ≠ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  intro h
  have hq2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hodd1 : Odd (2 ^ f - 1) := odd_two_pow_sub_one hf
  have hodd2 : Odd ((2 ^ f) ^ 2 + 1) := by
    have he : Even ((2 ^ f) ^ 2) := (Nat.even_pow' (by norm_num)).mpr
      ((Nat.even_pow' (by omega)).mpr even_two)
    exact he.add_one
  have h' : 2 ^ (2 * f) * ((2 ^ f - 1) * ((2 ^ f) ^ 2 + 1)) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [← h, mul_comm 2 f, pow_mul, mul_assoc]
  obtain ⟨h1, h2⟩ := two_pow_mul_odd_inj (hodd1.mul hodd2) (odd_two_pow_pow_sub_one hn
    (by norm_num)) h'
  rw [← h1, mul_comm 2 f, pow_mul] at h2
  set q := 2 ^ f with hq
  have e1 : 1 ≤ q := by omega
  have e2 : 1 ≤ (q ^ 2) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  zify [e1, e2] at h2
  nlinarith [h2]

theorem isShapeGroup_of_lieModel_psl2 {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (h : LieModel X .PSL 2 2 n) : Vol2.Ch10.SecA.IsShapeGroup X := by
  obtain ⟨e⟩ := nonempty_equiv_psl_of_lieModel (by omega) h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hc : CharP (GaloisField 2 n) 2 := charP_two_of_card hK
  have hZ : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) = ⊥ :=
    center_sl_eq_bot fun r hr => by
      have h1 : (r - 1) ^ 2 = 0 := by
        rw [sub_sq, hr, mul_one, two_mul, CharTwo.add_self_eq_zero, sub_zero, one_pow,
          CharTwo.add_self_eq_zero]
      exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h1)
  exact Or.inl ⟨n, hn, GaloisField 2 n, inferInstance, inferInstance, hK,
    ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)⟩⟩

section Extend

variable {G : Type} [Group G] {Y V W : Subgroup G} [IsMulCommutative ↥V] [IsMulCommutative ↥W]

theorem FFModel.Realizes.extend {D : FFModel} (hYV : Y ≤ Subgroup.normalizer (V : Set G))
    (hYW : Y ≤ Subgroup.normalizer (W : Set G)) (hWV : W ≤ V)
    (hker : Y ⊓ Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer (V : Set G))
    (h : D.Realizes (autOn Y W) ⊤ ⊥) : D.Realizes (autOn Y V) (W.subgroupOf V) ⊥ := by
  obtain ⟨π, hsurj, -, hks, -, -, hsec, hkerD, β, hβs, hβk, hβe⟩ := h
  obtain ⟨r, hrs, hr⟩ := exists_autOn_restrict hYV hYW hWV
  have hri : Function.Injective r := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨⟨y, hyN⟩, hyY, hya⟩ := Subgroup.mem_map.mp a.2
    rw [Subgroup.mem_subgroupOf] at hyY
    have hyW : y ∈ Subgroup.centralizer (W : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h1 := hr a ⟨w, hw⟩
      rw [ha] at h1
      have h2 : ((a : MulAut ↥V) ⟨w, hWV hw⟩ : G) = y * w * y⁻¹ := by
        rw [← hya, conjAct_coe_apply]
      have h3 : (w : G) = y * w * y⁻¹ := h1.trans h2
      have h4 := congrArg (· * y) h3
      simpa [mul_assoc] using h4
    have hyV := Subgroup.mem_centralizer_iff.mp (hker ⟨hyY, hyW⟩)
    apply Subtype.ext
    rw [← hya]
    ext v
    rw [conjAct_coe_apply, OneMemClass.coe_one, MulAut.one_apply, ← hyV (v : G) v.2,
      mul_inv_cancel_right]
  let e : ↥(autOn Y V) ≃* ↥(autOn Y W) := MulEquiv.ofBijective r ⟨hri, hrs⟩
  have he : ∀ x, r (e.symm x) = x := fun x => e.apply_symm_apply x
  let φ : ↥(W.subgroupOf V) →* ↥(⊤ : Subgroup ↥W) :=
    { toFun := fun u => ⟨⟨(u : ↥V), u.2⟩, Subgroup.mem_top _⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hφs : Function.Surjective φ := by
    rintro ⟨⟨w, hw⟩, -⟩
    exact ⟨⟨⟨w, hWV hw⟩, hw⟩, rfl⟩
  have hinvW : ∀ x : ↥(autOn Y V), ∀ u ∈ W.subgroupOf V, (x : MulAut ↥V) u ∈ W.subgroupOf V := by
    intro x u hu
    obtain ⟨⟨y, hyN⟩, hyY, hyx⟩ := Subgroup.mem_map.mp x.2
    rw [Subgroup.mem_subgroupOf] at hyY ⊢
    rw [← hyx, conjAct_coe_apply]
    exact (Subgroup.mem_normalizer_iff.mp (hYW hyY) _).mp hu
  refine ⟨e.symm.toMonoidHom.comp π, e.symm.surjective.comp hsurj, bot_le, hks, hinvW, ?_, hsec,
    hkerD, β.comp φ, hβs.comp hφs, ?_, ?_⟩
  · intro a z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro u
    rw [MonoidHom.comp_apply, hβk, Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · intro h1
      apply Subtype.ext
      exact congrArg (fun x : ↥W => (x : G)) h1
    · intro h1
      apply Subtype.ext
      exact congrArg (fun x : ↥V => (x : G)) h1
  · intro γ u m hu hm hum
    have hmem : (((π γ : ↥(autOn Y W)) : MulAut ↥W) (φ u : ↥W) : G) ∈ (W : Set G) :=
      (((π γ : ↥(autOn Y W)) : MulAut ↥W) (φ u : ↥W)).2
    have h1 : φ ⟨((e.symm (π γ) : ↥(autOn Y V)) : MulAut ↥V) (u : ↥V), hu⟩ =
        ⟨((π γ : ↥(autOn Y W)) : MulAut ↥W) (φ u : ↥W), Subgroup.mem_top _⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      have := hr (e.symm (π γ)) (φ u : ↥W)
      rw [he] at this
      exact this.symm
    show β (φ ⟨((e.symm (π γ) : ↥(autOn Y V)) : MulAut ↥V) (u : ↥V), hu⟩) = _
    rw [h1]
    exact hβe γ (φ u) m (Subgroup.mem_top _) hm hum

end Extend

namespace Hyp5_0_1

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

theorem lemma_5_1_3_top (hF : Vol2.Ch10.SecA.Facts10_1) (h45 : AsB45)
    (h16 : ASInputs.AS_I_1_6) (h : Hyp5_0_1 G T M L n) (hV : IsCh5Module T L V)
    (hC : V ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hq : qhatInt (L ⊔ T) V hV.isTwoReducedIn.2.2.1 ≤ 2)
    (hI : IsIrrPlusBase L V ⁅V, L⁆) :
    IsNatQuotCh5 L ⁅V, L⁆ n ∨ IsOrthCh5 L V n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := hV.isTwoReducedIn
  have hVel : IsElemAbelian 2 V := hred.2.2.1
  have hYV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hYV
  set U := ⁅V, L⁆ with hUdef
  have hUV : U ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hYU : L ⊔ T ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_commutator_of hYV h.sup_le_normalizer
  have hLU : L ≤ Subgroup.normalizer (U : Set G) := le_sup_left.trans hYU
  have hUcomm : ⁅U, L⁆ = U := hI.2.2.2.1
  have hUL : ⁅U, L⁆ ≠ ⊥ := by rw [hUcomm]; exact hI.2.1
  have hUel : IsElemAbelian 2 U := isElemAbelian_mono hVel hUV
  let _ : IsMulCommutative ↥U := hUel.1
  let _ : IsMulCommutative ↥V := hVel.1
  have hUC : U ⊓ Subgroup.centralizer (L : Set G) = ⊥ :=
    le_bot_iff.mp (hC ▸ inf_le_inf_right _ hUV)
  set C : Subgroup ↥U := (Subgroup.centralizer (L : Set G)).subgroupOf U with hCdef
  have hCbot : C = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    have : (u : G) ∈ U ⊓ Subgroup.centralizer (L : Set G) := ⟨u.2, hu⟩
    rw [hUC, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  have hsec : InternalSec.ISec U (L ⊔ T) L (Subgroup.centralizer (L : Set G)) := by
    refine ⟨fun u hu => hVel.2 u (hUV hu), hYU, le_sup_left, h.sup_le_normalizer, ?_, ?_,
      inf_le_right, hUcomm, ?_, ?_, h.pCoreOf_autOn_L_eq_bot_of_le hV hUV hYU hUL,
      h.isQuasisimple_autOn_of_le hV hUV hYU hUL⟩
    · intro y hy
      obtain ⟨e, he⟩ := InternalSec.two_of_sup h.sylow.1 h.T_le_normalizer y hy
      exact ⟨e, Subgroup.mem_sup_left he⟩
    · rw [hUC]
      intro g _
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp
    · intro hle
      apply hI.2.1
      rw [eq_bot_iff, ← hUC]
      exact le_inf le_rfl hle
    · intro J h1 h2 h3
      exact hI.2.2.2.2.2 J h1 h2 h3
  have hSK := h.sqtkGroup_autOn_of_le hV hUV hYU hUL
  have hB := hsec.b4Hyp hSK
  have hqs := hsec.qsec
  have hK : autOn L U ≤ stabSub C := hqs.le.trans hqs.stab
  have hf : autOn L U ⊓ centSec ⊤ C = ⊥ := hqs.faithful
  have hfaith : (L ⊔ T) ⊓ Subgroup.centralizer (U : Set G) ≤
      Subgroup.centralizer (V : Set G) := by
    rw [h.sup_inf_centralizer_eq_of_le hV hUV hYU hUL]
    exact inf_le_right
  have hqU : qhatInt (L ⊔ T) U hUel ≤ 2 :=
    (qhatInt_le_qhatInt_of_le hVel hUV hYU hfaith hq).trans hq
  have hqU' : qhatOf (autOn (L ⊔ T) U) ≤ (2 : WithTop ℚ) := hqU
  have hqsec : qhatOf (autSec (autOn (L ⊔ T) U) ⊤ C) ≤ ((2 : ℚ) : WithTop ℚ) := by
    refine hsec.qhatOf_sec_le.trans ?_
    exact_mod_cast hqU'
  have hkerL : L ⊓ Subgroup.centralizer (U : Set G) ≤ Subgroup.centralizer (V : Set G) :=
    fun x hx => hfaith ⟨Subgroup.mem_sup_left hx.1, hx.2⟩
  obtain ⟨eL⟩ := h.nonempty_autOn_equiv_of_le hV hUV hYU hUL
  let e' : ↥(autSec (autOn L U) ⊤ C) ≃* ↥(autOn L U) :=
    (B5.secEquiv (autOn L U) (InternalSec.le_stabSub_top _) hK hf).symm
  have : IsSimpleGroup ↥(autSec (autOn L U) ⊤ C) := by
    have := h.isSimple
    exact (e'.trans eL).isSimpleGroup
  have hsh : Vol2.Ch10.SecA.IsShapeGroup ↥(autSec (autOn L U) ⊤ C) :=
    (isShapeGroup_of_lieModel_psl2 h.two_le h.lie).of_mulEquiv (e'.trans eL)
  have hcK : Nat.card ↥(autOn L U) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr eL.toEquiv]
    exact h.card_quot
  have hsv : ∀ v : Sec (⊤ : Subgroup ↥U) C, v ^ 2 = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H w =>
      rw [← QuotientGroup.mk_pow,
        show w ^ 2 = 1 from Subtype.ext (Subtype.ext (by simpa using hVel.2 _ (hUV (w : ↥U).2))),
        QuotientGroup.mk_one]
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hVel.2 v v.2)
  have hfix0 : fixV (autOn L V) = ⊥ := by
    rw [fixV_autOn hLV, eq_bot_iff]
    intro v hv
    have : (v : G) ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨v.2, hv⟩
    rw [hC, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  have hcommV : commV (autOn L V) = U.subgroupOf V := by
    apply Subgroup.map_injective V.subtype_injective
    rw [map_commV_autOn hLV, Subgroup.map_subgroupOf_eq_of_le hUV]
  have htop : ASInputs.I16Module (autOn L V) (U.subgroupOf V) ⊥ 0 → U.subgroupOf V = ⊤ := by
    intro hM
    rw [← hcommV] at hM
    have h1 := (h16 ↥V hV2 (autOn L V) 0).2 hfix0 hM
    rw [pow_zero] at h1
    have h2 : (commV (autOn L V)).index = 1 :=
      le_antisymm h1 (Nat.one_le_iff_ne_zero.mpr (Subgroup.index_ne_zero_of_finite))
    rw [← hcommV]
    exact Subgroup.index_eq_one.mp h2
  have hext : ∀ {D : FFModel}, D.Realizes (autOn L U) ⊤ C →
      D.Realizes (autOn L V) (U.subgroupOf V) ⊥ := by
    intro D hD
    rw [hCbot] at hD
    exact FFModel.Realizes.extend hLV hLU hUV hkerL hD
  have horth : ∀ m : ℕ, 1 ≤ m → BinaryOrthogonalFour (autOn L U) ⊤ C m → IsOrthCh5 L V n := by
    intro m hm hO
    obtain ⟨F, _, _, _, hFc, hR⟩ := hO
    have h1 := card_eq_card_gam (Vol2.Ch10.SecA.twistTensor_faithful m) hR
    have h2 : Nat.card (FFModel.twistTensor m (StatedSL 2 F)).Gam =
        Nat.card F * (Nat.card F ^ 2 - 1) := card_statedSL_two
    rw [h2, hFc, hcK] at h1
    have hnm : n = 2 * m := l2Order_inj h1
    have hRV := hext hR
    have hU := htop (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm, rfl,
      ⟨F, inferInstance, inferInstance, inferInstance, hFc, hRV⟩⟩))))
    rw [hU] at hRV
    exact ⟨m, hnm, hLV, hVel.1, F, inferInstance, inferInstance, inferInstance, hFc, hRV⟩
  rcases h45 _ hsv _ _ hB hqsec with ⟨-, ⟨A, hA⟩, hall⟩ | ⟨-, ht⟩ | h3
  · rcases Vol2.Ch10.SecA.b42_of_isShapeGroup hF hsv hB hA (hall A hA) hsh with
      ⟨m, -, hnat⟩ | hnat3 | halt
    ·
      have hnatU := InternalSec.binaryNaturalSL_of_autSec hK hf hnat
      obtain ⟨F, _, _, hFc, hR⟩ := hnatU
      have h1 := card_eq_card_gam (FFModel.nat_faithful _) hR
      have h2 : Nat.card (FFModel.nat (StatedSL 2 F)).Gam =
          Nat.card F * (Nat.card F ^ 2 - 1) := card_statedSL_two
      rw [h2, hFc, hcK] at h1
      have hmn : m = n := (l2Order_inj h1).symm
      exact Or.inl ⟨hLU, hUel.1, F, inferInstance, inferInstance, hmn ▸ hFc, hR⟩
    · obtain ⟨F, _, _, hFc, hR⟩ := InternalSec.binaryNaturalSL_of_autSec hK hf hnat3
      exact (false_of_natSL_two hcK (Or.inl rfl) (by rw [hFc, pow_one]) hR).elim
    ·
      have haltU := InternalSec.alternatingNatural_of_autSec hK hf halt
      have h1 := card_eq_card_gam (G64.altDn_faithful (by norm_num)) haltU
      change Nat.card ↥(autOn L U) = Nat.card ↥(alternatingGroup (Fin 5)) at h1
      rw [SteinbergCB.nat_card_alternating_five, hcK] at h1
      have hn2 : n = 2 := l2Order_inj (h1.trans (by norm_num))
      have hRV := hext haltU
      have hU := htop (Or.inl ⟨5, Or.inl rfl, rfl, hRV⟩)
      rw [hU] at hRV
      exact Or.inr ⟨1, by omega, hLV, hVel.1,
        OrthFour.binaryOrthogonalFour_one_of_alternatingNatural_five hRV⟩
  · rcases Vol2.Ch10.SecA.table_of_isShapeGroup hF hB ht hsh with ⟨m, hm, hO⟩ | ⟨f, hsz⟩
    · exact Or.inr (horth m hm (InternalSec.binaryOrthogonalFour_of_autSec hK hf hO))
    · exfalso
      obtain ⟨a, ha, hfa, F, _, _, hFc, hR⟩ := InternalSec.binaryNaturalSz_of_autSec hK hf hsz
      have h1 := card_eq_card_gam (FFModel.nat_faithful _) hR
      have h2 : Nat.card (FFModel.nat (suzukiGroup a F)).Gam =
          (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) :=
        CFSG.LieType.Ree.suzuki_order (hfa ▸ hFc)
      rw [h2, hcK] at h1
      exact l2Order_ne_sz (by omega) (by have := h.two_le; omega) h1.symm
  · exact (Vol2.Ch10.SecA.not_part3_of_isShapeGroup hF h3 hsh).elim

end Hyp5_0_1

end CFSG.Quasithin.H13
