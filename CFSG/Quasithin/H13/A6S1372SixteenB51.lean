module

public import CFSG.Quasithin.H13.A6S1372SixteenTilde
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative commutatorElement

namespace A6B51

theorem card_of_lieModel_psl32 {Y : Type} [Group Y] (h : CFSG.Blueprint.LieModel Y .PSL 3 2 1) :
    Nat.card Y = 168 :=
  CFSG.Blueprint.LieModel.card_psl_three_two h

theorem card_statedSL_three_of_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) = 168 :=
  CFSG.Open.StatedAPI.card_statedSL_three_of_card_eq_two hF

theorem lt_card_statedSL_three {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : 2 ≤ n) : 1080 < Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) := by
  have : Fintype F := Fintype.ofFinite F
  rw [← Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).toEquiv,
    Matrix.card_SL_field, ← Nat.card_eq_fintype_card, hF, Fin.prod_univ_three]
  set q := 2 ^ n with hq
  have hq4 : 4 ≤ q := by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by omega)]
  have h1 : q ^ 2 * (q - 1) ≤ q ^ 3 - 1 := by
    have : q ^ 2 * (q - 1) = q ^ 3 - q ^ 2 := by
      rw [Nat.mul_sub, mul_one, ← pow_succ]
    rw [this]
    have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have h2 : q ^ 2 * (q - 1) ≤ q ^ 3 - q := by
    have : q ^ 2 * (q - 1) = q ^ 3 - q ^ 2 := by
      rw [Nat.mul_sub, mul_one, ← pow_succ]
    rw [this]
    have : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
    omega
  have h3 : q ^ 2 * (q - 1) = q ^ 3 - q ^ 2 := by
    rw [Nat.mul_sub, mul_one, ← pow_succ]
  have hq3 : 3 ≤ q - 1 := by omega
  have hq16 : 16 ≤ q ^ 2 := by nlinarith
  calc (1080 + 1) * (q - 1) ≤ (q ^ 2 * (q - 1)) * (q ^ 2 * (q - 1)) * (q ^ 2 * (q - 1)) := by
        have hA : 48 ≤ q ^ 2 * (q - 1) := by nlinarith
        nlinarith
    _ ≤ (q ^ 3 - 1) * (q ^ 3 - q) * (q ^ 3 - q ^ 2) := by
        rw [← h3]
        exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) le_rfl

theorem card_statedSL_four_two :
    Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) = 20160 :=
  CFSG.Open.StatedAPI.card_statedSL_four_zmod_two

theorem card_statedSL_five_two :
    Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)) = 9999360 :=
  CFSG.Open.StatedAPI.card_statedSL_five_zmod_two

theorem card_eq_of_realizesVia_nat {V : Type} [CommGroup V] [Finite V] {ι F : Type} [Fintype ι]
    [DecidableEq ι] [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)}
    {H : Subgroup (MulAut V)} {U : Subgroup V} {π : (FFModel.nat Γ).Gam →* ↥H}
    (h : (FFModel.nat Γ).RealizesVia H U ⊥ π) : Nat.card ↥Γ = Nat.card ↥H :=
  Nat.card_congr (Equiv.ofBijective π ⟨B42Small.injective_of_realizesVia_nat h, h.1⟩)


theorem comm_eq_of_faithful {V : Type} [CommGroup V] [Finite V] {X K D : Subgroup (MulAut V)}
    (hKq : CFSG.IsQuasisimple ↥K) (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut V)))
    (hfaith : ∀ Y ≤ X, IsPGroup 2 ↥Y → Y ⊓ Subgroup.centralizer (K : Set (MulAut V)) = ⊥)
    (hD : IsFFStarOffender X D) : ⁅K, D⁆ = K := by
  have hDN := hD.1.trans hXN
  have hDnc : ¬ D ≤ Subgroup.centralizer (K : Set (MulAut V)) := by
    intro h
    apply hD.2.1
    rw [eq_bot_iff, ← hfaith D hD.1 hD.2.2.1.isPGroup]
    exact le_inf le_rfl h
  exact FFJImage.commutator_eq_of_not_le_centralizer hKq hDN hDnc

theorem pCoreOf_eq_bot_of_faithful {V : Type} [CommGroup V] [Finite V] {X K J : Subgroup (MulAut V)}
    (hKq : CFSG.IsQuasisimple ↥K) (hKJ : K ≤ J) (hJX : J ≤ X)
    (hJN : J ≤ Subgroup.normalizer (K : Set (MulAut V)))
    (hfaith : ∀ Y ≤ X, IsPGroup 2 ↥Y → Y ⊓ Subgroup.centralizer (K : Set (MulAut V)) = ⊥) :
    pCoreOf 2 J = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 ↥(pCoreOf 2 J) := pCoreOf_isPGroup 2 _
  have hRJ : pCoreOf 2 J ≤ J := pCoreOf_le 2 _
  have hnot : ¬ K ≤ pCoreOf 2 J := by
    intro hle
    have hnil := (hR2.to_le hle).isNilpotent
    have : Group.IsPerfect ↥K := hKq.1
    have : Nontrivial ↥K :=
      (Subgroup.nontrivial_iff_ne_bot _).2 (FFJImage.ne_bot_of_isQuasisimple hKq)
    exact Group.IsPerfect.not_isNilpotent _ hnil
  have hcomm := B1Red.commute_of_normal_not_le (B1Red.isQuasisimple_to_open hKq)
    (fun n hn l hl => (Subgroup.mem_normalizer_iff.mp (hJN (hRJ hn)) l).mp hl)
    (fun l hl n hn => B1Red.conj_mem_pCoreOf (hKJ hl) hn) hnot
  rw [eq_bot_iff, ← hfaith _ (hRJ.trans hJX) hR2]
  exact fun r hr => ⟨hr, Subgroup.mem_centralizer_iff.mpr fun l hl => (hcomm r hr l hl).symm⟩

theorem sq_mem_of_mem_sup {Ω : Type} [Group Ω] {K D : Subgroup Ω}
    (hDN : D ≤ Subgroup.normalizer (K : Set Ω)) (hD2 : ∀ d ∈ D, d ^ 2 = 1) {y : Ω}
    (hy : y ∈ K ⊔ D) : y ^ 2 ∈ K := by
  have hy' : y ∈ ((K ⊔ D : Subgroup Ω) : Set Ω) := hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hDN] at hy'
  obtain ⟨k, hk, d, hd, rfl⟩ := Set.mem_mul.mp hy'
  have hd2 : d * d = 1 := by rw [← pow_two]; exact hD2 d hd
  have e : (k * d) ^ 2 = k * (d * k * d⁻¹) * (d * d) := by
    rw [pow_two]
    group
  rw [e, hd2, mul_one]
  exact Subgroup.mul_mem _ hk ((Subgroup.mem_normalizer_iff.mp (hDN hd) k).mp hk)

theorem genFitting_ffJ_sup_eq {V : Type} [CommGroup V] [Finite V] {X K D : Subgroup (MulAut V)}
    (hKq : CFSG.IsQuasisimple ↥K) (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut V)))
    (hfaith : ∀ Y ≤ X, IsPGroup 2 ↥Y → Y ⊓ Subgroup.centralizer (K : Set (MulAut V)) = ⊥)
    (hD : IsFFStarOffender X D) :
    quasithinGenFitting (ffJ (K ⊔ D)) = K ∧ pCoreOf 2 (ffJ (K ⊔ D)) = ⊥ ∧ K ≤ ffJ (K ⊔ D) := by
  have hKD := comm_eq_of_faithful hKq hXN hfaith hD
  have hDN := hD.1.trans hXN
  have hMN : K ⊔ D ≤ Subgroup.normalizer (K : Set (MulAut V)) :=
    sup_le Subgroup.le_normalizer hDN
  have hDM : IsFFStarOffender (K ⊔ D) D := ⟨le_sup_right, hD.2.1, hD.2.2.1, hD.2.2.2⟩
  have hKG : K ≤ ffJ (K ⊔ D) := B1Red.K_le_ffJ le_sup_left hDM hKD
  have hGM : ffJ (K ⊔ D) ≤ K ⊔ D := B6.ffJ_le (K ⊔ D)
  have hO2 : pCoreOf 2 (ffJ (K ⊔ D)) = ⊥ :=
    pCoreOf_eq_bot_of_faithful hKq hKG (hGM.trans (sup_le hKX hD.1)) (hGM.trans hMN) hfaith
  refine ⟨?_, hO2, hKG⟩
  exact B1Red.quasithinGenFitting_eq_of_two_quot hKG
    (fun y hy l hl => (Subgroup.mem_normalizer_iff.mp (hMN (hGM hy)) l).mp hl)
    (B1Red.isQuasisimple_to_open hKq)
    (fun y hy => sq_mem_of_mem_sup hDN hD.2.2.1.2 (hGM hy)) hO2

theorem b51Hyp_ffJ_sup {V : Type} [CommGroup V] [Finite V] {X K D : Subgroup (MulAut V)}
    (hKq : CFSG.IsQuasisimple ↥K) (hSQK : SQTKGroup ↥K) (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut V)))
    (hfaith : ∀ Y ≤ X, IsPGroup 2 ↥Y → Y ⊓ Subgroup.centralizer (K : Set (MulAut V)) = ⊥)
    (hD : IsFFStarOffender X D) :
    B51Hyp (ffJ (K ⊔ D)) K ∧ ⁅K, D⁆ = K ∧ D ≤ ffJ (K ⊔ D) := by
  obtain ⟨hF, hO2, hKG⟩ := genFitting_ffJ_sup_eq hKq hKX hXN hfaith hD
  have hZ : centerOf (ffJ (K ⊔ D)) ≤ K :=
    (InternalSec.centerOf_le_quasithinGenFitting _).trans hF.le
  have hDM : IsFFStarOffender (K ⊔ D) D := ⟨le_sup_right, hD.2.1, hD.2.2.1, hD.2.2.2⟩
  refine ⟨⟨?_, hKq, hSQK, hKG, hO2, (InternalSec.ffJ_ffJ _).symm⟩,
    comm_eq_of_faithful hKq hXN hfaith hD, B6.le_ffJ hDM⟩
  rw [hF, sup_eq_left.2 hZ]

end A6B51

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

section KTilde

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

namespace Conf

variable [IsMulCommutative ↥(conjClosure S.V3 H)] {C : S.Conf H}
  {B : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))}
  {K : Subgroup G}

omit hab in
theorem KData.nonempty_mulEquiv_quot_tilde (hK : C.KData B K) :
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKc : K ∈ cComp H := hK.2.2.1
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  set κ := (A6Mod.secAct hHU hHV).comp (Subgroup.inclusion hKH) with hκ
  have hr : κ.range = autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) := by
    ext ψ
    rw [MonoidHom.mem_range, A6Mod.mem_autSec_iff hHU hHV hKH]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨_, k.2, rfl⟩
    · rintro ⟨h, hk, rfl⟩
      exact ⟨⟨h, hk⟩, rfl⟩
  have hOK : pCoreOf 2 K ≤ pCoreOf 2 H := A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hKc)
  have hKQ : K ⊓ pCoreOf 2 H ≤ pCoreOf 2 K :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun k hk => F7.mem_normalizer_inf (Subgroup.le_normalizer hk)
        (le_normalizer_pCoreOf 2 H (hKH hk)))
      ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
  have hker : κ.ker = CFSG.pCore 2 ↥K := by
    ext k
    rw [MonoidHom.mem_ker, hκ, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      S.ker_secAct_tilde hNS h13315 h1356two hH]
    constructor
    · intro hk
      have h1 : (k : G) ∈ pCoreOf 2 H := ⟨_, hk, rfl⟩
      obtain ⟨x, hx, hxk⟩ := hKQ ⟨k.2, h1⟩
      rwa [show x = k from Subtype.ext hxk] at hx
    · intro hk
      obtain ⟨x, hx, hxk⟩ := hOK ⟨k, hk, rfl⟩
      rwa [show x = Subgroup.inclusion hKH k from Subtype.ext hxk] at hx
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange κ).trans (MulEquiv.subgroupCongr hr))⟩

omit hab in
theorem KData.card_tilde (hhat : ¬ IsHatA6 L)
    (hNU : ¬ LieModel G .PSU 4 3 1) (hLem : Lem1374One) (h1352 : Stmt13_5_2)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) (hK : C.KData B K)
    (hKU : ¬ K ≤ Subgroup.centralizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G)) :
    Nat.card ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = 60 ∨
      Nat.card ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = 168 ∨
      Nat.card ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = 360 ∨
      Nat.card ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = 1080 := by
  obtain ⟨e⟩ := hK.nonempty_mulEquiv_quot_tilde hNS h13315 h1356two hH
  rw [← Nat.card_congr e.toEquiv]
  rcases hK.list13_5_2 hNS h13315 h1356two hH hab hhat hNU hLem h1352 hKU with
    h5 | h32 | h6 | ⟨-, hZ, h6⟩
  · obtain ⟨e5⟩ := h5
    left
    rw [Nat.card_congr e5.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    rfl
  · exact Or.inr (Or.inl (A6B51.card_of_lieModel_psl32 h32))
  · obtain ⟨e6⟩ := h6
    right; right; left
    rw [Nat.card_congr e6.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    rfl
  · obtain ⟨e6⟩ := h6
    right; right; right
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center _), hZ,
      Nat.card_congr e6.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    rfl


omit hab in
theorem KData.not_commV_tilde_le (hK : C.KData B K) :
    ¬ commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ≤
      fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊔
        (((conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G).subgroupOf
          (conjClosure S.V3 H)).map
          (InternalSec.secMk
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) := by
  intro hle
  have hKc : K ∈ cComp H := hK.2.2.1
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHC := S.le_normalizer_U0 (H := H)
  have hHV := S.le_normalizer_UV1 hH
  have hV1C : (fsuV1 T V).subgroupOf (conjClosure S.V3 H) ≤
      (Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H) :=
    fun x hx => S.V1_le_centralizer_QH hNS h13315 h1356two hH hx
  set p := QuotientGroup.map
    (((fsuV1 T V).subgroupOf (conjClosure S.V3 H)).subgroupOf ⊤)
    (((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)).subgroupOf ⊤)
    (MonoidHom.id _) (fun x hx => hV1C hx) with hp
  have hpmk : ∀ u : ↥(conjClosure S.V3 H),
      p (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u) =
        InternalSec.secMk
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))
            u := fun _ => rfl
  have hpeq : ∀ (h : ↥H)
      (x : Sec (⊤ : Subgroup ↥(conjClosure S.V3 H)) ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))),
      p (A6Mod.secAct hHU hHV h x) = A6Mod.secAct hHU hHC h (p x) := by
    intro h x
    obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective _ x
    rfl
  have hKq : CFSG.IsQuasisimple ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) :=
    B1Red.isQuasisimple_of_open hK.2.2.2.1.2.2
  refine FFJImage.ne_bot_of_isQuasisimple hKq (FFJImage.eq_bot_of_commV_le_fixV hKq.1 ?_)
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨ψ, hψ, v, rfl⟩
  obtain ⟨k, hkK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHC hKH).1 hψ
  obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective _ v
  set x := InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u with hx
  have hk' : A6Mod.secAct hHU hHV k ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) :=
    (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨k, hkK, rfl⟩
  have hmem := hle (Subgroup.subset_closure ⟨_, hk', x, rfl⟩)
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 hmem
  have hpb : p b = 1 := by
    obtain ⟨w, hw, rfl⟩ := hb
    rw [hpmk, A6Mod.secMk_eq_one_iff]
    exact hw.2
  have hpa : p a ∈ fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) := by
    intro φ hφ
    obtain ⟨l, hlK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHC hKH).1 hφ
    rw [← hpeq, ha _ ((A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨l, hlK, rfl⟩)]
  have e : A6Mod.secAct hHU hHC k
      (InternalSec.secMk
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) u) *
      (InternalSec.secMk
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) u)⁻¹ =
      p (A6Mod.secAct hHU hHV k x * x⁻¹) := by
    rw [map_mul, map_inv, hpeq, hx, hpmk]
  rw [e, ← hab, map_mul, hpb, mul_one]
  exact hpa

omit hab in
theorem KData.not_commSub_tilde_le
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) (hK : C.KData B K)
    (hKU : ¬ K ≤ Subgroup.centralizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G)) :
    ¬ commSub
        (((conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G).subgroupOf
        (conjClosure S.V3 H)).map
        (InternalSec.secMk
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ≤
      fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := by
  intro hle
  have hKc : K ∈ cComp H := hK.2.2.1
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  have hF := S.hypF91 hNS h13315 h1356two hH
  set U₀ : Subgroup G := conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)
    with hU₀def
  have hU₀U : U₀ ≤ conjClosure S.V3 H := inf_le_left
  have hKN : K ≤ Subgroup.normalizer (U₀ : Set G) := hKH.trans S.le_normalizer_U0
  have hU₀ab : ∀ x ∈ U₀, ∀ y ∈ U₀, x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hab.1.is_comm.comm ⟨x, hx.1⟩ ⟨y, hy.1⟩)
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hKc
  have hcc : ⁅⁅U₀, K⁆, K⁆ = ⁅U₀, K⁆ := SBd5.commutator_commutator_eq_self hperf hKN hU₀ab
  have hcU : ⁅U₀, K⁆ ≤ U₀ := Subgroup.le_normalizer_iff_commutator_le_left.mp hKN
  set Y : Subgroup G := ((commSub
      (((conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G).subgroupOf
        (conjClosure S.V3 H)).map
        (InternalSec.secMk
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))).comap
      (InternalSec.secMk
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))).map (conjClosure S.V3 H).subtype with hY
  have hle' : ⁅U₀, K⁆ ≤ Y := by
    rw [Subgroup.commutator_le]
    intro u hu k hk
    have hku : k * u⁻¹ * k⁻¹ ∈ U₀ :=
      (Subgroup.mem_normalizer_iff.mp (hKN hk) _).mp (U₀.inv_mem hu)
    have e : ⁅u, k⁆ = u * (k * u⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
    have hcm : ⁅u, k⁆ ∈ conjClosure S.V3 H := by
      rw [e]
      exact (conjClosure S.V3 H).mul_mem (hU₀U hu) (hU₀U hku)
    refine ⟨⟨⁅u, k⁆, hcm⟩, ?_, rfl⟩
    have e2 : InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ⟨⁅u, k⁆, hcm⟩ =
        A6Mod.secAct hHU hHV ⟨k, hKH hk⟩
          (InternalSec.secMk
              ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ⟨u⁻¹, hU₀U (U₀.inv_mem hu)⟩) *
          (InternalSec.secMk
              ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ⟨u⁻¹, hU₀U (U₀.inv_mem hu)⟩)⁻¹ := by
      rw [A6Mod.secAct_secMk, ← map_inv, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe, inv_inv, e]
      exact hU₀ab _ hu _ hku
    rw [SetLike.mem_coe, Subgroup.mem_comap, e2]
    exact Subgroup.subset_closure ⟨_, (A6Mod.mem_autSec_iff hHU hHV hKH).2
      ⟨⟨k, hKH hk⟩, hk, rfl⟩, _, ⟨⟨u⁻¹, hU₀U (U₀.inv_mem hu)⟩, U₀.inv_mem hu, rfl⟩, rfl⟩
  have hV1 : ⁅⁅U₀, K⁆, K⁆ ≤ fsuV1 T V := by
    rw [Subgroup.commutator_le]
    intro y hy k hk
    obtain ⟨z, hz, hzy⟩ := hle' hy
    have hzy' : (z : G) = y := hzy
    have h1 := hle hz _ ((A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨⟨k, hKH hk⟩, hk, rfl⟩)
    rw [A6Mod.secAct_secMk, ← mul_inv_eq_one, ← map_inv, ← map_mul,
      A6Mod.secMk_eq_one_iff] at h1
    have e2 : (((Setup.rho (conjClosure S.V3 H) H hHU ⟨k, hKH hk⟩) z * z⁻¹ :
        ↥(conjClosure S.V3 H)) : G) = (⁅y, k⁆)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe, commutatorElement_def]
      rw [hzy']
      group
    rw [e2] at h1
    simpa using (fsuV1 T V).inv_mem h1
  apply hKU
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm, eq_bot_iff]
  have h1 : ⁅U₀, K⁆ ≤ fsuV1 T V := hcc ▸ hV1
  calc ⁅U₀, K⁆ = ⁅⁅U₀, K⁆, K⁆ := hcc.symm
    _ ≤ ⁅fsuV1 T V, K⁆ := Subgroup.commutator_mono h1 le_rfl
    _ ≤ ⊥ := by
        rw [Subgroup.commutator_le]
        intro v hv k hk
        have hvk := (Subgroup.mem_centralizer_iff.mp (hF.H_le_centralizer (hKH hk))) v hv
        rw [commutatorElement_def, hvk, mul_inv_cancel_right, mul_inv_cancel]
        exact Subgroup.one_mem _


omit hab in
theorem KData.not_irrPlus_tilde
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) (hK : C.KData B K)
    (hKU : ¬ K ≤ Subgroup.centralizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G)) :
    commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ∉
      IrrPlus (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊤ := by
  intro hirr
  have hKc : K ∈ cComp H := hK.2.2.1
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  set Kt := autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) with hKt
  set W0 := ((conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) :
      Subgroup G).subgroupOf (conjClosure S.V3 H)).map
    (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) with hW0
  obtain ⟨-, -, -, hirr'⟩ := mem_irrPlus_top_iff.1 hirr
  have hinv0 : ∀ x ∈ Kt, ∀ w ∈ W0, x w ∈ W0 := by
    intro x hx w hw
    obtain ⟨k, hkK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 hx
    obtain ⟨u, hu, rfl⟩ := hw
    refine ⟨Setup.rho (conjClosure S.V3 H) H hHU k u, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Setup.rho_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp (S.le_normalizer_U0 k.2) _).mp hu
  have hinv1 : ∀ x ∈ Kt, ∀ w ∈ commSub W0 Kt, x w ∈ commSub W0 Kt := by
    intro x hx w hw
    have hle : commSub W0 Kt ≤ (commSub W0 Kt).comap (x : MulAut _).toMonoidHom := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨y, hy, v, hv, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
      have e : x (y v * v⁻¹) = (x * y * x⁻¹) (x v) * (x v)⁻¹ := by
        simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
      rw [e]
      exact Subgroup.subset_closure ⟨_, Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
        (Subgroup.inv_mem _ hx), _, hinv0 x hx v hv, rfl⟩
    exact hle hw
  set J := (commV Kt ⊓ fixV Kt) ⊔ commSub W0 Kt with hJ
  have hJinv : ∀ x ∈ Kt, ∀ w ∈ J, x w ∈ J := by
    intro x hx w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hw
    rw [map_mul]
    refine J.mul_mem (Subgroup.mem_sup_left ⟨?_, ?_⟩) (Subgroup.mem_sup_right (hinv1 x hx b hb))
    · rw [ha.2 x hx]; exact ha.1
    · rw [ha.2 x hx]; exact ha.2
  have hJle : J ≤ commV Kt :=
    sup_le inf_le_left (by rw [commV_eq_commSub]; exact commSub_mono le_top le_rfl)
  rcases hirr' J hJinv le_sup_left hJle with h1 | h1
  · apply hK.not_commSub_tilde_le hNS h13315 h1356two hH hab hKU
    exact (le_sup_right.trans h1.le).trans inf_le_right
  · apply hK.not_commV_tilde_le hNS h13315 h1356two hH
    rw [← h1]
    exact sup_le (inf_le_right.trans le_sup_left)
      ((commSub_le_of_invariant hinv0).trans le_sup_right)

omit hab in
theorem KData.sqtkGroup_tilde (hK : C.KData B K) :
    SQTKGroup ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := by
  have hKH : K ≤ H := le_of_mem_cComp hK.2.2.1
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  have hSQ : SQTKGroup ↥H := sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple
    S.h13.nonabelian hH.1.2
  have hSQX : SQTKGroup ↥(autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := by
    have h1 := InternalSec.sqtkGroup_of_surjective (A6Mod.secAct hHU hHV).rangeRestrict
      (A6Mod.secAct hHU hHV).rangeRestrict_surjective
      (by
        rw [MonoidHom.ker_rangeRestrict, S.ker_secAct_tilde hNS h13315 h1356two hH]
        exact CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥H)) hSQ
    exact S.range_secAct_tilde hH ▸ h1
  exact A6Fifteen.sqtkGroup_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe (autSec_mono (InternalSec.autOn_le_autOn_of_le hKH) _ _))
    (InternalSec.sqtkGroup_subgroup hSQX _)

omit hab in
theorem KData.b51Hyp_tilde (hhat : ¬ IsHatA6 L)
    (hNU : ¬ LieModel G .PSU 4 3 1) (hLem : Lem1374One)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) (hK : C.KData B K)
    {D : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))}
    (hD : IsFFStarOffender (autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) D) :
    B51Hyp (ffJ (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ⊔ D))
        (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ∧
      ⁅autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)), D⁆ =
        autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ∧
      D ≤ ffJ (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ⊔ D) :=
  A6B51.b51Hyp_ffJ_sup (hK.isQuasisimple_tilde hNS h13315 h1356two hH hab hhat hNU hLem)
    (hK.sqtkGroup_tilde hNS h13315 h1356two hH)
    (autSec_mono (InternalSec.autOn_le_autOn_of_le (le_of_mem_cComp hK.2.2.1)) _ _)
    (hK.le_normalizer_tilde hNS h13315 h1356two hH hhat hNU hLem hab)
    (fun _ hY hY2 => hK.inf_centralizer_tilde_eq_bot hNS h13315 h1356two hH hab hhat hNU hLem hY
      hY2) hD


omit hab in
theorem KData.case1ii_tilde (hhat : ¬ IsHatA6 L)
    (hNU : ¬ LieModel G .PSU 4 3 1) (hLem : Lem1374One) (h1352 : Stmt13_5_2) (h51 : AsB51)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) (hK : C.KData B K)
    (hKU : ¬ K ≤ Subgroup.centralizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G))
    {D : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))}
    (hD : IsFFStarOffender (autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) D) :
    B51Case1ii (ffJ (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ⊔ D))
        (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ∧
      Nat.card ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = 168 ∧
      D ≤ ffJ (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ⊔ D) := by
  obtain ⟨hb51, -, hDG⟩ := hK.b51Hyp_tilde hNS h13315 h1356two hH hhat hNU hLem hab hD
  have hV' : ∀ v : ↥(conjClosure S.V3 H), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hab.2 v v.2)
  have hV := Bridge.sec_sq_eq_one hV' (⊤ : Subgroup ↥(conjClosure S.V3 H))
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
  obtain ⟨⟨-, hcases⟩, -⟩ := h51 _ hV _ _ hb51
  have hcard := hK.card_tilde hNS h13315 h1356two hH hhat hNU hLem h1352 hab hKU
  rcases hcases with h1 | h2 | ⟨n, h3⟩ | h4
  · exact absurd h1.1 (hK.not_irrPlus_tilde hNS h13315 h1356two hH hab hKU)
  · refine ⟨h2, ?_, hDG⟩
    obtain ⟨-, n, F, _, _, hF, I, π, -, -, hR, -, -⟩ := h2
    have hc := A6B51.card_eq_of_realizesVia_nat (hR 0)
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have hn1 : n = 1 := by
        have h1 : 1 < Nat.card F := Finite.one_lt_card
        rw [hF] at h1
        rcases n with _ | _ | n
        · simp at h1
        · rfl
        · omega
      subst hn1
      rw [← hc]
      exact A6B51.card_statedSL_three_of_two (by rw [hF]; norm_num)
    · have h1 := A6B51.lt_card_statedSL_three hF hn
      rw [hc] at h1
      omega
  · exfalso
    obtain ⟨-, hn45, π, U₁, U₂, -, hR1, -⟩ := h3
    have hc := A6B51.card_eq_of_realizesVia_nat hR1
    rcases hn45 with rfl | rfl
    · rw [A6B51.card_statedSL_four_two] at hc
      omega
    · rw [A6B51.card_statedSL_five_two] at hc
      omega
  · exfalso
    obtain ⟨-, n, hn45, k, hk1, -, I, π, -, -, -, hR⟩ := h4
    have hc := A6B51.card_eq_of_realizesVia_nat (hR ⟨0, hk1⟩)
    rcases hn45 with rfl | rfl
    · rw [A6B51.card_statedSL_four_two] at hc
      omega
    · rw [A6B51.card_statedSL_five_two] at hc
      omega

end Conf

end KTilde

end Setting4

end CFSG.Quasithin.H13.A6
