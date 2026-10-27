module

public import CFSG.Quasithin.H13.L32ACPGL1
public import CFSG.Quasithin.EmptyFaithful.LRed3Bridge
public import CFSG.Quasithin.Vol2.Ch5Sec1L34B45Swap
public import CFSG.Quasithin.H13.L32AC44a
public import CFSG.Quasithin.H13.L32ACSk12
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

theorem exists_injective_factor {A B C : Type*} [Group A] [Group B] [Group C] (π : A →* B)
    (hπ : Function.Surjective π) (hB : CFSG.IsQuasisimple B) (hZ : Subgroup.center B = ⊥)
    (κ : A →* C) (hker : π.ker ≤ κ.ker) (hne : ∃ a, κ a ≠ 1) :
    ∃ θ : B →* C, Function.Injective θ ∧ ∀ a, θ (π a) = κ a := by
  let e := QuotientGroup.quotientKerEquivOfSurjective π hπ
  let θ : B →* C := (QuotientGroup.lift π.ker κ hker).comp e.symm.toMonoidHom
  have hθ : ∀ a, θ (π a) = κ a := by
    intro a
    have h1 : e.symm (π a) = (a : A ⧸ π.ker) := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    show QuotientGroup.lift π.ker κ hker (e.symm (π a)) = κ a
    rw [h1]
    rfl
  refine ⟨θ, ?_, hθ⟩
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hB θ.ker with h | h
  · rw [hZ] at h
    exact le_bot_iff.mp h
  · exfalso
    obtain ⟨a, ha⟩ := hne
    apply ha
    rw [← hθ a]
    exact MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top (π a))

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

omit [Finite G] in
theorem exists_kb_lift {X : Type*} [Group X] {K : Subgroup G} (hKH : K ≤ H)
    (hq : CFSG.IsQuasisimple ↥(modO2Image H K)) (hZ : Subgroup.center ↥(modO2Image H K) = ⊥)
    (κ : ↥K →* X) (hker : ∀ k : ↥K, (k : G) ∈ pCoreOf 2 H → κ k = 1) (hne : ∃ k, κ k ≠ 1) :
    ∃ θ : ↥(modO2Image H K) →* X, Function.Injective θ ∧
      ∀ k : ↥K, θ ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨k, hKH k.2⟩,
        mem_modO2Image'.mpr ⟨_, k.2, rfl⟩⟩ = κ k := by
  let π : ↥K →* ↥(modO2Image H K) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hKH)).codRestrict _
      fun k => mem_modO2Image'.mpr ⟨_, k.2, rfl⟩
  have hπ : Function.Surjective π := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := mem_modO2Image'.mp hy
    exact ⟨⟨a, ha⟩, rfl⟩
  have hk : π.ker ≤ κ.ker := by
    intro k hk1
    rw [MonoidHom.mem_ker] at hk1 ⊢
    refine hker k ((mk_pCore_eq_one_iff (⟨k, hKH k.2⟩ : ↥H)).mp ?_)
    exact congrArg Subtype.val hk1
  obtain ⟨θ, hθi, hθ⟩ := exists_injective_factor π hπ hq hZ κ hk hne
  exact ⟨θ, hθi, hθ⟩

theorem center_eq_bot_of_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hZ : Subgroup.center X = ⊥) : Subgroup.center Y = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h1 : e.symm z ∈ Subgroup.center X :=
    (Subgroup.centerCongr e.symm).toEquiv.toFun ⟨z, hz⟩ |>.2
  rw [hZ, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot, ← e.apply_symm_apply z, h1, map_one]

theorem card_eq_of_isPSL34 {X : Type} [Group X] (hX : IsPSL 3 2 2 X) : Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four hX

section Generic

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem exists_secAct {J : Type*} [Group J] {Y Lq : Subgroup (MulAut W)} {Vs : Subgroup W}
    {C : Subgroup ↥Vs} (hY : Y ≤ stabSub Vs) (hYC : autSub Y Vs ≤ stabSub C) (hLY : Lq ≤ Y)
    (φ : J →* MulAut W) {J₀ : Subgroup J} (hφ : ∀ j ∈ J₀, φ j ∈ Y) :
    ∃ κ : ↥J₀ →* MulAut (Sec (⊤ : Subgroup ↥Vs) C),
      (∀ j, κ j ∈ autSec (autSub Y Vs) ⊤ C) ∧
      (∀ j : ↥J₀, φ j ∈ Lq → κ j ∈ autSec (autSub Lq Vs) ⊤ C) ∧
      (∀ j : ↥J₀, φ j = 1 → κ j = 1) ∧
      ∀ l ∈ autSec (autSub Lq Vs) ⊤ C, ∃ y ∈ Lq, ∀ j : ↥J₀, φ j = y → κ j = l := by
  have hXt : autSub Y Vs ≤ stabSub (⊤ : Subgroup ↥Vs) := InternalSec.le_stabSub_top _
  let ψ : ↥J₀ →* ↥(autSub Y Vs) :=
    ((resHom Vs).comp ((φ.comp J₀.subtype).codRestrict (stabSub Vs) fun j =>
      hY (hφ j j.2))).codRestrict _ fun j => mem_autSub.mpr ⟨_, hφ j j.2, rfl⟩
  have hLX : autSub Lq Vs ≤ autSub Y Vs := autSub_mono hLY Vs
  refine ⟨(B5.secHom (autSub Y Vs) hXt hYC).comp ψ, fun j => ?_, fun j hj => ?_,
    fun j hj => ?_, fun l hl => ?_⟩
  · rw [← B5.range_secHom (autSub Y Vs) hXt hYC]
    exact ⟨ψ j, rfl⟩
  · rw [← B5.map_secHom_eq_autSec (autSub Y Vs) hXt hYC hLX]
    exact ⟨ψ j, Subgroup.mem_subgroupOf.mpr (mem_autSub.mpr ⟨_, hj, rfl⟩), rfl⟩
  · have h1 : ψ j = 1 := by
      apply Subtype.ext
      show resHom Vs ⟨φ j, _⟩ = 1
      rw [← map_one (resHom Vs)]
      congr 1
      exact Subtype.ext hj
    show B5.secHom (autSub Y Vs) hXt hYC (ψ j) = 1
    rw [h1, map_one]
  · rw [← B5.map_secHom_eq_autSec (autSub Y Vs) hXt hYC hLX] at hl
    obtain ⟨x, hx, rfl⟩ := hl
    obtain ⟨y, hyL, hyx⟩ := mem_autSub.mp (Subgroup.mem_subgroupOf.mp hx)
    refine ⟨y, hyL, fun j hj => ?_⟩
    show B5.secHom (autSub Y Vs) hXt hYC (ψ j) = _
    congr 1
    apply Subtype.ext
    show resHom Vs ⟨φ j, _⟩ = (x : MulAut ↥Vs)
    rw [← hyx]
    congr 1
    exact Subtype.ext hj

theorem false_of_d310Two_psl34 {T Lq : Subgroup (MulAut W)} {U : Subgroup W}
    (h : D310Two T Lq U) {X : Type} [Group X] [Finite X] (hX : IsPSL 3 2 2 X)
    (hZX : Subgroup.center X = ⊥) (θ : X →* MulAut W) (hθi : Function.Injective θ)
    (hθr : θ.range = Lq) : False := by
  let e : X ≃* ↥Lq := (MonoidHom.ofInjective hθi).trans (MulEquiv.subgroupCongr hθr)
  have hZL : Subgroup.center ↥Lq = ⊥ := center_eq_bot_of_equiv e hZX
  have hPL : IsPSL 3 2 2 (↥Lq ⧸ Subgroup.center ↥Lq) :=
    isPSL_congr (e.trans ((QuotientGroup.quotientMulEquivOfEq hZL).trans
      QuotientGroup.quotientBot).symm) hX
  have hc : Nat.card ↥Lq = 1 * 20160 := by
    rw [one_mul, ← card_eq_of_isPSL34 hX]
    exact (Nat.card_congr e.toEquiv).symm
  have hzc : Nat.card (Subgroup.center ↥Lq) = 1 := by rw [hZL, Subgroup.card_bot]
  obtain ⟨h13, -⟩ := d310Two_psl34 h (by decide) hc hzc hPL
  omega

theorem map_eq_of_qhatOf_le_two
    (hW2 : ∀ v : W, v ^ 2 = 1) {G₁ L₁ : Subgroup (MulAut W)}
    (hHyp : B4Hyp G₁ L₁) (hq : qhatOf G₁ ≤ ((2 : ℚ) : WithTop ℚ)) {X : Type} [Group X]
    [Finite X] (hX : IsPSL 3 2 2 X) (hZX : Subgroup.center X = ⊥) (θ : X →* MulAut W)
    (hθi : Function.Injective θ) (hθr : θ.range = L₁) {S Q : Subgroup X}
    (hS : IsSylowTwoOf S ⊤) (hQS : Q ≤ S) (hQe : IsElemAbelian 2 Q) (hQc : Nat.card Q = 16)
    (α : MulAut X) (hαS : S.map α.toMonoidHom = S) {g : MulAut W} (hg : g ∈ G₁)
    (hgθ : ∀ y, θ (α y) = g * θ y * g⁻¹) : Q.map α.toMonoidHom = Q := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun σ : MulAut W => (σ : W → W)) DFunLike.coe_injective
  let e : X ≃* ↥L₁ := (MonoidHom.ofInjective hθi).trans (MulEquiv.subgroupCongr hθr)
  have hZL : Subgroup.center ↥L₁ = ⊥ := center_eq_bot_of_equiv e hZX
  have hmodel : IsPSL 3 2 2 (↥L₁ ⧸ Subgroup.center ↥L₁) :=
    isPSL_congr (e.trans ((QuotientGroup.quotientMulEquivOfEq hZL).trans
      QuotientGroup.quotientBot).symm) hX
  have hS'L : IsSylowTwoOf (S.map θ) L₁ := by
    refine ⟨?_, hS.2.1.map θ, ?_⟩
    · rw [← hθr]
      exact Subgroup.map_le_range θ S
    · have h1 := Subgroup.relIndex_map_map_of_injective S ⊤ hθi
      rw [← MonoidHom.range_eq_map, hθr] at h1
      change ¬ 2 ∣ (S.map θ).relIndex _
      rw [h1]
      exact hS.2.2
  have hgS : g ∈ Subgroup.normalizer ((S.map θ : Subgroup (MulAut W)) : Set (MulAut W)) := by
    refine Subgroup.mem_normalizer_fintype fun s hs => ?_
    obtain ⟨y, hy, rfl⟩ := hs
    rw [← hgθ]
    refine ⟨α y, ?_, rfl⟩
    rw [← hαS]
    exact ⟨y, hy, rfl⟩
  have hQ'e : IsElemAbelian 2 (Q.map θ) := by
    have := hQe.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← map_mul, ← map_mul]
      exact congrArg θ (congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : Q) ⟨y, hy⟩))
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hQe.2 x hx, map_one]
  have hQ'c : Nat.card (Q.map θ) = 16 := by
    rw [Subgroup.card_map_of_injective hθi, hQc]
  have hQn := B45L34.mem_normalizer_of_qhatOf_le_two hW2 hHyp hZL hmodel hq hS'L
    (Subgroup.map_mono hQS) hQ'e hQ'c hg hgS
  have hle : Q.map α.toMonoidHom ≤ Q := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : g * θ x * g⁻¹ ∈ Q.map θ :=
      (Subgroup.mem_normalizer_iff.mp hQn (θ x)).mp ⟨x, hx, rfl⟩
    rw [← hgθ] at h1
    obtain ⟨q, hq', hqx⟩ := h1
    show α x ∈ Q
    rw [← hθi hqx]
    exact hq'
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective).ge

theorem map_eq_of_sec
    (hexp : ∀ w : W, w ^ 2 = 1) {Y Lq : Subgroup (MulAut W)}
    {Vs : Subgroup W} {C : Subgroup ↥Vs} (hY : Y ≤ stabSub Vs) (hYC : autSub Y Vs ≤ stabSub C)
    (hLY : Lq ≤ Y) (hb4 : B4Hyp (autSec (autSub Y Vs) ⊤ C) (autSec (autSub Lq Vs) ⊤ C))
    (hqh : qhatOf (autSec (autSub Y Vs) ⊤ C) ≤ ((2 : ℚ) : WithTop ℚ)) {J X : Type} [Group J]
    [Group X] [Finite X] (hX : IsPSL 3 2 2 X) (hZX : Subgroup.center X = ⊥)
    (hXq : CFSG.IsQuasisimple X) (φ : J →* MulAut W) {J₀ K' : Subgroup J}
    (hφ : ∀ j ∈ J₀, φ j ∈ Y) (hKJ : K' ≤ J₀) (hK'L : ∀ k ∈ K', φ k ∈ Lq)
    (hK's : ∀ y ∈ Lq, ∃ k ∈ K', φ k = y) (π : ↥K' →* X) (hπ : Function.Surjective π)
    (hker : ∀ k : ↥K', π k = 1 → φ k = 1) (α : MulAut X) {t : J} (htJ : t ∈ J₀)
    (htK : ∀ k : ↥K', t * k * t⁻¹ ∈ K')
    (hα : ∀ k : ↥K', π ⟨t * k * t⁻¹, htK k⟩ = α (π k)) {S Q : Subgroup X}
    (hS : IsSylowTwoOf S ⊤) (hQS : Q ≤ S) (hQe : IsElemAbelian 2 Q) (hQc : Nat.card Q = 16)
    (hαS : S.map α.toMonoidHom = S) : Q.map α.toMonoidHom = Q := by
  obtain ⟨κ, hκG, hκL, hκ1, hκs⟩ := exists_secAct hY hYC hLY φ hφ
  let incl : ↥K' →* ↥J₀ := Subgroup.inclusion hKJ
  have hne : ∃ k, (κ.comp incl) k ≠ 1 := by
    have := CFSG.LocalCores.isQuasisimple_nontrivial hb4.2.2.1
    obtain ⟨l, hl1⟩ := exists_ne (1 : ↥(autSec (autSub Lq Vs) ⊤ C))
    obtain ⟨y, hyL, hy⟩ := hκs l l.2
    obtain ⟨k, hk, rfl⟩ := hK's y hyL
    exact ⟨⟨k, hk⟩, fun h1 => hl1 (Subtype.ext ((hy (incl ⟨k, hk⟩) rfl).symm.trans h1))⟩
  have hkerκ : π.ker ≤ (κ.comp incl).ker := fun k hk =>
    hκ1 (incl k) (hker k (MonoidHom.mem_ker.mp hk))
  obtain ⟨θ, hθi, hθ⟩ := exists_injective_factor π hπ hXq hZX (κ.comp incl) hkerκ hne
  have hθr : θ.range = autSec (autSub Lq Vs) ⊤ C := by
    ext l
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨k, rfl⟩ := hπ x
      rw [hθ k]
      exact hκL _ (hK'L k k.2)
    · intro hl
      obtain ⟨y, hyL, hy⟩ := hκs l hl
      obtain ⟨k, hk, rfl⟩ := hK's y hyL
      exact ⟨π ⟨k, hk⟩, (hθ _).trans (hy (incl ⟨k, hk⟩) rfl)⟩
  have hW2 : ∀ v : Sec (⊤ : Subgroup ↥Vs) C, v ^ 2 = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H w =>
      rw [← QuotientGroup.mk_pow, show w ^ 2 = 1 from Subtype.ext (Subtype.ext (hexp _)),
        QuotientGroup.mk_one]
  have hgθ : ∀ x : X, θ (α x) = κ ⟨t, htJ⟩ * θ x * (κ ⟨t, htJ⟩)⁻¹ := by
    intro x
    obtain ⟨k, rfl⟩ := hπ x
    have h2 : incl ⟨t * k * t⁻¹, htK k⟩ = ⟨t, htJ⟩ * incl k * (⟨t, htJ⟩)⁻¹ := rfl
    rw [← hα, hθ, hθ, MonoidHom.comp_apply, MonoidHom.comp_apply, h2, map_mul, map_mul, map_inv]
  exact map_eq_of_qhatOf_le_two hW2 hb4 hqh hX hZX θ hθi hθr hS hQS hQe hQc α hαS (hκG _) hgθ

end Generic

attribute [local instance] commGroupOfFact

theorem lemma14741PGL_of_inputs
    (h310 : D310) (hA21 : AsA21SQTKSection) (hN1 : LieSylowOver3)
    (h29 : Thm14_7_29) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h30 : Lemma14_7_30) (h32 : Lemma14_7_32) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) :
    Lemma14741PGL := by
  intro G _ _ T L V H S K hK hHeq n hn hLie hl1K hO hP
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hq, -, -, hF918⟩ := h30 G T L V H S K hK
  have hTK := h32 G T L V H S K hK
  have hKn := le_normalizer_of_setting hA37 hA38 S hK hTK
  have hTH : T ≤ H := Setting147.TH' S
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hK₀ : conjClosure K T = K := conjClosure_T_eq_self (hTH.trans hKn)
  have hHeq' : conjClosure K T ⊔ (l1 T L V ⊔ T) = H := by
    rw [hK₀]
    exact hHeq.symm
  rw [hHeq'] at hF918
  have hKbN : (modO2Image H K).Normal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKn).map _
      (QuotientGroup.mk'_surjective _)
  obtain ⟨t, htT, Q, hQS, hQe, hQc, hQt⟩ :=
    exists_t_move hN1 h29 h1222 h1332 h1334 S hK hq hKn hHeq hn hLie hl1K hO hP
  have hZ := center_kb_eq_bot_of_oddCore hK hq hKn hLie hO
  have hPK := isPSL_kb hK hP hZ
  obtain ⟨hqX, -, -⟩ := kst_props hK hq hLie
  have hcardK : Nat.card ↥(modO2Image H K) = 20160 := by
    obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hPK
    rw [Nat.card_congr e.toEquiv, card_psl34 hF]
  have hH : SQTKGroup ↥H := sqtkGroup_of_setting S
  obtain ⟨I, hV₁I, hIU, W, hW, hirr⟩ := exists_isIrrPlusTildeU hF918
  have hFI := factElem hF918 hIU
  have hirr' : subM (fsuV1 T V) (conjClosure I H) I ∈
      IrrPlusOn (autIH (fsuV1 T V) I H (conjClosure K T))
        (orbSup (autIH (fsuV1 T V) I H T) (subM (fsuV1 T V) (conjClosure I H) I))
        (autIH (fsuV1 T V) I H T) := isIrrPlusTildeT_of_ambient hF918 hIU W hW hirr
  have hnt := hnt_of_irrSec hF918 hIU hirr'.1.2.2.2.1
  have hD := d31_of_hyp hF918 hH hIU hV₁I hirr'
  have hKI := K₀_le_normalizer_of_isInv hF918 hIU hV₁I hirr'.1.2.1
  obtain ⟨B, hA⟩ := qOff_of_hyp hF918 hIU hV₁I hKI hnt
  have hKne := map_K_ne_bot hF918 hIU hnt
  rw [hK₀] at hD hA hirr'
  have hD3 : D3Std (autIH (fsuV1 T V) I H H) (autIH (fsuV1 T V) I H K)
      (autIH (fsuV1 T V) I H T) (autIH (fsuV1 T V) I H K)
      (subM (fsuV1 T V) (conjClosure I H) I) :=
    ⟨hD, hA.qhat_VT hD.exp, hirr'⟩
  have hqM := hA.qhat_M hD.sylow.1
  set φ := actH hF918.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) with hφ
  have hφK : ∀ k : ↥K, φ (Subgroup.inclusion hKH k) ∈ autIH (fsuV1 T V) I H K := by
    intro k
    rw [autIH_eq_map hF918 hKH]
    exact ⟨_, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
  have hφT : ∀ x : ↥H, (x : G) ∈ T → φ x ∈ autIH (fsuV1 T V) I H T := by
    intro x hx
    rw [autIH_eq_map hF918 hTH]
    exact ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hφO : ∀ x : ↥H, (x : G) ∈ pCoreOf 2 H → φ x = 1 := fun x hx =>
    hF918.actH_eq_one_of_mem_pCoreOf hIU hx
  rcases h310 _ _ _ _ _ _ hD3 rfl hqM with hT | h2
  swap
  ·
    have hne : ∃ k : ↥K, toAutI hF918 I k ≠ 1 := by
      by_contra hcon
      push Not at hcon
      apply hKne
      rw [eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_bot]
      exact (toAutI_eq_one_iff hF918 I ⟨x, Subgroup.mem_subgroupOf.mp hx⟩).mp (hcon _)
    obtain ⟨θ, hθi, hθ⟩ := exists_kb_lift hKH hqX hZ (toAutI hF918 I)
      (fun k hk => (toAutI_eq_one_iff hF918 I k).mpr (hφO _ hk)) hne
    refine false_of_d310Two_psl34 h2 hPK hZ ((autIH (fsuV1 T V) I H K).subtype.comp θ)
      ((autIH (fsuV1 T V) I H K).subtype_injective.comp hθi) ?_
    ext l
    constructor
    · rintro ⟨y, rfl⟩
      exact (θ y).2
    · intro hl
      obtain ⟨k, hk⟩ := toAutI_surjective hF918 I ⟨l, hl⟩
      exact ⟨_, by rw [MonoidHom.comp_apply, hθ k, hk]; rfl⟩
  have hTs : autIH (fsuV1 T V) I H T ≤ stabSub (subM (fsuV1 T V) (conjClosure I H) I) :=
    fun x hx => hT x hx
  have hMs := insp5a_le_stabSub hD
  have hO2 := lred3_pCoreOf_autSub_sup_eq_bot hD hTs
  have hQ := lred3_qsec hD rfl hO2
  have hb4 := lred3_b4Hyp hA21 hD rfl hO2
  have hqh := lred3_qhatOf_autSec hD3 rfl hTs
  have hJφ : ∀ j ∈ K.subgroupOf H ⊔ T.subgroupOf H,
      φ j ∈ autIH (fsuV1 T V) I H K ⊔ autIH (fsuV1 T V) I H T := by
    intro j hj
    rw [autIH_eq_map hF918 hKH, autIH_eq_map hF918 hTH, ← Subgroup.map_sup]
    exact ⟨j, hj, rfl⟩
  have hK'L : ∀ k ∈ K.subgroupOf H, φ k ∈ autIH (fsuV1 T V) I H K := by
    intro k hk
    rw [autIH_eq_map hF918 hKH]
    exact ⟨k, hk, rfl⟩
  have hK's : ∀ y ∈ autIH (fsuV1 T V) I H K, ∃ k ∈ K.subgroupOf H, φ k = y := by
    intro y hy
    rw [autIH_eq_map hF918 hKH] at hy
    exact hy
  let π : ↥(K.subgroupOf H) →* ↥(modO2Image H K) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (K.subgroupOf H).subtype).codRestrict _
      fun k => mem_modO2Image'.mpr ⟨k, k.2, rfl⟩
  have hπ : Function.Surjective π := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := mem_modO2Image'.mp hy
    exact ⟨⟨a, ha⟩, rfl⟩
  have hker : ∀ k : ↥(K.subgroupOf H), π k = 1 → φ k = 1 := by
    intro k hk
    exact hφO _ ((mk_pCore_eq_one_iff (k : ↥H)).mp (congrArg Subtype.val hk))
  have htK : ∀ k : ↥(K.subgroupOf H), t * k * t⁻¹ ∈ K.subgroupOf H := fun k =>
    Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp (hKn t.2) _).mp k.2)
  have hα : ∀ k : ↥(K.subgroupOf H), π ⟨t * k * t⁻¹, htK k⟩ =
      (MulAut.conjNormal (QuotientGroup.mk' (CFSG.pCore 2 ↥H) t) : MulAut ↥(modO2Image H K))
        (π k) := by
    intro k
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    show QuotientGroup.mk' (CFSG.pCore 2 ↥H) (t * k * t⁻¹) = _
    rw [map_mul, map_mul, map_inv]
    rfl
  have htS1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) t ∈
      Subgroup.normalizer (szS1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    have htT' : QuotientGroup.mk' (CFSG.pCore 2 ↥H) t ∈ modO2Image H T :=
      mem_modO2Image'.mpr ⟨t, htT, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun s hs => ?_
    exact ⟨(modO2Image H T).mul_mem ((modO2Image H T).mul_mem htT' hs.1)
      ((modO2Image H T).inv_mem htT'), hKbN.conj_mem _ hs.2 _⟩
  exact hQt (map_eq_of_sec hD.exp (sup_le hMs hTs) hQ.stab le_sup_left hb4 hqh hPK hZ hqX φ hJφ
    le_sup_left hK'L hK's π hπ hker _ (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr htT))
    htK hα (isSylowTwoOf_subgroupOf (isSylowIn_szS1_of S hK)) hQS hQe hQc
    (map_conjNormal_szS1 htS1))

end CFSG.Quasithin.H13.L32A.C
