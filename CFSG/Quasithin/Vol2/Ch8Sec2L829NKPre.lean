module

public import CFSG.Quasithin.Background.RonanD33
public import CFSG.Quasithin.EmptyFaithful.S153E58B
public import CFSG.Quasithin.Vol2.Ch12Sec2Action
public import CFSG.Quasithin.Vol2.Ch8Sec2D5Inputs
public import CFSG.Quasithin.Vol2.Ch8Sec2L829Coc
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN0
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LNx
public import CFSG.Quasithin.Vol2.Ch8Sec2L829S9Main2

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs
  CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.H13.L829N
open scoped commutatorElement

private theorem nk_le_normalizer_of_commutator_le_asf {G : Type} [Group G] {V Lu : Subgroup G}
    (h : ⁅V, Lu⁆ ≤ V) : Lu ≤ Subgroup.normalizer (V : Set G) := by
  have key : ∀ l ∈ Lu, ∀ x ∈ V, l * x * l⁻¹ ∈ V := by
    intro l hl x hx
    have h1 : ⁅x, l⁆ ∈ V := h (Subgroup.commutator_mem_commutator hx hl)
    have h2 : l * x * l⁻¹ = (⁅x, l⁆)⁻¹ * x := by
      simp only [commutatorElement_def]
      group
    rw [h2]
    exact V.mul_mem (V.inv_mem h1) hx
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key l hl x hx, fun hx => ?_⟩
  have := key l⁻¹ (Lu.inv_mem hl) _ hx
  rwa [show l⁻¹ * (l * x * l⁻¹) * l⁻¹⁻¹ = x by group] at this

private theorem nk_le_normalizer_commutator_asf {G : Type} [Group G] {Λ A B : Subgroup G}
    (hA : Λ ≤ Subgroup.normalizer (A : Set G)) (hB : Λ ≤ Subgroup.normalizer (B : Set G)) :
    Λ ≤ Subgroup.normalizer (⁅A, B⁆ : Subgroup G) := by
  have key : ∀ y ∈ Λ, ∀ g ∈ (⁅A, B⁆ : Subgroup G), y * g * y⁻¹ ∈ (⁅A, B⁆ : Subgroup G) := by
    intro y hy
    have hle : (⁅A, B⁆ : Subgroup G) ≤
        (⁅A, B⁆ : Subgroup G).comap (MulAut.conj y).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_comap]
      show y * ⁅a, b⁆ * y⁻¹ ∈ (⁅A, B⁆ : Subgroup G)
      have e : y * ⁅a, b⁆ * y⁻¹ = ⁅y * a * y⁻¹, y * b * y⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.commutator_mem_commutator
        ((Subgroup.mem_normalizer_iff.mp (hA hy) a).mp ha)
        ((Subgroup.mem_normalizer_iff.mp (hB hy) b).mp hb)
    exact fun g hg => hle hg
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact fun hg => key y hy g hg
  · intro hg
    have e : y⁻¹ * (y * g * y⁻¹) * y⁻¹⁻¹ = g := by group
    have := key y⁻¹ (Λ.inv_mem hy) _ hg
    rwa [e] at this

private theorem nk_conjClosure_normalized_asf {G : Type} [Group G] {V H : Subgroup G} :
    H ≤ Subgroup.normalizer (conjClosure V H : Set G) := by
  have key : ∀ y ∈ H, ∀ g ∈ conjClosure V H, y * g * y⁻¹ ∈ conjClosure V H := by
    intro y hy g hg
    induction hg using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨x, hx, v, hv, rfl⟩ := hs
      exact Subgroup.subset_closure ⟨y * x, H.mul_mem hy hx, v, hv, by group⟩
    | one => simp
    | mul a b _ _ ha hb =>
      rw [show y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) by group]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      rw [show y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ ha
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => key y hy g hg, fun hg => ?_⟩
  have := key y⁻¹ (H.inv_mem hy) _ hg
  rwa [show y⁻¹ * (y * g * y⁻¹) * y⁻¹⁻¹ = g by group] at this

theorem nk_prelude (hmod : StmtFSUModule) (hD4 : StmtD4L3M22) (hS3 : Step828Three)
    (h825 : Stmt8_2_5) (h828 : Stmt8_2_8)
    {G : Type} [Group G] [Finite G] {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I)
    (h731 : Hyp7_3_1 T L I) (h821 : Hyp8_2_1 T L I) [hc : IsMulCommutative ↥(fsuV T I)]
    (hrow : Case8_2 T L I) {H : Subgroup G} {h : G} {k : ℕ}
    (hH : IsHStar T (fsuM T L) H) (hh : h ∈ H) (hC : Concl822 T L I H h k)
    (hrow' : Row711L3Nine T L I 1 ∨ Row711M22Code T L I)
    {K : Subgroup G} (hKc : K ∈ cComp H) :
    K ≤ conjClosure (fsuV T I) H ∧
    ∃ (W₀ W₁ : Subgroup G) (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W)
      (SW : SectionModule (ch82LU L (ch82U (fsuV T I) h) ⊔ H) W₀ W₁ W),
      TransvConfig (SW.img (ch82LU L (ch82U (fsuV T I) h))) (SW.img (conjClosure (fsuV T I) H))
        (SW.img T) (SW.img (fsuV T I)) (SW.sub (fsuV T I ⊓ W₁)) ∧ SW.img K ≠ ⊥ := by
  obtain ⟨hVT, hTV, hVc, hVsq⟩ := asf_V_basic hmod hyp
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hC5 := h825 G T L I hyp h731 h821 hc hrow H h k hH hh hC
  have hC8 := h828 G T L I hyp h731 h821 hc hrow H h k hH hh hC
  have hT : QuasithinUnique.IsSylowTwoOf T H :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hH.1.1
  have hTH : T ≤ H := hT.1
  have hT2 : IsPGroup 2 T := hyp.fsu.sylow.1
  have hHIT : H = ch82I (fsuV T I) h ⊔ T := H_eq_ch82I_sup_T_829 hmod hyp hH hC
  obtain ⟨-, -, -, hL3, hM22, -, -, hTU, hInH, -, -, -, hIU⟩ := id hC5
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hUB, -, -, -⟩ := id hC
  obtain ⟨hNL, -, hLuI, hLuPI, hVLuB⟩ := id hC8
  obtain ⟨hlt, hirr, hmQ, hnonab⟩ := hD4 G T L I hyp h731 h821 hc hrow H h k hH hh hC hrow'
  obtain ⟨-, hL3B, -, hM22B, -, -⟩ := hS3 G T L I hyp h731 h821 hc hrow H h k hH hh hC
  have hIH : ch82I (fsuV T I) h ≤ H := ch82I_le_829 (hVT.trans hTH) hh
  have hHLu : H ≤ Subgroup.normalizer (ch82LU L (ch82U (fsuV T I) h) : Set G) :=
    H_le_normalizer_LU_829 hHIT hIU hTU hNL
  have hLuU : ch82LU L (ch82U (fsuV T I) h) ≤ Subgroup.normalizer (ch82U (fsuV T I) h : Set G) :=
    (perfectCore_le _).trans inf_le_right
  have hHU : H ≤ Subgroup.normalizer (ch82U (fsuV T I) h : Set G) := by
    have : ch82I (fsuV T I) h ⊔ T ≤ Subgroup.normalizer (ch82U (fsuV T I) h : Set G) :=
      sup_le (hIU.trans (Subgroup.centralizer_le_normalizer _)) hTU
    rwa [← hHIT] at this
  have hΛU : ch82LU L (ch82U (fsuV T I) h) ⊔ H ≤
      Subgroup.normalizer (ch82U (fsuV T I) h : Set G) := sup_le hLuU hHU
  have hTΛ : T ≤ ch82LU L (ch82U (fsuV T I) h) ⊔ H := hTH.trans le_sup_right
  have hrkU : rk ↥(ch82U (fsuV T I) h) = 4 := by
    rcases hrow' with h1 | h1
    · exact (hL3 ⟨1, h1⟩).2.2.2
    · exact (hM22 h1).2.2.2
  have hUne : ch82U (fsuV T I) h ≠ ⊥ := by
    intro hU
    rw [hU] at hrkU
    have : rk ↥(⊥ : Subgroup G) = 0 := by simp [rk]
    omega
  have hVp2 : IsPGroup 2 ↥(fsuV T I) := B2F.isPGroup_of_isElemAbelian hV
  have hUV : ch82U (fsuV T I) h ≤ fsuV T I := inf_le_left
  have hVI : fsuV T I ≤ ch82I (fsuV T I) h := le_sup_left
  have hUΛ : ch82U (fsuV T I) h ≤ ch82LU L (ch82U (fsuV T I) h) ⊔ H :=
    (hUV.trans hVI).trans (hIH.trans le_sup_right)
  have hUle : ch82U (fsuV T I) h ≤ pCoreOf 2 (ch82LU L (ch82U (fsuV T I) h) ⊔ H) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUΛ hΛU (hVp2.to_le hUV)
  have hchar : QuasithinUnique.CharTwo (ch82LU L (ch82U (fsuV T I) h) ⊔ H) :=
    charTwo_of_inH' hyp.fsu.qtke hyp.fsu.sylow ⟨hTΛ, fun hb => hUne (le_bot_iff.mp (hb ▸ hUle))⟩
  have hTsylΛ : QuasithinUnique.IsSylowTwoOf T (ch82LU L (ch82U (fsuV T I) h) ⊔ H) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hTΛ
  have hR₀T : pCoreOf 2 (ch82LU L (ch82U (fsuV T I) h) ⊔ H) ≤ T :=
    CFSG.Quasithin.RonanD33.pCoreOf_le_of_sylow hTΛ hT2 hTsylΛ.2.2
  have hIcc : ch82I (fsuV T I) h ≤ conjClosure (fsuV T I) H := by
    refine sup_le (le_conjClosure _ _) ?_
    intro x hx
    rw [B6.mem_conjSub] at hx
    have := mem_conjClosure hh hx
    convert this using 1
    group
  have hHG : H ≤ conjClosure (fsuV T I) H ⊔ T :=
    calc H = ch82I (fsuV T I) h ⊔ T := hHIT
      _ ≤ conjClosure (fsuV T I) H ⊔ T := sup_le_sup_right hIcc T
  have hBV : ch82B (fsuV T I) h ≤ fsuV T I := inf_le_left
  have hLuV : ch82LU L (ch82U (fsuV T I) h) ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    nk_le_normalizer_of_commutator_le_asf (hVLuB.trans hBV)
  have hLuB : ch82LU L (ch82U (fsuV T I) h) ≤ Subgroup.normalizer (ch82B (fsuV T I) h : Set G) :=
    (le_inf hLuV hLuPI).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hBLu : ⁅ch82B (fsuV T I) h, ch82LU L (ch82U (fsuV T I) h)⁆ ≤ ch82B (fsuV T I) h := by
    rw [Subgroup.commutator_le]
    intro b hb l hl
    have h1 : l * b⁻¹ * l⁻¹ ∈ ch82B (fsuV T I) h :=
      (Subgroup.mem_normalizer_iff.mp (hLuB hl) b⁻¹).mp ((ch82B (fsuV T I) h).inv_mem hb)
    have e : ⁅b, l⁆ = b * (l * b⁻¹ * l⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (ch82B (fsuV T I) h).mul_mem hb h1
  have hLuB₁ : ch82LU L (ch82U (fsuV T I) h) ≤ Subgroup.normalizer
      ((⁅ch82B (fsuV T I) h, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔ ch82U (fsuV T I) h : Subgroup G) :
        Set G) :=
    (le_inf (nk_le_normalizer_commutator_asf hLuB Subgroup.le_normalizer) hLuU).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hB₁B : ⁅ch82B (fsuV T I) h, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔ ch82U (fsuV T I) h ≤
      ch82B (fsuV T I) h := sup_le hBLu hUB
  have hR₀H : pCoreOf 2 (ch82LU L (ch82U (fsuV T I) h) ⊔ H) ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hR₀T.trans hTH)
      (le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hIpc : ch82I (fsuV T I) h ⊓ pCoreOf 2 H ≤ pCoreOf 2 (ch82I (fsuV T I) h) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      ((le_inf Subgroup.le_normalizer
        (hIH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_right)
  have hVR : fsuV T I ⊓ pCoreOf 2 (ch82LU L (ch82U (fsuV T I) h) ⊔ H) ≤
      ch82B (fsuV T I) h := fun x hx => ⟨hx.1, hIpc ⟨hVI hx.1, hR₀H hx.2⟩⟩
  have hcard : Nat.card ↥(⁅ch82B (fsuV T I) h, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔
      ch82U (fsuV T I) h) = 16 * Nat.card ↥(ch82U (fsuV T I) h) :=
    asf_card_of_mQuot_eq_four le_sup_right (hB₁B.trans hBV) hVp2 hmQ
  have hBdim : Nat.card ↥(ch82B (fsuV T I) h) ≤ 2 * Nat.card ↥(⁅ch82B (fsuV T I) h,
      ch82LU L (ch82U (fsuV T I) h)⁆ ⊔ ch82U (fsuV T I) h) := by
    rcases hrow' with h1 | h1
    · rw [hL3B 1 h1]
      omega
    · have := hM22B h1
      have h2 := asf_card_eq_relIndex_mul hB₁B
      rw [this] at h2
      omega
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hKperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hKc
  have hKsub : IsSubnormal K H := subnormal_of_mem_cComp hKc
  have hKnot2 : ¬ IsPGroup 2 ↥K := by
    intro hp
    haveI : Group.IsNilpotent ↥K := hp.isNilpotent
    exact not_isSolvable_of_mem_cComp hKc inferInstance
  have hKO : K ≤ oTwoUpper H := by
    have h1 := CFSG.Quasithin.S153E58.oTwoUpper_eq_of_perfect hKperf
    calc K = oTwoUpper K := h1.symm
      _ ≤ oTwoUpper H := Subgroup.closure_mono (fun _ hx => ⟨hKH hx.1, hx.2⟩)
  have hTN : T ≤ Subgroup.normalizer (conjClosure (fsuV T I) H : Set G) :=
    hTH.trans nk_conjClosure_normalized_asf
  have hKG : K ≤ conjClosure (fsuV T I) H := by
    refine hKO.trans ?_
    rw [oTwoUpper, Subgroup.closure_le]
    rintro x ⟨hxH, hxo⟩
    have hx : x ∈ conjClosure (fsuV T I) H ⊔ T := hHG hxH
    exact CFSG.Quasithin.mem_of_mem_sup_of_pow_eq_one hTN hT2 hx hxo (pow_orderOf_eq_one x)
  have hKU : K ≤ Subgroup.centralizer (ch82U (fsuV T I) h : Set G) :=
    hKO.trans (oTwoUpper_le_centralizer_U_829 hT2 hHIT hIU hTU)

  refine ⟨hKG, ?_⟩
  exact s9main_config hchar hHLu hTH hHG hR₀T hVT hTV hVc hVsq hLuV hVLuB hΛU hLuB hLuB₁
    le_sup_right hB₁B hBV hVR hirr hlt hcard hnonab hBdim hKH hKG hKnot2 hKU hKsub

end CFSG.Quasithin.H13.L829NK
