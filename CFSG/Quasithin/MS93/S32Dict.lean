module

public import CFSG.Quasithin.MS93.S32Basic
public import CFSG.Quasithin.MS93.M15Quot
public import CFSG.Quasithin.Background.InternalSecB51

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def SQTKQuot : Prop :=
  ∀ (P Q : Type) [Group P] [Group Q] [Finite P] [Finite Q], SQTKGroup P → ∀ f : P →* Q,
    Function.Surjective f → CFSG.IsQuasisimple Q → SQTKGroup Q

structure IsSecW (M L W : Subgroup G) : Prop where
  le_Xq : W ≤ Xq M
  le_normalizer : M ≤ Subgroup.normalizer (W : Set G)
  not_le : ¬ L ≤ Subgroup.centralizer (W : Set G)

variable {M T L W : Subgroup G}

theorem conj_mem_commutator_left' {H K : Subgroup G} {y : G} (hy : y ∈ H) {d : G}
    (hd : d ∈ ⁅H, K⁆) : y * d * y⁻¹ ∈ ⁅H, K⁆ := by
  rw [Subgroup.commutator_def] at hd ⊢
  induction hd using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have e : y * ⁅a, b⁆ * y⁻¹ = ⁅y * a, b⁆ * ⁅y, b⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨y * a, H.mul_mem hy ha, b, hb, rfl⟩)
      (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨y, hy, b, hb, rfl⟩))
  | one => simp
  | mul x z _ _ hx hz =>
    have e : y * (x * z) * y⁻¹ = (y * x * y⁻¹) * (y * z * y⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hz
  | inv x _ hx =>
    have e : y * x⁻¹ * y⁻¹ = (y * x * y⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

namespace IsSecW

variable (hs : IsSecW M L W)
include hs

theorem isElemAbelian [Finite G] (h : PUHyp M T L) : IsElemAbelian 2 W :=
  isElemAbelian_of_le h.isElemAbelian_Xq hs.le_Xq

theorem pCoreOf_le_centralizer : pCoreOf 2 M ≤ Subgroup.centralizer (W : Set G) := by
  rw [← Subgroup.le_centralizer_iff]
  exact hs.le_Xq.trans ((PU.omegaOneCenterOf_le_centerOf _).trans inf_le_right)

theorem L_le_normalizer [Finite G] (h : PUHyp M T L) : L ≤ Subgroup.normalizer (W : Set G) :=
  h.L_le.trans hs.le_normalizer

theorem le_normalizer_kernel :
    M ≤ Subgroup.normalizer ((M ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) : Set G) :=
  le_normalizer_inf Subgroup.le_normalizer (le_normalizer_centralizer hs.le_normalizer)

theorem not_le_kernel : ¬ L ≤ M ⊓ Subgroup.centralizer (W : Set G) :=
  fun hL => hs.not_le (hL.trans inf_le_right)

variable [Finite G] (h : PUHyp M T L)

include h in
theorem mem_pCoreOf_of_mem_centralizer {t : G} (htM : t ∈ M) (ht2 : ∃ e : ℕ, t ^ 2 ^ e = 1)
    (htW : t ∈ Subgroup.centralizer (W : Set G)) : t ∈ pCoreOf 2 M := by
  refine h.mem_pCoreOf_of_rel hs.le_normalizer_kernel hs.not_le_kernel htM ht2 fun l hl => ?_
  have hD : t ∈ M ⊓ Subgroup.centralizer (W : Set G) := ⟨htM, htW⟩
  have hDn := hs.le_normalizer_kernel
  have h1 : l * t⁻¹ * l⁻¹ ∈ M ⊓ Subgroup.centralizer (W : Set G) :=
    (Subgroup.mem_normalizer_iff.mp (hDn (h.L_le hl)) _).mp (Subgroup.inv_mem _ hD)
  have e : ⁅t, l⁆ = t * (l * t⁻¹ * l⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Subgroup.mul_mem _ hD h1

include h in
theorem inf_centralizer_eq : T ⊓ Subgroup.centralizer (W : Set G) = pCoreOf 2 M := by
  refine le_antisymm (fun t ht => ?_) (le_inf h.pCore_le hs.pCoreOf_le_centralizer)
  obtain ⟨e, he⟩ := h.isPGroup ⟨t, ht.1⟩
  exact hs.mem_pCoreOf_of_mem_centralizer h (h.le ht.1)
    ⟨e, by simpa using congrArg Subtype.val he⟩ ht.2

include h in
theorem card_autI_of_le_T {E : Subgroup G} (hET : E ≤ T) :
    Nat.card ↥(autI (hs.isElemAbelian h) E) = (pCoreOf 2 M).relIndex E := by
  rw [card_autI_eq _ (hET.trans (h.le.trans hs.le_normalizer))]
  calc (E ⊓ Subgroup.centralizer (W : Set G)).relIndex E
      = (E ⊓ (T ⊓ Subgroup.centralizer (W : Set G))).relIndex E := by
        rw [← inf_assoc, inf_eq_left.2 hET]
    _ = (pCoreOf 2 M ⊓ E).relIndex E := by rw [hs.inf_centralizer_eq h, inf_comm]
    _ = (pCoreOf 2 M).relIndex E := Subgroup.inf_relIndex_right _ _

section Groups

include h

theorem autI_L_le : autI (hs.isElemAbelian h) L ≤ autI (hs.isElemAbelian h) M :=
  autI_mono _ h.L_le

theorem autI_le_normalizer :
    autI (hs.isElemAbelian h) M ≤
      Subgroup.normalizer (autI (hs.isElemAbelian h) L : Set (MulAut (IntMod W _))) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨InternalSec.autOn_normal_of h.le_normalizer x hx k, fun hk => ?_⟩
  have := InternalSec.autOn_normal_of (U := W) h.le_normalizer x⁻¹
    ((autI (hs.isElemAbelian h) M).inv_mem hx) _ hk
  have this' : x⁻¹ * (x * k * x⁻¹) * x⁻¹⁻¹ ∈ autI (hs.isElemAbelian h) L := this
  have e : x⁻¹ * (x * k * x⁻¹) * x⁻¹⁻¹ = k := by group
  rwa [e] at this'

theorem two : ∀ x ∈ autI (hs.isElemAbelian h) M, ∃ e : ℕ, x ^ 2 ^ e ∈ autI (hs.isElemAbelian h) L :=
  InternalSec.autOn_two_of (hs.L_le_normalizer h) fun y hy => by
    obtain ⟨e, he⟩ := h.exists_pow_mem_L hy
    exact ⟨e, Subgroup.mem_sup_left he⟩

theorem cent : ∀ c ∈ autI (hs.isElemAbelian h) M,
    (∀ k ∈ autI (hs.isElemAbelian h) L, c * k = k * c) → ∀ e : ℕ, c ^ 2 ^ e = 1 → c = 1 := by
  intro c hc hck e he
  set hW := hs.isElemAbelian h
  have hMN := hs.le_normalizer
  rw [← range_convHom hW M hMN] at hc
  obtain ⟨m, rfl⟩ := hc
  obtain ⟨k, hk, f, hf⟩ := exists_pow_isTwoElt (convHom hW M hMN) m he
  rw [← hk]
  set m' := m ^ k
  have hm'Q : (m' : G) ∈ pCoreOf 2 M := by
    refine h.mem_pCoreOf_of_rel hs.le_normalizer_kernel hs.not_le_kernel m'.2
      ⟨f, by simpa using congrArg Subtype.val hf⟩ fun l hl => ?_
    refine ⟨M.mul_mem (M.mul_mem (M.mul_mem m'.2 (h.L_le hl)) (M.inv_mem m'.2))
      (M.inv_mem (h.L_le hl)), ?_⟩
    have hlK : convHom hW M hMN ⟨l, h.L_le hl⟩ ∈ autI hW L :=
      convI_mem_autI hW hl (hMN (h.L_le hl))
    have hcomm : convHom hW M hMN m' * convHom hW M hMN ⟨l, h.L_le hl⟩ =
        convHom hW M hMN ⟨l, h.L_le hl⟩ * convHom hW M hMN m' := by
      rw [hk]
      exact hck _ hlK
    have h1 : convHom hW M hMN ⁅m', ⟨l, h.L_le hl⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm
    have h2 := (convI_eq_one_iff hW _).mp h1
    simpa [commutatorElement_def] using h2
  exact (convI_eq_one_iff hW _).mpr (hs.pCoreOf_le_centralizer hm'Q)

noncomputable def quotHom :
    ↥L ⧸ CFSG.pCore 2 ↥L →* ↥(autI (hs.isElemAbelian h) L) :=
  QuotientGroup.lift (CFSG.pCore 2 ↥L)
    ((convHom (hs.isElemAbelian h) L (hs.L_le_normalizer h)).codRestrict _ fun l => by
      rw [← range_convHom (hs.isElemAbelian h) L (hs.L_le_normalizer h)]
      exact ⟨l, rfl⟩)
    (by
      intro o ho
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      have hoQ : (o : G) ∈ pCoreOf 2 M :=
        pCoreOf_le_pCoreOf_of_le_normalizer h.L_le h.le_normalizer
          (mem_pCoreOf_of_mem_pCore_two ho)
      exact (convI_eq_one_iff _ _).mpr (hs.pCoreOf_le_centralizer hoQ))

theorem quotHom_surjective : Function.Surjective (hs.quotHom h) := by
  rintro ⟨x, hx⟩
  rw [← range_convHom (hs.isElemAbelian h) L (hs.L_le_normalizer h)] at hx
  obtain ⟨l, rfl⟩ := hx
  exact ⟨QuotientGroup.mk l, rfl⟩

theorem quotHom_ne_one : ∃ k, hs.quotHom h k ≠ 1 := by
  by_contra hcon
  push Not at hcon
  apply hs.not_le
  intro l hl
  have h1 := hcon (QuotientGroup.mk ⟨l, hl⟩)
  have h2 : convHom (hs.isElemAbelian h) L (hs.L_le_normalizer h) ⟨l, hl⟩ = 1 :=
    congrArg Subtype.val h1
  exact (convI_eq_one_iff _ _).mp h2

theorem quasisimple : CFSG.IsQuasisimple ↥(autI (hs.isElemAbelian h) L) :=
  CFSG.LieType.CurtisTits.isQuasisimple_of_surjective h.quasisimple (hs.quotHom_surjective h)
    (hs.quotHom_ne_one h)

theorem rankTwo :
    IsRankTwoLie2Derived (↥(autI (hs.isElemAbelian h) L) ⧸
      Subgroup.center ↥(autI (hs.isElemAbelian h) L)) :=
  isRankTwoLie2Derived_of_mulEquiv
    (CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple h.quasisimple
      (hs.quotHom_surjective h)
      (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple h.quasisimple
        (hs.quotHom_ne_one h))) h.rankTwo

theorem sqtk (hSQ : SQTKQuot) : SQTKGroup ↥(autI (hs.isElemAbelian h) L) := by
  have hL : SQTKGroup ↥(L.subgroupOf M) := InternalSec.sqtkGroup_subgroup h.sqtk _
  let f : ↥(L.subgroupOf M) →* ↥(autI (hs.isElemAbelian h) L) :=
    ((hs.quotHom h).comp (QuotientGroup.mk' _)).comp
      (Subgroup.subgroupOfEquivOfLe h.L_le).toMonoidHom
  refine hSQ _ _ hL f ?_ (hs.quasisimple h)
  intro y
  obtain ⟨q, rfl⟩ := hs.quotHom_surjective h y
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨(Subgroup.subgroupOfEquivOfLe h.L_le).symm l, by simp [f]⟩

theorem autI_L_perfect :
    ⁅autI (hs.isElemAbelian h) L, autI (hs.isElemAbelian h) L⁆ = autI (hs.isElemAbelian h) L :=
  Subgroup.isPerfect_iff.mp (hs.quasisimple h).1

theorem commutator_eq_bot_of_le_center {A : Subgroup (MulAut (IntMod W (hs.isElemAbelian h)))}
    (hc : ⁅autI (hs.isElemAbelian h) L, A⁆ ≤
      (Subgroup.center ↥(autI (hs.isElemAbelian h) L)).map (Subgroup.subtype _)) :
    ⁅autI (hs.isElemAbelian h) L, A⁆ = ⊥ := by
  set K := autI (hs.isElemAbelian h) L
  have hcK : ⁅⁅K, A⁆, K⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hc hx
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k, hk⟩)
  have h3 : ⁅⁅K, K⁆, A⁆ ≤ ⊥ := by
    have hbn : ∀ H : Subgroup (MulAut (IntMod W (hs.isElemAbelian h))),
        H ≤ Subgroup.normalizer ((⊥ : Subgroup (MulAut (IntMod W (hs.isElemAbelian h)))) :
          Set (MulAut (IntMod W (hs.isElemAbelian h)))) := fun H x _ => by
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top x
    refine three_subgroups_le (N := ⊥) (hbn _) (hbn _) (hbn _) ?_ ?_
    · rw [hcK]
    · rw [Subgroup.commutator_comm A K, hcK]
  rw [hs.autI_L_perfect h] at h3
  exact le_bot_iff.mp h3

theorem commutator_eq_of_isPGroup {A : Subgroup (MulAut (IntMod W (hs.isElemAbelian h)))}
    (hAX : A ≤ autI (hs.isElemAbelian h) M) (hA : IsPGroup 2 A) (hA1 : A ≠ ⊥) :
    ⁅autI (hs.isElemAbelian h) L, A⁆ = autI (hs.isElemAbelian h) L := by
  set K := autI (hs.isElemAbelian h) L
  have hAK : A ≤ Subgroup.normalizer (K : Set _) := hAX.trans (hs.autI_le_normalizer h)
  have hle : ⁅K, A⁆ ≤ K := Subgroup.le_normalizer_iff_commutator_le_left.mp hAK
  set N : Subgroup ↥K := (⁅K, A⁆).subgroupOf K
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact conj_mem_commutator_left' g.2 hn⟩
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple (hs.quasisimple h) N
    with hc | htop
  · exfalso
    have hc' : ⁅K, A⁆ ≤ (Subgroup.center ↥K).map K.subtype := fun x hx =>
      ⟨⟨x, hle hx⟩, hc (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    have hbot := hs.commutator_eq_bot_of_le_center h hc'
    apply hA1
    rw [eq_bot_iff]
    intro a ha
    obtain ⟨e, he⟩ := hA ⟨a, ha⟩
    refine Subgroup.mem_bot.mpr (hs.cent h a (hAX ha) (fun k hk => ?_) e
      (by simpa using congrArg Subtype.val he))
    have h1 : ⁅k, a⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator hk ha
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  · refine le_antisymm hle fun k hk => ?_
    have : (⟨k, hk⟩ : ↥K) ∈ N := by rw [htop]; exact Subgroup.mem_top _
    exact this

theorem not_isPGroup_autI_L : ¬ IsPGroup 2 ↥(autI (hs.isElemAbelian h) L) := by
  intro hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := hs.quasisimple h
  have : Group.IsPerfect ↥(autI (hs.isElemAbelian h) L) := hq.1
  have : Nontrivial ↥(autI (hs.isElemAbelian h) L) := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hab
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    rw [Subsingleton.elim a' b']
  exact Group.IsPerfect.not_isNilpotent _ hp.isNilpotent

theorem pCoreOf_eq_bot : pCoreOf 2 (autI (hs.isElemAbelian h) M) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := autI (hs.isElemAbelian h) M
  set K := autI (hs.isElemAbelian h) L
  by_contra hP
  have hPX : pCoreOf 2 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hP2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have h1 := hs.commutator_eq_of_isPGroup h hPX hP2 hP
  have h2 : ⁅K, pCoreOf 2 X⁆ ≤ pCoreOf 2 X := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((hs.autI_L_le h).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))
  rw [h1] at h2
  exact hs.not_isPGroup_autI_L h (hP2.to_le h2)

theorem isFFModule {E W' : Subgroup G} (hET : E ≤ T) (hE : IsElemAbelian 2 E)
    (hEQ : ¬ E ≤ pCoreOf 2 M) (hWW' : W ≤ W')
    (hFF : (Subgroup.centralizer (E : Set G)).relIndex W' ≤ (pCoreOf 2 M).relIndex E) :
    IsFFModule (autI (hs.isElemAbelian h) M) := by
  set hW := hs.isElemAbelian h
  have hEN : E ≤ Subgroup.normalizer (W : Set G) := hET.trans (h.le.trans hs.le_normalizer)
  refine ⟨autI hW E, autI_mono _ (hET.trans h.le), fun hbot => hEQ ?_,
    isElemAbelian2_autI hW hE hEN, ?_⟩
  · rw [← hs.inf_centralizer_eq h]
    exact le_inf hET ((autI_eq_bot_iff hW hEN).mp hbot)
  · rw [hs.card_autI_of_le_T h hET, card_fixV_autI hW hEN]
    have hW0 : (Subgroup.centralizer (E : Set G)).relIndex W' ≠ 0 :=
      (Subgroup.index_ne_zero_of_finite :
        ((Subgroup.centralizer (E : Set G)).subgroupOf W').index ≠ 0)
    have hle := Subgroup.relIndex_le_of_le_right hWW' hW0
    have hcard := Subgroup.relIndex_mul_card (Subgroup.centralizer (E : Set G)) W
    have hcardW : Nat.card (IntMod W hW) = Nat.card W := rfl
    rw [hcardW, ← hcard, inf_comm]
    exact Nat.mul_le_mul_right _ (hle.trans hFF)

theorem b51Hyp (hSQ : SQTKQuot) (hFF : IsFFModule (autI (hs.isElemAbelian h) M)) :
    B51Hyp (ffJ (autI (hs.isElemAbelian h) M)) (autI (hs.isElemAbelian h) L) := by
  have : IsMulCommutative ↥W := (hs.isElemAbelian h).1
  obtain ⟨A, hA⟩ := B6.exists_isFFStarOffender hFF
  have hA2 : IsPGroup 2 A := by
    intro a
    refine ⟨1, ?_⟩
    have := hA.2.2.1.2 a.1 a.2
    exact Subtype.ext (by simpa using this)
  exact (InternalSec.b51Hyp_ffJ_autOn (Y := M) hs.le_normalizer h.L_le h.le_normalizer
    (fun y hy => by
      obtain ⟨e, he⟩ := h.exists_pow_mem_L hy
      exact ⟨e, Subgroup.mem_sup_left he⟩)
    (hs.pCoreOf_eq_bot h) (hs.quasisimple h) (hs.sqtk h hSQ) hA
    (hs.commutator_eq_of_isPGroup h hA.1 hA2 hA.2.1)).1

end Groups

end IsSecW

end CFSG.Quasithin.MS93
