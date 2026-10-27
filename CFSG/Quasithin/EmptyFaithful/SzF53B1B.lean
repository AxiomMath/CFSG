module

public import CFSG.Quasithin.EmptyFaithful.SzF53B1A
public import CFSG.Quasithin.Recognition.F112WLocal2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace F53B1

section Hyp

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace B1Hyp

theorem normal_of_centralized (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H)
    {X : Subgroup G} (hQ : pCoreOf 2 M ≤ Subgroup.normalizer (X : Set G))
    (hZ : VZ S H ≤ Subgroup.centralizer (X : Set G))
    (hZ2 : conjSub x (VZ S H) ≤ Subgroup.centralizer (X : Set G)) :
    M ≤ Subgroup.normalizer (X : Set G) ∧ oTwoUpper M ≤ Subgroup.centralizer (X : Set G) := by
  have hD : VZ S H ⊔ conjSub x (VZ S H) ≤ Subgroup.centralizer (X : Set G) := sup_le hZ hZ2
  exact ⟨(h.M_eq_Qb_sup_D hx hxH).le.trans
      (sup_le hQ (hD.trans (Subgroup.centralizer_le_normalizer _))),
    (h.oTwoUpper_M_le_D hx hxH).trans hD⟩

theorem normal_Za_inf_Qa2 (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    M ≤ Subgroup.normalizer ((VZ S H ⊓ conjSub x (pCoreOf 2 H) : Subgroup G) : Set G) ∧
      oTwoUpper M ≤
        Subgroup.centralizer ((VZ S H ⊓ conjSub x (pCoreOf 2 H) : Subgroup G) : Set G) := by
  refine h.normal_of_centralized hx hxH
    (F7.le_normalizer_inf h.Qb_le_normalizer_Za (h.Qb_le_normalizer_Qa2 hx)) ?_ ?_
  · intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact F7.isElemAbelian_comm h.zfacts.elemAbelian hy.1 hg
  · intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp (h.Za2_le_centralizer_Qa2 x hg) y hy.2

theorem normal_Za2_inf_Qa (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    M ≤ Subgroup.normalizer ((conjSub x (VZ S H) ⊓ pCoreOf 2 H : Subgroup G) : Set G) ∧
      oTwoUpper M ≤
        Subgroup.centralizer ((conjSub x (VZ S H) ⊓ pCoreOf 2 H : Subgroup G) : Set G) := by
  refine h.normal_of_centralized hx hxH
    (F7.le_normalizer_inf (h.Qb_le_normalizer_Za2 hx) h.Qb_le_normalizer_Qa) ?_ ?_
  · intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp (h.Za_le_centralizer_Qa hg) y hy.2
  · intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact F7.isElemAbelian_comm (h.isElemAbelian_Za2 x) hy.1 hg

theorem R_eq_Za_inf_Qa2 (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    VZ S H ⊓ conjSub x (VZ S H) = VZ S H ⊓ conjSub x (pCoreOf 2 H) := by
  obtain ⟨hn, -⟩ := h.normal_Za_inf_Qa2 hx hxH
  have hle : VZ S H ⊓ conjSub x (pCoreOf 2 H) ≤ conjSub x (VZ S H) := by
    have e := F7.conjSub_eq_of_mem_normalizer (hn hx)
    calc VZ S H ⊓ conjSub x (pCoreOf 2 H)
        = conjSub x (VZ S H ⊓ conjSub x (pCoreOf 2 H)) := e.symm
      _ ≤ conjSub x (VZ S H) := conjSub_mono x inf_le_left
  exact le_antisymm (inf_le_inf_left _ (h.Za2_le_Qa2 x)) (le_inf inf_le_left hle)

theorem R_eq_Za2_inf_Qa (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    VZ S H ⊓ conjSub x (VZ S H) = conjSub x (VZ S H) ⊓ pCoreOf 2 H := by
  obtain ⟨hn, -⟩ := h.normal_Za2_inf_Qa hx hxH
  have hle : conjSub x (VZ S H) ⊓ pCoreOf 2 H ≤ VZ S H := by
    have e := F7.conjSub_eq_of_mem_normalizer (hn (M.inv_mem hx))
    calc conjSub x (VZ S H) ⊓ pCoreOf 2 H
        = conjSub x⁻¹ (conjSub x (VZ S H) ⊓ pCoreOf 2 H) := e.symm
      _ ≤ conjSub x⁻¹ (conjSub x (VZ S H)) := conjSub_mono _ inf_le_left
      _ = VZ S H := conjSub_conjSub_inv x _
  exact le_antisymm (le_inf inf_le_right (inf_le_left.trans h.Za_le_Qa)) (le_inf hle inf_le_left)

theorem R_le_Qb (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    VZ S H ⊓ conjSub x (VZ S H) ≤ pCoreOf 2 M :=
  (inf_le_inf h.Za_le_Qa (h.Za2_le_Qa2 x)).trans (h.inf_Qa_Qa2_le hx hxH)

theorem R_normal (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    M ≤ Subgroup.normalizer ((VZ S H ⊓ conjSub x (VZ S H) : Subgroup G) : Set G) := by
  rw [h.R_eq_Za_inf_Qa2 hx hxH]
  exact (h.normal_Za_inf_Qa2 hx hxH).1

theorem oTwoUpper_le_centralizer_R (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    oTwoUpper M ≤ Subgroup.centralizer ((VZ S H ⊓ conjSub x (VZ S H) : Subgroup G) : Set G) := by
  rw [h.R_eq_Za_inf_Qa2 hx hxH]
  exact (h.normal_Za_inf_Qa2 hx hxH).2

theorem commutator_R_oTwoUpper (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    ⁅VZ S H ⊓ conjSub x (VZ S H), oTwoUpper M⁆ = ⊥ := by
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (h.oTwoUpper_le_centralizer_R hx hxH)

theorem Zb_le_R (h : B1Hyp H M S) {x : G} (hx : x ∈ M) :
    VZ S M ≤ VZ S H ⊓ conjSub x (VZ S H) := by
  refine le_inf h.Zb_le_Za ?_
  have e := F7.conjSub_eq_of_mem_normalizer (h.M_le_normalizer_Zb hx)
  calc VZ S M = conjSub x (VZ S M) := e.symm
    _ ≤ conjSub x (VZ S H) := conjSub_mono x h.Zb_le_Za

theorem R_le_Ha (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    VZ S H ⊓ conjSub x (VZ S H) ≤ VZ S H ⊓ pCoreOf 2 M :=
  le_inf inf_le_left (h.R_le_Qb hx hxH)

theorem R_le_Ha2 (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    VZ S H ⊓ conjSub x (VZ S H) ≤ conjSub x (VZ S H) ⊓ pCoreOf 2 M :=
  le_inf inf_le_right (h.R_le_Qb hx hxH)

theorem inf_Ha_Qa2 (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    (VZ S H ⊓ pCoreOf 2 M) ⊓ conjSub x (pCoreOf 2 H) = VZ S H ⊓ conjSub x (VZ S H) := by
  calc (VZ S H ⊓ pCoreOf 2 M) ⊓ conjSub x (pCoreOf 2 H)
      = (VZ S H ⊓ conjSub x (pCoreOf 2 H)) ⊓ pCoreOf 2 M := inf_right_comm _ _ _
    _ = (VZ S H ⊓ conjSub x (VZ S H)) ⊓ pCoreOf 2 M := by rw [h.R_eq_Za_inf_Qa2 hx hxH]
    _ = VZ S H ⊓ conjSub x (VZ S H) := inf_eq_left.mpr (h.R_le_Qb hx hxH)

theorem inf_Ha2_Qa (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    (conjSub x (VZ S H) ⊓ pCoreOf 2 M) ⊓ pCoreOf 2 H = VZ S H ⊓ conjSub x (VZ S H) := by
  calc (conjSub x (VZ S H) ⊓ pCoreOf 2 M) ⊓ pCoreOf 2 H
      = (conjSub x (VZ S H) ⊓ pCoreOf 2 H) ⊓ pCoreOf 2 M := inf_right_comm _ _ _
    _ = (VZ S H ⊓ conjSub x (VZ S H)) ⊓ pCoreOf 2 M := by rw [h.R_eq_Za2_inf_Qa hx hxH]
    _ = VZ S H ⊓ conjSub x (VZ S H) := inf_eq_left.mpr (h.R_le_Qb hx hxH)

theorem not_oTwoUpper_M_le_Qb (h : B1Hyp H M S) : ¬ oTwoUpper M ≤ pCoreOf 2 M := by
  intro hle
  have hM : M ≤ S := by
    rw [← F112W.sup_oTwoUpper_eq_of_isSylowTwoOf h.sylow_M]
    exact sup_le le_rfl (hle.trans h.Qb_le_S)
  have := Subgroup.relIndex_eq_one.mpr hM
  have h3 := h.relIndex_S_M
  omega

theorem eta_Qb_ne_zero (h : B1Hyp H M S) :
    F112W.eta M (pCoreOf 2 M) (pCoreOf 2 M) ≠ 0 := by
  intro h0
  have hN : IsNormalIn M (pCoreOf 2 M) (pCoreOf 2 M) :=
    F112W.isNormalIn_of_le_normalizer le_rfl (le_normalizer_pCoreOf 2 M)
  have hc := (F112W.eta_eq_zero_iff (pCoreOf_le 2 M) le_rfl hN).mp h0
  apply h.not_oTwoUpper_M_le_Qb
  have hcen : oTwoUpper M ≤ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hc
  intro g hg
  exact h.amalgam.charTwo_right ⟨oTwoUpper_le M hg, hcen hg⟩

theorem R_ne_Ha (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    VZ S H ⊓ conjSub x (VZ S H) ≠ VZ S H ⊓ pCoreOf 2 M := by
  intro hR
  have hRle2 := h.R_le_Ha2 hx hxH
  have hHa2 : VZ S H ⊓ pCoreOf 2 M = conjSub x (VZ S H) ⊓ pCoreOf 2 M := by
    have hle : VZ S H ⊓ pCoreOf 2 M ≤ conjSub x (VZ S H) ⊓ pCoreOf 2 M := hR ▸ hRle2
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [h.card_Ha, h.card_Ha2 hx])
  have hc1 : ⁅pCoreOf 2 M, VZ S H⁆ ≤ VZ S H ⊓ conjSub x (VZ S H) := by
    rw [Subgroup.commutator_comm, h.commutator_Za_Qb, hR]
  have hc2 : ⁅pCoreOf 2 M, conjSub x (VZ S H)⁆ ≤ VZ S H ⊓ conjSub x (VZ S H) := by
    rw [Subgroup.commutator_comm, h.commutator_Za2_Qb hx, ← hHa2, ← hR]
  have hRn := h.R_normal hx hxH
  have hZa : VZ S H ≤ Subgroup.normalizer ((VZ S H ⊓ conjSub x (VZ S H) : Subgroup G) : Set G) :=
    fun _ hg => hRn (h.S_le_M (h.Za_le_S hg))
  have hZa2 : conjSub x (VZ S H) ≤
      Subgroup.normalizer ((VZ S H ⊓ conjSub x (VZ S H) : Subgroup G) : Set G) :=
    fun _ hg => hRn (h.conjSub_S_le_M hx (h.Za2_le_S2 x hg))
  have hQR : ⁅pCoreOf 2 M, oTwoUpper M⁆ ≤ VZ S H ⊓ conjSub x (VZ S H) :=
    (Subgroup.commutator_mono le_rfl (h.oTwoUpper_M_le_D hx hxH)).trans
      (commutator_sup_le hZa hZa2 hc1 hc2)
  have hNr : IsNormalIn M (pCoreOf 2 M) (VZ S H ⊓ conjSub x (VZ S H)) :=
    F112W.isNormalIn_of_le_normalizer (h.R_le_Qb hx hxH) hRn
  have hNq : IsNormalIn M (pCoreOf 2 M) (pCoreOf 2 M) :=
    F112W.isNormalIn_of_le_normalizer le_rfl (le_normalizer_pCoreOf 2 M)
  have e1 : F112W.eta M (pCoreOf 2 M) (pCoreOf 2 M) =
      F112W.eta M (pCoreOf 2 M) (VZ S H ⊓ conjSub x (VZ S H)) :=
    F112W.eta_eq_of_commutator_le (pCoreOf_le 2 M) le_rfl hNr hNq (h.R_le_Qb hx hxH) hQR
  have e2 : F112W.eta M (pCoreOf 2 M) (VZ S H ⊓ conjSub x (VZ S H)) = 0 :=
    (F112W.eta_eq_zero_iff (pCoreOf_le 2 M) le_rfl hNr).mpr (h.commutator_R_oTwoUpper hx hxH)
  exact h.eta_Qb_ne_zero (by rw [e1, e2])

theorem card_R_le_four (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    Nat.card ↥(VZ S H ⊓ conjSub x (VZ S H)) ≤ 4 := by
  have hlt : VZ S H ⊓ conjSub x (VZ S H) < VZ S H ⊓ pCoreOf 2 M :=
    lt_of_le_of_ne (h.R_le_Ha hx hxH) (h.R_ne_Ha hx hxH)
  have h1 := Subgroup.card_lt_of_lt hlt
  have h2 := Subgroup.card_dvd_of_le (h.R_le_Ha hx hxH)
  rw [h.card_Ha] at h1 h2
  obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show _ ∣ 2 ^ 3 from h2)
  rw [hci] at h1 ⊢
  interval_cases i <;> omega

theorem S_le_normalizer_Ha (h : B1Hyp H M S) :
    S ≤ Subgroup.normalizer ((VZ S H ⊓ pCoreOf 2 M : Subgroup G) : Set G) :=
  F7.le_normalizer_inf h.S_le_normalizer_Za h.S_le_normalizer_Qb

theorem Qb_le_normalizer_Ha2 (h : B1Hyp H M S) {x : G} (hx : x ∈ M) :
    pCoreOf 2 M ≤ Subgroup.normalizer ((conjSub x (VZ S H) ⊓ pCoreOf 2 M : Subgroup G) : Set G) :=
  F7.le_normalizer_inf (h.Qb_le_normalizer_Za2 hx)
    fun _ hg => h.M_le_normalizer_Qb (pCoreOf_le 2 M hg)

theorem Qb_le_normalizer_Ha (h : B1Hyp H M S) :
    pCoreOf 2 M ≤ Subgroup.normalizer ((VZ S H ⊓ pCoreOf 2 M : Subgroup G) : Set G) :=
  fun _ hg => h.S_le_normalizer_Ha (h.Qb_le_S hg)

theorem Za_le_normalizer_Vh (h : B1Hyp H M S) {x : G} (_hx : x ∈ M) :
    VZ S H ≤ Subgroup.normalizer
      (((VZ S H ⊓ pCoreOf 2 M) ⊔ (conjSub x (VZ S H) ⊓ pCoreOf 2 M) : Subgroup G) : Set G) := by
  apply le_normalizer_of_commutator_le
  calc ⁅(VZ S H ⊓ pCoreOf 2 M) ⊔ (conjSub x (VZ S H) ⊓ pCoreOf 2 M), VZ S H⁆
      ≤ ⁅pCoreOf 2 M, VZ S H⁆ :=
        Subgroup.commutator_mono (sup_le inf_le_right inf_le_right) le_rfl
    _ = VZ S H ⊓ pCoreOf 2 M := (Subgroup.commutator_comm _ _).trans h.commutator_Za_Qb
    _ ≤ _ := le_sup_left

theorem Za2_le_normalizer_Vh (h : B1Hyp H M S) {x : G} (hx : x ∈ M) :
    conjSub x (VZ S H) ≤ Subgroup.normalizer
      (((VZ S H ⊓ pCoreOf 2 M) ⊔ (conjSub x (VZ S H) ⊓ pCoreOf 2 M) : Subgroup G) : Set G) := by
  apply le_normalizer_of_commutator_le
  calc ⁅(VZ S H ⊓ pCoreOf 2 M) ⊔ (conjSub x (VZ S H) ⊓ pCoreOf 2 M), conjSub x (VZ S H)⁆
      ≤ ⁅pCoreOf 2 M, conjSub x (VZ S H)⁆ :=
        Subgroup.commutator_mono (sup_le inf_le_right inf_le_right) le_rfl
    _ = conjSub x (VZ S H) ⊓ pCoreOf 2 M :=
        (Subgroup.commutator_comm _ _).trans (h.commutator_Za2_Qb hx)
    _ ≤ _ := le_sup_right

theorem Vh_normal (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    M ≤ Subgroup.normalizer
      (((VZ S H ⊓ pCoreOf 2 M) ⊔ (conjSub x (VZ S H) ⊓ pCoreOf 2 M) : Subgroup G) : Set G) := by
  refine (h.M_eq_Qb_sup_D hx hxH).le.trans (sup_le ?_ (sup_le (h.Za_le_normalizer_Vh hx)
    (h.Za2_le_normalizer_Vh hx)))
  exact F1.le_normalizer_sup h.Qb_le_normalizer_Ha (h.Qb_le_normalizer_Ha2 hx)

theorem commutator_Qb_oTwoUpper_le_Vh (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    ⁅pCoreOf 2 M, oTwoUpper M⁆ ≤
      (VZ S H ⊓ pCoreOf 2 M) ⊔ (conjSub x (VZ S H) ⊓ pCoreOf 2 M) := by
  have h1 : ⁅pCoreOf 2 M, VZ S H⁆ ≤
      (VZ S H ⊓ pCoreOf 2 M) ⊔ (conjSub x (VZ S H) ⊓ pCoreOf 2 M) :=
    ((Subgroup.commutator_comm _ _).trans h.commutator_Za_Qb).le.trans le_sup_left
  have h2 : ⁅pCoreOf 2 M, conjSub x (VZ S H)⁆ ≤
      (VZ S H ⊓ pCoreOf 2 M) ⊔ (conjSub x (VZ S H) ⊓ pCoreOf 2 M) :=
    ((Subgroup.commutator_comm _ _).trans (h.commutator_Za2_Qb hx)).le.trans le_sup_right
  exact (Subgroup.commutator_mono le_rfl (h.oTwoUpper_M_le_D hx hxH)).trans
    (commutator_sup_le (h.Za_le_normalizer_Vh hx) (h.Za2_le_normalizer_Vh hx) h1 h2)

theorem not_commutator_Vh_le_R (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    ¬ ⁅(VZ S H ⊓ pCoreOf 2 M) ⊔ (conjSub x (VZ S H) ⊓ pCoreOf 2 M), oTwoUpper M⁆ ≤
      VZ S H ⊓ conjSub x (VZ S H) := by
  intro hc
  have hVhQ : (VZ S H ⊓ pCoreOf 2 M) ⊔ (conjSub x (VZ S H) ⊓ pCoreOf 2 M) ≤ pCoreOf 2 M :=
    sup_le inf_le_right inf_le_right
  have hNv : IsNormalIn M (pCoreOf 2 M)
      ((VZ S H ⊓ pCoreOf 2 M) ⊔ (conjSub x (VZ S H) ⊓ pCoreOf 2 M)) :=
    F112W.isNormalIn_of_le_normalizer hVhQ (h.Vh_normal hx hxH)
  have hNr : IsNormalIn M (pCoreOf 2 M) (VZ S H ⊓ conjSub x (VZ S H)) :=
    F112W.isNormalIn_of_le_normalizer (h.R_le_Qb hx hxH) (h.R_normal hx hxH)
  have hNq : IsNormalIn M (pCoreOf 2 M) (pCoreOf 2 M) :=
    F112W.isNormalIn_of_le_normalizer le_rfl (le_normalizer_pCoreOf 2 M)
  have hRV : VZ S H ⊓ conjSub x (VZ S H) ≤
      (VZ S H ⊓ pCoreOf 2 M) ⊔ (conjSub x (VZ S H) ⊓ pCoreOf 2 M) :=
    (h.R_le_Ha hx hxH).trans le_sup_left
  have e1 : F112W.eta M (pCoreOf 2 M) ((VZ S H ⊓ pCoreOf 2 M) ⊔
      (conjSub x (VZ S H) ⊓ pCoreOf 2 M)) =
      F112W.eta M (pCoreOf 2 M) (VZ S H ⊓ conjSub x (VZ S H)) :=
    F112W.eta_eq_of_commutator_le (pCoreOf_le 2 M) le_rfl hNr hNv hRV hc
  have e2 : F112W.eta M (pCoreOf 2 M) (pCoreOf 2 M) = F112W.eta M (pCoreOf 2 M)
      ((VZ S H ⊓ pCoreOf 2 M) ⊔ (conjSub x (VZ S H) ⊓ pCoreOf 2 M)) :=
    F112W.eta_eq_of_commutator_le (pCoreOf_le 2 M) le_rfl hNv hNq hVhQ
      (h.commutator_Qb_oTwoUpper_le_Vh hx hxH)
  have e3 : F112W.eta M (pCoreOf 2 M) (VZ S H ⊓ conjSub x (VZ S H)) = 0 :=
    (F112W.eta_eq_zero_iff (pCoreOf_le 2 M) le_rfl hNr).mpr (h.commutator_R_oTwoUpper hx hxH)
  exact h.eta_Qb_ne_zero (by rw [e2, e1, e3])

end B1Hyp

end Hyp

end F53B1

end CFSG.Quasithin
