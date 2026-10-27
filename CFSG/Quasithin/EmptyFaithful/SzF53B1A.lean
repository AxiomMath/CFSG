module

public import CFSG.Quasithin.EmptyFaithful.SzF53B1Defs
public import CFSG.Quasithin.Recognition.F112WValency
public import CFSG.Quasithin.Recognition.F112WChief
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace F53B1

section Pure

variable {G : Type*} [Group G]

theorem pow_mul_eq_of_mem_normalizer {D : Subgroup G} {q d : G}
    (hq : q ∈ Subgroup.normalizer (D : Set G)) (hd : d ∈ D) (n : ℕ) :
    ∃ d' ∈ D, (q * d) ^ n = q ^ n * d' := by
  induction n with
  | zero => exact ⟨1, D.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨d', hd', he⟩ := ih
    refine ⟨(q⁻¹ * d' * q) * d, D.mul_mem ?_ hd, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (D : Set G)).inv_mem hq) d').mp
        hd'
      simpa using this
    · rw [pow_succ, he, pow_succ]
      group

end Pure

section Hyp

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace B1Hyp

theorem Qb_le_normalizer_Qa (h : B1Hyp H M S) :
    pCoreOf 2 M ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
  fun _ hg => h.H_le_normalizer_Qa (h.S_le_H (h.Qb_le_S hg))

theorem Qb_le_normalizer_Za (h : B1Hyp H M S) :
    pCoreOf 2 M ≤ Subgroup.normalizer (VZ S H : Set G) :=
  fun _ hg => h.H_le_normalizer_Za (h.S_le_H (h.Qb_le_S hg))

theorem S_le_normalizer_Za (h : B1Hyp H M S) : S ≤ Subgroup.normalizer (VZ S H : Set G) :=
  fun _ hg => h.H_le_normalizer_Za (h.S_le_H hg)

theorem S_le_normalizer_Qa (h : B1Hyp H M S) : S ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
  fun _ hg => h.H_le_normalizer_Qa (h.S_le_H hg)

theorem S_le_normalizer_Qb (h : B1Hyp H M S) : S ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
  fun _ hg => h.M_le_normalizer_Qb (h.S_le_M hg)

theorem Qa_le_normalizer_Qb (h : B1Hyp H M S) :
    pCoreOf 2 H ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
  fun _ hg => h.S_le_normalizer_Qb (h.Qa_le_S hg)

theorem Za_le_normalizer_Qb (h : B1Hyp H M S) :
    VZ S H ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
  fun _ hg => h.S_le_normalizer_Qb (h.Za_le_S hg)

theorem Za_ne_bot (h : B1Hyp H M S) : VZ S H ≠ ⊥ := by
  intro hbot
  have h1 := h.zfacts.card_eq
  rw [hbot, Subgroup.card_bot] at h1
  omega

theorem sup_Za_Qb (h : B1Hyp H M S) : VZ S H ⊔ pCoreOf 2 M = S := by
  rw [sup_comm]
  exact sup_eq_of_relIndex_two h.Qb_le_S h.relIndex_Qb_S h.Za_le_S h.b_one

theorem sup_Qa_Qb (h : B1Hyp H M S) : pCoreOf 2 H ⊔ pCoreOf 2 M = S :=
  le_antisymm (sup_le h.Qa_le_S h.Qb_le_S)
    (h.sup_Za_Qb.symm.le.trans (sup_le_sup_right h.Za_le_Qa _))

theorem relIndex_Qa_inf_Qb (h : B1Hyp H M S) :
    (pCoreOf 2 H ⊓ pCoreOf 2 M).relIndex (pCoreOf 2 H) = 2 := by
  have h1 := F1.relIndex_sup_eq_of_le_normalizer h.Qa_le_normalizer_Qb
  rw [h.sup_Qa_Qb, h.relIndex_Qb_S] at h1
  rw [Subgroup.inf_relIndex_left]
  exact h1.symm

theorem relIndex_Za_inf_Qb (h : B1Hyp H M S) :
    (VZ S H ⊓ pCoreOf 2 M).relIndex (VZ S H) = 2 := by
  have h1 := F1.relIndex_sup_eq_of_le_normalizer h.Za_le_normalizer_Qb
  rw [h.sup_Za_Qb, h.relIndex_Qb_S] at h1
  rw [Subgroup.inf_relIndex_left]
  exact h1.symm

theorem card_Ha (h : B1Hyp H M S) : Nat.card ↥(VZ S H ⊓ pCoreOf 2 M) = 8 := by
  have h1 := Subgroup.relIndex_mul_card (VZ S H ⊓ pCoreOf 2 M) (VZ S H)
  rw [inf_eq_left.mpr (inf_le_left : VZ S H ⊓ pCoreOf 2 M ≤ VZ S H), h.relIndex_Za_inf_Qb,
    h.zfacts.card_eq] at h1
  omega

theorem conjSub_Qb (h : B1Hyp H M S) {x : G} (hx : x ∈ M) :
    conjSub x (pCoreOf 2 M) = pCoreOf 2 M :=
  F7.conjSub_eq_of_mem_normalizer (h.M_le_normalizer_Qb hx)

theorem conjSub_S_le_M (h : B1Hyp H M S) {x : G} (hx : x ∈ M) : conjSub x S ≤ M := by
  have := conjSub_mono x h.S_le_M
  rwa [F7.conjSub_eq_of_mem hx] at this

theorem Qb_le_conjSub_S (h : B1Hyp H M S) {x : G} (hx : x ∈ M) : pCoreOf 2 M ≤ conjSub x S := by
  have := conjSub_mono x h.Qb_le_S
  rwa [h.conjSub_Qb hx] at this

theorem Qb_le_conjSub_H (h : B1Hyp H M S) {x : G} (hx : x ∈ M) : pCoreOf 2 M ≤ conjSub x H :=
  (h.Qb_le_conjSub_S hx).trans (conjSub_mono x h.S_le_H)

theorem sup_conj (h : B1Hyp H M S) {x : G} (hx : x ∈ M) :
    conjSub x S = conjSub x (VZ S H) ⊔ pCoreOf 2 M ∧
      conjSub x S = conjSub x (pCoreOf 2 H) ⊔ pCoreOf 2 M := by
  constructor
  · have := congrArg (conjSub x) h.sup_Za_Qb.symm
    rwa [conjSub_sup, h.conjSub_Qb hx] at this
  · have := congrArg (conjSub x) h.sup_Qa_Qb.symm
    rwa [conjSub_sup, h.conjSub_Qb hx] at this

theorem Qb_le_normalizer_Qa2 (h : B1Hyp H M S) {x : G} (hx : x ∈ M) :
    pCoreOf 2 M ≤ Subgroup.normalizer (conjSub x (pCoreOf 2 H) : Set G) :=
  fun _ hg => conjSub_le_normalizer h.H_le_normalizer_Qa (h.Qb_le_conjSub_H hx hg)

theorem Qb_le_normalizer_Za2 (h : B1Hyp H M S) {x : G} (hx : x ∈ M) :
    pCoreOf 2 M ≤ Subgroup.normalizer (conjSub x (VZ S H) : Set G) :=
  fun _ hg => conjSub_le_normalizer h.H_le_normalizer_Za (h.Qb_le_conjSub_H hx hg)

theorem conjSub_S_le_normalizer_Qa2 (h : B1Hyp H M S) (x : G) :
    conjSub x S ≤ Subgroup.normalizer (conjSub x (pCoreOf 2 H) : Set G) :=
  conjSub_le_normalizer h.S_le_normalizer_Qa

theorem Za2_le_Qa2 (h : B1Hyp H M S) (x : G) :
    conjSub x (VZ S H) ≤ conjSub x (pCoreOf 2 H) := conjSub_mono x h.Za_le_Qa

theorem Za2_le_S2 (h : B1Hyp H M S) (x : G) : conjSub x (VZ S H) ≤ conjSub x S :=
  conjSub_mono x h.Za_le_S

theorem Qa2_le_S2 (h : B1Hyp H M S) (x : G) : conjSub x (pCoreOf 2 H) ≤ conjSub x S :=
  conjSub_mono x h.Qa_le_S

theorem Za2_le_centralizer_Qa2 (h : B1Hyp H M S) (x : G) :
    conjSub x (VZ S H) ≤ Subgroup.centralizer (conjSub x (pCoreOf 2 H) : Set G) := by
  rw [conjSub_centralizer]
  exact conjSub_mono x h.Za_le_centralizer_Qa

theorem isElemAbelian_Za2 (h : B1Hyp H M S) (x : G) :
    IsElemAbelian 2 (conjSub x (VZ S H)) := F7.isElemAbelian_conjSub h.zfacts.elemAbelian

theorem card_Ha2 (h : B1Hyp H M S) {x : G} (hx : x ∈ M) :
    Nat.card ↥(conjSub x (VZ S H) ⊓ pCoreOf 2 M) = 8 := by
  have e : conjSub x (VZ S H ⊓ pCoreOf 2 M) = conjSub x (VZ S H) ⊓ pCoreOf 2 M := by
    rw [conjSub_inf, h.conjSub_Qb hx]
  rw [← e, card_conjSub]
  exact h.card_Ha

theorem coreIn_S_M (h : B1Hyp H M S) : coreIn S M = pCoreOf 2 M := by
  apply le_antisymm
  · refine le_pCoreOf_of_le_normalizer 2 (coreIn_le_left S M) (le_normalizer_coreIn S M) ?_
    exact h.sylow_M.2.1.to_le (coreIn_le_right S M)
  · exact le_coreIn (pCoreOf_le 2 M) (le_normalizer_pCoreOf 2 M) h.Qb_le_S

theorem inf_conj_S (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    S ⊓ conjSub x S = pCoreOf 2 M := by
  rw [← h.coreIn_S_M]
  exact (F112W.coreIn_eq_inf_conjSub_of_relIndex_three h.S_le_M h.relIndex_S_M hx
    (h.not_mem_S hxH)).symm

theorem inf_Qa_Qa2_le (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    pCoreOf 2 H ⊓ conjSub x (pCoreOf 2 H) ≤ pCoreOf 2 M := by
  rw [← h.inf_conj_S hx hxH]
  exact inf_le_inf h.Qa_le_S (h.Qa2_le_S2 x)

theorem conjClosure_eq (h : B1Hyp H M S) {Y : Subgroup G} (hY : Y ≤ VZ S H) (hne : Y ≠ ⊥) :
    conjClosure Y H = VZ S H := by
  have hle : conjClosure Y H ≤ VZ S H :=
    conjClosure_le fun k hk z hz =>
      (Subgroup.mem_normalizer_iff.mp (h.H_le_normalizer_Za hk) z).mp (hY hz)
  rcases h.zfacts.irred _ hle (le_normalizer_conjClosure Y H) with h1 | h1
  · exfalso
    exact hne (le_bot_iff.mp (h1 ▸ le_conjClosure Y H))
  · exact h1

theorem isChiefSeriesFrom_Za (h : B1Hyp H M S) :
    IsChiefSeriesFrom H (pCoreOf 2 H) (VZ S H) 1 := by
  have hZa : IsNormalIn H (pCoreOf 2 H) (VZ S H) :=
    F112W.isNormalIn_of_le_normalizer h.Za_le_Qa h.H_le_normalizer_Za
  have hbot : IsNormalIn H (pCoreOf 2 H) ⊥ :=
    F112W.isNormalIn_of_le_normalizer bot_le fun g _ => by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      simp only [Subgroup.mem_bot]
      constructor
      · rintro rfl; group
      · intro hy
        have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
        rw [this, hy]; group
  have hstep : IsChiefStep H (pCoreOf 2 H) ⊥ (VZ S H) := by
    refine ⟨hZa, hbot, bot_lt_iff_ne_bot.mpr h.Za_ne_bot, fun K hK _ hKZ => ?_⟩
    exact h.zfacts.irred K hKZ (fun g hg => by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · exact hK.2 g hg y
      · intro hy
        have := hK.2 g⁻¹ (H.inv_mem hg) _ hy
        simpa [mul_assoc] using this)
  have hnc : ¬ IsCentralStep H ⊥ (VZ S H) := by
    intro hc
    obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h.Za_ne_bot
    have hzpow : Subgroup.zpowers (z : G) ≤ VZ S H := by
      rw [Subgroup.zpowers_le]; exact z.2
    have hn : H ≤ Subgroup.normalizer ((Subgroup.zpowers (z : G) : Subgroup G) : Set G) := by
      intro g hg
      have hcomm : g * (z : G) = (z : G) * g := by
        have := hc g hg (z : G) z.2
        rw [Subgroup.mem_bot] at this
        have h2 : g * (z : G) * g⁻¹ = (z : G) := by
          have := mul_inv_eq_one.mp this
          exact this
        calc g * (z : G) = g * (z : G) * g⁻¹ * g := by group
          _ = (z : G) * g := by rw [h2]
      have hmem : g ∈ Subgroup.centralizer ((Subgroup.zpowers (z : G) : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨k, rfl⟩
        exact (Commute.zpow_left (show Commute (z : G) g from hcomm.symm) k).eq
      exact Subgroup.centralizer_le_normalizer _ hmem
    rcases h.zfacts.irred _ hzpow hn with h1 | h1
    · apply hz1
      have : (z : G) ∈ Subgroup.zpowers (z : G) := Subgroup.mem_zpowers _
      rw [h1, Subgroup.mem_bot] at this
      exact Subtype.ext this
    · have hc2 : (z : G) ^ 2 = 1 := F7.isElemAbelian_pow_eq_one h.zfacts.elemAbelian z.2
      have h3 : Nat.card (Subgroup.zpowers (z : G)) ≤ 2 := by
        rw [Nat.card_zpowers]
        exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hc2)
      rw [h1, h.zfacts.card_eq] at h3
      omega
  exact IsChiefSeriesFrom.noncentral hstep hnc IsChiefSeriesFrom.bot

theorem Za_le_of_normal (h : B1Hyp H M S) {D : Subgroup G} (hDS : D ≤ S)
    (hDn : H ≤ Subgroup.normalizer (D : Set G)) (hD : D ≠ ⊥) : VZ S H ≤ D := by
  obtain ⟨z, hzD, hzC, hz2, hz1⟩ := exists_involution_of_normal h.sylow_H.2.1 hDS
    (fun g hg => hDn (h.S_le_H hg)) hD
  have hzS : z ∈ S := hDS hzD
  have hzZ : z ∈ VZ S H :=
    le_conjClosure _ _ (Subgroup.subset_closure ⟨⟨hzS, hzC⟩, hz2⟩)
  have hY : Subgroup.zpowers z ≤ VZ S H := by
    rw [Subgroup.zpowers_le]; exact hzZ
  have hYD : Subgroup.zpowers z ≤ D := by
    rw [Subgroup.zpowers_le]; exact hzD
  have hne : Subgroup.zpowers z ≠ ⊥ := fun hb => hz1 (Subgroup.zpowers_eq_bot.mp hb)
  rw [← h.conjClosure_eq hY hne]
  exact conjClosure_le fun k hk y hy => (Subgroup.mem_normalizer_iff.mp (hDn hk) y).mp (hYD hy)

theorem isElemAbelian_Qa (h : B1Hyp H M S) : IsElemAbelian 2 (pCoreOf 2 H) := by
  set Φ : Subgroup G := ⁅pCoreOf 2 H, pCoreOf 2 H⁆ ⊔
    Subgroup.closure {g | ∃ q ∈ pCoreOf 2 H, g = q ^ 2} with hΦ
  have hΦQb : Φ ≤ pCoreOf 2 M := by
    refine sup_le ?_ ?_
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact (commutator_sq_mem_of_relIndex_two h.relIndex_Qb_S (h.Qa_le_S ha) (h.Qa_le_S hb)).1
    · rw [Subgroup.closure_le]
      rintro _ ⟨q, hq, rfl⟩
      exact (commutator_sq_mem_of_relIndex_two h.relIndex_Qb_S (h.Qa_le_S hq) (h.Qa_le_S hq)).2
  have hΦn : H ≤ Subgroup.normalizer (Φ : Set G) := by
    refine F1.le_normalizer_sup ?_ ?_
    · intro g hg
      apply mem_normalizer_of_conjSub_eq
      rw [← conjSub_commutator, F7.conjSub_eq_of_mem_normalizer (h.H_le_normalizer_Qa hg)]
    · refine F7.le_normalizer_closure _ fun g hg s hs => ?_
      obtain ⟨q, hq, rfl⟩ := hs
      exact ⟨g * q * g⁻¹, (Subgroup.mem_normalizer_iff.mp (h.H_le_normalizer_Qa hg) q).mp hq,
        by rw [conj_pow]⟩
  have hΦ0 : Φ = ⊥ := by
    by_contra hne
    exact h.b_one ((h.Za_le_of_normal (hΦQb.trans h.Qb_le_S) hΦn hne).trans hΦQb)
  rw [F7.isElemAbelian_iff]
  constructor
  · intro a ha b hb
    have h1 : ⁅a, b⁆ ∈ Φ := Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator ha hb)
    rw [hΦ0, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  · intro a ha
    have h1 : a ^ 2 ∈ Φ := Subgroup.mem_sup_right (Subgroup.subset_closure ⟨a, ha, rfl⟩)
    rwa [hΦ0, Subgroup.mem_bot] at h1

theorem S_le_normalizer_commutator_Za_Qb (h : B1Hyp H M S) :
    S ≤ Subgroup.normalizer ((⁅VZ S H, pCoreOf 2 M⁆ : Subgroup G) : Set G) := by
  intro g hg
  apply mem_normalizer_of_conjSub_eq
  rw [← conjSub_commutator, F7.conjSub_eq_of_mem_normalizer (h.S_le_normalizer_Za hg),
    F7.conjSub_eq_of_mem_normalizer (h.S_le_normalizer_Qb hg)]

theorem commutator_Za_Qb (h : B1Hyp H M S) :
    ⁅VZ S H, pCoreOf 2 M⁆ = VZ S H ⊓ pCoreOf 2 M := by
  have hle : ⁅VZ S H, pCoreOf 2 M⁆ ≤ VZ S H ⊓ pCoreOf 2 M :=
    F7.commutator_le_inf_of_normalizes h.Za_le_normalizer_Qb h.Qb_le_normalizer_Za
  have hSn := h.S_le_normalizer_commutator_Za_Qb
  have hsup : ⁅VZ S H, S⁆ ≤ ⁅VZ S H, pCoreOf 2 M⁆ := by
    have e : ⁅VZ S H, S⁆ = ⁅VZ S H, VZ S H ⊔ pCoreOf 2 M⁆ := by rw [h.sup_Za_Qb]
    rw [e]
    refine commutator_sup_le (fun g hg => hSn (h.Za_le_S hg)) (fun g hg => hSn (h.Qb_le_S hg))
      ?_ le_rfl
    rw [F7.commutator_self_eq_bot h.zfacts.elemAbelian]
    exact bot_le
  have hge : ⁅VZ S H, S⁆ = ⁅VZ S H, pCoreOf 2 M⁆ :=
    le_antisymm hsup (Subgroup.commutator_mono le_rfl h.Qb_le_S)
  have hcard : Nat.card ↥⁅VZ S H, pCoreOf 2 M⁆ = 8 := by
    rw [← hge]
    exact h.zfacts.card_comm
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, h.card_Ha])

theorem commutator_Za2_Qb (h : B1Hyp H M S) {x : G} (hx : x ∈ M) :
    ⁅conjSub x (VZ S H), pCoreOf 2 M⁆ = conjSub x (VZ S H) ⊓ pCoreOf 2 M := by
  have := congrArg (conjSub x) h.commutator_Za_Qb
  rwa [← conjSub_commutator, conjSub_inf, h.conjSub_Qb hx] at this

theorem Qb_le_normalizer_D (h : B1Hyp H M S) {x : G} (hx : x ∈ M) :
    pCoreOf 2 M ≤ Subgroup.normalizer ((VZ S H ⊔ conjSub x (VZ S H) : Subgroup G) : Set G) :=
  F1.le_normalizer_sup h.Qb_le_normalizer_Za (h.Qb_le_normalizer_Za2 hx)

theorem M_eq_Qb_sup_D (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    M = pCoreOf 2 M ⊔ (VZ S H ⊔ conjSub x (VZ S H)) := by
  apply le_antisymm
  · refine (h.sup_conj_S hx (h.not_mem_S hxH)).symm.le.trans (sup_le ?_ ?_)
    · exact h.sup_Za_Qb.symm.le.trans
        (sup_le (le_sup_of_le_right le_sup_left) le_sup_left)
    · exact (h.sup_conj hx).1.le.trans (sup_le (le_sup_of_le_right le_sup_right) le_sup_left)
  · exact sup_le (pCoreOf_le 2 M) (sup_le (h.Za_le_S.trans h.S_le_M)
      ((h.Za2_le_S2 x).trans (h.conjSub_S_le_M hx)))

theorem oTwoUpper_M_le_D (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    oTwoUpper M ≤ VZ S H ⊔ conjSub x (VZ S H) := by
  apply oTwoUpper_le_of_pow_mem
  intro g hg
  have hg' : g ∈ pCoreOf 2 M ⊔ (VZ S H ⊔ conjSub x (VZ S H)) := (h.M_eq_Qb_sup_D hx hxH).le hg
  obtain ⟨q, hq, d, hd, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_le_normalizer (h.Qb_le_normalizer_D hx)).mp hg'
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 M ⟨q, hq⟩
  have hq1 : q ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨d', hd', he⟩ := pow_mul_eq_of_mem_normalizer (h.Qb_le_normalizer_D hx hq) hd (2 ^ k)
  exact ⟨k, by rw [he, hq1, one_mul]; exact hd'⟩

end B1Hyp

end Hyp

end F53B1

end CFSG.Quasithin
