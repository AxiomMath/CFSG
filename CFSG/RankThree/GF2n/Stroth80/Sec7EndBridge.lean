module

public import CFSG.RankThree.GF2n.Stroth80.Sec7EndModel
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailSylow
public import CFSG.RankThree.GF2n.Stroth80.Sec310Nt
public import CFSG.RankThree.GF2n.Stroth80.Sec45Cases
public import CFSG.RankThree.GF2n.Stroth80.ClassicalQuasisimple
public import CFSG.RankThree.GF2n.Stroth80.Sec311Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement
open scoped commutatorElement Matrix

section F0

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem endg_inv_comm_mem (hc : Ctx M Q Z B) {t c : G} (hcM : c ∈ M)
    (hct : ⁅c, t⁆ ∈ Q) : ⁅c⁻¹, t⁆ ∈ Q := by
  have h1 : ⁅t, c⁆ ∈ Q := by
    have := Q.inv_mem hct
    rwa [commutatorElement_inv] at this
  have hmem : ⁅t, c⁆ ∈ conjSubgroup c Q := by
    rw [hc.conj_Q_eq hcM]
    exact h1
  have e : ⁅c⁻¹, t⁆ = c⁻¹ * ⁅t, c⁆ * c := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact mem_conjSubgroup.mp hmem

private theorem endg_q_mem (hc : Ctx M Q Z B) {t c : G} (hcM : c ∈ M)
    (hct : ⁅c, t⁆ ∈ Q) : c⁻¹ * t * c * t⁻¹ ∈ Q := by
  have := endg_inv_comm_mem hc hcM hct
  rwa [commutatorElement_def, inv_inv] at this

private theorem endg_key (hc : Ctx M Q Z B) {t c : G} (hcM : c ∈ M) (hct : ⁅c, t⁆ ∈ Q)
    {m : G} (hm : m ∈ M) (hT : t ∈ conjSubgroup m (LB M Q B)) :
    c * m ∈ M ∧ t ∈ conjSubgroup (c * m) (LB M Q B) := by
  refine ⟨M.mul_mem hcM hm, ?_⟩
  have hq : c⁻¹ * t * c * t⁻¹ ∈ conjSubgroup m Q := by
    rw [hc.conj_Q_eq hm]
    exact endg_q_mem hc hcM hct
  have hqm : m⁻¹ * (c⁻¹ * t * c * t⁻¹) * m ∈ Q := mem_conjSubgroup.mp hq
  have hT' : m⁻¹ * t * m ∈ LB M Q B := mem_conjSubgroup.mp hT
  have hQL : Q ≤ LB M Q B := le_sup_left
  rw [mem_conjSubgroup]
  have e : (c * m)⁻¹ * t * (c * m) = (m⁻¹ * (c⁻¹ * t * c * t⁻¹) * m) * (m⁻¹ * t * m) := by
    group
  rw [e]
  exact (LB M Q B).mul_mem (hQL hqm) hT'

private theorem endg_conj_Rt_le (hc : Ctx M Q Z B) {t c : G} (hcM : c ∈ M)
    (hct : ⁅c, t⁆ ∈ Q) : conjSubgroup c (Rt M (LB M Q B) t) ≤ Rt M (LB M Q B) t := by
  have key : ∀ m ∈ M, t ∈ conjSubgroup m (LB M Q B) →
      conjSubgroup c (conjSubgroup m (LB M Q B)) ≤ Rt M (LB M Q B) t := by
    intro m hm hT
    obtain ⟨hcm, hT'⟩ := endg_key hc hcM hct hm hT
    rw [← conjSubgroup_mul]
    exact conjSubgroup_le_Rt hcm hT'
  show conjSubgroup c (⨆ (m : G) (_ : m ∈ M) (_ : t ∈ conjSubgroup m (LB M Q B)),
    conjSubgroup m (LB M Q B)) ≤ _
  rw [conjSubgroup_iSup_eq]
  refine iSup_le fun m => ?_
  rw [conjSubgroup_iSup_eq]
  refine iSup_le fun hm => ?_
  rw [conjSubgroup_iSup_eq]
  exact iSup_le fun hT => key m hm hT

private theorem endg_conj_Vt_le (hc : Ctx M Q Z B) {t c : G} (hcM : c ∈ M)
    (hct : ⁅c, t⁆ ∈ Q) : conjSubgroup c (Vt M (LB M Q B) B Z t) ≤ Vt M (LB M Q B) B Z t := by
  have key : ∀ m ∈ M, t ∈ conjSubgroup m (LB M Q B) →
      conjSubgroup c (conjSubgroup m B) ≤ Vt M (LB M Q B) B Z t := by
    intro m hm hT
    obtain ⟨hcm, hT'⟩ := endg_key hc hcM hct hm hT
    rw [← conjSubgroup_mul]
    exact le_sup_of_le_right (le_iSup₂_of_le (c * m) hcm (le_iSup_of_le hT' le_rfl))
  show conjSubgroup c (Z ⊔ ⨆ (m : G) (_ : m ∈ M) (_ : t ∈ conjSubgroup m (LB M Q B)),
    conjSubgroup m B) ≤ _
  rw [conjSubgroup_sup', hc.conj_Z_eq hcM, conjSubgroup_iSup_eq]
  refine sup_le le_sup_left (iSup_le fun m => ?_)
  rw [conjSubgroup_iSup_eq]
  refine iSup_le fun hm => ?_
  rw [conjSubgroup_iSup_eq]
  exact iSup_le fun hT => key m hm hT

private theorem endg_le_of_conj {T : Subgroup G} {c : G} (h : ∀ x ∈ T, c * x * c⁻¹ ∈ T) :
    conjSubgroup c T ≤ T := by
  intro y hy
  have hx : c⁻¹ * y * c ∈ T := mem_conjSubgroup.mp hy
  have := h _ hx
  rwa [show c * (c⁻¹ * y * c) * c⁻¹ = y by group] at this

private theorem endg_conj_mem {T : Subgroup G} {c x : G} (h : conjSubgroup c T ≤ T)
    (hx : x ∈ T) : c * x * c⁻¹ ∈ T := by
  have h1 : c * x * c⁻¹ ∈ conjSubgroup c T := by
    rw [mem_conjSubgroup, show c⁻¹ * (c * x * c⁻¹) * c = x by group]
    exact hx
  exact h h1

private theorem endg_eq_of_le {T : Subgroup G} {c : G} (h : conjSubgroup c T ≤ T)
    (h' : conjSubgroup c⁻¹ T ≤ T) : conjSubgroup c T = T := by
  refine le_antisymm h ?_
  have e : conjSubgroup c (conjSubgroup c⁻¹ T) = T := by
    rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
  calc T = conjSubgroup c (conjSubgroup c⁻¹ T) := e.symm
    _ ≤ conjSubgroup c T := Subgroup.map_mono h'

private theorem endg_conj_CN_le (hc : Ctx M Q Z B) {t c : G} (hcM : c ∈ M)
    (hct : ⁅c, t⁆ ∈ Q) : conjSubgroup c (hc.CN t) ≤ hc.CN t := by
  refine endg_le_of_conj fun x hx => ?_
  obtain ⟨hxR, hxV⟩ := Ctx.mem_CN.mp hx
  refine Ctx.mem_CN.mpr ⟨endg_conj_mem (endg_conj_Rt_le hc hcM hct) hxR, fun v hv => ?_⟩
  have hct' : ⁅c⁻¹, t⁆ ∈ Q := endg_inv_comm_mem hc hcM hct
  have hv' : c⁻¹ * v * c ∈ Vt M (LB M Q B) B Z t := by
    have := endg_conj_mem (endg_conj_Vt_le hc (M.inv_mem hcM) hct') hv
    rwa [inv_inv] at this
  have e : ⁅c * x * c⁻¹, v⁆ = c * ⁅x, c⁻¹ * v * c⁆ * c⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact endg_conj_mem (hc.conj_Z_eq hcM).le (hxV _ hv')

theorem endg_F0_Rt (hc : Ctx M Q Z B) {t c : G} (hcM : c ∈ M) (hct : ⁅c, t⁆ ∈ Q) :
    conjSubgroup c (Rt M (LB M Q B) t) = Rt M (LB M Q B) t :=
  endg_eq_of_le (endg_conj_Rt_le hc hcM hct)
    (endg_conj_Rt_le hc (M.inv_mem hcM) (endg_inv_comm_mem hc hcM hct))

theorem endg_F0_Vt (hc : Ctx M Q Z B) {t c : G} (hcM : c ∈ M) (hct : ⁅c, t⁆ ∈ Q) :
    conjSubgroup c (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t :=
  endg_eq_of_le (endg_conj_Vt_le hc hcM hct)
    (endg_conj_Vt_le hc (M.inv_mem hcM) (endg_inv_comm_mem hc hcM hct))

theorem endg_F0_CN (hc : Ctx M Q Z B) {t c : G} (hcM : c ∈ M) (hct : ⁅c, t⁆ ∈ Q) :
    conjSubgroup c (hc.CN t) = hc.CN t :=
  endg_eq_of_le (endg_conj_CN_le hc hcM hct)
    (endg_conj_CN_le hc (M.inv_mem hcM) (endg_inv_comm_mem hc hcM hct))

end F0

private theorem endg14_mem_bar_iff {G : Type} [Group G] {M Q S : Subgroup G}
    [(Q.subgroupOf M).Normal] (hQS : Q ≤ S) (y : M) :
    QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q S ↔ (y : G) ∈ S := by
  constructor
  · intro hy
    obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.mp hy
    have h1 : s⁻¹ * y ∈ Q.subgroupOf M := QuotientGroup.eq.mp hsy
    have h2 : (s : G)⁻¹ * y ∈ S := hQS h1
    have e : (y : G) = s * ((s : G)⁻¹ * y) := by group
    rw [e]
    exact S.mul_mem hs h2
  · intro hy
    exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩

private theorem endg14_mem_conj_iff {G : Type} [Group G] {M Q S : Subgroup G}
    [(Q.subgroupOf M).Normal] (hQS : Q ≤ S) (m y : M) :
    QuotientGroup.mk' (Q.subgroupOf M) y ∈
        conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) m) (bar M Q S) ↔
      (y : G) ∈ conjSubgroup (m : G) S := by
  rw [mem_conjSubgroup, mem_conjSubgroup, ← map_inv, ← map_mul, ← map_mul,
    endg14_mem_bar_iff hQS]
  rfl

private theorem endg14_mk_normalizer_bar {G : Type} [Group G] {M Q S : Subgroup G}
    [(Q.subgroupOf M).Normal] (hQS : Q ≤ S) (y : M)
    (hy : (y : G) ∈ Subgroup.normalizer (S : Set G)) :
    QuotientGroup.mk' (Q.subgroupOf M) y ∈
      Subgroup.normalizer (bar M Q S : Set (↥M ⧸ Q.subgroupOf M)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) n
  rw [← map_inv, ← map_mul, ← map_mul, endg14_mem_bar_iff hQS, endg14_mem_bar_iff hQS]
  exact Subgroup.mem_normalizer_iff.mp hy (z : G)

private theorem endg14_commute_mem {G : Type} [Group G] {M Q : Subgroup G}
    [(Q.subgroupOf M).Normal] {x y : M}
    (h : QuotientGroup.mk' (Q.subgroupOf M) x * QuotientGroup.mk' (Q.subgroupOf M) y =
      QuotientGroup.mk' (Q.subgroupOf M) y * QuotientGroup.mk' (Q.subgroupOf M) x) :
    ⁅(x : G), (y : G)⁆ ∈ Q := by
  have h1 : ⁅QuotientGroup.mk' (Q.subgroupOf M) x, QuotientGroup.mk' (Q.subgroupOf M) y⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr h
  rw [← map_commutatorElement (QuotientGroup.mk' (Q.subgroupOf M)) x y,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem endg_isTI_bar {G : Type} [Group G] {M Q Z0 : Subgroup G} [(Q.subgroupOf M).Normal]
    (hQ : Q ≤ Z0) (hZM : Z0 ≤ M)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 →
      g ∈ Subgroup.normalizer (Z0 : Set G)) :
    IsTIOf (bar M Q Z0) := by
  unfold IsTIOf
  intro g u hu hu1 hgu
  obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) g
  obtain ⟨u', rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) u
  have hu'Z : (u' : G) ∈ Z0 := (endg14_mem_bar_iff hQ u').mp hu
  have hu'Q : (u' : G) ∉ Q := fun h => hu1 ((QuotientGroup.eq_one_iff u').mpr h)
  rw [← map_inv, ← map_mul, ← map_mul, endg14_mem_bar_iff hQ] at hgu
  exact endg14_mk_normalizer_bar hQ g' (hTI g' g'.2 u' hu'Z hu'Q hgu)

theorem endg_EgenX_le_bar {G : Type} [Group G] {M Q Z0 : Subgroup G} [(Q.subgroupOf M).Normal]
    (hQ : Q ≤ Z0) (hZM : Z0 ≤ M) : EgenX (bar M Q Z0) ≤ bar M Q (Egen M Q Z0) := by
  unfold EgenX
  refine iSup₂_le fun g hg => ?_
  obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) g
  intro y hy
  obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) y
  have hyc : (y' : G) ∈ conjSubgroup (g' : G) Z0 := (endg14_mem_conj_iff hQ g' y').mp hy
  have hle : conjSubgroup (g' : G) Z0 ≤ Egen M Q Z0 := by
    unfold Egen
    refine le_iSup_of_le (g' : G) (le_iSup_of_le g'.2 (le_iSup_of_le ?_ le_rfl))
    intro z hz y₁ hy₁
    have hzM : z ∈ M := hZM hz
    have hyM : y₁ ∈ M := by
      have h1 : (g' : G)⁻¹ * y₁ * (g' : G) ∈ M := hZM (mem_conjSubgroup.mp hy₁)
      have h2 := M.mul_mem (M.mul_mem g'.2 h1) (M.inv_mem g'.2)
      rwa [show (g' : G) * ((g' : G)⁻¹ * y₁ * (g' : G)) * (g' : G)⁻¹ = y₁ by group] at h2
    have hzbar : QuotientGroup.mk' (Q.subgroupOf M) (⟨z, hzM⟩ : M) ∈ bar M Q Z0 :=
      (endg14_mem_bar_iff hQ _).mpr hz
    have hybar : QuotientGroup.mk' (Q.subgroupOf M) (⟨y₁, hyM⟩ : M) ∈
        conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) g') (bar M Q Z0) :=
      (endg14_mem_conj_iff hQ g' ⟨y₁, hyM⟩).mpr hy₁
    exact endg14_commute_mem (hg _ hzbar _ hybar)
  exact Subgroup.mem_map.mpr ⟨y', Subgroup.mem_subgroupOf.mpr (hle hyc), rfl⟩

theorem endg_hE_bar {G : Type} [Group G] {M Q Z0 : Subgroup G} [(Q.subgroupOf M).Normal]
    (hQ : Q ≤ Z0) (hZM : Z0 ≤ M) (hE : ⁅Egen M Q Z0, Egen M Q Z0⁆ ≤ Z0) :
    ⁅EgenX (bar M Q Z0), EgenX (bar M Q Z0)⁆ ≤ bar M Q Z0 := by
  refine (Subgroup.commutator_mono (endg_EgenX_le_bar hQ hZM)
    (endg_EgenX_le_bar hQ hZM)).trans ?_
  refine Subgroup.commutator_le.mpr ?_
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg₁
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg₂
  rw [← map_commutatorElement (QuotientGroup.mk' (Q.subgroupOf M)) x y]
  exact Subgroup.mem_map.mpr ⟨⁅x, y⁆, Subgroup.mem_subgroupOf.mpr
    (hE (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hx)
      (Subgroup.mem_subgroupOf.mp hy))), rfl⟩

private theorem endgO_iSup_iSup_induction {G : Type} [Group G] {ι : Type} (R : ι → Prop)
    (F : ι → Subgroup G) {C : G → Prop} {x : G} (hx : x ∈ ⨆ (i : ι) (_ : R i), F i)
    (mem : ∀ i, R i → ∀ y ∈ F i, C y) (one : C 1) (mul : ∀ a b, C a → C b → C (a * b)) :
    C x :=
  Subgroup.iSup_induction (C := C) (x := x) (fun i : ι => ⨆ (_ : R i), F i) hx
    (fun i y hy => Subgroup.iSup_induction (C := C) (x := y) (fun _ : R i => F i) hy
      (fun j z hz => mem i j z hz) one mul)
    one mul

private theorem endgO_Q_le_CN {G : Type} [Group G] [Finite G]
    {M Q Z B : Subgroup G} (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) :
    Q ≤ hc.CN t :=
  fun x hx => Ctx.mem_CN.mpr ⟨hc.Q_le_Rt ht hx, fun v hv =>
    hc.hyp.toHyp79.comm_mem_V hx (hc.Vt_le_Q t hv)⟩

private theorem endgO_CN_le_M {G : Type} [Group G] [Finite G]
    {M Q Z B : Subgroup G} (hc : Ctx M Q Z B) (t : G) : hc.CN t ≤ M :=
  fun x hx => hc.Rt_le_M t (Ctx.mem_CN.mp hx).1

theorem endg_N_gen_bar {G : Type} [Group G] [Finite G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {t : G}
    (htL : t ∈ LB M Q B)
    (hN : hc.CN t = ⨆ (h : G) (_ : h ∈ Rt M (LB M Q B) t),
      conjSubgroup h (LB M Q B) ⊓ hc.CN t) :
    bar M Q (hc.CN t) = ⨆ (h : Mbar M Q) (_ : h ∈ bar M Q (Rt M (LB M Q B) t)),
      conjSubgroup h (bar M Q (LB M Q B)) ⊓ bar M Q (hc.CN t) := by
  classical
  have hQC : Q ≤ hc.CN t := endgO_Q_le_CN hc htL
  have hQL : Q ≤ LB M Q B := le_sup_left
  apply le_antisymm
  · have claim : ∀ x ∈ (⨆ (h : G) (_ : h ∈ Rt M (LB M Q B) t),
        conjSubgroup h (LB M Q B) ⊓ hc.CN t),
        ∃ y : M, (y : G) = x ∧ (QuotientGroup.mk' (Q.subgroupOf M) y : Mbar M Q) ∈
          ⨆ (h : Mbar M Q) (_ : h ∈ bar M Q (Rt M (LB M Q B) t)),
            conjSubgroup h (bar M Q (LB M Q B)) ⊓ bar M Q (hc.CN t) := by
      intro x hx
      refine endgO_iSup_iSup_induction (fun h : G => h ∈ Rt M (LB M Q B) t)
        (fun h => conjSubgroup h (LB M Q B) ⊓ hc.CN t)
        (C := fun x => ∃ y : M, (y : G) = x ∧ (QuotientGroup.mk' (Q.subgroupOf M) y : Mbar M Q) ∈
          ⨆ (h : Mbar M Q) (_ : h ∈ bar M Q (Rt M (LB M Q B) t)),
            conjSubgroup h (bar M Q (LB M Q B)) ⊓ bar M Q (hc.CN t)) hx ?_ ?_ ?_
      · intro h hh g hg
        have hgM : g ∈ M := endgO_CN_le_M hc t hg.2
        have hhM : h ∈ M := hc.Rt_le_M t hh
        refine ⟨⟨g, hgM⟩, rfl, ?_⟩
        have hmemR : (QuotientGroup.mk' (Q.subgroupOf M) ⟨h, hhM⟩ : Mbar M Q) ∈
            bar M Q (Rt M (LB M Q B) t) :=
          Subgroup.mem_map.mpr ⟨⟨h, hhM⟩, Subgroup.mem_subgroupOf.mpr hh, rfl⟩
        have h1 : (QuotientGroup.mk' (Q.subgroupOf M) ⟨g, hgM⟩ : Mbar M Q) ∈
            conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) ⟨h, hhM⟩)
              (bar M Q (LB M Q B)) :=
          (mk_mem_conj_bar_iff_sec4 hQL ⟨h, hhM⟩ ⟨g, hgM⟩).mpr hg.1
        have h2 : (QuotientGroup.mk' (Q.subgroupOf M) ⟨g, hgM⟩ : Mbar M Q) ∈
            bar M Q (hc.CN t) :=
          (mk_mem_bar_iff_sec4 hQC ⟨g, hgM⟩).mpr hg.2
        exact le_iSup₂ (f := fun (h' : Mbar M Q) (_ : h' ∈ bar M Q (Rt M (LB M Q B) t)) =>
          conjSubgroup h' (bar M Q (LB M Q B)) ⊓ bar M Q (hc.CN t))
          (QuotientGroup.mk' (Q.subgroupOf M) ⟨h, hhM⟩) hmemR
          (Subgroup.mem_inf.mpr ⟨h1, h2⟩)
      · exact ⟨1, rfl, by rw [map_one]; exact one_mem _⟩
      · rintro a b ⟨a', ha', hamem⟩ ⟨b', hb', hbmem⟩
        refine ⟨a' * b', by rw [Subgroup.coe_mul, ha', hb'], ?_⟩
        rw [map_mul]
        exact mul_mem hamem hbmem
    intro y hy
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨z, hz, hzmem⟩ := claim (y' : G) (hN.le (Subgroup.mem_subgroupOf.mp hy'))
    have hzy : z = y' := Subtype.ext hz
    rw [hzy] at hzmem
    exact hzmem
  · exact iSup₂_le fun h _ => inf_le_right

theorem endg_N_pgroup_bar {G : Type} [Group G] [Finite G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {t : G}
    (htL : t ∈ LB M Q B) (h2 : IsPGroup 2 ↥(hc.CN t)) : IsPGroup 2 ↥(bar M Q (hc.CN t)) := by
  have h3 : IsPGroup 2 ↥((hc.CN t).subgroupOf M) :=
    h2.of_equiv (Subgroup.subgroupOfEquivOfLe (endgO_CN_le_M hc t)).symm
  exact h3.map (QuotientGroup.mk' (Q.subgroupOf M))

theorem endg_N_normal_bar {G : Type} [Group G] [Finite G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {t : G}
    (htL : t ∈ LB M Q B) :
    ((bar M Q (hc.CN t)).subgroupOf (bar M Q (Rt M (LB M Q B) t))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  exact hc.bar_CN_conj_mem htL g.2 hn

private theorem endgP_le_centralizer {Γ : Type} [Group Γ] {C K : Subgroup Γ}
    (h : ∀ c ∈ C, ∀ x ∈ K, c * x = x * c) : K ≤ Subgroup.centralizer (C : Set Γ) :=
  fun x hx => Subgroup.mem_centralizer_iff.mpr fun c hc => h c hc x hx

private theorem endgP_false_of_centralizer {Γ : Type} [Group Γ] {C L : Subgroup Γ}
    (hC : IsComponent C) (hCL : C ≤ L) (hcent : L ≤ Subgroup.centralizer (C : Set Γ)) :
    False := by
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_isComponent hC
  apply hab
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp (hcent (hCL b.2)) a a.2

private theorem endgP_isComponent {Γ : Type} [Group Γ] {L X : Subgroup Γ} (hL : L.Normal)
    (hXL : X ≤ L) (hN : L ≤ Subgroup.normalizer (X : Set Γ)) (hq : CFSG.IsQuasisimple X) :
    IsComponent X :=
  ⟨hq, Subgroup.IsSubnormal.trans hXL
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hXL).mpr hN).isSubnormal hL.isSubnormal⟩

theorem endg_count_of_45 {G : Type} [Group G] [Finite G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (hcs : CompSimple (Mbar M Q)) (h45 : Stroth45Statement) :
    ∃ F : Finset (Subgroup (Mbar M Q)), F.card ≤ 3 ∧
      ∀ C : Subgroup (Mbar M Q), IsComponent C → C ∈ F := by
  classical
  obtain ⟨-, h⟩ := h45 G M Q Z B hc n hw hn hno hgen
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  have hSL2 : ∀ (K : Type) [Field K] [Finite K], Nat.card K = Nat.card Z →
      CFSG.IsQuasisimple ↥(StatedSL 2 K) := by
    intro K _ _ hK
    haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hK.trans hZ2)
    exact (classicalQuasisimpleStatement_holds K (by rw [hK]; exact hq4)).1 2 le_rfl
  have hqSL : ∀ X : Subgroup (Mbar M Q), IsSLModel 2 (Nat.card Z) ↥X →
      CFSG.IsQuasisimple ↥X := by
    rintro X ⟨K, hF, hFin, hK, ⟨e⟩⟩
    exact isQuasisimple_of_mulEquiv' e.symm (hSL2 K hK)
  rcases h with hq | ⟨X, Y, hsup, -, hcomm, hXq, hYSL⟩ |
    ⟨X₁, X₂, X₃, hsup, -, -, hc12, hc3, hX₁SL, hX₂SL, hX₃SL, -, -, -⟩
  ·
    refine ⟨{layer (Mbar M Q)}, ?_, fun C hC => ?_⟩
    · rw [Finset.card_singleton]
      norm_num
    · rw [Finset.mem_singleton]
      exact (eq_of_isQuasisimple_of_component hq (CFSG.LocalCores.component_le_layer hC) hC
        (CFSG.LocalCores.layer_le_normalizer hC)).symm
  ·
    have hEn : (layer (Mbar M Q)).Normal := by
      haveI := CFSG.LocalCores.layer_characteristic (G := Mbar M Q)
      infer_instance
    have hYq : CFSG.IsQuasisimple ↥Y := hqSL Y hYSL
    have hXl : X ≤ layer (Mbar M Q) := by rw [← hsup]; exact le_sup_left
    have hYl : Y ≤ layer (Mbar M Q) := by rw [← hsup]; exact le_sup_right
    have hXN : layer (Mbar M Q) ≤ Subgroup.normalizer (X : Set (Mbar M Q)) := by
      rw [← hsup]
      exact sup_le_normalizer_of_commute hcomm
    have hYN : layer (Mbar M Q) ≤ Subgroup.normalizer (Y : Set (Mbar M Q)) := by
      rw [← hsup, sup_comm]
      exact sup_le_normalizer_of_commute (fun y hy x hx => (hcomm x hx y hy).symm)
    have hXc : IsComponent X := endgP_isComponent hEn hXl hXN hXq
    have hYc : IsComponent Y := endgP_isComponent hEn hYl hYN hYq
    refine ⟨{X, Y}, (Finset.card_le_two).trans (by norm_num), fun C hC => ?_⟩
    by_contra hne
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hne
    obtain ⟨hCX, hCY⟩ := hne
    have hcent : X ⊔ Y ≤ Subgroup.centralizer (C : Set (Mbar M Q)) :=
      sup_le (endgP_le_centralizer fun c hc x hx => comm_of_ne_component hC hXc hCX c hc x hx)
        (endgP_le_centralizer fun c hc y hy => comm_of_ne_component hC hYc hCY c hc y hy)
    exact endgP_false_of_centralizer hC (CFSG.LocalCores.component_le_layer hC)
      (by rw [← hsup]; exact hcent)
  ·
    have hEn : (layer (Mbar M Q)).Normal := by
      haveI := CFSG.LocalCores.layer_characteristic (G := Mbar M Q)
      infer_instance
    have hq₁ : CFSG.IsQuasisimple ↥X₁ := hqSL X₁ hX₁SL
    have hq₂ : CFSG.IsQuasisimple ↥X₂ := hqSL X₂ hX₂SL
    have hq₃ : CFSG.IsQuasisimple ↥X₃ := hqSL X₃ hX₃SL
    have hc13 : ∀ x ∈ X₁, ∀ y ∈ X₃, x * y = y * x := fun x hx y hy =>
      hc3 x (Subgroup.mem_sup_left hx) y hy
    have hc23 : ∀ x ∈ X₂, ∀ y ∈ X₃, x * y = y * x := fun x hx y hy =>
      hc3 x (Subgroup.mem_sup_right hx) y hy
    have hc21 : ∀ x ∈ X₂, ∀ y ∈ X₁, x * y = y * x := fun x hx y hy => (hc12 y hy x hx).symm
    have hc31 : ∀ x ∈ X₃, ∀ y ∈ X₁ ⊔ X₂, x * y = y * x := fun x hx y hy =>
      (hc3 y hy x hx).symm
    have hN₁ : layer (Mbar M Q) ≤ Subgroup.normalizer (X₁ : Set (Mbar M Q)) := by
      rw [← hsup]
      exact sup_le (sup_le_normalizer_of_commute hc12)
        (le_sup_right.trans (sup_le_normalizer_of_commute hc13))
    have hN₂ : layer (Mbar M Q) ≤ Subgroup.normalizer (X₂ : Set (Mbar M Q)) := by
      rw [← hsup]
      exact sup_le (sup_le (le_sup_right.trans (sup_le_normalizer_of_commute hc21))
          Subgroup.le_normalizer)
        (le_sup_right.trans (sup_le_normalizer_of_commute hc23))
    have hN₃ : layer (Mbar M Q) ≤ Subgroup.normalizer (X₃ : Set (Mbar M Q)) := by
      rw [← hsup]
      exact sup_le (le_sup_right.trans (sup_le_normalizer_of_commute hc31))
        Subgroup.le_normalizer
    have hX₁l : X₁ ≤ layer (Mbar M Q) := by rw [← hsup]; exact le_sup_of_le_left le_sup_left
    have hX₂l : X₂ ≤ layer (Mbar M Q) := by rw [← hsup]; exact le_sup_of_le_left le_sup_right
    have hX₃l : X₃ ≤ layer (Mbar M Q) := by rw [← hsup]; exact le_sup_right
    have hc₁ : IsComponent X₁ := endgP_isComponent hEn hX₁l hN₁ hq₁
    have hc₂ : IsComponent X₂ := endgP_isComponent hEn hX₂l hN₂ hq₂
    have hc₃ : IsComponent X₃ := endgP_isComponent hEn hX₃l hN₃ hq₃
    refine ⟨{X₁, X₂, X₃}, Finset.card_le_three, fun C hC => ?_⟩
    by_contra hne
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hne
    obtain ⟨h1, h2, h3⟩ := hne
    have hcent : X₁ ⊔ X₂ ⊔ X₃ ≤ Subgroup.centralizer (C : Set (Mbar M Q)) :=
      sup_le (sup_le
          (endgP_le_centralizer fun c hc x hx => comm_of_ne_component hC hc₁ h1 c hc x hx)
          (endgP_le_centralizer fun c hc x hx => comm_of_ne_component hC hc₂ h2 c hc x hx))
        (endgP_le_centralizer fun c hc x hx => comm_of_ne_component hC hc₃ h3 c hc x hx)
    exact endgP_false_of_centralizer hC (CFSG.LocalCores.component_le_layer hC)
      (by rw [← hsup]; exact hcent)

section BridgeCore

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem endg_bar_mono {S T : Subgroup G} (h : S ≤ T) : bar M Q S ≤ bar M Q T :=
  Subgroup.map_mono fun x hx => h hx

theorem endg_endHyp (h34 : Stroth34Statement) (h44 : Stroth44Statement)
    (h45 : Stroth45Statement) (h311a : Stroth311aStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hLBZ : Z0 ≤ LB M Q B) (hcardZ0 : Nat.card Z0 = Nat.card Q * Nat.card Z)
    (hlarge : Nat.card Q * Nat.card Z < Nat.card ↥(hc.CN t))
    (hlin : EndLinModel (Mbar M Q) (bar M Q (H0 M Z)) (bar M Q Z0))
    (hquot : ∃ (S : Type) (_ : Group S) (π : ↥(bar M Q (Rt M (LB M Q B) t)) →* S),
      Function.Surjective π ∧
      (∀ r : ↥(bar M Q (Rt M (LB M Q B) t)), π r = 1 ↔ (r : Mbar M Q) ∈ bar M Q (hc.CN t)) ∧
      IsSimpleGroup S ∧ 16 ∣ Nat.card S ∧
      ∀ p : ℕ, p.Prime → p ∣ Nat.card Z ^ 2 + 1 → p ∣ Nat.card S) :
    EndgameHyp (Mbar M Q) (bar M Q Z0) (bar M Q (Rt M (LB M Q B) t)) (bar M Q (hc.CN t))
      (bar M Q (H0 M Z)) (QuotientGroup.mk (⟨t, hc.LB_le_M hs.mem⟩ : ↥M)) := by
  classical
  have ht : t ∈ LB M Q B := hs.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have hQN : Q ≤ hc.CN t := fun x hx =>
    Ctx.mem_CN.mpr ⟨hQR hx, fun v hv => hc.hyp.toHyp79.comm_mem_V hx (hc.Vt_le_Q t hv)⟩
  have hNM : hc.CN t ≤ M := fun x hx => hRM (Ctx.mem_CN.mp hx).1
  let tm : ↥M := ⟨t, htM⟩
  have hcardA : Nat.card (bar M Q Z0) = Nat.card Z := by
    have h1 := bar_card_mul_card_of_le (M := M) hQZ0 hZ0M
    rw [hcardZ0] at h1
    have h2 : Nat.card (bar M Q Z0) * Nat.card Q = Nat.card Z * Nat.card Q := by
      rw [h1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  obtain ⟨S, hS, π, hπs, hπk, hSs, h16, hSp⟩ := hquot
  have hRne : Rt M (LB M Q B) t ≠ LB M Q B := by
    intro hR
    have hbar : bar M Q (Rt M (LB M Q B) t) = bar M Q (LB M Q B) := by rw [hR]
    have hmem : ∀ x : ↥(bar M Q (Rt M (LB M Q B) t)), (x : Mbar M Q) ∈ bar M Q (LB M Q B) :=
      fun x => Eq.mp (congrArg (fun T : Subgroup (Mbar M Q) => (x : Mbar M Q) ∈ T) hbar) x.2
    haveI : IsMulCommutative S := ⟨⟨fun a b => by
      obtain ⟨x, rfl⟩ := hπs a
      obtain ⟨y, rfl⟩ := hπs b
      rw [← map_mul, ← map_mul]
      congr 1
      have h' := hc.isElemAbelian_bar_LB.1.is_comm.comm ⟨(x : Mbar M Q), hmem x⟩
        ⟨(y : Mbar M Q), hmem y⟩
      have h2 := congrArg Subtype.val h'
      exact Subtype.ext h2⟩⟩
    have hprime := Group.is_simple_iff_prime_card.mp hSs
    rcases Nat.Prime.eq_one_or_self_of_dvd hprime 16 h16 with h | h
    · omega
    · rw [← h] at hprime
      norm_num at hprime
  have hN311 := h311a G M Q Z B hc n hs.width hs.n_gt hs.noA2 hs.gen
    t ht hs.notQ hRne
  have hcs := hc.compSimple h34 h44 hs.width hs.n_gt hs.noA2 hs.gen
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  refine
    { o2 := hc.pCore_two_Mbar
      H_normal := hc.normal_bar_H0
      A_le_R := endg_bar_mono hZ0.le
      R_le_H := endg_bar_mono (hc.Rt_le_H0 t)
      t_mem := Subgroup.mem_map.mpr ⟨tm, Subgroup.mem_subgroupOf.mpr htZ0, rfl⟩
      t_ne := fun h => hs.notQ
        (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h))
      A_sq := fun a ha => by
        have := hc.isElemAbelian_bar_LB.2 a (endg_bar_mono hLBZ ha)
        rwa [pow_two] at this
      A_comm := fun a ha b hb => congrArg Subtype.val
        (hc.isElemAbelian_bar_LB.1.is_comm.comm ⟨a, endg_bar_mono hLBZ ha⟩
          ⟨b, endg_bar_mono hLBZ hb⟩)
      A_cent := fun a ha r hr => by
        obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp ha
        exact endg_comm_centre hZ0 hRM (Subgroup.mem_subgroupOf.mp hz) hr
      cent_le := fun x hx hxc => by
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
        have hyR : (y : G) ∈ Rt M (LB M Q B) t := Subgroup.mem_subgroupOf.mp hy
        refine Subgroup.mem_map.mpr ⟨y, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
        refine (hZ0 _).mpr ⟨hyR, fun r hr => ?_⟩
        have hrM : r ∈ M := hRM hr
        have hcomm := hxc (QuotientGroup.mk ⟨r, hrM⟩)
          (Subgroup.mem_map.mpr ⟨⟨r, hrM⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩)
        exact (mk_commute_iff y ⟨r, hrM⟩).mp hcomm
      A_card := ⟨jj, ?_, ?_⟩
      N_le := hc.bar_CN_le_bar_Rt t
      N_normal := endg_N_normal_bar hc ht
      N_pgroup := endg_N_pgroup_bar hc ht (hc.isPGroup_CN_of_311 h34 hs hN311)
      N_gen := ⟨bar M Q (LB M Q B), fun x hx y hy => congrArg Subtype.val
        (hc.isElemAbelian_bar_LB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩),
        endg_N_gen_bar hc ht hN311⟩
      N_large := ?_
      F0 := fun c hct => by
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
        have hcom : ⁅(y : G), t⁆ ∈ Q := (mk_commute_iff y tm).mp hct
        exact ⟨mk_mem_normalizer_bar_of_normalizer hQR y
            (conjSubgroup_eq_self_iff.mp (endg_F0_Rt hc y.2 hcom)),
          mk_mem_normalizer_bar_of_normalizer hQN y
            (conjSubgroup_eq_self_iff.mp (endg_F0_CN hc y.2 hcom))⟩
      F5 := fun Y hY hYH hodd => h44 G M Q Z B hc n hs.width hs.n_gt
        hs.noA2 hs.gen Y hYH
        (fun l _ => (Subgroup.normalizer_eq_top_iff.mpr hY) ▸ Subgroup.mem_top l) hodd
      N1 := endg_commAll_of_linModel hlin
      N2 := endg_centOne_of_linModel hlin
      comps := hcs
      count := endg_count_of_45 hc hs.width hs.n_gt hs.noA2 hs.gen
        hcs h45
      quot := ⟨S, hS, π, hπs, hπk, hSs, h16, fun p hp hpd =>
        hSp p hp (by rw [← hcardA]; exact hpd)⟩ }
  · have h4 : 4 ≤ 2 ^ jj := hZ2 ▸ hc.hyp.q4
    by_contra hlt
    have hj : jj ≤ 1 := by omega
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hj
    omega
  · rw [hcardA, hZ2]
  · have hNcard := bar_card_mul_card_of_le (M := M) hQN hNM
    have hlt := hlarge
    rw [← hNcard] at hlt
    rw [hcardA]
    have : Nat.card Z * Nat.card Q < Nat.card (bar M Q (hc.CN t)) * Nat.card Q := by
      rw [mul_comm]
      exact hlt
    exact Nat.lt_of_mul_lt_mul_right this

end BridgeCore

end CFSG.RankThree.GF2n.Stroth80
