module

public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutLocal
public import CFSG.RankThree.PartTwo.Sec12.Item127
public import CFSG.RankThree.PartTwo.Sec12.Item124Bar

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint
open scoped commutatorElement

section IStructure

variable {G : Type} [Group G] [Finite G] {A E U : Subgroup G} {c : G} {L : Subgroup G}


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem CoverOut.iCore_structure (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) {a : G}
    (hfr : Frame217 E c L a) :
    Nonempty (↥(iCore L a) ≃* alternatingGroup (Fin 6)) ∧
    (∀ q ∈ A, q ∈ Subgroup.normalizer ((iCore L a : Subgroup G) : Set G)) ∧
    (∀ y ∈ iCore L a, (∀ x ∈ iCore L a, y * x = x * y) → y = 1) ∧
    (∀ x ∈ iCore L a, ∀ z ∈ dGroup a c ⊓ L, x * z = z * x) ∧
    Nat.card ↥(A ⊓ iCore L a : Subgroup G) = 9 ∧
    A ⊓ Subgroup.centralizer ((iCore L a : Subgroup G) : Set G) = dGroup a c := by
  obtain ⟨l, I', hlA, ⟨i, hai⟩, hl1, hl3, hlnc, hI'C, hI'perf, ⟨φ⟩, hI, hI'max, hD3, hDI,
    hDcomm, hCeq, hDeq, hDL⟩ := h.local_frame h45 hfr
  have hZI' := center_eq_bot_of_equiv_alt6 I' φ
  have hab := isElemAbelian_iff.1 h.isElemAbelian_A
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hab.1 x hx y hy
  have hcL : ∀ y ∈ L, c * y = y * c := h.c_comm
  have hczL : ∀ (k : ℤ), ∀ y ∈ L, c ^ k * y = y * c ^ k := fun k y hy =>
    ((show Commute c y from hcL y hy).zpow_left k).eq
  have hmemI : ∀ x ∈ iCore L a, ∃ y : ↥L, y ∈ I' ∧ (y : G) = x := by
    intro x hx
    rw [hI] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    exact ⟨y, hy, hyx⟩
  have hIL : ∀ y ∈ I', (y : G) ∈ iCore L a := fun y hy => by rw [hI]; exact ⟨y, hy, rfl⟩
  have hlI : ∀ z ∈ I', (l : G) * z = z * (l : G) := by
    intro z hz
    have : z * l = l * z := Subgroup.mem_centralizer_singleton_iff.1 (hI'C hz)
    exact (congrArg Subtype.val this).symm
  have hlIj : ∀ z ∈ I', ∀ j : ℤ, (l : G) ^ j * z = z * (l : G) ^ j := fun z hz j =>
    ((show Commute (l : G) z from hlI z hz).zpow_left j).eq
  have hFC : ∀ f : G, f ∈ A → ∀ hfL : f ∈ L, ∃ j : ℤ, ∃ y : ↥L, y ∈ I' ∧ f = (l : G) ^ j * y := by
    intro f hfA hfL
    have hfl : (⟨f, hfL⟩ : ↥L) * l = l * ⟨f, hfL⟩ := Subtype.ext (hcommA f hfA l hlA)
    have hmem : (⟨f, hfL⟩ : ↥L) ∈ Subgroup.zpowers l ⊔ I' := by
      rw [hCeq]; exact Subgroup.mem_centralizer_singleton_iff.2 hfl
    obtain ⟨x, hx, y, hy, hxy⟩ := (mem_sup_of_commute
      (fun x hx y hy => hDcomm x hx y (hI'C hy))).1 hmem
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    refine ⟨j, y, hy, ?_⟩
    have := congrArg Subtype.val hxy
    simpa using this.symm
  have hIcomm : ∀ x ∈ iCore L a, ∀ z ∈ dGroup a c ⊓ L, x * z = z * x := by
    intro x hx z hz
    rw [hDL] at hz
    obtain ⟨y, hy, rfl⟩ := hmemI x hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (hlIj y hy j).symm
  have hcenI : ∀ y ∈ iCore L a, (∀ x ∈ iCore L a, y * x = x * y) → y = 1 := by
    intro y hy hycomm
    obtain ⟨y', hy', rfl⟩ := hmemI y hy
    have hcen : (⟨y', hy'⟩ : ↥I') ∈ Subgroup.center ↥I' := by
      rw [Subgroup.mem_center_iff]
      intro z
      have := hycomm (z : G) (hIL z z.2)
      exact Subtype.ext (Subtype.ext this.symm)
    rw [hZI', Subgroup.mem_bot] at hcen
    have := congrArg (fun w : ↥I' => ((w : ↥L) : G)) hcen
    simpa using this
  have hlC : (l : G) ∈ Subgroup.centralizer ((iCore L a : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hmemI x hx
    exact (hlI y hy).symm
  have hcC : c ∈ Subgroup.centralizer ((iCore L a : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hmemI x hx
    exact (hcL y y.2).symm
  have hl3' : (l : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hl3
    simpa using this
  have hl1' : (l : G) ≠ 1 := fun h1 => hl1 (Subtype.ext h1)
  have hDA : dGroup a c ≤ A := by
    rw [hDeq]
    exact sup_le (Subgroup.zpowers_le.2 hlA) (Subgroup.zpowers_le.2 h.c_mem_A)
  refine ⟨⟨(MulEquiv.subgroupCongr hI).trans
      ((I'.equivMapOfInjective L.subtype L.subtype_injective).symm.trans φ)⟩, ?_, ?_, hIcomm, ?_, ?_⟩
  ·
    intro q hq
    refine mem_normalizer_of_forall_conj_mem fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hmemI x hx
    obtain ⟨f, hf, k, hqk⟩ := h.decomp_A h45 q hq
    obtain ⟨j, y₀, hy₀, hfj⟩ := hFC f hf.1 hf.2
    have hconj : q * (y : G) * q⁻¹ = ((y₀ * y * y₀⁻¹ : ↥L) : G) := by
      have h1 : q * (y : G) * q⁻¹ = f * (y : G) * f⁻¹ := by
        rw [hqk]
        calc f * c ^ k * (y : G) * (f * c ^ k)⁻¹
            = f * (c ^ k * (y : G)) * (c ^ k)⁻¹ * f⁻¹ := by group
          _ = f * ((y : G) * c ^ k) * (c ^ k)⁻¹ * f⁻¹ := by rw [hczL k y y.2]
          _ = f * (y : G) * f⁻¹ := by group
      rw [h1, hfj]
      have h2 : (l : G) ^ j * (y₀ : G) * (y : G) * ((l : G) ^ j * (y₀ : G))⁻¹ =
          ((l : G) ^ j) * ((y₀ : G) * (y : G) * (y₀ : G)⁻¹) * ((l : G) ^ j)⁻¹ := by group
      have hz : (y₀ * y * y₀⁻¹ : ↥L) ∈ I' := I'.mul_mem (I'.mul_mem hy₀ hy) (I'.inv_mem hy₀)
      have hzc := hlIj _ hz j
      have hz' : ((y₀ * y * y₀⁻¹ : ↥L) : G) = (y₀ : G) * (y : G) * (y₀ : G)⁻¹ := rfl
      rw [h2, ← hz', hzc]
      group
    rw [hconj]
    exact hIL _ (I'.mul_mem (I'.mul_mem hy₀ hy) (I'.inv_mem hy₀))
  · exact hcenI
  ·
    set P : Subgroup G := Subgroup.zpowers (l : G) with hP
    set Q : Subgroup G := A ⊓ iCore L a with hQ
    have hIl : iCore L a ≤ L := fun x hx => by
      obtain ⟨y, -, rfl⟩ := hmemI x hx
      exact y.2
    have hPF : P ≤ A ⊓ L := le_inf (Subgroup.zpowers_le.2 hlA) (Subgroup.zpowers_le.2 l.2)
    have hQF : Q ≤ A ⊓ L := fun x hx => ⟨hx.1, hIl hx.2⟩
    have hsup : P ⊔ Q = A ⊓ L := by
      apply le_antisymm (sup_le hPF hQF)
      intro f hf
      obtain ⟨j, y, hy, hfj⟩ := hFC f hf.1 hf.2
      have hyA : (y : G) ∈ A := by
        have : (y : G) = ((l : G) ^ j)⁻¹ * f := by rw [hfj]; group
        rw [this]
        exact A.mul_mem (A.inv_mem (Subgroup.zpow_mem _ hlA j)) hf.1
      rw [hfj]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers _ j))
        (Subgroup.mem_sup_right ⟨hyA, hIL y hy⟩)
    have hdisj : Disjoint P Q := by
      rw [Subgroup.disjoint_def]
      intro x hxP hxQ
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxP
      obtain ⟨y, hy, hyx⟩ := hmemI _ hxQ.2
      have hy' : (l ^ j : ↥L) = y := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hyx.symm)
      have hlj : l ^ j ∈ I' := hy' ▸ hy
      have h1 : (l ^ j : ↥L) = 1 :=
        Subgroup.disjoint_def.1 hDI (Subgroup.zpow_mem_zpowers l j) hlj
      have := congrArg Subtype.val h1
      simpa using this
    have hN : Q ≤ Subgroup.normalizer (P : Set G) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer (P : Set G))
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact hcommA x (hPF hx).1 q hq.1
    have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer P Q hN hdisj
    rw [hsup, h.card_inf_eq h45, hP, Nat.card_zpowers, orderOf_eq_prime hl3' hl1'] at hcard
    omega
  ·
    apply le_antisymm
    · rintro q ⟨hqA, hqC⟩
      obtain ⟨f, hf, k, hqk⟩ := h.decomp_A h45 q hqA
      have hckC : c ^ k ∈ Subgroup.centralizer ((iCore L a : Subgroup G) : Set G) :=
        Subgroup.zpow_mem _ hcC k
      have hfC : f ∈ Subgroup.centralizer ((iCore L a : Subgroup G) : Set G) := by
        have : f = q * (c ^ k)⁻¹ := by rw [hqk]; group
        rw [this]
        exact Subgroup.mul_mem _ hqC (Subgroup.inv_mem _ hckC)
      obtain ⟨j, y, hy, hfj⟩ := hFC f hf.1 hf.2
      have hyC : (y : G) ∈ Subgroup.centralizer ((iCore L a : Subgroup G) : Set G) := by
        have : (y : G) = ((l : G) ^ j)⁻¹ * f := by rw [hfj]; group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.zpow_mem _ hlC j)) hfC
      have hy1 : (y : G) = 1 := hcenI _ (hIL y hy) (fun x hx =>
        ((Subgroup.mem_centralizer_iff.1 hyC) x hx).symm)
      rw [hqk, hfj, hy1, mul_one, hDeq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers _ j))
        (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers c k))
    · refine le_inf hDA ?_
      rw [hDeq]
      exact sup_le (Subgroup.zpowers_le.2 hlC) (Subgroup.zpowers_le.2 hcC)

theorem centralizer_singleton_eq_of_mem_zpowers {X : Type*} [Group X] {x y : X}
    (hxy : x ∈ Subgroup.zpowers y) (hyx : y ∈ Subgroup.zpowers x) :
    Subgroup.centralizer ({x} : Set X) = Subgroup.centralizer ({y} : Set X) := by
  have key : ∀ {u v : X}, u ∈ Subgroup.zpowers v →
      Subgroup.centralizer ({v} : Set X) ≤ Subgroup.centralizer ({u} : Set X) := by
    intro u v huv z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 huv
    rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    exact ((show Commute z v from hz).zpow_right k).eq
  exact le_antisymm (key hyx) (key hxy)

theorem isSolvable_inSubgroup_theta {X : Type*} [Group X] [Finite X] (J : Subgroup X) :
    Group.IsSolvable ↥(inSubgroup (aschbacherSolvableCore 3) J) := by
  obtain ⟨hs, -⟩ := solvable_prime_complement_core_characterization (H := ↥J) Nat.prime_three
  unfold inSubgroup
  have e := (aschbacherSolvableCore 3 ↥J).equivMapOfInjective J.subtype J.subtype_injective
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

theorem inf_theta_eq_bot_of_A6 {X : Type*} [Group X] [Finite X] {I J : Subgroup X} (hIJ : I ≤ J)
    (e : ↥I ≃* alternatingGroup (Fin 6)) :
    I ⊓ inSubgroup (aschbacherSolvableCore 3) J = ⊥ := by
  have hA6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  haveI : IsSimpleGroup ↥I := @MulEquiv.isSimpleGroup _ _ _ _ hA6 e
  set N : Subgroup X := I ⊓ inSubgroup (aschbacherSolvableCore 3) J with hN
  have hNnorm : (N.subgroupOf I).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro x hx
    exact mem_normalizer_inf' (Subgroup.le_normalizer hx)
      (Sec6.normalizer_le_normalizer_theta J (Subgroup.le_normalizer (hIJ hx)))
  haveI := hNnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf I) with h1 | h1
  · rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.1⟩ : ↥I) ∈ N.subgroupOf I := Subgroup.mem_subgroupOf.2 hx
    rw [h1, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  · exfalso
    have hIθ : I ≤ inSubgroup (aschbacherSolvableCore 3) J := by
      intro x hx
      have : (⟨x, hx⟩ : ↥I) ∈ N.subgroupOf I := by rw [h1]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 this).2
    haveI : Group.IsSolvable ↥(inSubgroup (aschbacherSolvableCore 3) J) :=
      isSolvable_inSubgroup_theta J
    have hsol : Group.IsSolvable ↥I :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hIθ)
        (Subgroup.inclusion_injective hIθ)
    have : Group.IsSolvable (alternatingGroup (Fin 6)) :=
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]; decide
    exact not_isSolvable_of_simple (Q := alternatingGroup (Fin 6)) (by rw [h360]; norm_num) this

theorem mem_thetaQuotCentralizer_of_conj {X : Type*} [Group X] [Finite X] {J : Subgroup X} {s x : X}
    (hx : x ∈ Sec4.thetaQuotCentralizer (J.map (MulAut.conj s).toMonoidHom)) :
    s⁻¹ * x * s ∈ Sec4.thetaQuotCentralizer J := by
  obtain ⟨hxN, hxl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hx
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨?_, fun l hl => ?_⟩
  · refine mem_normalizer_of_forall_conj_mem fun y hy => ?_
    have hsy : s * y * s⁻¹ ∈ J.map (MulAut.conj s).toMonoidHom := ⟨y, hy, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.1 hxN _).1 hsy
    obtain ⟨z, hz, hzeq⟩ := h1
    have : z = s⁻¹ * x * s * y * (s⁻¹ * x * s)⁻¹ := by
      have h2 : s * z * s⁻¹ = x * (s * y * s⁻¹) * x⁻¹ := hzeq
      calc z = s⁻¹ * (s * z * s⁻¹) * s := by group
        _ = s⁻¹ * (x * (s * y * s⁻¹) * x⁻¹) * s := by rw [h2]
        _ = s⁻¹ * x * s * y * (s⁻¹ * x * s)⁻¹ := by group
    rw [← this]
    exact hz
  · have hsl : s * l * s⁻¹ ∈ J.map (MulAut.conj s).toMonoidHom := ⟨l, hl, rfl⟩
    have h1 := hxl _ hsl
    have hθ : inSubgroup (aschbacherSolvableCore 3) (J.map (MulAut.conj s).toMonoidHom) =
        (inSubgroup (aschbacherSolvableCore 3) J).map (MulAut.conj s).toMonoidHom :=
      (CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_aschbacherSolvableCore_mulEquiv
        Nat.prime_three (MulAut.conj s) J).symm
    rw [hθ] at h1
    obtain ⟨t, ht, hteq⟩ := h1
    have h3 : s * t * s⁻¹ = (s * l * s⁻¹)⁻¹ * (x * (s * l * s⁻¹) * x⁻¹) := hteq
    have : t = l⁻¹ * (s⁻¹ * x * s * l * (s⁻¹ * x * s)⁻¹) := by
      calc t = s⁻¹ * (s * t * s⁻¹) * s := by group
        _ = s⁻¹ * ((s * l * s⁻¹)⁻¹ * (x * (s * l * s⁻¹) * x⁻¹)) * s := by rw [h3]
        _ = l⁻¹ * (s⁻¹ * x * s * l * (s⁻¹ * x * s)⁻¹) := by group
    rw [← this]
    exact ht

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem CoverOut.iCore_eq_of_zpowers_eq_inf (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) {a : G}
    (hfr : Frame217 E c L a) {d : G} (hd : Subgroup.zpowers d = dGroup a c ⊓ L) :
    iCore L d = iCore L a := by
  obtain ⟨l, hlA, ⟨i, hai⟩, hl1, hl3, hlnc, hDeq, hDL, hDA, hDE⟩ := h.dgroup_decomp h45 hfr
  have hdDL : d ∈ dGroup a c ⊓ L := hd ▸ Subgroup.mem_zpowers d
  have hdl : d ∈ Subgroup.zpowers (l : G) := hDL ▸ hdDL
  have hd1 : d ≠ 1 := (h.frame_of_zpowers_eq_inf h45 hfr hd).1
  have hld : (l : G) ∈ Subgroup.zpowers d := mem_zpowers_of_mem_zpowers hl3 hd1 hdl
  have h1 := h.centralizer_inf_eq (l := l) (i := i) (a := a) hai
  have h2 := h.centralizer_inf_eq (l := ⟨d, hdDL.2⟩) (i := 0) (a := d) (by simp)
  have hcent : Subgroup.centralizer ({(⟨d, hdDL.2⟩ : ↥L)} : Set ↥L) =
      Subgroup.centralizer ({l} : Set ↥L) := by
    apply centralizer_singleton_eq_of_mem_zpowers
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hdl
      exact Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa using hk)⟩
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hld
      exact Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa using hk)⟩
  unfold iCore
  rw [h2, h1, hcent]

theorem CoverOut.card_dGroup (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) {a : G}
    (hfr : Frame217 E c L a) : Nat.card ↥(dGroup a c) = 9 := by
  obtain ⟨l, hlA, ⟨i, hai⟩, hl1, hl3, hlnc, hDeq, hDL, hDA, hDE⟩ := h.dgroup_decomp h45 hfr
  have hab := isElemAbelian_iff.1 h.isElemAbelian_A
  have hl1' : (l : G) ≠ 1 := fun h1 => hl1 (Subtype.ext h1)
  have hN : Subgroup.zpowers c ≤ Subgroup.normalizer ((Subgroup.zpowers (l : G) : Subgroup G) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer ((Subgroup.zpowers (l : G) : Subgroup G) : Set G))
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact ((show Commute (l : G) c from hab.1 _ hlA c h.c_mem_A).zpow_left k).eq
  have hdisj : Disjoint (Subgroup.zpowers (l : G)) (Subgroup.zpowers c) := by
    rw [Subgroup.disjoint_def]
    intro x hxl hxc
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxl
    exact h.eq_one_of_mem_zpowers_of_mem hxc (L.zpow_mem l.2 j)
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN hdisj
  rw [hDeq, hcard, Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hl3 hl1',
    orderOf_eq_prime h.c_cubed h.c_ne_one]

theorem not_isSolvable_of_equiv_alt6 {X : Type*} [Group X] {I : Subgroup X}
    (e : ↥I ≃* alternatingGroup (Fin 6)) : ¬ Group.IsSolvable ↥I := by
  intro hs
  have hs' : Group.IsSolvable (alternatingGroup (Fin 6)) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  have hA6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]; decide
  exact not_isSolvable_of_simple (Q := alternatingGroup (Fin 6)) (by rw [h360]; norm_num) hs'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem CoverOut.normalizes_D (h48 : Sec4.Item4_8) (h45 : Sec4.Item4_5) (h : CoverOut A E U c L)
    {a : G} (hfr : Frame217 E c L a) {d : G} (hd : Subgroup.zpowers d = dGroup a c ⊓ L)
    (hJ1 : ∀ J ∈ thetaComponentsAt 3 d, iCore L a ≤ J → c ∈ Sec4.thetaQuotCentralizer J) :
    ∀ s ∈ Subgroup.normalizer (A : Set G), s * d = d * s →
      s ∈ Subgroup.normalizer ((dGroup a c : Subgroup G) : Set G) := by
  intro s hsA hsd
  obtain ⟨⟨e⟩, hIA, hIcen, hIcomm, hcardAI, hAC⟩ := h.iCore_structure h45 hfr
  obtain ⟨hd1, hfrd⟩ := h.frame_of_zpowers_eq_inf h45 hfr hd
  have hiC := h.iCore_eq_of_zpowers_eq_inf h45 hfr hd
  have hD9 := h.card_dGroup h45 hfr
  obtain ⟨l, hlA, ⟨i, hai⟩, hl1, hl3, hlnc, hDeq, hDL, hDA, hDE⟩ := h.dgroup_decomp h45 hfr
  have hdDL : d ∈ dGroup a c ⊓ L := hd ▸ Subgroup.mem_zpowers d
  have hdl : d ∈ Subgroup.zpowers (l : G) := hDL ▸ hdDL
  have hld : (l : G) ∈ Subgroup.zpowers d := mem_zpowers_of_mem_zpowers hl3 hd1 hdl
  have hDeq' : dGroup a c = Subgroup.zpowers d ⊔ Subgroup.zpowers c := by
    rw [hDeq]
    congr 1
    exact le_antisymm (Subgroup.zpowers_le.2 hld) (Subgroup.zpowers_le.2 hdl)
  have hab := isElemAbelian_iff.1 h.isElemAbelian_A
  have hdA : d ∈ A := hDA hdDL.1
  have hIperf : ⁅iCore L a, iCore L a⁆ = iCore L a := perfect_of_equiv_alt6 _ e
  have hIs : ¬ Group.IsSolvable ↥(iCore L a) := not_isSolvable_of_equiv_alt6 e
  obtain ⟨J, hJ, hIJ'⟩ := h.exists_component_ge_iCore h48 h45 hfrd
  rw [hiC] at hIJ'
  have hIJ : iCore L a ≤ J := hIJ'
  have hcJ := hJ1 J hJ hIJ
  have hJC : J ≤ Subgroup.centralizer ({d} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hJ
  have hqnd : ∀ q : G, q * d = d * q →
      q ∈ Subgroup.normalizer ((Subgroup.zpowers d : Subgroup G) : Set G) := by
    intro q hq
    have hqC : q ∈ Subgroup.centralizer ((Subgroup.zpowers d : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact ((show Commute d q from hq.symm).zpow_left k).eq
    exact Subgroup.centralizer_le_normalizer ((Subgroup.zpowers d : Subgroup G) : Set G) hqC
  have hAJ : ∀ q ∈ A, q ∈ Subgroup.normalizer (J : Set G) := by
    intro q hq
    have hJ' := CFSG.RankThree.PartOne.Sec12TwoAssembly.conj_mem_thetaComponentsAt
      Nat.prime_three (hqnd q (hab.1 q hq d hdA)) hJ
    have hIJ2 : iCore L a ≤ J ⊓ J.map (MulAut.conj q).toMonoidHom := by
      intro x hx
      refine ⟨hIJ hx, ⟨q⁻¹ * x * q, hIJ ?_, ?_⟩⟩
      swap
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem (hIA q hq)) x).1 hx
      simpa using this
    have heq := eq_of_perfect_le_inf_thetaComponentsAt hJ hJ' hIJ2 hIperf hIs
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact heq.symm
  have hAQ : A ⊓ Sec4.thetaQuotCentralizer J = dGroup a c := by
    apply le_antisymm
    · rintro q ⟨hqA, hqQ⟩
      have hqC : q ∈ Subgroup.centralizer ((iCore L a : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have h1 := (Sec6.mem_thetaQuotCentralizer_iff.1 hqQ).2 x (hIJ hx)
        have h2 : x⁻¹ * (q * x * q⁻¹) ∈ iCore L a :=
          (iCore L a).mul_mem ((iCore L a).inv_mem hx)
            ((Subgroup.mem_normalizer_iff.1 (hIA q hqA) x).1 hx)
        have h3 : x⁻¹ * (q * x * q⁻¹) ∈
            iCore L a ⊓ inSubgroup (aschbacherSolvableCore 3) J := ⟨h2, h1⟩
        rw [inf_theta_eq_bot_of_A6 hIJ e, Subgroup.mem_bot] at h3
        have h4 : x = q * x * q⁻¹ := inv_mul_eq_one.1 h3
        calc x * q = (q * x * q⁻¹) * q := by rw [← h4]
          _ = q * x := by group
      rw [← hAC]
      exact ⟨hqA, hqC⟩
    · refine le_inf hDA ?_
      rw [hDeq']
      refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 hcJ)
      refine Sec6.mem_thetaQuotCentralizer_iff.2 ⟨?_, fun l' hl' => ?_⟩
      · have hdC : d ∈ Subgroup.centralizer (J : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro x hx
          exact Subgroup.mem_centralizer_singleton_iff.1 (hJC hx)
        exact Subgroup.centralizer_le_normalizer (J : Set G) hdC
      · have hl'd : l' * d = d * l' := Subgroup.mem_centralizer_singleton_iff.1 (hJC hl')
        have : d * l' * d⁻¹ = l' := by rw [← hl'd]; group
        rw [this, inv_mul_cancel]
        exact Subgroup.one_mem _
  have hJs := CFSG.RankThree.PartOne.Sec12TwoAssembly.conj_mem_thetaComponentsAt
    Nat.prime_three (hqnd s hsd) hJ
  by_cases hJeq : J.map (MulAut.conj s).toMonoidHom = J
  · have hsJ : s ∈ Subgroup.normalizer (J : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.2 hJeq
    have := Sec12.mem_normalizer_inf_thetaQuotCentralizer hsA hsJ
    rw [hAQ] at this
    exact this
  · exfalso
    have hne : J ≠ J.map (MulAut.conj s).toMonoidHom := fun h1 => hJeq h1.symm
    have hle : (A ⊓ iCore L a) ≤ (dGroup a c).map (MulAut.conj s).toMonoidHom := by
      rintro x ⟨hxA, hxI⟩
      have hsx : s⁻¹ * x * s ∈ A := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hsA) x).1 hxA
        simpa using this
      have hxN : x ∈ Subgroup.normalizer
          ((J.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G) := by
        refine mem_normalizer_of_forall_conj_mem fun y hy => ?_
        obtain ⟨z, hz, rfl⟩ := hy
        have hzN := (Subgroup.mem_normalizer_iff.1 (hAJ _ hsx) z).1 hz
        refine ⟨s⁻¹ * x * s * z * (s⁻¹ * x * s)⁻¹, ?_, ?_⟩
        · simpa using hzN
        · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
      have hxQ := Sec12.mem_thetaQuotCentralizer_of_ne hJ hJs hne (hIJ hxI) hxN
      have hQ := mem_thetaQuotCentralizer_of_conj hxQ
      have hmemD : s⁻¹ * x * s ∈ dGroup a c := by
        rw [← hAQ]
        exact ⟨hsx, hQ⟩
      refine ⟨s⁻¹ * x * s, hmemD, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hcardD : Nat.card ↥((dGroup a c).map (MulAut.conj s).toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective (f := (MulAut.conj s).toMonoidHom)
        (MulAut.conj s).injective, hD9]
    have heq : A ⊓ iCore L a = (dGroup a c).map (MulAut.conj s).toMonoidHom :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcardD, hcardAI])
    have hdmem : d ∈ (dGroup a c).map (MulAut.conj s).toMonoidHom := by
      refine ⟨d, hdDL.1, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hsd]; group
    rw [← heq] at hdmem
    exact hd1 (hIcen d hdmem.2 (fun x hx => (hIcomm x hx d hdDL).symm))

end IStructure

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
