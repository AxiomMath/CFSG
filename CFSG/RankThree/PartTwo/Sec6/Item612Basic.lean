module

import CFSG.LieType.CurtisTits.Recognition
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantSylowContainment
public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

theorem theta_le (L : Subgroup G) : inSubgroup (aschbacherSolvableCore 3) L ≤ L :=
  Subgroup.map_subtype_le _

theorem le_normalizer_theta (L : Subgroup G) :
    L ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) L : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨l, hl⟩ * y * ⟨l, hl⟩⁻¹, (aschbacherSolvableCore_normal 3 L).conj_mem y hy _, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨⟨l, hl⟩⁻¹ * y * ⟨l, hl⟩, ?_, ?_⟩
    · have := (aschbacherSolvableCore_normal 3 L).conj_mem y hy (⟨l, hl⟩⁻¹)
      simpa using this
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hyx ⊢
      rw [hyx]
      group

theorem theta_solvable_and_not_dvd [Finite G] (L : Subgroup G) :
    Group.IsSolvable (inSubgroup (aschbacherSolvableCore 3) L) ∧
      ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) L) := by
  obtain ⟨hs, -, hpn, -⟩ := solvable_prime_complement_core_characterization (H := L)
    Nat.prime_three
  refine ⟨Group.isSolvable_of_isSolvable_injective
    (f := ((aschbacherSolvableCore 3 L).equivMapOfInjective L.subtype
      L.subtype_injective).symm.toMonoidHom) (MulEquiv.injective _), ?_⟩
  rwa [inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]

theorem le_theta_of_normal [Finite G] {L N : Subgroup G} (hNL : N ≤ L)
    (hLN : L ≤ Subgroup.normalizer (N : Set G)) (hsol : Group.IsSolvable N)
    (h3 : ¬ 3 ∣ Nat.card N) : N ≤ inSubgroup (aschbacherSolvableCore 3) L := by
  have hmax := (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.2.2.1
  have hn : (N.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr hLN
  have hs : Group.IsSolvable (N.subgroupOf L) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNL).toMonoidHom) (MulEquiv.injective _)
  have h3' : ¬ 3 ∣ Nat.card (N.subgroupOf L) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNL).toEquiv]
  have hle := hmax _ hn hs h3'
  intro x hx
  exact ⟨⟨x, hNL hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem normalizer_le_normalizer_theta [Finite G] (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) L : Set G) := by
  intro g hg
  have hLg : L.map (MulAut.conj g).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (inSubgroup (aschbacherSolvableCore 3) L).map (MulAut.conj g).toMonoidHom = _
  set e : L ≃* L.map (MulAut.conj g).toMonoidHom :=
    L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have h1 : (inSubgroup (aschbacherSolvableCore 3) L).map (MulAut.conj g).toMonoidHom =
      inSubgroup (aschbacherSolvableCore 3) (L.map (MulAut.conj g).toMonoidHom) := by
    rw [inSubgroup, inSubgroup, ← aschbacherSolvableCore_map_mulEquiv Nat.prime_three e,
      Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [h1]
  have key : ∀ M : Subgroup G, M = L →
      inSubgroup (aschbacherSolvableCore 3) M = inSubgroup (aschbacherSolvableCore 3) L := by
    rintro M rfl
    rfl
  exact key _ hLg


theorem mem_thetaQuotCentralizer_iff [Finite G] {L : Subgroup G} {x : G} :
    x ∈ thetaQuotCentralizer L ↔ x ∈ Subgroup.normalizer (L : Set G) ∧
      ∀ l ∈ L, l⁻¹ * (x * l * x⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  have key : ∀ y : Subgroup.normalizer (L : Set G),
      y ∈ ((thetaQuotMulAut L).comp L.normalizerMonoidHom).ker ↔
        ∀ l ∈ L, l⁻¹ * ((y : G) * l * (y : G)⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    intro y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro hy l hl
      have h := congrArg (fun φ : MulAut (L ⧸ aschbacherSolvableCore 3 L) =>
        φ ((⟨l, hl⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)) hy
      simp only [MulAut.one_apply, thetaQuotMulAut_mk] at h
      rw [QuotientGroup.eq] at h
      refine ⟨_, inv_mem h, ?_⟩
      simp
    · intro h
      ext q
      induction q using QuotientGroup.induction_on with
      | H l =>
        rw [thetaQuotMulAut_mk, MulAut.one_apply, QuotientGroup.eq]
        obtain ⟨t, ht, hteq⟩ := h l l.2
        have : t = l⁻¹ * L.normalizerMonoidHom y l := Subtype.ext hteq
        have ht' := inv_mem ht
        rw [this] at ht'
        simpa using ht'
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, (key y).mp hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, (key ⟨x, hx⟩).mpr h, rfl⟩


theorem thetaQuotCentralizer_le_normalizer [Finite G] (L : Subgroup G) :
    thetaQuotCentralizer L ≤ Subgroup.normalizer (L : Set G) :=
  fun _ hx => (mem_thetaQuotCentralizer_iff.mp hx).1

theorem theta_le_thetaQuotCentralizer [Finite G] (L : Subgroup G) :
    inSubgroup (aschbacherSolvableCore 3) L ≤ thetaQuotCentralizer L := by
  intro t ht
  have htL := theta_le L ht
  refine mem_thetaQuotCentralizer_iff.mpr ⟨Subgroup.le_normalizer htL, fun l hl => ?_⟩
  have h1 : l⁻¹ * t * l⁻¹⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_theta L (inv_mem hl)) t).mp ht
  have h2 := Subgroup.mul_mem _ h1 (inv_mem ht)
  rwa [show l⁻¹ * t * l⁻¹⁻¹ * t⁻¹ = l⁻¹ * (t * l * t⁻¹) by group] at h2

theorem conj_mem_thetaQuotCentralizer [Finite G] {L : Subgroup G} {x g : G}
    (hx : x ∈ thetaQuotCentralizer L) (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    g * x * g⁻¹ ∈ thetaQuotCentralizer L := by
  obtain ⟨hxN, hxl⟩ := mem_thetaQuotCentralizer_iff.mp hx
  refine mem_thetaQuotCentralizer_iff.mpr
    ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hxN) (inv_mem hg), fun l hl => ?_⟩
  have hl' : g⁻¹ * l * g⁻¹⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) l).mp hl
  have h1 := hxl _ hl'
  have h2 : g * ((g⁻¹ * l * g⁻¹⁻¹)⁻¹ * (x * (g⁻¹ * l * g⁻¹⁻¹) * x⁻¹)) * g⁻¹ ∈
      inSubgroup (aschbacherSolvableCore 3) L :=
    (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_theta L hg) _).mp h1
  rwa [show g * ((g⁻¹ * l * g⁻¹⁻¹)⁻¹ * (x * (g⁻¹ * l * g⁻¹⁻¹) * x⁻¹)) * g⁻¹ =
    l⁻¹ * (g * x * g⁻¹ * l * (g * x * g⁻¹)⁻¹) by group] at h2

theorem normalizer_le_normalizer_thetaQuotCentralizer [Finite G] (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer (thetaQuotCentralizer L : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_thetaQuotCentralizer hx hg, fun hx => ?_⟩
  have := conj_mem_thetaQuotCentralizer hx (inv_mem hg)
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

theorem commutator_le_theta_iff [Finite G] {L X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (L : Set G)) :
    ⁅L, X⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L ↔ X ≤ thetaQuotCentralizer L := by
  rw [Subgroup.commutator_le]
  constructor
  · intro h x hx
    refine mem_thetaQuotCentralizer_iff.mpr ⟨hX hx, fun l hl => ?_⟩
    have := h _ (inv_mem hl) x hx
    rwa [commutatorElement_def, inv_inv, show l⁻¹ * x * l * x⁻¹ = l⁻¹ * (x * l * x⁻¹) by group]
      at this
  · intro h l hl x hx
    have := (mem_thetaQuotCentralizer_iff.mp (h hx)).2 _ (inv_mem hl)
    rwa [inv_inv, show l * (x * l⁻¹ * x⁻¹) = ⁅l, x⁆ by rw [commutatorElement_def]; group] at this

theorem le_normalizer_commutator_left (H K : Subgroup G) :
    H ≤ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  have key : ∀ h ∈ H, ∀ c ∈ ⁅H, K⁆, h * c * h⁻¹ ∈ ⁅H, K⁆ := by
    intro h hh c hc
    have hle : ⁅H, K⁆ ≤ ⁅H, K⁆.comap (MulAut.conj h).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha k hk
      rw [Subgroup.mem_comap]
      change h * ⁅a, k⁆ * h⁻¹ ∈ ⁅H, K⁆
      rw [show h * ⁅a, k⁆ * h⁻¹ = ⁅h * a, k⁆ * ⁅h, k⁆⁻¹ by
        simp only [commutatorElement_def]; group]
      exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (H.mul_mem hh ha) hk)
        (inv_mem (Subgroup.commutator_mem_commutator hh hk))
    exact hle hc
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key h hh c, fun hc => ?_⟩
  have := key h⁻¹ (inv_mem hh) _ hc
  rwa [show h⁻¹ * (h * c * h⁻¹) * h⁻¹⁻¹ = c by group] at this

theorem le_normalizer_commutator_right (H K : Subgroup G) :
    K ≤ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.commutator_comm]
  exact le_normalizer_commutator_left K H

theorem commutator_self_eq_of_isPerfect {L : Subgroup G} (hL : Group.IsPerfect L) :
    ⁅L, L⁆ = L := by
  have h := congrArg (Subgroup.map L.subtype) hL.commutator_eq_top
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h

theorem three_subgroups_mod {X Y Z N : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (N : Set G)) (hY : Y ≤ Subgroup.normalizer (N : Set G))
    (hZ : Z ≤ Subgroup.normalizer (N : Set G)) (h1 : ⁅⁅X, Y⁆, Z⁆ ≤ N) (h2 : ⁅⁅Y, Z⁆, X⁆ ≤ N) :
    ⁅⁅Z, X⁆, Y⁆ ≤ N := by
  set M := Subgroup.normalizer (N : Set G)
  have hN : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
  set π := QuotientGroup.mk' (N.subgroupOf M)
  have hmap : ∀ A B C : Subgroup G, A ≤ M → B ≤ M → C ≤ M →
      ⁅⁅A, B⁆, C⁆ = (⁅⁅A.subgroupOf M, B.subgroupOf M⁆, C.subgroupOf M⁆).map M.subtype := by
    intro A B C hA hB hC
    rw [Subgroup.map_commutator, Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
      Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le hC]
  have key : ∀ A B C : Subgroup G, A ≤ M → B ≤ M → C ≤ M →
      (⁅⁅A, B⁆, C⁆ ≤ N ↔ ⁅⁅(A.subgroupOf M).map π, (B.subgroupOf M).map π⁆,
        (C.subgroupOf M).map π⁆ = ⊥) := by
    intro A B C hA hB hC
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk', hmap A B C hA hB hC]
    constructor
    · intro h x hx
      exact Subgroup.mem_subgroupOf.mpr (h ⟨x, hx, rfl⟩)
    · rintro h _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (h hx)
  rw [key X Y Z hX hY hZ] at h1
  rw [key Y Z X hY hZ hX] at h2
  rw [key Z X Y hZ hX hY]
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2


theorem commutator_sup_le_of_le_normalizer {Y Z N : Subgroup G}
    (hY : Y ≤ Subgroup.normalizer (N : Set G)) (hZ : Z ≤ Subgroup.normalizer (N : Set G)) :
    ⁅Y ⊔ N, Z⁆ ≤ ⁅Y, Z⁆ ⊔ N := by
  rw [Subgroup.commutator_le]
  intro w hw z hz
  have hw' : w ∈ (Y : Set G) * (N : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y N hY]
    exact hw
  obtain ⟨y, hy, c, hc, rfl⟩ := hw'
  have hcz : ⁅c, z⁆ ∈ N := by
    rw [commutatorElement_def]
    have : z * c⁻¹ * z⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hZ hz) _).mp (inv_mem hc)
    simpa [mul_assoc] using N.mul_mem hc this
  have hycz : y * ⁅c, z⁆ * y⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hY hy) _).mp hcz
  rw [show ⁅y * c, z⁆ = (y * ⁅c, z⁆ * y⁻¹) * ⁅y, z⁆ by simp only [commutatorElement_def]; group]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hycz)
    (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hy hz))

theorem eq_of_sup_theta_eq [Finite G] {L N : Subgroup G} (hLp : Group.IsPerfect L)
    (hNL : N ≤ L) (hLN : L ≤ Subgroup.normalizer (N : Set G))
    (h : N ⊔ inSubgroup (aschbacherSolvableCore 3) L = L) : N = L := by
  apply le_antisymm hNL
  have hn : (N.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr hLN
  set N' := N.subgroupOf L
  set θ' := aschbacherSolvableCore 3 L
  have hsup : N' ⊔ θ' = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hNL, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact h
  have hsol : Group.IsSolvable θ' :=
    (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).1
  set f : θ' →* L ⧸ N' := (QuotientGroup.mk' N').comp θ'.subtype
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective N' q
    have hl : l ∈ N' ⊔ θ' := hsup ▸ Subgroup.mem_top l
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp hl
    refine ⟨⟨z, hz⟩, ?_⟩
    simp only [f, MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [← hyz, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have := hn.conj_mem y hy z⁻¹
    simpa [mul_assoc] using this
  have : Group.IsSolvable (L ⧸ N') := Group.isSolvable_of_surjective hf
  have : Group.IsPerfect L := hLp
  have hperf : Group.IsPerfect (L ⧸ N') :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N') (QuotientGroup.mk'_surjective _)
  have hsub : Subsingleton (L ⧸ N') := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable (L ⧸ N') ‹_›
  intro x hx
  have h1 : (QuotientGroup.mk' N' ⟨x, hx⟩ : L ⧸ N') = 1 := Subsingleton.elim _ _
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)

theorem sup_theta_eq_or_commutator_le [Finite G] {L N : Subgroup G}
    (hLq : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L)) (hNL : N ≤ L)
    (hLN : L ≤ Subgroup.normalizer (N : Set G)) :
    N ⊔ inSubgroup (aschbacherSolvableCore 3) L = L ∨
      ⁅N, L⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L := by
  have hn : (N.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr hLN
  set N' := N.subgroupOf L
  set θ' := aschbacherSolvableCore 3 L
  set π := QuotientGroup.mk' θ'
  have hNn : (N'.map π).Normal := Subgroup.Normal.map hn π (QuotientGroup.mk'_surjective _)
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hLq (N'.map π) with h | h
  · right
    rw [Subgroup.commutator_le]
    intro n hn' l hl
    have hc : π ⁅(⟨n, hNL hn'⟩ : L), ⟨l, hl⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp (h ⟨⟨n, hNL hn'⟩, Subgroup.mem_subgroupOf.mpr hn', rfl⟩)
        (π ⟨l, hl⟩)).symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc
    exact ⟨_, hc, rfl⟩
  · left
    have hsup : N' ⊔ θ' = ⊤ := by
      rw [eq_top_iff]
      intro l _
      have hl : π l ∈ N'.map π := h ▸ Subgroup.mem_top (π l)
      obtain ⟨n, hn', hnl⟩ := hl
      have hmem : n⁻¹ * l ∈ θ' := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnl
        exact hnl
      rw [show l = n * (n⁻¹ * l) by group]
      exact Subgroup.mul_mem_sup hn' hmem
    have h2 := congrArg (Subgroup.map L.subtype) hsup
    rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hNL, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h2

theorem commutator_eq_of_not_le_theta [Finite G] {L X : Subgroup G} (hLp : Group.IsPerfect L)
    (hLq : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L))
    (hX : X ≤ Subgroup.normalizer (L : Set G))
    (h : ¬ ⁅L, X⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L) : ⁅L, X⁆ = L := by
  have hNL : ⁅L, X⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_left.mp hX
  have hLN : L ≤ Subgroup.normalizer ((⁅L, X⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_left L X
  rcases sup_theta_eq_or_commutator_le hLq hNL hLN with h1 | h1
  · exact eq_of_sup_theta_eq hLp hNL hLN h1
  · exfalso
    apply h
    have hθ := le_normalizer_theta L
    have hXθ : X ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) L : Set G) :=
      hX.trans (normalizer_le_normalizer_theta L)
    have h2 : ⁅⁅X, L⁆, L⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L := by
      rwa [Subgroup.commutator_comm X L]
    have h3 := three_subgroups_mod hθ hXθ hθ h1 h2
    rwa [commutator_self_eq_of_isPerfect hLp] at h3


theorem commutator_le_theta_of_le_thetaQuotCentralizer [Finite G] {L X : Subgroup G}
    (hLp : Group.IsPerfect L) (hX : X ≤ Subgroup.normalizer (L : Set G))
    (h : ⁅L, X⁆ ≤ thetaQuotCentralizer L) : ⁅L, X⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L := by
  have hNL : ⁅L, X⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_left.mp hX
  have h1 : ⁅⁅L, X⁆, L⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L := by
    rw [Subgroup.commutator_comm]
    exact (commutator_le_theta_iff (hNL.trans Subgroup.le_normalizer)).mpr h
  have hθ := le_normalizer_theta L
  have hXθ : X ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) L : Set G) :=
    hX.trans (normalizer_le_normalizer_theta L)
  have h2 : ⁅⁅X, L⁆, L⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L := by
    rwa [Subgroup.commutator_comm X L]
  have h3 := three_subgroups_mod hθ hXθ hθ h1 h2
  rwa [commutator_self_eq_of_isPerfect hLp] at h3

theorem le_normalizer_of_forall_conj_mem {A M : Subgroup G}
    (h : ∀ a ∈ A, ∀ x ∈ M, a * x * a⁻¹ ∈ M) : A ≤ Subgroup.normalizer (M : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h a ha x, fun hx => ?_⟩
  have h2 := h a⁻¹ (A.inv_mem ha) _ hx
  rwa [show a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x by group] at h2

theorem le_normalizer_sup_of_conj {A H K : Subgroup G}
    (hH : ∀ a ∈ A, ∀ x ∈ H, a * x * a⁻¹ ∈ H ⊔ K) (hK : ∀ a ∈ A, ∀ x ∈ K, a * x * a⁻¹ ∈ H ⊔ K) :
    A ≤ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  refine le_normalizer_of_forall_conj_mem fun a ha x hx => ?_
  have hle : H ⊔ K ≤ (H ⊔ K).comap (MulAut.conj a).toMonoidHom :=
    sup_le (fun y hy => hH a ha y hy) (fun y hy => hK a ha y hy)
  exact hle hx

theorem exists_pow_mem_of_mem_sup {p : ℕ} {R C : Subgroup G} (hR : IsPGroup p R)
    (hRC : R ≤ Subgroup.normalizer (C : Set G)) {x : G} (hx : x ∈ R ⊔ C) :
    ∃ k : ℕ, x ^ (p ^ k) ∈ C := by
  have hx' : x ∈ (R : Set G) * (C : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right R C hRC]
    exact hx
  obtain ⟨r, hr, c, hc, rfl⟩ := hx'
  obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
  have hk' : r ^ (p ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have key : ∀ n : ℕ, ∃ c' ∈ C, (r * c) ^ n = r ^ n * c' := by
    intro n
    induction n with
    | zero => exact ⟨1, C.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨c', hc', he⟩ := ih
      refine ⟨r⁻¹ * c' * r⁻¹⁻¹ * c, C.mul_mem ?_ hc, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hRC (R.inv_mem hr)) c').mp hc'
      · rw [pow_succ, he, pow_succ]
        group
  obtain ⟨c', hc', he⟩ := key (p ^ k)
  exact ⟨k, by rw [he, hk', one_mul]; exact hc'⟩

theorem le_of_forall_exists_pow_mem [Finite G] {p : ℕ} [Fact p.Prime] {L N : Subgroup G}
    (hLp : Group.IsPerfect L) (hNL : N ≤ L) (hLN : L ≤ Subgroup.normalizer (N : Set G))
    (h : ∀ x ∈ L, ∃ k : ℕ, x ^ (p ^ k) ∈ N) : L ≤ N := by
  have hn : (N.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr hLN
  set N' := N.subgroupOf L
  have hpg : IsPGroup p (L ⧸ N') := by
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective N' q
    obtain ⟨k, hk⟩ := h l l.2
    refine ⟨k, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hk)
  have : Group.IsNilpotent (L ⧸ N') := hpg.isNilpotent
  have : Group.IsPerfect L := hLp
  have hperf : Group.IsPerfect (L ⧸ N') :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N') (QuotientGroup.mk'_surjective _)
  have hsub : Subsingleton (L ⧸ N') := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable (L ⧸ N') inferInstance
  intro x hx
  have h1 : (QuotientGroup.mk' N' ⟨x, hx⟩ : L ⧸ N') = 1 := Subsingleton.elim _ _
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)

theorem le_thetaQuotCentralizer_of_isPGroup_two [Finite G] {L Y R : Subgroup G}
    (hLp : Group.IsPerfect L) (hLq : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L))
    (hY : Y ≤ Subgroup.normalizer (L : Set G)) (hLY : L ≤ Y ⊔ thetaQuotCentralizer L)
    (hR : IsPGroup 2 R) (hRN : R ≤ Subgroup.normalizer (L : Set G))
    (hYR : Y ≤ Subgroup.normalizer (R : Set G)) : R ≤ thetaQuotCentralizer L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := thetaQuotCentralizer L
  have hCN := normalizer_le_normalizer_thetaQuotCentralizer L
  have hYC : Y ⊔ C ≤ Subgroup.normalizer ((R ⊔ C : Subgroup G) : Set G) := by
    apply le_normalizer_sup_of_conj
    · intro a ha x hx
      have ha' : a ∈ (Y : Set G) * (C : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y C (hY.trans hCN)]
        exact ha
      obtain ⟨y, hy, c, hc, rfl⟩ := ha'
      have h1 : y * x * y⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hYR hy) x).mp hx
      have h3 : y * c * y⁻¹ ∈ C := conj_mem_thetaQuotCentralizer hc (hY hy)
      rw [show y * c * x * (y * c)⁻¹ =
        (y * x * y⁻¹) * ((y * x * y⁻¹)⁻¹ * (y * c * y⁻¹) * (y * x * y⁻¹)) *
          (y * c * y⁻¹)⁻¹ by group]
      refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left h1)
        (Subgroup.mem_sup_right ?_)) (Subgroup.mem_sup_right (inv_mem h3))
      simpa using conj_mem_thetaQuotCentralizer h3 (inv_mem (hRN h1))
    · intro a ha x hx
      have hxC : a * x * a⁻¹ ∈ C :=
        conj_mem_thetaQuotCentralizer hx ((sup_le hY (thetaQuotCentralizer_le_normalizer L)) ha)
      exact Subgroup.mem_sup_right hxC
  set W := (R ⊔ C) ⊓ L
  have hWL : W ≤ L := inf_le_right
  have hLW : L ≤ Subgroup.normalizer (W : Set G) :=
    (le_inf (hLY.trans hYC) Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hWC : W ≤ C := by
    rcases sup_theta_eq_or_commutator_le hLq hWL hLW with h1 | h1
    ·
      have hθW : inSubgroup (aschbacherSolvableCore 3) L ≤ W :=
        le_inf ((theta_le_thetaQuotCentralizer L).trans le_sup_right) (theta_le L)
      have hLW' : L ≤ W := by rw [← h1]; exact sup_le le_rfl hθW
      have hZL : L ≤ C ⊓ L := by
        refine le_of_forall_exists_pow_mem (p := 2) hLp inf_le_right ?_ fun x hx => ?_
        · exact (le_inf (hLY.trans (sup_le (hY.trans hCN) Subgroup.le_normalizer))
            Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
        · obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup hR (hRN.trans hCN) (hLW' hx).1
          exact ⟨k, hk, L.pow_mem hx _⟩
      exact hWL.trans (hZL.trans inf_le_left)
    · rw [← commutator_le_theta_iff (hWL.trans Subgroup.le_normalizer), Subgroup.commutator_comm]
      exact h1
  have hLR : ⁅L, R⁆ ≤ C := by
    refine le_trans ?_ hWC
    rw [Subgroup.commutator_le]
    intro l hl r hr
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      have h1 : l * r * l⁻¹ ∈ R ⊔ C := (Subgroup.mem_normalizer_iff.mp
        (hYC (hLY hl)) r).mp (Subgroup.mem_sup_left hr)
      exact Subgroup.mul_mem _ h1 (Subgroup.mem_sup_left (inv_mem hr))
    · rw [commutatorElement_def]
      have h1 : r * l⁻¹ * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hRN hr) _).mp (inv_mem hl)
      simpa [mul_assoc] using L.mul_mem hl h1
  exact (commutator_le_theta_iff hRN).mp
    (commutator_le_theta_of_le_thetaQuotCentralizer hLp hRN hLR)

theorem commutator_le_theta_of_cover [Finite G] {L Y V : Subgroup G}
    (hLp : Group.IsPerfect L) (hLq : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L))
    (hY : Y ≤ Subgroup.normalizer (L : Set G)) (hLY : L ≤ Y ⊔ thetaQuotCentralizer L)
    (hV : V ≤ Subgroup.normalizer (L : Set G)) (hR : IsPGroup 2 (⁅Y, V⁆ : Subgroup G)) :
    ⁅L, V⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L := by
  have hRN : ⁅Y, V⁆ ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.commutator_mono hY hV).trans (Subgroup.commutator_le_self _)
  have hRC := le_thetaQuotCentralizer_of_isPGroup_two hLp hLq hY hLY hR hRN
    (le_normalizer_commutator_left Y V)
  have hCN := normalizer_le_normalizer_thetaQuotCentralizer L
  have hLV : ⁅L, V⁆ ≤ thetaQuotCentralizer L :=
    (Subgroup.commutator_mono hLY le_rfl).trans
      ((commutator_sup_le_of_le_normalizer (hY.trans hCN) (hV.trans hCN)).trans
        (sup_le hRC le_rfl))
  exact commutator_le_theta_of_le_thetaQuotCentralizer hLp hV hLV


theorem not_dvd_card_sup_of_isPGroup [Finite G] {p q : ℕ} [Fact p.Prime] (hq : q.Prime)
    (hpq : p ≠ q) {R N : Subgroup G} (hR : IsPGroup p R)
    (hRN : R ≤ Subgroup.normalizer (N : Set G)) (hN : ¬ q ∣ Nat.card N) :
    ¬ q ∣ Nat.card (R ⊔ N : Subgroup G) := by
  set W := R ⊔ N
  have hNW : N ≤ W := le_sup_right
  have hWN : W ≤ Subgroup.normalizer (N : Set G) := sup_le hRN Subgroup.le_normalizer
  have hn : (N.subgroupOf W).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNW).mpr hWN
  have hpg : IsPGroup p (W ⧸ N.subgroupOf W) := by
    intro q'
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf W) q'
    obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup hR hRN w.2
    refine ⟨k, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hk)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hpg
  have hcard : Nat.card W = p ^ m * Nat.card N := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf W), hm,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNW).toEquiv]
  rw [hcard]
  intro hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
  · exact hpq ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp (hq.dvd_of_dvd_pow h)).symm
  · exact hN h

theorem exists_inv_mul_mem_normalizer_sylow [Finite G] {p : ℕ} [Fact p.Prime] {X : Subgroup G}
    (P : Sylow p X) {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    ∃ x ∈ X, x⁻¹ * g ∈
      Subgroup.normalizer (((P : Subgroup X).map X.subtype : Subgroup G) : Set G) := by
  set S : Subgroup G := (P : Subgroup X).map X.subtype
  set S' : Subgroup G := S.map (MulAut.conj g).toMonoidHom
  have hSX : S ≤ X := Subgroup.map_subtype_le _
  have hS'X : S' ≤ X := by
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp (hSX hy)
  have hS : IsPGroup p S := P.isPGroup'.map X.subtype
  have hS' : IsPGroup p S' := hS.map _
  have hT : IsPGroup p (S'.subgroupOf X) := hS'.comap_of_injective X.subtype X.subtype_injective
  obtain ⟨Q, hTQ⟩ := IsPGroup.exists_le_sylow hT
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X P Q
  have hQ : ((Q : Subgroup X).map X.subtype) = S.map (MulAut.conj (x : G)).toMonoidHom := by
    rw [← hx, Sylow.coe_subgroup_smul]
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_smul_pointwise_iff_exists, S]
    constructor
    · rintro ⟨z, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨b, ⟨b, hb, rfl⟩, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨_, ⟨b, hb, rfl⟩, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
  have hle : S' ≤ S.map (MulAut.conj (x : G)).toMonoidHom := by
    rw [← hQ]
    intro y hy
    exact ⟨⟨y, hS'X hy⟩, hTQ (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  have heq : S' = S.map (MulAut.conj (x : G)).toMonoidHom := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj (x : G)).injective]
    exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  refine ⟨x, x.2, ?_⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change S.map (MulAut.conj ((x : G)⁻¹ * g)).toMonoidHom = S
  have hcomp : (MulAut.conj ((x : G)⁻¹ * g)).toMonoidHom =
      (MulAut.conj (x : G)⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  rw [hcomp, ← Subgroup.map_map, show S.map (MulAut.conj g).toMonoidHom = S' from rfl, heq,
    Subgroup.map_map]
  conv_rhs => rw [← Subgroup.map_id S]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]


theorem normalizer_le_normalizer_normalizer (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer ((Subgroup.normalizer (S : Set G) : Subgroup G) : Set G) :=
  Subgroup.le_normalizer

theorem commutator_le_theta_of_le_thetaQuotCentralizer_abelian [Finite G]
    {L E U V Q : Subgroup G} {c : G}
    (hLp : Group.IsPerfect L) (hLq : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L))
    (hE3 : IsPGroup 3 E) (hEL : E ≤ Subgroup.normalizer (L : Set G)) (hLE : ⁅L, E⁆ = L)
    (hEθ : ∀ T : Subgroup G, T ≤ inSubgroup (aschbacherSolvableCore 3) L → IsPGroup 2 T →
      E ≤ Subgroup.normalizer (T : Set G) → ⁅T, E⁆ = ⊥)
    (hU2 : IsPGroup 2 U) (hUab : ⁅U, U⁆ = ⊥)
    (hUL : U ≤ Subgroup.normalizer (L : Set G)) (hUC : U ≤ thetaQuotCentralizer L)
    (hEU : E ≤ Subgroup.normalizer (U : Set G))
    (hVL : V ≤ Subgroup.normalizer (L : Set G)) (hVQ : V ≤ Q) (hQ2 : IsPGroup 2 Q)
    (hQN : Subgroup.centralizer (U : Set G) ⊓ Subgroup.centralizer {c} ≤
      Subgroup.normalizer (Q : Set G))
    (hLc : L ≤ Subgroup.centralizer {c}) (hUc : U ≤ Subgroup.centralizer {c}) :
    ⁅L, V⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  set C := thetaQuotCentralizer L with hC
  have hθN := normalizer_le_normalizer_theta L
  have hCN := normalizer_le_normalizer_thetaQuotCentralizer L
  have hθLN : θL ≤ Subgroup.normalizer (L : Set G) := (theta_le L).trans Subgroup.le_normalizer
  set X := U ⊔ θL with hX
  have hUθ : U ≤ Subgroup.normalizer (θL : Set G) := hUL.trans hθN
  have hX3 : ¬ 3 ∣ Nat.card X := not_dvd_card_sup_of_isPGroup Nat.prime_three (by norm_num) hU2
    hUθ (theta_solvable_and_not_dvd L).2
  have hXC : X ≤ C := sup_le hUC (theta_le_thetaQuotCentralizer L)
  have hXL : X ≤ Subgroup.normalizer (L : Set G) := sup_le hUL hθLN
  have hEX : E ≤ Subgroup.normalizer (X : Set G) := by
    apply le_normalizer_sup_of_conj
    · intro e he x hx
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hEU he) x).mp hx)
    · intro e he x hx
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hθN (hEL he)) x).mp hx)
  obtain ⟨P, hUP, hEP⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.exists_normalized_sylow_containing_normalized_pSubgroup
      3 Nat.prime_three 2 Nat.prime_two E X U hE3 hX3 hEX le_sup_left hU2 hEU
  set S := (P : Subgroup X).map X.subtype with hS
  have hSX : S ≤ X := Subgroup.map_subtype_le _
  set T := S ⊓ θL with hT
  have hT2 : IsPGroup 2 T := (P.isPGroup'.map X.subtype).to_le inf_le_left
  have hET : E ≤ Subgroup.normalizer (T : Set G) :=
    (le_inf hEP (hEL.trans hθN)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hTE : ⁅T, E⁆ = ⊥ := hEθ T inf_le_right hT2 hET
  have hLX : L ≤ Subgroup.normalizer (X : Set G) := by
    refine le_normalizer_of_forall_conj_mem fun l hl x hx => ?_
    have hx' := (mem_thetaQuotCentralizer_iff.mp (inv_mem (hXC hx))).2 l hl
    have h1 : l * (l⁻¹ * (x⁻¹ * l * x⁻¹⁻¹)) * l⁻¹ ∈ θL :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_theta L hl) _).mp hx'
    rw [show l * x * l⁻¹ = x * (l * (l⁻¹ * (x⁻¹ * l * x⁻¹⁻¹)) * l⁻¹) by group]
    exact X.mul_mem hx (Subgroup.mem_sup_right h1)
  set NS := (L ⊔ X) ⊓ Subgroup.normalizer (S : Set G) with hNS
  have hLXN : L ⊔ X ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hXL
  have hNSL : NS ≤ Subgroup.normalizer (L : Set G) := inf_le_left.trans hLXN
  have hfr : L ≤ NS ⊔ C := by
    intro l hl
    obtain ⟨x, hxX, hxn⟩ := exists_inv_mul_mem_normalizer_sylow P (hLX hl)
    have h1 : x⁻¹ * l ∈ NS :=
      ⟨Subgroup.mul_mem _ (Subgroup.mem_sup_right (inv_mem hxX)) (Subgroup.mem_sup_left hl), hxn⟩
    rw [show l = x * (x⁻¹ * l) by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hXC hxX)) (Subgroup.mem_sup_left h1)
  have hELX : E ≤ Subgroup.normalizer ((L ⊔ X : Subgroup G) : Set G) := by
    apply le_normalizer_sup_of_conj
    · intro e he x hx
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hEL he) x).mp hx)
    · intro e he x hx
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hEX he) x).mp hx)
  have hENS : E ≤ Subgroup.normalizer (NS : Set G) :=
    (le_inf hELX (hEP.trans (normalizer_le_normalizer_normalizer S))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  set K := ⁅NS, E⁆ with hK
  have hKNS : K ≤ NS := Subgroup.le_normalizer_iff_commutator_le_left.mp hENS
  have hNST : NS ≤ Subgroup.normalizer (T : Set G) :=
    (le_inf inf_le_right (hNSL.trans hθN)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hKT : ⁅K, T⁆ = ⊥ := by
    apply Subgroup.commutator_commutator_eq_bot_of_rotate
    · rw [Subgroup.commutator_comm E T, hTE, Subgroup.commutator_bot_left]
    · rw [eq_bot_iff, ← hTE]
      exact Subgroup.commutator_mono (Subgroup.le_normalizer_iff_commutator_le_left.mp hNST) le_rfl
  have hLXX : ⁅L ⊔ X, X⁆ ≤ θL := by
    have hLX' : ⁅L, X⁆ ≤ θL := (commutator_le_theta_iff hXL).mpr hXC
    have hXX : ⁅X, X⁆ ≤ θL := by
      have h1 : ⁅U ⊔ θL, X⁆ ≤ ⁅U, X⁆ ⊔ θL :=
        commutator_sup_le_of_le_normalizer hUθ (hXL.trans hθN)
      have h2 : ⁅U, X⁆ ≤ θL := by
        rw [Subgroup.commutator_comm]
        have h3 : ⁅U ⊔ θL, U⁆ ≤ ⁅U, U⁆ ⊔ θL :=
          commutator_sup_le_of_le_normalizer hUθ hUθ
        rw [hUab, bot_sup_eq] at h3
        exact h3
      exact h1.trans (sup_le h2 le_rfl)
    rw [Subgroup.commutator_le]
    intro w hw x hx
    have hw' : w ∈ (L : Set G) * (X : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right L X hLX]
      exact hw
    obtain ⟨l, hl, y, hy, rfl⟩ := hw'
    rw [show ⁅l * y, x⁆ = (l * ⁅y, x⁆ * l⁻¹) * ⁅l, x⁆ by simp only [commutatorElement_def]; group]
    exact θL.mul_mem ((Subgroup.mem_normalizer_iff.mp (le_normalizer_theta L hl) _).mp
      (hXX (Subgroup.commutator_mem_commutator hy hx)))
      (hLX' (Subgroup.commutator_mem_commutator hl hx))
  have hNSS : ⁅NS, S⁆ ≤ T :=
    le_inf (Subgroup.le_normalizer_iff_commutator_le_right.mp inf_le_right)
      ((Subgroup.commutator_mono inf_le_left hSX).trans hLXX)
  have hτ : ∀ k ∈ K, ∀ s ∈ S, ⁅k, s⁆ ∈ T := fun k hk s hs =>
    hNSS (Subgroup.commutator_mem_commutator (hKNS hk) hs)
  have hkT : ∀ k ∈ K, ∀ t ∈ T, k * t = t * k := fun k hk t ht => by
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKT hk
    exact (Subgroup.mem_centralizer_iff.mp this t ht).symm
  have hST : S ≤ Subgroup.normalizer (T : Set G) :=
    (le_inf Subgroup.le_normalizer ((hSX.trans hXL).trans hθN)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hcent : ∀ k ∈ K, ∀ s ∈ S, ∀ t ∈ T, ⁅k, s⁆ * t = t * ⁅k, s⁆ := by
    intro k hk s hs t ht
    have ht' : s⁻¹ * t * s⁻¹⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hST (inv_mem hs)) t).mp ht
    have h1 := hkT k hk _ ht'
    have h2 := hkT k hk _ (hτ k hk s hs)
    have h3 : k * t * k⁻¹ = t := by
      rw [hkT k hk t ht]; group
    have h4 : k * (s⁻¹ * t * s⁻¹⁻¹) * k⁻¹ = s⁻¹ * t * s⁻¹⁻¹ := by
      rw [h1]; group
    have h5 : k * s * k⁻¹ = ⁅k, s⁆ * s := by rw [commutatorElement_def]; group
    calc ⁅k, s⁆ * t = ⁅k, s⁆ * (s * (s⁻¹ * t * s⁻¹⁻¹) * s⁻¹) := by group
      _ = (k * s * k⁻¹) * (k * (s⁻¹ * t * s⁻¹⁻¹) * k⁻¹) * (k * s * k⁻¹)⁻¹ * ⁅k, s⁆ := by
          rw [h4, h5]; group
      _ = k * t * k⁻¹ * ⁅k, s⁆ := by group
      _ = t * ⁅k, s⁆ := by rw [h3]
  have hKK : ⁅K, K⁆ ≤ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.commutator_le]
    intro k hk k' hk'
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have ha : k⁻¹ ∈ K := inv_mem hk
    have hb : k'⁻¹ ∈ K := inv_mem hk'
    set a := k⁻¹
    set b := k'⁻¹
    have hbs : b * s * b⁻¹ = ⁅b, s⁆ * s := by rw [commutatorElement_def]; group
    have has : a * s * a⁻¹ = ⁅a, s⁆ * s := by rw [commutatorElement_def]; group
    have hab : a * b * s * (a * b)⁻¹ = ⁅b, s⁆ * ⁅a, s⁆ * s := by
      calc a * b * s * (a * b)⁻¹ = a * (b * s * b⁻¹) * a⁻¹ := by group
        _ = a * ⁅b, s⁆ * a⁻¹ * (a * s * a⁻¹) := by rw [hbs]; group
        _ = ⁅b, s⁆ * (⁅a, s⁆ * s) := by
            rw [has, hkT a ha _ (hτ b hb s hs)]; group
        _ = ⁅b, s⁆ * ⁅a, s⁆ * s := by group
    have hba : b * a * s * (b * a)⁻¹ = ⁅a, s⁆ * ⁅b, s⁆ * s := by
      calc b * a * s * (b * a)⁻¹ = b * (a * s * a⁻¹) * b⁻¹ := by group
        _ = b * ⁅a, s⁆ * b⁻¹ * (b * s * b⁻¹) := by rw [has]; group
        _ = ⁅a, s⁆ * (⁅b, s⁆ * s) := by
            rw [hbs, hkT b hb _ (hτ a ha s hs)]; group
        _ = ⁅a, s⁆ * ⁅b, s⁆ * s := by group
    have hcomm : ⁅b, s⁆ * ⁅a, s⁆ = ⁅a, s⁆ * ⁅b, s⁆ :=
      (hcent a ha s hs _ (hτ b hb s hs)).symm
    have key : a * b * s * (a * b)⁻¹ = b * a * s * (b * a)⁻¹ := by rw [hab, hba, hcomm]
    have hk1 : k = a⁻¹ := (inv_inv k).symm
    have hk2 : k' = b⁻¹ := (inv_inv k').symm
    rw [hk1, hk2]
    calc s * ⁅a⁻¹, b⁻¹⁆ = (b * a)⁻¹ * (b * a * s * (b * a)⁻¹) * (b * a) * ⁅a⁻¹, b⁻¹⁆ := by group
      _ = (b * a)⁻¹ * (a * b * s * (a * b)⁻¹) * (b * a) * ⁅a⁻¹, b⁻¹⁆ := by rw [key]
      _ = ⁅a⁻¹, b⁻¹⁆ * s := by rw [commutatorElement_def]; group
  have hKN : K ≤ Subgroup.normalizer (L : Set G) := hKNS.trans hNSL
  have hLK : L ≤ K ⊔ C := by
    calc L = ⁅L, E⁆ := hLE.symm
      _ ≤ ⁅NS ⊔ C, E⁆ := Subgroup.commutator_mono hfr le_rfl
      _ ≤ ⁅NS, E⁆ ⊔ C := commutator_sup_le_of_le_normalizer (hNSL.trans hCN) (hEL.trans hCN)
  have hKCN : K ⊔ C ≤ Subgroup.normalizer (C : Set G) :=
    sup_le (hKN.trans hCN) Subgroup.le_normalizer
  have hLKK : L ≤ ⁅K, K⁆ ⊔ C := by
    calc L = ⁅L, L⁆ := (commutator_self_eq_of_isPerfect hLp).symm
      _ ≤ ⁅K ⊔ C, K ⊔ C⁆ := Subgroup.commutator_mono hLK hLK
      _ ≤ ⁅K, K ⊔ C⁆ ⊔ C := commutator_sup_le_of_le_normalizer (hKN.trans hCN) hKCN
      _ ≤ ⁅K, K⁆ ⊔ C := by
          refine sup_le ?_ le_sup_right
          rw [Subgroup.commutator_comm]
          exact commutator_sup_le_of_le_normalizer (hKN.trans hCN) (hKN.trans hCN)
  have hKc : K ≤ Subgroup.centralizer {c} := by
    refine hKNS.trans (inf_le_left.trans (sup_le hLc (sup_le hUc ((theta_le L).trans hLc))))
  have hYU : ⁅K, K⁆ ≤ Subgroup.centralizer (U : Set G) :=
    hKK.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hUP))
  have hYc : ⁅K, K⁆ ≤ Subgroup.centralizer {c} :=
    (Subgroup.commutator_mono hKc hKc).trans (Subgroup.commutator_le_self _)
  have hYQ : ⁅K, K⁆ ≤ Subgroup.normalizer (Q : Set G) := (le_inf hYU hYc).trans hQN
  have hR : IsPGroup 2 (⁅⁅K, K⁆, V⁆ : Subgroup G) := by
    refine hQ2.to_le ?_
    refine (Subgroup.commutator_mono le_rfl hVQ).trans ?_
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hYQ
  exact commutator_le_theta_of_cover hLp hLq
    ((Subgroup.commutator_mono hKN hKN).trans (Subgroup.commutator_le_self _)) hLKK hVL hR

end CFSG.RankThree.PartTwo.Sec6
