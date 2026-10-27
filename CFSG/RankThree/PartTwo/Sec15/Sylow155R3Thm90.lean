module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Thm90Y
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Thm90Pt
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Thm90Two
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank

namespace Thm90

theorem K9For_J2 (h : Res3K9) : K9For CFSG.Blueprint.NativeSporadic.J2 := h

section Conj

variable {G : Type} [Group G]

theorem mem_map_conj_iff {L : Subgroup G} {w y : G} :
    y ∈ L.map (MulAut.conj w).toMonoidHom ↔ w⁻¹ * y * w ∈ L := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have h : w⁻¹ * (w * z * w⁻¹) * w = z := by group
    show w⁻¹ * (w * z * w⁻¹) * w ∈ L
    rw [h]
    exact hz
  · intro hy
    refine ⟨w⁻¹ * y * w, hy, ?_⟩
    show w * (w⁻¹ * y * w) * w⁻¹ = y
    group

theorem mem_normalizer_map_conj {L : Subgroup G} {w x : G}
    (hx : w⁻¹ * x * w ∈ Subgroup.normalizer (L : Set G)) :
    x ∈ Subgroup.normalizer ((L.map (MulAut.conj w).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [mem_map_conj_iff, mem_map_conj_iff]
  have h1 := Subgroup.mem_normalizer_iff.mp hx (w⁻¹ * y * w)
  have h2 : (w⁻¹ * x * w) * (w⁻¹ * y * w) * (w⁻¹ * x * w)⁻¹ = w⁻¹ * (x * y * x⁻¹) * w := by
    group
  rw [h2] at h1
  exact h1

theorem mem_normalizer_of_map_conj_eq {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have e : g * y * g⁻¹ = g * x * g⁻¹ := hyx
    rw [← mul_left_cancel (mul_right_cancel e)]
    exact hy

theorem conj_mem_centralizer {A : Subgroup G} {w x : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G)) (hx : x ∈ Subgroup.centralizer (A : Set G)) :
    w⁻¹ * x * w ∈ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have ha' : w * a * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hw a).mp ha
  have h1 := Subgroup.mem_centralizer_iff.mp hx (w * a * w⁻¹) ha'
  calc a * (w⁻¹ * x * w) = w⁻¹ * ((w * a * w⁻¹) * x) * w := by group
    _ = w⁻¹ * (x * (w * a * w⁻¹)) * w := by rw [h1]
    _ = w⁻¹ * x * w * a := by group

theorem isElemAbelian_subgroupOf {p : ℕ} {A Y : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian p A) : CFSG.Assembly.IsElemAbelian p (A.subgroupOf Y) := by
  have hcomm : IsMulCommutative (A.subgroupOf Y) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    have h' := hA.1.is_comm.comm (⟨(a.1 : G), a.2⟩ : ↥A) ⟨(b.1 : G), b.2⟩
    have h'' : (a.1 : G) * (b.1 : G) = (b.1 : G) * (a.1 : G) := congrArg Subtype.val h'
    exact Subtype.ext (Subtype.ext h'')
  refine ⟨hcomm, fun g hg => ?_⟩
  exact Subtype.ext (by simpa using hA.2 (g : G) (Subgroup.mem_subgroupOf.mp hg))

end Conj

section Component

variable {G : Type} [Group G] [Finite G]

theorem conj_component {J : Type} [Group J] {c : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 c) (e : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* J) (w : G) :
    L.map (MulAut.conj w).toMonoidHom ∈ thetaComponentsAt 3 (w * c * w⁻¹) ∧
    Nonempty (↥(L.map (MulAut.conj w).toMonoidHom) ⧸
      aschbacherSolvableCore 3 ↥(L.map (MulAut.conj w).toMonoidHom) ≃* J) ∧
    Nat.card (aschbacherSolvableCore 3 ↥(L.map (MulAut.conj w).toMonoidHom)) =
      Nat.card (aschbacherSolvableCore 3 ↥L) := by
  let eL : ↥L ≃* ↥(L.map (MulAut.conj w).toMonoidHom) :=
    L.equivMapOfInjective (MulAut.conj w).toMonoidHom (MulAut.conj w).injective
  refine ⟨map_mem_thetaComponentsAt (MulAut.conj w) hL,
    ⟨((QuotientGroup.congr _ _ eL
      (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three eL)).symm).trans e⟩, ?_⟩
  rw [← CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three eL,
    Subgroup.card_map_of_injective eL.injective]

end Component

section Res

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {d : G}
  {K : Subgroup G}

theorem c_ne_one (h : Res3Ctx A c L d K) : c ≠ 1 := by
  have hord : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact (mem_omegaA_iff.mp h.R.zpowers_mem_omegaA).2.1
  intro h1
  rw [h1, orderOf_one] at hord
  omega

theorem centralizer_le_normalizer (h : Res3Ctx A c L d K) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have h3 : 3 ∣ Nat.card L := by
    have hd3 : d ^ 3 = 1 := h.R.toSec13Data.isElemAbelian.2 d h.d_mem
    rw [← orderOf_eq_prime hd3 h.d_ne]
    exact Subgroup.orderOf_dvd_natCard L h.d_L
  intro g hg
  have hgc : (MulAut.conj g) c = c := by
    rw [MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
  have hLg : L.map (MulAut.conj g).toMonoidHom ∈ thetaComponentsAt 3 c := by
    have := map_mem_thetaComponentsAt (MulAut.conj g) h.R.mem_lA.1
    rwa [hgc] at this
  have h3' : 3 ∣ Nat.card (L.map (MulAut.conj g).toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have heq := (h.R.chosen136.2 c h.R.zpowers_mem_omegaA L h.R.mem_lA).2 _ hLg h3'
  exact mem_normalizer_of_map_conj_eq heq

end Res

end Thm90

theorem Res3Ctx.theorem90 {G : Type} [Group G] [Finite G]
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h135 : Item135)
    (hJ : Thm90.J2Facts CFSG.Blueprint.NativeSporadic.J2) (hK9 : Res3K9)
    {A : Subgroup G} {c : G} {L : Subgroup G} {d : G} {K : Subgroup G}
    (h : Res3Ctx A c L d K) :
    ∀ x ∈ Subgroup.centralizer (A : Set G), (orderOf x).Prime →
      orderOf x = 2 ∨ orderOf x = 3 ∨ orderOf x = 5 ∨ orderOf x = 7 := by
  intro x hx hxprime
  by_contra hcon
  obtain ⟨p, hpdef⟩ : ∃ p, p = orderOf x := ⟨_, rfl⟩
  rw [← hpdef] at hxprime hcon
  have hp7 : ¬ (p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7) := hcon
  have hp2 : p ≠ 2 := fun h2' => hp7 (Or.inl h2')
  have hxp : x ^ p = 1 := by rw [hpdef]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h1' => hxprime.ne_one (by rw [hpdef, h1', orderOf_one])
  have hT4 : TheoremFourHyp G := h.R.toSec13Data.toTheoremFourHyp
  have hAe := h.R.toSec13Data.isElemAbelian
  have hA27 : Nat.card A = 27 := h.R.toSec13Data.card_eq
  have hcomm : ∀ a ∈ A, a * x = x * a := fun a ha => Subgroup.mem_centralizer_iff.mp hx a ha
  have hc3 : c ^ 3 = 1 := hAe.2 c h.c_mem
  have hd3 : d ^ 3 = 1 := hAe.2 d h.d_mem
  have hc1 : c ≠ 1 := Thm90.c_ne_one h
  have hNY : Subgroup.centralizer ({x} : Set G) ≠ ⊤ := by
    intro htop
    have hxz : x ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer ({x} : Set G) := htop ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    haveI := hT4.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hb | ht
    · rw [hb, Subgroup.mem_bot] at hxz
      exact hx1 hxz
    · obtain ⟨a, b, hab⟩ := hT4.nonabelian
      apply hab
      have ha : a ∈ Subgroup.center G := ht ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
  have hY : SectionFourHyp ↥(Subgroup.centralizer ({x} : Set G)) := hT4.sectionFourHyp hNY
  have hAY : A ≤ Subgroup.centralizer ({x} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a ha)
  obtain ⟨w, hwN, hwd, hdc⟩ := Thm90.second_point h
  have hc'A : w * c * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hwN c).mp h.c_mem
  have hcY : c ∈ Subgroup.centralizer ({x} : Set G) := hAY h.c_mem
  have hc'Y : w * c * w⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := hAY hc'A
  have hdY : d ∈ Subgroup.centralizer ({x} : Set G) := hAY h.d_mem
  have hc'1 : w * c * w⁻¹ ≠ 1 := fun h' => hc1 ((MulAut.conj w).injective (by
    rw [map_one]; exact h'))
  obtain ⟨e⟩ := h.J2
  have hL : L ∈ thetaComponentsAt 3 c := h.R.mem_lA.1
  have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
    h135 G A c L h.R.toSec13Data h.R.hypS_or_hypT
  have hθ : ¬ p ∣ Nat.card (aschbacherSolvableCore 3 ↥L) :=
    @Thm90.not_dvd_card_theta CFSG.Blueprint.NativeSporadic.J2 inferInstance ↥L inferInstance
      inferInstance hq e p hxprime hp2 (hJ.not_dvd_card hxprime hp7)
  have hxL : x ∈ Subgroup.normalizer (L : Set G) :=
    Thm90.centralizer_le_normalizer h
      (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm c h.c_mem).symm)
  obtain ⟨hL', ⟨e'⟩, hθcard⟩ := @Thm90.conj_component G _ _ CFSG.Blueprint.NativeSporadic.J2
    inferInstance c L hL e w
  have hθ' : ¬ p ∣ Nat.card (aschbacherSolvableCore 3 ↥(L.map (MulAut.conj w).toMonoidHom)) := by
    rw [hθcard]
    exact hθ
  have hxL' : x ∈ Subgroup.normalizer
      ((L.map (MulAut.conj w).toMonoidHom : Subgroup G) : Set G) := by
    apply Thm90.mem_normalizer_map_conj
    have hx' := Thm90.conj_mem_centralizer hwN hx
    exact Thm90.centralizer_le_normalizer h
      (Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hx' c h.c_mem).symm)
  have hdL' : d ∈ L.map (MulAut.conj w).toMonoidHom := by
    rw [Thm90.mem_map_conj_iff]
    have hwd' : w⁻¹ * d * w = d := by
      calc w⁻¹ * d * w = w⁻¹ * (w * d * w⁻¹) * w := by rw [hwd]
        _ = d := by group
    rw [hwd']
    exact h.d_L
  obtain ⟨M, hM, hdM, φ, hφ, hφd⟩ := Thm90.point_component hJ hxprime hp7 hxp hcY hdY hL e hxL
    hθ h.d_L hd3 h.d_ne
  obtain ⟨M', hM', hdM', φ', hφ', -⟩ := Thm90.point_component hJ hxprime hp7 hxp hc'Y hdY hL' e'
    hxL' hθ' hdL' hd3 h.d_ne
  have hAe_Y := Thm90.isElemAbelian_subgroupOf (Y := Subgroup.centralizer ({x} : Set G)) hAe
  have hA27_Y : Nat.card (A.subgroupOf (Subgroup.centralizer ({x} : Set G))) = 27 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv).trans hA27
  have hdY' : (⟨d, hdY⟩ : ↥(Subgroup.centralizer ({x} : Set G))) ∈
      Subgroup.zpowers (⟨c, hcY⟩ : ↥(Subgroup.centralizer ({x} : Set G))) ⊔
        Subgroup.zpowers (⟨w * c * w⁻¹, hc'Y⟩ : ↥(Subgroup.centralizer ({x} : Set G))) := by
    rw [← Subgroup.mem_map_iff_mem (Subgroup.centralizer ({x} : Set G)).subtype_injective,
      Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    exact hdc
  exact Thm90.false_of_two_points hJ (Thm90.K9For_J2 hK9) h45 h48 h1 h2 hY hAe_Y hA27_Y
    (c := ⟨c, hcY⟩) (c' := ⟨w * c * w⁻¹, hc'Y⟩) (d := ⟨d, hdY⟩)
    (Subgroup.mem_subgroupOf.mpr h.c_mem) (Subgroup.mem_subgroupOf.mpr hc'A)
    (fun h' => hc1 (congrArg Subtype.val h')) (fun h' => hc'1 (congrArg Subtype.val h')) hdY'
    hM hM' hdM hdM' φ hφ hφd φ' hφ'

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
