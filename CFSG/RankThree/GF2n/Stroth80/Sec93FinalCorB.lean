module

public import CFSG.RankThree.GF2n.Stroth80.Sec93FinalWC
public import CFSG.RankThree.GF2n.Stroth80.Sec4Model

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem sec93f_mem_Q_of_mk_mul_comm {a b : M}
    (h : QuotientGroup.mk' (Q.subgroupOf M) a * QuotientGroup.mk' (Q.subgroupOf M) b =
      QuotientGroup.mk' (Q.subgroupOf M) b * QuotientGroup.mk' (Q.subgroupOf M) a) :
    ⁅(a : G), (b : G)⁆ ∈ Q := by
  have h1 : QuotientGroup.mk' (Q.subgroupOf M) ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr h
  have h2 : ⁅a, b⁆ ∈ Q.subgroupOf M := (QuotientGroup.eq_one_iff _).mp h1
  have := Subgroup.mem_subgroupOf.mp h2
  simpa [commutatorElement_def] using this

theorem sec93f_mem_normalizer_map {X : Type*} [Group X] {H : Subgroup X} (P : Subgroup H)
    [hP : P.Normal] {h : X} (hh : h ∈ H) :
    h ∈ Subgroup.normalizer ((P.map H.subtype : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨⟨h, hh⟩ * q * (⟨h, hh⟩ : H)⁻¹, hP.conj_mem q hq _, rfl⟩
  · intro hx
    obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp hx
    have hq' : (q : X) = h * x * h⁻¹ := hqx
    refine Subgroup.mem_map.mpr
      ⟨⟨h⁻¹, H.inv_mem hh⟩ * q * (⟨h⁻¹, H.inv_mem hh⟩ : H)⁻¹, hP.conj_mem q hq _, ?_⟩
    show h⁻¹ * (q : X) * h⁻¹⁻¹ = x
    rw [hq']
    group

theorem sec93f_corBHyp (hc : Ctx M Q Z B) {t : G} {Z0 : Subgroup G} (hQZ0 : Q ≤ Z0)
    (hZ0M : Z0 ≤ M) (hZ0H : Z0 ≤ H0 M Z) (hZ0L : Z0 ≤ LB M Q B) (hZ0N : Z0 ≤ hc.CN t)
    (hcentre : ∀ s ∈ Z0, s ∉ Q → ⁅Q, Subgroup.zpowers s⁆ ⊔ Z = Vt M (LB M Q B) B Z t)
    (hwc : WeaklyClosedInCent M Q Z0) :
    CorBHyp ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) := by
  set Hb : Subgroup (Mbar M Q) := bar M Q (H0 M Z) with hHb
  set T : Subgroup ↥Hb := (bar M Q Z0).subgroupOf Hb with hT
  have lift : ∀ g : ↥Hb, ∃ m : M, QuotientGroup.mk' (Q.subgroupOf M) m = (g : Mbar M Q) := by
    intro g
    obtain ⟨y, -, hy⟩ := Subgroup.mem_map.mp g.2
    exact ⟨y, hy⟩
  have memT : ∀ (x : ↥Hb) (w : M), (x : Mbar M Q) = QuotientGroup.mk' (Q.subgroupOf M) w →
      (x ∈ T ↔ (w : G) ∈ Z0) := by
    intro x w hxw
    rw [hT, Subgroup.mem_subgroupOf, hxw]
    exact mk_mem_bar_iff_sec4 hQZ0 w
  have hbarle : bar M Q Z0 ≤ bar M Q (LB M Q B) :=
    Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hZ0L (Subgroup.mem_subgroupOf.mp hx))
  have hLBel := hc.isElemAbelian_bar_LB
  have hel : IsElemAbelian 2 T := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · have ha : (a.1 : Mbar M Q) ∈ bar M Q Z0 := Subgroup.mem_subgroupOf.mp a.2
      have hb : (b.1 : Mbar M Q) ∈ bar M Q Z0 := Subgroup.mem_subgroupOf.mp b.2
      have h := congrArg Subtype.val
        (hLBel.1.is_comm.comm ⟨_, hbarle ha⟩ ⟨_, hbarle hb⟩)
      exact Subtype.ext (Subtype.ext h)
    · have hx' : (x : Mbar M Q) ∈ bar M Q Z0 := Subgroup.mem_subgroupOf.mp hx
      have h2 := hLBel.2 (x : Mbar M Q) (hbarle hx')
      exact Subtype.ext (by simpa using h2)
  have hQH : Q ≤ H0 M Z := hQZ0.trans hZ0H
  have memHb : ∀ w : M, (w : G) ∈ H0 M Z → QuotientGroup.mk' (Q.subgroupOf M) w ∈ Hb :=
    fun w hw => (mk_mem_bar_iff_sec4 hQH w).mpr hw
  refine ⟨hel, fun g => ?_, fun g => ⟨fun hcomm => ?_, fun hg x hx y hy => ?_⟩⟩
  · obtain ⟨m, hm⟩ := lift g
    by_cases hcase : T ⊓ conjSubgroup g T = ⊥
    · exact Or.inl hcase
    · right
      obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcase
      obtain ⟨hyT, hyg⟩ := Subgroup.mem_inf.mp hy
      obtain ⟨w, hw⟩ := lift y
      have hwZ : (w : G) ∈ Z0 := (memT y w hw.symm).mp hyT
      have hyg' : g⁻¹ * y * g ∈ T := mem_conjSubgroup.mp hyg
      have key : ((g⁻¹ * y * g : ↥Hb) : Mbar M Q) =
          QuotientGroup.mk' (Q.subgroupOf M) (m⁻¹ * w * m) := by
        rw [map_mul, map_mul, map_inv, hm, hw]
        rfl
      have hmwm : ((m⁻¹ * w * m : M) : G) ∈ Z0 := (memT _ _ key).mp hyg'
      have hwQ : (w : G) ∉ Q := by
        intro hwQ
        apply hy1
        have h1 : QuotientGroup.mk' (Q.subgroupOf M) w = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hwQ)
        refine Subtype.ext (Subtype.ext ?_)
        show (y : Mbar M Q) = 1
        rw [← hw]
        exact h1
      have hmM : ((m⁻¹ : M) : G) ∈ M := (m⁻¹).2
      have hconj := sec93f_conj_eq_of_wc hc hZ0M hZ0N hcentre hwc hmM hwZ hwQ (by
        simpa using hmwm)
      have hnorm := conjSubgroup_eq_self_iff.mp hconj
      refine inf_eq_left.mpr fun x hx => ?_
      obtain ⟨w', hw'⟩ := lift x
      have hw'Z : (w' : G) ∈ Z0 := (memT x w' hw'.symm).mp hx
      have key' : ((g⁻¹ * x * g : ↥Hb) : Mbar M Q) =
          QuotientGroup.mk' (Q.subgroupOf M) (m⁻¹ * w' * m) := by
        rw [map_mul, map_mul, map_inv, hm, hw']
        rfl
      refine mem_conjSubgroup.mpr ((memT _ _ key').mpr ?_)
      have h3 := (Subgroup.mem_normalizer_iff.mp hnorm (w' : G)).mp hw'Z
      simpa using h3
  · obtain ⟨m, hm⟩ := lift g
    have hmM : (m : G) ∈ M := m.2
    have hall : ∀ x ∈ Z0, ∀ y ∈ Z0, ⁅(m : G) * x * (m : G)⁻¹, y⁆ ∈ Q := by
      intro x hx y hy
      have hxM : x ∈ M := hZ0M hx
      have hyM : y ∈ M := hZ0M hy
      set xb : ↥Hb := ⟨QuotientGroup.mk' (Q.subgroupOf M) ⟨x, hxM⟩, memHb _ (hZ0H hx)⟩ with hxb
      set yb : ↥Hb := ⟨QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩, memHb _ (hZ0H hy)⟩ with hyb
      have hxbT : xb ∈ T := (memT xb ⟨x, hxM⟩ rfl).mpr hx
      have hybT : yb ∈ T := (memT yb ⟨y, hyM⟩ rfl).mpr hy
      have hcg : g * xb * g⁻¹ ∈ conjSubgroup g T := by
        refine mem_conjSubgroup.mpr ?_
        have e : g⁻¹ * (g * xb * g⁻¹) * g = xb := by group
        rw [e]
        exact hxbT
      have h := congrArg Subtype.val (hcomm yb hybT _ hcg).eq
      have hmk : QuotientGroup.mk' (Q.subgroupOf M) (m * ⟨x, hxM⟩ * m⁻¹) =
          (g : Mbar M Q) * (xb : Mbar M Q) * (g : Mbar M Q)⁻¹ := by
        rw [map_mul, map_mul, map_inv, hm]
      have hcomm' : QuotientGroup.mk' (Q.subgroupOf M) (m * ⟨x, hxM⟩ * m⁻¹) *
          QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩ =
          QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩ *
          QuotientGroup.mk' (Q.subgroupOf M) (m * ⟨x, hxM⟩ * m⁻¹) := by
        rw [hmk]
        exact h.symm
      have := sec93f_mem_Q_of_mk_mul_comm hcomm'
      simpa using this
    have hle : conjSubgroup (m : G) Z0 ≤ Z0 := by
      have hall' := hwc (m : G) hmM hall
      intro x hx
      have hz0 : (m : G)⁻¹ * x * (m : G) ∈ Z0 := mem_conjSubgroup.mp hx
      have := hall' _ hz0
      simpa [mul_assoc] using this
    have hconjeq : conjSubgroup (m : G) Z0 = Z0 :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])
    have hnorm := conjSubgroup_eq_self_iff.mp hconjeq
    have hnorm' : ((m : G))⁻¹ ∈ Subgroup.normalizer (Z0 : Set G) :=
      (Subgroup.normalizer (Z0 : Set G)).inv_mem hnorm
    ext x
    obtain ⟨w, hw⟩ := lift x
    have key : ((g⁻¹ * x * g : ↥Hb) : Mbar M Q) =
        QuotientGroup.mk' (Q.subgroupOf M) (m⁻¹ * w * m) := by
      rw [map_mul, map_mul, map_inv, hm, hw]
      rfl
    rw [mem_conjSubgroup, memT _ _ key, memT x w hw.symm]
    have h3 := Subgroup.mem_normalizer_iff.mp hnorm' (w : G)
    simpa using h3.symm
  · rw [hg] at hy
    exact congrArg Subtype.val (hel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

end CFSG.RankThree.GF2n.Stroth80
