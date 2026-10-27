module

public import CFSG.RankThree.GF2n.Stroth80.Sec711Setup
public import CFSG.RankThree.GF2n.Stroth80.Sec12Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec83ChiEndo
public import CFSG.RankThree.GF2n.Stroth80.Sec83UpperModule
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly1015

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem n12l3_QB_inf_le_LB {G : Type} [Group G] [Finite G] {M Q B : Subgroup G} :
    QB B ⊓ M ≤ LB M Q B :=
  le_sup_right

theorem n12l3_X_facts {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (hc : Ctx M Q Z B) {t g : G} (hg : g ∈ n12X hc t) :
    g ∈ M ∧ g ∈ H0 M Z ∧ g ∈ hc.CN t :=
  ⟨hg.1.2, hc.LB_le_H0' (n12l3_QB_inf_le_LB hg.1), hg.2⟩

theorem n12l3_Y_facts {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (hc : Ctx M Q Z B) {t r g : G} (hrM : r ∈ M) (hg : g ∈ n12Y hc t r) :
    g ∈ M ∧ g ∈ H0 M Z ∧ g ∈ hc.CN t :=
  ⟨hg.1.2, (hc.conj_of_mem hrM).LB_le_H0' (n12l3_QB_inf_le_LB hg.1), hg.2⟩

theorem n12l3_union_facts {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (hc : Ctx M Q Z B) {t r g : G} (hrM : r ∈ M) (hg : g ∈ n12X hc t ∪ n12Y hc t r) :
    g ∈ M ∧ g ∈ H0 M Z ∧ g ∈ hc.CN t := by
  rcases hg with h | h
  · exact n12l3_X_facts hc h
  · exact n12l3_Y_facts hc hrM h

theorem n12l3_normalizes_Q {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (hc : Ctx M Q Z B) {g : G} (hgM : g ∈ M) {a : G} (ha : a ∈ Q) : g * a * g⁻¹ ∈ Q :=
  (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hgM) a).mp ha

theorem n12l3_conj_eq_of_H0 {G : Type} [Group G] {M Z : Subgroup G} {g : G}
    (hg : g ∈ H0 M Z) {z : G} (hz : z ∈ Z) : g * z * g⁻¹ = z := by
  have hgC : g ∈ Subgroup.centralizer (Z : Set G) :=
    (show g ∈ M ⊓ Subgroup.centralizer (Z : Set G) from hg).2
  have hzg : z * g = g * z := Subgroup.mem_centralizer_iff.mp hgC z hz
  exact mul_inv_eq_iff_eq_mul.mpr hzg.symm

theorem n12l3_Z_le_W {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (hc : Ctx M Q Z B) (t : G) : Z ≤ Wt Q (Vt M (LB M Q B) B Z t) :=
  fun z hz => ⟨hc.Z_le_Q hz, Subgroup.mem_centralizer_iff.mpr fun v hv =>
    (hc.hyp.toHyp79.V_central hz (hc.Vt_le_Q t hv)).symm⟩

theorem n12l3_Wt_le_Q {G : Type} [Group G] (Q V : Subgroup G) : Wt Q V ≤ Q :=
  inf_le_left

theorem n12l3_secHyp {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (hc : Ctx M Q Z B) {R : Subgroup G} (hRM : R ≤ M) : SecHyp R Q Z :=
  ⟨hc.Z_le_Q, fun x hx y hy => hc.hyp.toHyp79.comm_mem_V hx hy,
    fun x hx => hc.hyp.toHyp79.sq_mem_V hx,
    fun r hr x hx => (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hRM hr)) x).mp hx,
    fun r hr x hx => (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (hRM hr)) x).mp hx⟩

theorem n12l3_comm_mem_W {G : Type} [Group G] [Finite G] {R Q Z V W : Subgroup G} {t : G}
    (hSec : SecHyp R Q Z) (hchi : IsChiIso Q R W V Z t) (hVQ : V ≤ Q) (hZW : Z ≤ W)
    (hZV : Z ≤ V) {g : G} (hgR : g ∈ R) (hgV : ∀ v ∈ V, ⁅g, v⁆ ∈ Z) {a : G} (ha : a ∈ Q) :
    ⁅g, a⁆ ∈ W := by
  obtain ⟨Mo, _, _, κ, hκ⟩ := exists_sectionModule hSec
  obtain ⟨ε, hεκ, hker, -, hεR⟩ := exists_chi_endo hκ hchi hVQ hZW hZV hSec.normP
  have hfix : ∀ v : G, ∀ hvQ : v ∈ Q, v ∈ V →
      (⟨g, hgR⟩ : ↥R) • Multiplicative.toAdd (κ ⟨v, hvQ⟩) =
        Multiplicative.toAdd (κ ⟨v, hvQ⟩) := by
    intro v hvQ hv
    have hcQ : ⁅g, v⁆ ∈ Q := hSec.le (hgV v hv)
    have h1 : (⟨g, hgR⟩ : ↥R) • Multiplicative.toAdd (κ ⟨v, hvQ⟩) -
        Multiplicative.toAdd (κ ⟨v, hvQ⟩) = Multiplicative.toAdd (κ ⟨⁅g, v⁆, hcQ⟩) :=
      smul_toAdd_sub_eq hκ hSec.normP ⟨g, hgR⟩ ⟨v, hvQ⟩ hcQ
    have h2 : κ ⟨⁅g, v⁆, hcQ⟩ = 1 := (hκ.ker _).mpr (hgV v hv)
    rw [h2, toAdd_one] at h1
    exact sub_eq_zero.mp h1
  have hcQ' : ⁅g, a⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem (hSec.normP g hgR a ha) (Q.inv_mem ha)
  have h1 : (⟨g, hgR⟩ : ↥R) • Multiplicative.toAdd (κ ⟨a, ha⟩) -
      Multiplicative.toAdd (κ ⟨a, ha⟩) = Multiplicative.toAdd (κ ⟨⁅g, a⁆, hcQ'⟩) :=
    smul_toAdd_sub_eq hκ hSec.normP ⟨g, hgR⟩ ⟨a, ha⟩ hcQ'
  have hεa : ε (Multiplicative.toAdd (κ ⟨a, ha⟩)) =
      Multiplicative.toAdd (κ ⟨⁅a, t⁆, hVQ (hchi.1 a ha)⟩) := hεκ ⟨a, ha⟩
  have h0 : ε (Multiplicative.toAdd (κ ⟨⁅g, a⁆, hcQ'⟩)) = 0 := by
    rw [← h1, map_sub, hεR, hεa]
    exact sub_eq_zero.mpr (hfix ⁅a, t⁆ (hVQ (hchi.1 a ha)) (hchi.1 a ha))
  have hmem : Multiplicative.toAdd (κ ⟨⁅g, a⁆, hcQ'⟩) ∈ ε.ker :=
    AddMonoidHom.mem_ker.mpr h0
  rw [hker] at hmem
  exact (toAdd_mem_secSub_iff hκ hZW ⟨⁅g, a⁆, hcQ'⟩).mp hmem

theorem n12l3_mul_mem_sum {G : Type} [Group G] {A C V : Subgroup G} {a b : G}
    (ha : a ∈ A) (hb : b ∈ C) : a * b ∈ A ⊔ C ⊔ V := by
  have hA : A ≤ A ⊔ C ⊔ V := (le_sup_left : A ≤ A ⊔ C).trans le_sup_left
  have hC : C ≤ A ⊔ C ⊔ V := (le_sup_right : C ≤ A ⊔ C).trans le_sup_left
  exact (A ⊔ C ⊔ V).mul_mem (hA ha) (hC hb)

theorem n12l3_mem_inf_QB {G : Type} [Group G] [Finite G] {Q B V : Subgroup G} {x : G}
    (hx : x ∈ QB B ⊓ Wt Q V) : x ∈ Q ⊓ QB B :=
  ⟨n12l3_Wt_le_Q Q V hx.2, hx.1⟩

theorem n12l3_comm_inf_QB {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (hc : Ctx M Q Z B) : ∀ x ∈ Q ⊓ QB B, ∀ y ∈ Q ⊓ QB B, ⁅x, y⁆ = 1 := by
  intro x hx y hy
  have h : x * y = y * x :=
    congrArg Subtype.val (hc.inf_QB_elemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  exact commutatorElement_eq_one_iff_commute.2 h

theorem n12Lemma3_of (h34 : Stroth34Statement) (h52a : Stroth52aStatement)
    (h52c : Stroth52cStatement) : N12Lemma3Statement := by
  intro G _ _ M Q Z B hc n t r hs hr
  have hrM : r ∈ M := hc.Rt_le_M t hr.mem
  have hc' : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hVW : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) :=
    Vt_le_Wt_of_34 h34 hc hs.toSec5
  obtain ⟨hWdec, hNW⟩ := h52a G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
    (conjSubgroup r B) (hc.CN t) (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t))
    rfl rfl rfl rfl
  have hchi := h52c G M Q Z B hc n t hs.toSec5 hs.omegaNat (Rt M (LB M Q B) t)
    (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl
  have hSec : SecHyp (Rt M (LB M Q B) t) Q Z := n12l3_secHyp hc (hc.Rt_le_M t)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg a ha
    exact n12l3_normalizes_Q hc (n12l3_union_facts hc hrM hg).1 ha
  · intro g hg z hz
    exact n12l3_conj_eq_of_H0 (n12l3_union_facts hc hrM hg).2.1 hz
  · intro g hg a ha
    obtain ⟨hgR, hgV⟩ := Ctx.mem_CN.mp (n12l3_union_facts hc hrM hg).2.2
    exact n12l3_comm_mem_W hSec hchi (hc.Vt_le_Q t) (n12l3_Z_le_W hc t) le_sup_left hgR hgV ha
  · intro g hg a ha
    exact hNW g (n12l3_union_facts hc hrM hg).2.2 a ha
  · intro a ha b hb
    exact n12l3_comm_inf_QB hc a (n12l3_mem_inf_QB ha) b (n12l3_mem_inf_QB hb)
  · intro a ha b hb
    exact n12l3_comm_inf_QB hc' a (n12l3_mem_inf_QB ha) b (n12l3_mem_inf_QB hb)
  · apply le_antisymm
    · intro x hx
      obtain ⟨a, ha, b, hb, hxab⟩ := hWdec x hx
      rw [hxab]
      exact n12l3_mul_mem_sum ha hb
    · exact sup_le (sup_le inf_le_right inf_le_right) hVW

end CFSG.RankThree.GF2n.Stroth80
