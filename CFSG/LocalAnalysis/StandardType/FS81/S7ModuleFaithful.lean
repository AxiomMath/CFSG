module

public import CFSG.LocalAnalysis.StandardType.FS81.S7E7Incl
public import CFSG.LocalAnalysis.StandardType.FS81.S7CentDefs
import CFSG.LocalAnalysis.StandardType.FS81.S7ModuleTrivial
import CFSG.LocalAnalysis.StandardType.FS81.S7E7InclRange
import CFSG.LocalAnalysis.StandardType.FS81.S7ModuleNontrivial
import CFSG.LocalAnalysis.StandardType.FS81.S7HighRadicalComm
import CFSG.LocalAnalysis.StandardType.FS81.S7NormalizerW
import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourLevi
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction CFSG.QuasithinUnique

local notation "GF₂" => GaloisField 2 1
local notation "tθ" => EPilot.pinnedElt Tag.E8 (highRoot Tag.E8) (1 : GaloisField 2 1)
local notation "Qθ" => EPilot.highRadical Tag.E8 (GaloisField 2 1)
local notation "Dθ" => EPilot.perpLevi Tag.E8 (GaloisField 2 1)
local notation "s₇" => EPilot.pinnedElt Tag.E7 (highRoot Tag.E7) (1 : ZMod 2)
local notation "Q₇" => EPilot.highRadical Tag.E7 (ZMod 2)

private theorem commutator_mul_eq {G : Type*} [Group G] (a b w : G) :
    (a * b) * w * (a * b)⁻¹ * w⁻¹ =
      (a * (b * w * b⁻¹ * w⁻¹) * a⁻¹) * (a * w * a⁻¹ * w⁻¹) := by
  group

private theorem commutator_inv_eq {G : Type*} [Group G] (a w : G) :
    a⁻¹ * w * a * w⁻¹ = a⁻¹ * (a * w * a⁻¹ * w⁻¹)⁻¹ * a := by
  group

private theorem commutator_conj_eq {G : Type*} [Group G] (a n w : G) :
    (a * n * a⁻¹) * w * (a * n * a⁻¹)⁻¹ * w⁻¹ =
      a * (n * (a⁻¹ * w * a) * n⁻¹ * (a⁻¹ * w * a)⁻¹) * a⁻¹ := by
  group

private theorem conj_eq_of_mem_zpowers_of_comm {G : Type*} [Group G] {t a d : G}
    (h : a * t = t * a) (hd : d ∈ Subgroup.zpowers t) : a * d * a⁻¹ = d := by
  have ha : t ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact h
  have hd' : d ∈ Subgroup.centralizer ({a} : Set G) := (Subgroup.zpowers_le.2 ha) hd
  have hc : a * d = d * a := (Subgroup.mem_centralizer_iff.1 hd') a (Set.mem_singleton a)
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]

open scoped Pointwise in
private theorem mem_mul_of_mem_sup {G : Type*} [Group G] {H N : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer N) {y : G} (hy : y ∈ H ⊔ N) :
    ∃ h ∈ H, ∃ n ∈ N, h * n = y := by
  have hcoe : (↑(H ⊔ N) : Set G) = (H : Set G) * (N : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right H N hHN
  have hy' : y ∈ (↑(H ⊔ N) : Set G) := hy
  rw [hcoe] at hy'
  exact Set.mem_mul.1 hy'

section E7Model


theorem mem_map_highRadical_E7_of_trivial_on_modW (x : ↥(adjointGroup .E8 GF₂)) (hx : x ∈ Dθ)
    (hxσ : x * e7Incl s₇ * x⁻¹ * (e7Incl s₇)⁻¹ ∈ Qθ)
    (hxW : ∀ w ∈ modW Qθ tθ (e7Incl s₇), x * w * x⁻¹ * w⁻¹ ∈ Subgroup.zpowers tθ) :
    x ∈ (Q₇).map e7Incl := by
  have hsimple : IsSimpleGroup ↥(EPilot.perpLevi .E7 (ZMod 2)) :=
    E7Pilot.isSimpleGroup_perpLevi_E7 (K := ZMod 2)
  have hHD : Subgroup.centralizer ({tθ} : Set (adjointGroup .E8 GF₂)) = Qθ ⊔ Dθ :=
    (centralizer_pinnedElt_highRoot_E8 (K := GF₂)).1
  have hDnorm : Dθ ≤ Subgroup.normalizer (Qθ : Set (adjointGroup .E8 GF₂)) :=
    (centralizer_pinnedElt_highRoot_E8 (K := GF₂)).2.1
  have hdisj : Disjoint Qθ Dθ := (centralizer_pinnedElt_highRoot_E8 (K := GF₂)).2.2.1
  have hZle : ∀ a ∈ Dθ, a * tθ = tθ * a := by
    intro a ha
    have hac : a ∈ Subgroup.centralizer ({tθ} : Set (adjointGroup .E8 GF₂)) := by
      rw [hHD]; exact (le_sup_right : Dθ ≤ Qθ ⊔ Dθ) ha
    exact ((Subgroup.mem_centralizer_iff.1 hac) tθ (Set.mem_singleton tθ)).symm
  have hUn : ∀ h ∈ Subgroup.centralizer ({tθ} : Set (adjointGroup .E8 GF₂)),
      ∀ u ∈ Qθ, h * u * h⁻¹ ∈ Qθ := by
    intro h hh u hu
    have hh' : h ∈ Qθ ⊔ Dθ := hHD ▸ hh
    have hnorm : h ∈ Subgroup.normalizer (Qθ : Set (adjointGroup .E8 GF₂)) :=
      (sup_le Subgroup.le_normalizer hDnorm) hh'
    exact (Subgroup.mem_normalizer_iff.1 hnorm u).1 hu
  have ht₀U : tθ ∈ Qθ := pinnedElt_highRoot_mem_highRadical (K := GF₂)
  have ht₀H : ∀ h ∈ Subgroup.centralizer ({tθ} : Set (adjointGroup .E8 GF₂)),
      h * tθ = tθ * h := by
    intro h hh
    exact ((Subgroup.mem_centralizer_iff.1 hh) tθ (Set.mem_singleton tθ)).symm
  have hUU : ∀ u ∈ Qθ, ∀ v ∈ Qθ, u * v * u⁻¹ * v⁻¹ ∈ Subgroup.zpowers tθ :=
    commutator_highRadical_le_zpowers (τ := .E8) (Or.inr rfl) (K := GF₂)
      natCard_galoisField_two_one
  have hxrange : x ∈ e7Incl.range := by rw [range_e7Incl]; exact hx
  obtain ⟨y, hy⟩ : ∃ y, e7Incl y = x := by simpa using hxrange
  rw [← hy] at hxσ hxW ⊢
  have hs_D : e7Incl s₇ ∈ Dθ := by rw [← range_e7Incl]; exact ⟨s₇, rfl⟩
  have hy_D : e7Incl y ∈ Dθ := by rw [← range_e7Incl]; exact ⟨y, rfl⟩
  have hxσ_D : e7Incl y * e7Incl s₇ * (e7Incl y)⁻¹ * (e7Incl s₇)⁻¹ ∈ Dθ :=
    mul_mem (mul_mem (mul_mem hy_D hs_D) (inv_mem hy_D)) (inv_mem hs_D)
  have hy_eq_one : y * s₇ * y⁻¹ * s₇⁻¹ = 1 := by
    apply e7Incl_injective
    have h1 : e7Incl y * e7Incl s₇ * (e7Incl y)⁻¹ * (e7Incl s₇)⁻¹ = 1 :=
      (Subgroup.disjoint_def.1 hdisj) hxσ hxσ_D
    have h2 : e7Incl (y * s₇ * y⁻¹ * s₇⁻¹) =
        e7Incl y * e7Incl s₇ * (e7Incl y)⁻¹ * (e7Incl s₇)⁻¹ := by
      simp only [map_mul, map_inv]
    rw [h2, h1, map_one]
  have hycomm : y * s₇ = s₇ * y := by
    have h : (y * s₇) * (s₇ * y)⁻¹ = 1 := by
      simpa [mul_inv_rev, mul_assoc] using hy_eq_one
    exact mul_inv_eq_one.1 h
  have hycent : y ∈ Subgroup.centralizer ({s₇} : Set ↥(adjointGroup .E7 (ZMod 2))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hycomm.symm
  have hdecomp : F4Pilot.IsTwoRadicalDecomp s₇ Q₇ (EPilot.perpLevi .E7 (ZMod 2)) :=
    EPilot.isTwoRadicalDecomp_highRoot (K := ZMod 2) (Or.inr (Or.inl rfl)) one_ne_zero
  obtain ⟨-, hsup, -, hJnorm⟩ := hdecomp
  have hJcent : EPilot.perpLevi .E7 (ZMod 2) ≤
      Subgroup.centralizer ({s₇} : Set ↥(adjointGroup .E7 (ZMod 2))) := by
    rw [← hsup]; exact le_sup_right
  have hy_sup : y ∈ Q₇ ⊔ EPilot.perpLevi .E7 (ZMod 2) := by
    rw [hsup]; exact hycent
  rw [sup_comm] at hy_sup
  obtain ⟨j, hj, q, hq, hjq⟩ := mem_mul_of_mem_sup hJnorm hy_sup
  have hx_eq : e7Incl y = e7Incl j * e7Incl q := by rw [← hjq, map_mul]
  have hσH : e7Incl s₇ ∈ Subgroup.centralizer ({tθ} : Set (adjointGroup .E8 GF₂)) := by
    rw [hHD]; exact (le_sup_right : Dθ ≤ Qθ ⊔ Dθ) hs_D
  let N : Subgroup ↥(EPilot.perpLevi .E7 (ZMod 2)) :=
    { carrier := {h | ∀ w ∈ modW Qθ tθ (e7Incl s₇),
        e7Incl (h : ↥(adjointGroup .E7 (ZMod 2))) * w *
          (e7Incl (h : ↥(adjointGroup .E7 (ZMod 2))))⁻¹ * w⁻¹ ∈ Subgroup.zpowers tθ}
      one_mem' := by
        intro w _
        simp
      mul_mem' := by
        intro a b ha hb w hw
        have haD : e7Incl (a : ↥(adjointGroup .E7 (ZMod 2))) ∈ Dθ := by
          rw [← range_e7Incl]; exact ⟨(a : _), rfl⟩
        have hcomm : e7Incl (a : _) * tθ = tθ * e7Incl (a : _) := hZle _ haD
        have hbZ : e7Incl (b : _) * w * (e7Incl (b : _))⁻¹ * w⁻¹ ∈ Subgroup.zpowers tθ :=
          hb w hw
        have hconj : e7Incl (a : _) * (e7Incl (b : _) * w * (e7Incl (b : _))⁻¹ * w⁻¹) *
            (e7Incl (a : _))⁻¹ ∈ Subgroup.zpowers tθ := by
          rw [conj_eq_of_mem_zpowers_of_comm hcomm hbZ]
          exact hbZ
        have haZ : e7Incl (a : _) * w * (e7Incl (a : _))⁻¹ * w⁻¹ ∈ Subgroup.zpowers tθ :=
          ha w hw
        have hid : e7Incl (↑(a * b) : ↥(adjointGroup .E7 (ZMod 2))) * w *
              (e7Incl (↑(a * b) : ↥(adjointGroup .E7 (ZMod 2))))⁻¹ * w⁻¹ =
            (e7Incl (a : _) * (e7Incl (b : _) * w * (e7Incl (b : _))⁻¹ * w⁻¹) *
              (e7Incl (a : _))⁻¹) * (e7Incl (a : _) * w * (e7Incl (a : _))⁻¹ * w⁻¹) := by
          simp only [Subgroup.coe_mul, map_mul]
          exact commutator_mul_eq _ _ _
        rw [hid]
        exact mul_mem hconj haZ
      inv_mem' := by
        intro a ha w hw
        have haD : e7Incl (a : ↥(adjointGroup .E7 (ZMod 2))) ∈ Dθ := by
          rw [← range_e7Incl]; exact ⟨(a : _), rfl⟩
        have haZ : e7Incl (a : _) * w * (e7Incl (a : _))⁻¹ * w⁻¹ ∈ Subgroup.zpowers tθ :=
          ha w hw
        have hcomm : (e7Incl (a : _))⁻¹ * tθ = tθ * (e7Incl (a : _))⁻¹ :=
          hZle _ (show (e7Incl (a : _))⁻¹ ∈ Dθ from inv_mem haD)
        have hconj : (e7Incl (a : _))⁻¹ *
            (e7Incl (a : _) * w * (e7Incl (a : _))⁻¹ * w⁻¹)⁻¹ *
            ((e7Incl (a : _))⁻¹)⁻¹ ∈ Subgroup.zpowers tθ := by
          rw [conj_eq_of_mem_zpowers_of_comm hcomm
            (show (e7Incl (a : _) * w * (e7Incl (a : _))⁻¹ * w⁻¹)⁻¹ ∈
              Subgroup.zpowers tθ from inv_mem haZ)]
          exact inv_mem haZ
        have hid : e7Incl (↑(a⁻¹) : ↥(adjointGroup .E7 (ZMod 2))) * w *
              (e7Incl (↑(a⁻¹) : ↥(adjointGroup .E7 (ZMod 2))))⁻¹ * w⁻¹ =
            (e7Incl (a : _))⁻¹ * (e7Incl (a : _) * w * (e7Incl (a : _))⁻¹ * w⁻¹)⁻¹ *
              ((e7Incl (a : _))⁻¹)⁻¹ := by
          simp only [Subgroup.coe_inv, map_inv, inv_inv]
          exact commutator_inv_eq _ _
        rw [hid]
        exact hconj }
  have hjN : (⟨j, hj⟩ : ↥(EPilot.perpLevi .E7 (ZMod 2))) ∈ N := by
    intro w hw
    change e7Incl j * w * (e7Incl j)⁻¹ * w⁻¹ ∈ Subgroup.zpowers tθ
    have hqinv : (e7Incl q)⁻¹ ∈ (Q₇).map e7Incl :=
      Subgroup.inv_mem _ (Subgroup.mem_map.2 ⟨q, hq, rfl⟩)
    have hdZ : (e7Incl q)⁻¹ * w * ((e7Incl q)⁻¹)⁻¹ * w⁻¹ ∈ Subgroup.zpowers tθ :=
      highRadical_E7_trivial_on_modW _ hqinv w hw
    have hxZ : e7Incl y * w * (e7Incl y)⁻¹ * w⁻¹ ∈ Subgroup.zpowers tθ := hxW w hw
    have hterm1 : e7Incl y * ((e7Incl q)⁻¹ * w * ((e7Incl q)⁻¹)⁻¹ * w⁻¹) * (e7Incl y)⁻¹ ∈
        Subgroup.zpowers tθ := by
      rw [conj_eq_of_mem_zpowers_of_comm (hZle _ hy_D) hdZ]
      exact hdZ
    have hg_eq : e7Incl j = e7Incl y * (e7Incl q)⁻¹ := by rw [hx_eq]; group
    have hid : e7Incl j * w * (e7Incl j)⁻¹ * w⁻¹ =
        (e7Incl y * ((e7Incl q)⁻¹ * w * ((e7Incl q)⁻¹)⁻¹ * w⁻¹) * (e7Incl y)⁻¹) *
          (e7Incl y * w * (e7Incl y)⁻¹ * w⁻¹) := by
      rw [hg_eq, commutator_mul_eq]
    rw [hid]
    exact mul_mem hterm1 hxZ
  have hNnormal : N.Normal :=
    ⟨fun n hn g => by
      intro w hw
      have hgD : e7Incl (g : ↥(adjointGroup .E7 (ZMod 2))) ∈ Dθ := by
        rw [← range_e7Incl]; exact ⟨(g : _), rfl⟩
      have hgH : e7Incl (g : _) ∈
          Subgroup.centralizer ({tθ} : Set (adjointGroup .E8 GF₂)) := by
        rw [hHD]; exact (le_sup_right : Dθ ≤ Qθ ⊔ Dθ) hgD
      have hgcomm : ((g : ↥(EPilot.perpLevi .E7 (ZMod 2))) : ↥(adjointGroup .E7 (ZMod 2))) *
          s₇ = s₇ * ((g : ↥(EPilot.perpLevi .E7 (ZMod 2))) : ↥(adjointGroup .E7 (ZMod 2))) := by
        have h := (Subgroup.mem_centralizer_iff.1 (hJcent g.2)) s₇ (Set.mem_singleton s₇)
        exact h.symm
      have hg1 : ((g : ↥(EPilot.perpLevi .E7 (ZMod 2))) : ↥(adjointGroup .E7 (ZMod 2))) * s₇ *
          (((g : ↥(EPilot.perpLevi .E7 (ZMod 2))) : ↥(adjointGroup .E7 (ZMod 2))))⁻¹ * s₇⁻¹ =
          1 := by rw [hgcomm]; group
      have hgσ : e7Incl (g : _) * e7Incl s₇ * (e7Incl (g : _))⁻¹ * (e7Incl s₇)⁻¹ ∈ Qθ := by
        have h2 : e7Incl (((g : ↥(EPilot.perpLevi .E7 (ZMod 2))) :
              ↥(adjointGroup .E7 (ZMod 2))) * s₇ *
              (((g : ↥(EPilot.perpLevi .E7 (ZMod 2))) : ↥(adjointGroup .E7 (ZMod 2))))⁻¹ *
              s₇⁻¹) = 1 := by rw [hg1, map_one]
        have h3 : e7Incl (g : _) * e7Incl s₇ * (e7Incl (g : _))⁻¹ * (e7Incl s₇)⁻¹ = 1 := by
          simpa only [map_mul, map_inv] using h2
        rw [h3]; exact Subgroup.one_mem Qθ
      have hgnorm : e7Incl (g : _) ∈
          Subgroup.normalizer (modW Qθ tθ (e7Incl s₇) : Set (adjointGroup .E8 GF₂)) :=
        mem_normalizer_commutator_sup hUn ht₀U ht₀H hUU hσH hgH hgσ
      have hwW : (e7Incl (g : _))⁻¹ * w * e7Incl (g : _) ∈ modW Qθ tθ (e7Incl s₇) :=
        (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hgnorm) w).1 hw
      have hnZ : e7Incl (n : _) * ((e7Incl (g : _))⁻¹ * w * e7Incl (g : _)) *
          (e7Incl (n : _))⁻¹ * ((e7Incl (g : _))⁻¹ * w * e7Incl (g : _))⁻¹ ∈
          Subgroup.zpowers tθ := hn _ hwW
      have hconjZ : e7Incl (g : _) * (e7Incl (n : _) *
            ((e7Incl (g : _))⁻¹ * w * e7Incl (g : _)) * (e7Incl (n : _))⁻¹ *
            ((e7Incl (g : _))⁻¹ * w * e7Incl (g : _))⁻¹) * (e7Incl (g : _))⁻¹ ∈
          Subgroup.zpowers tθ := by
        rw [conj_eq_of_mem_zpowers_of_comm (hZle _ hgD) hnZ]
        exact hnZ
      have hid : e7Incl (↑(g * n * g⁻¹) : ↥(adjointGroup .E7 (ZMod 2))) * w *
            (e7Incl (↑(g * n * g⁻¹) : ↥(adjointGroup .E7 (ZMod 2))))⁻¹ * w⁻¹ =
          e7Incl (g : _) * (e7Incl (n : _) *
            ((e7Incl (g : _))⁻¹ * w * e7Incl (g : _)) * (e7Incl (n : _))⁻¹ *
            ((e7Incl (g : _))⁻¹ * w * e7Incl (g : _))⁻¹) * (e7Incl (g : _))⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
        exact commutator_conj_eq _ _ _
      rw [hid]
      exact hconjZ⟩
  have : N.Normal := hNnormal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hN | hN
  ·
    have hj1 : j = 1 := by
      have hjmem := hjN
      rw [hN] at hjmem
      have h := Subgroup.mem_bot.1 hjmem
      have h2 := congrArg (fun z : ↥(EPilot.perpLevi .E7 (ZMod 2)) =>
        (z : ↥(adjointGroup .E7 (ZMod 2)))) h
      simpa using h2
    refine Subgroup.mem_map.2 ⟨q, hq, ?_⟩
    rw [hx_eq, hj1, map_one, one_mul]
  ·
    obtain ⟨j₀, hj₀, w₀, hw₀, hne⟩ := exists_perpLevi_E7_not_trivial_on_modW
    have hmem : (⟨j₀, hj₀⟩ : ↥(EPilot.perpLevi .E7 (ZMod 2))) ∈ N := by
      rw [hN]; trivial
    exact absurd (hmem w₀ hw₀) hne

end E7Model

end CFSG.StandardType.FrameRoute.FS81

end
