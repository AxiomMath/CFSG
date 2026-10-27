module

public import CFSG.LocalAnalysis.StandardType.FS81.E7RecogPieces
public import CFSG.LocalAnalysis.StandardType.FS81.RootFusionGen
public import CFSG.LocalAnalysis.StandardType.FS81.S7Model
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotUniqueFieldInner
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClasses
public import CFSG.GF2Type.SmithTypeE.E8.E23aMod
public import CFSG.GF2Type.SmithTypeE.E7Order
import CFSG.LocalAnalysis.StandardType.FS81.S79Radical
public import CFSG.GF2Type.SmithTypeE.E8.SfCent
public import CFSG.GF2Type.SmithTypeE.Parts
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverCentral
public import CFSG.LargeExtraspecial.GLRElimInv
public import CFSG.LargeExtraspecial.GLRTransfer
public import CFSG.LargeExtraspecial.S14C10Apply
public import CFSG.LargeExtraspecial.S14C12Lit
public import CFSG.LargeExtraspecial.S14Claims
public import CFSG.LargeExtraspecial.S4EightA
public import CFSG.LargeExtraspecial.S4EightB
public import CFSG.LargeExtraspecial.S4EightC
public import CFSG.LargeExtraspecial.S4EightD
public import CFSG.LargeExtraspecial.S4EightE
public import CFSG.LargeExtraspecial.S4EightF4
public import CFSG.LargeExtraspecial.S4EightMain
public import CFSG.LargeExtraspecial.S4SevenB3
public import CFSG.LargeExtraspecial.S5Comp

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
  CFSG.QuasithinUnique

theorem eq_top_of_rootCent {G : Type} [Group G] [Finite G] (hHolt : HoltSimpleControl)
    {Y S : Subgroup G} {t b : G} (hYs : IsSimpleGroup ↥Y) (hYna : ∃ a c : ↥Y, a * c ≠ c * a)
    (hYo : ∀ m : ℕ, 2 ≤ m → 2 * Nat.card ↥Y ≠ (2 * m).factorial)
    (hS : IsSylow2In S Y) (htS : t ∈ S) (ht : orderOf t = 2) (htc : ∀ s ∈ S, s * t = t * s)
    (htC : Subgroup.centralizer ({t} : Set G) ≤ Y) (hbC : Subgroup.centralizer ({b} : Set G) ≤ Y)
    (hfus : ∀ g : G, g * b * g⁻¹ ∈ Y → ∃ y ∈ Y, g * b * g⁻¹ = y * b * y⁻¹)
    (hinv : ∀ w ∈ Y, orderOf w = 2 → ∃ y ∈ Y, Commute w (y * b * y⁻¹)) : Y = ⊤ := by
  have hcomm : ∀ g : G, g * t * g⁻¹ ∈ Y →
      ∃ y ∈ Y, Commute (g * t * g⁻¹) (y * b * y⁻¹) := by
    intro g hg
    exact hinv _ hg (by simpa [ht] using (MulAut.conj g).orderOf_eq t)
  exact hHolt G Y S t hYs hYna hYo hS htS ht htc
    (fun g hg => mem_of_conj_mem_of_commute_conj hbC (fun x hx => hfus x (htC hx)) hcomm hg)

private theorem fusion_of_conj {G : Type} [Group G] {Y : Subgroup G} {b₀ b y₀ : G}
    (hy₀ : y₀ ∈ Y) (hb₀ : b₀ = y₀ * b * y₀⁻¹)
    (hfus : ∀ g : G, g * b * g⁻¹ ∈ Y → ∃ y ∈ Y, g * b * g⁻¹ = y * b * y⁻¹) :
    ∀ g : G, g * b₀ * g⁻¹ ∈ Y → ∃ y ∈ Y, g * b₀ * g⁻¹ = y * b₀ * y⁻¹ := by
  intro g hg
  have hg' : (g * y₀) * b * (g * y₀)⁻¹ ∈ Y := by
    rw [show (g * y₀) * b * (g * y₀)⁻¹ = g * b₀ * g⁻¹ by rw [hb₀]; group]
    exact hg
  obtain ⟨y, hy, hyb⟩ := hfus (g * y₀) hg'
  refine ⟨y * y₀⁻¹, Y.mul_mem hy (Y.inv_mem hy₀), ?_⟩
  calc g * b₀ * g⁻¹ = (g * y₀) * b * (g * y₀)⁻¹ := by rw [hb₀]; group
    _ = y * b * y⁻¹ := hyb
    _ = (y * y₀⁻¹) * b₀ * (y * y₀⁻¹)⁻¹ := by rw [hb₀]; group

section ModelFacts


private noncomputable def e7ModelHom {G : Type} [Group G] {Y : Subgroup G}
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) : ↥(adjointGroup .E7 (ZMod 2)) →* G :=
  Y.subtype.comp ψ.toMonoidHom

private theorem e7ModelHom_injective {G : Type} [Group G] {Y : Subgroup G}
    {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y} : Function.Injective (e7ModelHom ψ) := by
  intro a c h
  exact ψ.injective (Subtype.ext h)

private theorem e7ModelHom_range {G : Type} [Group G] {Y : Subgroup G}
    {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y} : (e7ModelHom ψ).range = Y := by
  ext x
  constructor
  · rintro ⟨m, rfl⟩
    exact (ψ m).2
  · intro hx
    exact ⟨ψ.symm ⟨x, hx⟩, by simp [e7ModelHom]⟩

private theorem e7HighInv_orderOf : orderOf e7HighInv = 2 := by
  simpa [e7HighInv, EPilot.pinnedElt] using
    E6Pilot.orderOf_pinnedX_one_adjointGroup (τ := .E7) (K := ZMod 2) (highRoot .E7)

private theorem e7HighInv_mem_highRootSL2 :
    (e7HighInv : ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2) := by
  simpa [e7HighInv, EPilot.pinnedElt] using
    CFSG.GF2Type.SmithTypeE.E8.pinnedX_highRoot_mem_highRootSL2

private theorem e7HighInv_mem_highRadical :
    e7HighInv ∈ EPilot.highRadical .E7 (ZMod 2) := by
  have hθ : highRoot .E7 ∈ parabolicRadicalRoots .E7 (EPilot.perpNodes .E7) :=
    (EPilot.mem_parabolicRadicalRoots_perpNodes_iff_iform (Or.inr (Or.inl rfl))).2
      ⟨isRoot_highRoot _, iform_self_pos_of_isRoot (isRoot_highRoot _)⟩
  exact Subgroup.mem_subgroupOf.2 (pinnedX_mem_rootSpan hθ 1)

private theorem e7_twoRadicalDecomp :
    F4Pilot.IsTwoRadicalDecomp e7HighInv (EPilot.highRadical .E7 (ZMod 2))
      (EPilot.perpLevi .E7 (ZMod 2)) :=
  EPilot.isTwoRadicalDecomp_highRoot (Or.inr (Or.inl rfl)) (one_ne_zero : (1 : ZMod 2) ≠ 0)

private theorem e7_perpLevi_le_centralizer_highRootSL2 :
    EPilot.perpLevi .E7 (ZMod 2) ≤ Subgroup.centralizer (e7JTheta :
      Set ↥(adjointGroup .E7 (ZMod 2))) :=
  E7Pilot.perpLevi_le_centralizer_highRootSL2_E7_of_charTwo

private theorem e7_centralizer_inf_eq_bot {G : Type} [Group G] {Y : Subgroup G}
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) :
    Subgroup.centralizer (Y : Set G) ⊓ Y = ⊥ := by
  have hZ : Subgroup.center ↥(adjointGroup .E7 (ZMod 2)) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot_field .E7 (ZMod 2)
  have h := centralizer_range_inf_range_eq_map_center (e7ModelHom ψ) (e7ModelHom_injective (ψ := ψ))
  rw [e7ModelHom_range, hZ, Subgroup.map_bot] at h
  exact h

private theorem e7_twoSubgroup_bot {G : Type} [Group G] [Finite G] {Y : Subgroup G}
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) {r : ↥(adjointGroup .E7 (ZMod 2))}
    (hrJ : r ∈ e7JTheta) (hr3 : orderOf r = 3)
    (hCY : Subgroup.centralizer ({((ψ r : ↥Y) : G)} : Set G) ⊓ Y =
      Subgroup.zpowers ((ψ r : ↥Y) : G) ⊔
        (EPilot.perpLevi .E7 (ZMod 2)).map (e7ModelHom ψ)) :
    ∀ P : Subgroup G, IsPGroup 2 P →
      P ≤ Subgroup.centralizer ({((ψ r : ↥Y) : G)} : Set G) ⊓ Y →
      Subgroup.centralizer ({((ψ r : ↥Y) : G)} : Set G) ⊓ Y ≤
        Subgroup.normalizer (P : Set G) → P = ⊥ := by
  intro P hP hPC hPN
  have hιinj := e7ModelHom_injective (ψ := ψ)
  have hb3 : orderOf (((ψ r : ↥Y) : G)) = 3 := by
    exact (orderOf_injective (e7ModelHom ψ) hιinj r).trans hr3
  have hDC : EPilot.perpLevi .E7 (ZMod 2) ≤
      Subgroup.centralizer ({r} : Set ↥(adjointGroup .E7 (ZMod 2))) :=
    e7_perpLevi_le_centralizer_highRootSL2.trans
      (Subgroup.centralizer_le (by rintro x rfl; exact hrJ))
  have hKb : (EPilot.perpLevi .E7 (ZMod 2)).map (e7ModelHom ψ) ≤
      Subgroup.centralizer ({((ψ r : ↥Y) : G)} : Set G) := by
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show e7ModelHom ψ d * e7ModelHom ψ r = e7ModelHom ψ r * e7ModelHom ψ d
    rw [← map_mul, ← map_mul]
    exact congrArg (e7ModelHom ψ) (Subgroup.mem_centralizer_singleton_iff.1 (hDC hd))
  haveI hDsimple : IsSimpleGroup (EPilot.perpLevi .E7 (ZMod 2)) :=
    E7Pilot.isSimpleGroup_perpLevi_E7 (K := ZMod 2)
  have hKsimple : IsSimpleGroup ((EPilot.perpLevi .E7 (ZMod 2)).map (e7ModelHom ψ)) :=
    (Subgroup.equivMapOfInjective _ _ hιinj).symm.isSimpleGroup
  have hKcenter : Subgroup.center ((EPilot.perpLevi .E7 (ZMod 2)).map (e7ModelHom ψ)) = ⊥ := by
    rw [← Subgroup.map_center_eq (Subgroup.equivMapOfInjective _ _ hιinj),
      E7Pilot.center_perpLevi_E7_eq_bot (K := ZMod 2), Subgroup.map_bot]
  exact eq_bot_of_isPGroup_of_normalized_of_eq_sup_zpowers hb3 hKb hCY hKsimple hKcenter
    hP hPC hPN

private theorem e7_order_condition :
    ∀ m : ℕ, 2 ≤ m → 2 * Nat.card ↥(adjointGroup .E7 (ZMod 2)) ≠ (2 * m).factorial := by
  have hcard : Nat.card ↥(adjointGroup .E7 (ZMod 2)) = ordE7 2 := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E7 (K := ZMod 2), Nat.card_zmod]
  have h127 : 127 ∣ Nat.card ↥(adjointGroup .E7 (ZMod 2)) := by
    rw [hcard, CFSG.GF2Type.SmithTypeE.ordE7_two]
    norm_num
  have h23 : ¬ 23 ∣ Nat.card ↥(adjointGroup .E7 (ZMod 2)) := by
    rw [hcard, CFSG.GF2Type.SmithTypeE.ordE7_two]
    norm_num
  intro m _ heq
  have h127dvd : 127 ∣ (2 * m).factorial := by
    rw [← heq]
    exact dvd_mul_of_dvd_right h127 2
  have h127le : 127 ≤ 2 * m :=
    (Nat.Prime.dvd_factorial (by norm_num : Nat.Prime 127)).mp h127dvd
  have h23dvd : 23 ∣ (2 * m).factorial :=
    (Nat.Prime.dvd_factorial (by norm_num : Nat.Prime 23)).mpr (by omega)
  have h23dvd2 : 23 ∣ 2 * Nat.card ↥(adjointGroup .E7 (ZMod 2)) := by
    rw [heq]
    exact h23dvd
  have h23' : 23 ∣ Nat.card ↥(adjointGroup .E7 (ZMod 2)) := by
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 23)).mp h23dvd2 with h | h
    · norm_num at h
    · exact h
  exact h23 h23'

private theorem e7_exists_sylow_central :
    ∃ S : Sylow 2 ↥(adjointGroup .E7 (ZMod 2)),
      e7HighInv ∈ (S : Subgroup ↥(adjointGroup .E7 (ZMod 2))) ∧
        e7HighInv ∈ Subgroup.centralizer
          ((S : Subgroup ↥(adjointGroup .E7 (ZMod 2))) : Set ↥(adjointGroup .E7 (ZMod 2))) := by
  haveI : CharP (ZMod 2) 2 := ZMod.charP 2
  refine ⟨E8Pilot.posUnipotentSylowE .E7 (ZMod 2), ?_, ?_⟩
  · rw [E8Pilot.mem_posUnipotentSylowE]
    exact pinnedX_mem_posUnipotent_annih (isRoot_highRoot .E7) (height_highRoot_pos .E7) 1
  · rw [Subgroup.mem_centralizer_iff]
    intro u hu
    refine Subtype.ext ?_
    have h := E8Pilot.posUnipotent_le_centralizer_pinnedX_highRoot (τ := .E7) (K := ZMod 2) 1
      (E8Pilot.mem_posUnipotentSylowE.1 hu)
    exact Subgroup.mem_centralizer_singleton_iff.1 h

private theorem e7_involution_commute {G : Type} [Group G] {Y : Subgroup G}
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) {r : ↥(adjointGroup .E7 (ZMod 2))}
    (hrJ : r ∈ e7JTheta) :
    ∀ w ∈ Y, orderOf w = 2 →
      ∃ y ∈ Y, Commute w (y * ((ψ r : ↥Y) : G) * y⁻¹) := by
  intro w hwY hw2
  obtain ⟨k, l, hlY, hlw, -⟩ :=
    E7Pilot.exists_mem_conj_eq_symm_e7Rep (K := ZMod 2) (L := Y) (e := ψ.symm) hwY hw2
  have hcomm : Commute (((ψ (E7Pilot.e7Rep (ZMod 2) k) : ↥Y) : G)) (((ψ r : ↥Y) : G)) := by
    have hrC : r ∈ Subgroup.centralizer ({E7Pilot.e7Rep (ZMod 2) k} :
        Set ↥(adjointGroup .E7 (ZMod 2))) :=
      E7Pilot.highRootSL2_subgroupOf_le_centralizer_e7Rep (K := ZMod 2) k hrJ
    have h : r * E7Pilot.e7Rep (ZMod 2) k = E7Pilot.e7Rep (ZMod 2) k * r :=
      Subgroup.mem_centralizer_singleton_iff.1 hrC
    show e7ModelHom ψ (E7Pilot.e7Rep (ZMod 2) k) * e7ModelHom ψ r =
      e7ModelHom ψ r * e7ModelHom ψ (E7Pilot.e7Rep (ZMod 2) k)
    rw [← map_mul, ← map_mul]
    exact (congrArg (e7ModelHom ψ) h).symm
  refine ⟨l⁻¹, Y.inv_mem hlY, ?_⟩
  have hw : w = l⁻¹ * ((ψ (E7Pilot.e7Rep (ZMod 2) k) : ↥Y) : G) * l := by
    calc w = l⁻¹ * (l * w * l⁻¹) * l := by group
      _ = l⁻¹ * ((ψ (E7Pilot.e7Rep (ZMod 2) k) : ↥Y) : G) * l := by
        rw [hlw]
        rfl
  rw [hw]
  have h := hcomm.map (MulAut.conj l⁻¹).toMonoidHom
  simpa [MulAut.conj_apply] using h

private theorem e7_step613_pieces {G : Type} [Group G] {Y : Subgroup G}
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) :
    IsPGroup 2 ((EPilot.highRadical .E7 (ZMod 2)).map (e7ModelHom ψ)) ∧
      ((EPilot.highRadical .E7 (ZMod 2)).map (e7ModelHom ψ) ≤ Y) ∧
      ((EPilot.highRadical .E7 (ZMod 2)).map (e7ModelHom ψ) ≤
        Subgroup.centralizer ({e7ModelHom ψ e7HighInv} : Set G)) ∧
      ((EPilot.perpLevi .E7 (ZMod 2)).map (e7ModelHom ψ) ≤
        Subgroup.centralizer ({e7ModelHom ψ e7HighInv} : Set G)) ∧
      ((EPilot.perpLevi .E7 (ZMod 2)).map (e7ModelHom ψ) ≤
        Subgroup.normalizer (((EPilot.highRadical .E7 (ZMod 2)).map (e7ModelHom ψ) :
          Subgroup G) : Set G)) := by
  obtain ⟨hQp, hQDsup, hQD, hDN⟩ := e7_twoRadicalDecomp
  have hQC : EPilot.highRadical .E7 (ZMod 2) ≤
      Subgroup.centralizer ({e7HighInv} : Set ↥(adjointGroup .E7 (ZMod 2))) := by
    rw [← hQDsup]
    exact le_sup_left
  have hDC : EPilot.perpLevi .E7 (ZMod 2) ≤
      Subgroup.centralizer ({e7HighInv} : Set ↥(adjointGroup .E7 (ZMod 2))) := by
    rw [← hQDsup]
    exact le_sup_right
  refine ⟨hQp.map _, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.map_le_range _ _).trans (le_of_eq e7ModelHom_range)
  · rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show e7ModelHom ψ q * e7ModelHom ψ e7HighInv = e7ModelHom ψ e7HighInv * e7ModelHom ψ q
    rw [← map_mul, ← map_mul]
    exact congrArg (e7ModelHom ψ) (Subgroup.mem_centralizer_singleton_iff.1 (hQC hq))
  · rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show e7ModelHom ψ d * e7ModelHom ψ e7HighInv = e7ModelHom ψ e7HighInv * e7ModelHom ψ d
    rw [← map_mul, ← map_mul]
    exact congrArg (e7ModelHom ψ) (Subgroup.mem_centralizer_singleton_iff.1 (hDC hd))
  · exact (Subgroup.map_mono hDN).trans (Subgroup.le_normalizer_map (e7ModelHom ψ))

private theorem e7_step613_centralizer_le {G : Type} [Group G] {Y : Subgroup G}
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) {r : ↥(adjointGroup .E7 (ZMod 2))}
    (g : ↥(adjointGroup .E7 (ZMod 2))) :
    (Subgroup.centralizer ({e7ModelHom ψ (g * r * g⁻¹)} : Set G) ⊓
        Subgroup.centralizer ({e7ModelHom ψ e7HighInv} : Set G) ⊓ Y ≤
      (Subgroup.centralizer ({(g * r * g⁻¹)} : Set ↥(adjointGroup .E7 (ZMod 2))) ⊓
        Subgroup.centralizer ({e7HighInv} : Set ↥(adjointGroup .E7 (ZMod 2)))).map
        (e7ModelHom ψ)) ∧
    ((Subgroup.centralizer ({(g * r * g⁻¹)} : Set ↥(adjointGroup .E7 (ZMod 2))) ⊓
        Subgroup.centralizer ({e7HighInv} : Set ↥(adjointGroup .E7 (ZMod 2)))).map
        (e7ModelHom ψ) ≤
      Subgroup.centralizer ({e7ModelHom ψ (g * r * g⁻¹)} : Set G) ⊓
        Subgroup.centralizer ({e7ModelHom ψ e7HighInv} : Set G) ⊓ Y) := by
  have hιinj := e7ModelHom_injective (ψ := ψ)
  have h1 := centralizer_singleton_inf_range_eq_map (e7ModelHom ψ) hιinj (g * r * g⁻¹)
  have h2 := centralizer_singleton_inf_range_eq_map (e7ModelHom ψ) hιinj e7HighInv
  rw [e7ModelHom_range] at h1 h2
  refine ⟨?_, ?_⟩
  · intro x hx
    have hx' := Subgroup.mem_inf.mp hx
    have hx1 : x ∈ Subgroup.centralizer ({e7ModelHom ψ (g * r * g⁻¹)} : Set G) ⊓ Y :=
      ⟨hx'.1.1, hx'.2⟩
    have hx2 : x ∈ Subgroup.centralizer ({e7ModelHom ψ e7HighInv} : Set G) ⊓ Y :=
      ⟨hx'.1.2, hx'.2⟩
    rw [Subgroup.map_inf _ _ _ hιinj]
    exact ⟨h1 ▸ hx1, h2 ▸ hx2⟩
  · rw [Subgroup.map_inf _ _ _ hιinj]
    intro x hx
    have hx' := Subgroup.mem_inf.mp hx
    have hx1 : x ∈ Subgroup.centralizer ({e7ModelHom ψ (g * r * g⁻¹)} : Set G) ⊓ Y :=
      h1.symm ▸ hx'.1
    have hx2 : x ∈ Subgroup.centralizer ({e7ModelHom ψ e7HighInv} : Set G) ⊓ Y :=
      h2.symm ▸ hx'.2
    exact ⟨⟨hx1.1, hx2.1⟩, hx1.2⟩

private theorem e7_step613_setup {G : Type} [Group G] {Y : Subgroup G}
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) {r : ↥(adjointGroup .E7 (ZMod 2))}
    (hrSL2 : (r : ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2))
    (hr3 : orderOf r = 3) (hL3 : E7ModelL3) (hConj : E7ModelConj) :
    ∃ (g : ↥(adjointGroup .E7 (ZMod 2))) (P : Subgroup G),
      (g * r * g⁻¹) ∈ e7JThetaD6 ∧ orderOf (g * r * g⁻¹) = 3 ∧
        P ≤ (EPilot.perpLevi .E7 (ZMod 2)).map (e7ModelHom ψ) ∧
        Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
        orderOf (e7ModelHom ψ (g * r * g⁻¹)) = 3 ∧
        e7ModelHom ψ (g * r * g⁻¹) ∈ P ∧
        ∃ y ∈ Y, e7ModelHom ψ (g * r * g⁻¹) = y * ((ψ r : ↥Y) : G) * y⁻¹ := by
  have hrJ : r ∈ e7JTheta := by
    rw [e7JTheta, Subgroup.mem_subgroupOf]
    exact hrSL2
  obtain ⟨g, hgJ⟩ := hConj
  have hr'D6 : (g * r * g⁻¹) ∈ e7JThetaD6 := by
    have hmem : (MulAut.conj g) r ∈ e7JThetaD6 := by
      rw [← hgJ]
      exact Subgroup.mem_map_of_mem _ hrJ
    simpa [MulAut.conj_apply] using hmem
  have hr'3 : orderOf (g * r * g⁻¹) = 3 := by
    simpa [MulAut.conj_apply, hr3] using (MulAut.conj g).orderOf_eq r
  obtain ⟨P₀, hJ'P₀, hP₀D, ⟨eP₀⟩⟩ := hL3.2
  have hιinj := e7ModelHom_injective (ψ := ψ)
  refine ⟨g, P₀.map (e7ModelHom ψ), hr'D6, hr'3, Subgroup.map_mono hP₀D, ?_, ?_, ?_, ?_⟩
  · exact ⟨(Subgroup.equivMapOfInjective P₀ (e7ModelHom ψ) hιinj).symm.trans eP₀⟩
  · exact (orderOf_injective (e7ModelHom ψ) hιinj (g * r * g⁻¹)).trans hr'3
  · exact Subgroup.mem_map_of_mem _ (hJ'P₀ hr'D6)
  · refine ⟨e7ModelHom ψ g, (le_of_eq e7ModelHom_range) ⟨g, rfl⟩, ?_⟩
    have h : e7ModelHom ψ (g * r * g⁻¹) =
        e7ModelHom ψ g * e7ModelHom ψ r * (e7ModelHom ψ g)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [h]
    rfl

private theorem e7_step613_Umax {G : Type} [Group G] {Y : Subgroup G}
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) {r : ↥(adjointGroup .E7 (ZMod 2))}
    (hO2model : E7ModelO2) (g : ↥(adjointGroup .E7 (ZMod 2)))
    (hr'D6 : (g * r * g⁻¹) ∈ e7JThetaD6) (hr'3 : orderOf (g * r * g⁻¹) = 3) :
    ∀ N : Subgroup G, IsPGroup 2 N →
      N ≤ Subgroup.centralizer ({e7ModelHom ψ (g * r * g⁻¹)} : Set G) ⊓
        Subgroup.centralizer ({e7ModelHom ψ e7HighInv} : Set G) ⊓ Y →
      Subgroup.centralizer ({e7ModelHom ψ (g * r * g⁻¹)} : Set G) ⊓
        Subgroup.centralizer ({e7ModelHom ψ e7HighInv} : Set G) ⊓ Y ≤
        Subgroup.normalizer (N : Set G) →
      N ≤ (EPilot.highRadical .E7 (ZMod 2)).map (e7ModelHom ψ) := by
  have hιinj := e7ModelHom_injective (ψ := ψ)
  have hUmaxM : ∀ N : Subgroup ↥(adjointGroup .E7 (ZMod 2)), IsPGroup 2 N →
      N ≤ Subgroup.centralizer ({(g * r * g⁻¹)} : Set ↥(adjointGroup .E7 (ZMod 2))) ⊓
        Subgroup.centralizer ({e7HighInv} : Set ↥(adjointGroup .E7 (ZMod 2))) →
      Subgroup.centralizer ({(g * r * g⁻¹)} : Set ↥(adjointGroup .E7 (ZMod 2))) ⊓
        Subgroup.centralizer ({e7HighInv} : Set ↥(adjointGroup .E7 (ZMod 2))) ≤
        Subgroup.normalizer (N : Set ↥(adjointGroup .E7 (ZMod 2))) →
      N ≤ EPilot.highRadical .E7 (ZMod 2) :=
    fun N hN hNC hNN => hO2model (g * r * g⁻¹) hr'D6 hr'3 N hN hNC hNN
  have hUmaxG := hUmax_map (e7ModelHom ψ) hιinj
    (C := Subgroup.centralizer ({(g * r * g⁻¹)} : Set ↥(adjointGroup .E7 (ZMod 2))) ⊓
      Subgroup.centralizer ({e7HighInv} : Set ↥(adjointGroup .E7 (ZMod 2))))
    (Q := EPilot.highRadical .E7 (ZMod 2)) hUmaxM
  obtain ⟨hCGle, hmap_le⟩ := e7_step613_centralizer_le ψ g
  intro N hN hNC hNN
  exact hUmaxG N hN (hNC.trans hCGle) (hmap_le.trans hNN)

private theorem e7_step613 {G : Type} [Group G] [Finite G] {Y R : Subgroup G}
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) {r : ↥(adjointGroup .E7 (ZMod 2))}
    (hrSL2 : (r : ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2))
    (hr3 : orderOf r = 3)
    (hZ : Subgroup.centralizer (Y : Set G) ⊓ Y = ⊥)
    (hRY : R ≤ Subgroup.centralizer (Y : Set G))
    (hCeq₀ : Subgroup.centralizer ({((ψ r : ↥Y) : G)} : Set G) =
      R ⊔ (Subgroup.centralizer ({((ψ r : ↥Y) : G)} : Set G) ⊓ Y))
    (hRodd : ¬ 2 ∣ Nat.card R)
    (hL3 : E7ModelL3) (hConj : E7ModelConj) (hIrr : E7ModelIrr) (hO2model : E7ModelO2)
    (hO2Eq : FS81RootO2)
    (hCharS : ∀ s : ↥(adjointGroup .E7 (ZMod 2)),
      (s : ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2) → orderOf s = 2 →
      CharTwo (Subgroup.centralizer ({((ψ s : ↥Y) : G)} : Set G))) :
    R = ⊥ ∧ pCoreOf 2 (Subgroup.centralizer ({((ψ e7HighInv : ↥Y) : G)} : Set G)) =
      ((EPilot.highRadical .E7 (ZMod 2)).map ψ.toMonoidHom).map Y.subtype := by
  obtain ⟨g, P, hr'D6, hr'3, hPleL, hP2, hb3, hbP, hconjWit⟩ :=
    e7_step613_setup ψ hrSL2 hr3 hL3 hConj
  have hιinj := e7ModelHom_injective (ψ := ψ)
  have hPleY : P ≤ Y := hPleL.trans ((Subgroup.map_le_range _ _).trans (le_of_eq e7ModelHom_range))
  have hUmax := e7_step613_Umax ψ hO2model g hr'D6 hr'3
  have hirr := hirr_map (e7ModelHom ψ) hιinj (t := e7HighInv)
    (D := EPilot.perpLevi .E7 (ZMod 2)) (Q := EPilot.highRadical .E7 (ZMod 2))
    (L := (EPilot.perpLevi .E7 (ZMod 2)).map (e7ModelHom ψ)) hIrr le_rfl
  obtain ⟨hU2, hUY, hUC, hLC, hLN⟩ := e7_step613_pieces ψ
  have ht2 : orderOf (e7ModelHom ψ e7HighInv) = 2 := by
    rw [orderOf_injective (e7ModelHom ψ) hιinj e7HighInv, e7HighInv_orderOf]
  have htU : e7ModelHom ψ e7HighInv ∈ (EPilot.highRadical .E7 (ZMod 2)).map
      (e7ModelHom ψ) := Subgroup.mem_map_of_mem _ e7HighInv_mem_highRadical
  have hCharT : CharTwo (Subgroup.centralizer ({e7ModelHom ψ e7HighInv} : Set G)) :=
    hCharS e7HighInv e7HighInv_mem_highRootSL2 e7HighInv_orderOf
  obtain ⟨hRbot, hcore⟩ :=
    hO2Eq G Y R ((EPilot.highRadical .E7 (ZMod 2)).map (e7ModelHom ψ))
      ((EPilot.perpLevi .E7 (ZMod 2)).map (e7ModelHom ψ)) P
      ((ψ r : ↥Y) : G) (e7ModelHom ψ (g * r * g⁻¹)) (e7ModelHom ψ e7HighInv)
      hZ hRY hCeq₀ hRodd ht2 htU hU2 hUY hUC hLC hLN hirr hconjWit hb3 hbP
      hPleL hP2 hUmax hCharT
  refine ⟨hRbot, ?_⟩
  rw [Subgroup.map_map]
  exact hcore

private theorem e7_cent_le {G : Type} [Group G] [Finite G] {Y R : Subgroup G}
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) {r : ↥(adjointGroup .E7 (ZMod 2))}
    (hrJ : r ∈ e7JTheta) (hr3 : orderOf r = 3)
    (hCeq₀ : Subgroup.centralizer ({((ψ r : ↥Y) : G)} : Set G) =
      R ⊔ (Subgroup.centralizer ({((ψ r : ↥Y) : G)} : Set G) ⊓ Y))
    (hRbot : R = ⊥)
    (hfus : ∀ g : G, g * ((ψ r : ↥Y) : G) * g⁻¹ ∈ Y →
      ∃ y ∈ Y, g * ((ψ r : ↥Y) : G) * g⁻¹ = y * ((ψ r : ↥Y) : G) * y⁻¹)
    (hcore : pCoreOf 2 (Subgroup.centralizer ({((ψ e7HighInv : ↥Y) : G)} : Set G)) =
      ((EPilot.highRadical .E7 (ZMod 2)).map ψ.toMonoidHom).map Y.subtype)
    (hCharS : ∀ s : ↥(adjointGroup .E7 (ZMod 2)),
      (s : ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2) → orderOf s = 2 →
      CharTwo (Subgroup.centralizer ({((ψ s : ↥Y) : G)} : Set G)))
    (hCent : E7RootCentStep) :
    Subgroup.centralizer ({((ψ e7HighInv : ↥Y) : G)} : Set G) ≤ Y := by
  have hb₀C : Subgroup.centralizer ({((ψ r : ↥Y) : G)} : Set G) ≤ Y := by
    have h : Subgroup.centralizer ({((ψ r : ↥Y) : G)} : Set G) =
        Subgroup.centralizer ({((ψ r : ↥Y) : G)} : Set G) ⊓ Y := by
      rw [hCeq₀, hRbot, bot_sup_eq, inf_assoc, inf_idem]
    exact inf_eq_left.mp h.symm
  have hconjmem : ∀ g : G, g * ((ψ r : ↥Y) : G) * g⁻¹ ∈ Y → g ∈ Y := by
    intro g hg
    obtain ⟨y, hy, hyb⟩ := hfus g hg
    have hmem : g⁻¹ * y ∈ Subgroup.centralizer ({((ψ r : ↥Y) : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst h
      have e : (g⁻¹ * y) * ((ψ r : ↥Y) : G) * (g⁻¹ * y)⁻¹ =
          ((ψ r : ↥Y) : G) := by
        calc (g⁻¹ * y) * ((ψ r : ↥Y) : G) * (g⁻¹ * y)⁻¹
            = g⁻¹ * (y * ((ψ r : ↥Y) : G) * y⁻¹) * g := by group
          _ = g⁻¹ * (g * ((ψ r : ↥Y) : G) * g⁻¹) * g := by rw [← hyb]
          _ = ((ψ r : ↥Y) : G) := by group
      calc ((ψ r : ↥Y) : G) * (g⁻¹ * y)
          = ((g⁻¹ * y) * ((ψ r : ↥Y) : G) * (g⁻¹ * y)⁻¹) * (g⁻¹ * y) := by rw [e]
        _ = (g⁻¹ * y) * ((ψ r : ↥Y) : G) := by group
    have hgy : g = y * (g⁻¹ * y)⁻¹ := by group
    rw [hgy]
    exact Y.mul_mem hy (Y.inv_mem (hb₀C hmem))
  exact hCent G Y ψ r hrJ hr3 hb₀C hconjmem
    (hCharS e7HighInv e7HighInv_mem_highRootSL2 e7HighInv_orderOf) hcore

private theorem e7_finish {G : Type} [Group G] [Finite G] {Y : Subgroup G}
    (hHolt : HoltSimpleControl) (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y)
    {r : ↥(adjointGroup .E7 (ZMod 2))} (hrJ : r ∈ e7JTheta)
    (hYs : IsSimpleGroup ↥Y) (hYna : ∃ a c : ↥Y, a * c ≠ c * a)
    (hYo : ∀ m : ℕ, 2 ≤ m → 2 * Nat.card ↥Y ≠ (2 * m).factorial)
    (hCentY : Subgroup.centralizer ({((ψ e7HighInv : ↥Y) : G)} : Set G) ≤ Y)
    (hb₀C : Subgroup.centralizer ({((ψ r : ↥Y) : G)} : Set G) ≤ Y)
    (hfus₀ : ∀ g : G, g * ((ψ r : ↥Y) : G) * g⁻¹ ∈ Y →
      ∃ y ∈ Y, g * ((ψ r : ↥Y) : G) * g⁻¹ = y * ((ψ r : ↥Y) : G) * y⁻¹) :
    Y = ⊤ := by
  have hιinj := e7ModelHom_injective (ψ := ψ)
  obtain ⟨S₀, htS₀, htcS₀⟩ := e7_exists_sylow_central
  have hS : IsSylow2In ((S₀ : Subgroup ↥(adjointGroup .E7 (ZMod 2))).map (e7ModelHom ψ)) Y := by
    have h := isSylow2In_map (e7ModelHom ψ) hιinj S₀
    rwa [e7ModelHom_range] at h
  have htS : e7ModelHom ψ e7HighInv ∈
      (S₀ : Subgroup ↥(adjointGroup .E7 (ZMod 2))).map (e7ModelHom ψ) :=
    Subgroup.mem_map_of_mem _ htS₀
  have ht2 : orderOf (e7ModelHom ψ e7HighInv) = 2 := by
    rw [orderOf_injective (e7ModelHom ψ) hιinj e7HighInv, e7HighInv_orderOf]
  have htc : ∀ s ∈ (S₀ : Subgroup ↥(adjointGroup .E7 (ZMod 2))).map (e7ModelHom ψ),
      s * e7ModelHom ψ e7HighInv = e7ModelHom ψ e7HighInv * s := by
    intro s hs
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hs
    rw [← map_mul, ← map_mul]
    exact congrArg (e7ModelHom ψ) (Subgroup.mem_centralizer_iff.1 htcS₀ u hu)
  exact eq_top_of_rootCent hHolt hYs hYna hYo hS htS ht2 htc hCentY hb₀C hfus₀
    (e7_involution_commute ψ hrJ)

private theorem e7_centralizer_decomp {G : Type} [Group G] {Y : Subgroup G}
    {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y} {r : ↥(adjointGroup .E7 (ZMod 2))}
    (hrJ : r ∈ e7JTheta) (hr3 : orderOf r = 3) :
    Subgroup.centralizer ({((ψ r : ↥Y) : G)} : Set G) ⊓ Y =
      Subgroup.zpowers ((ψ r : ↥Y) : G) ⊔
        (EPilot.perpLevi .E7 (ZMod 2)).map (e7ModelHom ψ) := by
  have hXJ : Subgroup.zpowers r ≤ (EPilot.highRootSL2 .E7 (ZMod 2)).subgroupOf
      (adjointGroup .E7 (ZMod 2)) := by
    rw [Subgroup.zpowers_le]
    exact hrJ
  have hXcard : Nat.card (Subgroup.zpowers r) = Nat.card (ZMod 2) + 1 := by
    rw [Nat.card_zpowers, hr3, Nat.card_zmod]
  have hns := E7Pilot.inf_centralizer_nonsplit_E7_of_finite (K := ZMod 2) (G := G) (L := Y)
    (e := ψ.symm) (X := Subgroup.zpowers r) hXJ hXcard (Subgroup.isCyclic_zpowers r)
  simp only [MulEquiv.symm_symm] at hns
  have hmap1 : Subgroup.map Y.subtype (Subgroup.map ψ.toMonoidHom (Subgroup.zpowers r)) =
      Subgroup.zpowers ((ψ r : ↥Y) : G) := by
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have hmap2 : Subgroup.map Y.subtype
      (Subgroup.map ψ.toMonoidHom (EPilot.perpLevi .E7 (ZMod 2))) =
      (EPilot.perpLevi .E7 (ZMod 2)).map (e7ModelHom ψ) := by
    rw [Subgroup.map_map]
    rfl
  have hcent : Subgroup.centralizer
      (Subgroup.zpowers ((ψ r : ↥Y) : G) : Set G) =
      Subgroup.centralizer ({((ψ r : ↥Y) : G)} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hmap1, hmap2, hcent, inf_comm] at hns
  exact hns

private theorem e7_R_not_even {G : Type} [Group G] [Finite G] {Y R : Subgroup G}
    {ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y} {r : ↥(adjointGroup .E7 (ZMod 2))}
    (hrJ : r ∈ e7JTheta) (hr3 : orderOf r = 3)
    (hZ : Subgroup.centralizer (Y : Set G) ⊓ Y = ⊥)
    (hRY : R ≤ Subgroup.centralizer (Y : Set G))
    (hCeq₀ : Subgroup.centralizer ({((ψ r : ↥Y) : G)} : Set G) =
      R ⊔ (Subgroup.centralizer ({((ψ r : ↥Y) : G)} : Set G) ⊓ Y))
    (h2sub : ∀ P : Subgroup G, IsPGroup 2 P →
      P ≤ Subgroup.centralizer ({((ψ r : ↥Y) : G)} : Set G) ⊓ Y →
      Subgroup.centralizer ({((ψ r : ↥Y) : G)} : Set G) ⊓ Y ≤
        Subgroup.normalizer (P : Set G) → P = ⊥)
    (hOdd : FS81RadicalOdd) (hL3 : E7ModelL3)
    (hCharR : ∀ t ∈ R, orderOf t = 2 → CharTwo (Subgroup.centralizer ({t} : Set G))) :
    ¬ 2 ∣ Nat.card R := by
  obtain ⟨P₀, hJP₀, ⟨eP₀⟩⟩ := hL3.1
  have hιinj := e7ModelHom_injective (ψ := ψ)
  refine hOdd G Y R (P₀.map (e7ModelHom ψ)) ((ψ r : ↥Y) : G) hZ hRY hCeq₀ h2sub ?_ ?_ ?_
    ⟨(Subgroup.equivMapOfInjective P₀ (e7ModelHom ψ) hιinj).symm.trans eP₀⟩ hCharR
  · exact (orderOf_injective (e7ModelHom ψ) hιinj r).trans hr3
  · exact Subgroup.mem_map_of_mem _ (hJP₀ hrJ)
  · exact (Subgroup.map_le_range _ _).trans (le_of_eq e7ModelHom_range)

theorem e7RootRecog_of_pieces
    (hHolt : HoltSimpleControl) (hOdd : FS81RadicalOdd) (hO2Eq : FS81RootO2)
    (hL3 : E7ModelL3) (hConj : E7ModelConj) (hO2 : E7ModelO2) (hIrr : E7ModelIrr)
    (hCent : E7RootCentStep) : E7RootRecog := by
  intro G _ _ Y R ψ r b hrSL2 hr3 hconj hRY hR3 hCeq hfus hCharR hCharS
  obtain ⟨y₀, hy₀, hb₀⟩ := hconj
  have hCeq₀ : Subgroup.centralizer ({((ψ r : ↥Y) : G)} : Set G) =
      R ⊔ (Subgroup.centralizer ({((ψ r : ↥Y) : G)} : Set G) ⊓ Y) :=
    centralizer_eq_sup_of_conj hy₀ hb₀ hRY hCeq
  have hfus₀ := fusion_of_conj hy₀ hb₀ hfus
  have hZ := e7_centralizer_inf_eq_bot ψ
  have hrJ : r ∈ e7JTheta := by
    rw [e7JTheta, Subgroup.mem_subgroupOf]
    exact hrSL2
  have hCY := e7_centralizer_decomp (G := G) (Y := Y) (ψ := ψ) hrJ hr3
  have h2sub := e7_twoSubgroup_bot ψ hrJ hr3 hCY
  have hRodd := e7_R_not_even hrJ hr3 hZ hRY hCeq₀ h2sub hOdd hL3 hCharR
  obtain ⟨hRbot, hcore⟩ :=
    e7_step613 (ψ := ψ) (hrSL2 := hrSL2) (hr3 := hr3) (hZ := hZ) (hRY := hRY)
      (hCeq₀ := hCeq₀) (hRodd := hRodd) (hL3 := hL3) (hConj := hConj)
      (hIrr := hIrr) (hO2model := hO2) (hO2Eq := hO2Eq) (hCharS := hCharS)
  have hCentY := e7_cent_le ψ hrJ hr3 hCeq₀ hRbot hfus₀ hcore hCharS hCent
  have hb₀C : Subgroup.centralizer ({((ψ r : ↥Y) : G)} : Set G) ≤ Y := by
    have h : Subgroup.centralizer ({((ψ r : ↥Y) : G)} : Set G) =
        Subgroup.centralizer ({((ψ r : ↥Y) : G)} : Set G) ⊓ Y := by
      rw [hCeq₀, hRbot, bot_sup_eq, inf_assoc, inf_idem]
    exact inf_eq_left.mp h.symm
  have hYs : IsSimpleGroup ↥Y := by
    haveI : IsSimpleGroup ↥(adjointGroup .E7 (ZMod 2)) :=
      E7Pilot.isSimpleGroup_adjointGroup_E7 (ZMod 2)
    exact ψ.symm.isSimpleGroup
  have hYna : ∃ a c : ↥Y, a * c ≠ c * a :=
    E7Pilot.exists_mul_ne_mul_of_mulEquiv_adjointGroup_E7 (K := ZMod 2) ψ.symm
  have hYo : ∀ m : ℕ, 2 ≤ m → 2 * Nat.card ↥Y ≠ (2 * m).factorial := by
    intro m hm
    rw [← Nat.card_congr ψ.toEquiv]
    exact e7_order_condition m hm
  exact e7_finish hHolt ψ hrJ hYs hYna hYo hCentY hb₀C hfus₀

end ModelFacts

end CFSG.StandardType.FrameRoute.FS81

