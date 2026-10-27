module

public import CFSG.Quasithin.Vol2.Ch10SecD31D
public import CFSG.Quasithin.Vol2.Ch10SecC8V1
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch10SecD211A

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem fixV_autOn_V1 (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) [IsMulCommutative ↥(fsuUL T L I)] :
    fixV (autOn L (fsuUL T L I)) = cV1 T L I := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp h.not_normal
  have hLt := conjugate_le_centralizer_V1 h ht htn
  ext v
  rw [Subgroup.mem_subgroupOf]
  have h1 : v ∈ fixV (autOn L (fsuUL T L I)) ↔ (v : G) ∈ Subgroup.centralizer (L : Set G) :=
    (mem_centralizer_iff_autOn L_le_normalizer_V1 v).symm
  rw [h1, SecA.fsuL0_eq_sup h37 h38 h ht htn]
  constructor
  · intro hv
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hle : L ⊔ CFSG.conjugate L t ≤ Subgroup.centralizer ({(v : G)} : Set G) := by
      refine sup_le (fun l hl => ?_) (fun l hl => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hv l hl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp (hLt hl)) v v.2).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  · intro hv
    exact Subgroup.centralizer_le (le_sup_left : L ≤ L ⊔ CFSG.conjugate L t) hv

theorem card_V1_eq (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hI16 : ASInputs.AS_I_1_6) (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I)
    (hV1 : fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) :
    Nat.card ↥(fsuUL T L I) = 16 ∧ Nat.card ↥(cV1 T L I) = 2 := by
  obtain ⟨-, hcomm, hnat⟩ := h3
  obtain ⟨D⟩ := hnat.toL3Coord
  have hU := D.card_U
  rw [Subgroup.card_top] at hU
  have hfix := fixV_autOn_V1 h37 h38 h
  have hle : Nat.card ↥(cV1 T L I) ≤ 2 := by
    have hc := (hI16 (↥(fsuUL T L I)) (SecC.sq_eq_one_fsuUL h) (autOn L (fsuUL T L I)) 1).1
      (SecC.commV_autOn_fsuUL h) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨rfl, by rw [hfix]; exact hnat⟩))))))
    rw [hfix, pow_one] at hc
    exact hc
  have hne : cV1 T L I ≠ ⊥ := by
    intro hbot
    apply hV1
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.1⟩ : ↥(fsuUL T L I)) ∈ fixV (autOn L (fsuUL T L I)) :=
      (mem_centralizer_iff_autOn L_le_normalizer_V1 _).mp hx.2
    rw [hfix, hbot, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hx')
  have hge : 2 ≤ Nat.card ↥(cV1 T L I) := by
    obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    have : 1 < Nat.card ↥(cV1 T L I) :=
      Finite.one_lt_card_iff_nontrivial.mpr ⟨⟨⟨x, hx⟩, 1, hx1⟩⟩
    omega
  constructor <;> omega

omit [Finite G] in
theorem mem_fixV_zpowers_iff {W : Type*} [CommGroup W] {x : MulAut W} {w : W} :
    w ∈ fixV (Subgroup.zpowers x) ↔ x w = w :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem mem_centralizer_V1 (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hI16 : ASInputs.AS_I_1_6) (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I)
    (hV1 : fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) {g : G}
    (hgL : g ∈ Subgroup.normalizer (L : Set G))
    (hgV : g ∈ Subgroup.normalizer (fsuUL T L I : Set G))
    (hidx : (Subgroup.centralizer ({g} : Set G)).relIndex (fsuUL T L I) ≤ 2) :
    g ∈ Subgroup.centralizer (fsuUL T L I : Set G) := by
  have hcard := (card_V1_eq h37 h38 hI16 h h3 hV1).1
  obtain ⟨-, hcomm, hnat⟩ := h3
  have hfix := fixV_autOn_V1 h37 h38 h
  rw [← hfix] at hnat
  have hnorm : ∀ (g' : G) (hgL' : g' ∈ Subgroup.normalizer (L : Set G))
      (hgV' : g' ∈ Subgroup.normalizer (fsuUL T L I : Set G)),
      ∀ σ ∈ autOn L (fsuUL T L I), conjAct (fsuUL T L I) ⟨g', hgV'⟩ * σ *
        (conjAct (fsuUL T L I) ⟨g', hgV'⟩)⁻¹ ∈ autOn L (fsuUL T L I) := by
    rintro g' hgL' hgV' _ ⟨⟨l, hlN⟩, hl, rfl⟩
    refine ⟨⟨g', hgV'⟩ * ⟨l, hlN⟩ * (⟨g', hgV'⟩)⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hgL' l).mp (Subgroup.mem_subgroupOf.mp hl)
    · rw [map_mul, map_mul, map_inv]
  set x : MulAut ↥(fsuUL T L I) := conjAct (fsuUL T L I) ⟨g, hgV⟩ with hxdef
  have hgV' : g⁻¹ ∈ Subgroup.normalizer (fsuUL T L I : Set G) :=
    (Subgroup.normalizer _).inv_mem hgV
  have hxinv : conjAct (fsuUL T L I) ⟨g⁻¹, hgV'⟩ = x⁻¹ := by
    rw [hxdef, ← map_inv]
    rfl
  have hx : ∀ σ, σ ∈ autOn L (fsuUL T L I) ↔ x * σ * x⁻¹ ∈ autOn L (fsuUL T L I) := by
    intro σ
    refine ⟨hnorm g hgL hgV σ, fun hσ => ?_⟩
    have h1 := hnorm g⁻¹ ((Subgroup.normalizer _).inv_mem hgL) hgV' _ hσ
    rw [hxinv, inv_inv] at h1
    have e1 : x⁻¹ * (x * σ * x⁻¹) * x = σ := by group
    rwa [e1] at h1
  have hfixx : fixV (Subgroup.zpowers x) =
      (Subgroup.centralizer ({g} : Set G)).subgroupOf (fsuUL T L I) := by
    ext v
    rw [mem_fixV_zpowers_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hv
      have h1 : g * (v : G) * g⁻¹ = v := congrArg Subtype.val hv
      calc (v : G) * g = g * v * g⁻¹ * g := by rw [h1]
        _ = g * v := by group
    · intro hv
      apply Subtype.ext
      show g * (v : G) * g⁻¹ = v
      rw [← hv]
      group
  have hidx' : (fixV (Subgroup.zpowers x)).index ≤ 2 := by
    rw [hfixx]
    exact hidx
  have hx1 := eq_one_of_normalizes (SecC.sq_eq_one_fsuUL h) hnat hcard (SecC.commV_autOn_fsuUL h)
    hx hidx'
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 := congrArg (fun φ : MulAut ↥(fsuUL T L I) => ((φ ⟨v, hv⟩ : ↥(fsuUL T L I)) : G)) hx1
  have h2 : g * v * g⁻¹ = v := h1
  calc v * g = g * v * g⁻¹ * g := by rw [h2]
    _ = g * v := by group

end CFSG.Quasithin.Vol2.Ch10.SecD
