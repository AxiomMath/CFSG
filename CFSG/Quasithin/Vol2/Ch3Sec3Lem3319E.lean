module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3319D

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.L3319

open CFSG.Open (pCoreOf quasithinOmegaOneCenter)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.JonesParshall (wedgeRep wedgeMat)
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le)
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem mem_Ugrp_iff {u : SpecialLinearGroup (Fin 5) (ZMod 2)} :
    u ∈ JonesParshall.Curtis.Ugrp ↔ u ∈ unitriangular 5 (ZMod 2) := by
  rw [JonesParshall.Curtis.mem_Ugrp, mem_unitriangular]
  constructor
  · intro h
    exact ⟨fun i j hji => (h i j).1 hji, fun i => (h i i).2 rfl⟩
  · rintro ⟨h1, h2⟩ a b
    exact ⟨h1 a b, fun hab => hab ▸ h2 a⟩

theorem wedgeRep_e01 (g : SpecialLinearGroup (Fin 5) (ZMod 2)) (k : Fin 10) :
    wedgeRep g JonesParshall.Curtis.e01 k =
      (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) (JonesParshall.pr5 k).1 0 *
          (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) (JonesParshall.pr5 k).2 1 -
        (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) (JonesParshall.pr5 k).1 1 *
          (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) (JonesParshall.pr5 k).2 0 := by
  rw [JonesParshall.Curtis.wedgeRep_apply', JonesParshall.Curtis.e01, Matrix.mulVec_single_one]
  rfl

theorem wedge_e01_iff (g : SpecialLinearGroup (Fin 5) (ZMod 2)) :
    wedgeRep g JonesParshall.Curtis.e01 = JonesParshall.Curtis.e01 ↔
      g ∈ flagStabilizer 5 (ZMod 2) {2} := by
  set c : Fin 5 → ZMod 2 := fun a => (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) a 0 with hc
  set d : Fin 5 → ZMod 2 := fun a => (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) a 1 with hd
  constructor
  · intro h
    have hk : ∀ k : Fin 10, c (JonesParshall.pr5 k).1 * d (JonesParshall.pr5 k).2 -
        d (JonesParshall.pr5 k).1 * c (JonesParshall.pr5 k).2 =
          JonesParshall.Curtis.e01 k := fun k => by
      rw [← h, wedgeRep_e01]
    have h0 : c 0 * d 1 - d 0 * c 1 = 1 := hk 0
    have hz : ∀ a : Fin 5, 2 ≤ (a : ℕ) → c a = 0 ∧ d a = 0 := by
      intro a ha
      obtain ⟨h1, h2⟩ : c 0 * d a - d 0 * c a = 0 ∧ c 1 * d a - d 1 * c a = 0 := by
        fin_cases a
        · exact absurd ha (by decide)
        · exact absurd ha (by decide)
        · exact ⟨hk 1, hk 4⟩
        · exact ⟨hk 2, hk 5⟩
        · exact ⟨hk 3, hk 6⟩
      constructor
      · linear_combination (-c a) * h0 + c 1 * h1 - c 0 * h2
      · linear_combination (-d a) * h0 + d 1 * h1 - d 0 * h2
    refine mem_flagStabilizer_of_entries fun k l i hi hli hik => ?_
    rw [Set.mem_singleton_iff] at hi
    subst hi
    rcases l with ⟨l, hl5⟩
    have hl2 : l < 2 := hli
    interval_cases l
    · exact (hz k hik).1
    · exact (hz k hik).2
  · intro hg
    have hP : g ∈ stabilizer (flagSpace 5 (ZMod 2) 2) := mem_flagStabilizer.mp hg 2 rfl
    have hz : ∀ a : Fin 5, 2 ≤ (a : ℕ) → c a = 0 ∧ d a = 0 := fun a ha =>
      ⟨stabilizer_entries hP (l := 0) (by norm_num) ha,
        stabilizer_entries hP (l := 1) (by norm_num) ha⟩
    have h01 : c 0 * d 1 - d 0 * c 1 = 1 := by
      by_contra hne
      have key : ∀ a b c' d' : ZMod 2, a * d' - b * c' ≠ 1 →
          (a = 0 ∧ c' = 0) ∨ (b = 0 ∧ d' = 0) ∨ (a = b ∧ c' = d') := by decide
      have hdet : (g : Matrix (Fin 5) (Fin 5) (ZMod 2)).det = 1 := g.2
      rcases key (c 0) (d 0) (c 1) (d 1) hne with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [Matrix.det_eq_zero_of_column_eq_zero 0 fun i => by
          fin_cases i
          · exact h1
          · exact h2
          · exact (hz 2 (by decide)).1
          · exact (hz 3 (by decide)).1
          · exact (hz 4 (by decide)).1] at hdet
        exact zero_ne_one hdet
      · rw [Matrix.det_eq_zero_of_column_eq_zero 1 fun i => by
          fin_cases i
          · exact h1
          · exact h2
          · exact (hz 2 (by decide)).2
          · exact (hz 3 (by decide)).2
          · exact (hz 4 (by decide)).2] at hdet
        exact zero_ne_one hdet
      · rw [Matrix.det_zero_of_column_eq (i := 0) (j := 1) (by decide) fun i => by
          fin_cases i
          · exact h1
          · exact h2
          · exact (hz 2 (by decide)).1.trans (hz 2 (by decide)).2.symm
          · exact (hz 3 (by decide)).1.trans (hz 3 (by decide)).2.symm
          · exact (hz 4 (by decide)).1.trans (hz 4 (by decide)).2.symm] at hdet
        exact zero_ne_one hdet
    funext k
    rw [wedgeRep_e01]
    change c (JonesParshall.pr5 k).1 * d (JonesParshall.pr5 k).2 -
      d (JonesParshall.pr5 k).1 * c (JonesParshall.pr5 k).2 = JonesParshall.Curtis.e01 k
    by_cases hk : k = 0
    · subst hk
      exact h01
    · have h2 : 2 ≤ ((JonesParshall.pr5 k).2 : ℕ) := by
        revert hk
        revert k
        decide
      rw [(hz _ h2).1, (hz _ h2).2, mul_zero, mul_zero, sub_zero, JonesParshall.Curtis.e01,
        Pi.single_eq_of_ne hk]

namespace Data

variable {T M L D : Subgroup G} {α : ↥L →* SpecialLinearGroup (Fin 5) (ZMod 2)}
  {Φ : Multiplicative (Fin 10 → ZMod 2) →* ↥(vPlus L T)}

theorem exists_eq (hD : Data G T M L D α Φ) {w : G} (hw : w ∈ ⁅vPlus L T, L⁆) :
    ∃ x, (Φ x : G) = w := by
  have hwV : w ∈ vPlus L T := by
    have hred := Hyp331.vPlus_reduced hD.hyp.toSetup331
    have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hred.2.2.2.1
    exact Ch1Sec3.commutator_le_left_of_le_normalizer hLV hw
  have : (⟨w, hwV⟩ : ↥(vPlus L T)) ∈ Φ.range := by
    rw [hD.range]
    exact Subgroup.mem_subgroupOf.mpr hw
  obtain ⟨x, hx⟩ := this
  exact ⟨x, congrArg Subtype.val hx⟩

theorem comm_iff (hD : Data G T M L D α Φ) (l : ↥L) (x : Multiplicative (Fin 10 → ZMod 2)) :
    (l : G) * (Φ x : G) * (l : G)⁻¹ = (Φ x : G) ↔
      wedgeRep (α l) (Multiplicative.toAdd x) = Multiplicative.toAdd x := by
  rw [hD.equiv]
  constructor
  · intro hc
    have h1 := hD.inj (Subtype.ext hc)
    exact congrArg Multiplicative.toAdd h1
  · intro hc
    rw [hc]
    rfl

theorem eq_of_fix (hD : Data G T M L D α Φ)
    {x : Multiplicative (Fin 10 → ZMod 2)}
    (hx : ∀ t ∈ T ⊓ L, t * (Φ x : G) * t⁻¹ = (Φ x : G)) :
    Multiplicative.toAdd x = 0 ∨ Multiplicative.toAdd x = JonesParshall.Curtis.e01 := by
  apply JonesParshall.Curtis.wedge_fix
  intro u hu
  have hu' : u ∈ unitriangular 5 (ZMod 2) := mem_Ugrp_iff.mp hu
  rw [← hD.mapU] at hu'
  obtain ⟨t, ht, rfl⟩ := hu'
  exact (hD.comm_iff t x).mp (hx t (Subgroup.mem_subgroupOf.mp ht))

theorem wedge_e01_of_mem (hD : Data G T M L D α Φ) {t : ↥L} (ht : (t : G) ∈ T) :
    wedgeRep (α t) JonesParshall.Curtis.e01 = JonesParshall.Curtis.e01 := by
  have hu : α t ∈ unitriangular 5 (ZMod 2) := by
    rw [← hD.mapU]
    exact ⟨t, Subgroup.mem_subgroupOf.mpr ⟨ht, t.2⟩, rfl⟩
  exact JonesParshall.Curtis.e01_mem_fixU _ (mem_Ugrp_iff.mpr hu)

noncomputable abbrev w₀ (_hD : Data G T M L D α Φ) : G :=
  (Φ (Multiplicative.ofAdd JonesParshall.Curtis.e01) : G)

theorem inf_centralizer_eq (hD : Data G T M L D α Φ) :
    L ⊓ Subgroup.centralizer
        ((vPlus L T ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) : Subgroup G) :
          Set G) =
      liftPre α (flagStabilizer 5 (ZMod 2) {2}) := by
  set Z := quasithinOmegaOneCenter T with hZ
  set Z₀ := vPlus L T ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) with hZ₀
  have hcomm : ∀ (g y : G), g * y * g⁻¹ = y ↔ g * y = y * g := fun g y => by
    constructor
    · intro h
      calc g * y = g * y * g⁻¹ * g := by group
        _ = y * g := by rw [h]
    · intro h
      rw [h, mul_inv_cancel_right]
  have hw₀ : hD.w₀ ∈ Z₀ := by
    refine ⟨(Φ _).2, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
    have h1 := (hD.comm_iff ⟨t, ht.2⟩ (Multiplicative.ofAdd JonesParshall.Curtis.e01)).mpr
      (hD.wedge_e01_of_mem ht.1)
    exact (hcomm _ _).mp h1
  have hl : ∀ l : ↥L, (l : G) * hD.w₀ = hD.w₀ * l ↔ α l ∈ flagStabilizer 5 (ZMod 2) {2} := by
    intro l
    rw [← hcomm, hD.comm_iff, toAdd_ofAdd, wedge_e01_iff]
  obtain ⟨-, hdec⟩ := hD.hyp.vPlus_decomp
  rw [Hyp331.mPlus_eq_of_le hD.TL] at hdec
  have hZT : Z ≤ T := (B2F.omegaOneCenter_le_inf_centralizer T).trans inf_le_left
  have hZC : Z ≤ Subgroup.centralizer (T : Set G) :=
    (B2F.omegaOneCenter_le_inf_centralizer T).trans inf_le_right
  have hAZ₀ : Z ⊓ Subgroup.centralizer (L : Set G) ≤ Z₀ :=
    le_inf (inf_le_left.trans (le_conjClosure _ _))
      (inf_le_left.trans (hZC.trans (Subgroup.centralizer_le inf_le_left)))
  have hN : Z ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.normalizer ((⁅vPlus L T, L⁆ : Subgroup G) : Set G) := fun z hz =>
    Ch1Sec3.commutator_le_normalizer (Hyp331.le_normalizer_vPlus L T (hZT hz.1))
      (Subgroup.centralizer_le_normalizer _ hz.2)
  have hZ₀le : Z₀ ≤ (Z ⊓ Subgroup.centralizer (L : Set G)) ⊔ (Z₀ ⊓ ⁅vPlus L T, L⁆) := by
    have h1 : Z₀ ≤ ⁅vPlus L T, L⁆ ⊔ (Z ⊓ Subgroup.centralizer (L : Set G)) := by
      rw [← hdec]
      exact inf_le_left
    rw [sup_comm] at h1
    exact (le_inf le_rfl h1).trans (ChiefCount.inf_sup_le hAZ₀ hN)
  have hW : ∀ w ∈ Z₀ ⊓ ⁅vPlus L T, L⁆, w = 1 ∨ w = hD.w₀ := by
    rintro w ⟨hwZ₀, hwW⟩
    obtain ⟨x, rfl⟩ := hD.exists_eq hwW
    have hfix : ∀ t ∈ T ⊓ L, t * (Φ x : G) * t⁻¹ = (Φ x : G) := fun t ht =>
      (hcomm _ _).mpr (Subgroup.mem_centralizer_iff.mp hwZ₀.2 t ht)
    rcases hD.eq_of_fix hfix with h0 | h1
    · left
      have : x = 1 := Multiplicative.toAdd.injective (by rw [h0]; rfl)
      rw [this, map_one]
      rfl
    · right
      have : x = Multiplicative.ofAdd JonesParshall.Curtis.e01 :=
        Multiplicative.toAdd.injective (by rw [h1]; rfl)
      rw [this]
  apply le_antisymm
  · rintro x ⟨hxL, hxC⟩
    refine ⟨⟨x, hxL⟩, ?_, rfl⟩
    exact (hl ⟨x, hxL⟩).mp (Subgroup.mem_centralizer_iff.mp hxC _ hw₀).symm
  · rintro _ ⟨l, hlP, rfl⟩
    refine ⟨l.2, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    have hle : (Z ⊓ Subgroup.centralizer (L : Set G)) ⊔ (Z₀ ⊓ ⁅vPlus L T, L⁆) ≤
        Subgroup.centralizer ({(l : G)} : Set G) := by
      refine sup_le (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hy.2 l l.2).symm) (fun y hy => ?_)
      rcases hW y hy with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_centralizer_singleton_iff.mpr ((hl l).mpr hlP).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hZ₀le hz))

end Data

end CFSG.Quasithin.H13.L3319
