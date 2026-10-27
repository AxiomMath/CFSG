module

import CFSG.Quasithin.Background.Harris.R1.QbetaPerf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c8_relIndex_inf_centralizer_le {Y U : Subgroup G} {v : G}
    (h : ∀ y ∈ Y, y * v * y⁻¹ * v⁻¹ ∈ U) :
    (Y ⊓ centralizer ({v} : Set G)).relIndex Y ≤ Nat.card U := by
  classical
  let C : Subgroup G := Y ⊓ centralizer ({v} : Set G)
  let φ : ↥Y → ↥U := fun y => ⟨y.1 * v * y.1⁻¹ * v⁻¹, h y.1 y.2⟩
  have hφ : ∀ a b : ↥Y, QuotientGroup.leftRel (C.subgroupOf Y) a b → φ a = φ b := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hab
    have hc : a.1⁻¹ * b.1 * v = v * (a.1⁻¹ * b.1) := by
      have hm := (Subgroup.mem_inf.1 hab).2
      simpa using Subgroup.mem_centralizer_singleton_iff.mp hm
    apply Subtype.ext
    have hv : a.1 * v * a.1⁻¹ = b.1 * v * b.1⁻¹ := by
      have key : b.1 * v * b.1⁻¹ = a.1 * v * a.1⁻¹ := by
        calc b.1 * v * b.1⁻¹
            = a.1 * (a.1⁻¹ * b.1 * v) * b.1⁻¹ := by group
          _ = a.1 * (v * (a.1⁻¹ * b.1)) * b.1⁻¹ := by rw [hc]
          _ = a.1 * v * a.1⁻¹ := by group
      exact key.symm
    show a.1 * v * a.1⁻¹ * v⁻¹ = b.1 * v * b.1⁻¹ * v⁻¹
    rw [hv]
  let ψ : ↥Y ⧸ (C.subgroupOf Y) → ↥U := Quotient.lift φ hφ
  have hψ : Function.Injective ψ := by
    intro q q' hq
    obtain ⟨a, rfl⟩ := Quotient.mk_surjective q
    obtain ⟨b, rfl⟩ := Quotient.mk_surjective q'
    change φ a = φ b at hq
    apply Quotient.sound
    show QuotientGroup.leftRel (C.subgroupOf Y) a b
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
    have hv : a.1 * v * a.1⁻¹ = b.1 * v * b.1⁻¹ :=
      mul_right_cancel (Subtype.ext_iff.mp hq)
    have hc : b.1⁻¹ * a.1 ∈ C := by
      rw [Subgroup.mem_inf]
      refine ⟨Y.mul_mem (Y.inv_mem b.2) a.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcv : (b.1⁻¹ * a.1) * v * (b.1⁻¹ * a.1)⁻¹ = v := by
        have h := congrArg (fun x => b.1⁻¹ * x * b.1) hv
        have h1 : b.1⁻¹ * (a.1 * v * a.1⁻¹) * b.1 =
            (b.1⁻¹ * a.1) * v * (b.1⁻¹ * a.1)⁻¹ := by group
        have h2 : b.1⁻¹ * (b.1 * v * b.1⁻¹) * b.1 = v := by group
        rwa [h1, h2] at h
      calc (b.1⁻¹ * a.1) * v
          = ((b.1⁻¹ * a.1) * v * (b.1⁻¹ * a.1)⁻¹) * (b.1⁻¹ * a.1) := by group
        _ = v * (b.1⁻¹ * a.1) := by rw [hcv]
    have h : a.1⁻¹ * b.1 = (b.1⁻¹ * a.1)⁻¹ := by group
    change a.1⁻¹ * b.1 ∈ C
    rw [h]
    exact C.inv_mem hc
  show (C.subgroupOf Y).index ≤ Nat.card U
  rw [Subgroup.index_eq_card]
  exact Nat.card_le_card_of_injective ψ hψ

private theorem c8_relIndex_map_dvd {G₁ G₂ : Type*} [Group G₁] [Group G₂] (φ : G₁ →* G₂)
    (H K : Subgroup G₁) : (H.map φ).relIndex (K.map φ) ∣ H.relIndex K := by
  have hK : K.map φ = (φ.comp K.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hK, ← Subgroup.index_comap]
  exact Subgroup.index_dvd_of_le fun k hk =>
    Subgroup.mem_comap.mpr (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩)

theorem c8_relIndex_barSub_le {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} (v₀ : IntMod V hV)
    {Y : Subgroup G} (hY : Y ≤ stabTil V₀ V)
    (hfix : ∀ y ∈ Y, y * v₀.val * y⁻¹ * (v₀.val)⁻¹ ∈ V₀) :
    (barSub V₀ V hV (Y ⊓ centralizer ({v₀.val} : Set G))).relIndex (barSub V₀ V hV Y) ≤
      Nat.card V₀ := by
  let f : ↥(stabTil V₀ V) →* MulAut (Vtil V₀ V hV) := actTil V₀ V hV
  let Y' : Subgroup ↥(stabTil V₀ V) := Y.subgroupOf (stabTil V₀ V)
  let C' : Subgroup ↥(stabTil V₀ V) :=
    (Y ⊓ centralizer ({v₀.val} : Set G)).subgroupOf (stabTil V₀ V)
  have hidx : C'.relIndex Y' = (Y ⊓ centralizer ({v₀.val} : Set G)).relIndex Y :=
    Subgroup.relIndex_subgroupOf hY
  have hA : (Y ⊓ centralizer ({v₀.val} : Set G)).relIndex Y ≤ Nat.card V₀ :=
    c8_relIndex_inf_centralizer_le hfix
  have hdvd : (C'.map f).relIndex (Y'.map f) ∣ C'.relIndex Y' := c8_relIndex_map_dvd f C' Y'
  have hpos : C'.relIndex Y' ≠ 0 := by
    rw [hidx]
    haveI : Finite (↥Y ⧸ (Y ⊓ centralizer ({v₀.val} : Set G)).subgroupOf Y) :=
      Quotient.finite _
    exact Subgroup.index_ne_zero_of_finite
  change (C'.map f).relIndex (Y'.map f) ≤ Nat.card V₀
  calc (C'.map f).relIndex (Y'.map f)
      ≤ C'.relIndex Y' := Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) hdvd
    _ = (Y ⊓ centralizer ({v₀.val} : Set G)).relIndex Y := hidx
    _ ≤ Nat.card V₀ := hA

theorem c8_barSub_inf_centralizer_eq (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hM : Mbar D.M V₀ V hV = lBar V₀ V hV L) (v₀ : IntMod V hV)
    (hperf : ⁅ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀),
        ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀)⁆ =
      ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀)) :
    barSub V₀ V hV (L ⊓ centralizer ({v₀.val} : Set G)) =
      ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀) := by
  classical
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  set P : Subgroup (MulAut (Vtil V₀ V hV)) :=
    ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀) with hPdef
  let w : Vtil V₀ V hV := mkTil V₀ V hV v₀
  let S : Subgroup (MulAut (Vtil V₀ V hV)) := MulAction.stabilizer (MulAut (Vtil V₀ V hV)) w
  let Y : Subgroup G := L ⊓ (S.comap (actTil V₀ V hV)).map (stabTil V₀ V).subtype
  have hPmem : ∀ φ : MulAut (Vtil V₀ V hV),
      φ ∈ P ↔ φ ∈ Mbar D.M V₀ V hV ∧ φ w = w := by
    intro φ
    rw [hPdef]
    change φ ∈ Mbar D.M V₀ V hV ⊓ MulAction.stabilizer (MulAut (Vtil V₀ V hV)) w ↔
      φ ∈ Mbar D.M V₀ V hV ∧ φ w = w
    rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAut.smul_def]
  have hYstab : Y ≤ stabTil V₀ V := fun _ hy => Subgroup.map_subtype_le _ hy.2
  have hYfix : ∀ g : ↥(stabTil V₀ V), (g : G) ∈ Y → actTil V₀ V hV g w = w := by
    intro g hg
    have hg2 : (g : G) ∈ (S.comap (actTil V₀ V hV)).map (stabTil V₀ V).subtype := hg.2
    rw [Subgroup.mem_map] at hg2
    obtain ⟨g', hg'S, hg'g⟩ := hg2
    have hgg : g' = g := Subtype.ext hg'g
    have hmem : actTil V₀ V hV g ∈ S := by
      rw [← hgg]
      exact hg'S
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hmem
    exact hmem
  have hfixY : ∀ y ∈ Y, y * v₀.val * y⁻¹ * (v₀.val)⁻¹ ∈ V₀ := by
    intro y hy
    have h := hYfix ⟨y, hYstab hy⟩ hy
    have h1 : mkTil V₀ V hV (actStab V₀ V hV ⟨y, hYstab hy⟩ v₀) = mkTil V₀ V hV v₀ := by
      rw [← actTil_mk]
      exact h
    rw [mkTil_eq_iff, actStab_apply_val] at h1
    exact h1
  have hsub : barSub V₀ V hV (L ⊓ centralizer ({v₀.val} : Set G)) ≤ P := by
    intro φ hφ
    rw [hPmem]
    obtain ⟨g, hg, rfl⟩ :=
      (mem_barSub V₀ V hV (L ⊓ centralizer ({v₀.val} : Set G)) φ).1 hφ
    refine ⟨actTil_mem_barSub V₀ V hV (hS.setting.hyp151.le hg.1) g.2, ?_⟩
    have hcomm : (g : G) * v₀.val * (g : G)⁻¹ = v₀.val := by
      have hc := Subgroup.mem_centralizer_singleton_iff.mp hg.2
      calc (g : G) * v₀.val * (g : G)⁻¹ = v₀.val * (g : G) * (g : G)⁻¹ := by rw [hc]
        _ = v₀.val := by group
    have hact : actStab V₀ V hV g v₀ = v₀ := by
      apply IntMod.val_injective
      rw [actStab_apply_val, hcomm]
    rw [show w = mkTil V₀ V hV v₀ from rfl, actTil_mk, hact]
  have hbarYle : barSub V₀ V hV Y ≤ P := by
    intro φ hφ
    rw [hPmem]
    obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV Y φ).1 hφ
    exact ⟨actTil_mem_barSub V₀ V hV (hS.setting.hyp151.le hg.1) g.2, hYfix g hg⟩
  have hbarYge : P ≤ barSub V₀ V hV Y := by
    intro φ hφ
    rw [hPmem] at hφ
    obtain ⟨hφM, hφw⟩ := hφ
    have hphiL : φ ∈ barSub V₀ V hV L := by
      have : φ ∈ lBar V₀ V hV L := by rwa [← hM]
      exact this
    obtain ⟨g, hgL, hgφ⟩ := (mem_barSub V₀ V hV L φ).1 hphiL
    refine (mem_barSub V₀ V hV Y φ).2 ⟨g, ⟨hgL, ?_⟩, hgφ⟩
    refine Subgroup.mem_map.mpr ⟨g, ?_, rfl⟩
    refine Subgroup.mem_comap.mpr ?_
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, hgφ]
    exact hφw
  have hbarY : barSub V₀ V hV Y = P := le_antisymm hbarYle hbarYge
  have hB := c8_relIndex_barSub_le (hV := hV) v₀ (Y := Y) hYstab hfixY
  have hBP : (barSub V₀ V hV (Y ⊓ centralizer ({v₀.val} : Set G))).relIndex P ≤
      Nat.card V₀ := by
    rw [hbarY] at hB
    exact hB
  have hHK : barSub V₀ V hV (Y ⊓ centralizer ({v₀.val} : Set G)) ≤
      barSub V₀ V hV (L ⊓ centralizer ({v₀.val} : Set G)) :=
    barSub_mono (V₀ := V₀) (V := V) (hV := hV)
      (inf_le_inf (show Y ≤ L from inf_le_left) le_rfl)
  have hne : (barSub V₀ V hV (Y ⊓ centralizer ({v₀.val} : Set G))).relIndex P ≠ 0 := by
    haveI : Finite (↥P ⧸
        (barSub V₀ V hV (Y ⊓ centralizer ({v₀.val} : Set G))).subgroupOf P) :=
      Quotient.finite _
    exact Subgroup.index_ne_zero_of_finite
  have hrelLes : (barSub V₀ V hV (L ⊓ centralizer ({v₀.val} : Set G))).relIndex P ≤
      (barSub V₀ V hV (Y ⊓ centralizer ({v₀.val} : Set G))).relIndex P :=
    Subgroup.relIndex_le_of_le_left hHK hne
  have hV02 : IsPGroup 2 V₀ :=
    fun g => ⟨1, Subtype.ext (by
      simpa using hS.setting.hyp16.hyp125.pairFacts.elemAbelian₀.2 (g : G) g.2)⟩
  have hcard : Nat.card V₀ = 2 ^ mSub V₀ := card_eq_two_pow_mSub hV02
  have hle4 : Nat.card V₀ ≤ 4 := by
    calc Nat.card V₀ = 2 ^ mSub V₀ := hcard
      _ ≤ 2 ^ 2 := (Nat.pow_le_pow_iff_right (show 2 ≤ 2 by norm_num)).2
        hS.setting.hyp16.small
      _ = 4 := by norm_num
  have hrel_le4 : (barSub V₀ V hV (L ⊓ centralizer ({v₀.val} : Set G))).relIndex P ≤ 4 :=
    le_trans hrelLes (le_trans hBP hle4)
  have hperfP : ⁅P, P⁆ = P := by
    rw [hPdef]
    exact hperf
  haveI : Finite ↥P := Subtype.finite
  exact le_antisymm hsub
    (CFSG.Quasithin.Background.Harris.R1.perfect_le_of_index_le_four
      (K := P) (Stab := barSub V₀ V hV (L ⊓ centralizer ({v₀.val} : Set G)))
      hperfP hsub hrel_le4)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
