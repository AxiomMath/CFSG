module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G44Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G43Kit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G43Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BlockNatural
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoTrans

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c1G43_relIndex_cent {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D ⊥ V L hV) {B : Subgroup G} (hBM : B ≤ D.M)
    (hB16 : Nat.card (barSub ⊥ V hV B) = 16) :
    (B ⊓ centralizer (V : Set G)).relIndex B = 16 := by
  have hMstab : D.M ≤ stabTil (⊥ : Subgroup G) V :=
    le_stabTil hS.setting.hyp151.hyp125.pairFacts.le_normalizer
      hS.setting.hyp151.hyp125.pairFacts.le_normalizer₀
  have hBst : B ≤ stabTil (⊥ : Subgroup G) V := hBM.trans hMstab
  have hcard := s16c1G44_relIndex_inf_preBarSub_eq_card_barSub
    (V₀ := ⊥) (V := V) (hV := hV) hBM hBst
  have hset : B ⊓ preBarSub D.M (⊥ : Subgroup G) V hV ⊥ = B ⊓ centralizer (V : Set G) := by
    ext b
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨hbB, hpre⟩
      obtain ⟨-, h, hact⟩ := (mem_preBarSub D.M ⊥ V hV ⊥).1 hpre
      exact ⟨hbB, (s16c7_actTil_eq_one_iff_mem_centralizer V hV ⟨b, h⟩).1
        (Subgroup.mem_bot.1 hact)⟩
    · rintro ⟨hbB, hcent⟩
      refine ⟨hbB, (mem_preBarSub D.M ⊥ V hV ⊥).2 ⟨hBM hbB, hBst hbB, ?_⟩⟩
      exact Subgroup.mem_bot.2
        ((s16c7_actTil_eq_one_iff_mem_centralizer V hV ⟨b, hBst hbB⟩).2 hcent)
  rw [← hset, hcard, hB16]

private theorem s16c1G43_actTil_mk_val {V : Subgroup G} {hV : IsElemAbelian 2 V}
    {b : G} (hb : b ∈ stabTil (⊥ : Subgroup G) V) {v : G} (hv : v ∈ V) :
    actTil (⊥ : Subgroup G) V hV ⟨b, hb⟩ (mkTil ⊥ V hV (IntMod.mk hV ⟨v, hv⟩)) =
      mkTil ⊥ V hV (IntMod.mk hV ⟨b * v * b⁻¹,
        (Subgroup.mem_normalizer_iff.1 (stabTil_le_normalizer ⊥ V hb) v).1 hv⟩) := by
  rw [actTil_mk]
  apply congrArg (mkTil (⊥ : Subgroup G) V hV)
  apply IntMod.val_injective
  rw [actStab_apply_val]
  rfl

private theorem s16c1G43_actTil_val_eq_iff {V : Subgroup G} {hV : IsElemAbelian 2 V}
    {b : G} (hb : b ∈ stabTil (⊥ : Subgroup G) V) {v : G} (hv : v ∈ V)
    (w : IntMod V hV) :
    actTil (⊥ : Subgroup G) V hV ⟨b, hb⟩ (mkTil ⊥ V hV (IntMod.mk hV ⟨v, hv⟩)) =
      mkTil ⊥ V hV w ↔ b * v * b⁻¹ = w.val := by
  rw [s16c1G43_actTil_mk_val hb hv, mkTil_eq_iff, Subgroup.mem_bot, mul_inv_eq_one]
  exact Iff.rfl

theorem s16c1G43_lift (hkitE : OmegaKitE16) {D : Data G} {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D ⊥ V L hV) (hc : Case167_1 D ⊥ V hV L)
    {B : Subgroup G} {g : G} (hBM : B ≤ D.M) (hBg : B ≤ conjSubgroup V g)
    (hBL : barSub ⊥ V hV B ≤ lBar ⊥ V hV L) (hB16 : Nat.card (barSub ⊥ V hV B) = 16) :
    ∃ (z : G) (P : Subgroup G), E16Lift V B z P := by
  have hMstab : D.M ≤ stabTil (⊥ : Subgroup G) V :=
    le_stabTil hS.setting.hyp151.hyp125.pairFacts.le_normalizer
      hS.setting.hyp151.hyp125.pairFacts.le_normalizer₀
  have hBst : B ≤ stabTil (⊥ : Subgroup G) V := hBM.trans hMstab
  have hEel : IsElemAbelian2 (barSub (⊥ : Subgroup G) V hV B) :=
    s16c1G44_isElemAbelian2_barSub hBg hBst
  obtain ⟨zt, hztne, Ptil, hPtilidx, hE1, hE2, hE3, hE4, hE5⟩ :=
    hkitE (Vtil (⊥ : Subgroup G) V hV) (lBar (⊥ : Subgroup G) V hV L) hc.2.1
      (barSub (⊥ : Subgroup G) V hV B) hBL hEel hB16
  obtain ⟨zh, hzh⟩ := mkTil_surjective (⊥ : Subgroup G) V hV zt
  let z : G := zh.val
  let P : Subgroup G := preTil (⊥ : Subgroup G) V hV Ptil
  have hzinj : Function.Injective (mkTil (⊥ : Subgroup G) V hV) := mkTil_bot_injective hV
  have hzne : z ≠ 1 := by
    intro h1
    apply hztne
    have hzh1 : zh = 1 := by
      apply IntMod.val_injective
      show z = 1
      exact h1
    rw [← hzh, hzh1, map_one]
  let S : Set G :=
    {v : G | v ∈ V ∧ ∃ b ∈ B, b ∉ centralizer (V : Set G) ∧ b * v * b⁻¹ = v}
  let S' : Set (IntMod V hV) := {x : IntMod V hV | x.val ∈ S}
  let T : Set (Vtil (⊥ : Subgroup G) V hV) :=
    {w : Vtil (⊥ : Subgroup G) V hV |
      ∃ e ∈ barSub (⊥ : Subgroup G) V hV B, e ≠ 1 ∧ e w = w}
  have hval : valHom V hV '' S' = S := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hg
      change g ∈ V ∧ ∃ b ∈ B, b ∉ centralizer (V : Set G) ∧ b * g * b⁻¹ = g at hg
      obtain ⟨hgV, hb⟩ := hg
      exact ⟨IntMod.mk hV ⟨g, hgV⟩, ⟨hgV, hb⟩, rfl⟩
  have hT : T = mkTil (⊥ : Subgroup G) V hV '' S' := by
    ext w
    constructor
    · rintro ⟨e, heE, hene, hew⟩
      obtain ⟨b, hbB, rfl⟩ := (mem_barSub (⊥ : Subgroup G) V hV B e).1 heE
      obtain ⟨x, rfl⟩ := mkTil_surjective (⊥ : Subgroup G) V hV w
      refine ⟨x, ?_, rfl⟩
      have hbcent : (b : G) ∉ centralizer (V : Set G) := fun hc =>
        hene ((s16c7_actTil_eq_one_iff_mem_centralizer V hV b).2 hc)
      have hbact : (b : G) * x.val * (b : G)⁻¹ = x.val :=
        (s16c1G43_actTil_val_eq_iff b.2 x.val_mem x).1 hew
      exact ⟨x.val_mem, (b : G), hbB, hbcent, hbact⟩
    · rintro ⟨x, hxS', rfl⟩
      change x.val ∈ V ∧ ∃ b ∈ B, b ∉ centralizer (V : Set G) ∧
        b * x.val * b⁻¹ = x.val at hxS'
      obtain ⟨hxV, b, hbB, hbcent, hbact⟩ := hxS'
      have hb' : b ∈ stabTil (⊥ : Subgroup G) V := hBst hbB
      refine ⟨actTil (⊥ : Subgroup G) V hV ⟨b, hb'⟩,
        actTil_mem_barSub (⊥ : Subgroup G) V hV hbB hb', ?_, ?_⟩
      · intro he1
        exact hbcent ((s16c7_actTil_eq_one_iff_mem_centralizer V hV ⟨b, hb'⟩).1 he1)
      · exact (s16c1G43_actTil_val_eq_iff hb' hxV x).2 hbact
  refine ⟨z, P, zh.val_mem, hzne, preTil_le (⊥ : Subgroup G) V hV Ptil, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hPsub : intSub V hV P = Ptil.comap (mkTil (⊥ : Subgroup G) V hV) := by
      ext x
      rw [mem_intSub, Subgroup.mem_comap,
        mem_preTil_iff_of_mem (⊥ : Subgroup G) V hV Ptil x.val_mem]
      exact Iff.rfl
    change (intSub V hV P).index = 2
    rw [hPsub, Subgroup.index_comap_of_surjective (H := Ptil)
      (f := mkTil (⊥ : Subgroup G) V hV) (mkTil_surjective (⊥ : Subgroup G) V hV), hPtilidx]
  · intro v hv
    let x_v : IntMod V hV := IntMod.mk hV ⟨v, hv⟩
    have hw1 : mkTil (⊥ : Subgroup G) V hV x_v = 1 ↔ v = 1 := by
      conv_lhs => rw [← map_one (mkTil (⊥ : Subgroup G) V hV)]
      rw [hzinj.eq_iff]
      exact Subtype.ext_iff
    have hwz : mkTil (⊥ : Subgroup G) V hV x_v = zt ↔ v = z := by
      conv_lhs => rw [← hzh]
      rw [hzinj.eq_iff]
      exact Subtype.ext_iff
    have hfix : (∀ b ∈ B, b * v * b⁻¹ = v) ↔
        (∀ e ∈ barSub (⊥ : Subgroup G) V hV B,
          e (mkTil (⊥ : Subgroup G) V hV x_v) = mkTil (⊥ : Subgroup G) V hV x_v) := by
      constructor
      · intro hb e he
        obtain ⟨b, hbB, rfl⟩ := (mem_barSub (⊥ : Subgroup G) V hV B e).1 he
        exact (s16c1G43_actTil_val_eq_iff b.2 hv x_v).2 (hb (b : G) hbB)
      · intro he b hbB
        have hb' : b ∈ stabTil (⊥ : Subgroup G) V := hBst hbB
        exact (s16c1G43_actTil_val_eq_iff hb' hv x_v).1
          (he (actTil (⊥ : Subgroup G) V hV ⟨b, hb'⟩)
            (actTil_mem_barSub (⊥ : Subgroup G) V hV hbB hb'))
    exact hfix.trans ((hE1 (mkTil (⊥ : Subgroup G) V hV x_v)).trans (or_congr hw1 hwz))
  · intro b hbB v hvP
    have hb' : b ∈ stabTil (⊥ : Subgroup G) V := hBst hbB
    have hvV : v ∈ V := preTil_le (⊥ : Subgroup G) V hV Ptil hvP
    let x_v : IntMod V hV := IntMod.mk hV ⟨v, hvV⟩
    have hxP : mkTil (⊥ : Subgroup G) V hV x_v ∈ Ptil :=
      (mem_preTil_iff_of_mem (⊥ : Subgroup G) V hV Ptil hvV).1 hvP
    rcases hE2 (actTil (⊥ : Subgroup G) V hV ⟨b, hb'⟩)
      (actTil_mem_barSub (⊥ : Subgroup G) V hV hbB hb')
      (mkTil (⊥ : Subgroup G) V hV x_v) hxP with h | h
    · left
      exact (s16c1G43_actTil_val_eq_iff hb' hvV x_v).1 h
    · right
      have h' : actTil (⊥ : Subgroup G) V hV ⟨b, hb'⟩
            (mkTil (⊥ : Subgroup G) V hV x_v) =
          mkTil (⊥ : Subgroup G) V hV (x_v * zh) := by
        rw [h, ← hzh, ← map_mul]
      have h2 := (s16c1G43_actTil_val_eq_iff hb' hvV (x_v * zh)).1 h'
      exact h2
  · intro b hbB hbcent v hvV hdisj
    have hb' : b ∈ stabTil (⊥ : Subgroup G) V := hBst hbB
    have hene : actTil (⊥ : Subgroup G) V hV ⟨b, hb'⟩ ≠ 1 := fun he1 =>
      hbcent ((s16c7_actTil_eq_one_iff_mem_centralizer V hV ⟨b, hb'⟩).1 he1)
    let x_v : IntMod V hV := IntMod.mk hV ⟨v, hvV⟩
    rw [mem_preTil_iff_of_mem (⊥ : Subgroup G) V hV Ptil hvV]
    refine hE3 (actTil (⊥ : Subgroup G) V hV ⟨b, hb'⟩)
      (actTil_mem_barSub (⊥ : Subgroup G) V hV hbB hb') hene
      (mkTil (⊥ : Subgroup G) V hV x_v) ?_
    rcases hdisj with h | h
    · left
      exact (s16c1G43_actTil_val_eq_iff hb' hvV x_v).2 h
    · right
      have h2 : actTil (⊥ : Subgroup G) V hV ⟨b, hb'⟩
            (mkTil (⊥ : Subgroup G) V hV x_v) =
          mkTil (⊥ : Subgroup G) V hV (x_v * zh) :=
        (s16c1G43_actTil_val_eq_iff hb' hvV (x_v * zh)).2 h
      rwa [map_mul, hzh] at h2
  · intro v hvP
    have hvV : v ∈ V := preTil_le (⊥ : Subgroup G) V hV Ptil hvP
    let x_v : IntMod V hV := IntMod.mk hV ⟨v, hvV⟩
    have hxP : mkTil (⊥ : Subgroup G) V hV x_v ∈ Ptil :=
      (mem_preTil_iff_of_mem (⊥ : Subgroup G) V hV Ptil hvV).1 hvP
    have hwcl : mkTil (⊥ : Subgroup G) V hV x_v ∈ Subgroup.closure T := hE4 hxP
    have hxcl : x_v ∈ Subgroup.closure S' := by
      have hmem : mkTil (⊥ : Subgroup G) V hV x_v ∈
          (Subgroup.closure S').map (mkTil (⊥ : Subgroup G) V hV) := by
        rw [MonoidHom.map_closure, ← hT]
        exact hwcl
      obtain ⟨y, hy, hyeq⟩ := hmem
      have hyx : y = x_v := hzinj hyeq
      rwa [hyx] at hy
    have hvm : v ∈ (Subgroup.closure S').map (valHom V hV) := ⟨x_v, hxcl, rfl⟩
    rwa [MonoidHom.map_closure, hval] at hvm
  · obtain ⟨e, heE, w, hwP, hne⟩ := hE5
    obtain ⟨b, hbB, rfl⟩ := (mem_barSub (⊥ : Subgroup G) V hV B e).1 heE
    obtain ⟨x, rfl⟩ := mkTil_surjective (⊥ : Subgroup G) V hV w
    have hxP : x.val ∈ P := by
      rw [mem_preTil_iff_of_mem (⊥ : Subgroup G) V hV Ptil x.val_mem]
      exact hwP
    exact ⟨(b : G), hbB, x.val, hxP, fun heq =>
      hne ((s16c1G43_actTil_val_eq_iff b.2 x.val_mem x).2 heq)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
