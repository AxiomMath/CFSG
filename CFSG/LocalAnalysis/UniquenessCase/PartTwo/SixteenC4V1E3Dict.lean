module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1E3Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47K1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary (SUid)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

private theorem s16c4v1e3_commutator_le_of_le_stabTil {V₀ V X : Subgroup G}
    (hX : X ≤ stabTil V₀ V) : ⁅V, X⁆ ≤ V :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp
    (hX.trans (stabTil_le_normalizer V₀ V))

private theorem s16c4v1e3_mkTil_commutator_mem_commSub {V₀ V X : Subgroup G}
    (hV : IsElemAbelian 2 V) (hX : X ≤ stabTil V₀ V)
    {W : Subgroup (Vtil V₀ V hV)} {v x : G} (hv : v ∈ V) (hx : x ∈ X)
    (hW : mkTil V₀ V hV (IntMod.mk hV ⟨v, hv⟩) ∈ W) :
    mkTil V₀ V hV (IntMod.mk hV ⟨⁅v, x⁆, s16c4v1e3_commutator_le_of_le_stabTil hX
      (Subgroup.commutator_mem_commutator hv hx)⟩) ∈
      commSub W (barSub V₀ V hV X) := by
  classical
  have hcommV : ⁅V, X⁆ ≤ V := s16c4v1e3_commutator_le_of_le_stabTil hX
  have hsq : ∀ w : Vtil V₀ V hV, w⁻¹ = w := by
    intro w
    obtain ⟨y, rfl⟩ := mkTil_surjective V₀ V hV w
    have h2 : (mkTil V₀ V hV y) ^ 2 = 1 := by
      rw [← map_pow, IntMod.sq_eq_one y, map_one]
    rw [pow_two] at h2
    exact inv_eq_of_mul_eq_one_right h2
  have hmul : ∀ a b : Vtil V₀ V hV, a * b = b * a := fun a b => mul_comm a b
  set xb : MulAut (Vtil V₀ V hV) := actTil V₀ V hV ⟨x, hX hx⟩ with hxb
  set a : Vtil V₀ V hV := mkTil V₀ V hV (IntMod.mk hV ⟨v, hv⟩) with ha
  have hmem3 : x * v⁻¹ * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp
    (stabTil_le_normalizer V₀ V (hX hx)) v⁻¹).1 (V.inv_mem hv)
  have hc : mkTil V₀ V hV (IntMod.mk hV ⟨x * v⁻¹ * x⁻¹, hmem3⟩) = xb a⁻¹ := by
    rw [hxb, ha, ← map_inv, actTil_mk]
    rw [show (actStab V₀ V hV ⟨x, hX hx⟩) (IntMod.mk hV ⟨v, hv⟩)⁻¹ =
        IntMod.mk hV ⟨x * v⁻¹ * x⁻¹, hmem3⟩ from by
      rw [map_inv]
      congr 1
      apply IntMod.val_injective
      rw [IntMod.val_inv, actStab_apply_val]
      group
      rfl]
  have h1 : ⁅v, x⁆ = v * (x * v⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
  have hval : v * (x * v⁻¹ * x⁻¹) ∈ V := V.mul_mem hv hmem3
  have h2 : mkTil V₀ V hV (IntMod.mk hV ⟨⁅v, x⁆, hcommV
      (Subgroup.commutator_mem_commutator hv hx)⟩) = xb a * a⁻¹ := by
    have h3 : IntMod.mk hV ⟨⁅v, x⁆, hcommV
        (Subgroup.commutator_mem_commutator hv hx)⟩ =
        IntMod.mk hV ⟨v * (x * v⁻¹ * x⁻¹), hval⟩ := Subtype.ext h1
    rw [h3]
    have h4 : IntMod.mk hV ⟨v * (x * v⁻¹ * x⁻¹), hval⟩ =
        IntMod.mk hV ⟨v, hv⟩ * IntMod.mk hV ⟨x * v⁻¹ * x⁻¹, hmem3⟩ := rfl
    rw [h4, map_mul, hc]
    simp only [hsq]
    change a * xb a = xb a * a
    exact hmul a (xb a)
  rw [h2]
  exact Subgroup.subset_closure ⟨xb, actTil_mem_barSub V₀ V hV hx (hX hx), a, hW, rfl⟩

private theorem s16c4v1e3_imgTil_commutator_eq_commSub {V₀ V A X : Subgroup G}
    (hV : IsElemAbelian 2 V) (hA : A ≤ V) (hX : X ≤ stabTil V₀ V) :
    imgTil V₀ V hV ⁅A, X⁆ = commSub (imgTil V₀ V hV A) (barSub V₀ V hV X) := by
  classical
  have hcommV : ⁅A, X⁆ ≤ V := (Subgroup.commutator_mono hA le_rfl).trans
    (s16c4v1e3_commutator_le_of_le_stabTil hX)
  apply le_antisymm
  · rw [imgTil, Subgroup.map_le_iff_le_comap]
    intro w hw
    rw [Subgroup.mem_comap]
    have hmain : ∀ (a : G) (ha : a ∈ ⁅A, X⁆), mkTil V₀ V hV
        (IntMod.mk hV ⟨a, hcommV ha⟩) ∈
        commSub (imgTil V₀ V hV A) (barSub V₀ V hV X) := by
      intro a ha
      induction ha using Subgroup.closure_induction with
      | mem a ha =>
        obtain ⟨v, hv, x, hx, rfl⟩ := ha
        have hW : mkTil V₀ V hV (IntMod.mk hV ⟨v, hA hv⟩) ∈ imgTil V₀ V hV A :=
          (mem_imgTil V₀ V hV A _).2 ⟨IntMod.mk hV ⟨v, hA hv⟩, hv, rfl⟩
        exact s16c4v1e3_mkTil_commutator_mem_commSub hV hX (hA hv) hx hW
      | one =>
        rw [show IntMod.mk hV ⟨1, hcommV (one_mem _)⟩ = 1 from Subtype.ext rfl, map_one]
        exact one_mem _
      | mul a b ha hb iha ihb =>
        rw [show IntMod.mk hV ⟨a * b, hcommV (mul_mem ha hb)⟩ =
          IntMod.mk hV ⟨a, hcommV ha⟩ * IntMod.mk hV ⟨b, hcommV hb⟩ from Subtype.ext rfl,
          map_mul]
        exact mul_mem iha ihb
      | inv a ha iha =>
        rw [show IntMod.mk hV ⟨a⁻¹, hcommV (inv_mem ha)⟩ =
          (IntMod.mk hV ⟨a, hcommV ha⟩)⁻¹ from Subtype.ext rfl, map_inv]
        exact inv_mem iha
    have hw' : IntMod.mk hV ⟨w.val, hcommV hw⟩ = w := IntMod.val_injective rfl
    have hres := hmain w.val hw
    rwa [hw'] at hres
  · rw [commSub, Subgroup.closure_le]
    rintro c ⟨xb, hxb, w, hw, rfl⟩
    change xb w * w⁻¹ ∈ imgTil V₀ V hV ⁅A, X⁆
    rw [mem_imgTil]
    obtain ⟨x, hxX, rfl⟩ := (mem_barSub V₀ V hV X xb).1 hxb
    obtain ⟨z, hzA, hzw⟩ := (mem_imgTil V₀ V hV A w).1 hw
    rw [← hzw]
    obtain ⟨v, rfl⟩ : ∃ v : ↥V, IntMod.mk hV v = z :=
      ⟨⟨z.val, z.val_mem⟩, IntMod.val_injective rfl⟩
    have hmem2 : (x : G) * (v : G) * (x : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp
      (stabTil_le_normalizer V₀ V (hX hxX)) (v : G)).1 v.2
    have hmem3 : (x : G) * (v : G) * (x : G)⁻¹ * (v : G)⁻¹ ∈ V :=
      V.mul_mem hmem2 (V.inv_mem v.2)
    have hcomm : ⁅(x : G), (v : G)⁆ ∈ ⁅A, X⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hxX hzA
    refine ⟨IntMod.mk hV ⟨(x : G) * (v : G) * (x : G)⁻¹ * (v : G)⁻¹, hmem3⟩,
      hcomm, ?_⟩
    have h1 : (actStab V₀ V hV x) (IntMod.mk hV v) =
        IntMod.mk hV ⟨(x : G) * (v : G) * (x : G)⁻¹, hmem2⟩ := by
      apply IntMod.val_injective
      rw [actStab_apply_val]
      rfl
    rw [actTil_mk, h1, ← map_inv, ← map_mul]
    rfl

theorem s16c4v1e3_dict_E (S : s16c4v1_Sit D V L hV) (h1217 : R1217 D) {g : G}
    (hg : s16c4v1_Cex D V g) :
    barSub (v1Sub D.M ⊥ V hV L) V hV (conjSubgroup V g) ≤
        normalizer (lBar (v1Sub D.M ⊥ V hV L) V hV L :
          Set (MulAut (Vtil (v1Sub D.M ⊥ V hV L) V hV))) ∧
      IsElemAbelian2 (barSub (v1Sub D.M ⊥ V hV L) V hV (conjSubgroup V g)) ∧
      Nat.card (barSub (v1Sub D.M ⊥ V hV L) V hV (conjSubgroup V g)) =
        2 ^ s16c4v1_r2 V g := by
  have hA2 : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  refine ⟨?_, ?_, ?_⟩
  · intro φ hφ
    obtain ⟨a, haA, rfl⟩ :=
      (mem_barSub (v1Sub D.M ⊥ V hV L) V hV (conjSubgroup V g) φ).1 hφ
    exact Sixteen24.actTil_v1Sub_mem_normalizer D h1217 S.sect.setting.hyp151 hV (hg.1 haA)
      (by rw [Sixteen24.nBar_eq_of_uFrame D S.sect.setting.hyp151 hV S.F]; exact hg.1 haA)
      (s16c4v1_mem_stabTil S (hg.1 haA))
  · exact isElemAbelian2_barSub hV hA2
  · calc Nat.card (barSub (v1Sub D.M ⊥ V hV L) V hV (conjSubgroup V g))
        = (Subgroup.centralizer (V : Set G)).relIndex (conjSubgroup V g) :=
          s16c4v1_cxh_card_barSub S h1217 hg.1
      _ = 2 ^ E3.mQuot (conjSubgroup V g) (Subgroup.centralizer (V : Set G)) :=
          E3.relIndex_eq_two_pow hA2.isPGroup (Subgroup.centralizer (V : Set G))
      _ = 2 ^ s16c4v1_r2 V g := rfl

theorem s16c4v1e3_dict_ne_bot (S : s16c4v1_Sit D V L hV) (h1217 : R1217 D) {g : G}
    (hg : s16c4v1_Cex D V g) :
    barSub (v1Sub D.M ⊥ V hV L) V hV (conjSubgroup V g) ≠ ⊥ := by
  intro hbot
  apply hg.2
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have haM : a ∈ D.M := hg.1 ha
  have has : a ∈ stabTil (v1Sub D.M ⊥ V hV L) V := s16c4v1_mem_stabTil S haM
  have hmem : actTil (v1Sub D.M ⊥ V hV L) V hV ⟨a, has⟩ ∈
      barSub (v1Sub D.M ⊥ V hV L) V hV (conjSubgroup V g) :=
    actTil_mem_barSub (v1Sub D.M ⊥ V hV L) V hV ha has
  rw [hbot] at hmem
  have h1 : actTil (v1Sub D.M ⊥ V hV L) V hV ⟨a, has⟩ = 1 := Subgroup.mem_bot.1 hmem
  have htriv := (actTil_eq_one_iff (v1Sub D.M ⊥ V hV L) V hV ⟨a, has⟩).1 h1
  have hfix := (s16c4v1_centralizes_iff S h1217 haM).1 htriv
  calc a * v = (a * v * a⁻¹) * a := by group
    _ = v * a := by rw [hfix v hv]

theorem s16c4v1e3_dict_cent (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1e3_Std D) {g : G}
    (hg : s16c4v1_Cex D V g) (hg' : s16c4v1_Cex D V g⁻¹) :
    imgTil (v1Sub D.M ⊥ V hV L) V hV (Subgroup.centralizer (conjSubgroup V g : Set G)) =
      fixV (barSub (v1Sub D.M ⊥ V hV L) V hV (conjSubgroup V g)) := by
  set V₁ : Subgroup G := v1Sub D.M ⊥ V hV L with hV₁
  have hstab : ∀ m ∈ D.M, m ∈ stabTil V₁ V := by
    intro m hm
    rw [hV₁]
    exact s16c4v1_mem_stabTil S hm
  have hV1leV : V₁ ≤ V := by
    rw [hV₁]
    exact s16c4v1_v1_le S
  have hcentV1 : ∀ a ∈ conjSubgroup V g, ∀ x ∈ V₁, a * x * a⁻¹ = x := by
    intro a ha x hx
    exact s16c4v1e3_cex_cent_V1 S hstd hg hg' a ha x (by rw [hV₁] at hx; exact hx)
  apply le_antisymm
  · intro q hq
    rw [mem_fixV]
    intro φ hφ
    obtain ⟨x, hxC, rfl⟩ :=
      (mem_imgTil V₁ V hV (Subgroup.centralizer (conjSubgroup V g : Set G)) q).1 hq
    obtain ⟨a', ha'A, rfl⟩ :=
      (mem_barSub V₁ V hV (conjSubgroup V g) φ).1 hφ
    rw [actTil_mk]
    congr 1
    apply IntMod.val_injective
    rw [actStab_apply_val]
    have hcomm := (Subgroup.mem_centralizer_iff.1 hxC) (a' : G) ha'A
    calc (a' : G) * x.val * (a' : G)⁻¹
        = x.val * (a' : G) * (a' : G)⁻¹ := by rw [hcomm]
      _ = x.val := by group
  · intro q hq
    rw [mem_imgTil]
    obtain ⟨x, hx⟩ := mkTil_surjective V₁ V hV q
    refine ⟨x, ?_, hx⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have has : a ∈ stabTil V₁ V := hstab a (hg.1 ha)
    have hfix := hq (actTil V₁ V hV ⟨a, has⟩) (actTil_mem_barSub V₁ V hV ha has)
    rw [← hx, actTil_mk] at hfix
    let d : G := (actStab V₁ V hV ⟨a, has⟩ x).val * x.val⁻¹
    have hdV1 : d ∈ V₁ := (mkTil_eq_iff V₁ V hV _ _).1 hfix
    have hdmem : d ∈ ⁅V, conjSubgroup V g⁆ := by
      have h1 : d = ⁅a, x.val⁆ := by
        rw [show d = (actStab V₁ V hV ⟨a, has⟩ x).val * x.val⁻¹ from rfl,
          actStab_apply_val, commutatorElement_def]
      rw [h1, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator ha x.val_mem
    have hd1 : d = 1 := by
      by_contra hne
      exact (s16c4v1e3_cex_D_sing S hstd hg hg' d hdmem hne).1
        ((s16c4v1_vec_eq_zero_iff S (hV1leV hdV1)).2 hdV1)
    have hfixA : a * x.val * a⁻¹ = x.val := by
      have h2 : (actStab V₁ V hV ⟨a, has⟩ x).val = a * x.val * a⁻¹ :=
        actStab_apply_val V₁ V hV ⟨a, has⟩ x
      rw [show d = (actStab V₁ V hV ⟨a, has⟩ x).val * x.val⁻¹ from rfl] at hd1
      rw [← h2]
      exact mul_inv_eq_one.1 hd1
    calc a * x.val = (a * x.val * a⁻¹) * a := by group
      _ = x.val * a := by rw [hfixA]

theorem s16c4v1e3_dict_fix (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1e3_Std D) {g : G}
    (hg : s16c4v1_Cex D V g) (hg' : s16c4v1_Cex D V g⁻¹) :
    2 ^ s16c4v1_r1 V g *
      Nat.card (fixV (barSub (v1Sub D.M ⊥ V hV L) V hV (conjSubgroup V g))) = 2 ^ 8 := by
  set V₁ : Subgroup G := v1Sub D.M ⊥ V hV L with hV₁
  have hV1leV : V₁ ≤ V := by
    rw [hV₁]
    exact s16c4v1_v1_le S
  have hV1leC : V₁ ≤ Subgroup.centralizer (conjSubgroup V g : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h := s16c4v1e3_cex_cent_V1 S hstd hg hg' a ha x (by rw [hV₁] at hx; exact hx)
    calc a * x = (a * x * a⁻¹) * a := by group
      _ = x * a := by rw [h]
  have hcent : fixV (barSub V₁ V hV (conjSubgroup V g)) =
      imgTil V₁ V hV (Subgroup.centralizer (conjSubgroup V g : Set G)) := by
    rw [hV₁]
    exact (s16c4v1e3_dict_cent S hstd hg hg').symm
  have hcard1 := s16c1_card_imgTil_mul (V₀ := V₁) (V := V)
    (U := Subgroup.centralizer (conjSubgroup V g : Set G) ⊓ V) hV inf_le_right
  have himg : imgTil V₁ V hV (Subgroup.centralizer (conjSubgroup V g : Set G) ⊓ V) =
      imgTil V₁ V hV (Subgroup.centralizer (conjSubgroup V g : Set G)) := by
    ext q
    rw [mem_imgTil, mem_imgTil]
    exact ⟨fun ⟨x, hx, hq⟩ => ⟨x, hx.1, hq⟩,
      fun ⟨x, hx, hq⟩ => ⟨x, ⟨hx, x.val_mem⟩, hq⟩⟩
  have hinf : (Subgroup.centralizer (conjSubgroup V g : Set G) ⊓ V) ⊓ V₁ = V₁ :=
    inf_eq_right.2 (le_inf hV1leC hV1leV)
  have hcard1' : Nat.card (imgTil V₁ V hV
        (Subgroup.centralizer (conjSubgroup V g : Set G))) * Nat.card V₁ =
      Nat.card ↥(Subgroup.centralizer (conjSubgroup V g : Set G) ⊓ V) := by
    simpa only [himg, hinf] using hcard1
  have hmq : E3.mQuot V (Subgroup.centralizer (conjSubgroup V g : Set G) ⊓ V) =
      s16c4v1_r1 V g := by
    rw [s16c4v1_r1]
    simp only [E3.mQuot, Subgroup.inf_relIndex_right]
  have hcardV : Nat.card V = 2 ^ s16c4v1_r1 V g *
      Nat.card ↥(Subgroup.centralizer (conjSubgroup V g : Set G) ⊓ V) := by
    rw [← hmq]
    exact E3.card_eq_two_pow_mul hV.isPGroup inf_le_right
  have key : 2 ^ s16c4v1_r1 V g *
      Nat.card (fixV (barSub V₁ V hV (conjSubgroup V g))) * Nat.card V₁ =
      2 ^ 8 * Nat.card V₁ := by
    calc 2 ^ s16c4v1_r1 V g *
          Nat.card (fixV (barSub V₁ V hV (conjSubgroup V g))) * Nat.card V₁
        = 2 ^ s16c4v1_r1 V g *
          (Nat.card (fixV (barSub V₁ V hV (conjSubgroup V g))) * Nat.card V₁) := by ring
      _ = 2 ^ s16c4v1_r1 V g *
          (Nat.card (imgTil V₁ V hV
            (Subgroup.centralizer (conjSubgroup V g : Set G))) * Nat.card V₁) := by
            rw [hcent]
      _ = 2 ^ s16c4v1_r1 V g *
          Nat.card ↥(Subgroup.centralizer (conjSubgroup V g : Set G) ⊓ V) := by
            rw [hcard1']
      _ = Nat.card V := hcardV.symm
      _ = 2 ^ 8 * Nat.card V₁ := s16c4v1_card_V S
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos key

theorem s16c4v1e3_dict_img (S : s16c4v1_Sit D V L hV) {A : Subgroup G} (hA : A ≤ D.M) :
    imgTil (v1Sub D.M ⊥ V hV L) V hV ⁅V, A⁆ =
      commV (barSub (v1Sub D.M ⊥ V hV L) V hV A) := by
  have hAstab : A ≤ stabTil (v1Sub D.M ⊥ V hV L) V := by
    intro a ha
    exact s16c4v1_mem_stabTil S (hA ha)
  have h := s16c4v1e3_imgTil_commutator_eq_commSub (V₀ := v1Sub D.M ⊥ V hV L)
    (A := V) (X := A) hV le_rfl hAstab
  have htop : imgTil (v1Sub D.M ⊥ V hV L) V hV V = ⊤ := by
    refine le_antisymm le_top ?_
    intro q _
    obtain ⟨x, rfl⟩ := mkTil_surjective (v1Sub D.M ⊥ V hV L) V hV q
    exact (mem_imgTil (v1Sub D.M ⊥ V hV L) V hV V
      (mkTil (v1Sub D.M ⊥ V hV L) V hV x)).2 ⟨x, x.val_mem, rfl⟩
  rw [htop, ← commV_eq_commSub] at h
  exact h

theorem s16c4v1e3_dict_comm (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1e3_Std D) {g : G}
    (hg : s16c4v1_Cex D V g) (hg' : s16c4v1_Cex D V g⁻¹) :
    Nat.card ↥⁅V, conjSubgroup V g⁆ =
      Nat.card (commV (barSub (v1Sub D.M ⊥ V hV L) V hV (conjSubgroup V g))) := by
  have hVn := S.sect.setting.hyp16.hyp125.pairFacts.le_normalizer
  have hDV : ⁅V, conjSubgroup V g⁆ ≤ V :=
    (s16c4v1_cex_comm_le hVn hg.1 hg'.1).trans inf_le_left
  have hbot : ⁅V, conjSubgroup V g⁆ ⊓ v1Sub D.M ⊥ V hV L = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro d hd
    rw [Subgroup.mem_inf] at hd
    obtain ⟨hdD, hdV1⟩ := hd
    by_contra hd1
    exact (s16c4v1e3_cex_D_sing S hstd hg hg' d hdD hd1).1
      ((s16c4v1_vec_eq_zero_iff S (s16c4v1_v1_le S hdV1)).2 hdV1)
  have hbot1 : Nat.card ↥(⁅V, conjSubgroup V g⁆ ⊓ v1Sub D.M ⊥ V hV L) = 1 := by
    rw [hbot, Subgroup.card_bot]
  have hcard := s16c1_card_imgTil_mul (V₀ := v1Sub D.M ⊥ V hV L) (V := V)
    (U := ⁅V, conjSubgroup V g⁆) hV hDV
  rw [hbot1, Nat.mul_one] at hcard
  rw [← hcard, s16c4v1e3_dict_img S hg.1]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
