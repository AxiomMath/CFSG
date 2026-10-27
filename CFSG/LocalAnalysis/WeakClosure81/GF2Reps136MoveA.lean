module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Defs
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SectTransfer
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136IrrCorr
import CFSG.Quasithin.Background.MovingSectionRank
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Four

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369_stableUnder_sup {X : Subgroup (MulAut W)} {A B : Subgroup W}
    (hA : StableUnder X A) (hB : StableUnder X B) : StableUnder X (A ⊔ B) := by
  intro x hx u hu
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hu
  rw [map_mul]
  exact Subgroup.mul_mem_sup (hA x hx a ha) (hB x hx b hb)

private theorem w1369_stableUnder_inf {X : Subgroup (MulAut W)} {A B : Subgroup W}
    (hA : StableUnder X A) (hB : StableUnder X B) : StableUnder X (A ⊓ B) := by
  intro x hx u hu
  obtain ⟨huA, huB⟩ := Subgroup.mem_inf.mp hu
  exact Subgroup.mem_inf.mpr ⟨hA x hx u huA, hB x hx u huB⟩

private theorem w1369_commSub_sup (A B : Subgroup W) (X : Subgroup (MulAut W)) :
    commSub (A ⊔ B) X = commSub A X ⊔ commSub B X := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
    have h1 : x (a * b) * (a * b)⁻¹ = (x a * a⁻¹) * (x b * b⁻¹) := by
      rw [map_mul, mul_inv_rev]
      calc x a * x b * (b⁻¹ * a⁻¹)
          = x a * x b * (a⁻¹ * b⁻¹) := by rw [mul_comm (b⁻¹) (a⁻¹)]
        _ = x a * (x b * (a⁻¹ * b⁻¹)) := by rw [mul_assoc]
        _ = x a * (a⁻¹ * (x b * b⁻¹)) := by
              rw [← mul_assoc (x b) (a⁻¹) (b⁻¹), mul_comm (x b) (a⁻¹), mul_assoc]
        _ = (x a * a⁻¹) * (x b * b⁻¹) := by rw [← mul_assoc]
    rw [h1]
    exact Subgroup.mul_mem_sup (Subgroup.subset_closure ⟨x, hx, a, ha, rfl⟩)
      (Subgroup.subset_closure ⟨x, hx, b, hb, rfl⟩)
  · exact sup_le (commSub_mono le_sup_left le_rfl) (commSub_mono le_sup_right le_rfl)

private theorem w1369_stableUnder_fixV (X : Subgroup (MulAut W)) : StableUnder X (fixV X) := by
  intro x hx u hu
  rw [mem_fixV] at hu ⊢
  intro z hz
  calc z (x u) = (z * x) u := rfl
    _ = u := hu (z * x) (X.mul_mem hz hx)
    _ = x u := (hu x hx).symm

private theorem w1369_commSub_fixV_bot (X : Subgroup (MulAut W)) : commSub (fixV X) X = ⊥ :=
  commSub_eq_bot_iff.mpr le_rfl

structure Move136 (Y : Subgroup (MulAut W)) (t : MulAut W) (L : Subgroup (MulAut W))
    (I : Subgroup W) : Prop where
  ctx : Ctx136 Y t L
  hI : I ∈ irrSet L
  hmove : I.map t.toMonoidHom ≠ I

private theorem w1369_mul_self {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} {I : Subgroup W} (S : Move136 Y t L I) : t * t = 1 := by
  have h := pow_orderOf_eq_one t
  rw [S.ctx.std.t2] at h
  simpa [pow_two] using h

theorem move_conj_irr {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)}
    {I : Subgroup W} (S : Move136 Y t L I) :
    I.map t.toMonoidHom ∈ irrSet L ∧ (I.map t.toMonoidHom).map t.toMonoidHom = I ∧
      StableUnder L (I.map t.toMonoidHom) := by
  have htN : t ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (S.ctx.hfix L S.ctx.comp)
  obtain ⟨-, -, hItstab, -, -⟩ := (irr_stab htN).2.2 I S.hI
  have hmem : I.map t.toMonoidHom ∈ irrSet L := (irr_stab htN).2.2 I S.hI
  have ht2 : t * t = 1 := w1369_mul_self S
  have hcomp : t.toMonoidHom.comp t.toMonoidHom = MonoidHom.id W := by
    ext v
    have h := congrArg (fun g : MulAut W => g v) ht2
    simpa [MulAut.mul_apply] using h
  refine ⟨hmem, ?_, hItstab⟩
  rw [Subgroup.map_map, hcomp, Subgroup.map_id]

theorem move_symm {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)}
    {I : Subgroup W} (S : Move136 Y t L I) : Move136 Y t L (I.map t.toMonoidHom) :=
  ⟨S.ctx, (move_conj_irr S).1, fun h => S.hmove (((move_conj_irr S).2.1) ▸ h).symm⟩

theorem move_inter (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} {I : Subgroup W} (S : Move136 Y t L I) :
    I ⊓ I.map t.toMonoidHom ≤ fixV L := by
  obtain ⟨-, -, hItstab⟩ := move_conj_irr S
  obtain ⟨hIcomm, hIlt, hIstab, hZstab, hirr⟩ := S.hI
  set J : Subgroup W := I ⊓ I.map t.toMonoidHom with hJ
  have hJstab : StableUnder L J := w1369_stableUnder_inf hIstab hItstab
  have hsupstab : StableUnder L (J ⊔ (I ⊓ fixV L)) := w1369_stableUnder_sup hJstab hZstab
  rcases hirr (J ⊔ (I ⊓ fixV L)) hsupstab le_sup_right
      (sup_le inf_le_left inf_le_left) with h | h
  · exact le_trans (le_trans le_sup_left (le_of_eq h)) inf_le_right
  · exfalso
    have hCbot : commSub (I ⊓ fixV L) L = ⊥ :=
      le_bot_iff.mp ((commSub_mono inf_le_right le_rfl).trans
        (le_of_eq (w1369_commSub_fixV_bot L)))
    have hcomm : commSub (J ⊔ (I ⊓ fixV L)) L = commSub J L := by
      rw [w1369_commSub_sup, hCbot, sup_bot_eq]
    have hIle : I ≤ I.map t.toMonoidHom := by
      calc I = commSub I L := hIcomm.symm
        _ = commSub (J ⊔ (I ⊓ fixV L)) L := by rw [h]
        _ = commSub J L := hcomm
        _ ≤ J := commSub_le_of_invariant hJstab
        _ ≤ I.map t.toMonoidHom := inf_le_right
    have hcard : Nat.card ↥(I.map t.toMonoidHom) = Nat.card ↥I :=
      Subgroup.card_map_of_injective t.injective
    have hEq : I = I.map t.toMonoidHom :=
      Subgroup.eq_of_le_of_card_ge hIle (le_of_eq hcard)
    exact S.hmove hEq.symm

private theorem w1369_mQuot_eq_rk_sect (I Z : Subgroup W) :
    E3.mQuot I Z = rk ↥(⊤ : Subgroup (Sect I Z)) := by
  rw [CFSG.Quasithin.rk_top]
  rfl

private theorem w1369_mQuot_fixV_zpowers_eq (I : Subgroup W) (t : MulAut W) :
    E3.mQuot I (I ⊓ fixV (Subgroup.zpowers t)) = rk ↥(I.map (commHom t)) := by
  have hker : I ⊓ (commHom t).ker = I ⊓ fixV (Subgroup.zpowers t) := by rw [ker_commHom]
  have h1 : rk ↥(I.map (commHom t)) + rk ↥(I ⊓ fixV (Subgroup.zpowers t)) = rk ↥I := by
    have h := rk_map_add_rk_inf_ker (commHom t) I
    rwa [hker] at h
  have h2 : E3.mQuot I (I ⊓ fixV (Subgroup.zpowers t)) +
      rk ↥(I ⊓ fixV (Subgroup.zpowers t)) = rk ↥I := by
    have hcard := rk_add_rkIdx ((I ⊓ fixV (Subgroup.zpowers t)).subgroupOf I)
    have hZ : rk ↥((I ⊓ fixV (Subgroup.zpowers t)).subgroupOf I) =
        rk ↥(I ⊓ fixV (Subgroup.zpowers t)) := by
      unfold rk
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    rw [E3.mQuot_eq_rkIdx]
    rw [hZ] at hcard
    omega
  omega

private theorem w1369_mQuot_fixV_zpowers_le (I : Subgroup W) (t : MulAut W) :
    E3.mQuot I (I ⊓ fixV (Subgroup.zpowers t)) ≤
      rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
  rw [w1369_mQuot_fixV_zpowers_eq]
  refine rk_mono ?_
  rw [commSub_zpowers_eq_map (W := ⊤) (fun _ _ w _ => trivial)]
  exact Subgroup.map_mono le_top

private theorem w1369_commutator_eq_self_of_isQuasisimple {G : Type*} [Group G]
    {L : Subgroup G} (h : CFSG.IsQuasisimple ↥L) : ⁅L, L⁆ = L := by
  have h1 : (commutator ↥L).map L.subtype = ⁅L, L⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [h.1.commutator_eq_top] at h1
  rw [← h1, Subgroup.map_top, Subgroup.range_subtype]

private theorem w1369_eq_of_le_of_mQuot_eq (hw2 : ∀ w : W, w ^ 2 = 1) {A B I : Subgroup W}
    (hAB : A ≤ B) (hBI : B ≤ I) (h : E3.mQuot I A = E3.mQuot I B) : A = B := by
  have hadd := E3.mQuot_add hAB hBI
  have h0 : E3.mQuot B A = 0 := by omega
  have hB2 : IsPGroup 2 ↥B := (CFSG.Quasithin.isPGroup_two_of_sq_eq_one hw2).to_subgroup B
  exact (E3.mQuot_eq_zero_iff hB2 hAB).mp h0

private theorem w1369_fix_mod_le {L : Subgroup (MulAut W)} {I : Subgroup W} (hI : I ∈ irrSet L)
    {a : W} (ha : a ∈ I) (h : ∀ l ∈ L, l a * a⁻¹ ∈ fixV L) : a ∈ fixV L := by
  obtain ⟨hIcomm, hIlt, hIstab, -, hirr⟩ := hI
  set Z : Subgroup W := I ⊓ fixV L with hZ
  let X : Subgroup W :=
    { carrier := {x | x ∈ I ∧ ∀ l ∈ L, l x * x⁻¹ ∈ fixV L}
      one_mem' := ⟨I.one_mem, fun l _ => by simpa using (fixV L).one_mem⟩
      mul_mem' := fun {x y} hx hy =>
        ⟨I.mul_mem hx.1 hy.1, fun l hl => by
          have h1 : l (x * y) * (x * y)⁻¹ = (l x * x⁻¹) * (l y * y⁻¹) := by
            rw [map_mul, mul_inv_rev]; ac_rfl
          rw [h1]
          exact (fixV L).mul_mem (hx.2 l hl) (hy.2 l hl)⟩
      inv_mem' := fun {x} hx =>
        ⟨I.inv_mem hx.1, fun l hl => by
          have h1 : l x⁻¹ * (x⁻¹)⁻¹ = (l x * x⁻¹)⁻¹ := by
            simp only [map_inv, inv_inv, mul_inv_rev]
            ac_rfl
          rw [h1]
          exact (fixV L).inv_mem (hx.2 l hl)⟩ }
  have hXstab : StableUnder L X := by
    intro l' hl' x hx
    refine ⟨hIstab l' hl' x hx.1, fun l hl => ?_⟩
    have hk : l'⁻¹ * l * l' ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hl') hl) hl'
    have hx' : (l'⁻¹ * l * l') x * x⁻¹ ∈ fixV L := hx.2 (l'⁻¹ * l * l') hk
    have heq : l' ((l'⁻¹ * l * l') x * x⁻¹) = l (l' x) * (l' x)⁻¹ := by
      have hcomp : (l' * (l'⁻¹ * l * l') : MulAut W) = l * l' := by group
      have h2 : (l' * (l'⁻¹ * l * l')) x = l (l' x) := by rw [hcomp, MulAut.mul_apply]
      rw [← h2]
      simp only [MulAut.mul_apply, map_mul, map_inv]
    rw [← heq]
    exact w1369_stableUnder_fixV L l' hl' _ hx'
  have hZX : Z ≤ X := by
    intro z hz
    refine ⟨hz.1, fun l hl => ?_⟩
    have h1 : l z = z := (mem_fixV.mp hz.2) l hl
    rw [h1, mul_inv_cancel]
    exact (fixV L).one_mem
  have hXI : X ≤ I := fun x hx => hx.1
  have hcommX : commSub X L ≤ Z := by
    have h1 : commSub X L ≤ X := commSub_le_of_invariant hXstab
    have h2 : commSub X L ≤ fixV L := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨l, hl, x, hx, rfl⟩
      exact hx.2 l hl
    exact (le_inf h1 h2).trans (inf_le_inf hXI le_rfl)
  rcases hirr X hXstab hZX hXI with hXZ | hXI'
  · exact (hXZ ▸ (show a ∈ X from ⟨ha, h⟩)).2
  · exfalso
    have hIZ : I = Z := by
      have h1 : commSub I L ≤ Z := hXI' ▸ hcommX
      rw [hIcomm] at h1
      exact le_antisymm h1 inf_le_left
    exact absurd hIZ.symm (ne_of_lt hIlt)

theorem move_rank (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} {I : Subgroup W} (S : Move136 Y t L I) :
    E3.mQuot I (I ⊓ fixV L) = 3 ∧ I ⊓ fixV (Subgroup.zpowers t) = I ⊓ fixV L ∧
      I ⊓ I.map t.toMonoidHom = I ⊓ fixV L ∧
      commSub ⊤ (Subgroup.zpowers t) ≤ I ⊔ I.map t.toMonoidHom := by
  obtain ⟨hIcomm, hIlt, hIstab, hZstab, hirr⟩ := S.hI
  let Z : Subgroup W := I ⊓ fixV L
  have hmQuot_upper : E3.mQuot I Z ≤ 3 :=
    (mQuot_le_rk_commSub_of_inf_map_le t inf_le_left
      (le_inf inf_le_left (move_inter hw2 S))).trans S.ctx.std.cost
  have hmQuot_lower : 3 ≤ E3.mQuot I Z := by
    have hStabL : StabPair L I Z := fun l hl => ⟨hIstab l hl, hZstab l hl⟩
    have hLq : CFSG.IsQuasisimple ↥L :=
      CFSG.Quasithin.B1Red.isQuasisimple_of_open S.ctx.comp.2.2
    have hLp : ⁅L, L⁆ = L := w1369_commutator_eq_self_of_isQuasisimple hLq
    have hperf : ⁅secSub I Z L, secSub I Z L⁆ = secSub I Z L := by
      rw [secSub_commutator hStabL hStabL, hLp]
    have hne : secSub I Z L ≠ ⊥ := by
      intro hbot
      have hle : commSub I L ≤ Z := by
        rw [commSub, Subgroup.closure_le]
        rintro _ ⟨l, hl, u, hu, rfl⟩
        exact (w1369_secSub_eq_bot_iff inf_le_left hStabL).mp hbot l hl u hu
      rw [hIcomm] at hle
      exact absurd (le_antisymm hle inf_le_left).symm (ne_of_lt hIlt)
    have hle3 : rk ↥(⊤ : Subgroup (Sect I Z)) ≤ 3 := by
      rw [← w1369_mQuot_eq_rk_sect I Z]
      exact hmQuot_upper
    have hrk3 : rk ↥(⊤ : Subgroup (Sect I Z)) = 3 :=
      (w16f_perfect_gl_three (W := Sect I Z) (sect_exp_two hw2 I Z) hle3
        (secSub I Z L) hperf hne).1
    rw [w1369_mQuot_eq_rk_sect I Z]
    exact le_of_eq hrk3.symm
  have hmQuot3 : E3.mQuot I Z = 3 := le_antisymm hmQuot_upper hmQuot_lower
  have hCt_le : I ⊓ fixV (Subgroup.zpowers t) ≤ Z := by
    intro u hu
    refine ⟨hu.1, ?_⟩
    have htu : t u = u := (mem_fixV.mp hu.2) t (Subgroup.mem_zpowers t)
    exact move_inter hw2 S ⟨hu.1, Subgroup.mem_map.mpr ⟨u, hu.1, htu⟩⟩
  have hCt_eq : I ⊓ fixV (Subgroup.zpowers t) = Z := by
    refine w1369_eq_of_le_of_mQuot_eq hw2 hCt_le inf_le_left ?_
    have h1 : E3.mQuot I (I ⊓ fixV (Subgroup.zpowers t)) ≤ 3 :=
      (w1369_mQuot_fixV_zpowers_le I t).trans S.ctx.std.cost
    have h2 : E3.mQuot I Z ≤ E3.mQuot I (I ⊓ fixV (Subgroup.zpowers t)) :=
      E3.mQuot_mono hCt_le
    omega
  have hCt_le_map : I ⊓ fixV (Subgroup.zpowers t) ≤ I ⊓ I.map t.toMonoidHom := by
    intro u hu
    refine ⟨hu.1, Subgroup.mem_map.mpr ⟨u, hu.1, ?_⟩⟩
    exact (mem_fixV.mp hu.2) t (Subgroup.mem_zpowers t)
  have hmap_eq : I ⊓ I.map t.toMonoidHom = Z :=
    le_antisymm (le_inf inf_le_left (move_inter hw2 S)) (hCt_eq ▸ hCt_le_map)
  have hjoin : commSub ⊤ (Subgroup.zpowers t) ≤ I ⊔ I.map t.toMonoidHom := by
    have himage_le : I.map (commHom t) ≤ I ⊔ I.map t.toMonoidHom := by
      rintro v ⟨u, hu, rfl⟩
      refine Subgroup.mul_mem _ ?_ ?_
      · exact Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩)
      · exact Subgroup.mem_sup_left (I.inv_mem hu)
    have hle : I.map (commHom t) ≤ commSub ⊤ (Subgroup.zpowers t) := by
      rw [commSub_zpowers_eq_map (W := ⊤) (fun _ _ w _ => trivial)]
      exact Subgroup.map_mono le_top
    have hrk_image : rk ↥(I.map (commHom t)) = 3 := by
      rw [← w1369_mQuot_fixV_zpowers_eq I t, hCt_eq, hmQuot3]
    have hrk_comm : rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 3 := by
      have h := rk_mono hle
      have hc := S.ctx.std.cost
      omega
    have hEq : I.map (commHom t) = commSub ⊤ (Subgroup.zpowers t) :=
      eq_of_le_of_rk_le hw2 hle (le_of_eq (hrk_comm.trans hrk_image.symm))
    rw [hEq] at himage_le
    exact himage_le
  exact ⟨hmQuot3, hCt_eq, hmap_eq, hjoin⟩

private theorem w1369_zpowers_mem_of_mem {U : Subgroup W} {t : MulAut W} (ht2 : t * t = 1)
    (ht : ∀ u ∈ U, t u ∈ U) : ∀ x ∈ Subgroup.zpowers t, ∀ u ∈ U, x u ∈ U := by
  intro x hx u hu
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have ht2z : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht2]
  rw [zpow_eq_zpow_emod n ht2z]
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · rw [h, zpow_zero]
    simpa using hu
  · rw [h, zpow_one]
    exact ht u hu

theorem move_W (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} {I : Subgroup W} (S : Move136 Y t L I) :
    Wd L = I ⊔ I.map t.toMonoidHom := by
  obtain ⟨-, -, hIstab, hZstab, hirr⟩ := S.hI
  obtain ⟨hItmem, hItt, hItstab⟩ := move_conj_irr S
  have hjoin : commSub ⊤ (Subgroup.zpowers t) ≤ I ⊔ I.map t.toMonoidHom :=
    (move_rank hw2 S).2.2.2
  refine le_antisymm ?_ ?_
  · have hUstab : StableUnder L (I ⊔ I.map t.toMonoidHom) :=
      w1369_stableUnder_sup hIstab hItstab
    have hUt : ∀ u ∈ I ⊔ I.map t.toMonoidHom, t u ∈ I ⊔ I.map t.toMonoidHom := by
      intro u hu
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hu
      rw [map_mul]
      refine Subgroup.mul_mem _ ?_ ?_
      · exact Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
      · obtain ⟨c, hc, hcb⟩ := Subgroup.mem_map.mp hb
        have htbc : t b = c := by
          rw [← hcb]
          have h := congrArg (fun g : MulAut W => g c) (w1369_mul_self S)
          simpa [MulAut.mul_apply] using h
        rw [htbc]
        exact Subgroup.mem_sup_left hc
    have hStabL : StabPair L ⊤ (I ⊔ I.map t.toMonoidHom) :=
      fun l hl => ⟨fun _ _ => trivial, hUstab l hl⟩
    have hStabT : StabPair (Subgroup.zpowers t) ⊤ (I ⊔ I.map t.toMonoidHom) :=
      fun x hx => ⟨fun _ _ => trivial, w1369_zpowers_mem_of_mem (w1369_mul_self S) hUt x hx⟩
    have hTbot : secSub ⊤ (I ⊔ I.map t.toMonoidHom) (Subgroup.zpowers t) = ⊥ :=
      (w1369_secSub_eq_bot_iff le_top hStabT).mpr fun x hx u _ =>
        hjoin (Subgroup.subset_closure ⟨x, hx, u, trivial, rfl⟩)
    have hLbot : secSub ⊤ (I ⊔ I.map t.toMonoidHom) L = ⊥ := by
      have h := secSub_commutator hStabL hStabT
      rw [S.ctx.Lt, hTbot, Subgroup.commutator_bot_right] at h
      exact h.symm
    have hpoint := (w1369_secSub_eq_bot_iff le_top hStabL).mp hLbot
    rw [Wd, commSub, Subgroup.closure_le]
    rintro _ ⟨l, hl, u, -, rfl⟩
    exact hpoint l hl u trivial
  · refine sup_le ?_ ?_
    · calc I = commSub I L := S.hI.1.symm
        _ ≤ commSub ⊤ L := commSub_mono le_top le_rfl
    · calc I.map t.toMonoidHom = commSub (I.map t.toMonoidHom) L := hItmem.1.symm
        _ ≤ commSub ⊤ L := commSub_mono le_top le_rfl

theorem move_C (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} {I : Subgroup W} (S : Move136 Y t L I) :
    Cd L = I ⊓ fixV L ∧ I.map t.toMonoidHom ⊓ fixV L = I ⊓ fixV L := by
  obtain ⟨-, -, hIstab, -, hirr⟩ := S.hI
  obtain ⟨hItmem, hItt, hItstab⟩ := move_conj_irr S
  have hW := move_W hw2 S
  obtain ⟨-, -, hmap_eq, hjoin⟩ := move_rank hw2 S
  have hsym : I.map t.toMonoidHom ⊓ fixV L = I ⊓ fixV L := by
    have h2 := (move_rank hw2 (move_symm S)).2.2.1
    rw [hItt] at h2
    rw [inf_comm (I.map t.toMonoidHom) I] at h2
    rw [← h2, hmap_eq]
  refine ⟨?_, hsym⟩
  have hCd : Cd L = (I ⊔ I.map t.toMonoidHom) ⊓ fixV L := by
    change commSub ⊤ L ⊓ fixV L = (I ⊔ I.map t.toMonoidHom) ⊓ fixV L
    rw [show commSub ⊤ L = I ⊔ I.map t.toMonoidHom from hW]
  rw [hCd]
  refine le_antisymm ?_ ?_
  · intro u hu
    obtain ⟨hu_sup, hufix⟩ := Subgroup.mem_inf.mp hu
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hu_sup
    have hZa : a ∈ I ⊓ fixV L := by
      refine ⟨ha, w1369_fix_mod_le S.hI ha (fun l hl => ?_)⟩
      have hla_Z : l a * a⁻¹ ∈ I ⊓ I.map t.toMonoidHom := by
        have h1 : l (a * b) * (a * b)⁻¹ = (l a * a⁻¹) * (l b * b⁻¹) := by
          rw [map_mul, mul_inv_rev]; ac_rfl
        have h2 : l (a * b) * (a * b)⁻¹ = 1 := by
          rw [hab, (mem_fixV.mp hufix) l hl, mul_inv_cancel]
        have hla_mem : l a * a⁻¹ ∈ I := I.mul_mem (hIstab l hl a ha) (I.inv_mem ha)
        have hlb_mem : l b * b⁻¹ ∈ I.map t.toMonoidHom :=
          (I.map t.toMonoidHom).mul_mem (hItstab l hl b hb) ((I.map t.toMonoidHom).inv_mem hb)
        have hla_eq : l a * a⁻¹ = (l b * b⁻¹)⁻¹ := by
          have h := h1
          rw [h2] at h
          exact mul_eq_one_iff_eq_inv.mp h.symm
        exact ⟨hla_mem, hla_eq ▸ (I.map t.toMonoidHom).inv_mem hlb_mem⟩
      rw [hmap_eq] at hla_Z
      exact hla_Z.2
    have hZb : b ∈ I ⊓ fixV L := by
      have hb_fix : b ∈ fixV L := by
        refine w1369_fix_mod_le hItmem hb (fun l hl => ?_)
        have h1 : l (a * b) * (a * b)⁻¹ = (l a * a⁻¹) * (l b * b⁻¹) := by
          rw [map_mul, mul_inv_rev]; ac_rfl
        have h2 : l (a * b) * (a * b)⁻¹ = 1 := by
          rw [hab, (mem_fixV.mp hufix) l hl, mul_inv_cancel]
        have hla_mem : l a * a⁻¹ ∈ I := I.mul_mem (hIstab l hl a ha) (I.inv_mem ha)
        have hlb_mem : l b * b⁻¹ ∈ I.map t.toMonoidHom :=
          (I.map t.toMonoidHom).mul_mem (hItstab l hl b hb) ((I.map t.toMonoidHom).inv_mem hb)
        have hla_eq : l a * a⁻¹ = (l b * b⁻¹)⁻¹ := by
          have h := h1
          rw [h2] at h
          exact mul_eq_one_iff_eq_inv.mp h.symm
        have hla_Z : l a * a⁻¹ ∈ I ⊓ I.map t.toMonoidHom :=
          ⟨hla_mem, hla_eq ▸ (I.map t.toMonoidHom).inv_mem hlb_mem⟩
        rw [hmap_eq] at hla_Z
        have hlb_eq : l b * b⁻¹ = (l a * a⁻¹)⁻¹ := by
          have h := h1
          rw [h2] at h
          exact mul_eq_one_iff_eq_inv.mp (by rw [mul_comm]; exact h.symm)
        rw [hlb_eq]
        exact (fixV L).inv_mem hla_Z.2
      have hbI : b ∈ I := by
        have hbZ : b ∈ I.map t.toMonoidHom ⊓ fixV L := ⟨hb, hb_fix⟩
        rw [hsym] at hbZ
        exact hbZ.1
      exact ⟨hbI, hb_fix⟩
    refine ⟨?_, hufix⟩
    rw [← hab]
    exact I.mul_mem hZa.1 hZb.1
  · intro u hu
    exact ⟨Subgroup.mem_sup_left hu.1, hu.2⟩

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
