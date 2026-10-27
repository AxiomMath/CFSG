module

public import CFSG.Sporadic.Recognition.LyonsModelPerm
public import CFSG.Sporadic.Recognition.LyonsModelGroup
public import CFSG.Sporadic.Recognition.LyonsAmalgamExtOutMcL

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.Ly0

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Recognition.McLMultiplier
  CFSG.LieType.Multipliers Equiv Subgroup

noncomputable abbrev B0 : Subgroup (Perm (Fin deg)) := closure {cG, dG}

noncomputable abbrev M0 : Subgroup (Perm (Fin deg)) := closure {AG, BG}

theorem cG_mem : cG ∈ B0 := subset_closure (by simp)

theorem dG_mem : dG ∈ B0 := subset_closure (by simp)

theorem wG_mem (S : Subgroup (Perm (Fin deg))) (gs : ℕ → Perm (Fin deg)) (m : ℕ)
    (hgs : ∀ k < m, gs k ∈ S) (w : List ℤ) (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ m) :
    wG gs w ∈ S := by
  induction w with
  | nil => simp
  | cons l w ih =>
    rw [wG_cons]
    have hl := hw l (by simp)
    refine mul_mem ?_ (ih fun l' hl' => hw l' (by simp [hl']))
    by_cases hp : 0 < l
    · rw [letterG_pos gs hp]
      exact hgs _ (by omega)
    · rw [letterG_neg_of gs hp]
      exact inv_mem (hgs _ (by omega))

theorem gens0_mem : ∀ k < 2, gens0 k ∈ B0 := by
  intro k hk
  interval_cases k
  · rw [gens0_zero]; exact cG_mem
  · rw [gens0_one]; exact dG_mem

theorem AG_mem : AG ∈ B0 := by
  rw [AG_def]; exact wG_mem B0 gens0 2 gens0_mem wordA (decodeWord_mem _)

theorem BG_mem : BG ∈ B0 := by
  rw [BG_def]; exact wG_mem B0 gens0 2 gens0_mem wordB (decodeWord_mem _)

theorem gens1_mem_B0 : ∀ k < 2, gens1 k ∈ B0 := by
  intro k hk
  interval_cases k
  · rw [gens1_zero]; exact AG_mem
  · rw [gens1_one]; exact BG_mem

theorem yG_mem_B0 : ∀ k < 6, yG k ∈ B0 := by
  intro k hk
  rw [yG_def]
  refine wG_mem B0 gens1 2 gens1_mem_B0 _ ?_
  intro l hl
  interval_cases k <;> simp [mclGenWord] at hl <;> omega

theorem R0G_mem_B0 : R0G ∈ B0 := by
  rw [R0G_def]
  exact wG_mem B0 yG 6 yG_mem_B0 _ fun l hl => by
    obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
    exact letterZ_mem l'

theorem xG_mem_B0 : xG ∈ B0 := by
  rw [xG_def]; exact inv_mem R0G_mem_B0

theorem y0G_mem_B0 : y0G ∈ B0 := by
  rw [y0G_def]; exact wG_mem B0 gens0 2 gens0_mem wordY (decodeWord_mem _)

theorem fG_mem_B0 : fG ∈ B0 := by
  rw [fG_def]; exact wG_mem B0 gens0 2 gens0_mem wordF (decodeWord_mem _)

theorem nG_mem_B0 : nG ∈ B0 := by
  rw [nG_def]; exact wG_mem B0 gens0 2 gens0_mem wordN (decodeWord_mem _)

theorem M0_le_B0 : M0 ≤ B0 := by
  refine (closure_le B0).2 fun g hg => ?_
  rcases hg with hg | hg
  · rw [hg]; exact AG_mem
  · rw [Set.mem_singleton_iff.1 hg]; exact BG_mem

theorem AG_mem_M0 : AG ∈ M0 := subset_closure (by simp)

theorem BG_mem_M0 : BG ∈ M0 := subset_closure (by simp)

theorem gens1_mem_M0 : ∀ k < 2, gens1 k ∈ M0 := by
  intro k hk
  interval_cases k
  · rw [gens1_zero]; exact AG_mem_M0
  · rw [gens1_one]; exact BG_mem_M0

theorem yG_mem_M0 : ∀ k < 6, yG k ∈ M0 := by
  intro k hk
  rw [yG_def]
  refine wG_mem M0 gens1 2 gens1_mem_M0 _ ?_
  intro l hl
  interval_cases k <;> simp [mclGenWord] at hl <;> omega

theorem dG_mem_M0 (h : tabCheck = true) (hs : structCheck = true) : dG ∈ M0 := by
  rw [dG_eq h hs]
  exact wG_mem M0 gens1 2 gens1_mem_M0 _ (decodeWord_mem _)

section Cover

variable (h : tabCheck = true) (hc : coverCheck = true)

theorem range_coverHom_eq_closure :
    (coverHom h hc).range = closure (Set.range fun k : Fin 6 => yG k.val) := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp]
  have : (⇑(coverHom h hc) ∘ PresentedGroup.of) = fun k : Fin 6 => yG k.val :=
    funext (coverHom_of h hc)
  rw [this]

theorem xG_eq_coverHom : xG = (coverHom h hc z0)⁻¹ := by
  rw [coverHom_z0 h hc, xG_def]

variable {h hc}

theorem xG_mem_closure_yG : xG ∈ closure (Set.range fun k : Fin 6 => yG k.val) := by
  rw [xG_def, R0G_def]
  exact inv_mem (wG_mem _ yG 6 (fun k hk => subset_closure (Set.mem_range.2 ⟨⟨k, hk⟩, rfl⟩)) _
    fun l hl => by
      obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
      exact letterZ_mem l')

theorem range_coverHom_eq (hs : structCheck = true) : (coverHom h hc).range = M0 := by
  rw [range_coverHom_eq_closure h hc]
  refine le_antisymm ((closure_le M0).2 ?_) ((closure_le _).2 fun g hg => ?_)
  · rintro _ ⟨k, rfl⟩
    exact yG_mem_M0 k.val k.isLt
  · rcases hg with hg | hg
    · rw [hg, ← yG_five h hs]
      exact subset_closure (Set.mem_range.2 ⟨5, rfl⟩)
    · rw [Set.mem_singleton_iff.1 hg, BG_eq h hs]
      refine mul_mem ?_ (mul_mem xG_mem_closure_yG xG_mem_closure_yG)
      exact wG_mem _ yG 6 (fun k hk => subset_closure (Set.mem_range.2 ⟨⟨k, hk⟩, rfl⟩)) _
        fun l hl => by
          obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
          exact letterZ_mem l'

end Cover

section Injective


theorem coverMap_ker_eq_center :
    (coverMap McLMultiplier.isPresentation_mclGen_of_certificate
      McLMultiplier.lift_mclCommW_of_certificate).ker =
      Subgroup.center MclCover :=
  ker_eq_center_of_central_ker _
    (coverMap_surjective _ _) (coverMap_ker_le_center _ _)
    (center_eq_bot_of_equiv_mcl CFSG.Sporadic.McL.mclEquivJ.symm)

theorem coverHom_injective (h : tabCheck = true) (hc : coverCheck = true)
    (hs : structCheck = true) : Function.Injective (coverHom h hc) := by
  have hP := McLMultiplier.isPresentation_mclGen_of_certificate
  have hwg := McLMultiplier.lift_mclCommW_of_certificate
  have := isPerfect_mclCover
  have : IsSimpleGroup CFSG.Sporadic.McL.J := CFSG.Sporadic.McL.isSimpleGroup_J
  refine injective_of_ne_one_central (coverMap hP hwg) (coverMap_surjective hP hwg)
    (coverMap_ker_le_center hP hwg) ?_ (coverHom h hc) (z := z0) ?_ ?_
  · rw [coverMap_ker_eq_center]
    exact card_center_mclCover
  · rw [MonoidHom.mem_ker]
    rw [z0_def, coverMap_mk]
    exact hP.lift_eq_one (List.mem_map_of_mem (f := FreeGroup.mk) mclR0_mem)
  · rw [coverHom_z0 h hc]
    exact R0G_ne_one h hs

theorem z0_ne_one (h : tabCheck = true) (hc : coverCheck = true) (hs : structCheck = true) :
    z0 ≠ 1 := by
  intro h1
  apply R0G_ne_one h hs
  rw [← coverHom_z0 h hc, h1, map_one]

theorem center_mclCover_eq (h : tabCheck = true) (hc : coverCheck = true)
    (hs : structCheck = true) : Subgroup.center MclCover = zpowers z0 := by
  have hcard := card_center_mclCover
  have hz : (⟨z0, z0_mem_center⟩ : Subgroup.center MclCover) ≠ 1 := fun h1 =>
    z0_ne_one h hc hs (congrArg Subtype.val h1)
  have hfin : Finite (Subgroup.center MclCover) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hdvd : orderOf (⟨z0, z0_mem_center⟩ : Subgroup.center MclCover) ∣ 3 := by
    rw [← hcard]; exact orderOf_dvd_natCard _
  have hord : orderOf z0 = 3 := by
    have h1 : orderOf z0 = orderOf (⟨z0, z0_mem_center⟩ : Subgroup.center MclCover) :=
      Subgroup.orderOf_coe (⟨z0, z0_mem_center⟩ : Subgroup.center MclCover)
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h2 | h2
    · exact absurd (orderOf_eq_one_iff.1 h2) hz
    · rw [h1, h2]
  symm
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [zpowers_le]; exact z0_mem_center
  · rw [hcard, Nat.card_zpowers, hord]


theorem card_mclCover : Nat.card MclCover = 2694384000 := by
  have hP := McLMultiplier.isPresentation_mclGen_of_certificate
  have hwg := McLMultiplier.lift_mclCommW_of_certificate
  have hc := card_presentedCover hP McLMultiplier.mclCommW_mem_commutator hwg
  rw [CFSG.Sporadic.McL.card_J] at hc
  rw [hc, McLMultiplier.card_griessHopfMultiplier_J_of_certificate]

end Injective

@[expose] noncomputable def cB : B0 := ⟨cG, cG_mem⟩

@[expose] noncomputable def dB : B0 := ⟨dG, dG_mem⟩

@[expose] noncomputable def xB : B0 := ⟨xG, xG_mem_B0⟩

@[expose] noncomputable def yB : B0 := ⟨y0G, y0G_mem_B0⟩

noncomputable abbrev K0 : Subgroup B0 := M0.subgroupOf B0

theorem mem_K0 {g : B0} : g ∈ K0 ↔ (g : Perm (Fin deg)) ∈ M0 := Iff.rfl

theorem closure_cB_dB : closure ({cB, dB} : Set B0) = ⊤ := by
  have h := Subgroup.closure_closure_coe_preimage (k := ({cG, dG} : Set (Perm (Fin deg))))
  convert h using 2
  ext x
  simp [cB, dB, Subtype.ext_iff]

theorem conj_M0 (h : tabCheck = true) (hs : structCheck = true) :
    ∀ k ∈ M0, cG * k * cG⁻¹ ∈ M0 := by
  intro k hk
  induction hk using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with hg | hg
    · rw [hg, mul_assoc, cAc_eq h hs]
      exact wG_mem M0 gens1 2 gens1_mem_M0 _ (decodeWord_mem _)
    · rw [Set.mem_singleton_iff.1 hg, mul_assoc, cBc_eq h hs]
      exact wG_mem M0 gens1 2 gens1_mem_M0 _ (decodeWord_mem _)
  | one => simp
  | mul a b _ _ ha hb =>
    have : cG * (a * b) * cG⁻¹ = (cG * a * cG⁻¹) * (cG * b * cG⁻¹) := by group
    rw [this]
    exact mul_mem ha hb
  | inv a _ ha =>
    have : cG * a⁻¹ * cG⁻¹ = (cG * a * cG⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem ha

theorem K0_normal_index_le_two (h : tabCheck = true) (hs : structCheck = true) :
    K0.Normal ∧ K0.index ≤ 2 := by
  refine normal_and_index_le_two_of_closure_pair (c := cB) (d := dB) closure_cB_dB K0 ?_ ?_ ?_
  · apply Subtype.ext
    simp [cB, pow_two, cG_sq h hs]
  · exact Subgroup.mem_subgroupOf.mpr (dG_mem_M0 h hs)
  · intro k hk
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      show (cB : Perm (Fin deg)) = cG from rfl]
    exact conj_M0 h hs _ (Subgroup.mem_subgroupOf.mp hk)

theorem coe_xB : (xB : Perm (Fin deg)) = xG := rfl

theorem coe_cB : (cB : Perm (Fin deg)) = cG := rfl

theorem xB_pow_three (h : tabCheck = true) (hs : structCheck = true) : xB ^ 3 = 1 := by
  apply Subtype.ext
  have h1 : xG ^ 3 = 1 := by rw [xG_def, inv_pow, R0G_pow_three h hs, inv_one]
  rw [Subgroup.coe_pow, coe_xB, h1]
  rfl

theorem xB_ne_one (h : tabCheck = true) (hs : structCheck = true) : xB ≠ 1 := by
  intro h1
  apply R0G_ne_one h hs
  have h2 : xG = 1 := congrArg Subtype.val h1
  rw [← inv_inv R0G]
  rw [xG_def] at h2
  rw [h2, inv_one]

theorem orderOf_xB (h : tabCheck = true) (hs : structCheck = true) : orderOf xB = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (xB_pow_three h hs) (xB_ne_one h hs)

theorem cB_xB (h : tabCheck = true) (hs : structCheck = true) : cB * xB * cB⁻¹ = xB⁻¹ := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, coe_xB, coe_cB,
    mul_assoc]
  exact cG_xG h hs

theorem cB_xB_ne (h : tabCheck = true) (hs : structCheck = true) : cB * xB ≠ xB * cB := by
  intro hcomm
  have h2 : cB * xB * cB⁻¹ = xB := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hcomm
  rw [cB_xB h hs] at h2
  have h3 : xB * xB = 1 := by
    calc xB * xB = xB * xB⁻¹ := by rw [h2]
      _ = 1 := mul_inv_cancel xB
  have h4 : xB ^ 2 = 1 := by rw [pow_two]; exact h3
  have h5 : 3 ∣ 2 := (orderOf_xB h hs) ▸ orderOf_dvd_of_pow_eq_one h4
  omega

theorem cB_not_mem_K0 (h : tabCheck = true) (hs : structCheck = true)
    (hK : K0 ≤ centralizer {xB}) : cB ∉ K0 := fun hc =>
  cB_xB_ne h hs (Subgroup.mem_centralizer_iff.1 (hK hc) xB (Set.mem_singleton xB)).symm

section Structure

theorem coverHom_comm_xG (h : tabCheck = true) (hc : coverCheck = true) (p : MclCover) :
    coverHom h hc p * xG = xG * coverHom h hc p := by
  have hcomm : Commute p z0 := Subgroup.mem_center_iff.1 z0_mem_center p
  rw [xG_eq_coverHom h hc, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg (coverHom h hc) hcomm.inv_right.eq

variable (h : tabCheck = true) (hc : coverCheck = true) (hs : structCheck = true)
include h hc hs

theorem K0_le_centralizer : K0 ≤ centralizer ({xB} : Set B0) := by
  intro k hk
  have hk' : (k : Perm (Fin deg)) ∈ (coverHom h hc).range := by
    rw [range_coverHom_eq (h := h) (hc := hc) hs]; exact hk
  obtain ⟨p, hp⟩ := hk'
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff.1 hy]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hp, coe_xB]
  exact (coverHom_comm_xG h hc p).symm

theorem K0_index_two : K0.index = 2 := by
  obtain ⟨-, hle⟩ := K0_normal_index_le_two h hs
  have hne : K0.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hne1 : K0.index ≠ 1 := by
    intro h1
    rw [Subgroup.index_eq_one] at h1
    exact cB_not_mem_K0 h hs (K0_le_centralizer h hc hs) (h1 ▸ Subgroup.mem_top cB)
  omega


noncomputable def K0EquivCover : K0 ≃* MclCover :=
  (Subgroup.subgroupOfEquivOfLe M0_le_B0).trans
    ((MulEquiv.subgroupCongr (range_coverHom_eq (h := h) (hc := hc) hs).symm).trans
      (MonoidHom.ofInjective (coverHom_injective h hc hs)).symm)

theorem card_K0 : Nat.card K0 = 2694384000 := by
  rw [Nat.card_congr (K0EquivCover h hc hs).toEquiv]
  exact card_mclCover

theorem card_B0 : Nat.card B0 = 5388768000 := by
  have := Subgroup.card_mul_index K0
  rw [card_K0 h hc hs, K0_index_two h hc hs] at this
  omega

theorem isPerfect_K0 : Group.IsPerfect K0 := by
  have := isPerfect_mclCover
  exact Group.IsPerfect.ofSurjective (f := (K0EquivCover h hc hs).symm.toMonoidHom)
    (K0EquivCover h hc hs).symm.surjective

theorem K0_center : ∀ z ∈ K0, (∀ k ∈ K0, k * z = z * k) → z ∈ zpowers xB := by
  intro z hz hzc
  have hz' : (z : Perm (Fin deg)) ∈ (coverHom h hc).range := by
    rw [range_coverHom_eq (h := h) (hc := hc) hs]; exact hz
  obtain ⟨p, hp⟩ := hz'
  have hpc : p ∈ Subgroup.center MclCover := by
    rw [Subgroup.mem_center_iff]
    intro q
    apply coverHom_injective h hc hs
    have hq : (coverHom h hc q) ∈ M0 := by
      rw [← range_coverHom_eq (h := h) (hc := hc) hs]; exact ⟨q, rfl⟩
    have := hzc ⟨coverHom h hc q, M0_le_B0 hq⟩ hq
    have := congrArg Subtype.val this
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at this
    simpa [map_mul, hp] using this
  rw [center_mclCover_eq h hc hs] at hpc
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hpc
  refine Subgroup.mem_zpowers_iff.2 ⟨-n, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_zpow, coe_xB, xG_eq_coverHom h hc, ← hp, ← hn, map_zpow, inv_zpow', neg_neg]

theorem K0_centralizer_and_inv :
    K0 = centralizer ({xB} : Set B0) ∧ ∀ b : B0, b ∉ K0 → b * xB * b⁻¹ = xB⁻¹ := by
  refine centralizer_eq_and_inv_of_index_two K0 xB (K0_index_two h hc hs) (orderOf_xB h hs) ?_
    (K0_center h hc hs) ⟨cB, fun hcomm => cB_xB_ne h hs hcomm⟩
  intro k hk
  exact (Subgroup.mem_centralizer_iff.1 (K0_le_centralizer h hc hs hk) xB
    (Set.mem_singleton xB)).symm

end Structure

theorem w0G_mem_B0 : w0G ∈ B0 := by
  rw [w0G_def]; exact wG_mem B0 gens0 2 gens0_mem wordW fun l hl => mem_wordW hl

theorem t0G_mem_B0 : t0G ∈ B0 := by
  rw [t0G_def]; exact wG_mem B0 gens0 2 gens0_mem wordT0 (decodeWord_mem _)

theorem gG_mem_B0 : gG ∈ B0 := by
  rw [gG_def]; exact wG_mem B0 gens0 2 gens0_mem wordGg (decodeWord_mem _)

theorem uG_mem_B0 (j : ℕ) : uG j ∈ B0 := by
  rw [uG_def]
  by_cases hj : j < 4
  · exact wG_mem B0 gens0 2 gens0_mem _ (uWords_mem j hj)
  · have : uWords.getD j [] = [] := by simp [uWords, hj]
    rw [this, wG_nil]
    exact one_mem _

@[expose] noncomputable def wB : B0 := ⟨w0G, w0G_mem_B0⟩

@[expose] noncomputable def tB : B0 := ⟨t0G, t0G_mem_B0⟩

@[expose] noncomputable def fB : B0 := ⟨fG, fG_mem_B0⟩

@[expose] noncomputable def nB : B0 := ⟨nG, nG_mem_B0⟩

@[expose] noncomputable def gB : B0 := ⟨gG, gG_mem_B0⟩

@[expose] noncomputable def uB (j : ℕ) : B0 := ⟨uG j, uG_mem_B0 j⟩

theorem coe_yB : (yB : Perm (Fin deg)) = y0G := rfl

theorem coe_wB : (wB : Perm (Fin deg)) = w0G := rfl

theorem coe_fB : (fB : Perm (Fin deg)) = fG := rfl

theorem coe_nB : (nB : Perm (Fin deg)) = nG := rfl

theorem coe_gB : (gB : Perm (Fin deg)) = gG := rfl

theorem coe_uB (j : ℕ) : (uB j : Perm (Fin deg)) = uG j := rfl

theorem coe_tB : (tB : Perm (Fin deg)) = t0G := rfl

section Mark

variable (h : tabCheck = true) (hs : structCheck = true) (hm : markCheck = true)
include h hs hm

theorem tB_mul_self : tB * tB = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_tB, Subgroup.coe_one]
  exact (mark_facts h hs hm).1

theorem tB_ne_one : tB ≠ 1 := by
  intro h1
  apply (mark_facts h hs hm).2.1
  have := congrArg Subtype.val h1
  rwa [coe_tB, Subgroup.coe_one] at this

theorem tB_comm_xB : tB * xB = xB * tB := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_tB, coe_xB]
  exact (mark_facts h hs hm).2.2.1

theorem tB_comm_yB : tB * yB = yB * tB := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_tB, coe_yB]
  exact (mark_facts h hs hm).2.2.2.1

theorem tB_comm_wB : tB * wB = wB * tB := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_tB, coe_wB]
  exact (mark_facts h hs hm).2.2.2.2

end Mark

noncomputable abbrev Y0 : Subgroup B0 := normalizer (zpowers yB : Set B0)

noncomputable abbrev A30 : Subgroup B0 := closure ({xB, yB, wB} : Set B0)

noncomputable abbrev Tx : Subgroup B0 := normalizer (A30 : Set B0)

noncomputable abbrev Txy : Subgroup B0 :=
  normalizer (zpowers xB : Set B0) ⊓ normalizer (zpowers yB : Set B0) ⊓
    normalizer (zpowers wB : Set B0)

noncomputable abbrev Dp : Subgroup B0 := centralizer ({tB} : Set B0)

noncomputable abbrev UY : Subgroup B0 :=
  (closure (Set.range fun j : Fin 4 => uG j.val)).subgroupOf B0

end CFSG.Sporadic.Recognition.LyonsSims.Ly0
