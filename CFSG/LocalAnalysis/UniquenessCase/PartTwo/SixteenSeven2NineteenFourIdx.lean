module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg4Index

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W]

structure Four19 (E : Subgroup (MulAut W)) (𝒴 : Set (Subgroup W)) : Prop where
  sq : ∀ w : W, w ^ 2 = 1
  sq_E : ∀ e ∈ E, e * e = 1
  comm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a
  ncard : 𝒴.ncard = 4
  rk_eq : ∀ Y ∈ 𝒴, rk ↥Y = 2
  indep : sSupIndep 𝒴
  sup : sSup 𝒴 = ⊤
  perm : ∀ e ∈ E, ∀ Y ∈ 𝒴, Y.map e.toMonoidHom ∈ 𝒴

variable [Finite W]

theorem s16c167_four_faithful {E : Subgroup (MulAut W)} {𝒴 : Set (Subgroup W)}
    (F : Four19 E 𝒴) {e : MulAut W} (he : ∀ Y ∈ 𝒴, e ∈ centSub Y) : e = 1 := by
  have hle : sSup 𝒴 ≤ fixV (Subgroup.zpowers e) := by
    refine sSup_le fun Y hY => ?_
    intro y hy
    rw [mem_fixV_zpowers_iff_apply]
    exact (mem_centSub.mp (he Y hY)) y hy
  rw [F.sup] at hle
  ext w
  have hw : w ∈ fixV (Subgroup.zpowers e) := hle trivial
  simpa using (mem_fixV_zpowers_iff_apply.mp hw)

private theorem s16c167_four_mem_stabSub_of_map_eq {Y : Subgroup W} {g : MulAut W}
    (h : Y.map g.toMonoidHom = Y) : g ∈ stabSub Y := by
  rw [mem_stabSub]
  intro u
  constructor
  · intro hgu
    have hmem : g u ∈ Y.map g.toMonoidHom := by rw [h]; exact hgu
    rw [Subgroup.mem_map] at hmem
    obtain ⟨v, hv, hvu⟩ := hmem
    exact g.injective hvu ▸ hv
  · intro hu
    rw [← h]
    exact Subgroup.mem_map_of_mem _ hu

theorem s16c167_four_index_stab {E : Subgroup (MulAut W)} {𝒴 : Set (Subgroup W)}
    (F : Four19 E 𝒴) {Y : Subgroup W} (hY : Y ∈ 𝒴) :
    E3.mQuot E (E ⊓ stabSub Y) ≤ 2 := by
  classical
  have hE2 : IsPGroup 2 ↥E :=
    isPGroup_two_of_sq_eq_one fun e => Subtype.ext (by simpa [pow_two] using F.sq_E e.1 e.2)
  letI : MulAction ↥E ↥𝒴 :=
    { smul := fun e Y₀ => ⟨Y₀.1.map e.1.toMonoidHom, F.perm e.1 e.2 Y₀.1 Y₀.2⟩
      one_smul := fun Y₀ => by
        apply Subtype.ext
        change Y₀.1.map (MonoidHom.id W) = Y₀.1
        rw [Subgroup.map_id]
      mul_smul := fun e₁ e₂ Y₀ => by
        apply Subtype.ext
        show Y₀.1.map ((e₁ * e₂ : ↥E)).1.toMonoidHom =
          (Y₀.1.map e₂.1.toMonoidHom).map e₁.1.toMonoidHom
        rw [Subgroup.map_map]
        rfl }
  have hstab : (E ⊓ stabSub Y).subgroupOf E = MulAction.stabilizer ↥E (⟨Y, hY⟩ : ↥𝒴) := by
    ext e
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rintro ⟨-, he⟩
      rw [MulAction.mem_stabilizer_iff]
      exact Subtype.ext (map_eq_of_mem_stabSub he)
    · intro he
      rw [MulAction.mem_stabilizer_iff] at he
      exact ⟨e.2, s16c167_four_mem_stabSub_of_map_eq (congrArg Subtype.val he)⟩
  have hrel : (E ⊓ stabSub Y).relIndex E =
      (MulAction.orbit ↥E (⟨Y, hY⟩ : ↥𝒴)).ncard := by
    change ((E ⊓ stabSub Y).subgroupOf E).index =
      (MulAction.orbit ↥E (⟨Y, hY⟩ : ↥𝒴)).ncard
    rw [hstab, MulAction.index_stabilizer]
  have hle : (E ⊓ stabSub Y).relIndex E ≤ 2 ^ 2 := by
    rw [hrel]
    calc (MulAction.orbit ↥E (⟨Y, hY⟩ : ↥𝒴)).ncard ≤ Nat.card ↥𝒴 := Set.ncard_le_card _
      _ = 𝒴.ncard := Nat.card_coe_set_eq 𝒴
      _ = 4 := F.ncard
      _ = 2 ^ 2 := by norm_num
  have hpow : 2 ^ E3.mQuot E (E ⊓ stabSub Y) ≤ 2 ^ 2 := by
    rw [← E3.relIndex_eq_two_pow hE2 (E ⊓ stabSub Y)]
    exact hle
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow

theorem s16c167_four_index_ker {E : Subgroup (MulAut W)} {𝒴 : Set (Subgroup W)}
    (F : Four19 E 𝒴) {Y : Subgroup W} (hY : Y ∈ 𝒴) :
    E3.mQuot (E ⊓ stabSub Y) (E ⊓ centSub Y) ≤ 1 := by
  classical
  set A : Subgroup (MulAut W) := E ⊓ stabSub Y with hAdef
  have hA_le : A ≤ stabSub Y := by rw [hAdef]; exact inf_le_right
  have hAis : IsPGroup 2 ↥A := by
    refine isPGroup_two_of_sq_eq_one fun a => ?_
    apply Subtype.ext
    have haE : a.1 ∈ E := (show a.1 ∈ E ⊓ stabSub Y from a.2).1
    simpa [pow_two] using F.sq_E a.1 haE
  have hN_le_A : E ⊓ centSub Y ≤ A := by
    rw [hAdef]
    intro g hg
    exact ⟨hg.1, centSub_le_stabSub Y hg.2⟩
  have hN_eq : A ⊓ centSub Y = E ⊓ centSub Y := by
    rw [hAdef, inf_assoc, inf_eq_right.mpr (centSub_le_stabSub Y)]
  set c : ℕ := Nat.card ↥(E ⊓ centSub Y) with hc
  have hcardAut := card_autSub_mul (A := A) (U := Y) hA_le
  have hNcard : Nat.card A = 2 ^ E3.mQuot A (E ⊓ centSub Y) * c := by
    have h := E3.card_eq_two_pow_mul hAis hN_le_A
    simpa [c] using h
  have haut_sq : ∀ φ : ↥(autSub A Y), φ ^ 2 = 1 := by
    intro φ
    obtain ⟨g, hgA, hgφ⟩ := mem_autSub.mp φ.2
    apply Subtype.ext
    show φ.1 * φ.1 = 1
    have hgg : g * g = 1 := Subtype.ext (by
      show (g : MulAut W) * (g : MulAut W) = 1
      have hgE : (g : MulAut W) ∈ E := (show (g : MulAut W) ∈ E ⊓ stabSub Y from hgA).1
      exact F.sq_E (g : MulAut W) hgE)
    have hres : resHom Y g * resHom Y g = 1 := by
      rw [← map_mul, hgg, map_one]
    rw [← hgφ]
    exact hres
  have hcardAutAut : Nat.card ↥(autSub A Y) = 2 ^ rk ↥(autSub A Y) :=
    card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one haut_sq)
  have hYcard : Nat.card ↥Y = 4 := by
    rw [card_eq_two_pow F.sq Y, F.rk_eq Y hY]
    norm_num
  have hexpY : ∀ y : ↥Y, y ^ 2 = 1 :=
    fun y => Subtype.ext (by simpa using F.sq (y : W))
  have hdvd6 : Nat.card ↥(autSub A Y) ∣ 6 :=
    (Subgroup.card_subgroup_dvd_card (autSub A Y)).trans
      (s16c167_cfg4_card_aut_dvd hYcard hexpY)
  have hrk_le : rk ↥(autSub A Y) ≤ 1 := by
    have hpad6 : padicValNat 2 6 = 1 := by
      rw [show (6 : ℕ) = 2 ^ 1 * 3 by norm_num,
        padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow]
      have h3 : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
      rw [h3]
    calc rk ↥(autSub A Y) = padicValNat 2 (Nat.card ↥(autSub A Y)) := rfl
      _ ≤ padicValNat 2 6 := padicValNat_two_le_of_dvd (by norm_num) hdvd6
      _ = 1 := hpad6
  have haut_le : Nat.card ↥(autSub A Y) ≤ 2 := by
    rw [hcardAutAut]
    calc 2 ^ rk ↥(autSub A Y) ≤ 2 ^ 1 :=
          pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) hrk_le
      _ = 2 := by norm_num
  have hkey : Nat.card ↥(autSub A Y) * c = 2 ^ E3.mQuot A (E ⊓ centSub Y) * c := by
    rw [hN_eq] at hcardAut
    rw [hNcard] at hcardAut
    simpa [c] using hcardAut
  have hcpos : 0 < c := card_subgroup_pos (E ⊓ centSub Y)
  have hle : 2 ^ E3.mQuot A (E ⊓ centSub Y) * c ≤ 2 * c := by
    rw [← hkey]
    exact Nat.mul_le_mul_right c haut_le
  have h2m : 2 ^ E3.mQuot A (E ⊓ centSub Y) ≤ 2 :=
    Nat.le_of_mul_le_mul_right hle hcpos
  have hpow : 2 ^ E3.mQuot A (E ⊓ centSub Y) ≤ 2 ^ 1 := by simpa using h2m
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
