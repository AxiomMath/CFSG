module

public import CFSG.Quasithin.Background.E3Defs
import CFSG.GroupTheory.CoprimeHyperplaneCentralizer
import CFSG.Quasithin.Background.OddCoprimeFixV
import CFSG.Quasithin.Background.CommVBasics

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

variable {W : Type*} [CommGroup W] [Finite W]

theorem s16c11_inf_centSub_fixV_eq_bot (hW : ∀ w : W, w ^ 2 = 1) {P S : Subgroup (MulAut W)}
    (hP : ¬ 2 ∣ Nat.card P) (hS : IsPGroup 2 S)
    (hSP : S ≤ normalizer (P : Set (MulAut W))) :
    P ⊓ centSub (fixV S) = ⊥ := by
  classical
  set F : Subgroup (MulAut W) := P ⊓ centSub (fixV S) with hFdef
  have hFP : F ≤ P := inf_le_left
  have hFodd : Odd (Nat.card F) :=
    Nat.not_even_iff_odd.mp fun he =>
      hP (dvd_trans (even_iff_two_dvd.mp he) (Subgroup.card_dvd_of_le hFP))
  have hconj : ∀ s ∈ S, ∀ f, f ∈ F → s * f * s⁻¹ ∈ F := by
    intro s hs f hf
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hSP hs) f).mp hf.1, mem_centSub.mpr ?_⟩
    intro u hu
    show (s * f * s⁻¹) u = u
    rw [MulAut.mul_apply, MulAut.mul_apply, hu s⁻¹ (S.inv_mem hs),
      mem_centSub.mp hf.2 u hu, hu s hs]
  have hSF : S ≤ normalizer (F : Set (MulAut W)) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro f
    exact ⟨fun hf => hconj s hs f hf, fun hf => by
      have h := hconj s⁻¹ (S.inv_mem hs) (s * f * s⁻¹) hf
      rw [inv_inv] at h
      rwa [show s⁻¹ * (s * f * s⁻¹) * s = f by group] at h⟩
  have hRbot : commV F = ⊥ := by
    by_contra hRne
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : MulAction S ↥(commV F) :=
      { smul := fun s r => ⟨(s : MulAut W) (r : W),
          commV_apply_mem_of_normalizes (Y := F) (c := (s : MulAut W))
            (fun f hf => hconj s s.2 f hf) r.2⟩
        one_smul := fun _ => rfl
        mul_smul := fun _ _ _ => rfl }
    have hR2 : IsPGroup 2 ↥(commV F) := fun r => ⟨1, by
      apply Subtype.ext
      simpa [sq] using hW (r : W)⟩
    have hdvd : 2 ∣ Nat.card ↥(commV F) :=
      hR2.card_eq_or_dvd.resolve_left fun h => hRne (Subgroup.card_eq_one.1 h)
    have h1 : (1 : ↥(commV F)) ∈ MulAction.fixedPoints S ↥(commV F) :=
      fun s => Subtype.ext (map_one (s : MulAut W))
    obtain ⟨b, hb, hne⟩ :=
      hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥(commV F) hdvd h1
    have hbS : ∀ s ∈ S, (s : MulAut W) (b : W) = (b : W) :=
      fun s hs => congrArg Subtype.val ((MulAction.mem_fixedPoints.mp hb) ⟨s, hs⟩)
    have hbfixF : (b : W) ∈ fixV F := by
      rw [mem_fixV]
      intro f hf
      exact mem_centSub.mp hf.2 (b : W) (mem_fixV.mpr hbS)
    have hmem : (b : W) ∈ (⊥ : Subgroup W) := by
      rw [← commV_inf_fixV_eq_bot_of_odd_card hW F hFodd]
      exact ⟨b.2, hbfixF⟩
    exact hne (Subtype.ext (Subgroup.mem_bot.mp hmem)).symm
  rw [eq_bot_iff]
  intro f hf
  rw [Subgroup.mem_bot]
  ext w
  have hmem : f w * w⁻¹ ∈ commV F := Subgroup.subset_closure ⟨f, hf, w, rfl⟩
  rw [hRbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  simpa using hmem

theorem s16c11_le_centralizer_of_mem_aSet_two (hW : ∀ w : W, w ^ 2 = 1)
    {X A Y : Subgroup (MulAut W)} (hA : A ∈ E3.aSet 2 X) (hY : ¬ 2 ∣ Nat.card Y)
    (hAY : A ≤ normalizer (Y : Set (MulAut W))) :
    A ≤ centralizer (Y : Set (MulAut W)) := by
  classical
  obtain ⟨hAX, hAne, hAab, hAfix⟩ := hA
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 A := fun a => ⟨1, by
    apply Subtype.ext
    simpa [sq] using hAab.2 a.1 a.2⟩
  have hcardA : Nat.card A = 2 ^ E3.mQuot A ⊥ := by
    have h := E3.card_eq_two_pow_mul (V := A) (U := (⊥ : Subgroup (MulAut W))) hA2 bot_le
    simpa using h
  have hmq : 2 ≤ E3.mQuot A ⊥ := by
    by_contra hlt
    have h01 : E3.mQuot A ⊥ = 0 ∨ E3.mQuot A ⊥ = 1 := by omega
    rcases h01 with h0 | h1
    · have hc : Nat.card A = 1 := by rw [hcardA, h0]; norm_num
      exact hAne (Subgroup.card_eq_one.1 hc)
    · have hfix : fixV (⊥ : Subgroup (MulAut W)) = fixV A :=
        hAfix ⊥ bot_le (by rw [h1]; norm_num)
      have htop : fixV A = ⊤ := by
        rw [← hfix]
        ext v
        simp [mem_fixV]
      have hbot : A = ⊥ := by
        rw [eq_bot_iff]
        intro a ha
        rw [Subgroup.mem_bot]
        ext v
        have hv : v ∈ fixV A := by rw [htop]; trivial
        simpa using (mem_fixV.mp hv) a ha
      exact hAne hbot
  have hA4 : 4 ≤ Nat.card A := by
    rw [hcardA]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ E3.mQuot A ⊥ := Nat.pow_le_pow_right (by norm_num) hmq
  by_contra hnot
  have hEab : CFSG.Open.IsElemAbelian 2 A :=
    ⟨IsMulCommutative.of_comm (fun a b => Subtype.ext (hAab.1 a a.2 b b.2)),
      fun a ha => hAab.2 a ha⟩
  have hEcard : 2 ^ 2 ≤ Nat.card A := by norm_num; exact hA4
  obtain ⟨D, hDA, hDcard, hDnot⟩ :=
    CFSG.GroupTheory.exists_hyperplane_not_le_centralizer_inf_centralizer
      (r := 2) hEab hEcard hAY hY hnot
  have hrel : D.relIndex A = 2 := by
    have h := Subgroup.relIndex_mul_card (H := D) (K := A)
    rw [inf_eq_left.2 hDA, ← hDcard, mul_comm (Nat.card D) 2] at h
    exact Nat.mul_right_cancel Nat.card_pos h
  have hmqD : E3.mQuot A D < 2 := by
    have h1 : E3.mQuot A D = 1 := by
      unfold E3.mQuot
      rw [hrel]
      exact padicValNat_self
    omega
  have hfixD : fixV D = fixV A := hAfix D hDA hmqD
  have hD2 : IsPGroup 2 D := fun d => ⟨1, by
    apply Subtype.ext
    simpa [sq] using hAab.2 d.1 (hDA d.2)⟩
  have hDY : D ≤ Subgroup.normalizer (Y : Set (MulAut W)) := fun d hd => hAY (hDA hd)
  obtain ⟨b, hbA, hbD, hcover⟩ :=
    Subgroup.relIndex_eq_two_iff_exists_notMem_and'.mp hrel
  have hAle : A ≤ Subgroup.centralizer
      ((Y ⊓ Subgroup.centralizer (D : Set (MulAut W)) : Subgroup (MulAut W)) :
        Set (MulAut W)) := by
    rw [Subgroup.le_centralizer_iff]
    intro y hy
    have hyY : y ∈ Y := hy.1
    have hyD : y ∈ Subgroup.centralizer (D : Set (MulAut W)) := hy.2
    have hbA' : b⁻¹ ∈ A := A.inv_mem hbA
    have hyb : y * b = b * y := by
      have hcY : y⁻¹ * (b⁻¹ * y * b) ∈ Y := by
        refine Y.mul_mem (Y.inv_mem hyY) ?_
        have hbn : b⁻¹ ∈ Subgroup.normalizer (Y : Set (MulAut W)) := hAY hbA'
        simpa using (Subgroup.mem_normalizer_iff.mp hbn y).mp hyY
      have hcC : y⁻¹ * (b⁻¹ * y * b) ∈ centSub (fixV D) := by
        rw [mem_centSub]
        intro w hw
        have hbw : b w = w := by
          have hwA : w ∈ fixV A := by rw [← hfixD]; exact hw
          exact (mem_fixV.mp hwA) b hbA
        have hbiw : b⁻¹ (y w) = y w := by
          have hywA : y w ∈ fixV A := by
            rw [← hfixD, mem_fixV]
            intro d hd
            have hdy : d * y = y * d := Subgroup.mem_centralizer_iff.mp hyD d hd
            calc d (y w) = (d * y) w := rfl
              _ = (y * d) w := by rw [hdy]
              _ = y (d w) := rfl
              _ = y w := by rw [mem_fixV.mp hw d hd]
          exact (mem_fixV.mp hywA) b⁻¹ hbA'
        show (y⁻¹ * (b⁻¹ * y * b)) w = w
        rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hbw, hbiw,
          MulAut.inv_apply_self]
      have hbot := s16c11_inf_centSub_fixV_eq_bot hW (P := Y) (S := D) hY hD2 hDY
      have hmem : y⁻¹ * (b⁻¹ * y * b) ∈ (⊥ : Subgroup (MulAut W)) := by
        rw [← hbot]
        exact ⟨hcY, hcC⟩
      have hc1 : y⁻¹ * (b⁻¹ * y * b) = 1 := Subgroup.mem_bot.mp hmem
      have h2 : y = b⁻¹ * y * b := inv_mul_eq_one.mp hc1
      calc y * b = b * (b⁻¹ * y * b) := by group
        _ = b * y := by rw [← h2]
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rcases hcover a ha with hba | haD
    · have h1 : y * (b * a) = (b * a) * y :=
        (Subgroup.mem_centralizer_iff.mp hyD (b * a) hba).symm
      have h3 : y * a = a * y := by
        have h4 : b * (y * a) = b * (a * y) := by
          calc b * (y * a) = (b * y) * a := by group
            _ = (y * b) * a := by rw [hyb]
            _ = y * (b * a) := by group
            _ = (b * a) * y := h1
            _ = b * (a * y) := by group
        exact mul_left_cancel h4
      exact h3.symm
    · exact Subgroup.mem_centralizer_iff.mp hyD a haD
  exact hDnot hAle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
