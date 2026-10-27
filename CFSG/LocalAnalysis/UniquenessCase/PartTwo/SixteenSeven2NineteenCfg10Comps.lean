module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenCfg10Ker
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenCfg10E9

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {X Fs : Subgroup (MulAut W)} {I₁ I₂ : Subgroup W}

private lemma s16c167_cfg10_zpowers_resHom (I : Subgroup W) (f : stabSub I) :
    Subgroup.zpowers (resHom I f) = autSub (Subgroup.zpowers (f : MulAut W)) I := by
  rw [autSub]
  have hsub : (Subgroup.zpowers (f : MulAut W)).subgroupOf (stabSub I) =
      Subgroup.zpowers f := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    exact ⟨fun ⟨k, hk⟩ => ⟨k, Subtype.ext (by simpa using hk)⟩,
      fun ⟨k, hk⟩ => ⟨k, by simpa using congrArg Subtype.val hk⟩⟩
  rw [hsub, MonoidHom.map_zpowers]

theorem s16c167_cfg10_autSub_facts (F : Cfg10Mod X Fs I₁ I₂) {I : Subgroup W}
    (hI : I = I₁ ∨ I = I₂) :
    Nat.card ↥(autSub Fs I) = 9 ∧ (∀ x ∈ autSub Fs I, x ^ 3 = 1) ∧
      (∀ x ∈ autSub Fs I, ∀ y ∈ autSub Fs I, x * y = y * x) ∧ Nat.card ↥I = 16 ∧
      ∀ v : ↥I, v * v = 1 := by
  have hstab : Fs ≤ stabSub I := by
    rcases hI with rfl | rfl
    · intro f hf; exact (s16c167_cfg10_stab F hf).1
    · intro f hf; exact (s16c167_cfg10_stab F hf).2
  have hcardF : Nat.card ↥Fs = 27 := s16c167_cfg10_F_card F.el
  have hker : Nat.card ↥(Fs ⊓ centSub I) = 3 := s16c167_cfg10_ker_card F hI
  have hmul := card_autSub_mul hstab
  have hcard9 : Nat.card ↥(autSub Fs I) = 9 := by
    rw [hcardF, hker] at hmul
    omega
  have hcardI : Nat.card ↥I = 16 := by
    rw [card_eq_two_pow F.sq I]
    rcases hI with rfl | rfl
    · rw [F.rk₁]; norm_num
    · rw [F.rk₂]; norm_num
  have hsqI : ∀ v : ↥I, v * v = 1 := by
    intro v
    exact Subtype.ext (by simpa [pow_two] using F.sq (v : W))
  refine ⟨hcard9, ?_, ?_, hcardI, hsqI⟩
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hx
    have hg3 : (g : stabSub I) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using (pow_three' (g : MulAut W)).trans (s16c167_cfg10_F_pow F.el g hg)
    rw [← map_pow, hg3, map_one]
  · intro x hx y hy
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hx
    obtain ⟨g', hg', rfl⟩ := mem_autSub.mp hy
    rw [← map_mul, ← map_mul]
    exact congrArg (resHom I) (Subtype.ext (s16c167_cfg10_F_comm F.el g hg g' hg'))

theorem s16c167_cfg10_comps (F : Cfg10Mod X Fs I₁ I₂) {I : Subgroup W} (hI : I = I₁ ∨ I = I₂) :
    ∃ A B : Subgroup W, A ≤ I ∧ B ≤ I ∧ rk ↥A = 2 ∧ rk ↥B = 2 ∧ A ⊓ B = ⊥ ∧ A ⊔ B = I ∧
      (∃ R : Subgroup (MulAut W), R ≤ Fs ∧ A = I ⊓ fixV R) ∧
      (∃ R : Subgroup (MulAut W), R ≤ Fs ∧ B = I ⊓ fixV R) ∧
      ∀ R : Subgroup (MulAut W), R ≤ Fs → rk ↥(I ⊓ fixV R) = 2 →
        I ⊓ fixV R = A ∨ I ⊓ fixV R = B := by
  obtain ⟨hP9, hP3, hPc, hIcard, hIsq⟩ := s16c167_cfg10_autSub_facts F hI
  obtain ⟨A', B', hA4, hB4, hABbot, hABtop, ⟨g, hg, hAeq⟩, ⟨h, hh, hBeq⟩, hchar⟩ :=
    s16c167_e9_comps hIsq hIcard hP9 hP3 hPc
  have hIsq2 : ∀ v : ↥I, v ^ 2 = 1 := fun v => by rw [pow_two]; exact hIsq v
  have hAstab : Fs ≤ stabSub I := by
    rcases hI with rfl | rfl
    · intro f hf; exact (s16c167_cfg10_stab F hf).1
    · intro f hf; exact (s16c167_cfg10_stab F hf).2
  have hArk : rk ↥(A'.map I.subtype) = 2 := by
    have hc : Nat.card ↥(A'.map I.subtype) = 2 ^ 2 := by
      rw [Subgroup.card_map_of_injective I.subtype_injective, hA4]
      norm_num
    unfold rk
    rw [hc, padicValNat.prime_pow]
  have hBrk : rk ↥(B'.map I.subtype) = 2 := by
    have hc : Nat.card ↥(B'.map I.subtype) = 2 ^ 2 := by
      rw [Subgroup.card_map_of_injective I.subtype_injective, hB4]
      norm_num
    unfold rk
    rw [hc, padicValNat.prime_pow]
  have hinf : A'.map I.subtype ⊓ B'.map I.subtype = ⊥ := by
    rw [← Subgroup.map_inf A' B' I.subtype I.subtype_injective, hABbot, Subgroup.map_bot]
  have hsup : A'.map I.subtype ⊔ B'.map I.subtype = I := by
    rw [← Subgroup.map_sup A' B' I.subtype, hABtop, Subgroup.map_top, Subgroup.range_subtype]
  have hAexists : ∃ R : Subgroup (MulAut W), R ≤ Fs ∧ A'.map I.subtype = I ⊓ fixV R := by
    obtain ⟨f, hfFs, hres⟩ := mem_autSub.mp hg
    refine ⟨Subgroup.zpowers (f : MulAut W), Subgroup.zpowers_le.mpr hfFs, ?_⟩
    have hRstab : Subgroup.zpowers (f : MulAut W) ≤ stabSub I :=
      Subgroup.zpowers_le.mpr f.2
    have hAfix : A' = fixV (autSub (Subgroup.zpowers (f : MulAut W)) I) := by
      rw [hAeq, ← hres, s16c167_cfg10_zpowers_resHom I f]
    have hmap :=
      map_subtype_fixV_autSub (A := Subgroup.zpowers (f : MulAut W)) (U := I) hRstab
    rw [hAfix]
    exact hmap
  have hBexists : ∃ R : Subgroup (MulAut W), R ≤ Fs ∧ B'.map I.subtype = I ⊓ fixV R := by
    obtain ⟨f, hfFs, hres⟩ := mem_autSub.mp hh
    refine ⟨Subgroup.zpowers (f : MulAut W), Subgroup.zpowers_le.mpr hfFs, ?_⟩
    have hRstab : Subgroup.zpowers (f : MulAut W) ≤ stabSub I :=
      Subgroup.zpowers_le.mpr f.2
    have hBfix : B' = fixV (autSub (Subgroup.zpowers (f : MulAut W)) I) := by
      rw [hBeq, ← hres, s16c167_cfg10_zpowers_resHom I f]
    have hmap :=
      map_subtype_fixV_autSub (A := Subgroup.zpowers (f : MulAut W)) (U := I) hRstab
    rw [hBfix]
    exact hmap
  refine ⟨A'.map I.subtype, B'.map I.subtype, Subgroup.map_subtype_le A',
    Subgroup.map_subtype_le B', hArk, hBrk, hinf, hsup, hAexists, hBexists, ?_⟩
  intro R hRFs hRrk
  have hRstab : R ≤ stabSub I := hRFs.trans hAstab
  have hfixrk : rk (fixV (autSub R I)) = 2 := by
    rw [rk_fixV_autSub hRstab, hRrk]
  have hfixcard : Nat.card ↥(fixV (autSub R I)) = 4 := by
    rw [card_eq_two_pow hIsq2 (fixV (autSub R I)), hfixrk]
    norm_num
  have hle : autSub R I ≤ autSub Fs I := autSub_mono hRFs I
  rcases hchar (autSub R I) hle hfixcard with hh | hh
  · left
    rw [← hh]
    exact (map_subtype_fixV_autSub hRstab).symm
  · right
    rw [← hh]
    exact (map_subtype_fixV_autSub hRstab).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
