module

public import CFSG.Quasithin.Background.B3SpecFacts
public import CFSG.Certificates.Kernel.B3MaskSound
public import Certificates.Kernel.B3.N5
public import Certificates.Kernel.B3.N6
public import Certificates.Kernel.B3.N7
public import Certificates.Kernel.B3.N8

public section

namespace CFSG.KD.B3MA

open CFSG.KC.B3M CFSG.Quasithin CFSG.Quasithin.B3

theorem n5 : B3M5.dat.n = 5 := by decide +kernel
theorem n6 : B3M6.dat.n = 6 := by decide +kernel
theorem n7 : B3M7.dat.n = 7 := by decide +kernel
theorem n8 : B3M8.dat.n = 8 := by decide +kernel

theorem ok5 : Ok B3M5.dat :=
  ⟨by simp [n5], by simp [n5], B3M5.bp_ok, B3M5.tm_ok, B3M5.ea_ok,
    B3M5.named_ok, by decide +kernel, by decide +kernel⟩

theorem ok6 : Ok B3M6.dat :=
  ⟨by simp [n6], by simp [n6], B3M5.bp_ok, B3M6.tm_ok, B3M6.ea_ok,
    B3M6.named_ok, by decide +kernel, by decide +kernel⟩

theorem ok7 : Ok B3M7.dat :=
  ⟨by simp [n7], by simp [n7], B3M5.bp_ok, B3M7.tm_ok, B3M7.ea_ok,
    B3M7.named_ok, by decide +kernel, by decide +kernel⟩

theorem ok8 : Ok B3M8.dat :=
  ⟨by simp [n8], by simp [n8], B3M5.bp_ok, B3M8.tm_ok, B3M8.ea_ok,
    B3M8.named_ok, by decide +kernel, by decide +kernel⟩

theorem mods {d : Dat} (h0 : chkModM d 0 = true) (h1 : chkModM d 1 = true)
    (h2 : chkModM d 2 = true) (h3 : chkModM d 3 = true) (k : Mod) :
    chkModM d (mIdx k) = true := by
  cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem propB32A_all (n : ℕ) (k : Mod) (hn : SQTKn n) (hA : CaseA n k) : PropB32A n k := by
  rcases hn with rfl | rfl | rfl | rfl
  · exact spec_caseAM B3M5.dat n5 ok5 k (by cases k <;> decide)
      (mods B3M5.mod0_ok B3M5.mod1_ok B3M5.mod2_ok B3M5.mod3_ok k)
  · refine spec_caseAM B3M6.dat n6 ok6 k ?_
      (mods B3M6.mod0_ok B3M6.mod1_ok B3M6.mod2_ok B3M6.mod3_ok k)
    rcases hA with h | rfl | rfl
    · norm_num at h
    · decide
    · decide
  · exact spec_caseAM B3M7.dat n7 ok7 k (by cases k <;> decide)
      (mods B3M7.mod0_ok B3M7.mod1_ok B3M7.mod2_ok B3M7.mod3_ok k)
  · refine spec_caseAM B3M8.dat n8 ok8 k ?_
      (mods B3M8.mod0_ok B3M8.mod1_ok B3M8.mod2_ok B3M8.mod3_ok k)
    rcases hA with h | rfl | rfl
    · norm_num at h
    · decide
    · decide

theorem propB32B5_all (n : ℕ) (k : Mod) (hn : SQTKn n) (hB : CaseB n k)
    (hexc : ¬ (n = 8 ∧ k = Mod.ut0)) : PropB32B5 n k := by
  obtain ⟨hev, hk⟩ := hB
  rcases hn with rfl | rfl | rfl | rfl
  · norm_num at hev
  · rcases hk with rfl | rfl
    · exact spec_caseB5M B3M6.dat n6 ok6 _ (by decide) B3M6.mod1_ok
    · exact spec_caseB5M B3M6.dat n6 ok6 _ (by decide) B3M6.mod3_ok
  · norm_num at hev
  · rcases hk with rfl | rfl
    · exact spec_caseB5M B3M8.dat n8 ok8 _ (by decide) B3M8.mod1_ok
    · exact absurd ⟨rfl, rfl⟩ hexc

theorem propB32B6_eight : PropB32B6 8 Mod.ut0 :=
  spec_caseB6M B3M8.dat n8 ok8 Mod.ut0 rfl (by decide) B3M8.mod3_ok

theorem subOK_Tl6 : subOK 6 (Tl 6) = true := by decide +kernel

theorem Tl6_sub : ∀ t ∈ Tl 6, t ∈ B3M6.dat.TL := by decide +kernel

theorem sub_Tl6 : ∀ t ∈ B3M6.dat.TL, t ∈ Tl 6 := by decide +kernel

theorem strong_of_iff (d : Dat) (hd : Ok d) {n : ℕ} (hdn : d.n = n) (k : Mod)
    (hc : caseOf n (mIdx k) ≠ 0) (hM : chkModM d (mIdx k) = true) {TL : List Tab}
    (hT : subOK n TL = true) (hTL : ∀ t, t ∈ TL ↔ t ∈ d.TL) (A : Subgroup (Gp n))
    (hA : A ≤ subOf n TL) :
    IsStrongFFStarOffender ((subOf n TL).map (Mod.act n k)) (A.map (Mod.act n k)) ↔
      A = Dsub n := by
  subst hdn
  rw [subOf_eq_of_iff hT (base_facts d hd).1 hTL] at hA ⊢
  exact strong_BM d hd k hc hM hA

theorem strongTl6 {k : Mod} (hk : k = Mod.u0 ∨ k = Mod.ut0) : StrongTl6 k := by
  have hTL : ∀ t, t ∈ Tl 6 ↔ t ∈ B3M6.dat.TL := fun t => ⟨Tl6_sub t, sub_Tl6 t⟩
  rcases hk with rfl | rfl
  · exact strong_of_iff B3M6.dat ok6 n6 Mod.u0 (by decide) B3M6.mod1_ok subOK_Tl6 hTL
  · exact strong_of_iff B3M6.dat ok6 n6 Mod.ut0 (by decide) B3M6.mod3_ok subOK_Tl6 hTL

end CFSG.KD.B3MA
