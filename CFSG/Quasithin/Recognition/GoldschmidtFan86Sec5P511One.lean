module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P58Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P511Conj
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5StmtA

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem zz_of_isCore {ℓ : Line Γ} {z : G} (hzz : z * z = 1) {a b : ℤ} (h : ℓ.IsCore z a b) :
    z ∈ ℓ.ZZ := by
  obtain ⟨hab, hc, -, -⟩ := (ℓ.isCore_iff).1 h
  exact ⟨hzz, a, hc a le_rfl hab⟩

theorem conj_involution {g z : G} (hzz : z * z = 1) : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
  calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
    _ = 1 := by rw [hzz]; group

theorem exists_partner (T : Track Γ G) (hrefl : T.HasReflections) {z : G} (hzz : z * z = 1)
    {a tL tR : ℤ} (hcore : T.line.IsCoreFix z a (a + 1) tL tR) (hlr : a - tL = tR - (a + 1)) :
    ∃ (z' : G) (a' b' tL' tR' : ℤ), z' * z' = 1 ∧ T.line.IsCoreFix z' a' b' tL' tR' ∧
      tR = a' ∧ tL' = a + 1 := by
  rcases Int.emod_two_eq_zero_or_one (tR - (a + 1)) with he | ho
  · obtain ⟨d, hd⟩ : ∃ d : ℤ, 2 * d = a + 1 + tR := ⟨(a + 1 + tR) / 2, by omega⟩
    obtain ⟨f, hf⟩ := hrefl d
    have hfv : ∀ i, f • T.line.vert i = T.line.vert (2 * d - i) := fun i => by
      have := hf.2 (i - d)
      rwa [show d + (i - d) = i by ring, show d - (i - d) = 2 * d - i by ring] at this
    refine ⟨f * z * f⁻¹, _, _, _, _, conj_involution hzz,
      T.line.isCoreFix_conj_refl (c := 2 * d) hfv hcore, ?_, ?_⟩ <;> omega
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, 2 * m = tR - (a + 1) + 1 := ⟨(tR - a) / 2, by omega⟩
    refine ⟨T.τ ^ m * z * (T.τ ^ m)⁻¹, _, _, _, _, conj_involution hzz,
      T.line.isCoreFix_conj_trans (g := T.τ ^ m) (s := 2 * m)
        (fun i => T.zpow_smul_vert m i) hcore, ?_, ?_⟩ <;> omega

theorem core_one_false (F : FanTree Γ G) (h40 : Fan40 F) (T : Track Γ G) (hrefl : T.HasReflections)
    (h53b : Fan53b F) (h57b : Fan57bT F) (h58b : Fan58b F) {z : G} (hz : z ∈ T.line.ZZ)
    {a tL tR : ℤ} (hcore : T.line.IsCoreFix z a (a + 1) tL tR) (hlr : a - tL = tR - (a + 1)) :
    False := by
  have hC : T.line.IsCoreC z a (a + 1) := h53b h40 T.line z a (a + 1) hz hcore.core
  obtain ⟨z', a', b', tL', tR', hz'z', hcore', hpos1, hpos2⟩ :=
    exists_partner T hrefl hz.1 hcore hlr
  have hz' : z' ∈ T.line.ZZ := zz_of_isCore hz'z' hcore'.core
  have hC' : T.line.IsCoreC z' a' b' := h53b h40 T.line z' a' b' hz' hcore'.core
  have hperf : T.line.InPerfectPos z z' a (a + 1) tL tR a' b' tL' tR' :=
    ⟨⟨hcore.fix, hC⟩, ⟨hcore'.fix, hC'⟩, hpos1, hpos2⟩
  have hr : tR - (a + 1) ≤ 2 :=
    h57b h40 T z z' a (a + 1) tL tR a' b' tL' tR' hz hz' hcore hcore' hperf
  have := h58b h40 T z a (a + 1) tL tR hz hcore hr (by omega)
  omega

end CFSG.Quasithin.Fan86
