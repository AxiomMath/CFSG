module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P512Cen
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Swap

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P517

theorem ker_track (F : FanTree Γ G) (h510 : Fan510 F) (h511 : Fan511 F) (h53a : Fan53a F)
    (h40 : Fan40 F) {T : Track Γ G} (hT : InXi T) {z : G} {a : ℤ} (hz : z ∈ T.line.ZZ)
    (hz1 : z ≠ 1) (hcore : T.line.IsCore z a (a + 2))
    (hα : valence Γ (T.line.vert (a + 1)) = 5) (g : G)
    (hg : Γ.dist (T.line.vert (a + 1)) (g • T.line.vert (a + 1)) = 2) :
    g * z * g⁻¹ ∈ nbrStab Γ G (T.line.vert (a + 1)) := by
  set ℓ := T.line with hℓ
  have hzα : z ∈ Cinv G (ℓ.vert (a + 1)) := fan512cen F h40 T z a hT hz hz1 hcore
  obtain ⟨⟨a', b', tL, tR, hf⟩, -⟩ := P512.coreSat2 h510 h511 h40 hT hz hz1
  have hfix : ℓ.IsCoreFix z a (a + 2) tL tR := ⟨hf.fix, hcore⟩
  obtain ⟨-, hl1, -, hl2⟩ := h53a h40 ℓ z a (a + 2) tL tR hz hfix
  have htR : a + 2 ≤ tR := ((hf.fix (a + 2)).1 (hcore.2.1 (a + 2) (by omega) le_rfl)).2
  have hl2' : 2 ≤ a - tL := by
    by_contra hlt
    have htL : tL = a - 1 := by omega
    have hv := ℓ.valence_add_two F (a - 1)
    rw [show a - 1 + 2 = a + 1 by ring, hα] at hv
    have := hl2 (by rw [htL, ← hv]; omega)
    omega
  have hza : z • ℓ.vert (a - 2) = ℓ.vert (a - 2) := (hf.fix (a - 2)).2 ⟨by omega, by omega⟩
  have hzb : z • ℓ.vert a = ℓ.vert a := hcore.2.1 a le_rfl (by omega)
  have h1 : T.τ⁻¹ • ℓ.vert a = ℓ.vert (a - 2) := by
    rw [inv_smul_eq_iff, T.trans, show a - 2 + 2 = a by ring]
  have h2 : T.τ⁻¹ • ℓ.vert (a + 2) = ℓ.vert a := by rw [inv_smul_eq_iff, T.trans]
  have hfa : (T.τ * z * T.τ⁻¹) • ℓ.vert a = ℓ.vert a := by
    rw [mul_smul, mul_smul, h1, hza, T.trans, show a - 2 + 2 = a by ring]
  have hfc : (T.τ * z * T.τ⁻¹) • ℓ.vert (a + 2) = ℓ.vert (a + 2) := by
    rw [mul_smul, mul_smul, h2, hzb, T.trans]
  have hne : ℓ.vert a ≠ ℓ.vert (a + 2) := ℓ.nb a
  have hK₁ : T.τ * z * T.τ⁻¹ ∈ nbrStab Γ G (ℓ.vert (a + 1)) :=
    F.fix_two_nbrs (ℓ.adj a).symm (Line.adj_add_two ℓ a) hne hfa hfc
  obtain ⟨ν, hν⟩ := P62.exists_br F hg
  have hbr₀ : P62.Br Γ (ℓ.vert (a + 1)) (ℓ.vert (a + 2)) (ℓ.vert (a + 3)) := by
    refine ⟨Line.adj_add_two ℓ a, ?_, ?_⟩
    · have := ℓ.adj (a + 2)
      rwa [show a + 2 + 1 = a + 3 by ring] at this
    · have := ℓ.nb (a + 1)
      rw [show a + 1 + 2 = a + 3 by ring] at this
      exact this.symm
  obtain ⟨k, hk, hkx⟩ := P62.exists_stab_smul_br F h40 hα hbr₀ hν
  have hτα : (k * T.τ) • ℓ.vert (a + 1) = g • ℓ.vert (a + 1) := by
    rw [mul_smul, T.trans, show a + 1 + 2 = a + 3 by ring, hkx]
  have e1 := P514.Lb_eq hzα (g := g) rfl
  have e2 := P514.Lb_eq hzα hτα
  rw [← e1, e2]
  have hkα : k • ℓ.vert (a + 1) = ℓ.vert (a + 1) := MulAction.mem_stabilizer_iff.1 hk
  have := F.conj_mem_nbrStab_smul k hK₁
  rw [hkα] at this
  have heq : k * T.τ * z * (k * T.τ)⁻¹ = k * (T.τ * z * T.τ⁻¹) * k⁻¹ := by group
  rw [heq]
  exact this

end P517

end CFSG.Quasithin.Fan86
