module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62DCin
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P55Run

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P512d

theorem cinv_conj_iff (g : G) (v : V) (w : G) :
    g * w * g⁻¹ ∈ Cinv G (g • v) ↔ w ∈ Cinv G v := by
  have hS : ∀ k : G, g * k * g⁻¹ ∈ (MulAction.stabilizer G (g • v) : Set G) ↔
      k ∈ (MulAction.stabilizer G v : Set G) := by
    intro k
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, mul_smul, inv_smul_smul]
    exact (MulAction.injective g).eq_iff
  have hne : g * w * g⁻¹ ≠ 1 ↔ w ≠ 1 := by
    rw [Ne, Ne, mul_inv_eq_one, mul_eq_left]
  have hsq : g * w * g⁻¹ * (g * w * g⁻¹) = 1 ↔ w * w = 1 := by
    have : g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
    rw [this, mul_inv_eq_one, mul_eq_left]
  show (g * w * g⁻¹ ≠ 1 ∧ g * w * g⁻¹ * (g * w * g⁻¹) = 1 ∧
      g * w * g⁻¹ ∈ Cen (MulAction.stabilizer G (g • v) : Set G)) ↔
    (w ≠ 1 ∧ w * w = 1 ∧ w ∈ Cen (MulAction.stabilizer G v : Set G))
  rw [hne, hsq, P55.cen_conj_iff g hS w]

variable (F : FanTree Γ G)
include F

theorem cinv_zz (ℓ : Line Γ) {a : ℤ} {u : G} (hu : u ∈ Cinv G (ℓ.vert (a + 1))) :
    u ∈ ℓ.ZZ ∧ u ∈ Cen (ℓ.edgeStab (G := G) a : Set G) ∧
      u ∈ Cen (ℓ.edgeStab (G := G) (a + 1) : Set G) := by
  have hK := P62.cinv_mem_nbrStab F hu
  have hua : u ∈ Cen (ℓ.edgeStab (G := G) a : Set G) :=
    ⟨⟨MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hK _ (ℓ.adj a).symm), hu.2.2.1⟩,
      fun h hh => hu.2.2.2 h hh.2⟩
  have hub : u ∈ Cen (ℓ.edgeStab (G := G) (a + 1) : Set G) :=
    ⟨⟨hu.2.2.1, MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hK _ (ℓ.adj (a + 1)))⟩,
      fun h hh => hu.2.2.2 h hh.1⟩
  exact ⟨⟨hu.2.1, a, hua⟩, hua, hub⟩

theorem fixIdx_eq (h62 : Fan62 F) (h53b : Fan53b F) (h54 : Fan54 F) (h40 : Fan40 F)
    (T : Track Γ G) (hT : InXi T) {a : ℤ} {u : G} (hu : u ∈ Cinv G (T.line.vert (a + 1))) :
    ∀ j, j ∈ T.line.fixIdx u ↔ a - 3 ≤ j ∧ j ≤ a + 5 := by
  obtain ⟨hZZ, hca, hcb⟩ := cinv_zz F T.line hu
  have hZc : u ∈ T.line.Zc := P55.zz_le_zc hZZ
  obtain ⟨⟨a₁, b₁, tL₁, tR₁, hd⟩, hP⟩ := h62 h40 T hT u hZZ hu.1
  obtain ⟨hb, hr, hl⟩ := hP a₁ b₁ tL₁ tR₁ hd
  have hdC : T.line.IsCoreCFix u a₁ b₁ tL₁ tR₁ := ⟨hd.fix, h53b h40 T.line u a₁ b₁ hZZ hd.core⟩
  have hcore : ∀ i, u ∈ Cen (T.line.edgeStab (G := G) i : Set G) → a₁ ≤ i ∧ i < b₁ := by
    intro i hi
    have hs : u ∈ T.line.edgeStab (G := G) i := hi.1
    have hcI : u ∈ Cen (T.line.edgeCirc (G := G) i) := by
      refine ⟨P55.mem_edgeCirc_of_fix hu.2.1 (MulAction.mem_stabilizer_iff.1 hs.1)
        (MulAction.mem_stabilizer_iff.1 hs.2), fun h hh => ?_⟩
      have hfix := T.line.edgeCirc_fix hh
      exact hi.2 h ⟨MulAction.mem_stabilizer_iff.2 hfix.1, MulAction.mem_stabilizer_iff.2 hfix.2⟩
    obtain ⟨a₂, b₂, hC₂, ha₂, hb₂⟩ := P55.core_exists hd.fix hcI
    obtain ⟨e1, e2⟩ := fan55b F h54 h40 T u a₁ b₁ tL₁ tR₁ a₂ b₂ hZc hdC hC₂
    omega
  have h1 := hcore a hca
  have h2 := hcore (a + 1) hcb
  intro j
  rw [hd.fix j]
  omega

end P512d

end CFSG.Quasithin.Fan86
