module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.CentralizerTV

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_conjClosure_of_mem_normalizer {K W : Subgroup G} {g : G}
    (hK : g ∈ Subgroup.normalizer (K : Set G))
    (hW : g ∈ Subgroup.normalizer (W : Set G)) :
    g ∈ Subgroup.normalizer (conjClosure K W : Set G) := by
  refine uc22p22v_mem_normalizer_conjClosure ?_ ?_
  · intro x hx z hz
    exact ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hK x).mp hx,
      g * z * g⁻¹, (Subgroup.mem_normalizer_iff.mp hW z).mp hz, by group⟩
  · intro x hx z hz
    exact ⟨g⁻¹ * x * g,
      by
        simpa using
          (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hK) x).mp hx,
      g⁻¹ * z * g,
      by
        simpa using
          (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hW) z).mp hz,
      by group⟩

theorem s23_13_of (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h12 : S23_12 D Ch)
    (hN4' : H1930 D → ∀ c : Ctx2311 D Ch, ∀ w ∈ c.W, ∃ x ∈ c.X,
      w ∈ conjSubgroup D.Z x)
    (hN7 : H1930 D → ∀ c : Ctx2311 D Ch, conjClosure c.K c.W = c.V) :
    S23_13 D Ch := by
  intro h1930 c
  have hXW : c.X ≤ Subgroup.normalizer (c.W : Set G) :=
    uc22p22v_le_normalizer_conjClosure c.X D.Z
  have hZleW : D.Z ≤ c.W := uc22p22v_le_conjClosure c.X D.Z
  have hKM : c.K ≤ D.M := (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left
  have hMN : D.M ≤ Subgroup.normalizer (c.K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp (h12 h1930 c)
  have hMW_le_NV : Subgroup.normalizer (c.W : Set G) ⊓ D.M ≤
      Subgroup.normalizer (c.V : Set G) := by
    intro g hg
    have hgK : g ∈ Subgroup.normalizer (c.K : Set G) := hMN hg.2
    have hgW : g ∈ Subgroup.normalizer (c.W : Set G) := hg.1
    have hgV : g ∈ Subgroup.normalizer (conjClosure c.K c.W : Set G) :=
      mem_normalizer_conjClosure_of_mem_normalizer hgK hgW
    rwa [hN7 h1930 c] at hgV
  have hNW_le_sup : Subgroup.normalizer (c.W : Set G) ≤
      (Subgroup.normalizer (c.W : Set G) ⊓ D.M) ⊔ c.X := by
    intro g hg
    have hPg_le : conjSubgroup D.Z g ≤ c.W := by
      intro z hz
      rw [CFSG.Quasithin.mem_conjSubgroup_iff] at hz
      exact (Subgroup.mem_normalizer_iff.mp hg z).mpr (hZleW hz)
    have hPg_ne : conjSubgroup D.Z g ≠ ⊥ := by
      intro hbot
      apply uc22main1_Z_ne_bot D
      have hcard : Nat.card (conjSubgroup D.Z g) = Nat.card D.Z :=
        CFSG.Quasithin.E3.card_conjSubgroup D.Z g
      have hone : Nat.card D.Z = 1 := by
        rw [← hcard, hbot]
        simp
      exact Subgroup.card_eq_one.mp hone
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPg_ne
    have hzW : (z : G) ∈ c.W := hPg_le z.2
    obtain ⟨x, hxX, hzPx⟩ := hN4' h1930 c (z : G) hzW
    have hz_ne : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
    have hinter : conjSubgroup D.Z g ⊓ conjSubgroup D.Z x ≠ ⊥ := by
      intro hbot
      have hzbot : (z : G) ∈ (⊥ : Subgroup G) := by
        rw [← hbot]
        exact Subgroup.mem_inf.mpr ⟨z.2, hzPx⟩
      exact hz_ne (Subgroup.mem_bot.mp hzbot)
    have hPx_eq : conjSubgroup D.Z x = conjSubgroup D.Z g := by
      have h := c.conjSubgroup_TI h4 h1930 g (g⁻¹ * x)
      have hx_eq : conjSubgroup (conjSubgroup D.Z g) (g⁻¹ * x) =
          conjSubgroup D.Z x := by
        rw [CFSG.Quasithin.conjSubgroup_conjSubgroup]
        congr 1
        group
      rw [hx_eq] at h
      exact h hinter
    have hZconj : conjSubgroup D.Z (g * x⁻¹) = D.Z := by
      calc conjSubgroup D.Z (g * x⁻¹) =
          conjSubgroup (conjSubgroup D.Z g) x⁻¹ :=
            (CFSG.Quasithin.conjSubgroup_conjSubgroup D.Z g x⁻¹).symm
        _ = conjSubgroup (conjSubgroup D.Z x) x⁻¹ := by rw [← hPx_eq]
        _ = conjSubgroup D.Z (x * x⁻¹) :=
            CFSG.Quasithin.conjSubgroup_conjSubgroup D.Z x x⁻¹
        _ = D.Z := by rw [mul_inv_cancel, CFSG.Quasithin.conjSubgroup_one]
    have hNZ : Subgroup.normalizer (D.Z : Set G) = D.M := by
      have hUZ : D.U = D.Z := (h4 h1930 c.toCtx23L).1
      rw [← hUZ]
      exact D.normalizer_U_eq
    have hgxM : g * x⁻¹ ∈ D.M := by
      rw [← hNZ]
      exact (CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer).mp hZconj
    have hgxW : g * x⁻¹ ∈ Subgroup.normalizer (c.W : Set G) :=
      (Subgroup.normalizer (c.W : Set G)).mul_mem hg
        ((Subgroup.normalizer (c.W : Set G)).inv_mem (hXW hxX))
    have hgx : g * x⁻¹ ∈ Subgroup.normalizer (c.W : Set G) ⊓ D.M :=
      Subgroup.mem_inf.mpr ⟨hgxW, hgxM⟩
    have heq : g = (g * x⁻¹) * x := by group
    rw [heq]
    exact ((Subgroup.normalizer (c.W : Set G) ⊓ D.M) ⊔ c.X).mul_mem
      (Subgroup.mem_sup_left hgx) (Subgroup.mem_sup_right hxX)
  have hX_le_NV : c.X ≤ Subgroup.normalizer (c.V : Set G) :=
    c.hX.1.2.1.trans
      ((le_sup_left : c.L ≤ c.L ⊔ D.T).trans
        (Ctx23L.sup_le_normalizer_V D Ch c.toCtx23L))
  have hsup_le_NV : (Subgroup.normalizer (c.W : Set G) ⊓ D.M) ⊔ c.X ≤
      Subgroup.normalizer (c.V : Set G) :=
    sup_le hMW_le_NV hX_le_NV
  have hNW_le_NV : Subgroup.normalizer (c.W : Set G) ≤
      Subgroup.normalizer (c.V : Set G) :=
    hNW_le_sup.trans hsup_le_NV
  rwa [c.normalizer_V_eq h4 h1930] at hNW_le_NV

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
