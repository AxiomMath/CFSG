module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1L5
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs

public section

namespace CFSG.StandardType.RCKC1

open Matrix CFSG.LieType.Universal CFSG.StandardType CFSG.Open

private theorem rckHA_mem_rootGroup_matrix {F : Type} [Field F] {m : ℕ} {β : Fin m → ℤ}
    (hβ : β ∈ (SpecialLinear.rootDatum m F).roots) {x : SpecialLinearGroup (Fin (m + 1)) F}
    (hx : x ∈ SpecialLinear.rootGroup m F β) :
    ∃ c : F, (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      1 + c • Matrix.single (SpecialLinear.idx m β).1 (SpecialLinear.idx m β).2 1 := by
  obtain ⟨hij, hstd⟩ := SpecialLinear.idx_spec m hβ
  rw [SpecialLinear.rootGroup_eq m F hij hstd] at hx
  obtain ⟨c, hc⟩ := (SpecialLinear.mem_rootSubgroup hij x).mp hx
  refine ⟨c, ?_⟩
  rw [← hc, Matrix.SpecialLinearGroup.transvection_coe]
  simp

private theorem rckHA_cent_of_transvection {F : Type} [Field F] {m : ℕ}
    {i j : Fin (m + 1)} (hij : i ≠ j) {c₀ : F} (hc₀ : c₀ ≠ 0)
    {x k : SpecialLinearGroup (Fin (m + 1)) F}
    (hx : (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 + c₀ • Matrix.single i j 1)
    (hk : Commute k x) :
    k ∈ Subgroup.centralizer (SpecialLinear.rootSubgroup m F hij : Set _) := by
  have hkxm : Commute (k : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
      (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
    simpa only [Matrix.SpecialLinearGroup.coeMonoidHom_apply] using
      hk.map Matrix.SpecialLinearGroup.coeMonoidHom
  rw [hx] at hkxm
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨c, hc⟩ := (SpecialLinear.mem_rootSubgroup hij y).mp hy
  have hym : (y : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      1 + c • Matrix.single i j 1 := by
    rw [← hc, Matrix.SpecialLinearGroup.transvection_coe]
    simp
  have hcomm := commute_one_add_smul_of_ne_zero hc₀ hkxm c
  have hkym : Commute (k : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
      (y : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
    rw [hym]
    exact hcomm
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  exact hkym.symm

private theorem rckHA_cent_specialLinear (F : Type) [Field F] (m : ℕ) {β : Fin m → ℤ}
    (hβ : β ∈ (SpecialLinear.rootDatum m F).roots) :
    ∀ x ∈ SpecialLinear.rootGroup m F β, x ≠ 1 →
      Subgroup.centralizer {x} ≤
        Subgroup.centralizer
          (SpecialLinear.rootGroup m F β : Set (SpecialLinearGroup (Fin (m + 1)) F)) := by
  obtain ⟨hij, hstd⟩ := SpecialLinear.idx_spec m hβ
  intro x hx hx1
  obtain ⟨c₀, hxmat⟩ := rckHA_mem_rootGroup_matrix hβ hx
  have hc₀ : c₀ ≠ 0 := by
    intro h0
    apply hx1
    apply Subtype.ext
    rw [hxmat, h0, zero_smul, add_zero]
    rfl
  rw [SpecialLinear.rootGroup_eq m F hij hstd]
  intro k hk
  exact rckHA_cent_of_transvection hij hc₀ hxmat
    (Subgroup.mem_centralizer_singleton_iff.mp hk)

theorem rck_lemmaHC_A
    {m g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .PSL m g).D.rank → ℤ}
    (hβ : GGLongRoot (ggU .PSL m g).D β) :
    RCKLemmaHCent (ggU .PSL m g) β := by
  cases m with
  | zero =>
    exfalso
    obtain ⟨w, γ₀, hγ₀, -, -⟩ := hβ
    rcases hγ₀ with ⟨w', i, -⟩ | ⟨w', i, -, -⟩
    · exact Fin.elim0 i
    · exact Fin.elim0 i
  | succ m' =>
    change ∀ x ∈ SpecialLinear.rootGroup m' (GaloisField 2 g) β, x ≠ 1 →
      Subgroup.centralizer {x} ≤
        Subgroup.centralizer
          (SpecialLinear.rootGroup m' (GaloisField 2 g) β :
            Set (SpecialLinearGroup (Fin (m' + 1)) (GaloisField 2 g)))
    refine rckHA_cent_specialLinear (GaloisField 2 g) m' ?_
    obtain ⟨w, γ₀, hγ₀, -, hβeq⟩ := hβ
    rw [hβeq]
    exact CFSG.LieType.RootSystem.weylAction_mem_roots (SpecialLinear.isFiniteType_A m') w hγ₀

end CFSG.StandardType.RCKC1
