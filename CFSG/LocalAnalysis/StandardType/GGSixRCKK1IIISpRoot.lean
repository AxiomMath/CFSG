module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Defs
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionSp
public import CFSG.LieType.Universal.SymplecticExtras.Matrices

public section

namespace CFSG.StandardType.RCKK1IIISp

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.RCKC1 CFSG.Open
open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.LieType.Steinberg

private theorem rckSpRoot_allEven_stdVec_positiveLong {n : ℕ} (i : Fin n) :
    GGRootSp.AllEven (stdVec (.positiveLong i)) := by
  intro a
  simp only [stdVec, Pi.smul_apply, Pi.single_apply]
  split_ifs <;> simp

private theorem rckSpRoot_allEven_of_ggLongRoot (n : ℕ) (F : Type) [Field F] (hn : 2 ≤ n)
    {β : Fin (Symplectic.rootDatum n F).rank → ℤ}
    (hl : GGLongRoot (Symplectic.rootDatum n F) β) :
    GGRootSp.AllEven (Symplectic.toStd n β) := by
  obtain ⟨w, γ₀, hγ₀, hmax, rfl⟩ := hl
  refine (GGRootSp.allEven_toStd_weylAction_iff w γ₀).2 ?_
  obtain ⟨r₀, hr₀⟩ := exists_stdVec_of_mem_roots hγ₀
  change GGRootSp.AllEven (toStd n γ₀)
  rw [← hr₀]
  have hn0 : 0 < n := by omega
  obtain ⟨θ, hθ, hθstd⟩ := GGRootSp.exists_root_toStd_eq (n := n) (.positiveLong ⟨0, hn0⟩)
  have hθ2 : 2 * ht θ = 2 * (2 * n - 1) := by
    rw [two_mul_ht, hθstd, stdVec, map_nsmul, lv_single, nsmul_eq_mul]
    push_cast
    ring_nf
  have hle : ht (ι := Fin n) θ ≤ ht (ι := Fin n) γ₀ := hmax θ hθ
  have hγ2 := two_mul_ht (n := n) γ₀
  rw [← hr₀] at hγ2
  have h4 : 4 * (n : ℤ) - 4 < lv n (stdVec r₀) := by omega
  rw [GGRootSp.stdVec_eq_of_lv_lt hn r₀ h4]
  exact rckSpRoot_allEven_stdVec_positiveLong _

theorem rckSp_shortRoot (m g : ℕ) (hm : 2 ≤ m) :
    ∃ β : Fin (Symplectic.rootDatum m (GaloisField 2 g)).rank → ℤ,
      β ∈ (Symplectic.rootDatum m (GaloisField 2 g)).roots ∧
      ¬ GGLongRoot (Symplectic.rootDatum m (GaloisField 2 g)) β ∧
      2 • β ∉ (Symplectic.rootDatum m (GaloisField 2 g)).roots := by
  obtain hm0 : 0 < m := by omega
  have hβ : (Pi.single (⟨0, hm0⟩ : Fin m) 1 : Fin m → ℤ) ∈
      (Symplectic.rootDatum m (GaloisField 2 g)).roots := by
    change (Pi.single (⟨0, hm0⟩ : Fin m) 1 : Fin m → ℤ) ∈ roots (isFiniteType_cartanC m) ∅
    refine Or.inl ⟨1, ⟨0, hm0⟩, ?_⟩
    simp
  have hβnl : ¬ GGLongRoot (Symplectic.rootDatum m (GaloisField 2 g))
      (Pi.single (⟨0, hm0⟩ : Fin m) 1) := by
    intro hl
    have hev := rckSpRoot_allEven_of_ggLongRoot m (GaloisField 2 g) hm hl
    have hev' : ¬ (⟨0, hm0⟩ : Fin m).val + 1 < m :=
      (GGRootSp.allEven_toStd_single_iff (n := m) (⟨0, hm0⟩ : Fin m)).1 hev
    simp only [Fin.val_mk, zero_add] at hev'
    exact absurd (by omega : (1 : ℕ) < m) hev'
  have h2β : 2 • (Pi.single (⟨0, hm0⟩ : Fin m) 1 : Fin m → ℤ) ∉
      (Symplectic.rootDatum m (GaloisField 2 g)).roots := by
    intro h2
    exact (not_eq_two_smul_of_divisible_eq_empty
      (D := Symplectic.rootDatum m (GaloisField 2 g)) rfl hβ h2) rfl
  exact ⟨Pi.single (⟨0, hm0⟩ : Fin m) 1, hβ, hβnl, h2β⟩

end CFSG.StandardType.RCKK1IIISp
