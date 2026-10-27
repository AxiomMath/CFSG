module

public import CFSG.Sporadic.Fi24.Simple
public meta import Certificates.Data.CFSGNative.Fi24.Certificate
public import Certificates.Certificate1019
public import CFSG.Sporadic.Fi24.Faithful
public import CFSG.Sporadic.Fi24.SepSpec

public section

namespace CFSG.Sporadic.Fi24

open Native CFSG.Sporadic.Th.Native

theorem subLab_a_root :
    subLab (a • root) = 2 := by
  classical
  obtain ⟨Γ, hseed, hmain⟩ := Certificates.certificate1019
  have hJ : J ≤ Γ := by
    change Subgroup.closure {gA, gB} ≤ Γ
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact hseed _ (Or.inl rfl)
    · exact hseed _ (Or.inr rfl)
  set P : Fin 306936 → Submodule (ZMod 3) (Fin 781 → ZMod 3) := fun k => (pt k.val).sp with hPdef
  have hP : Function.Injective P := fun i j h =>
    Fin.ext (pt_inj (by rw [nPts_eq]; exact i.isLt) (by rw [nPts_eq]; exact j.isLt) (Sub781.ext' h))
  have hPs : ∀ (h : J) (k : Fin 306936),
      (P k).map (Matrix.mulVecLin (((h : GL (Fin 781) (ZMod 3))) :
        Matrix (Fin 781) (Fin 781) (ZMod 3))) = P (h • k) := by
    intro h k
    rw [hPdef]
    dsimp only
    rw [pt_smul, smul_sp]
  have hPg : ∀ k, ∃ g ∈ Γ, P k = (pt 0).sp.map
      (Matrix.mulVecLin (g : Matrix (Fin 781) (Fin 781) (ZMod 3))) := by
    intro k
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq J root k
    refine ⟨h, hJ h.2, ?_⟩
    have := hPs h root
    rw [hh] at this
    exact this.symm
  obtain ⟨Ψ, hcard, hne, hstab, k, hk, hkA⟩ := hmain P hP hPg
  have hsub : ∀ q ∈ Ψ, subLab q = 2 := by
    intro q hq
    have hq0 : subLab q ≠ 0 := by
      intro h0
      exact hne q hq (by rw [subLab_eq_zero.1 h0])
    have hq1 : subLab q ≠ 1 := by
      intro h1
      have hall : Finset.univ.filter (fun p : Fin 306936 => subLab p = 1) ⊆ Ψ := by
        intro q' hq'
        rw [Finset.mem_filter] at hq'
        obtain ⟨h, hh, rfl⟩ := subLab_orb q q' (by rw [h1, hq'.2])
        have hfix : (pt 0).sp.map (Matrix.mulVecLin (((h : GL (Fin 781) (ZMod 3))) :
            Matrix (Fin 781) (Fin 781) (ZMod 3))) = (pt 0).sp := by
          have := hPs h root
          rw [lvl_one_fix hh] at this
          exact this
        obtain ⟨k', hk', e⟩ := hstab h (hJ h.2) hfix q hq
        rw [hPs] at e
        rw [hP e]
        exact hk'
      have := Finset.card_le_card hall
      rw [card_subLab_one, hcard] at this
      omega
    rcases hl : subLab q with ⟨_ | _ | _ | n, hn⟩
    · exact absurd hl hq0
    · exact absurd hl hq1
    · rfl
    · omega
  have hka : k = a • root := hP (hkA.trans (hPs a root))
  rw [← hka]
  exact hsub k hk

end CFSG.Sporadic.Fi24
