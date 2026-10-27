module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.HypA39Aux
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.HypA

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open scoped Pointwise commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type u} [Group Γ]

theorem hasB_of_quot {p : ℕ} {H A D D₁ D₂ M N L R : Subgroup Γ}
    (h15 : HypA15 p H A D D₁ D₂) (hM : Admits (H ⊔ A) M)
    (h6 : HypA6 (AChief.qimg M H) (AChief.qimg M A) (AChief.qimg M D) (AChief.qimg M D₁)
      (AChief.qimg M D₂))
    (hMN : M ≤ N) (hLR : L ≤ R) (hRH : R ≤ H)
    (hNadm : Admits (D ⊔ A) N) (hLadm : Admits (D ⊔ A) L) (hRadm : Admits (D ⊔ A) R)
    (hchief : IsChiefFactorOf (R ⊔ D ⊔ A) L N)
    (hcen : A ⊔ R ≤ secCenIn (R ⊔ D ⊔ A) L N)
    (hRD : R ⊓ D = D₁) (hND : D ⊓ N ≤ D₂)
    (hdir : IsDirectProductMod N (D₁ ⊔ N) (D₂ ⊔ N) L) :
    HasB A D D₁ D₂ R := by
  have hNL : N ≤ L := hchief.2.2.1.le
  have hHn : H ≤ AChief.nrm M := le_sup_left.trans hM
  have hAn : A ≤ AChief.nrm M := le_sup_right.trans hM
  have hD₂D : D₂ ≤ D := h15.D₂_le
  have hD₁D : D₁ ≤ D := h15.D₁_le
  have hDn : D ≤ AChief.nrm M := h15.D_le.trans hHn
  have hRn : R ≤ AChief.nrm M := hRH.trans hHn
  have hLn : L ≤ AChief.nrm M := hLR.trans hRn
  have hNn : N ≤ AChief.nrm M := hNL.trans hLn
  have hD₁n : D₁ ≤ AChief.nrm M := hD₁D.trans hDn
  have hD₂n : D₂ ≤ AChief.nrm M := hD₂D.trans hDn
  have hNR : N ≤ R := hNL.trans hLR
  have hMR : M ≤ R := hMN.trans hNR
  have hY : R ⊔ D ⊔ A ≤ AChief.nrm M := sup_le (sup_le hRn hDn) hAn
  have hqDA : AChief.qimg M (D ⊔ A) = AChief.qimg M D ⊔ AChief.qimg M A :=
    SolQuot.qimg_sup hDn hAn
  have hqY : AChief.qimg M (R ⊔ D ⊔ A) =
      AChief.qimg M R ⊔ AChief.qimg M D ⊔ AChief.qimg M A := by
    rw [SolQuot.qimg_sup (sup_le hRn hDn) hAn, SolQuot.qimg_sup hRn hDn]
  have hRadmY : Admits (R ⊔ D ⊔ A) R := sup_le (sup_le Subgroup.le_normalizer
    (le_sup_left.trans hRadm)) (le_sup_right.trans hRadm)
  have hNadm' : Admits (AChief.qimg M D ⊔ AChief.qimg M A) (AChief.qimg M N) := by
    rw [← hqDA]
    exact HypAAux.admits_qimg hNadm
  have hLadm' : Admits (AChief.qimg M D ⊔ AChief.qimg M A) (AChief.qimg M L) := by
    rw [← hqDA]
    exact HypAAux.admits_qimg hLadm
  have hRadm' : Admits (AChief.qimg M D ⊔ AChief.qimg M A) (AChief.qimg M R) := by
    rw [← hqDA]
    exact HypAAux.admits_qimg hRadm
  have hchief' : IsChiefFactorOf (AChief.qimg M R ⊔ AChief.qimg M D ⊔ AChief.qimg M A)
      (AChief.qimg M L) (AChief.qimg M N) := by
    rw [← hqY]
    exact (HypAAux.isChiefFactorOf_qimg_iff (N := M) (hLR.trans (le_sup_left.trans le_sup_left))
      hNL hY (inf_le_right.trans hMN)).mpr hchief
  have hcen' : AChief.qimg M A ⊔ AChief.qimg M R ≤
      secCenIn (AChief.qimg M R ⊔ AChief.qimg M D ⊔ AChief.qimg M A) (AChief.qimg M L)
        (AChief.qimg M N) := by
    intro z hz
    rw [← SolQuot.qimg_sup hAn hRn] at hz
    obtain ⟨y, hy, rfl⟩ := (AChief.mem_qimg_iff M _ z).mp hz
    obtain ⟨hyY, hys⟩ := Subgroup.mem_inf.mp (hcen hy)
    obtain ⟨hyN, hyL, hcomm⟩ := McBride.mem_sectionCentralizer_iff.mp hys
    have hyq : AChief.qmap M y ∈ AChief.qimg M (R ⊔ D ⊔ A) :=
      (AChief.mem_qimg_iff M _ _).mpr ⟨y, hyY, rfl⟩
    rw [hqY] at hyq
    refine Subgroup.mem_inf.mpr ⟨hyq, McBride.mem_sectionCentralizer_iff.mpr ⟨?_, ?_, ?_⟩⟩
    · exact HypAAux.admits_qimg (N := M) hchief.1.2 (by rw [← hqY] at hyq; exact hyq)
    · exact HypAAux.admits_qimg (N := M) hchief.2.1.2 (by rw [← hqY] at hyq; exact hyq)
    · intro x' hx'
      obtain ⟨x, hx, rfl⟩ := (AChief.mem_qimg_iff M _ x').mp hx'
      obtain ⟨hmn, hq⟩ := HypAAux.qmap_commutator y.2 x.2
      have hq' : ⁅AChief.qmap M y, AChief.qmap M x⁆ =
          AChief.qmap M ⟨⁅(y : Γ), (x : Γ)⁆, hmn⟩ := hq.symm
      rw [hq']
      exact (AChief.mem_qimg_iff M N _).mpr ⟨⟨⁅(y : Γ), (x : Γ)⁆, hmn⟩, hcomm _ hx, rfl⟩
  have hRD' : AChief.qimg M R ⊓ AChief.qimg M D = AChief.qimg M D₁ := by
    rw [inf_comm, ← SolQuot.qimg_inf_of_le hRn hMR, inf_comm, hRD]
  have hND' : AChief.qimg M D ⊓ AChief.qimg M N ≤ AChief.qimg M D₂ := by
    rw [← SolQuot.qimg_inf_of_le hNn hMN]
    exact SolQuot.qimg_mono hND
  have hdir' : IsDirectProductMod (AChief.qimg M N) (AChief.qimg M D₁ ⊔ AChief.qimg M N)
      (AChief.qimg M D₂ ⊔ AChief.qimg M N) (AChief.qimg M L) := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hdir
    refine ⟨le_sup_right, SolQuot.qimg_mono hNL, ?_, ?_, ?_⟩
    · have := congrArg (AChief.qimg M) h3
      rwa [SolQuot.qimg_sup (sup_le hD₂n hNn) hLn, SolQuot.qimg_sup hD₂n hNn,
        SolQuot.qimg_sup hD₁n hNn] at this
    · have := congrArg (AChief.qimg M) h4
      rwa [SolQuot.qimg_inf_of_le hLn (hMN.trans hNL), SolQuot.qimg_sup hD₂n hNn] at this
    · refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
      rw [← SolQuot.qimg_sup hD₂n hNn] at hx
      obtain ⟨x₀, hx₀, rfl⟩ := (AChief.mem_qimg_iff M _ x).mp hx
      obtain ⟨y₀, hy₀, rfl⟩ := (AChief.mem_qimg_iff M _ y).mp hy
      obtain ⟨hmn, hq⟩ := HypAAux.qmap_commutator x₀.2 y₀.2
      have hq' : ⁅AChief.qmap M x₀, AChief.qmap M y₀⁆ =
          AChief.qmap M ⟨⁅(x₀ : Γ), (y₀ : Γ)⁆, hmn⟩ := hq.symm
      rw [hq']
      exact (AChief.mem_qimg_iff M N _).mpr
        ⟨⟨⁅(x₀ : Γ), (y₀ : Γ)⁆, hmn⟩, h5 (Subgroup.commutator_mem_commutator hx₀ hy₀), rfl⟩
  obtain ⟨B', hB'R, hB'adm, hB'D, hRB'⟩ := h6 (AChief.qimg M N) (AChief.qimg M L)
    (AChief.qimg M R) (SolQuot.qimg_mono (hNR.trans hRH)) (SolQuot.qimg_mono (hLR.trans hRH))
    (SolQuot.qimg_mono hRH) hNadm' hLadm' hRadm' (SolQuot.qimg_mono hLR) hchief' hcen' hRD'
    hND' hdir'
  have hD₁R : D₁ ≤ R := by
    rw [← hRD]
    exact inf_le_left
  have hD₂R : D₂ ≤ R := h15.D₂_lt.le.trans hD₁R
  have hqpre : SolQuot.qpre M B' ≤ AChief.nrm M := SolQuot.qpre_le_nrm B'
  have hqB : AChief.qimg M (R ⊓ SolQuot.qpre M B') = B' := HypAAux.qimg_inf_qpre hB'R
  have hMB : M ≤ R ⊓ SolQuot.qpre M B' := le_inf hMR (SolQuot.le_qpre B')
  refine ⟨R ⊓ SolQuot.qpre M B', inf_le_left, ?_, ?_, ?_⟩
  · refine Admits.inf hRadmY (HypAAux.admits_qpre hY ?_)
    rw [hqY]
    exact hB'adm
  · have hDB : D ⊓ SolQuot.qpre M B' ≤ D₂ := by
      refine HypAAux.inf_le_of_qimg_inf_le hDn hD₂D ((inf_le_inf_left D hMN).trans hND)
        (SolQuot.le_qpre B') hqpre ?_
      rw [SolQuot.qimg_qpre, inf_comm]
      exact hB'D.le
    have hD₂B' : AChief.qimg M D₂ ≤ B' := by
      rw [← hB'D]
      exact inf_le_left
    refine le_antisymm (fun x hx => ?_) (le_inf (le_inf hD₂R ((SolQuot.qimg_le_iff hD₂n).mp hD₂B'))
      hD₂D)
    obtain ⟨hxB, hxD⟩ := Subgroup.mem_inf.mp hx
    exact hDB (Subgroup.mem_inf.mpr ⟨hxD, (Subgroup.mem_inf.mp hxB).2⟩)
  · have hBn : R ⊓ SolQuot.qpre M B' ≤ AChief.nrm M := inf_le_left.trans hRn
    have himg : AChief.qimg M ((R ⊓ SolQuot.qpre M B') ⊔ D₁) = AChief.qimg M R := by
      rw [SolQuot.qimg_sup hBn hD₁n, hqB]
      exact hRB'.symm
    exact HypAAux.eq_of_qimg_eq hRn le_rfl (sup_le inf_le_left hD₁R) inf_le_left
      (inf_le_right.trans (hMB.trans le_sup_left)) himg.symm

end CFSG.SignalizerFunctorTheorem.McBride.Near
