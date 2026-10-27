module

public import CFSG.LocalAnalysis.StandardType.GGA11Defs
public import CFSG.LocalAnalysis.StandardType.GGA11Present

public section

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear

namespace CFSG.StandardType.A11

private theorem a11sp_conj_one_comp {M N : Type*} [Group M] [Group N] (f : N →* M) :
    (MulAut.conj (1 : M)).toMonoidHom.comp f = f := by
  apply MonoidHom.ext
  intro x
  change MulAut.conj (1 : M) (f x) = f x
  rw [MulAut.conj_apply, one_mul, inv_one, mul_one]

theorem a11StrongOfDataInput_of_present
    : A11StrongOfDataInput := by
  have h := CFSG.StandardType.A11.a11PresentInput_holds
  intro G _ _ B Bs x L D J hR hA y K φ₃ f n Φ ρ hFrame hCoh hRho hN
  obtain ⟨hGlue, hφ₃K, hNbr, _hBs, _hx, _hy, _hD, hnL, hJK, _hJ, hLcl⟩ := hFrame
  obtain ⟨hΦ3, _hInj, hRange, _hT9, _hCohΦ⟩ := hCoh
  obtain ⟨hCore3, hClosΦ, hRhoRange⟩ := hRho
  have hKle : K ≤ ggG0 7 B x L D J := le_ggG0_of_ggNbr hNbr
  have hLKle : L ⊔ K ≤ ggG0 7 B x L D J := sup_le (le_ggG0_left 7 B x L D J) hKle
  have hmap_le : ∀ l : Fin 4, K.map (MulAut.conj (n l)).toMonoidHom ≤ L ⊔ K := by
    intro l
    rw [Subgroup.map_le_iff_le_comap]
    intro k hk
    rw [Subgroup.mem_comap]
    change MulAut.conj (n l) k ∈ L ⊔ K
    rw [MulAut.conj_apply]
    exact mul_mem (mul_mem ((show L ≤ L ⊔ K from le_sup_left) (hnL l))
      ((show K ≤ L ⊔ K from le_sup_right) hk))
      (inv_mem ((show L ≤ L ⊔ K from le_sup_left) (hnL l)))
  have hΦl_le : ∀ l : Fin 4, (Φ l).range ≤ ggG0 7 B x L D J := by
    intro l
    calc (Φ l).range = φ₃.range.map (MulAut.conj (n l)).toMonoidHom := hRange l
      _ = K.map (MulAut.conj (n l)).toMonoidHom := by rw [hφ₃K]
      _ ≤ L ⊔ K := hmap_le l
      _ ≤ ggG0 7 B x L D J := hLKle
  have hρG : ρ.range ≤ ggG0 7 B x L D J := hRhoRange.trans (iSup_le hΦl_le)
  have hφ₃G : φ₃.range ≤ ggG0 7 B x L D J := (le_of_eq hφ₃K).trans hKle
  have hφ₃Clos : φ₃.range ≤ Clos φ₃ ρ := by simpa only [hΦ3] using hClosΦ 3
  have hJleClos : J ≤ Clos φ₃ ρ := hJK.trans ((le_of_eq hφ₃K.symm).trans hφ₃Clos)
  have hJ2leClos : J.map (MulAut.conj (n 2)).toMonoidHom ≤ Clos φ₃ ρ := by
    have h1 : J.map (MulAut.conj (n 2)).toMonoidHom ≤
        φ₃.range.map (MulAut.conj (n 2)).toMonoidHom :=
      Subgroup.map_mono (hJK.trans (le_of_eq hφ₃K.symm))
    exact h1.trans (by simpa only [hRange 2, hΦ3] using hClosΦ 2)
  have hL : L ≤ Clos φ₃ ρ :=
    hLcl.trans ((Subgroup.closure_le (Clos φ₃ ρ)).mpr
      (Set.union_subset (fun _ hx => hJleClos hx) (fun _ hx => hJ2leClos hx)))
  obtain ⟨ψ₀, hpres, hext⟩ :=
    h G B Bs x L D J hR hA φ₃ ρ hGlue.1 (by simpa only [hΦ3] using hCore3) hφ₃G hρG hL hN
  refine ⟨ψ₀, y, K, 1, hpres, hNbr, ?_⟩
  have hcomp : (MulAut.conj (1 : (ggU .PSL 12 1).K)).toMonoidHom.comp
      (slBlockHom₃ 8 (GaloisField 2 1)) = slBlockHom₃ 8 (GaloisField 2 1) :=
    a11sp_conj_one_comp _
  have heq : ψ₀.comp (slBlockHom₃ 8 (GaloisField 2 1)) = φ₃ := MonoidHom.ext hext
  rw [hcomp, heq, hφ₃K]

end CFSG.StandardType.A11

end
