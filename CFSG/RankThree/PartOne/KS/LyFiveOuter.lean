module

public import CFSG.Sporadic.Schreier.LyOuter
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.RankThree.PartOne.KS.LyFiveOuterPerm
public import CFSG.RankThree.PartOne.KS.LyFiveCover

public section

namespace CFSG.RankThree.PartOne.LyFive

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier Equiv Equiv.Perm Subgroup

theorem inner_of_fixes_C_centralizer
    {w : J} (hwC : w ∈ lyC) (hw : orderOf w = 5) {α : MulAut J}
    (hαz : α lyz = lyz) (hα2 : α * α = 1)
    (hfix : ∀ c ∈ lyC, c * w = w * c → α c = c) :
    ∃ x : J, MulAut.conj x = α := by
  have hαA : α ∈ autZ := mem_autZ.2 hαz
  let a : autZ := ⟨α, hαA⟩
  let β : MulAut lyC := restrictC a
  have hββ : β * β = 1 := by
    have h : a * a = 1 := Subtype.ext hα2
    show restrictC a * restrictC a = 1
    rw [← map_mul, h, map_one]
  have hβapp : ∀ c : lyC, ((β c : lyC) : J) = α c := fun c => restrictC_apply a c
  let γ : MulAut (alternatingGroup (Fin 11)) :=
    lyCoverEquiv.symm.trans ((quotAut β).trans lyCoverEquiv)
  have hγmk : ∀ u : lyC, γ (lyCoverEquiv (u : lyC ⧸ zGroup)) =
      lyCoverEquiv ((β u : lyC) : lyC ⧸ zGroup) := by
    intro u
    simp only [γ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, quotAut_mk]
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 11
    (by norm_num) (by norm_num)
  obtain ⟨σ, hσ⟩ := hbij.2 γ
  have hσapp : ∀ g : alternatingGroup (Fin 11),
      ((γ g : alternatingGroup (Fin 11)) : Perm (Fin 11)) = σ * (g : Perm (Fin 11)) * σ⁻¹ := by
    intro g
    rw [← hσ]
    exact MulAut.conjNormal_apply σ g
  have hγγ : ∀ g : alternatingGroup (Fin 11), γ (γ g) = g := by
    intro g
    obtain ⟨ū, hū⟩ := lyCoverEquiv.surjective g
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective ū
    rw [← hū, hγmk, hγmk]
    have : β (β u) = u := by
      have := congrArg (fun f : MulAut lyC => f u) hββ
      simpa using this
    rw [this]
  have hσσ : σ * σ = 1 := by
    apply hbij.1
    rw [map_mul, hσ, map_one]
    refine MulEquiv.ext fun g => ?_
    simpa [MulAut.mul_apply] using hγγ g
  set wC : lyC := ⟨w, hwC⟩ with hwCdef
  have hw5 : w ^ 5 = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw] at this
  have hwC5 : wC ^ 5 = 1 := Subtype.ext (by simpa [wC] using hw5)
  have hcomm : ∀ g : Perm (Fin 11), sign g = 1 → Commute g (imgC wC) → Commute g σ := by
    intro g hg hgw
    have hgA : g ∈ alternatingGroup (Fin 11) := mem_alternatingGroup.2 hg
    obtain ⟨ū, hū⟩ := lyCoverEquiv.surjective ⟨g, hgA⟩
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective ū
    have hug : imgC u = g := by rw [imgC_apply, hū]
    have hcz : u * wC * u⁻¹ * wC⁻¹ ∈ zGroup := by
      rw [← imgC_eq_one_iff, map_mul, map_mul, map_mul, map_inv, map_inv, hug]
      have h1 := hgw.eq
      calc g * imgC wC * g⁻¹ * (imgC wC)⁻¹ = (g * imgC wC) * g⁻¹ * (imgC wC)⁻¹ := by group
        _ = (imgC wC * g) * g⁻¹ * (imgC wC)⁻¹ := by rw [h1]
        _ = 1 := by group
    have hcu : u * wC = wC * u := by
      rcases mem_zGroup.1 hcz with h | h
      · calc u * wC = (u * wC * u⁻¹ * wC⁻¹) * (wC * u) := by group
          _ = wC * u := by rw [h, one_mul]
      · exfalso
        have h1 : u * wC * u⁻¹ = zC * wC := by
          calc u * wC * u⁻¹ = (u * wC * u⁻¹ * wC⁻¹) * wC := by group
            _ = zC * wC := by rw [h]
        have hz2 : zC ^ 2 = 1 := by rw [← orderOf_dvd_iff_pow_eq_one, orderOf_zC]
        have hzc : Commute zC wC := (Subgroup.mem_center_iff.1 zC_mem_center wC).symm
        have hz1 : zC = 1 := eq_one_of_conj_eq_mul (G := lyC) hz2 hzc hwC5 h1
        have h2 := orderOf_zC
        rw [hz1, orderOf_one] at h2
        omega
    have hcuJ : (u : J) * w = w * (u : J) := by
      have h := congrArg Subtype.val hcu
      simpa [wC] using h
    have hβu : β u = u := Subtype.ext (by rw [hβapp]; exact hfix _ u.2 hcuJ)
    have h1 := hσapp ⟨g, hgA⟩
    have h2 : γ ⟨g, hgA⟩ = ⟨g, hgA⟩ := by
      rw [← hū, hγmk, hβu]
    rw [h2] at h1
    change g = σ * g * σ⁻¹ at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1.symm).symm
  have hσ1 : σ = 1 := by
    refine eq_one_of_commute_even_centralizer (imgC wC) σ ?_ hσσ hcomm
    rw [← map_pow, hwC5, map_one]
  have hγ1 : ∀ g : alternatingGroup (Fin 11), γ g = g := by
    intro g
    apply Subtype.ext
    rw [hσapp, hσ1]
    simp
  have hβ1 : β = 1 := by
    apply eq_one_of_trivial_on_quotient zGroup zGroup_le_center commutator_lyC β
    intro c
    rw [← imgC_eq_one_iff, map_mul, map_inv]
    have h1 : imgC (β c) = imgC c := by
      rw [imgC_apply, imgC_apply, ← hγmk, hγ1]
    rw [h1, inv_mul_cancel]
  have hfixC : ∀ c ∈ lyC, α c = c := by
    intro c hc
    have := congrArg (fun f : MulAut lyC => ((f ⟨c, hc⟩ : lyC) : J)) hβ1
    simpa [hβapp] using this
  rcases fixes_C_cases hfixC with h | h
  · exact ⟨1, by rw [h, map_one]⟩
  · exact ⟨lyz, h.symm⟩

theorem hpt_J
    {w : J} (hw : orderOf w = 5)
    (hev : ∃ u : J, orderOf u = 2 ∧ u * w = w * u) {v : MulAut J} (hv : v * v = 1)
    (hfix : ∀ g ∈ Subgroup.centralizer ({w} : Set J), v g = g) :
    ∃ x : J, MulAut.conj x = v := by
  obtain ⟨u, hu, huw⟩ := hev
  obtain ⟨g, hg⟩ := (involution_centralizer_fusion_generator.2 u hu)
  have hvu : v u = u := hfix u (Subgroup.mem_centralizer_singleton_iff.2 huw)
  have htw := exists_twist g hv
  obtain ⟨α, hαx, hα2, hback⟩ := htw
  have hgu : g⁻¹ * u * g = lyz := by
    rw [← hg]; group
  have hαz : α lyz = lyz := by
    rw [hαx, hg, hvu, hgu]
  have hwg : (g * lyz * g⁻¹) * w = w * (g * lyz * g⁻¹) := by rw [hg]; exact huw
  have hwC : g⁻¹ * w * g ∈ lyC := by
    rw [lyC_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    calc (g⁻¹ * w * g) * lyz = g⁻¹ * (w * (g * lyz * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * lyz * g⁻¹) * w) * g := by rw [hwg]
      _ = lyz * (g⁻¹ * w * g) := by group
  have hw' : orderOf (g⁻¹ * w * g) = 5 := (orderOf_conj_inv g w).trans hw
  have hfix' : ∀ c ∈ lyC, c * (g⁻¹ * w * g) = (g⁻¹ * w * g) * c → α c = c := by
    intro c _ hc
    have hmem : g * c * g⁻¹ ∈ Subgroup.centralizer ({w} : Set J) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (g * c * g⁻¹) * w = g * (c * (g⁻¹ * w * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * w * g) * c) * g⁻¹ := by rw [hc]
        _ = w * (g * c * g⁻¹) := by group
    rw [hαx, hfix _ hmem]
    group
  obtain ⟨x, hx⟩ := inner_of_fixes_C_centralizer hwC hw' hαz hα2 hfix'
  exact ⟨g * x * g⁻¹, hback x hx⟩

end CFSG.RankThree.PartOne.LyFive
