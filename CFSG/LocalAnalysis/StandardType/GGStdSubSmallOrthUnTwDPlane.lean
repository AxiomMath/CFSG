module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnFixed
public import CFSG.LinearAlgebra.CoprimeActions.AbelianFixedFreeLinearCyclic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.TwistedConfig
public import CFSG.RankThree.PartOne.K159.RowFourFixed
public import CFSG.RankThree.PartOne.KFR4.Frame
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel

public section

namespace CFSG.StandardType

namespace SmallOrthUn

open Module Polynomial CFSG.Assembly CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2 OrthRestOdd SmallOrth
  CFSG.RankThree.PartOne.K159 CFSG.GroupTheory.WeirSylow
  CFSG.LinearAlgebra.CoprimeActions.AbelianFixedFreeLinearCyclic
  CFSG.LocalAnalysis.GLTheoremA.H81Orth

section Plane

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem eq_one_of_pow_of_plus_plane {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {QW : QuadraticForm K W}
    (hreg : (QuadraticMap.polarBilin QW).Nondegenerate) (hdim : finrank K W = 2)
    (hplus : IsPlusType QW) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    (τ : W ≃ₗ[K] W) (hτ : τ ∈ TauCeti.QuadraticMap.orthogonalGroup QW) (hτp : τ ^ p = 1) :
    τ = 1 := by
  classical
  have hN := natCard_orthogonalGroup_of_type (K := K) hreg (m := 0) (by omega) (ε := 1)
    (Or.inl ⟨rfl, hplus⟩)
  simp only [pow_zero, mul_one, zero_add, pow_one] at hN
  rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) from by decide, Finset.prod_empty, mul_one] at hN
  have : Fact p.Prime := ⟨hp⟩
  by_contra hne
  set N := Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup QW) with hNdef
  let τ' : ↥(TauCeti.QuadraticMap.orthogonalGroup QW) := ⟨τ, hτ⟩
  have hτ'p : τ' ^ p = 1 := Subtype.ext hτp
  have hord : orderOf τ' = p := orderOf_eq_prime hτ'p fun h => hne (congrArg Subtype.val h)
  have hdvd : p ∣ N := hord ▸ orderOf_dvd_natCard τ'
  have h1 : (p : ℤ) ∣ 2 * ((Nat.card K : ℤ) - 1) := by
    rw [← hN]
    exact Int.natCast_dvd_natCast.mpr hdvd
  have h2 : (p : ℤ) ∣ (Nat.card K : ℤ) + 1 := by exact_mod_cast hpq
  have h3 : (p : ℤ) ∣ 4 := by
    have h4 := (h2.mul_left 2).sub h1
    have e : 2 * ((Nat.card K : ℤ) + 1) - 2 * ((Nat.card K : ℤ) - 1) = 4 := by ring
    rwa [e] at h4
  have h4 : p ∣ 4 := by exact_mod_cast h3
  have h5 : p ∣ 2 := hp.dvd_of_dvd_pow (n := 2) (by norm_num; exact h4)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h5)

omit [Finite K] in
theorem isoGroup_of_orth {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ} {T : Subgroup (V ≃ₗ[K] V)}
    (hTO : T ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hTc : ∀ g ∈ T, ∀ h ∈ T, g * h = h * g)
    (hTp : ∀ g ∈ T, g ^ p = 1) : IsoGroup (QuadraticMap.polarBilin Q) p T where
  sep := hQ.1
  alt := fun v => by
    rw [QuadraticMap.polarBilin_apply_apply]
    exact polar_self_eq_zero Q v
  comm := hTc
  pow := hTp
  pres := fun g hg u w => by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hTO hg) u w

theorem card_le_of_four_minus {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {QW : QuadraticForm K W} (hreg : (QuadraticMap.polarBilin QW).Nondegenerate)
    (hdim : finrank K W = 4) (hV : ¬ IsPlusType QW) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (T : Subgroup (W ≃ₗ[K] W))
    (hTO : T ≤ TauCeti.QuadraticMap.orthogonalGroup QW) (hTc : ∀ g ∈ T, ∀ h ∈ T, g * h = h * g)
    (hTp : ∀ g ∈ T, g ^ p = 1) : Nat.card T ≤ p := by
  classical
  by_contra hlt
  push Not at hlt
  have : Fact p.Prime := ⟨hp⟩
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) := finite_linearEquiv
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_odd hp hp2
  have hIso : IsoGroup (QuadraticMap.polarBilin QW) p T := isoGroup_of_orth hreg hTO hTc hTp
  by_cases hfree : ∀ g ∈ T, g ≠ 1 → ∀ v : W, g v = v → v = 0
  ·
    have : IsMulCommutative ↥T :=
      IsMulCommutative.of_comm fun a b => Subtype.ext (hTc a a.2 b b.2)
    have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
    have hcyc : IsCyclic ↥T :=
      isCyclic_of_fixedFree
        ((LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := K) (M := W)).comp
          T.subtype) fun a ha v hv =>
            hfree (a : W ≃ₗ[K] W) a.2 (fun h1 => ha (Subtype.ext h1)) v hv
    have := CFSG.StandardType.TableB.card_le_of_isCyclic hp.pos hcyc fun y hy => hTp y hy
    omega
  ·
    push Not at hfree
    obtain ⟨g, hgT, hg1, v, hvC, hv0⟩ := hfree
    have hx : OddOrderIsometry QW p g :=
      ⟨hTO hgT, hTp g hgT, hpK, fun v hv => hreg.1 v fun w => by
        rw [QuadraticMap.polarBilin_apply_apply]; exact hv w⟩
    obtain ⟨hcompl, horth⟩ := hx.fixed_others
    set C := fixedSpace g with hC
    set R := othersSpace g.toLinearMap (X - 1) with hR
    have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
    have hCbot : C ≠ ⊥ := by
      intro hCb
      apply hv0
      have hv : v ∈ C := by rw [hC]; exact mem_fixedSpace.2 hvC
      rw [hCb] at hv
      simpa using hv
    have hRbot : R ≠ ⊥ := by
      intro hRb
      apply hg1
      have hW' : C = ⊤ := by
        have := hcompl.sup_eq_top
        rwa [hRb, sup_bot_eq] at this
      ext v
      have : v ∈ C := hW' ▸ Submodule.mem_top
      exact mem_fixedSpace.1 this
    have hRinv : ∀ u ∈ R, g u ∈ R := by
      intro u hu
      have hmap : R.map g.toLinearMap ≤ R := by
        rw [hR]
        unfold othersSpace
        rw [Submodule.map_iSup]
        refine iSup_le fun k => ?_
        rw [Submodule.map_iSup]
        refine iSup_le fun hk => ?_
        refine le_iSup₂_of_le k hk ?_
        rintro _ ⟨v, hv, rfl⟩
        exact apply_mem_primaryComponent (Commute.refl _) hv
      exact hmap ⟨u, hu, rfl⟩
    have hRfix : ∀ u ∈ R, g u = u → u = 0 := by
      intro u hu hxu
      have hW' : u ∈ C := mem_fixedSpace.2 hxu
      exact (Submodule.disjoint_def.1 hcompl.disjoint) u hW' hu
    have hRreg : RegOn QW R := by
      intro u hu hperp
      refine hx.regular u fun v => ?_
      obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hcompl v
      rw [QuadraticMap.polar_add_right, hperp r hr, QuadraticMap.polar_comm QW u w,
        horth w hw u hu, add_zero]
    have hR2 : Even (finrank K R) := by
      have : Even (finrank K C + finrank K R) := by rw [hsum, hdim]; exact ⟨2, rfl⟩
      exact (Nat.even_add.1 this).1 hx.even_finrank_fixed
    obtain ⟨k, hk⟩ := hR2
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · exact absurd (Submodule.finrank_eq_zero.1 (by omega : finrank K R = 0)) hRbot
      · exact h0
    have hCpos : 0 < finrank K C := by
      by_contra h0
      exact hCbot (Submodule.finrank_eq_zero.1 (by omega))
    have hRdim : finrank K R = 2 := by
      obtain ⟨m, hm⟩ := hx.even_finrank_fixed
      omega
    have hCdim : finrank K C = 2 := by omega
    have eV : QW.IsometryEquiv ((QW.comp C.subtype).prod (QW.comp R.subtype)) :=
      (isometryTop QW).trans ((isometryOfEq QW hcompl.sup_eq_top.symm).trans
        (isometryEquivSup QW C R hcompl.disjoint horth))
    have htype : IsPlusType QW ↔
        (IsPlusType (QW.comp C.subtype) ↔ IsPlusType (QW.comp R.subtype)) :=
      (isPlusType_congr eV).trans
        (isPlusType_prod_iff hx.polarBilin_fixed_nondegenerate (nondegenerate_of_regOn hRreg)
          (d₁ := 1) (d₂ := 1) le_rfl le_rfl (by omega) (by omega))
    have hnotiff : ¬ (IsPlusType (QW.comp C.subtype) ↔ IsPlusType (QW.comp R.subtype)) :=
      fun h => hV (htype.2 h)
    have hcent : ∀ t ∈ T, t ∈ Subgroup.centralizer ({g} : Set (W ≃ₗ[K] W)) := fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hTc t ht g hgT)
    have hCinv : ∀ t ∈ T, ∀ s ∈ C, t s ∈ C := fun t ht s hs =>
      mem_fixedSpace_of_apply (hcent t ht) hs
    have hRinv' : ∀ t ∈ T, ∀ s ∈ R, t s ∈ R := fun t ht s hs =>
      mem_othersSpace_of_apply (hcent t ht) hs
    have hresC_mem : ∀ t : T, resHom T C hCinv t ∈
        TauCeti.QuadraticMap.orthogonalGroup (QW.comp C.subtype) := by
      intro t
      refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun s => ?_
      change QW ((t : W ≃ₗ[K] W) (s : W)) = QW (s : W)
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hTO t.2) s
    have hresC_pow : ∀ t : T, (resHom T C hCinv t) ^ p = 1 := by
      intro t
      rw [← map_pow]
      have : t ^ p = 1 := Subtype.ext (hTp t t.2)
      rw [this, map_one]
    have hresR_mem : ∀ t : T, resHom T R hRinv' t ∈
        TauCeti.QuadraticMap.orthogonalGroup (QW.comp R.subtype) := by
      intro t
      refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun s => ?_
      change QW ((t : W ≃ₗ[K] W) (s : W)) = QW (s : W)
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hTO t.2) s
    have hresR_pow : ∀ t : T, (resHom T R hRinv' t) ^ p = 1 := by
      intro t
      rw [← map_pow]
      have : t ^ p = 1 := Subtype.ext (hTp t t.2)
      rw [this, map_one]
    have hgresR1 : resHom T R hRinv' ⟨g, hgT⟩ ≠ 1 := by
      intro h1
      apply hg1
      ext w
      change g w = w
      obtain ⟨c, hc, r, hr, rfl⟩ := exists_add_of_isCompl hcompl w
      have hgc : g c = c := mem_fixedSpace.1 hc
      have hgr : g r = r := by
        have h2 := congrArg (fun f : R ≃ₗ[K] R => ((f ⟨r, hr⟩ : R) : W)) h1
        simpa [resHom_apply] using h2
      rw [map_add, hgc, hgr]
    have htriv : ∀ t ∈ T, ∀ c ∈ C, t c = c := by
      intro t ht c hc
      by_contra htc
      have hresC1 : resHom T C hCinv ⟨t, ht⟩ ≠ 1 := by
        intro h1
        apply htc
        have h2 := congrArg (fun f : C ≃ₗ[K] C => ((f ⟨c, hc⟩ : C) : W)) h1
        simpa [resHom_apply] using h2
      have hCdiv := int_dvd_of_plane hx.polarBilin_fixed_nondegenerate hCdim hp hp2
        (hresC_mem ⟨t, ht⟩) (hresC_pow ⟨t, ht⟩) hresC1
      have hRdiv := int_dvd_of_plane (nondegenerate_of_regOn hRreg) hRdim hp hp2
        (hresR_mem ⟨g, hgT⟩) (hresR_pow ⟨g, hgT⟩) hgresR1
      have htwo : (p : ℤ) ∣ 2 := by
        by_cases hCplus : IsPlusType (QW.comp C.subtype)
        · have hRminus : ¬ IsPlusType (QW.comp R.subtype) := fun hRplus =>
            hnotiff ⟨fun _ => hRplus, fun _ => hCplus⟩
          have h4 := (hRdiv.2 hRminus).sub (hCdiv.1 hCplus)
          have e : ((Nat.card K : ℤ) + 1) - ((Nat.card K : ℤ) - 1) = 2 := by ring
          rwa [e] at h4
        · have hRplus : IsPlusType (QW.comp R.subtype) := by
            by_contra hRminus
            exact hnotiff ⟨fun hC => absurd hC hCplus, fun hR => absurd hR hRminus⟩
          have h4 := (hCdiv.2 hCplus).sub (hRdiv.1 hRplus)
          have e : ((Nat.card K : ℤ) + 1) - ((Nat.card K : ℤ) - 1) = 2 := by ring
          rwa [e] at h4
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (Int.natCast_dvd_natCast.mp htwo))
    have hinj : (resHom T R hRinv').ker = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro t ht
      have hR1 : ∀ r ∈ R, (t : W ≃ₗ[K] W) r = r := fun r hr =>
        congrArg Subtype.val (LinearEquiv.congr_fun (MonoidHom.mem_ker.mp ht) ⟨r, hr⟩)
      apply Subtype.ext
      apply LinearEquiv.ext
      intro w
      obtain ⟨c, hc, r, hr, rfl⟩ := exists_add_of_isCompl hcompl w
      rw [map_add, htriv t t.2 c hc, hR1 r hr]
      rfl
    have hcard : Nat.card T = Nat.card (resHom T R hRinv').range := by
      have := Subgroup.card_ker_mul_card_range (resHom T R hRinv')
      rw [hinj, Subgroup.card_bot, one_mul] at this
      exact this.symm
    have horth' : ∀ r ∈ R, ∀ c ∈ C, QuadraticMap.polarBilin QW r c = 0 := fun r hr c hc => by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
      exact horth c hc r hr
    have hb := card_res_le hp hpK hIso hcompl.symm hRinv' horth'
    rw [show finrank K R / 2 = 1 by omega, pow_one] at hb
    omega
end Plane

end SmallOrthUn

end CFSG.StandardType

end
