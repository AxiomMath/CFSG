module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosure
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Defs
public import CFSG.LocalAnalysis.StandardType.GGPZTrivUAll
public import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem pft_forall_permAutV_eq_one {d p : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d)
    (hd : 0 < d) {v : ↥(UCoord.sumZero d p)}
    (hv : ∀ σ : Equiv.Perm (Fin d), UCoord.permAutV σ v = v) : v = 1 := by
  have hconst : ∀ k l : Fin d, UCoord.crd v k = UCoord.crd v l := by
    intro k l
    by_cases hkl : k = l
    · rw [hkl]
    · have h := UCoord.crd_apply_eq_of_fix (hv (Equiv.swap k l)) k
      rw [Equiv.swap_apply_left] at h
      exact h.symm
  have hsum : ∑ k : Fin d, UCoord.crd v k = 0 := UCoord.sum_crd v
  have hzero : UCoord.crd v ⟨0, hd⟩ = 0 := by
    have h1 : (d : ZMod p) * UCoord.crd v ⟨0, hd⟩ = 0 := by
      calc (d : ZMod p) * UCoord.crd v ⟨0, hd⟩
          = (Finset.univ.card : ℕ) • UCoord.crd v ⟨0, hd⟩ := by
            rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = ∑ _k : Fin d, UCoord.crd v ⟨0, hd⟩ := (Finset.sum_const _).symm
        _ = ∑ k : Fin d, UCoord.crd v k :=
            Finset.sum_congr rfl fun k _ => (hconst k ⟨0, hd⟩).symm
        _ = 0 := hsum
    have : Fact p.Prime := ⟨hp⟩
    have hd0 : (d : ZMod p) ≠ 0 := by
      intro h0
      exact hpd ((ZMod.natCast_eq_zero_iff d p).mp h0)
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hd0
    · exact h
  refine UCoord.ext_crd fun k => ?_
  rw [UCoord.crd_one]
  exact (hconst k ⟨0, hd⟩).trans hzero

theorem ggPZ_fixed_trivial_twA
    {G : Type} [Group G] [Finite G] {p l n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {J EJ : Subgroup G} (hl : 2 ≤ l) (hpq : p ∣ 2 ^ n + 1) (hpl : p ∣ l + 3)
    (hJ : GGHasLabel ⟨.twA, l, n⟩ (↥J ⧸ Subgroup.center ↥J)) (_hJq : IsQuasisimple ↥J)
    (hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J)) (hEJ : EJ ≤ J) (hE : IsElemAbelian p EJ)
    (hcard : Nat.card ↥EJ = p ^ l) :
    ∀ a ∈ EJ, (∀ g ∈ J, g ∈ Subgroup.normalizer (EJ : Set G) → g * a * g⁻¹ = a) → a = 1 := by
  classical
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  have hn : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst hn0
    have hdvd : p ∣ 2 := by simpa using hpq
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  have hpl1 : ¬ p ∣ l + 1 := by
    intro h
    have hsub : p ∣ (l + 3) - (l + 1) := Nat.dvd_sub hpl h
    have h2 : p ∣ 2 := by
      rw [show (l + 3) - (l + 1) = 2 from by omega] at hsub
      exact hsub
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  unfold GGHasLabel at hJ
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hJ
  unfold LargeEvenRecipeUnitary at hJ
  obtain ⟨K, hKfld, hKfin, hKcard, ⟨e⟩⟩ := hJ
  let R := LargeEvenProj (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n))
  let π : ↥J →* R := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥J))
  let EJ' : Subgroup ↥J := EJ.subgroupOf J
  let φ : EJ' →* R := π.comp EJ'.subtype
  let E : Subgroup R := φ.range
  have hφinj : Function.Injective φ := by
    intro a b hab
    change π (a : ↥J) = π (b : ↥J) at hab
    let w : ↥J := (a : ↥J) * (b : ↥J)⁻¹
    have hπw : π w = 1 := by
      change π ((a : ↥J) * (b : ↥J)⁻¹) = 1
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have hmk : (QuotientGroup.mk' (Subgroup.center ↥J)) w = 1 := by
      apply e.injective
      simpa [π, MonoidHom.comp_apply] using hπw
    have hwcenter : w ∈ Subgroup.center ↥J := by
      rw [← QuotientGroup.eq_one_iff]
      simpa [QuotientGroup.mk'_apply] using hmk
    have hwmem : ((w : ↥J) : G) ∈ EJ := by
      change ((a : ↥J) : G) * ((b : ↥J) : G)⁻¹ ∈ EJ
      exact EJ.mul_mem (Subgroup.mem_subgroupOf.mp a.2)
        (EJ.inv_mem (Subgroup.mem_subgroupOf.mp b.2))
    have hwp : w ^ p = 1 := by
      apply Subtype.ext
      have hEp := hE.2 ((w : ↥J) : G) hwmem
      simpa using hEp
    have ho1 : orderOf w ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hwp
    have hzp : Subgroup.zpowers w ≤ Subgroup.center ↥J := by
      rw [Subgroup.zpowers_le]
      exact hwcenter
    have ho2 : orderOf w ∣ Nat.card ↥(Subgroup.center ↥J) := by
      rw [← Nat.card_zpowers w]
      exact Subgroup.card_dvd_of_le hzp
    have hcop : Nat.Coprime p (Nat.card ↥(Subgroup.center ↥J)) :=
      (hp.coprime_iff_not_dvd).mpr hZ
    have hone : orderOf w = 1 := Nat.eq_one_of_dvd_coprimes hcop ho1 ho2
    have hw1 : w = 1 := orderOf_eq_one_iff.mp hone
    exact Subtype.ext (mul_inv_eq_one.mp hw1)
  have hπinjEJ : ∀ a b : ↥J, ((a : G) ∈ EJ) → ((b : G) ∈ EJ) →
      π a = π b → a = b := by
    intro a b ha hb hab
    let a' : EJ' := ⟨a, Subgroup.mem_subgroupOf.mpr ha⟩
    let b' : EJ' := ⟨b, Subgroup.mem_subgroupOf.mpr hb⟩
    have h' : (a' : ↥J) = (b' : ↥J) :=
      congrArg (fun z : EJ' => (z : ↥J)) (hφinj hab)
    simpa [a', b'] using h'
  have hEJ'comm : IsMulCommutative EJ' := by
    rw [isMulCommutative_iff]
    intro x y
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    simpa using congrArg Subtype.val (isMulCommutative_iff.mp hE.1
      ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
      ⟨(y : G), Subgroup.mem_subgroupOf.mp y.2⟩)
  have hEab : IsElemAbelian p E := by
    refine ⟨?_, ?_⟩
    · rw [isMulCommutative_iff]
      intro x y
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      obtain ⟨x', hx'⟩ := MonoidHom.mem_range.mp x.2
      obtain ⟨y', hy'⟩ := MonoidHom.mem_range.mp y.2
      rw [← hx', ← hy', ← map_mul, ← map_mul, isMulCommutative_iff.mp hEJ'comm x' y']
    · intro x hx
      obtain ⟨x', hx'⟩ := MonoidHom.mem_range.mp hx
      rw [← hx', ← map_pow]
      have hx'p : x' ^ p = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        change (((x' : ↥J) : G)) ^ p = 1
        exact hE.2 ((x' : ↥J) : G) (Subgroup.mem_subgroupOf.mp x'.2)
      rw [hx'p, map_one]
  have hcardEJ' : Nat.card ↥EJ' = p ^ l := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv, hcard]
  have hcardE : Nat.card ↥E = p ^ l := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, hcardEJ']
  obtain ⟨E', hEE', hE', hsc⟩ := A6InsideSp.exists_elemAbelian_le_selfCentralizing hp hEab
  obtain ⟨τ, hτinj, hτrange, hτperm, -⟩ :=
    UModel.ggTorusPermEltSCAll_unitary (K := K) (n := n) (d := l + 1) (p := p)
      hKcard hn (by omega) hp hp2 hpq hpl1 E' hE' hsc
  have hcardE'le : Nat.card ↥E' ≤ p ^ l := by
    rw [← hτrange, Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv.symm]
    exact UCoord.card_sumZero_le l p
  have hE'E : E' = E :=
    (Subgroup.eq_of_le_of_card_ge hEE' (by rw [hcardE]; exact hcardE'le)).symm
  have hτrange' : τ.range = E := hτrange.trans hE'E
  let ιE : ↥(UCoord.sumZero (l + 1) p) ≃* ↥E :=
    (MonoidHom.ofInjective hτinj).trans (MulEquiv.subgroupCongr hτrange')
  let ι₂ : ↥E ≃* EJ' := (MonoidHom.ofInjective hφinj).symm
  let ι₃ : EJ' ≃* ↥EJ := Subgroup.subgroupOfEquivOfLe hEJ
  let ι : ↥(UCoord.sumZero (l + 1) p) ≃* ↥EJ := ιE.trans (ι₂.trans ι₃)
  let θ : ↥(UCoord.sumZero (l + 1) p) →* G := EJ.subtype.comp ι.toMonoidHom
  have hθrange : θ.range = EJ := by
    change (EJ.subtype.comp ι.toMonoidHom).range = EJ
    rw [MonoidHom.range_comp]
    have htop : ι.toMonoidHom.range = ⊤ := by
      rw [MonoidHom.range_eq_top]
      exact ι.surjective
    rw [htop, Subgroup.map_top, Subgroup.range_subtype]
  have hθinj : Function.Injective θ := by
    intro a b hab
    exact ι.injective (Subtype.ext hab)
  have hθmem : ∀ f, θ f ∈ EJ := by
    intro f
    rw [← hθrange]
    exact MonoidHom.mem_range.mpr ⟨f, rfl⟩
  have hιE_coe : ∀ f, (ιE f : R) = τ f := fun _ => rfl
  have hι₂_φ : ∀ x : ↥E, φ (ι₂ x) = (x : R) := by
    intro x
    have h := (MonoidHom.ofInjective hφinj).apply_symm_apply x
    exact congrArg Subtype.val h
  have hθfπ : ∀ f, π (⟨((ι f : ↥EJ) : G), hEJ (ι f).2⟩ : ↥J) = τ f := by
    intro f
    have h1 : (⟨((ι f : ↥EJ) : G), hEJ (ι f).2⟩ : ↥J)
        = (⟨((ι₂ (ιE f) : EJ') : G), hEJ (ι₂ (ιE f)).2⟩ : ↥J) := rfl
    rw [h1]
    change φ (ι₂ (ιE f)) = τ f
    rw [hι₂_φ, hιE_coe]
  have hπsurj : Function.Surjective π := by
    intro w
    obtain ⟨y, hy⟩ := e.surjective w
    obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective (N := Subgroup.center ↥J) y
    refine ⟨z, ?_⟩
    change e (QuotientGroup.mk' (Subgroup.center ↥J) z) = w
    rw [hz]
    exact hy
  have hfwd_gen : ∀ (u : ↥J), π u ∈ Subgroup.normalizer (E : Set R) → ∀ x : G, x ∈ EJ →
      (u : G) * x * (u : G)⁻¹ ∈ EJ := by
    intro u huE x hx
    let xJ : ↥J := ⟨x, hEJ hx⟩
    have hxJ' : xJ ∈ EJ' := Subgroup.mem_subgroupOf.mpr hx
    have hπxE : π xJ ∈ E := MonoidHom.mem_range.mpr ⟨⟨xJ, hxJ'⟩, rfl⟩
    have hπE : π (u * xJ * u⁻¹) ∈ E := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp huE (π xJ)).mp hπxE
    obtain ⟨y, hyeq⟩ := MonoidHom.mem_range.mp hπE
    let yJ : ↥J := (y : ↥J)
    have hyJ' : yJ ∈ EJ' := y.2
    let z : ↥J := (u * xJ * u⁻¹) * yJ⁻¹
    have hz : z ∈ Subgroup.center ↥J := by
      have hyφ : π yJ = φ y := rfl
      have hπ1 : π ((u * xJ * u⁻¹) * yJ⁻¹) = 1 := by
        rw [map_mul, map_inv, hyφ, ← hyeq, mul_inv_cancel]
      have h1 : (QuotientGroup.mk' (Subgroup.center ↥J))
          ((u * xJ * u⁻¹) * yJ⁻¹) = 1 := by
        apply e.injective
        simpa [π, MonoidHom.comp_apply] using hπ1
      change (u * xJ * u⁻¹) * yJ⁻¹ ∈ Subgroup.center ↥J
      rw [← QuotientGroup.eq_one_iff]
      simpa [QuotientGroup.mk'_apply] using h1
    have hdecomp : u * xJ * u⁻¹ = z * yJ := by
      change u * xJ * u⁻¹ = ((u * xJ * u⁻¹) * yJ⁻¹) * yJ
      group
    have hup : (u * xJ * u⁻¹) ^ p = 1 := by
      have hxJp : xJ ^ p = 1 := by
        apply Subtype.ext
        change (xJ : G) ^ p = 1
        exact hE.2 x hx
      calc (u * xJ * u⁻¹) ^ p = ((MulAut.conj u) xJ) ^ p := by rw [MulAut.conj_apply]
        _ = (MulAut.conj u) (xJ ^ p) := (map_pow _ _ _).symm
        _ = 1 := by rw [hxJp, map_one]
    have hyp : yJ ^ p = 1 := by
      apply Subtype.ext
      change (yJ : G) ^ p = 1
      exact hE.2 (yJ : G) (Subgroup.mem_subgroupOf.mp hyJ')
    have hcomm : Commute z yJ := (Subgroup.mem_center_iff.mp hz yJ).symm
    have hzp : z ^ p = 1 := by
      have h1 : (z * yJ) ^ p = 1 := by rw [← hdecomp]; exact hup
      rw [hcomm.mul_pow p, hyp, mul_one] at h1
      exact h1
    have hz1 : z = 1 := by
      have ho1 : orderOf z ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hzp
      have hzp' : Subgroup.zpowers z ≤ Subgroup.center ↥J := by
        rw [Subgroup.zpowers_le]
        exact hz
      have ho2 : orderOf z ∣ Nat.card ↥(Subgroup.center ↥J) := by
        rw [← Nat.card_zpowers]
        exact Subgroup.card_dvd_of_le hzp'
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
        ((hp.coprime_iff_not_dvd).mpr hZ) ho1 ho2)
    have hmem : u * xJ * u⁻¹ ∈ EJ' := by
      rw [hdecomp, hz1, one_mul]
      exact hyJ'
    exact Subgroup.mem_subgroupOf.mp hmem
  have hgN_of_pi : ∀ (g : ↥J), π g ∈ Subgroup.normalizer (E : Set R) →
      (g : G) ∈ Subgroup.normalizer (EJ : Set G) := by
    intro g hgE
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hfwd_gen g hgE x, fun hx => ?_⟩
    have hgEinv : π g⁻¹ ∈ Subgroup.normalizer (E : Set R) := by
      rw [map_inv]
      exact Subgroup.inv_mem _ hgE
    have h := hfwd_gen g⁻¹ hgEinv ((g : G) * x * (g : G)⁻¹) hx
    simpa [mul_assoc] using h
  intro a ha hfix
  obtain ⟨v, hv⟩ : ∃ v : ↥(UCoord.sumZero (l + 1) p), θ v = a := by
    rw [← hθrange] at ha
    exact MonoidHom.mem_range.mp ha
  have hfixv : ∀ σ : Equiv.Perm (Fin (l + 1)), UCoord.permAutV σ v = v := by
    intro σ
    obtain ⟨w, hw⟩ := hτperm σ
    have hwE1 : ∀ e ∈ E, w * e * w⁻¹ ∈ E := by
      intro e he
      have he' : e ∈ τ.range := by rw [hτrange']; exact he
      obtain ⟨f, rfl⟩ := he'
      rw [← hτrange']
      exact ⟨UCoord.permAutV σ f, (hw f).symm⟩
    have hwE2 : ∀ e ∈ E, w⁻¹ * e * w ∈ E := by
      intro e he
      have he' : e ∈ τ.range := by rw [hτrange']; exact he
      obtain ⟨f, rfl⟩ := he'
      have hper : UCoord.permAutV σ (UCoord.permAutV σ⁻¹ f) = f := by
        rw [← MulAut.mul_apply, ← UCoord.permAutV_mul, mul_inv_cancel, UCoord.permAutV_one,
          MulAut.one_apply]
      have h1 : w * τ (UCoord.permAutV σ⁻¹ f) * w⁻¹ = τ f := by
        have h2 := hw (UCoord.permAutV σ⁻¹ f)
        rwa [hper] at h2
      have hgoal : w⁻¹ * τ f * w = τ (UCoord.permAutV σ⁻¹ f) := by
        rw [← h1]
        group
      rw [hgoal, ← hτrange']
      exact ⟨UCoord.permAutV σ⁻¹ f, rfl⟩
    have hwE : w ∈ Subgroup.normalizer (E : Set R) := by
      rw [Subgroup.mem_normalizer_iff]
      intro e
      exact ⟨hwE1 e, fun he => by
        have h := hwE2 (w * e * w⁻¹) he
        simpa [mul_assoc] using h⟩
    obtain ⟨g, hg⟩ := hπsurj w
    have hgN' : π g ∈ Subgroup.normalizer (E : Set R) := by rw [hg]; exact hwE
    have hgN : (g : G) ∈ Subgroup.normalizer (EJ : Set G) := hgN_of_pi g hgN'
    have hact : ∀ f, (g : G) * θ f * (g : G)⁻¹ = θ (UCoord.permAutV σ f) := by
      intro f
      have hleft : (g : G) * θ f * (g : G)⁻¹ ∈ EJ :=
        (Subgroup.mem_normalizer_iff.mp hgN (θ f)).mp (hθmem f)
      have hright : θ (UCoord.permAutV σ f) ∈ EJ := hθmem _
      let a' : ↥J := ⟨(g : G) * θ f * (g : G)⁻¹, hEJ hleft⟩
      let b' : ↥J := ⟨θ (UCoord.permAutV σ f), hEJ hright⟩
      have hπab : π a' = π b' := by
        have ha' : π a' = w * τ f * w⁻¹ := by
          change π (g * (⟨((ι f : ↥EJ) : G), hEJ (ι f).2⟩ : ↥J) * g⁻¹)
            = w * τ f * w⁻¹
          rw [map_mul, map_mul, map_inv, hg, hθfπ f]
        have hb' : π b' = τ (UCoord.permAutV σ f) := hθfπ _
        exact ha'.trans ((hw f).trans hb'.symm)
      have hab : a' = b' := hπinjEJ a' b' hleft hright hπab
      exact congrArg (fun z : ↥J => (z : G)) hab
    have h1 : (g : G) * a * (g : G)⁻¹ = a := hfix (g : G) g.2 hgN
    rw [← hv] at h1
    have h2 : θ (UCoord.permAutV σ v) = θ v := by
      rw [← hact v, h1]
    exact hθinj h2
  have hv1 : v = 1 :=
    pft_forall_permAutV_eq_one hp hpl1 (by omega) hfixv
  rw [← hv, hv1, map_one]

end CFSG.StandardType

end
