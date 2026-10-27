module

public import CFSG.LocalAnalysis.StandardType.GGPZTrivUAll
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggPZ_twA_torus
    {G : Type} [Group G] [Finite G] {p l n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {J EJ : Subgroup G} (hl : 2 ≤ l) (hpq : p ∣ 2 ^ n + 1) (hpl : p ∣ l + 3)
    (hJ : GGHasLabel ⟨.twA, l, n⟩ (↥J ⧸ Subgroup.center ↥J)) (_hJq : IsQuasisimple ↥J)
    (hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J)) (hEJ : EJ ≤ J) (hE : IsElemAbelian p EJ)
    (hcard : Nat.card ↥EJ = p ^ l) :
    ∃ θ : ↥(UCoord.sumZero (l + 1) p) →* G, Function.Injective θ ∧ θ.range = EJ ∧
      ∀ g ∈ J, g ∈ Subgroup.normalizer (EJ : Set G) →
        ∃ π : Equiv.Perm (Fin (l + 1)), ∀ f, g * θ f * g⁻¹ = θ (UCoord.permAutV π f) := by
  classical
  have hp : p.Prime := Fact.out
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
  have hcardE : Nat.card ↥E = p ^ (l + 1 - 1) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, hcardEJ']
    norm_num
  obtain ⟨τ, hτinj, hτrange, hτnorm⟩ :=
    UModel.ggTorusPermElt_unitary_of_card (K := K) (n := n) (d := l + 1) (p := p)
      hKcard hn (by omega) hp hp2 hpq hpl1 hEab hcardE
  let ιE : ↥(UCoord.sumZero (l + 1) p) ≃* ↥E :=
    (MonoidHom.ofInjective hτinj).trans (MulEquiv.subgroupCongr hτrange)
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
  refine ⟨θ, hθinj, hθrange, ?_⟩
  intro g hgJ hgN
  let g' : ↥J := ⟨g, hgJ⟩
  have hgN' : ∀ h : G, h ∈ EJ ↔ g * h * g⁻¹ ∈ EJ :=
    Subgroup.mem_normalizer_iff.mp hgN
  have hg''norm : ∀ e ∈ E, π g' * e * (π g')⁻¹ ∈ E := by
    intro e he
    rw [MonoidHom.mem_range] at he
    obtain ⟨y, rfl⟩ := he
    refine MonoidHom.mem_range.mpr ⟨⟨g' * y * g'⁻¹, ?_⟩, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      have hyG : ((y : ↥J) : G) ∈ EJ := Subgroup.mem_subgroupOf.mp y.2
      have h := (hgN' ((y : ↥J) : G)).mp hyG
      simpa using h
    · change π (g' * (y : ↥J) * g'⁻¹) = π g' * π (y : ↥J) * (π g')⁻¹
      rw [map_mul, map_mul, map_inv]
  obtain ⟨π₀, hπ₀⟩ := hτnorm (π g') hg''norm
  refine ⟨π₀, ?_⟩
  intro f
  have hθf : θ f ∈ EJ := by
    rw [← hθrange]
    exact MonoidHom.mem_range.mpr ⟨f, rfl⟩
  have hleft : g * θ f * g⁻¹ ∈ EJ := (hgN' (θ f)).mp hθf
  have hright : θ (UCoord.permAutV π₀ f) ∈ EJ := by
    rw [← hθrange]
    exact MonoidHom.mem_range.mpr ⟨UCoord.permAutV π₀ f, rfl⟩
  let a : ↥J := ⟨g * θ f * g⁻¹, hEJ hleft⟩
  let b : ↥J := ⟨θ (UCoord.permAutV π₀ f), hEJ hright⟩
  have hπab : π a = π b := by
    have ha : π a = π g' * τ f * (π g')⁻¹ := by
      change π (g' * (⟨((ι f : ↥EJ) : G), hEJ (ι f).2⟩ : ↥J) * g'⁻¹)
        = π g' * τ f * (π g')⁻¹
      rw [map_mul, map_mul, map_inv, hθfπ f]
    have hb : π b = τ (UCoord.permAutV π₀ f) := by
      change π (⟨((ι (UCoord.permAutV π₀ f) : ↥EJ) : G),
        hEJ (ι (UCoord.permAutV π₀ f)).2⟩ : ↥J) = _
      exact hθfπ (UCoord.permAutV π₀ f)
    exact ha.trans ((hπ₀ f).trans hb.symm)
  have hab : a = b := hπinjEJ a b hleft hright hπab
  simpa [a, b] using congrArg (fun z : ↥J => (z : G)) hab

end CFSG.StandardType

end
