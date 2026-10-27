module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosure
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Defs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggPZ_fixed_trivial_D4
    {G : Type} [Group G] [Finite G] {n : ℕ} [Fact (Nat.Prime 3)]
    {J EJ : Subgroup G} (hpq : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1)
    (hJ : GGHasLabel ⟨.D, 4, n⟩ (↥J ⧸ Subgroup.center ↥J)) (_hJq : IsQuasisimple ↥J)
    (hZ : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥J)) (hEJ : EJ ≤ J) (hE : IsElemAbelian 3 EJ)
    (hcard : Nat.card ↥EJ = 3 ^ 4) :
    ∀ a ∈ EJ, (∀ g ∈ J, g ∈ Subgroup.normalizer (EJ : Set G) → g * a * g⁻¹ = a) → a = 1 := by
  classical
  intro a ha hfix
  have hp3 : Nat.Prime 3 := Nat.prime_three
  unfold GGHasLabel at hJ
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hJ
  unfold LargeEvenRecipeOmegaPlus at hJ
  obtain ⟨K, hKfld, hKfin, hKcard, ⟨e⟩⟩ := hJ
  have : Fintype K := Fintype.ofFinite K
  have hn : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst hn0
    have hcard1 : Nat.card K = 1 := by simpa using hKcard
    have hlt : 1 < Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    omega
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn hKcard
  let π : ↥J →* OrthRest.RPlus K 4 :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥J))
  let EJ' : Subgroup ↥J := EJ.subgroupOf J
  let φ : EJ' →* OrthRest.RPlus K 4 := π.comp EJ'.subtype
  let E : Subgroup (OrthRest.RPlus K 4) := φ.range
  have hφinj : Function.Injective φ := by
    intro x y hxy
    change π (x : ↥J) = π (y : ↥J) at hxy
    let w : ↥J := (x : ↥J) * (y : ↥J)⁻¹
    have hπw : π w = 1 := by
      change π ((x : ↥J) * (y : ↥J)⁻¹) = 1
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have hmk : (QuotientGroup.mk' (Subgroup.center ↥J)) w = 1 := by
      apply e.injective
      simpa [π, MonoidHom.comp_apply] using hπw
    have hwcenter : w ∈ Subgroup.center ↥J := by
      rw [← QuotientGroup.eq_one_iff]
      simpa [QuotientGroup.mk'_apply] using hmk
    have hwmem : ((w : ↥J) : G) ∈ EJ := by
      change ((x : ↥J) : G) * ((y : ↥J) : G)⁻¹ ∈ EJ
      exact EJ.mul_mem (Subgroup.mem_subgroupOf.mp x.2)
        (EJ.inv_mem (Subgroup.mem_subgroupOf.mp y.2))
    have hwp : w ^ 3 = 1 := by
      apply Subtype.ext
      have hEp := hE.2 ((w : ↥J) : G) hwmem
      simpa using hEp
    have ho1 : orderOf w ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hwp
    have hzp : Subgroup.zpowers w ≤ Subgroup.center ↥J := by
      rw [Subgroup.zpowers_le]
      exact hwcenter
    have ho2 : orderOf w ∣ Nat.card ↥(Subgroup.center ↥J) := by
      rw [← Nat.card_zpowers w]
      exact Subgroup.card_dvd_of_le hzp
    have hcop : Nat.Coprime 3 (Nat.card ↥(Subgroup.center ↥J)) :=
      (hp3.coprime_iff_not_dvd).mpr hZ
    have hone : orderOf w = 1 := Nat.eq_one_of_dvd_coprimes hcop ho1 ho2
    have hw1 : w = 1 := orderOf_eq_one_iff.mp hone
    exact Subtype.ext (mul_inv_eq_one.mp hw1)
  have hEJ'comm : IsMulCommutative EJ' := by
    rw [isMulCommutative_iff]
    intro x y
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    simpa using congrArg Subtype.val (isMulCommutative_iff.mp hE.1
      ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
      ⟨(y : G), Subgroup.mem_subgroupOf.mp y.2⟩)
  have hEab : IsElemAbelian 3 E := by
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
      have hx'p : x' ^ 3 = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        change (((x' : ↥J) : G)) ^ 3 = 1
        exact hE.2 ((x' : ↥J) : G) (Subgroup.mem_subgroupOf.mp x'.2)
      rw [hx'p, map_one]
  have hcardEJ' : Nat.card ↥EJ' = 3 ^ 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv, hcard]
  have hcardE : Nat.card ↥E = 3 ^ 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, hcardEJ']
  obtain ⟨E', hEE', hE', hscE'⟩ :=
    A6InsideSp.exists_elemAbelian_le_selfCentralizing hp3 hEab
  have hcond : 3 ∣ Nat.card K - 1 ∨ (Even 4 ∧ 3 ∣ Nat.card K + 1) := by
    rw [hKcard]
    rcases hpq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨by norm_num, h⟩
  have hT : GGTorusEvenSignedPermEltSC 3 (OrthRest.RPlus K 4) (fun k => k = 4) :=
    ggOrthEvenTorusInput_holds.1 K 4 3 (by norm_num) hp3 hcond
  have h3E' : 3 ^ 3 ≤ Nat.card ↥E' :=
    (by norm_num : 3 ^ 3 ≤ 3 ^ 4).trans (by
      rw [← hcardE]
      exact Subgroup.card_le_of_le hEE')
  obtain ⟨k, τ, hτinj, hτrange, hk4, hdinv, _, _⟩ := hT E' hE' h3E' hscE'
  subst hk4
  have hE'card : Nat.card ↥E' = 3 ^ 4 := by
    rw [← hτrange, Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv.symm,
      Nat.card_fun, Nat.card_fin]
    have h3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    rw [h3]
  have hE'E : E' = E := (Subgroup.eq_of_le_of_card_ge hEE' (by rw [hE'card, hcardE])).symm
  let ιE : (Fin 4 → Multiplicative (ZMod 3)) ≃* ↥E :=
    (MonoidHom.ofInjective hτinj).trans (MulEquiv.subgroupCongr (hτrange.trans hE'E))
  let ι₂ : ↥E ≃* EJ' := (MonoidHom.ofInjective hφinj).symm
  let ι₃ : EJ' ≃* ↥EJ := Subgroup.subgroupOfEquivOfLe hEJ
  let ι : (Fin 4 → Multiplicative (ZMod 3)) ≃* ↥EJ := ιE.trans (ι₂.trans ι₃)
  have hιE_coe : ∀ f, (ιE f : OrthRest.RPlus K 4) = τ f := fun _ => rfl
  have hι₂_φ : ∀ x : ↥E, φ (ι₂ x) = (x : OrthRest.RPlus K 4) := by
    intro x
    have h := (MonoidHom.ofInjective hφinj).apply_symm_apply x
    exact congrArg Subtype.val h
  have hιπ : ∀ f, π (⟨((ι f : ↥EJ) : G), hEJ (ι f).2⟩ : ↥J) = τ f := by
    intro f
    have h1 : (⟨((ι f : ↥EJ) : G), hEJ (ι f).2⟩ : ↥J)
        = (⟨((ι₂ (ιE f) : EJ') : G), hEJ (ι₂ (ιE f)).2⟩ : ↥J) := rfl
    rw [h1]
    change φ (ι₂ (ιE f)) = τ f
    rw [hι₂_φ, hιE_coe]
  have hτrangeE : τ.range = E := hτrange.trans hE'E
  have hπker : ∀ x : ↥J, π x = 1 ↔ x ∈ Subgroup.center ↥J := by
    intro x
    constructor
    · intro hx
      have hmk : QuotientGroup.mk' (Subgroup.center ↥J) x = 1 := by
        apply e.injective
        simpa [π, MonoidHom.comp_apply] using hx
      exact (QuotientGroup.eq_one_iff x).mp (by simpa [QuotientGroup.mk'_apply] using hmk)
    · intro hx
      have hmk : QuotientGroup.mk x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      simp [π, MonoidHom.comp_apply, QuotientGroup.mk'_apply, hmk]
  have hEJ'3 : ∀ x ∈ EJ', x ^ 3 = 1 := by
    intro x hx
    have h := hE.2 ((x : ↥J) : G) (Subgroup.mem_subgroupOf.mp hx)
    exact Subtype.ext (by simpa using h)
  have mem_EJ'_of : ∀ x : ↥J, π x ∈ E → x ^ 3 = 1 → x ∈ EJ' := by
    intro x hxE hx3
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (show π x ∈ φ.range from hxE)
    have hy' : π (y : ↥J) = π x := hy
    have hz : y⁻¹ * x ∈ Subgroup.center ↥J := by
      rw [← hπker]
      rw [map_mul, Subgroup.coe_inv, map_inv, hy', inv_mul_cancel]
    have hx_eq : x = (y : ↥J) * (y⁻¹ * x) := by
      rw [Subgroup.coe_inv]
      group
    have hcomm : Commute (y : ↥J) (y⁻¹ * x) :=
      Subgroup.mem_center_iff.mp hz (y : ↥J)
    have hz3 : (y⁻¹ * x) ^ 3 = 1 := by
      have h1 : ((y : ↥J) * (y⁻¹ * x)) ^ 3 = 1 := by rw [← hx_eq, hx3]
      rw [hcomm.mul_pow, hEJ'3 y y.2, one_mul] at h1
      exact h1
    have hcop : Nat.Coprime 3 (Nat.card ↥(Subgroup.center ↥J)) :=
      (hp3.coprime_iff_not_dvd).mpr hZ
    have ho1 : orderOf (y⁻¹ * x) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hz3
    have ho2 : orderOf (y⁻¹ * x) ∣ Nat.card ↥(Subgroup.center ↥J) := by
      rw [← Nat.card_zpowers (y⁻¹ * x)]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hz)
    have hone : orderOf (y⁻¹ * x) = 1 := Nat.eq_one_of_dvd_coprimes hcop ho1 ho2
    have hz1 : y⁻¹ * x = 1 := orderOf_eq_one_iff.mp hone
    rw [hx_eq, hz1, mul_one]
    exact y.2
  have hπsurj : Function.Surjective π :=
    e.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥J))
  let va : Fin 4 → Multiplicative (ZMod 3) := ι.symm ⟨a, ha⟩
  have hva : ((ι va : EJ) : G) = a :=
    congrArg Subtype.val (MulEquiv.apply_symm_apply ι ⟨a, ha⟩)
  let ιJ : (Fin 4 → Multiplicative (ZMod 3)) →* ↥J :=
    (Subgroup.inclusion hEJ).comp ι.toMonoidHom
  have hιπJ : ∀ f, π (ιJ f) = τ f := fun f => by
    change π (⟨((ι f : EJ) : G), hEJ (ι f).2⟩ : ↥J) = τ f
    exact hιπ f
  have hιJmem : ∀ f, ιJ f ∈ EJ' := by
    intro f
    change (⟨((ι f : EJ) : G), hEJ (ι f).2⟩ : ↥J) ∈ EJ'
    exact Subgroup.mem_subgroupOf.mpr (ι f).2
  have lift : ∀ (w : OrthRest.RPlus K 4)
      (α : (Fin 4 → Multiplicative (ZMod 3)) → (Fin 4 → Multiplicative (ZMod 3))),
      (∀ f, w * τ f * w⁻¹ = τ (α f)) →
      ∃ g : G, g ∈ J ∧ g ∈ Subgroup.normalizer (EJ : Set G) ∧
        g * ((ι va : EJ) : G) * g⁻¹ = ((ι (α va) : EJ) : G) := by
    intro w α hw
    obtain ⟨gJ, hgJπ⟩ := hπsurj w
    have hfwd : ∀ x : ↥J, x ∈ EJ' → gJ * x * gJ⁻¹ ∈ EJ' := by
      intro x hx
      apply mem_EJ'_of
      · have hxE' : π x ∈ τ.range := by rw [hτrangeE]; exact MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩
        obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hxE'
        rw [map_mul, map_mul, map_inv, hgJπ, ← hg, hw g]
        exact hτrangeE ▸ MonoidHom.mem_range.mpr ⟨α g, rfl⟩
      · rw [conj_pow, hEJ'3 x hx]
        simp
    have hφeq : ∀ {x y : ↥J}, x ∈ EJ' → y ∈ EJ' → π x = π y → x = y := by
      intro x y hx hy h
      have h1 : (⟨x, hx⟩ : EJ') = ⟨y, hy⟩ := by
        apply hφinj
        show π x = π y
        exact h
      exact Subtype.ext_iff.mp h1
    let F : EJ' → EJ' := fun y => ⟨gJ * (y : ↥J) * gJ⁻¹, hfwd y y.2⟩
    have hinj : Function.Injective F := by
      intro y z hyz
      have h1 : gJ * (y : ↥J) * gJ⁻¹ = gJ * (z : ↥J) * gJ⁻¹ := congrArg Subtype.val hyz
      have h2 : (y : ↥J) = (z : ↥J) := by
        have h1' : gJ * ((y : ↥J) * gJ⁻¹) = gJ * ((z : ↥J) * gJ⁻¹) := by
          simpa [mul_assoc] using h1
        exact mul_right_cancel (mul_left_cancel h1')
      exact Subtype.ext h2
    have hsurj : Function.Surjective F := Finite.surjective_of_injective hinj
    have hgN' : gJ ∈ Subgroup.normalizer (EJ' : Set ↥J) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · exact hfwd x
      · intro hx
        obtain ⟨y, hy⟩ := hsurj ⟨gJ * x * gJ⁻¹, hx⟩
        have h1 : gJ * (y : ↥J) * gJ⁻¹ = gJ * x * gJ⁻¹ := congrArg Subtype.val hy
        have h2 : (y : ↥J) = x := by
          have h1' : gJ * ((y : ↥J) * gJ⁻¹) = gJ * (x * gJ⁻¹) := by
            simpa [mul_assoc] using h1
          exact mul_right_cancel (mul_left_cancel h1')
        rw [← h2]
        exact y.2
    have hgN : (gJ : G) ∈ Subgroup.normalizer (EJ : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have hxJ : x ∈ J := hEJ hx
        have hx' : (⟨x, hxJ⟩ : ↥J) ∈ EJ' := Subgroup.mem_subgroupOf.mpr hx
        have h := (Subgroup.mem_normalizer_iff.mp hgN' (⟨x, hxJ⟩ : ↥J)).mp hx'
        have h2 : ((gJ * (⟨x, hxJ⟩ : ↥J) * gJ⁻¹ : ↥J) : G) ∈ EJ :=
          Subgroup.mem_subgroupOf.mp h
        simpa using h2
      · intro hx
        have hxJ : x ∈ J := by
          have h1 : (gJ : G)⁻¹ * ((gJ : G) * x * (gJ : G)⁻¹) * (gJ : G) ∈ J :=
            J.mul_mem (J.mul_mem (J.inv_mem gJ.2) (hEJ hx)) gJ.2
          have h2 : (gJ : G)⁻¹ * ((gJ : G) * x * (gJ : G)⁻¹) * (gJ : G) = x := by group
          rwa [h2] at h1
        have hy : (⟨x, hxJ⟩ : ↥J) ∈ EJ' := by
          refine (Subgroup.mem_normalizer_iff.mp hgN' (⟨x, hxJ⟩ : ↥J)).mpr ?_
          rw [Subgroup.mem_subgroupOf]
          simpa using hx
        simpa using Subgroup.mem_subgroupOf.mp hy
    have hconjJ : ∀ f, gJ * ιJ f * gJ⁻¹ = ιJ (α f) := by
      intro f
      have hmem : gJ * ιJ f * gJ⁻¹ ∈ EJ' := by
        apply hfwd
        exact hιJmem f
      have hmem' : ιJ (α f) ∈ EJ' := hιJmem (α f)
      exact hφeq hmem hmem' (by
        rw [map_mul, map_mul, map_inv, hιπJ f, hιπJ (α f), hgJπ, hw f])
    refine ⟨(gJ : G), gJ.2, hgN, ?_⟩
    simpa [ιJ] using congrArg Subtype.val (hconjJ va)
  have hvan : ∀ i : Fin 4, va i = 1 := by
    intro i
    have hex : ∃ j : Fin 4, j ≠ i := by
      by_cases hi : i = 0
      · exact ⟨1, by rw [hi]; decide⟩
      · exact ⟨0, fun h => hi h.symm⟩
    obtain ⟨j, hji⟩ := hex
    have hij : i ≠ j := fun h => hji h.symm
    obtain ⟨w, hw⟩ := hdinv i j hij
    obtain ⟨g, hgJ, hgN, hconj⟩ := lift w (NbrOrth.dinv i j) hw
    have hfixg := hfix g hgJ hgN
    have hconj'a := hconj
    rw [hva] at hconj'a
    have hEq : ((ι (NbrOrth.dinv i j va) : EJ) : G) = a := by rw [← hconj'a, hfixg]
    have hveq : NbrOrth.dinv i j va = va := by
      apply ι.injective
      exact Subtype.ext (hEq.trans hva.symm)
    have hcoord : (va i)⁻¹ = va i := by
      have h := congrFun hveq i
      simp [NbrOrth.dinv, hij] at h
      exact h
    have hx : Multiplicative.toAdd (va i) = 0 := by
      have h := congrArg Multiplicative.toAdd hcoord
      rw [toAdd_inv] at h
      have h2 : (2 : ZMod 3) * Multiplicative.toAdd (va i) = 0 := by
        rw [two_mul]
        nth_rewrite 1 [h.symm]
        exact neg_add_cancel _
      have h2ne : (2 : ZMod 3) ≠ 0 := by
        have h3 : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
        have h2eq : (2 : ZMod 3) = -1 := by
          rw [eq_neg_iff_add_eq_zero]
          have : (2 : ZMod 3) + 1 = 3 := by norm_num
          rw [this, h3]
        rw [h2eq]
        exact neg_ne_zero.mpr one_ne_zero
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 h2ne
      · exact h3
    exact Multiplicative.toAdd.injective (by rw [hx]; rfl)
  have hva1 : va = 1 := funext hvan
  have hfin : ((ι va : EJ) : G) = 1 := by rw [hva1]; simp
  rw [hva] at hfin
  exact hfin

end CFSG.StandardType

end
