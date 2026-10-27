module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosure
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Defs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGSignedPermCount
public import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem pztd_isSignedPerm_negAut (p k : ℕ) :
    SpCoord.IsSignedPerm (⇑(OrthExcEven.negAut : MulAut (Fin k → Multiplicative (ZMod p)))) :=
  ⟨1, fun _ => -1, fun _ => Or.inr rfl, fun f i => by
    rw [OrthExcEven.negAut_apply, SpCoord.toAdd_inv_apply, Equiv.Perm.one_apply]
    ring⟩

private theorem pztd_sgnAut_injective {i j : Fin 4}
    (h : (SpCoord.sgnAut (p := 3) i : MulAut (Fin 4 → Multiplicative (ZMod 3))) =
      SpCoord.sgnAut j) :
    i = j := by
  by_contra hne
  have h1 := congrArg (fun u : MulAut (Fin 4 → Multiplicative (ZMod 3)) =>
      (u (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod 3)))) i) h
  simp only [SpCoord.sgnAut_apply, Function.update_self, Function.update_of_ne hne,
    Pi.mulSingle_eq_same] at h1
  have h2 : (-1 : ZMod 3) = 1 := by
    have := congrArg Multiplicative.toAdd h1
    simpa using this
  exact (by decide : (-1 : ZMod 3) ≠ 1) h2

private theorem pztd_negAut_ne_one :
    (OrthExcEven.negAut : MulAut (Fin 4 → Multiplicative (ZMod 3))) ≠ 1 := by
  intro h
  have h1 := congrArg (fun u : MulAut (Fin 4 → Multiplicative (ZMod 3)) =>
      (u (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod 3)))) 0) h
  rw [OrthExcEven.negAut_apply] at h1
  simp only [Pi.mulSingle_eq_same, MulAut.one_apply] at h1
  have h2 : (-1 : ZMod 3) = 1 := by
    have := congrArg Multiplicative.toAdd h1
    simpa using this
  exact (by decide : (-1 : ZMod 3) ≠ 1) h2

private theorem pztd_central_eq_one_or_negAut
    {u : MulAut (Fin 4 → Multiplicative (ZMod 3))}
    (huW : SpCoord.IsSignedPerm ⇑u)
    (hcent : ∀ v : MulAut (Fin 4 → Multiplicative (ZMod 3)),
      SpCoord.IsSignedPerm ⇑v → v * u = u * v) :
    u = 1 ∨ u = OrthExcEven.negAut := by
  classical
  obtain ⟨π, ε, hε, hsign⟩ := huW
  have hπi : ∀ i, π i = i := by
    intro i
    have h' : (SpCoord.sgnAut (p := 3) i : MulAut (Fin 4 → Multiplicative (ZMod 3))) =
        SpCoord.sgnAut (π i) := by
      have h1 := hcent (SpCoord.sgnAut i) (SpCoord.isSignedPerm_sgnAut i)
      have h2 := SpCoord.IsSignedPerm.mul_sgnAut hsign i
      rw [h2] at h1
      exact mul_right_cancel h1
    exact (pztd_sgnAut_injective h').symm
  have hdiag : ∀ f i, Multiplicative.toAdd (u f i) = ε i * Multiplicative.toAdd (f i) := by
    intro f i
    have := hsign f i
    rwa [hπi i] at this
  have hεconst : ∀ i : Fin 4, ε i = ε 0 := by
    intro i
    by_cases hi : i = 0
    · rw [hi]
    · have hmain : SpCoord.permAut (Equiv.swap 0 i)
            (u (Pi.mulSingle i (Multiplicative.ofAdd 1))) =
          u (Pi.mulSingle 0 (Multiplicative.ofAdd 1)) := by
        have hcomm := hcent (SpCoord.permAut (Equiv.swap 0 i))
          (SpCoord.isSignedPerm_permAut _)
        have h := congrArg (fun w : MulAut (Fin 4 → Multiplicative (ZMod 3)) =>
            w (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod 3)))) hcomm
        simpa [MulAut.mul_apply, SpCoord.permAut_mulSingle, Equiv.swap_apply_right] using h
      have hL : Multiplicative.toAdd
          (SpCoord.permAut (Equiv.swap 0 i) (u (Pi.mulSingle i (Multiplicative.ofAdd 1))) 0) =
          ε i := by
        rw [SpCoord.permAut_apply, Function.comp_apply,
          show (Equiv.swap 0 i)⁻¹ 0 = i from by
            rw [Equiv.swap_inv]; exact Equiv.swap_apply_left 0 i]
        rw [hdiag (Pi.mulSingle i (Multiplicative.ofAdd 1)) i, SpCoord.toAdd_mulSingle]
        simp
      have hR : Multiplicative.toAdd (u (Pi.mulSingle 0 (Multiplicative.ofAdd 1)) 0) =
          ε 0 := by
        rw [hdiag (Pi.mulSingle 0 (Multiplicative.ofAdd 1)) 0, SpCoord.toAdd_mulSingle]
        simp
      have h := congrArg (fun g => Multiplicative.toAdd (g 0)) hmain
      rw [hL, hR] at h
      exact h
  rcases hε 0 with h0 | h0
  · left
    refine MulEquiv.ext fun f => SpCoord.eq_of_toAdd_eq fun i => ?_
    rw [hdiag f i, show ε i = 1 from (hεconst i).trans h0, one_mul]
    rfl
  · right
    refine MulEquiv.ext fun f => SpCoord.eq_of_toAdd_eq fun i => ?_
    rw [hdiag f i, show ε i = -1 from (hεconst i).trans h0, OrthExcEven.negAut_apply,
      SpCoord.toAdd_inv_apply, neg_one_mul]

theorem ggPZ_automizer_D4
    {G : Type} [Group G] [Finite G] {n : ℕ} [Fact (Nat.Prime 3)]
    {J EJ : Subgroup G} (hpq : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1)
    (hJ : GGHasLabel ⟨.D, 4, n⟩ (↥J ⧸ Subgroup.center ↥J)) (_hJq : IsQuasisimple ↥J)
    (hZ : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥J)) (hEJ : EJ ≤ J) (hE : IsElemAbelian 3 EJ)
    (hcard : Nat.card ↥EJ = 3 ^ 4) :
    ∃ (W : Type) (_ : Group W) (_ : Finite W) (f : W →* MulAut ↥EJ), Nat.card W = 384 ∧
      Nat.card ↥(Subgroup.center W) = 2 ∧ ggAutomizer J EJ ≤ f.range := by
  classical
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
  obtain ⟨k, τ, hτinj, hτrange, hk4, _, _, hτnorm⟩ := hT E' hE' h3E' hscE'
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
  let WS : Subgroup (MulAut (Fin 4 → Multiplicative (ZMod 3))) :=
    SignedPermCount.signedPermSubgroup 3 4
  have hcardW : Nat.card ↥WS = 384 := by
    have hcard : Nat.card ↥(SignedPermCount.signedPermSubgroup 3 4) =
        2 ^ 4 * (4:ℕ).factorial :=
      SignedPermCount.card_signedPermSubgroup (p := 3) (k := 4) (by norm_num) (by norm_num)
    dsimp only [WS]
    rw [hcard]
    norm_num
  have hnegmem : OrthExcEven.negAut ∈ WS := by
    dsimp only [WS, SignedPermCount.signedPermSubgroup]
    exact pztd_isSignedPerm_negAut 3 4
  have hcenterW : Nat.card ↥(Subgroup.center ↥WS) = 2 := by
    have hcenter_eq : Subgroup.center ↥WS =
        Subgroup.zpowers (⟨OrthExcEven.negAut, hnegmem⟩ : ↥WS) := by
      refine le_antisymm ?_ ?_
      · intro u hu
        rw [Subgroup.mem_zpowers_iff]
        have hcent : ∀ v : MulAut (Fin 4 → Multiplicative (ZMod 3)),
            SpCoord.IsSignedPerm ⇑v → v * u.1 = u.1 * v := fun v hv =>
          Subtype.ext_iff.mp (Subgroup.mem_center_iff.mp hu ⟨v, hv⟩)
        rcases pztd_central_eq_one_or_negAut u.2 hcent with h | h
        · exact ⟨0, by rw [show u = 1 from Subtype.ext h]; simp⟩
        · exact ⟨1, by rw [show u = ⟨OrthExcEven.negAut, hnegmem⟩ from Subtype.ext h]; simp⟩
      · rw [Subgroup.zpowers_le]
        refine Subgroup.mem_center_iff.mpr fun v => Subtype.ext ?_
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        exact (OrthExcEven.negAut_mul_comm v.1).symm
    rw [hcenter_eq, Nat.card_zpowers]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [sq]
      exact Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_one]
        exact OrthExcEven.negAut_mul_self)
    · intro h
      exact pztd_negAut_ne_one (Subtype.ext_iff.mp h)
  let f : ↥WS →* MulAut ↥EJ := (MulAut.congr ι).toMonoidHom.comp WS.subtype
  refine ⟨↥WS, inferInstance, inferInstance, f, hcardW, hcenterW, ?_⟩
  intro ψ hψ
  obtain ⟨g, hgJ, hgN, hg⟩ := mem_ggAutomizer_iff.mp hψ
  let g' : ↥J := ⟨g, hgJ⟩
  have hgN' : ∀ h : G, h ∈ EJ ↔ g * h * g⁻¹ ∈ EJ :=
    Subgroup.mem_normalizer_iff.mp hgN
  have hrn : ∀ x ∈ E, π g' * x * (π g')⁻¹ ∈ E := by
    intro x hx
    rw [MonoidHom.mem_range] at hx
    obtain ⟨y, rfl⟩ := hx
    refine MonoidHom.mem_range.mpr ⟨⟨g' * y * g'⁻¹, ?_⟩, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      have hyG : ((y : ↥J) : G) ∈ EJ := Subgroup.mem_subgroupOf.mp y.2
      have h := (hgN' ((y : ↥J) : G)).mp hyG
      simpa using h
    · change π (g' * (y : ↥J) * g'⁻¹) = π g' * π (y : ↥J) * (π g')⁻¹
      rw [map_mul, map_mul, map_inv]
  have hrn' : ∀ x ∈ E', π g' * x * (π g')⁻¹ ∈ E' := by
    intro x hx
    rw [hE'E] at hx ⊢
    exact hrn x hx
  obtain ⟨π₀, ε, hε, hrel⟩ := hτnorm (π g') hrn'
  let wAut : MulAut (Fin 4 → Multiplicative (ZMod 3)) :=
    (MulAut.congr ι).symm (ggConjAut EJ hgN)
  have hwAut_apply : (MulAut.congr ι) wAut = ggConjAut EJ hgN :=
    MulEquiv.apply_symm_apply _ _
  have hwchar : ∀ u₀, τ (wAut u₀) = π g' * τ u₀ * (π g')⁻¹ := by
    intro u₀
    have h1 : ι (wAut u₀) = ggConjAut EJ hgN (ι u₀) := by
      have h := congrArg (fun ψ : MulAut ↥EJ => ψ (ι u₀)) hwAut_apply
      simpa [MulAut.congr_apply, MulEquiv.symm_apply_apply] using h
    have h2 := congrArg (fun b : ↥EJ => π (⟨((b : G)), hEJ b.2⟩ : ↥J)) h1
    rw [hιπ (wAut u₀)] at h2
    have h3 : (⟨((ggConjAut EJ hgN (ι u₀) : EJ) : G),
        hEJ (ggConjAut EJ hgN (ι u₀)).2⟩ : ↥J)
        = g' * (⟨((ι u₀ : EJ) : G), hEJ (ι u₀).2⟩ : ↥J) * g'⁻¹ := by
      refine Subtype.ext ?_
      rw [ggConjAut_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h3, map_mul, map_mul, map_inv, hιπ u₀] at h2
    exact h2
  have hwsigned : SpCoord.IsSignedPerm ⇑wAut :=
    ⟨π₀, ε, hε, fun u₀ i => hrel u₀ (wAut u₀) (hwchar u₀).symm i⟩
  have hwW : wAut ∈ WS := hwsigned
  refine ⟨⟨wAut, hwW⟩, ?_⟩
  show (MulAut.congr ι) wAut = ψ
  rw [hwAut_apply]
  exact MulEquiv.ext fun b => Subtype.ext ((ggConjAut_apply EJ hgN b).trans (hg b).symm)

end CFSG.StandardType

end
