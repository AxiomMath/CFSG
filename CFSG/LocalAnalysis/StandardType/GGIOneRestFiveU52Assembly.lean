module

public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveU52Layer
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveU52Reduction
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvModel
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverTwo

public section

namespace CFSG.StandardType

namespace IOneU52

open scoped commutatorElement
open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly

theorem commutator_mul_central {Y : Type*} [Group Y] {a b z w : Y} (hz : z ∈ Subgroup.center Y)
    (hw : w ∈ Subgroup.center Y) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz' := Subgroup.mem_center_iff.mp hz
  have hw' := Subgroup.mem_center_iff.mp hw
  rw [commutatorElement_def, commutatorElement_def]
  have h1 : a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹ =
      a * (z * (b * w) * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by group
  have h2 : z * (b * w) * z⁻¹ = b * w := by rw [← hz' (b * w)]; group
  rw [h1, h2]
  have h3 : a * (b * w) * a⁻¹ * w⁻¹ * b⁻¹ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by group
  have h4 : w * a⁻¹ * w⁻¹ = a⁻¹ := by rw [← hw' a⁻¹]; group
  rw [h3, h4]

theorem surjective_of_cover {K : Type} [Field K] [Finite K] {L' : Type} [Group L']
    {ψ : L' →* UnitaryR K 1 5} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {φ₀ : ↥(unitarySU 2 1 K 5) →* L'}
    (hφ₀ : ∀ s, ψ (φ₀ s) = LargeEvenProjMk (unitarySU 2 1 K 5) s) :
    Function.Surjective φ₀ := by
  have hcomm : commutator L' ≤ φ₀.range := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨s, hs⟩ : ∃ s, LargeEvenProjMk (unitarySU 2 1 K 5) s = ψ x :=
      QuotientGroup.mk'_surjective _ (ψ x)
    obtain ⟨t, ht⟩ : ∃ t, LargeEvenProjMk (unitarySU 2 1 K 5) t = ψ y :=
      QuotientGroup.mk'_surjective _ (ψ y)
    have hz : (φ₀ s)⁻¹ * x ∈ Subgroup.center L' := hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφ₀ s, hs, inv_mul_cancel])
    have hw : (φ₀ t)⁻¹ * y ∈ Subgroup.center L' := hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφ₀ t, ht, inv_mul_cancel])
    have e : ⁅x, y⁆ = ⁅φ₀ s, φ₀ t⁆ := by
      have hx : x = φ₀ s * ((φ₀ s)⁻¹ * x) := by group
      have hy : y = φ₀ t * ((φ₀ t)⁻¹ * y) := by group
      rw [hx, hy, commutator_mul_central hz hw]
    rw [e, ← map_commutatorElement]
    exact ⟨_, rfl⟩
  intro x
  exact hcomm (by rw [hperf]; exact Subgroup.mem_top x)

theorem injective_of_cover {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    {L' : Type} [Group L'] {ψ : L' →* UnitaryR K 1 5} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {φ₀ : ↥(unitarySU 2 1 K 5) →* L'}
    (hφ₀ : ∀ s, ψ (φ₀ s) = LargeEvenProjMk (unitarySU 2 1 K 5) s) :
    Function.Injective ψ := by
  have hsurj := surjective_of_cover hψ hker hperf hφ₀
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨s, rfl⟩ := hsurj x
  rw [hφ₀ s] at hx
  have hs : s ∈ (LargeEvenProjMk (unitarySU 2 1 K 5)).ker := MonoidHom.mem_ker.mpr hx
  have hs1 : s = 1 :=
    TableBUE.eq_one_of_mem_suScalars (TableBU.unitaryFieldData_of_card hK le_rfl) Nat.prime_three
      (by norm_num) hs (pow_three_of_ker_proj hK 5 s hs)
  rw [hs1, map_one]

end IOneU52

section Certs

namespace IOneU52

open scoped commutatorElement
open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly

theorem ggIOneUnitaryFiveRootInput_holds : GGIOneUnitaryFiveRootInput := by
  intro K _ _ hK L' _ _ ψ hψ hker hperf A hA hAI h3r h3 hN
  have hcov : LineU.UnitaryCoverAt 1 5 K :=
    LineU.unitaryUniversalCover_holds 1 5 K hK (by norm_num) (by decide)
  obtain ⟨φ₀, hφ₀⟩ := hcov.2 L' ψ hψ hker hperf
  have hψinj : Function.Injective ψ := injective_of_cover hK hψ hker hperf hφ₀
  let e : L' ≃* UnitaryR K 1 5 := MulEquiv.ofBijective ψ ⟨hψinj, hψ⟩
  have hψsymm : ∀ x : UnitaryR K 1 5, ψ (e.symm x) = x := fun x => e.apply_symm_apply x
  have hcard : 3 ^ (5 / 3 + 2) ≤ Nat.card A := by
    rw [show (5 : ℕ) / 3 + 2 = 3 from rfl]
    exact h3r
  obtain ⟨φ, hφs, hφker, hdiag⟩ := UnitTv.exists_diagModel' (n := 1) (d := 5) (p := 3) hK
    le_rfl (by norm_num) Nat.prime_three (by norm_num)
    (LineU.unitaryUniversalCover_holds 1 5 K hK (by norm_num) (by decide)) hψ hker hperf hA hAI
    hcard
  have hM : UnitTB.Model φ := ⟨TableBU.unitaryFieldData_of_card hK le_rfl, hφs, hφker⟩
  have hφinj : Function.Injective φ := injective_of_scalar hK hφker
  have hact : ∀ a ∈ A, ∃ σ : Fin 5 → Kˣ, SmallU.ActsU φ a σ := fun a ha => by
    obtain ⟨t, ht⟩ := hdiag a ha
    obtain ⟨σ, -, hσ⟩ := SmallU.ActsU.of_actsDiagU ht
    exact ⟨σ, hσ⟩
  have hex : ∀ a : A, ∃ t : UnitaryR K 1 5, ∀ l, ψ ((a : MulAut L') l) = t * ψ l * t⁻¹ := by
    intro a
    obtain ⟨φ', hφ'I, hφ'⟩ := hAI a a.2
    have hφ'p : φ' ^ 3 = 1 := by
      ext x
      obtain ⟨l, rfl⟩ := hψ x
      rw [pow_apply_comp_eq hφ' 3 l, hA.2 a a.2, MulAut.one_apply, MulAut.one_apply]
    obtain ⟨t, rfl⟩ := ggOutdiagPrime_five hK φ' hφ'I hφ'p
    exact ⟨t, fun l => (hφ' l).symm⟩
  choose χf hχf using hex
  have hZ : Subgroup.center (UnitaryR K 1 5) = ⊥ :=
    TableBUE.center_proj_eq_bot hK (by norm_num) (by decide)
  have huniq : ∀ (a : MulAut L') (t t' : UnitaryR K 1 5),
      (∀ l, ψ (a l) = t * ψ l * t⁻¹) → (∀ l, ψ (a l) = t' * ψ l * t'⁻¹) → t = t' := by
    intro a t t' ht ht'
    have hc : t'⁻¹ * t ∈ Subgroup.center (UnitaryR K 1 5) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := hψ g
      have e' := (ht l).symm.trans (ht' l)
      calc ψ l * (t'⁻¹ * t) = t'⁻¹ * (t' * ψ l * t'⁻¹) * t := by group
        _ = t'⁻¹ * (t * ψ l * t⁻¹) * t := by rw [e']
        _ = (t'⁻¹ * t) * ψ l := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.mp hc).symm
  have hχmul : ∀ a b : A, χf (a * b) = χf a * χf b := by
    intro a b
    refine huniq ((a * b : A) : MulAut L') _ _ (hχf (a * b)) fun l => ?_
    rw [Subgroup.coe_mul, MulAut.mul_apply, hχf a, hχf b]
    group
  have hχone : χf 1 = 1 := huniq 1 _ _ (hχf 1) fun l => by simp
  let χ : A →* UnitaryR K 1 5 :=
    { toFun := χf, map_one' := hχone, map_mul' := hχmul }
  have hχ : ∀ a : A, ∀ l, ψ ((a : MulAut L') l) = χ a * ψ l * (χ a)⁻¹ := hχf
  have hχgen : ∀ (a : MulAut L') (ha : a ∈ A) (x : L'),
      ψ (a x) = χ ⟨a, ha⟩ * ψ x * (χ ⟨a, ha⟩)⁻¹ := fun a ha x => hχ ⟨a, ha⟩ x
  have hχinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    apply Subtype.ext
    apply MulEquiv.ext
    intro l
    apply hψinj
    rw [hχ a l, ha, one_mul, inv_one, mul_one]
    rfl
  have hAbA : IsElemAbelian 3 χ.range :=
    isElemAbelian_range (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hA a.2 b.2))
      (fun a => Subtype.ext (by simpa using hA.2 a a.2)) χ
  have hcardAb : Nat.card χ.range = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hχinj).toEquiv).symm
  obtain ⟨U, hU1, hU2, hAU⟩ := hN
  have hUAb : ∃ U : Subgroup (UnitaryR K 1 5), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      χ.range ≤ Subgroup.normalizer (U : Set (UnitaryR K 1 5)) := by
    refine ⟨U, hU1, hU2, ?_⟩
    rw [Subgroup.le_normalizer_iff]
    rintro _ ⟨a, rfl⟩ u hu
    obtain ⟨l, rfl⟩ := hψ u
    have := hAU a a.2 l hu
    rwa [hχ] at this
  have hr3 : 3 ^ (5 - 2) ≤ Nat.card χ.range := by
    rw [hcardAb]
    exact h3r
  obtain ⟨t₀, hend, -, U₀, hU₀J, hU₀1, hU₀2, hAU₀⟩ := exists_rootEndNode_five hK
    (Ab := χ.range) hAbA hr3 hUAb
  obtain ⟨ht₀Ā, ht₀1, hcomp₀, hcent₀⟩ := hend
  obtain ⟨a₀, ha₀eq⟩ := MonoidHom.mem_range.mp ht₀Ā
  have hconj : ∀ a : A, (a : MulAut L') = MulAut.conj (e.symm (χ a)) := by
    intro a
    apply MulEquiv.ext
    intro l
    apply hψinj
    rw [MulAut.conj_apply, hχ a l, map_mul, map_mul, map_inv, hψsymm]
  set g₀ : L' := e.symm t₀ with hg₀
  have hconj₀ : (a₀ : MulAut L') = MulAut.conj g₀ := by
    rw [hconj a₀, ha₀eq]
  have hfix₀ : ggFix (MulAut.conj g₀) = Subgroup.centralizer ({g₀} : Set L') := by
    ext x
    rw [mem_ggFix, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff,
      mul_inv_eq_iff_eq_mul, eq_comm]
  have hL : (LargeEvenLayer (Subgroup.centralizer ({t₀} : Set (UnitaryR K 1 5)))).map
      e.symm.toMonoidHom = LargeEvenLayer (Subgroup.centralizer ({g₀} : Set L')) := by
    rw [← CFSG.StandardType.largeEvenLayer_map_of_injective e.symm.toMonoidHom e.symm.injective,
      TableBSymp.map_centralizer_singleton e.symm t₀]
  have hLg : (LargeEvenLayer (Subgroup.centralizer ({g₀} : Set L'))).map e.toMonoidHom =
      LargeEvenLayer (Subgroup.centralizer ({t₀} : Set (UnitaryR K 1 5))) := by
    rw [← CFSG.StandardType.largeEvenLayer_map_of_injective e.toMonoidHom e.injective,
      TableBSymp.map_centralizer_singleton e g₀, hg₀, e.apply_symm_apply]
  have hcompA : IsComponentOf (LargeEvenLayer (ggFix (MulAut.conj g₀)))
      (ggFix (MulAut.conj g₀)) := by
    rw [hfix₀]
    have h := CFSG.StandardType.isComponentOf_map_of_injective e.symm.toMonoidHom
      e.symm.injective hcomp₀
    rw [hL, TableBSymp.map_centralizer_singleton e.symm t₀] at h
    exact h
  have hcompA₀ : IsComponentOf (LargeEvenLayer (ggFix (a₀ : MulAut L')))
      (ggFix (a₀ : MulAut L')) := by
    rw [hconj₀]
    exact hcompA
  have hcentA : GGCentEnd A (a₀ : MulAut L') := by
    intro a' ha'
    set s : UnitaryR K 1 5 := χ ⟨a', ha'⟩ with hs
    have hkey : ∀ j : L', a' j = j ↔ s * ψ j = ψ j * s := by
      intro j
      have hj : ψ (a' j) = s * ψ j * s⁻¹ := hχgen a' ha' j
      constructor
      · intro h
        rw [h] at hj
        calc s * ψ j = s * ψ j * s⁻¹ * s := by group
          _ = ψ j * s := by rw [← hj]
      · intro h
        apply hψinj
        rw [hj, h]
        group
    have hClaim1 : (∀ j ∈ LargeEvenLayer (ggFix (a₀ : MulAut L')), a' j = j) ↔
        (∀ j' ∈ LargeEvenLayer (Subgroup.centralizer ({t₀} : Set (UnitaryR K 1 5))),
          s * j' = j' * s) := by
      rw [hconj₀, hfix₀]
      constructor
      · intro h j' hj'
        rw [← hLg] at hj'
        obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hj'
        exact (hkey j).mp (h j hj)
      · intro h j hj
        apply (hkey j).mpr
        exact h (e j) (by rw [← hLg]; exact Subgroup.mem_map_of_mem _ hj)
    have hs_mem : s ∈ χ.range := MonoidHom.mem_range.mpr ⟨⟨a', ha'⟩, rfl⟩
    have hClaim2 := hcent₀ s hs_mem
    have hClaim3 : a' ∈ Subgroup.zpowers (a₀ : MulAut L') ↔ s ∈ Subgroup.zpowers t₀ := by
      constructor
      · intro hmem
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
        have hkA : (⟨a', ha'⟩ : A) = a₀ ^ k :=
          Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
        rw [hs, hkA, map_zpow, ha₀eq]
        exact Subgroup.zpow_mem_zpowers t₀ k
      · intro hmem
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
        have hkA : (a₀ ^ k : A) = ⟨a', ha'⟩ := hχinj (by rw [map_zpow, ha₀eq, hk])
        have hk' := congrArg Subtype.val hkA
        rw [Subgroup.coe_zpow] at hk'
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, hk'⟩
    exact hClaim1.trans (hClaim2.trans hClaim3.symm)
  have hNS : GGNonSmallRule 3 A (a₀ : MulAut L') := by
    rintro - ⟨a₁, ⟨ha₁A, ha₁1, hcomp₁, -⟩, hns⟩ -
    exact hns (layer_small_of_component hK hM hφinj ha₁1 (hact a₁ ha₁A) hcomp₁)
  refine ⟨(a₀ : MulAut L'), ⟨a₀.2, ?_, hcompA₀, hcentA⟩, hNS,
    U₀.map e.symm.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro h
    have ha₀1 : a₀ = 1 := Subtype.ext h
    apply ht₀1
    rw [← ha₀eq, ha₀1]
    exact map_one χ
  · rw [hconj₀, hfix₀, ← hL]
    exact Subgroup.map_mono hU₀J
  · intro hbot
    exact hU₀1 (Subgroup.map_injective e.symm.injective (hbot.trans (Subgroup.map_bot _).symm))
  · exact hU₀2.map _
  · intro a' ha' u hu
    obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.mp hu
    have hv : e (a' (e.symm u₀)) ∈ U₀ := by
      have h1 : e (a' (e.symm u₀)) = χ ⟨a', ha'⟩ * u₀ * (χ ⟨a', ha'⟩)⁻¹ := by
        show ψ (a' (e.symm u₀)) = _
        rw [hχgen a' ha', hψsymm]
      rw [h1]
      exact (Subgroup.mem_normalizer_iff.mp
        (hAU₀ (MonoidHom.mem_range.mpr ⟨⟨a', ha'⟩, rfl⟩)) u₀).mp hu₀
    exact Subgroup.mem_map.mpr ⟨e (a' (e.symm u₀)), hv, e.symm_apply_apply _⟩

end IOneU52

theorem ggIOneUnitaryFiveTwoInput_holds : GGIOneUnitaryFiveTwoInput :=
  ggIOneUnitaryFiveTwoInput_of_rootInput IOneU52.ggIOneUnitaryFiveRootInput_holds

end Certs

end CFSG.StandardType
