module

public import CFSG.LocalAnalysis.StandardType.FS81.RootE8Defs
public import CFSG.LocalAnalysis.StandardType.FS81.S7Model
public import Certificates.Certificate1952
public import Certificates.Certificate8064
public import Certificates.Certificate13691
import CFSG.LocalAnalysis.StandardType.FS81.RootD6ModelDefs
import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsTwoE
import CFSG.RankThree.PartOne.KE.E7FiveBlock

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
open CFSG.HardMathSupport.Timmesfeld.Steinberg
open CFSG.LieType.AlgebraicGroups
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.Torality

private theorem isElemAbelian_range_of_exponent {A H : Type*} [CommGroup A] [Group H]
    (φ : A →* H) (p : ℕ) (hexp : ∀ a : A, a ^ p = 1) : IsElemAbelian p φ.range := by
  refine ⟨?_, ?_⟩
  · refine isMulCommutative_iff.2 fun a b => ?_
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    show a.1 * b.1 = b.1 * a.1
    rw [← hz, ← hw, ← map_mul, ← map_mul, mul_comm z w]
  · rintro x hx
    obtain ⟨z, rfl⟩ := MonoidHom.mem_range.1 hx
    rw [← map_pow, hexp z, map_one]

private theorem card_range_of_injective {A H : Type*} [Group A] [Group H] [Finite A]
    (φ : A →* H) (hinj : Function.Injective φ) : Nat.card φ.range = Nat.card A := by
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top]

private theorem canonicalRep_conj_rootDiagUnit_sq'
    {τ : Tag} {L : Type} [Field L] {w₀ : WeylGroup τ}
    (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u) {a : Fin τ.rank → Lˣ}
    (ha3 : ∀ i, a i ^ 3 = 1) :
    canonicalRep (coxeterSystem τ) L w₀ * rootDiagUnit τ a *
      (canonicalRep (coxeterSystem τ) L w₀)⁻¹ = rootDiagUnit τ a ^ 2 := by
  rw [canonicalRep_conj_rootDiagUnit_of_neg hw₀]
  have hd3 : rootDiagUnit τ a ^ 3 = 1 := by
    have h1 : rootDiagUnit τ (a ^ 3) = rootDiagUnit τ a ^ 3 :=
      map_pow (rootDiagUnitHom τ L) a 3
    rw [← h1, show a ^ 3 = 1 from funext ha3, rootDiagUnit_one]
  exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hd3])

private theorem exists_elemAbelian_card_eight_of_orderOf_eq_three
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {x : adjointGroup .E8 K} (hx : orderOf x = 3) :
    ∃ D : Subgroup (adjointGroup .E8 K), IsElemAbelian 3 D ∧ 3 ^ 8 ≤ Nat.card D ∧
      ∃ g : adjointGroup .E8 K, g * x * g⁻¹ ∈ D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨Fr, hFr, g0, hg0C, hg0⟩ := exists_lang_data Tag.E8 K e8Neg
  have hFr2 : Fr = iterateFrobenius (AlgebraicClosure K) 2 1 :=
    RingHom.ext fun c => by rw [hFr, hK, iterateFrobenius_two_one]
  subst hFr2
  have hMW : langModel Tag.E8 K (AlgebraicClosure K) g0 ≤
      twModel (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) e8Neg)
        (iterateFrobenius (AlgebraicClosure K) 2 1) :=
    langModel_le_twModel Tag.E8 K (AlgebraicClosure K) hFr hg0C hg0
  have : Finite (twModel (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) e8Neg)
      (iterateFrobenius (AlgebraicClosure K) 2 1)) := finite_twModel hg0C hg0
  have hWM : twModel (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) e8Neg)
      (iterateFrobenius (AlgebraicClosure K) 2 1) ≤
      langModel Tag.E8 K (AlgebraicClosure K) g0 :=
    le_langModel_E8_of_le_twModel K (AlgebraicClosure K) hFr hg0C hg0 (P :=
      twModel (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) e8Neg)
        (iterateFrobenius (AlgebraicClosure K) 2 1)) le_rfl
  obtain ⟨ω, hω, -⟩ := exists_orderOf_eq_of_dvd_add_one K (L := AlgebraicClosure K) (N := 3)
    (by rw [hK])
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hLang : ∀ a : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ, (∀ i, a i ^ 3 = 1) →
      ∀ c ∈ toralCentralizer Tag.E8 (AlgebraicClosure K) a,
        ∃ z ∈ toralCentralizer Tag.E8 (AlgebraicClosure K) a, z⁻¹ * frobTwistGL Tag.E8
          (AlgebraicClosure K) 2 1 (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K)
            e8Neg) z = c := fun a ha3 c hc =>
    toral_centralizer_Lang_E8_three 2 (AlgebraicClosure K) (by norm_num) a ha3 1 le_rfl
      (canonicalRep_mem_adjointGroup _ _ _) (s := 2) (by norm_num)
      (canonicalRep_conj_rootDiagUnit_sq' e8Neg_smul ha3) c hc
  let e := langModelEquiv Tag.E8 K (AlgebraicClosure K) g0
  have hxpow : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hs_mem : ((e x : langModel Tag.E8 K (AlgebraicClosure K) g0) :
      ModGL Tag.E8 (AlgebraicClosure K)) ∈
      twModel (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) e8Neg)
        (iterateFrobenius (AlgebraicClosure K) 2 1) := hMW (e x).2
  have hs3 : ((e x : langModel Tag.E8 K (AlgebraicClosure K) g0) :
      ModGL Tag.E8 (AlgebraicClosure K)) ^ 3 = 1 := by
    have h1 : (e x) ^ 3 = 1 := by rw [← map_pow, hxpow, map_one]
    simpa using congrArg (fun m : langModel Tag.E8 K (AlgebraicClosure K) g0 =>
      (m : ModGL Tag.E8 (AlgebraicClosure K))) h1
  obtain ⟨u, hu, y, huy⟩ := exists_conj_dV_twModel
    (isAlgebraic_zmod_algebraicClosure_of_finite K 2)
    (monomialToralAt_three_of_block a2BlockToral_E8) e8Neg_smul hLang hω hs_mem hs3
  have huM : u ∈ langModel Tag.E8 K (AlgebraicClosure K) g0 := hWM hu
  have hG : ∀ z : Fin Tag.E8.rank → ZMod 3,
      dV (τ := Tag.E8) ω z ∈ langModel Tag.E8 K (AlgebraicClosure K) g0 := fun z =>
    hWM (dV_mem_twModel rootDiagUnit_mem_torusGroup_E8 e8Neg_smul hω3 z)
  let dVh : Multiplicative (Fin Tag.E8.rank → ZMod 3) →*
      langModel Tag.E8 K (AlgebraicClosure K) g0 :=
    (dVHom (τ := Tag.E8) (k := AlgebraicClosure K) hω3).codRestrict _ (fun z => hG z.toAdd)
  let φ : Multiplicative (Fin Tag.E8.rank → ZMod 3) →* adjointGroup Tag.E8 K :=
    e.symm.toMonoidHom.comp dVh
  let D : Subgroup (adjointGroup Tag.E8 K) := φ.range
  have hD : IsElemAbelian 3 D :=
    isElemAbelian_range_of_exponent φ 3 fun z => by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      have h3 : ((3 : ℕ) : ZMod 3) = 0 := CharP.cast_eq_zero (ZMod 3) 3
      calc (3 : ℕ) • Multiplicative.toAdd z
          = ((3 : ℕ) : ZMod 3) • Multiplicative.toAdd z :=
            (Nat.cast_smul_eq_nsmul (ZMod 3) 3 _).symm
        _ = 0 := by rw [h3, zero_smul]
  have hinj : Function.Injective φ := by
    intro a b hab
    have h1 : dVh a = dVh b := e.symm.injective hab
    have h2 : dV (τ := Tag.E8) ω a.toAdd = dV (τ := Tag.E8) ω b.toAdd :=
      congrArg (fun m : langModel Tag.E8 K (AlgebraicClosure K) g0 =>
        (m : ModGL Tag.E8 (AlgebraicClosure K))) h1
    exact Multiplicative.toAdd.injective (dV_injective hω h2)
  have hDcard : Nat.card D = 3 ^ 8 := by
    rw [card_range_of_injective φ hinj, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      Fintype.card_fun, ZMod.card, Fintype.card_fin]
    decide
  have hinner : (⟨u, huM⟩ * e x * ⟨u, huM⟩⁻¹ :
      langModel Tag.E8 K (AlgebraicClosure K) g0) =
      ⟨dV (τ := Tag.E8) ω y, hG y⟩ := by
    apply Subtype.ext
    show u * (e x : ModGL Tag.E8 (AlgebraicClosure K)) * u⁻¹ = dV (τ := Tag.E8) ω y
    exact huy
  refine ⟨D, hD, hDcard.ge, e.symm ⟨u, huM⟩, ?_⟩
  have hφy : φ (Multiplicative.ofAdd y) = e.symm ⟨dV (τ := Tag.E8) ω y, hG y⟩ :=
    congrArg e.symm (Subtype.ext rfl)
  rw [show e.symm ⟨u, huM⟩ * x * (e.symm ⟨u, huM⟩)⁻¹ =
      e.symm (⟨u, huM⟩ * e x * ⟨u, huM⟩⁻¹) by
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]]
  rw [hinner, ← hφy]
  exact ⟨Multiplicative.ofAdd y, rfl⟩

theorem exists_conj_mem_frameTorusE8_of_orderOf_eq_three
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {x : adjointGroup .E8 K} (hx : orderOf x = 3) :
    ∃ g : adjointGroup .E8 K, g * x * g⁻¹ ∈ frameTorusE8 K := by
  obtain ⟨D, hD, hcard, g, hg⟩ := exists_elemAbelian_card_eight_of_orderOf_eq_three hK hx
  obtain ⟨c, hc⟩ := TableBExcTwoTB.exists_conj_frame_of_card_E8 hK hD hcard
  have hc' : D = (frameTorusE8 K).map (MulAut.conj c).toMonoidHom := hc
  rw [hc'] at hg
  obtain ⟨t, ht, htc⟩ := hg
  change (MulAut.conj c) t = g * x * g⁻¹ at htc
  rw [MulAut.conj_apply] at htc
  refine ⟨c⁻¹ * g, ?_⟩
  have hconj : c⁻¹ * (g * x * g⁻¹) * c = t := by rw [← htc]; group
  rw [show (c⁻¹ * g) * x * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * x * g⁻¹) * c by group, hconj]
  exact ht

private theorem exists_conj_mem_of_rootSetting
    {G : Type} [Group G] [Finite G] {r : Row} {b₀ : G} {K E : Subgroup G}
    {B : Basis3 G (r.n + 1)} {Y : Subgroup G} (h : RootSetting r b₀ K E B Y)
    (hr : r = Row.E7 ∨ r = Row.twD7) {x : G} (hxY : x ∈ Y) (hx3 : orderOf x = 3) :
    ∃ y ∈ Y, y * x * y⁻¹ ∈ E := by
  have hEm : IsEm 8 Y := by
    rcases hr with rfl | rfl
    · exact h.isEm
    · exact h.isEm
  obtain ⟨ι, hιinj, hιrange⟩ := exists_injective_hom_range_eq_of_isEm_eight hEm
  have hK : Nat.card (GaloisField 2 1) = 2 := natCard_galoisField_two_one
  have hxι : x ∈ ι.range := by rw [hιrange]; exact hxY
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.1 hxι
  have hm3 : orderOf m = 3 := by
    rw [← orderOf_injective ι hιinj m, hm, hx3]
  have hEle : E ≤ ι.range := by rw [hιrange]; exact h.torus_le
  have hEelem : IsElemAbelian 3 (E.comap ι) :=
    isElemAbelian_comap ι hιinj h.std.2.1.2.1.2.1
  have hrm : r.m = 8 := by rcases hr with h | h <;> rw [h] <;> rfl
  have hEcard : Nat.card (E.comap ι) = 3 ^ 8 := by
    rw [← Subgroup.card_map_of_injective (K := E.comap ι) (f := ι) hιinj,
      Subgroup.map_comap_eq_self hEle, h.std.2.1.2.2.2.1, hrm]
  obtain ⟨c, hc⟩ := TableBExcTwoTB.exists_conj_frame_of_card_E8 (K := GaloisField 2 1) hK
    hEelem hEcard.ge
  obtain ⟨g, hg⟩ := exists_conj_mem_frameTorusE8_of_orderOf_eq_three (K := GaloisField 2 1) hK hm3
  refine ⟨ι (c * g), hιrange.le ⟨c * g, rfl⟩, ?_⟩
  rw [← hm]
  simp only [← map_mul, ← map_inv]
  rw [← Subgroup.mem_comap, hc]
  refine ⟨g * m * g⁻¹, hg, ?_⟩
  change c * (g * m * g⁻¹) * c⁻¹ = c * g * m * (c * g)⁻¹
  group

theorem e8TorusAt_E7 :
    E8TorusAt Row.E7 := by
  intro G _ _ b₀ K E B Y h x hxY hx3
  exact exists_conj_mem_of_rootSetting h (Or.inl rfl) hxY hx3

theorem e8TorusAt_twD7 :
    E8TorusAt Row.twD7 := by
  intro G _ _ b₀ K E B Y h x hxY hx3
  exact exists_conj_mem_of_rootSetting h (Or.inr rfl) hxY hx3

end CFSG.StandardType.FrameRoute.FS81

end
