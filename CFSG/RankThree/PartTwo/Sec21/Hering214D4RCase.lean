module

public import CFSG.RankThree.PartTwo.Sec21.Hering214D4RD12
public import CFSG.RankThree.PartTwo.Sec21.Hering214D4RDef
public import CFSG.RankThree.PartTwo.Sec21.Item211LieProofBar
public import CFSG.LocalAnalysis.ComponentClassification.ElementaryAbelianModule
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open Item211Res2Proof
open CFSG.ComponentClassification

variable {G : Type} [Group G] [Finite G]

section Act

variable {A L : Subgroup G}

@[expose] abbrev NLA (A L : Subgroup G) : Subgroup (Subgroup.normalizer (A : Set G)) :=
  L.subgroupOf (Subgroup.normalizer (A : Set G))

@[expose] noncomputable def classNLA (A L : Subgroup G) : ↥(NLA A L) →* lBar L where
  toFun y := QuotientGroup.mk (⟨((y : Subgroup.normalizer (A : Set G)) : G),
    Subgroup.mem_subgroupOf.mp y.2⟩ : L)
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] noncomputable def actNLA (A L : Subgroup G) : ↥(NLA A L) →* MulAut (lBar L) :=
  MulAut.conj.comp (classNLA A L)

theorem NLA.mem_normalizer (y : ↥(NLA A L)) :
    ((y : Subgroup.normalizer (A : Set G)) : G) ∈ Subgroup.normalizer (L : Set G) :=
  Subgroup.le_normalizer (Subgroup.mem_subgroupOf.mp y.2)

theorem barAct_eq_actNLA (y : ↥(NLA A L)) :
    barAct L ⟨((y : Subgroup.normalizer (A : Set G)) : G), NLA.mem_normalizer y⟩ =
      actNLA A L y := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H l => rfl

end Act

section Rho

variable {A E U L : Subgroup G} {c : G}

theorem actNLA_conj_mem (hEA : E = A) (y : ↥(NLA A L)) :
    ∀ ε ∈ barImage L E, actNLA A L y * ε * (actNLA A L y)⁻¹ ∈ barImage L E := by
  intro ε hε
  rw [← barAct_eq_actNLA]
  refine barImage_conj_mem (NLA.mem_normalizer y) ?_ ε hε
  intro x hx
  rw [hEA] at hx ⊢
  exact (Subgroup.mem_normalizer_iff.mp y.1.2 x).mp hx

theorem actNLA_mem_normalizer (hEA : E = A) (y : ↥(NLA A L)) :
    actNLA A L y ∈ Subgroup.normalizer
      ((barImage L E : Subgroup (MulAut (lBar L))) : Set (MulAut (lBar L))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro ε
  refine ⟨actNLA_conj_mem hEA y ε, fun hε => ?_⟩
  have h := actNLA_conj_mem hEA y⁻¹ _ hε
  rw [map_inv] at h
  have e : (actNLA A L y)⁻¹ * (actNLA A L y * ε * (actNLA A L y)⁻¹) * ((actNLA A L y)⁻¹)⁻¹ =
      ε := by group
  rw [e] at h
  exact h

@[expose] noncomputable def rho0 (hEA : E = A) : ↥(NLA A L) →* MulAut ↥(barImage L E) :=
  (barImage L E).normalizerMonoidHom.comp
    ((actNLA A L).codRestrict _ (actNLA_mem_normalizer hEA))

theorem rho0_apply_coe (hEA : E = A) (y : ↥(NLA A L)) (ε : ↥(barImage L E)) :
    ((rho0 hEA y ε : ↥(barImage L E)) : MulAut (lBar L)) =
      actNLA A L y * ε * (actNLA A L y)⁻¹ := rfl

theorem rho0_eq_one_of_centralizes (hEA : E = A) (y : ↥(NLA A L))
    (hy : A.normalizerMonoidHom (y : Subgroup.normalizer (A : Set G)) = 1) :
    rho0 hEA y = 1 := by
  refine MulEquiv.ext fun ε => Subtype.ext ?_
  obtain ⟨a, haN, haE, hε⟩ := mem_barImage_iff.mp ε.2
  rw [rho0_apply_coe]
  show actNLA A L y * ε * (actNLA A L y)⁻¹ = ε
  have h1 : ((y : Subgroup.normalizer (A : Set G)) : G) * a *
      ((y : Subgroup.normalizer (A : Set G)) : G)⁻¹ = a := by
    have := congrArg (fun f : MulAut A => ((f ⟨a, hEA ▸ haE⟩ : A) : G)) hy
    simpa only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] using this
  rw [← hε, ← barAct_eq_actNLA, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact h1

theorem kernel_cube (h : Item211LieProof.PairFacts A E U c L) (hEA : E = A) (y : ↥(NLA A L))
    (hy : rho0 hEA y = 1) :
    (A.normalizerMonoidHom (y : Subgroup.normalizer (A : Set G))) ^ 3 = 1 := by
  obtain ⟨yy, hyy⟩ : ∃ yy : G, yy = ((y : Subgroup.normalizer (A : Set G)) : G) := ⟨_, rfl⟩
  have hyA : yy ∈ Subgroup.normalizer (A : Set G) := hyy ▸ y.1.2
  have hyL : yy ∈ L := hyy ▸ Subgroup.mem_subgroupOf.mp y.2
  have hyNL : yy ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hyL
  have hyc : Commute yy c :=
    Subgroup.mem_centralizer_singleton_iff.mp (h.L_le_centralizer hyL)
  have key : ∀ a ∈ A, ∃ z ∈ Subgroup.zpowers c, yy * a * yy⁻¹ = z * a := by
    intro a ha
    have haN : a ∈ Subgroup.normalizer (L : Set G) := h.AL ha
    have hyaA : yy * a * yy⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hyA a).mp ha
    have hzA : yy * a * yy⁻¹ * a⁻¹ ∈ A := A.mul_mem hyaA (A.inv_mem ha)
    have hzN : yy * a * yy⁻¹ * a⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.normalizer (L : Set G) |>.mul_mem
        ((Subgroup.normalizer (L : Set G)).mul_mem
          ((Subgroup.normalizer (L : Set G)).mul_mem hyNL haN)
          ((Subgroup.normalizer (L : Set G)).inv_mem hyNL))
        ((Subgroup.normalizer (L : Set G)).inv_mem haN)
    have hεa : barAct L ⟨a, haN⟩ ∈ barImage L E :=
      mem_barImage_iff.mpr ⟨a, haN, hEA ▸ ha, rfl⟩
    have htriv := congrArg (fun f : MulAut ↥(barImage L E) =>
      ((f ⟨barAct L ⟨a, haN⟩, hεa⟩ : ↥(barImage L E)) : MulAut (lBar L))) hy
    simp only [rho0_apply_coe, MulAut.one_apply] at htriv
    have hker : barAct L ⟨yy * a * yy⁻¹ * a⁻¹, hzN⟩ = 1 := by
      have e : (⟨yy * a * yy⁻¹ * a⁻¹, hzN⟩ : Subgroup.normalizer (L : Set G)) =
          ⟨yy, hyNL⟩ * ⟨a, haN⟩ * ⟨yy, hyNL⟩⁻¹ * ⟨a, haN⟩⁻¹ := rfl
      have hbar : barAct L ⟨yy, hyNL⟩ = actNLA A L y := by
        rw [← barAct_eq_actNLA]
        congr 1
        exact Subtype.ext hyy
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hbar, htriv, mul_inv_cancel]
    have hzK : yy * a * yy⁻¹ * a⁻¹ ∈ Sec4.thetaQuotCentralizer L :=
      ⟨⟨yy * a * yy⁻¹ * a⁻¹, hzN⟩, hker, rfl⟩
    have hzc : yy * a * yy⁻¹ * a⁻¹ ∈ A ⊓ Sec4.thetaQuotCentralizer L := ⟨hzA, hzK⟩
    rw [h.CA] at hzc
    exact ⟨_, hzc, by group⟩
  have hz3 : ∀ z ∈ Subgroup.zpowers c, z ^ 3 = 1 :=
    (CFSG.Open.isElemAbelian_zpowers h.c3).2
  have hzcomm : ∀ z ∈ Subgroup.zpowers c, yy * z * yy⁻¹ = z := by
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact mul_inv_eq_iff_eq_mul.mpr (hyc.zpow_right k).eq
  have hcube : ∀ a ∈ A, yy ^ 3 * a * (yy ^ 3)⁻¹ = a := by
    intro a ha
    obtain ⟨z, hz, e1⟩ := key a ha
    have e2 : yy * (z * a) * yy⁻¹ = z * (z * a) := by
      calc yy * (z * a) * yy⁻¹ = (yy * z * yy⁻¹) * (yy * a * yy⁻¹) := by group
        _ = z * (z * a) := by rw [hzcomm z hz, e1]
    have e3 : yy * (z * (z * a)) * yy⁻¹ = z * (z * (z * a)) := by
      calc yy * (z * (z * a)) * yy⁻¹ = (yy * z * yy⁻¹) * (yy * (z * a) * yy⁻¹) := by group
        _ = z * (z * (z * a)) := by rw [hzcomm z hz, e2]
    calc yy ^ 3 * a * (yy ^ 3)⁻¹ = yy * (yy * (yy * a * yy⁻¹) * yy⁻¹) * yy⁻¹ := by
          rw [pow_three']
          group
      _ = z * (z * (z * a)) := by rw [e1, e2, e3]
      _ = z ^ 3 * a := by
          rw [pow_three']
          simp only [mul_assoc]
      _ = a := by rw [hz3 z hz, one_mul]
  have hpow : (A.normalizerMonoidHom (y : Subgroup.normalizer (A : Set G))) ^ 3 =
      A.normalizerMonoidHom ((y : Subgroup.normalizer (A : Set G)) ^ 3) := (map_pow _ _ _).symm
  rw [hpow]
  refine MulEquiv.ext fun a => Subtype.ext ?_
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  show ((y : Subgroup.normalizer (A : Set G)) : G) ^ 3 * a *
    (((y : Subgroup.normalizer (A : Set G)) : G) ^ 3)⁻¹ = a
  rw [← hyy]
  exact hcube a a.2

theorem reflectsE_of_case211_eight (h : Item211LieProof.PairFacts A E U c L)
    (hA : Nat.card A = 3 ^ 3) (hD : Nonempty (starOf A L ≃* DihedralGroup 6)) :
    ReflectsE (lBar L) (barImage L E) := by
  obtain ⟨e⟩ := hD
  have hEA : E = A := Subgroup.eq_of_le_of_card_ge h.EA (by rw [hA, h.E27]; norm_num)
  let σ0 : ↥(NLA A L) →* ↥(starOf A L) := A.normalizerMonoidHom.subgroupMap (NLA A L)
  have hσ0 : Function.Surjective σ0 := MonoidHom.subgroupMap_surjective _ _
  let τ : ↥(NLA A L) →* DihedralGroup 6 := e.toMonoidHom.comp σ0
  have hτ : Function.Surjective τ := e.surjective.comp hσ0
  have hσ0coe : ∀ y : ↥(NLA A L), ((σ0 y : ↥(starOf A L)) : MulAut A) =
      A.normalizerMonoidHom (y : Subgroup.normalizer (A : Set G)) := fun y => rfl
  have hker : τ.ker ≤ (rho0 hEA).ker := by
    intro y hy
    apply rho0_eq_one_of_centralizes hEA y
    have h0 : e (σ0 y) = 1 := hy
    have h1 : σ0 y = 1 := e.injective (h0.trans (map_one e).symm)
    have h2 := congrArg Subtype.val h1
    rw [hσ0coe] at h2
    exact h2
  obtain ⟨ρ, hρ⟩ : ∃ ρ : DihedralGroup 6 →* MulAut ↥(barImage L E), ∀ y, ρ (τ y) = rho0 hEA y :=
    ⟨(MonoidHom.liftOfRightInverse τ (Function.surjInv hτ) (Function.rightInverse_surjInv hτ))
      ⟨rho0 hEA, hker⟩, fun y => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _⟩
  have hcube : ∀ d ∈ ρ.ker, d ^ 3 = 1 := by
    intro d hd
    obtain ⟨y, rfl⟩ := hτ d
    have hy : rho0 hEA y = 1 := by rw [← hρ]; exact hd
    have h3 := kernel_cube h hEA y hy
    show (e (σ0 y)) ^ 3 = 1
    rw [← map_pow]
    have : (σ0 y) ^ 3 = 1 := Subtype.ext (by
      show ((σ0 y : ↥(starOf A L)) : MulAut A) ^ 3 = 1
      rw [hσ0coe]
      exact h3)
    rw [this, map_one]
  have hodd : Odd (Nat.card ρ.ker) := by
    by_contra hnot
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hnot
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Finite ρ.ker := inferInstance
    obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := ρ.ker) 2 hnot
    have h3 : d ^ 3 = 1 := Subtype.ext (hcube d.1 d.2)
    have := orderOf_dvd_of_pow_eq_one h3
    rw [hd] at this
    omega
  haveI : IsMulCommutative ↥(barImage L E) := (Item211LieProof.isElemAbelian_barImage_E h).1
  haveI : Finite ↥(barImage L E) := Nat.finite_of_card_ne_zero (by
    rw [Item211LieProof.card_barImage_E h]; norm_num)
  letI : CommGroup ↥(barImage L E) := ElementaryAbelianModule.subgroupCommGroup _
    (Item211LieProof.isElemAbelian_barImage_E h).1
  have hE3' : ∀ ε : ↥(barImage L E), ε ^ 3 = 1 := fun ε =>
    Subtype.ext (by simpa using (Item211LieProof.isElemAbelian_barImage_E h).2 ε ε.2)
  obtain ⟨d, e₁, e₂, h1, h2, hf1, hf2⟩ :=
    exists_reflection_of_dihedral hE3' (Item211LieProof.card_barImage_E h) ρ hodd
  obtain ⟨y, rfl⟩ := hτ d
  rw [hρ] at hf1 hf2
  refine ⟨classNLA A L y, e₁, e₁.2, e₂, e₂.2, fun h' => h1 (Subtype.ext h'),
    fun h' => h2 (Subtype.ext h'), actNLA_conj_mem hEA y, ?_, ?_⟩
  · exact congrArg Subtype.val hf1
  · exact congrArg Subtype.val hf2

end Rho

end CFSG.RankThree.PartTwo.Sec21.Hering214
