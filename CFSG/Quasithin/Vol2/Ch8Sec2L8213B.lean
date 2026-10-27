module

public import CFSG.Quasithin.Vol2.Ch8Sec2KG
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped commutatorElement

section L8213B

variable {C : Type} [Group C] {z : C}

omit [Group C] in
theorem conj_mem_zpowers_iff_82 [Group C] (hzC : z ∈ Subgroup.center C) (c y : C) :
    c * y * c⁻¹ ∈ Subgroup.zpowers z ↔ y ∈ Subgroup.zpowers z := by
  have hcomm : ∀ k : ℤ, c * z ^ k * c⁻¹ = z ^ k := by
    intro k
    have h1 : c * z = z * c := Subgroup.mem_center_iff.mp hzC c
    rw [(Commute.zpow_right h1 k).eq, mul_inv_cancel_right]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    have h2 : y = c⁻¹ * z ^ k * c := by rw [hk]; group
    have h3 : c⁻¹ * z ^ k * c = z ^ k := by
      have := hcomm k
      calc c⁻¹ * z ^ k * c = c⁻¹ * (c * z ^ k * c⁻¹) * c := by rw [this]
        _ = z ^ k := by group
    rw [h2, h3]
    exact Subgroup.zpow_mem_zpowers z k
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [hcomm]
    exact Subgroup.zpow_mem_zpowers z k

variable {E : Subgroup C} [hEn : E.Normal]

omit hEn in
theorem normal_zpowers_subgroupOf_82 (hzC : z ∈ Subgroup.center C) :
    ((Subgroup.zpowers z).subgroupOf E).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact (conj_mem_zpowers_iff_82 hzC g x).mpr hx

variable [hZn : ((Subgroup.zpowers z).subgroupOf E).Normal]

@[expose] noncomputable def quotConj82 (hzC : z ∈ Subgroup.center C) (c : C) :
    MulAut (↥E ⧸ (Subgroup.zpowers z).subgroupOf E) :=
  QuotientGroup.congr _ _ (MulAut.conjNormal (H := E) c) (by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      have hy' : (y : C) ∈ Subgroup.zpowers z := hy
      have h1 : (((MulAut.conjNormal (H := E) c) y : ↥E) : C) = c * y * c⁻¹ :=
        MulAut.conjNormal_apply c y
      show (((MulAut.conjNormal (H := E) c) y : ↥E) : C) ∈ Subgroup.zpowers z
      rw [h1]
      exact (conj_mem_zpowers_iff_82 hzC c y).mpr hy'
    · intro x hx
      have hx' : (x : C) ∈ Subgroup.zpowers z := hx
      refine ⟨MulAut.conjNormal (H := E) c⁻¹ x, ?_, ?_⟩
      · show (((MulAut.conjNormal (H := E) c⁻¹) x : ↥E) : C) ∈ Subgroup.zpowers z
        rw [MulAut.conjNormal_apply]
        exact (conj_mem_zpowers_iff_82 hzC c⁻¹ x).mpr hx'
      · apply Subtype.ext
        change (((MulAut.conjNormal (H := E) c) (MulAut.conjNormal (H := E) c⁻¹ x) : ↥E) : C) = x
        rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply]
        group)

theorem quotConj82_mk (hzC : z ∈ Subgroup.center C) (c : C) (x : ↥E) :
    quotConj82 (E := E) hzC c (x : ↥E ⧸ (Subgroup.zpowers z).subgroupOf E) =
      ((MulAut.conjNormal (H := E) c x : ↥E) : ↥E ⧸ (Subgroup.zpowers z).subgroupOf E) :=
  rfl

noncomputable def quotActC82 (hzC : z ∈ Subgroup.center C) :
    C →* MulAut (↥E ⧸ (Subgroup.zpowers z).subgroupOf E) where
  toFun := quotConj82 hzC
  map_one' := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rw [quotConj82_mk, map_one]
    rfl
  map_mul' a b := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MulAut.mul_apply, quotConj82_mk, quotConj82_mk, quotConj82_mk, map_mul]
    rfl

theorem le_ker_quotActC82 (hzC : z ∈ Subgroup.center C)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ Subgroup.zpowers z) :
    E ≤ (quotActC82 (E := E) hzC).ker := by
  intro e he
  rw [MonoidHom.mem_ker]
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  change quotConj82 hzC e _ = _
  rw [quotConj82_mk, MulAut.one_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have h1 : (((MulAut.conjNormal (H := E) e y)⁻¹ * y : ↥E) : C) = ⁅e, (y : C)⁻¹⁆ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply,
      commutatorElement_def]
    group
  rw [h1]
  exact hcomm e he _ (E.inv_mem y.2)

noncomputable def quotActHom82 (hzC : z ∈ Subgroup.center C)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ Subgroup.zpowers z) :
    C ⧸ E →* MulAut (↥E ⧸ (Subgroup.zpowers z).subgroupOf E) :=
  QuotientGroup.lift E (quotActC82 hzC) (le_ker_quotActC82 hzC hcomm)

theorem injective_quotActHom82 (hzC : z ∈ Subgroup.center C)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ Subgroup.zpowers z)
    (hA18 : ∀ c : C, (∀ e ∈ E, ⁅c, e⁆ ∈ Subgroup.zpowers z) → c ∈ E) :
    Function.Injective (quotActHom82 (E := E) hzC hcomm) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MonoidHom.mem_ker] at hx
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  refine hA18 c fun e he => ?_
  have h1 := congrArg (fun φ : MulAut (↥E ⧸ (Subgroup.zpowers z).subgroupOf E) =>
    φ ((⟨e, he⟩ : ↥E) : ↥E ⧸ (Subgroup.zpowers z).subgroupOf E)) hx
  change quotConj82 hzC c _ = _ at h1
  rw [quotConj82_mk, MulAut.one_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
  have h2 : (((MulAut.conjNormal (H := E) c ⟨e, he⟩)⁻¹ * ⟨e, he⟩ : ↥E) : C) =
      c * e⁻¹ * c⁻¹ * e := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
    group
  rw [h2] at h1
  have h3 : ⁅c, e⁆ = e * (c * e⁻¹ * c⁻¹ * e)⁻¹ * e⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [h3, conj_mem_zpowers_iff_82 hzC]
  exact Subgroup.inv_mem _ h1

theorem centralizer_eq_center_82 [Finite C] (hT12 : KG82HatM22Twelve)
    (hzC : z ∈ Subgroup.center C) (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) (hzE : z ∈ E)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ Subgroup.zpowers z)
    (hsq : ∀ x ∈ E, x ^ 2 ∈ Subgroup.zpowers z) (hEc : Nat.card ↥E = 2 ^ 13)
    (hA18 : ∀ c : C, (∀ e ∈ E, ⁅c, e⁆ ∈ Subgroup.zpowers z) → c ∈ E)
    (K : Subgroup (C ⧸ E)) (hKq : CFSG.Open.IsQuasisimple ↥K)
    (hKZ : Nat.card ↥(Subgroup.center ↥K) = 3)
    (hKM : IsSporadic .M22 (↥K ⧸ Subgroup.center ↥K)) :
    Subgroup.centralizer (K : Set (C ⧸ E)) = (Subgroup.center ↥K).map K.subtype := by
  set Zq := (Subgroup.zpowers z).subgroupOf E with hZq
  let hW : CommGroup (↥E ⧸ Zq) :=
    { (inferInstance : Group (↥E ⧸ Zq)) with
      mul_comm := fun a b => by
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        have e1 : (((x * y)⁻¹ * (y * x) : ↥E) : C) = ⁅(y : C)⁻¹, (x : C)⁻¹⁆ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
          group
        rw [e1]
        exact hcomm _ (E.inv_mem y.2) _ (E.inv_mem x.2) }
  have hZqc : Nat.card ↥Zq = 2 := by
    rw [hZq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.zpowers_le.mpr hzE)).toEquiv, Nat.card_zpowers]
    exact orderOf_eq_prime hz2 hz1
  have hWc : Nat.card (↥E ⧸ Zq) = 2 ^ 12 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Zq
    rw [hEc, hZqc] at h1
    have : 2 ^ 13 = 2 ^ 12 * 2 := by norm_num
    omega
  have hW2 : ∀ w : ↥E ⧸ Zq, w ^ 2 = 1 := by
    intro w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hsq x x.2
  set ψ := quotActHom82 (E := E) hzC hcomm with hψ
  have hψi : Function.Injective ψ := injective_quotActHom82 hzC hcomm hA18
  set ρ : ↥K →* MulAut (↥E ⧸ Zq) := ψ.comp K.subtype with hρ
  have hρi : Function.Injective ρ := hψi.comp K.subtype_injective
  have hcen := hT12 ↥K hKq hKZ hKM (↥E ⧸ Zq) hWc hW2 ρ hρi
  apply le_antisymm
  · intro d hd
    have h1 : ψ d ∈ Subgroup.centralizer (ρ.range : Set (MulAut (↥E ⧸ Zq))) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨k, rfl⟩
      rw [hρ, MonoidHom.comp_apply, ← map_mul, ← map_mul]
      congr 1
      exact (Subgroup.mem_centralizer_iff.mp hd k k.2)
    rw [hcen] at h1
    obtain ⟨k, hk, hkd⟩ := h1
    have h2 : (k : C ⧸ E) = d := hψi hkd
    exact ⟨k, hk, h2⟩
  · rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have := Subgroup.mem_center_iff.mp hk ⟨h, hh⟩
    exact (congrArg Subtype.val this)

end L8213B

end CFSG.Quasithin.H13
