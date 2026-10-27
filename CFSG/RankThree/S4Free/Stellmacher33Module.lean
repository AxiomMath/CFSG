module

public import CFSG.RankThree.S4Free.Stellmacher33Dihedral
public import CFSG.RankThree.S4Free.StellmacherW
import CFSG.RankThree.S4Free.StellmacherL24
import TauCeti.Algebra.Group.Coprime
public import CFSG.RankThree.S4Free.StellmacherOffender

public section

namespace CFSG.RankThree.S4Free.Stell33

open Subgroup CFSG.Quasithin
open scoped commutatorElement

universe u

variable {K : Type*} [Group K]

def centMod (V V₁ E : Subgroup K) [V₁.Normal] : Subgroup K where
  carrier := {v | v ∈ V ∧ ∀ e ∈ E, e * v * e⁻¹ * v⁻¹ ∈ V₁}
  one_mem' := ⟨V.one_mem, fun e _ => by simp⟩
  mul_mem' := by
    rintro v₁ v₂ ⟨h₁, k₁⟩ ⟨h₂, k₂⟩
    refine ⟨V.mul_mem h₁ h₂, fun e he => ?_⟩
    have eq : e * (v₁ * v₂) * e⁻¹ * (v₁ * v₂)⁻¹ =
        (e * v₁ * e⁻¹ * v₁⁻¹) * (v₁ * (e * v₂ * e⁻¹ * v₂⁻¹) * v₁⁻¹) := by group
    rw [eq]
    exact V₁.mul_mem (k₁ e he) ((inferInstance : V₁.Normal).conj_mem _ (k₂ e he) v₁)
  inv_mem' := by
    rintro v ⟨h₁, k₁⟩
    refine ⟨V.inv_mem h₁, fun e he => ?_⟩
    have eq : e * v⁻¹ * e⁻¹ * v⁻¹⁻¹ = v⁻¹ * (e * v * e⁻¹ * v⁻¹)⁻¹ * v⁻¹⁻¹ := by group
    rw [eq]
    exact (inferInstance : V₁.Normal).conj_mem _ (V₁.inv_mem (k₁ e he)) v⁻¹

theorem mem_centMod {V V₁ E : Subgroup K} [V₁.Normal] {v : K} :
    v ∈ centMod V V₁ E ↔ v ∈ V ∧ ∀ e ∈ E, e * v * e⁻¹ * v⁻¹ ∈ V₁ :=
  Iff.rfl

def kerMod (V V₁ : Subgroup K) [V.Normal] [V₁.Normal] : Subgroup K where
  carrier := {g | ∀ v ∈ V, g * v * g⁻¹ * v⁻¹ ∈ V₁}
  one_mem' := fun v _ => by simp
  mul_mem' := by
    intro g₁ g₂ h₁ h₂ v hv
    have eq : g₁ * g₂ * v * (g₁ * g₂)⁻¹ * v⁻¹ =
        (g₁ * (g₂ * v * g₂⁻¹ * v⁻¹) * g₁⁻¹) * (g₁ * v * g₁⁻¹ * v⁻¹) := by group
    rw [eq]
    exact V₁.mul_mem ((inferInstance : V₁.Normal).conj_mem _ (h₂ v hv) g₁) (h₁ v hv)
  inv_mem' := by
    intro g h₁ v hv
    have hv' : g⁻¹ * v * g ∈ V := by
      simpa using (inferInstance : V.Normal).conj_mem _ hv g⁻¹
    have eq : g⁻¹ * v * g⁻¹⁻¹ * v⁻¹ = (g * (g⁻¹ * v * g) * g⁻¹ * (g⁻¹ * v * g)⁻¹)⁻¹ := by group
    rw [eq]
    exact V₁.inv_mem (h₁ _ hv')

instance kerMod_normal (V V₁ : Subgroup K) [V.Normal] [V₁.Normal] : (kerMod V V₁).Normal := by
  refine ⟨fun x hx k v hv => ?_⟩
  have hv' : k⁻¹ * v * k ∈ V := by
    simpa using (inferInstance : V.Normal).conj_mem _ hv k⁻¹
  have eq : k * x * k⁻¹ * v * (k * x * k⁻¹)⁻¹ * v⁻¹ =
      k * (x * (k⁻¹ * v * k) * x⁻¹ * (k⁻¹ * v * k)⁻¹) * k⁻¹ := by group
  rw [eq]
  exact (inferInstance : V₁.Normal).conj_mem _ (hx _ hv') k

theorem commutator_le_of_le_kerMod {V₀ V₁ R : Subgroup K} [V₀.Normal] [V₁.Normal]
    (hR : R ≤ kerMod V₀ V₁) : ⁅V₀, R⁆ ≤ V₁ := by
  rw [commutator_le]
  intro v hv r hr
  have h := V₁.inv_mem (hR hr v hv)
  rwa [commutatorElement_def, show v * r * v⁻¹ * r⁻¹ = (r * v * r⁻¹ * v⁻¹)⁻¹ by group]

theorem commutator_pResidual_eq [Finite K] {V₀ : Subgroup K} [V₀.Normal]
    (hV₀2 : ∀ x ∈ V₀, x * x = 1) :
    ⁅⁅V₀, pResidual 2 K⁆, pResidual 2 K⁆ = ⁅V₀, pResidual 2 K⁆ := by
  haveI : (pResidual 2 K).Normal := normal_pResidual 2 K
  set R := pResidual 2 K with hR
  set V := ⁅V₀, R⁆ with hV
  refine le_antisymm (commutator_le_left _ _) ?_
  set V' := ⁅V, R⁆ with hV'
  have hVV₀ : V ≤ V₀ := commutator_le_left _ _
  have hRk : R ≤ kerMod V₀ V' := by
    refine pResidual_le (fun x => ?_)
    obtain ⟨k, hk⟩ := exists_pow_mem_pResidual 2 x
    refine ⟨k + 1, fun v hv => ?_⟩
    set y := x ^ 2 ^ k with hy
    have ha : y * v * y⁻¹ * v⁻¹ ∈ V := by
      rw [hV, commutator_comm]
      exact commutator_mem_commutator hk hv
    have hya : y * (y * v * y⁻¹ * v⁻¹) * y⁻¹ * (y * v * y⁻¹ * v⁻¹)⁻¹ ∈ V' := by
      rw [hV', commutator_comm]
      exact commutator_mem_commutator hk ha
    have e : x ^ 2 ^ (k + 1) * v * (x ^ 2 ^ (k + 1))⁻¹ * v⁻¹ =
        (y * (y * v * y⁻¹ * v⁻¹) * y⁻¹ * (y * v * y⁻¹ * v⁻¹)⁻¹) *
          ((y * v * y⁻¹ * v⁻¹) * (y * v * y⁻¹ * v⁻¹)) := by
      rw [pow_succ, pow_mul, hy]
      group
    rw [e, hV₀2 _ (hVV₀ ha), mul_one]
    exact hya
  exact commutator_le_of_le_kerMod hRk

theorem eq_bot_of_commutator_eq_self [Finite K] {p : ℕ} [Fact p.Prime] {V Q : Subgroup K}
    (hV : IsPGroup p V) (hQ : IsPGroup p Q) (hQV : Q ≤ normalizer (V : Set K))
    (h : ⁅V, Q⁆ = V) : V = ⊥ := by
  have hT : IsPGroup p ↥(V ⊔ Q) := hV.to_sup_of_normal_left' hQ hQV
  obtain ⟨n, hn⟩ := (isNilpotent_iff_lowerCentralSeries (V ⊔ Q)).1 hT.isNilpotent
  have hle : ∀ k, V ≤ (V ⊔ Q).lowerCentralSeries k := by
    intro k
    induction k with
    | zero => exact le_sup_left
    | succ k ih =>
      rw [Subgroup.lowerCentralSeries_succ]
      calc V = ⁅V, Q⁆ := h.symm
        _ ≤ ⁅(V ⊔ Q).lowerCentralSeries k, V ⊔ Q⁆ := commutator_mono ih le_sup_right
  exact le_bot_iff.1 (hn ▸ hle n)

theorem exists_conj_mem_of_pow [Finite K] (P : Sylow 2 K) {t : K} {k : ℕ} (ht : t ^ 2 ^ k = 1) :
    ∃ h : K, h * t * h⁻¹ ∈ (P : Subgroup K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : IsPGroup 2 (zpowers t) := by
    rintro ⟨g, hg⟩
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hg
    refine ⟨k, Subtype.ext ?_⟩
    change (t ^ j) ^ 2 ^ k = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht, one_zpow]
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq K Q P
  refine ⟨h, ?_⟩
  rw [← hh, Sylow.coe_subgroup_smul]
  have := Subgroup.smul_mem_pointwise_smul t (MulAut.conj h) (Q : Subgroup K)
    (hQ (mem_zpowers t))
  simpa [MulAut.smul_def] using this

@[expose] def ThmA (𝒦 : HostClass) : Prop :=
  ∀ (V : Type u) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ H : Subgroup (MulAut V), 𝒦.Holds H → CFSG.Open.pCoreOf 2 H = ⊥ →
      (∀ a ∈ H, ∀ y ∈ H, a ^ 2 = 1 → y ^ 3 = 1 → a * y * a⁻¹ = y⁻¹ → y = 1) →
      ∀ A : Subgroup (MulAut V), A ≤ H → IsElemAbelian2 A → 2 * rk A ≤ rkIdx (fixV A)

theorem sq_relIndex_le_of_thmA {𝒦 : HostClass} (hThmA : ThmA.{u} 𝒦) {K : Type u} [Group K]
    [Finite K] (hK : 𝒦.Holds K) (hS3 : IsSym3Free K) {T : Subgroup K}
    (hTsyl : ∃ P : Sylow 2 K, (P : Subgroup K) = T)
    (hM : ∀ N : Subgroup K, N.Normal → T ⊓ N ≤ oTwo K ∨ pResidual 2 K ≤ N)
    {V₀ V V₁ : Subgroup K} [V₀.Normal] [V.Normal] [V₁.Normal] (hV₀T : V₀ ≤ T)
    (hV₀c : ∀ x ∈ V₀, ∀ y ∈ V₀, x * y = y * x) (hV₀2 : ∀ x ∈ V₀, x * x = 1)
    (hVdef : ⁅V₀, pResidual 2 K⁆ = V) (hV₁def : ⁅V, oTwo K⁆ = V₁) (hV : V ≠ ⊥)
    {E : Subgroup K} (hET : E ≤ T) (hE2 : ∀ e ∈ E, e * e ∈ oTwo K)
    (hEc : ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ * e₂ * e₁⁻¹ * e₂⁻¹ ∈ oTwo K) :
    ((oTwo K).relIndex E) ^ 2 ≤ (centMod V V₁ E).relIndex V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (pResidual 2 K).Normal := normal_pResidual 2 K
  obtain ⟨Tsyl, hTsyl⟩ := hTsyl
  have hT2 : IsPGroup 2 T := hTsyl ▸ Tsyl.isPGroup'
  have hO2 : IsPGroup 2 (oTwo K) := Stell.oTwo_isPGroup K
  have hVV₀ : V ≤ V₀ := hVdef ▸ commutator_le_left _ _
  have hVT : V ≤ T := hVV₀.trans hV₀T
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    hV₀c x (hVV₀ hx) y (hVV₀ hy)
  have hV2 : ∀ x ∈ V, x * x = 1 := fun x hx => hV₀2 x (hVV₀ hx)
  have hVR : ⁅V, pResidual 2 K⁆ = V := by
    rw [← hVdef]
    exact commutator_pResidual_eq hV₀2
  have hVV₁ : ¬ V ≤ V₁ := by
    intro hle
    apply hV
    refine eq_bot_of_commutator_eq_self (hT2.to_le hVT) hO2 (fun g _ => ?_) ?_
    · rw [normalizer_eq_top_iff.mpr inferInstance]
      exact mem_top g
    · exact le_antisymm (commutator_le_left _ _) (hV₁def ▸ hle)
  have hRC : ¬ pResidual 2 K ≤ kerMod V V₁ := fun hle =>
    hVV₁ (hVR ▸ commutator_le_of_le_kerMod hle)
  have hOC : oTwo K ≤ kerMod V V₁ := by
    intro o ho v hv
    rw [← hV₁def]
    have e : o * v * o⁻¹ * v⁻¹ = ⁅v, o⁆⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact inv_mem (commutator_mem_commutator hv ho)
  have hTC : T ⊓ kerMod V V₁ ≤ oTwo K := (hM _ inferInstance).resolve_right hRC
  letI : CommGroup (↥V ⧸ (V₁.subgroupOf V)) :=
    { (inferInstance : Group (↥V ⧸ (V₁.subgroupOf V))) with
      mul_comm := fun a b => by
        induction a using QuotientGroup.induction_on with
        | H a =>
        induction b using QuotientGroup.induction_on with
        | H b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        exact congrArg _ (Subtype.ext (hVc a a.2 b b.2)) }
  have hQ2 : ∀ q : ↥V ⧸ (V₁.subgroupOf V), q ^ 2 = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
    rw [← QuotientGroup.mk_pow, sq, show a * a = 1 from Subtype.ext (hV2 a a.2)]
    rfl
  have hconj : ∀ g : K,
      (V₁.subgroupOf V).map (MulAut.conjNormal g).toMonoidHom = V₁.subgroupOf V := by
    intro g
    ext r
    constructor
    · rintro ⟨y, hy, rfl⟩
      change (y : K) ∈ V₁ at hy
      change ((MulAut.conjNormal g y : ↥V) : K) ∈ V₁
      rw [MulAut.conjNormal_apply]
      exact (inferInstance : V₁.Normal).conj_mem _ hy g
    · intro hr
      refine ⟨(MulAut.conjNormal g)⁻¹ r, ?_, by simp⟩
      change (r : K) ∈ V₁ at hr
      change (((MulAut.conjNormal g)⁻¹ r : ↥V) : K) ∈ V₁
      rw [← map_inv, MulAut.conjNormal_apply]
      simpa using (inferInstance : V₁.Normal).conj_mem _ hr g⁻¹
  let ρ : K →* MulAut (↥V ⧸ (V₁.subgroupOf V)) :=
    { toFun := fun g =>
        QuotientGroup.congr (V₁.subgroupOf V) (V₁.subgroupOf V) (MulAut.conjNormal g) (hconj g)
      map_one' := by
        ext x
        induction x using QuotientGroup.induction_on with
        | H r => simp
      map_mul' := fun g g' => by
        ext x
        induction x using QuotientGroup.induction_on with
        | H r =>
          change (QuotientGroup.mk (MulAut.conjNormal (g * g') r) : ↥V ⧸ V₁.subgroupOf V) =
            QuotientGroup.mk (MulAut.conjNormal g (MulAut.conjNormal g' r))
          rw [map_mul, MulAut.mul_apply] }
  have hρmk : ∀ (g : K) (v : ↥V), ρ g (QuotientGroup.mk v) =
      QuotientGroup.mk (MulAut.conjNormal g v) := fun _ _ => rfl
  have hmkeq : ∀ a b : ↥V, (QuotientGroup.mk a : ↥V ⧸ (V₁.subgroupOf V)) = QuotientGroup.mk b ↔
      (a : K)⁻¹ * b ∈ V₁ := by
    intro a b
    rw [QuotientGroup.eq, mem_subgroupOf]
    rfl
  have hker : ∀ g, ρ g = 1 ↔ g ∈ kerMod V V₁ := by
    intro g
    constructor
    · intro h1 v hv
      have h2 := congrArg
        (fun f : MulAut (↥V ⧸ (V₁.subgroupOf V)) => f (QuotientGroup.mk ⟨v⁻¹, inv_mem hv⟩)) h1
      simp only [hρmk, MulAut.one_apply] at h2
      rw [hmkeq, MulAut.conjNormal_apply] at h2
      have e : g * v * g⁻¹ * v⁻¹ = (g * v⁻¹ * g⁻¹)⁻¹ * v⁻¹ := by group
      rw [e]
      exact h2
    · intro hg
      ext x
      induction x using QuotientGroup.induction_on with
      | H v =>
      rw [hρmk, MulAut.one_apply, hmkeq, MulAut.conjNormal_apply]
      have h2 := hg _ (inv_mem v.2)
      have e : (g * (v : K) * g⁻¹)⁻¹ * v = g * (v : K)⁻¹ * g⁻¹ * (v : K)⁻¹⁻¹ := by group
      rw [e]
      exact h2
  haveI : Finite ↥ρ.range := Finite.of_surjective _ ρ.rangeRestrict_surjective
  have hKH : 𝒦.Holds ρ.range :=
    (hK.quotient ρ.ker).of_mulEquiv (QuotientGroup.quotientKerEquivRange ρ)
  have hker' : ∀ g, ρ.rangeRestrict g = 1 ↔ g ∈ kerMod V V₁ := fun g => by
    rw [← hker g, ← Subtype.coe_inj, MonoidHom.coe_rangeRestrict, OneMemClass.coe_one]
  have hpcore : CFSG.Open.pCoreOf 2 ρ.range = ⊥ := by
    have hNn : (CFSG.pCore 2 ↥ρ.range).Normal := Subgroup.sSup_normal _ (fun M hM => hM.1)
    have hN2 : IsPGroup 2 (CFSG.pCore 2 ↥ρ.range) :=
      Sylow.sSup_of_normal _ (fun M hM => hM.2) (fun M hM => hM.1)
    suffices hN : CFSG.pCore 2 ↥ρ.range = ⊥ by
      rw [CFSG.Open.pCoreOf, hN, Subgroup.map_bot]
    set N' := (CFSG.pCore 2 ↥ρ.range).comap ρ.rangeRestrict with hN'
    haveI : N'.Normal := hNn.comap _
    have hRN : ¬ pResidual 2 K ≤ N' := by
      intro hle
      apply hRC
      refine pResidual_le (fun x => ?_)
      obtain ⟨k₁, hk₁⟩ := exists_pow_mem_pResidual 2 x
      obtain ⟨k₂, hk₂⟩ := hN2 ⟨ρ.rangeRestrict (x ^ 2 ^ k₁), hle hk₁⟩
      refine ⟨k₁ + k₂, (hker' _).mp ?_⟩
      rw [pow_add, pow_mul, map_pow]
      exact congrArg Subtype.val hk₂
    have hTN : T ⊓ N' ≤ oTwo K := (hM N' inferInstance).resolve_right hRN
    rw [eq_bot_iff]
    intro n hn
    obtain ⟨g, rfl⟩ := ρ.rangeRestrict_surjective n
    have hgN : g ∈ N' := hn
    suffices hgC : g ∈ kerMod V V₁ by
      rw [mem_bot]
      exact (hker' g).mpr hgC
    obtain ⟨a, m', hm', hgm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
    have h1 : g ^ 2 ^ a ∈ kerMod V V₁ := by
      apply (hker' _).mp
      obtain ⟨b, hb⟩ := hN2 ⟨ρ.rangeRestrict (g ^ 2 ^ a), N'.pow_mem hgN _⟩
      have hb' : ρ.rangeRestrict (g ^ 2 ^ a) ^ 2 ^ b = 1 := congrArg Subtype.val hb
      have hm'1 : ρ.rangeRestrict (g ^ 2 ^ a) ^ m' = 1 := by
        rw [← map_pow, ← pow_mul, ← hgm, pow_orderOf_eq_one, map_one]
      have h3 := mem_of_odd_pow_mem (K := (⊥ : Subgroup ↥ρ.range)) hb' hm'
        (by rw [hm'1]; exact one_mem _)
      rwa [mem_bot] at h3
    have h2 : g ^ m' ∈ kerMod V V₁ := by
      apply hOC
      have ht : (g ^ m') ^ 2 ^ a = 1 := by
        rw [← pow_mul, mul_comm, ← hgm, pow_orderOf_eq_one]
      obtain ⟨h, hh⟩ := exists_conj_mem_of_pow Tsyl ht
      rw [hTsyl] at hh
      have hhN : h * g ^ m' * h⁻¹ ∈ N' :=
        (inferInstance : N'.Normal).conj_mem _ (N'.pow_mem hgN _) h
      have hhO := hTN ⟨hh, hhN⟩
      have h5 := (inferInstance : (oTwo K).Normal).conj_mem _ hhO h⁻¹
      rwa [inv_inv, show h⁻¹ * (h * g ^ m' * h⁻¹) * h = g ^ m' by group] at h5
    obtain ⟨i, j, hij⟩ := TauCeti.exists_zpow_mul_zpow_eq_of_coprime (G := K)
      (Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm'))
    rw [← hij g]
    exact mul_mem (zpow_mem h1 i) (zpow_mem h2 j)
  have hS3H : ∀ a ∈ ρ.range, ∀ y ∈ ρ.range, a ^ 2 = 1 → y ^ 3 = 1 → a * y * a⁻¹ = y⁻¹ →
      y = 1 := by
    intro a ha y hy ha2 hy3 hay
    have hH3 : IsSym3Free ↥ρ.range :=
      (hS3.quotient ρ.ker).of_mulEquiv (QuotientGroup.quotientKerEquivRange ρ)
    have h1 := hH3.eq_one_of_inv (a := ⟨a, ha⟩) (y := ⟨y, hy⟩) (Subtype.ext ha2)
      (Subtype.ext hy3) (Subtype.ext hay)
    exact congrArg Subtype.val h1
  have hEA : IsElemAbelian2 (E.map ρ) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨e₁, he₁, rfl⟩ _ ⟨e₂, he₂, rfl⟩
      have h1 : ρ (e₁ * e₂ * e₁⁻¹ * e₂⁻¹) = 1 := (hker _).mpr (hOC (hEc e₁ he₁ e₂ he₂))
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      calc ρ e₁ * ρ e₂ = (ρ e₁ * ρ e₂ * (ρ e₁)⁻¹ * (ρ e₂)⁻¹) * (ρ e₂ * ρ e₁) := by group
        _ = ρ e₂ * ρ e₁ := by rw [h1, one_mul]
    · rintro _ ⟨e, he, rfl⟩
      rw [sq, ← map_mul]
      exact (hker _).mpr (hOC (hE2 e he))
  have hA := hThmA _ hQ2 ρ.range hKH hpcore hS3H (E.map ρ) (map_le_range ρ E) hEA
  have hcardE : Nat.card (E.map ρ) = (oTwo K).relIndex E := by
    rw [← MonoidHom.domRestrict_range, ← index_ker, MonoidHom.ker_domRestrict]
    change ρ.ker.relIndex E = _
    rw [← inf_relIndex_right, ← inf_relIndex_right (H := oTwo K)]
    congr 1
    ext g
    constructor
    · rintro ⟨hgk, hgE⟩
      exact ⟨hTC ⟨hET hgE, (hker g).mp hgk⟩, hgE⟩
    · rintro ⟨hgO, hgE⟩
      exact ⟨(hker g).mpr (hOC hgO), hgE⟩
  have hfix : (fixV (E.map ρ)).index = (centMod V V₁ E).relIndex V := by
    have hcomap : (fixV (E.map ρ)).comap (QuotientGroup.mk' (V₁.subgroupOf V)) =
        (centMod V V₁ E).subgroupOf V := by
      ext v
      rw [mem_comap, mem_subgroupOf, QuotientGroup.mk'_apply, mem_fixV]
      have hcomm : ∀ e : K, (e * (v : K) * e⁻¹) * (v : K)⁻¹ ∈ V₁ ↔
          (e * (v : K) * e⁻¹)⁻¹ * v ∈ V₁ := by
        intro e
        have hx : e * (v : K) * e⁻¹ ∈ V := by
          simpa using (inferInstance : V.Normal).conj_mem _ v.2 e
        have hxv := hVc _ v.2 _ hx
        have e1 : (e * (v : K) * e⁻¹) * (v : K)⁻¹ = ((e * (v : K) * e⁻¹)⁻¹ * v)⁻¹ := by
          rw [show ((e * (v : K) * e⁻¹)⁻¹ * v)⁻¹ = (v : K)⁻¹ * (e * (v : K) * e⁻¹) by group]
          calc (e * (v : K) * e⁻¹) * (v : K)⁻¹
              = (v : K)⁻¹ * ((v : K) * (e * (v : K) * e⁻¹)) * (v : K)⁻¹ := by group
            _ = (v : K)⁻¹ * ((e * (v : K) * e⁻¹) * v) * (v : K)⁻¹ := by rw [hxv]
            _ = (v : K)⁻¹ * (e * (v : K) * e⁻¹) := by group
        rw [e1]
        refine ⟨fun h => ?_, fun h => V₁.inv_mem h⟩
        rw [← inv_inv ((e * (v : K) * e⁻¹)⁻¹ * v)]
        exact V₁.inv_mem h
      constructor
      · intro hv
        refine ⟨v.2, fun e he => ?_⟩
        have h1 := hv (ρ e) ⟨e, he, rfl⟩
        rw [hρmk, hmkeq, MulAut.conjNormal_apply] at h1
        exact (hcomm e).mpr h1
      · rintro ⟨-, hv⟩ _ ⟨e, he, rfl⟩
        rw [hρmk, hmkeq, MulAut.conjNormal_apply]
        exact (hcomm e).mp (hv e he)
    have h1 := index_comap_of_surjective (H := fixV (E.map ρ))
      (QuotientGroup.mk'_surjective (V₁.subgroupOf V))
    exact h1.symm.trans (congrArg Subgroup.index hcomap)
  have hrk : rk ↥(E.map ρ) = Stell.mRel (oTwo K) E := by
    rw [rk, hcardE, Stell.relIndex_eq_two_pow (hT2.to_le hET), padicValNat.prime_pow]
  have hrkIdx : rkIdx (fixV (E.map ρ)) = Stell.mRel (centMod V V₁ E) V := by
    rw [rkIdx, hfix, Stell.relIndex_eq_two_pow (hT2.to_le hVT), padicValNat.prime_pow]
  rw [hrk, hrkIdx] at hA
  rw [Stell.relIndex_eq_two_pow (hT2.to_le hET), Stell.relIndex_eq_two_pow (hT2.to_le hVT),
    ← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.RankThree.S4Free.Stell33
