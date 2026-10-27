module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesSplit
public import CFSG.HardMathSupport.Lang.AnisoE6.PlaneConjGen
public import CFSG.LieType.SeitzGeneration.ExcPlaneFamilies
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.StandardType

namespace ExcFrames

section Centralize

variable {Γ : Type*} [Group Γ] {p : ℕ} [Fact p.Prime]

theorem centralizes_of_pPart_mem (Δ : Subgroup Γ) [Finite Δ]
    (hab : ∀ Q : Subgroup Γ, Q ≤ Δ → IsPGroup p Q → ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    {E : Subgroup Γ} (hE : IsPGroup p E) (hEΔ : E ≤ Δ) {y : Γ} (hyΔ : y ∈ Δ)
    (hyN : y ∈ Subgroup.normalizer (E : Set Γ)) (hyp : ∀ e ∈ E, y ^ p * e * (y ^ p)⁻¹ = e) :
    ∀ e ∈ E, y * e * y⁻¹ = e := by
  have hpp : p.Prime := Fact.out
  have hn : orderOf y ≠ 0 := by
    have h1 : orderOf (⟨y, hyΔ⟩ : Δ) ≠ 0 := (orderOf_pos _).ne'
    rwa [← Subgroup.orderOf_coe] at h1
  obtain ⟨a, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hpp.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hn (by simpa using hnm)
  have hmdvd : m ∣ orderOf y := ⟨p ^ a, by rw [hnm, mul_comm]⟩
  have hzord : orderOf (y ^ m) = p ^ a := by
    rw [orderOf_pow_of_dvd hm0 hmdvd, hnm, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  set z : Γ := y ^ m with hz
  have hzΔ : z ∈ Δ := Δ.pow_mem hyΔ m
  have hzP : IsPGroup p (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := a) (by rw [Nat.card_zpowers, hzord])
  have hzN : Subgroup.zpowers z ≤ Subgroup.normalizer (E : Set Γ) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.pow_mem _ hyN m
  have hQ : IsPGroup p (E ⊔ Subgroup.zpowers z : Subgroup Γ) := hE.to_sup_of_normal_left' hzP hzN
  have hQΔ : (E ⊔ Subgroup.zpowers z : Subgroup Γ) ≤ Δ :=
    sup_le hEΔ ((Subgroup.zpowers_le (H := Δ)).2 hzΔ)
  have hzcomm : ∀ e ∈ E, e * z = z * e := fun e he =>
    hab _ hQΔ hQ e (Subgroup.mem_sup_left he) z (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have hzC : z ∈ Subgroup.centralizer (E : Set Γ) := Subgroup.mem_centralizer_iff.2 hzcomm
  have hypC : y ^ p ∈ Subgroup.centralizer (E : Set Γ) := by
    refine Subgroup.mem_centralizer_iff.2 fun e he => ?_
    have h := hyp e he
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hcop : IsCoprime (p : ℤ) (m : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hpp).2 hpm)
  obtain ⟨u, v, huv⟩ := hcop
  have hyeq : y = (y ^ p) ^ u * z ^ v := by
    have h1 : y = y ^ ((p : ℤ) * u + (m : ℤ) * v) := by
      rw [mul_comm (p : ℤ) u, mul_comm (m : ℤ) v, huv, zpow_one]
    rw [hz]
    conv_lhs => rw [h1]
    rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  have hyC : y ∈ Subgroup.centralizer (E : Set Γ) := by
    rw [hyeq]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hypC u) (Subgroup.zpow_mem _ hzC v)
  intro e he
  have h := Subgroup.mem_centralizer_iff.1 hyC e he
  rw [mul_inv_eq_iff_eq_mul]
  exact h.symm

theorem centralizes_of_fixedConj (Δ : Subgroup Γ) [Finite Δ]
    (hab : ∀ Q : Subgroup Γ, Q ≤ Δ → IsPGroup p Q → ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    (s : Γ →* Γ) {E : Subgroup Γ} (hE : IsPGroup p E) (hEΔ : E ≤ Δ)
    (hEs : ∀ e ∈ E, s e = e) {c : Γ} (hcΔ : c ∈ Δ) (hscΔ : s c ∈ Δ) {x : Γ} (hxΔ : x ∈ Δ)
    {Bs : Subgroup Γ} (hBs : Bs = E.map (MulAut.conj c).toMonoidHom)
    (hnorm : ∀ b ∈ Bs, x * s b * x⁻¹ ∈ Bs)
    (hord : ∀ b ∈ Bs, (fun h => x * s h * x⁻¹)^[p] b = b) :
    ∀ b ∈ Bs, x * s b * x⁻¹ = b := by
  obtain ⟨y, hy⟩ : ∃ y : Γ, y = c⁻¹ * x * s c := ⟨_, rfl⟩
  have hyΔ : y ∈ Δ := hy ▸ Δ.mul_mem (Δ.mul_mem (Δ.inv_mem hcΔ) hxΔ) hscΔ
  have hmem : ∀ e ∈ E, c * e * c⁻¹ ∈ Bs := fun e he => by rw [hBs]; exact ⟨e, he, rfl⟩
  have key : ∀ e ∈ E, x * s (c * e * c⁻¹) * x⁻¹ = c * (y * e * y⁻¹) * c⁻¹ := by
    intro e he
    rw [map_mul, map_mul, map_inv, hEs e he, hy]
    group
  have hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E := by
    intro e he
    have h1 := hnorm _ (hmem e he)
    rw [key e he, hBs] at h1
    obtain ⟨e', he', h'⟩ := h1
    have h'' : c * e' * c⁻¹ = c * (y * e * y⁻¹) * c⁻¹ := h'
    have h3 : e' = y * e * y⁻¹ := by
      have := mul_right_cancel h''
      exact mul_left_cancel this
    rw [← h3]
    exact he'
  have hpow : ∀ k : ℕ, ∀ e ∈ E, y ^ k * e * (y ^ k)⁻¹ ∈ E := by
    intro k
    induction k with
    | zero => intro e he; simpa using he
    | succ k ih =>
      intro e he
      have h1 := hyE _ (ih e he)
      have h2 : y * (y ^ k * e * (y ^ k)⁻¹) * y⁻¹ = y ^ (k + 1) * e * (y ^ (k + 1))⁻¹ := by
        rw [pow_succ', mul_inv_rev]
        group
      rwa [h2] at h1
  have hyN : y ∈ Subgroup.normalizer (E : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    refine ⟨fun he => hyE e he, fun he => ?_⟩
    have hpos : 0 < orderOf y := by
      have h1 : 0 < orderOf (⟨y, hyΔ⟩ : Δ) := orderOf_pos _
      rwa [← Subgroup.orderOf_coe] at h1
    have h1 : y ^ (orderOf y - 1) * y = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
    have h2 := hpow (orderOf y - 1) _ he
    rw [eq_inv_of_mul_eq_one_left h1] at h2
    have h3 : y⁻¹ * (y * e * y⁻¹) * y⁻¹⁻¹ = e := by group
    rwa [h3] at h2
  have hit : ∀ k : ℕ, ∀ e ∈ E, (fun h => x * s h * x⁻¹)^[k] (c * e * c⁻¹) =
      c * (y ^ k * e * (y ^ k)⁻¹) * c⁻¹ := by
    intro k
    induction k with
    | zero => intro e he; simp
    | succ k ih =>
      intro e he
      rw [Function.iterate_succ_apply', ih e he]
      show x * s (c * (y ^ k * e * (y ^ k)⁻¹) * c⁻¹) * x⁻¹ = _
      rw [key _ (hpow k e he)]
      congr 2
      rw [pow_succ', mul_inv_rev]
      group
  have hyp : ∀ e ∈ E, y ^ p * e * (y ^ p)⁻¹ = e := by
    intro e he
    have h1 := hord _ (hmem e he)
    rw [hit p e he] at h1
    have h2 := mul_right_cancel h1
    exact mul_left_cancel h2
  have hfin := centralizes_of_pPart_mem Δ hab hE hEΔ hyΔ hyN hyp
  intro b hb
  rw [hBs] at hb
  obtain ⟨e, he, rfl⟩ := hb
  have h1 : (MulAut.conj c).toMonoidHom e = c * e * c⁻¹ := rfl
  rw [h1, key e he, hfin e he]

theorem mem_of_pow_eq_one_of_pow_mem (H : Subgroup Γ) {z : Γ} {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : z ^ a = 1) (hb : z ^ b ∈ H) : z ∈ H := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
  have h1 : z = z ^ ((a : ℤ) * u + (b : ℤ) * v) := by
    rw [mul_comm (a : ℤ) u, mul_comm (b : ℤ) v, huv, zpow_one]
  rw [h1, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, ha, one_zpow, one_mul]
  exact Subgroup.zpow_mem _ hb v

theorem pow_mem_of_mem_normalizer {C : Subgroup Γ} {d c : Γ}
    (hd : d ∈ Subgroup.normalizer (C : Set Γ)) (hc : c ∈ C) (hdk : ∀ j : ℕ, d ^ j ∈ Subgroup.normalizer (C : Set Γ))
    (k : ℕ) (hk : d ^ k ∈ C) : (d * c) ^ k ∈ C := by
  have key : ∀ j : ℕ, ∃ c' ∈ C, (d * c) ^ j = c' * d ^ j := by
    intro j
    induction j with
    | zero => exact ⟨1, C.one_mem, by simp⟩
    | succ j ih =>
      obtain ⟨c', hc', h⟩ := ih
      have hconj : d ^ (j + 1) * c * (d ^ (j + 1))⁻¹ ∈ C :=
        (Subgroup.mem_normalizer_iff.1 (hdk (j + 1)) c).1 hc
      refine ⟨c' * (d ^ (j + 1) * c * (d ^ (j + 1))⁻¹), C.mul_mem hc' hconj, ?_⟩
      rw [pow_succ, h]
      group
  obtain ⟨c', hc', h⟩ := key k
  rw [h]
  exact C.mul_mem hc' hk

end Centralize

section Conj

open CFSG.LieType.SeitzGeneration CFSG.Open

theorem exists_conj_eq_of_le_card_of_sylowTorus {G : Type*} [Group G] [Finite G] {p m : ℕ}
    [Fact p.Prime] (h : SylowTorus G p m) {E E' : Subgroup G} (hE : IsElemAbelian p E)
    (hEc : p ^ m ≤ Nat.card E) (hE' : IsElemAbelian p E') (hEc' : p ^ m ≤ Nat.card E') :
    ∃ g : G, E.map (MulAut.conj g).toMonoidHom = E' :=
  CFSG.HardMathSupport.Lang.AnisoE6.exists_conj_eq_of_sylowTorus h hE
    (le_antisymm (h.rank_le Fact.out hE) hEc) hE' (le_antisymm (h.rank_le Fact.out hE') hEc')

end Conj

section Master

open CFSG.LieType.SeitzGeneration CFSG.Open
open scoped Pointwise

variable {Γ : Type*} [Group Γ] {p m k : ℕ} [Fact p.Prime]

theorem fixes_of_sylowTorus_of_fixedSubgroup {C Dg : Subgroup Γ}
    [Finite (C ⊔ Dg : Subgroup Γ)] (hDg : Dg ≤ Subgroup.normalizer (C : Set Γ)) (hk : ¬ p ∣ k)
    (hkDg : ∀ d ∈ Dg, d ^ k ∈ C) (hSyl : SylowTorus C p m) (s : Γ →* Γ)
    (hsC : ∀ h ∈ C, s h ∈ C) {E : Subgroup Γ} (hEC : E ≤ C) (hE : IsElemAbelian p E)
    (hEcard : p ^ m ≤ Nat.card E) (hEs : ∀ e ∈ E, s e = e) {Bs : Subgroup Γ} (hBsC : Bs ≤ C)
    (hBs : IsElemAbelian p Bs) (hBscard : p ^ m ≤ Nat.card Bs) {x : Γ} (hx : x ∈ C ⊔ Dg)
    (hnorm : ∀ b ∈ Bs, x * s b * x⁻¹ ∈ Bs)
    (hord : ∀ b ∈ Bs, (fun h => x * s h * x⁻¹)^[p] b = b) :
    ∀ b ∈ Bs, x * s b * x⁻¹ = b := by
  have hpp : p.Prime := Fact.out
  haveI : Finite C := Finite.of_injective (Subgroup.inclusion (le_sup_left : C ≤ C ⊔ Dg))
    (Subgroup.inclusion_injective _)
  have hΔk : ∀ z ∈ C ⊔ Dg, z ^ k ∈ C := by
    intro z hz
    have hz' : z ∈ (Dg : Set Γ) * (C : Set Γ) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Dg C hDg, sup_comm]
      exact hz
    obtain ⟨d, hd, c, hc, rfl⟩ := Set.mem_mul.1 hz'
    exact pow_mem_of_mem_normalizer (hDg hd) hc (fun j => hDg (Dg.pow_mem hd j)) k (hkDg d hd)
  have hpC : ∀ Q : Subgroup Γ, Q ≤ C ⊔ Dg → IsPGroup p Q → Q ≤ C := by
    intro Q hQ hQp z hz
    obtain ⟨j, hj⟩ := hQp ⟨z, hz⟩
    have hj' : z ^ p ^ j = 1 := congrArg Subtype.val hj
    exact mem_of_pow_eq_one_of_pow_mem C
      (Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hpp).2 hk)) hj' (hΔk z (hQ hz))
  have hab : ∀ Q : Subgroup Γ, Q ≤ C ⊔ Dg → IsPGroup p Q → ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    intro Q hQ hQp a ha b hb
    have hQC := hpC Q hQ hQp
    have hP : IsPGroup p (Q.subgroupOf C) := hQp.comap_subtype
    have h := CFSG.HardMathSupport.Timmesfeld.CrossChar.mul_comm_of_sylowTorus hSyl hP
      (a := ⟨a, hQC ha⟩) (b := ⟨b, hQC hb⟩) ha hb
    exact congrArg Subtype.val h
  have hE' : IsElemAbelian p (E.subgroupOf C) :=
    isElemAbelian_comap_frame C.subtype Subtype.val_injective hE
  have hB' : IsElemAbelian p (Bs.subgroupOf C) :=
    isElemAbelian_comap_frame C.subtype Subtype.val_injective hBs
  have hEc' : p ^ m ≤ Nat.card (E.subgroupOf C) := by
    rw [show E.subgroupOf C = E.comap C.subtype from rfl,
      card_comap_of_le_range C.subtype Subtype.val_injective (by rwa [Subgroup.range_subtype])]
    exact hEcard
  have hBc' : p ^ m ≤ Nat.card (Bs.subgroupOf C) := by
    rw [show Bs.subgroupOf C = Bs.comap C.subtype from rfl,
      card_comap_of_le_range C.subtype Subtype.val_injective (by rwa [Subgroup.range_subtype])]
    exact hBscard
  obtain ⟨c', hc'⟩ := exists_conj_eq_of_le_card_of_sylowTorus hSyl hE' hEc' hB' hBc'
  have hBsE : Bs = E.map (MulAut.conj (c' : Γ)).toMonoidHom := by
    ext b
    constructor
    · intro hb
      have hb' : (⟨b, hBsC hb⟩ : C) ∈ Bs.subgroupOf C := hb
      rw [← hc'] at hb'
      obtain ⟨e', he', hbe⟩ := hb'
      exact ⟨(e' : Γ), he', congrArg Subtype.val hbe⟩
    · rintro ⟨e, he, rfl⟩
      have he' : (⟨e, hEC he⟩ : C) ∈ E.subgroupOf C := he
      have h1 : (MulAut.conj c').toMonoidHom ⟨e, hEC he⟩ ∈ Bs.subgroupOf C := by
        rw [← hc']
        exact ⟨_, he', rfl⟩
      exact h1
  have hc'Δ : (c' : Γ) ∈ C ⊔ Dg := Subgroup.mem_sup_left c'.2
  have hsc'Δ : s (c' : Γ) ∈ C ⊔ Dg := Subgroup.mem_sup_left (hsC _ c'.2)
  exact centralizes_of_fixedConj (C ⊔ Dg) hab s (isPGroup_of_isElemAbelian hE)
    (hEC.trans le_sup_left) hEs hc'Δ hsc'Δ hx hBsE hnorm hord

end Master

end ExcFrames

end CFSG.StandardType
