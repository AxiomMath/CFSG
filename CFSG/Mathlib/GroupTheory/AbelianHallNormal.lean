module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Solvable
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

public section

namespace CFSG

open Subgroup
open scoped Pointwise

theorem conj_mem_of_permutes_of_centralizes {Γ : Type*} [Group Γ] [Finite Γ]
    {B V : Subgroup Γ} (hBab : IsMulCommutative ↥B) (hBodd : Odd (Nat.card B))
    (hV : IsPGroup 2 V) (hBV : (B : Set Γ) * (V : Set Γ) = (V : Set Γ) * (B : Set Γ))
    (hsolv : Group.IsSolvable ↥(B ⊔ V)) {y : Γ} (hy : y ∈ B)
    (hcent : ∀ R : Subgroup Γ, IsPGroup 2 R → R ≤ B ⊔ V → y ∈ normalizer (R : Set Γ) →
      ∀ r ∈ R, y * r = r * y)
    {h : Γ} (hh : h ∈ B ⊔ V) : h * y * h⁻¹ ∈ B := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup Γ := B ⊔ V with hHdef
  have hBH : B ≤ H := le_sup_left
  have hVH : V ≤ H := le_sup_right
  have hmul : ∀ g ∈ H, ∃ b ∈ B, ∃ v ∈ V, b * v = g := by
    let W : Subgroup Γ :=
      { carrier := (B : Set Γ) * (V : Set Γ)
        one_mem' := ⟨1, B.one_mem, 1, V.one_mem, one_mul 1⟩
        mul_mem' := by
          rintro _ _ ⟨b₁, hb₁, v₁, hv₁, rfl⟩ ⟨b₂, hb₂, v₂, hv₂, rfl⟩
          have h : v₁ * b₂ ∈ (V : Set Γ) * (B : Set Γ) := Set.mul_mem_mul hv₁ hb₂
          rw [← hBV] at h
          obtain ⟨b₃, hb₃, v₃, hv₃, he⟩ := h
          have he' : b₃ * v₃ = v₁ * b₂ := he
          refine ⟨b₁ * b₃, B.mul_mem hb₁ hb₃, v₃ * v₂, V.mul_mem hv₃ hv₂, ?_⟩
          calc b₁ * b₃ * (v₃ * v₂) = b₁ * (b₃ * v₃) * v₂ := by group
            _ = b₁ * (v₁ * b₂) * v₂ := by rw [he']
            _ = b₁ * v₁ * (b₂ * v₂) := by group
        inv_mem' := by
          rintro _ ⟨b, hb, v, hv, rfl⟩
          have h : v⁻¹ * b⁻¹ ∈ (V : Set Γ) * (B : Set Γ) :=
            Set.mul_mem_mul (V.inv_mem hv) (B.inv_mem hb)
          rw [← hBV] at h
          rwa [mul_inv_rev] }
    have hHW : H ≤ W := sup_le (fun b hb => ⟨b, hb, 1, V.one_mem, mul_one b⟩)
      (fun v hv => ⟨1, B.one_mem, v, hv, one_mul v⟩)
    intro g hg
    exact hHW hg
  have hBord : ∀ b ∈ B, Odd (orderOf b) := fun b hb =>
    Odd.of_dvd_nat hBodd (Subgroup.orderOf_dvd_natCard B hb)
  have hcop : ∀ {a : ℕ} {k : ℕ}, Odd a → Nat.Coprime (2 ^ k) a := fun ha =>
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 ha)
  have hodd : ∀ N : Subgroup ↥H, N.Normal → Odd (Nat.card N) → ∀ n ∈ N, (n : Γ) ∈ B := by
    intro N hN hNo n hn
    obtain ⟨b, hb, v, hv, he⟩ := hmul n n.2
    let q := QuotientGroup.mk' N
    have hbv : (⟨b, hBH hb⟩ : ↥H) * ⟨v, hVH hv⟩ = n := Subtype.ext he
    have h1 : q ⟨v, hVH hv⟩ = (q ⟨b, hBH hb⟩)⁻¹ := by
      have hn1 : q n = 1 := (QuotientGroup.eq_one_iff n).2 hn
      rw [← hbv, map_mul] at hn1
      exact eq_inv_of_mul_eq_one_right hn1
    obtain ⟨k, hk⟩ := hV ⟨v, hv⟩
    have hv2 : (⟨v, hVH hv⟩ : ↥H) ^ 2 ^ k = 1 := Subtype.ext (by
      simpa using congrArg Subtype.val hk)
    have hbo : Odd (orderOf (⟨b, hBH hb⟩ : ↥H)) := by
      rw [Subgroup.orderOf_mk]
      exact hBord b hb
    have hq1 : q ⟨v, hVH hv⟩ = 1 := by
      refine orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (hcop hbo)
        ((orderOf_map_dvd q _).trans (orderOf_dvd_of_pow_eq_one hv2)) ?_)
      rw [h1, orderOf_inv]
      exact orderOf_map_dvd q _
    have hvN : (⟨v, hVH hv⟩ : ↥H) ∈ N := (QuotientGroup.eq_one_iff _).1 hq1
    have hv1 : (⟨v, hVH hv⟩ : ↥H) = 1 := orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes
      (hcop hNo) (orderOf_dvd_of_pow_eq_one hv2) (Subgroup.orderOf_dvd_natCard N hvN))
    have hv1' : v = 1 := congrArg Subtype.val hv1
    rw [← he, hv1', mul_one]
    exact hb
  have hcent2 : ∀ r : ↥H, r ∈ CFSG.pCore 2 ↥H → y * r = r * y := by
    intro r hr
    refine hcent ((CFSG.pCore 2 ↥H).map H.subtype)
      ((CFSG.pCore_isPGroup (p := 2) (G := ↥H)).map _) (Subgroup.map_subtype_le _) ?_ r
      ⟨r, hr, rfl⟩
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨x', hx', rfl⟩
      exact ⟨⟨y, hBH hy⟩ * x' * (⟨y, hBH hy⟩)⁻¹,
        (CFSG.pCore_normal (p := 2) (G := ↥H)).conj_mem _ hx' _, rfl⟩
    · rintro ⟨x', hx', hxe⟩
      have hxe' : (x' : Γ) = y * x * y⁻¹ := hxe
      have hxH : x ∈ H := by
        have : x = y⁻¹ * (x' : Γ) * y := by rw [hxe']; group
        rw [this]
        exact H.mul_mem (H.mul_mem (H.inv_mem (hBH hy)) x'.2) (hBH hy)
      refine ⟨⟨x, hxH⟩, ?_, rfl⟩
      have h := (CFSG.pCore_normal (p := 2) (G := ↥H)).conj_mem _ hx' (⟨y, hBH hy⟩)⁻¹
      have hx'' : (⟨y, hBH hy⟩ : ↥H)⁻¹ * x' * ((⟨y, hBH hy⟩ : ↥H)⁻¹)⁻¹ = ⟨x, hxH⟩ :=
        Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, hxe']; group)
      rwa [hx''] at h
  set B' : Subgroup ↥H := B.subgroupOf H with hB'
  have hqB : ∀ q : (Nat.card ↥H).primeFactors.attach, q.1.1 ≠ 2 →
      CFSG.pCore q.1.1 ↥H ≤ B' := by
    intro q hq2 x hx
    have hqo : Odd (Nat.card (CFSG.pCore q.1.1 ↥H)) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := q.1.1) (G := ↥H))
      rw [hn]
      exact Odd.pow ((Nat.prime_of_mem_primeFactors q.1.2).odd_of_ne_two hq2)
    exact hodd _ CFSG.pCore_normal hqo x hx
  set y' : ↥H := ⟨y, hBH hy⟩ with hy'
  have hcp : ∀ q : (Nat.card ↥H).primeFactors.attach,
      zpowers y' ≤ centralizer (CFSG.pCore q.1.1 ↥H : Set ↥H) := by
    intro q
    rw [zpowers_le, mem_centralizer_iff]
    intro x hx
    by_cases hq2 : q.1.1 = 2
    · rw [hq2] at hx
      exact Subtype.ext (hcent2 x hx).symm
    · have hxB : (x : Γ) ∈ B := hqB q hq2 hx
      have h := congrArg Subtype.val (hBab.is_comm.comm ⟨(x : Γ), hxB⟩ ⟨y, hy⟩)
      exact Subtype.ext h
  have hyF : y' ∈ CFSG.fittingSubgroup ↥H :=
    ((CFSG.subgroup_le_centralizer_fitting_of_le_centralizer_pCores hcp).trans
      (CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv)) (mem_zpowers y')
  have hF2 : CFSG.fittingSubgroup ↥H ≤ CFSG.pCore 2 ↥H ⊔ B' := by
    rw [CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun q => ?_
    by_cases hq2 : q.1.1 = 2
    · rw [hq2]
      exact le_sup_left
    · exact le_sup_of_le_right (hqB q hq2)
  haveI : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  set h' : ↥H := ⟨h, hh⟩ with hh'
  have hxF : h' * y' * h'⁻¹ ∈ CFSG.fittingSubgroup ↥H :=
    (CFSG.fittingSubgroup_normal).conj_mem _ hyF h'
  have hxc : ∀ a ∈ CFSG.pCore 2 ↥H, h' * y' * h'⁻¹ * a = a * (h' * y' * h'⁻¹) := by
    intro a ha
    have ha' : h'⁻¹ * a * h'⁻¹⁻¹ ∈ CFSG.pCore 2 ↥H :=
      (CFSG.pCore_normal (p := 2) (G := ↥H)).conj_mem _ ha h'⁻¹
    have hc : y' * (h'⁻¹ * a * h'⁻¹⁻¹) = (h'⁻¹ * a * h'⁻¹⁻¹) * y' :=
      Subtype.ext (hcent2 _ ha')
    calc h' * y' * h'⁻¹ * a = h' * (y' * (h'⁻¹ * a * h'⁻¹⁻¹)) * h'⁻¹ := by group
      _ = h' * ((h'⁻¹ * a * h'⁻¹⁻¹) * y') * h'⁻¹ := by rw [hc]
      _ = a * (h' * y' * h'⁻¹) := by group
  have hmem := hF2 hxF
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  have hab' : a * b = h' * y' * h'⁻¹ := hab
  have hcomm : a * b = b * a := by
    have hb' : b = a⁻¹ * (h' * y' * h'⁻¹) := by rw [← hab']; group
    calc a * b = h' * y' * h'⁻¹ := hab'
      _ = a⁻¹ * (a * (h' * y' * h'⁻¹)) := by group
      _ = a⁻¹ * (h' * y' * h'⁻¹ * a) := by rw [hxc a ha]
      _ = b * a := by rw [hb']; group
  set m := orderOf (h' * y' * h'⁻¹) with hm
  have hmo : Odd m := by
    have hsc : SemiconjBy h' y' (h' * y' * h'⁻¹) := by
      unfold SemiconjBy
      group
    rw [hm, ← hsc.orderOf_eq, hy', Subgroup.orderOf_mk]
    exact hBord y hy
  have hpow : (a * b) ^ m = 1 := by rw [hab', hm, pow_orderOf_eq_one]
  rw [Commute.mul_pow hcomm m] at hpow
  have ham : a ^ m = (b ^ m)⁻¹ := eq_inv_of_mul_eq_one_left hpow
  have ham2 : a ^ m ∈ B' := by
    rw [ham]
    exact B'.inv_mem (B'.pow_mem hb m)
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨a, ha⟩
  have hak : a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have ham1 : a ^ m = 1 := by
    have hBo : Odd (orderOf (a ^ m)) := by
      rw [← Subgroup.orderOf_coe]
      exact hBord _ ham2
    have hpk : (a ^ m) ^ 2 ^ k = 1 := by rw [← pow_mul, mul_comm, pow_mul, hak, one_pow]
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (hcop hBo)
      (orderOf_dvd_of_pow_eq_one hpk) dvd_rfl)
  have ha1 : a = 1 := orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (hcop hmo)
    (orderOf_dvd_of_pow_eq_one hak) (orderOf_dvd_of_pow_eq_one ham1))
  have hxb : h' * y' * h'⁻¹ = b := by rw [← hab', ha1, one_mul]
  have h2 : ((h' * y' * h'⁻¹ : ↥H) : Γ) ∈ B := by rw [hxb]; exact hb
  exact h2

end CFSG
