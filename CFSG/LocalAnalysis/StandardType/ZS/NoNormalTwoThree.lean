module

public import CFSG.LocalAnalysis.StandardType.ZS.AbelianNormal
public import CFSG.LocalAnalysis.StandardType.ZS.ScalarCommutator
public import CFSG.LocalAnalysis.StandardType.ZS.FrameFour
public import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
public import CFSG.GroupTheory.CoprimeActionSupport.FaithfulIrreduciblePCoreTrivial
import CFSG.GroupTheory.CommuteOfSqEqOne

public section

namespace CFSG.StandardType.ZS

open Subgroup

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  [Module.Finite (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}

local notation "mk" => (QuotientGroup.mk : A → A ⧸ Subgroup.center A)

omit [Module.Finite (ZMod p) U] in
private theorem znn_pow_apply_of_smul_id {z : U ≃ₗ[ZMod p] U} {ζ : ZMod p}
    (hz : (z : U →ₗ[ZMod p] U) = ζ • LinearMap.id) (n : ℕ) (w : U) :
    (z ^ n) w = (ζ ^ n) • w := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hz_apply : z w = ζ • w := by
        simpa using congrArg (fun f : U →ₗ[ZMod p] U => f w) hz
      calc
        (z ^ (n + 1)) w = z ((z ^ n) w) := by
          rw [pow_succ', LinearEquiv.mul_apply]
        _ = z ((ζ ^ n) • w) := by rw [ih]
        _ = (ζ ^ n) • z w := by rw [LinearEquiv.map_smul]
        _ = (ζ ^ n) • (ζ • w) := by rw [hz_apply]
        _ = (ζ ^ (n + 1)) • w := by rw [smul_smul, pow_succ]

omit [Module.Finite (ZMod p) U] in
private theorem znn_le_center_of_refl_centralizes (hgen : ReflGen p A)
    {N₀ : Subgroup (A ⧸ Subgroup.center A)}
    (h : ∀ (t : U ≃ₗ[ZMod p] U) (htA : t ∈ A), IsRefl p t →
      ∀ n ∈ N₀, Commute (mk (⟨t, htA⟩ : A)) n) :
    N₀ ≤ Subgroup.center (A ⧸ Subgroup.center A) := by
  let C : Subgroup A :=
    { carrier := {a | ∀ n ∈ N₀, Commute (mk a) n}
      one_mem' := by
        intro n _
        simp
      mul_mem' := by
        intro a b ha hb n hn
        rw [QuotientGroup.mk_mul]
        exact (ha n hn).mul_left (hb n hn)
      inv_mem' := by
        intro a ha n hn
        rw [QuotientGroup.mk_inv]
        exact (ha n hn).inv_left }
  have hC : C = ⊤ := by
    apply (Subgroup.map_subtype_inj (H := A)).mp
    rw [Subgroup.map_top, Subgroup.range_subtype]
    apply le_antisymm
    · exact Subgroup.map_subtype_le C
    · have hcl : Subgroup.closure {t | t ∈ A ∧ IsRefl p t} ≤ C.map A.subtype := by
        refine (Subgroup.closure_le (C.map A.subtype)).mpr ?_
        intro t ht
        exact Subgroup.mem_map.mpr ⟨⟨t, ht.1⟩, h t ht.1 ht.2, rfl⟩
      rwa [← hgen] at hcl
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  have ha : a ∈ C := by rw [hC]; trivial
  exact (ha n hn).eq

private theorem znn_exists_refl_not_commute (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (hn3 : 3 ≤ Module.finrank (ZMod p) U)
    {N₀ : Subgroup (A ⧸ Subgroup.center A)} (hN₀ne : N₀ ≠ ⊥)
    {M : Subgroup A} (hM : M = N₀.comap (QuotientGroup.mk' (Subgroup.center A))) :
    ∃ (t : U ≃ₗ[ZMod p] U) (htA : t ∈ A), IsRefl p t ∧
      ∃ m ∈ M, ¬ Commute (mk (⟨t, htA⟩ : A)) (mk m) := by
  by_contra h
  have hcentral : ∀ (t : U ≃ₗ[ZMod p] U) (htA : t ∈ A), IsRefl p t →
      ∀ n ∈ N₀, Commute (mk (⟨t, htA⟩ : A)) n := by
    intro t htA ht n hn
    by_contra hnc
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective n
    have haM : a ∈ M := by
      rw [hM, Subgroup.mem_comap]
      simpa only [QuotientGroup.coe_mk'] using hn
    exact h ⟨t, htA, ht, a, haM, hnc⟩
  have hle : N₀ ≤ Subgroup.center (A ⧸ Subgroup.center A) :=
    znn_le_center_of_refl_centralizes hgen hcentral
  rw [center_quotient_center_eq_bot hgen hirr hn3] at hle
  exact hN₀ne (le_bot_iff.mp hle)

private theorem znn_eq_of_dvd_pow {o r k : ℕ} (ho : o = 2 ∨ o = 3)
    (hr : r = 2 ∨ r = 3) (h : o ∣ r ^ k) : r = o := by
  rcases ho with rfl | rfl <;> rcases hr with rfl | rfl
  · rfl
  · exfalso
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h) (by norm_num)
  · exfalso
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
  · rfl

private theorem znn_exists_g (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y →
      orderOf (x * y) ≤ 3)
    {M : Subgroup A} (hMnormal : M.Normal) {tA m : A} (ht : IsRefl p (tA : U ≃ₗ[ZMod p] U))
    (hmM : m ∈ M) (hnc : ¬ Commute (mk tA) (mk m)) :
    ∃ (t' g : A), IsRefl p (t' : U ≃ₗ[ZMod p] U) ∧ g = t' * tA ∧ g ∈ M ∧
      mk g ≠ 1 ∧ (orderOf g = 2 ∨ orderOf g = 3) := by
  let t' : A := m * tA * m⁻¹
  let g : A := t' * tA
  have ht' : IsRefl p (t' : U ≃ₗ[ZMod p] U) := by
    have h := ht.conj (m : U ≃ₗ[ZMod p] U)
    simpa [t', Subgroup.coe_mul, Subgroup.coe_inv] using h
  have htA_inv : tA⁻¹ = tA := by
    apply Subtype.ext
    exact inv_eq_of_mul_eq_one_left (by simpa using ht.1)
  have hgM : g ∈ M := by
    have hconj : tA * m⁻¹ * tA⁻¹ ∈ M :=
      hMnormal.conj_mem m⁻¹ (Subgroup.inv_mem M hmM) tA
    have heq : g = m * (tA * m⁻¹ * tA⁻¹) := by
      dsimp [g, t']
      rw [htA_inv]
      group
    rw [heq]
    exact Subgroup.mul_mem M hmM hconj
  have hgt : mk g = mk m * mk tA * (mk m)⁻¹ * mk tA := by
    dsimp [g, t']
  have hb2 : mk tA * mk tA = 1 := by
    rw [← QuotientGroup.mk_mul]
    have h : tA * tA = 1 := by
      apply Subtype.ext
      simpa using ht.1
    rw [h, QuotientGroup.mk_one]
  have hmk_ne : mk g ≠ 1 := by
    intro h1
    apply hnc
    rw [commute_iff_eq]
    have h1' : mk m * mk tA * (mk m)⁻¹ * mk tA = 1 := by
      rw [← hgt]
      exact h1
    have hb_inv : (mk tA)⁻¹ = mk tA := inv_eq_of_mul_eq_one_left hb2
    have h2 : mk m * mk tA * (mk m)⁻¹ = mk tA := by
      calc mk m * mk tA * (mk m)⁻¹ = (mk tA)⁻¹ := mul_eq_one_iff_eq_inv.mp h1'
        _ = mk tA := hb_inv
    have h3 : mk m * mk tA = mk tA * mk m := by
      have h := congrArg (fun x => x * mk m) h2
      simpa [mul_assoc] using h
    exact h3.symm
  have hgle : orderOf g ≤ 3 := by
    have h := h3 (t' : U ≃ₗ[ZMod p] U) t'.2 (tA : U ≃ₗ[ZMod p] U) tA.2 ht' ht
    rwa [← Subgroup.coe_mul, Subgroup.orderOf_coe] at h
  have hgne : g ≠ 1 := by
    intro hg1
    exact hmk_ne (by rw [hg1, QuotientGroup.mk_one])
  have hne1 : orderOf g ≠ 1 := by
    intro h1
    exact hgne (orderOf_eq_one_iff.mp h1)
  have hpos : 0 < orderOf g := orderOf_pos _
  refine ⟨t', g, ht', rfl, hgM, hmk_ne, ?_⟩
  omega

omit [Module.Finite (ZMod p) U] in
private theorem znn_commutator_data (hirr : AbsIrred p A)
    {N₀ : Subgroup (A ⧸ Subgroup.center A)}
    (hN₀comm : ∀ x ∈ N₀, ∀ y ∈ N₀, x * y = y * x)
    {M : Subgroup A} (hMmap : ∀ m ∈ M, mk m ∈ N₀)
    {g h : A} (hnc : ¬ Commute h g) (hhM : h ∈ M) (hgM : g ∈ M) :
    ∃ (z : A) (ζ : ZMod p), z ∈ Subgroup.center A ∧ z ≠ 1 ∧
      z = h * g * h⁻¹ * g⁻¹ ∧
      ((z : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = ζ • LinearMap.id ∧ ζ ≠ 1 ∧
      h * g * h⁻¹ = z * g := by
  let z : A := h * g * h⁻¹ * g⁻¹
  have hz_center : z ∈ Subgroup.center A := by
    apply (QuotientGroup.eq_one_iff (N := Subgroup.center A) z).mp
    have hzval : mk z = mk h * mk g * (mk h)⁻¹ * (mk g)⁻¹ := by
      dsimp [z]
    rw [hzval]
    have hcomm : mk h * mk g = mk g * mk h :=
      hN₀comm (mk h) (hMmap h hhM) (mk g) (hMmap g hgM)
    calc mk h * mk g * (mk h)⁻¹ * (mk g)⁻¹
        = (mk h * mk g) * (mk g * mk h)⁻¹ := by group
      _ = (mk h * mk g) * (mk h * mk g)⁻¹ := by rw [← hcomm]
      _ = 1 := mul_inv_cancel _
  have hz_ne : z ≠ 1 := by
    intro hz1
    apply hnc
    rw [commute_iff_eq]
    have hzg : h * g * h⁻¹ = g := by
      have h := congrArg (fun t => t * g) hz1
      dsimp [z] at h
      simpa [mul_assoc] using h
    have h := congrArg (fun t => t * h) hzg
    simpa [mul_assoc] using h
  obtain ⟨ζ, hζ⟩ := hirr.exists_eq_smul_of_mem_center hz_center
  have hζ1 : ζ ≠ 1 := by
    intro hζ1
    apply hz_ne
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have h := congrArg (fun f : U →ₗ[ZMod p] U => f v) hζ
    simpa [hζ1] using h
  have hzconj : h * g * h⁻¹ = z * g := by
    dsimp [z]
    group
  exact ⟨z, ζ, hz_center, hz_ne, rfl, hζ, hζ1, hzconj⟩

omit [Module.Finite (ZMod p) U] in
private theorem znn_zeta_data (hn : 4 ≤ Module.finrank (ZMod p) U) (hirr : AbsIrred p A)
    {N₀ : Subgroup (A ⧸ Subgroup.center A)}
    (hN₀comm : ∀ x ∈ N₀, ∀ y ∈ N₀, x * y = y * x)
    {M : Subgroup A} (hMmap : ∀ m ∈ M, mk m ∈ N₀)
    {g h : A} (hnc : ¬ Commute h g) (hhM : h ∈ M) (hgM : g ∈ M) :
    ∃ ζ : ZMod p, ζ ≠ 1 ∧ ζ ^ orderOf g = 1 ∧
      ∀ v, (h : U ≃ₗ[ZMod p] U) ((g : U ≃ₗ[ZMod p] U) v) =
        ζ • (g : U ≃ₗ[ZMod p] U) ((h : U ≃ₗ[ZMod p] U) v) := by
  obtain ⟨z, ζ, hz_center, -, hzdef, hζ, hζ1, hzconj⟩ :=
    znn_commutator_data hirr hN₀comm hMmap hnc hhM hgM
  have hζpow : ζ ^ orderOf g = 1 := by
    have hzpow : z ^ orderOf g = 1 := by
      have hcomm_a : Commute (h * g * h⁻¹) g := by
        rw [hzconj]
        exact ((commute_iff_eq z g).mpr
          (Subgroup.mem_center_iff.mp hz_center g).symm).mul_left (Commute.refl g)
      calc z ^ orderOf g
          = (h * g * h⁻¹) ^ orderOf g * (g⁻¹) ^ orderOf g := by
            rw [hzdef, hcomm_a.inv_right.mul_pow]
        _ = (h * g ^ orderOf g * h⁻¹) * (g ^ orderOf g)⁻¹ := by
            rw [conj_pow, inv_pow]
        _ = 1 := by
            rw [pow_orderOf_eq_one g]
            simp
    have hU : Nontrivial U :=
      Module.nontrivial_of_finrank_pos (R := ZMod p) (M := U) (by omega)
    obtain ⟨v, hv0⟩ := @exists_ne U hU 0
    have hzpow_coe : (((z ^ orderOf g : A) : U ≃ₗ[ZMod p] U)) v = v := by
      rw [hzpow]
      rfl
    have hzpow_smul : (((z ^ orderOf g : A) : U ≃ₗ[ZMod p] U)) v =
        (ζ ^ orderOf g) • v := by
      rw [Subgroup.coe_pow]
      exact znn_pow_apply_of_smul_id hζ (orderOf g) v
    have hveq : (ζ ^ orderOf g) • v = v := by
      rw [← hzpow_smul, hzpow_coe]
    have hzero : (ζ ^ orderOf g - 1) • v = 0 := by
      rw [sub_smul, one_smul, hveq, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero_iff_left hv0).mp hzero)
  have hconj : ∀ v, (h : U ≃ₗ[ZMod p] U) ((g : U ≃ₗ[ZMod p] U) v) =
      ζ • (g : U ≃ₗ[ZMod p] U) ((h : U ≃ₗ[ZMod p] U) v) := by
    intro v
    have hzlin : ((z : U ≃ₗ[ZMod p] U)) ((g : U ≃ₗ[ZMod p] U)
        ((h : U ≃ₗ[ZMod p] U) v)) =
        ζ • (g : U ≃ₗ[ZMod p] U) ((h : U ≃ₗ[ZMod p] U) v) := by
      simpa using congrArg (fun f : U →ₗ[ZMod p] U =>
        f ((g : U ≃ₗ[ZMod p] U) ((h : U ≃ₗ[ZMod p] U) v))) hζ
    calc (h : U ≃ₗ[ZMod p] U) ((g : U ≃ₗ[ZMod p] U) v)
        = ((h * g * h⁻¹ : A) : U ≃ₗ[ZMod p] U) ((h : U ≃ₗ[ZMod p] U) v) := by
          simp [Subgroup.coe_mul, LinearEquiv.mul_apply]
      _ = ((z * g : A) : U ≃ₗ[ZMod p] U) ((h : U ≃ₗ[ZMod p] U) v) := by
          rw [hzconj]
      _ = ζ • (g : U ≃ₗ[ZMod p] U) ((h : U ≃ₗ[ZMod p] U) v) := by
          rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
          exact hzlin
  exact ⟨ζ, hζ1, hζpow, hconj⟩

private theorem znn_imprimitive_of_frame (hp : p ≠ 2) (hgen : ReflGen p A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {h tA t' : A} (ht : IsRefl p (tA : U ≃ₗ[ZMod p] U)) (ht' : IsRefl p (t' : U ≃ₗ[ZMod p] U))
    (hdim : Module.finrank (ZMod p) U = 4)
    (hpair : Pairwise (fun i j => Commute
      (![(tA : U ≃ₗ[ZMod p] U), (t' : U ≃ₗ[ZMod p] U),
        (h : U ≃ₗ[ZMod p] U) * tA * (h : U ≃ₗ[ZMod p] U)⁻¹,
        (h : U ≃ₗ[ZMod p] U) * t' * (h : U ≃ₗ[ZMod p] U)⁻¹] i)
      (![(tA : U ≃ₗ[ZMod p] U), (t' : U ≃ₗ[ZMod p] U),
        (h : U ≃ₗ[ZMod p] U) * tA * (h : U ≃ₗ[ZMod p] U)⁻¹,
        (h : U ≃ₗ[ZMod p] U) * t' * (h : U ≃ₗ[ZMod p] U)⁻¹] j)))
    (hinj : Function.Injective ![(tA : U ≃ₗ[ZMod p] U), (t' : U ≃ₗ[ZMod p] U),
      (h : U ≃ₗ[ZMod p] U) * tA * (h : U ≃ₗ[ZMod p] U)⁻¹,
      (h : U ≃ₗ[ZMod p] U) * t' * (h : U ≃ₗ[ZMod p] U)⁻¹]) :
    CFSG.Quasithin.SimsG4.IsImprimitiveOnV A := by
  have hrA : ∀ i, ![ (tA : U ≃ₗ[ZMod p] U), (t' : U ≃ₗ[ZMod p] U),
      (h : U ≃ₗ[ZMod p] U) * (tA : U ≃ₗ[ZMod p] U) * (h : U ≃ₗ[ZMod p] U)⁻¹,
      (h : U ≃ₗ[ZMod p] U) * (t' : U ≃ₗ[ZMod p] U) *
        (h : U ≃ₗ[ZMod p] U)⁻¹] i ∈ A := by
    intro i; fin_cases i
    · exact tA.2
    · exact t'.2
    · simpa using Subgroup.mul_mem A (Subgroup.mul_mem A h.2 tA.2) (Subgroup.inv_mem A h.2)
    · simpa using Subgroup.mul_mem A (Subgroup.mul_mem A h.2 t'.2) (Subgroup.inv_mem A h.2)
  have hr : ∀ i, IsRefl p (![ (tA : U ≃ₗ[ZMod p] U), (t' : U ≃ₗ[ZMod p] U),
      (h : U ≃ₗ[ZMod p] U) * (tA : U ≃ₗ[ZMod p] U) * (h : U ≃ₗ[ZMod p] U)⁻¹,
      (h : U ≃ₗ[ZMod p] U) * (t' : U ≃ₗ[ZMod p] U) *
        (h : U ≃ₗ[ZMod p] U)⁻¹] i) := by
    intro i; fin_cases i
    · exact ht
    · exact ht'
    · simpa [Subgroup.coe_mul, Subgroup.coe_inv] using ht.conj (h : U ≃ₗ[ZMod p] U)
    · simpa [Subgroup.coe_mul, Subgroup.coe_inv] using ht'.conj (h : U ≃ₗ[ZMod p] U)
  exact isImprimitiveOnV_of_frame hp hdim hgen h3 hrA hr hpair hinj

private theorem znn_case_order_two (hp : p ≠ 2) (hn : 4 ≤ Module.finrank (ZMod p) U)
    (hgen : ReflGen p A) (hprim : ¬ CFSG.Quasithin.SimsG4.IsImprimitiveOnV A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {g h tA t' : A} {ζ : ZMod p} (hζ1 : ζ ≠ 1) (hζpow : ζ ^ orderOf g = 1)
    (hconj : ∀ v, (h : U ≃ₗ[ZMod p] U) ((g : U ≃ₗ[ZMod p] U) v) =
      ζ • (g : U ≃ₗ[ZMod p] U) ((h : U ≃ₗ[ZMod p] U) v))
    (ht : IsRefl p (tA : U ≃ₗ[ZMod p] U)) (ht' : IsRefl p (t' : U ≃ₗ[ZMod p] U))
    (hg_eq : g = t' * tA) (h2 : orderOf g = 2) : False := by
  have hsq : (t' * tA) * (t' * tA) = 1 := by
    have h := pow_orderOf_eq_one g
    rw [h2, pow_two] at h
    rwa [hg_eq] at h
  have htA_sq : tA * tA = 1 := by
    apply Subtype.ext
    simpa using ht.1
  have hcomm_lin : Commute (t' : U ≃ₗ[ZMod p] U) (tA : U ≃ₗ[ZMod p] U) := by
    refine CFSG.commute_of_sq_eq_one (by rw [sq]; exact ht'.1) (by rw [sq]; exact ht.1) ?_
    rw [sq]
    simpa [Subgroup.coe_mul] using congrArg (fun x : A => (x : U ≃ₗ[ZMod p] U)) hsq
  have hne : tA ≠ t' := by
    intro heq
    have hg1 : g = 1 := by
      calc g = t' * tA := hg_eq
        _ = tA * tA := by rw [← heq]
        _ = 1 := htA_sq
    have h1 : orderOf g = 1 := orderOf_eq_one_iff.mpr hg1
    omega
  have hζsq : ζ ^ 2 = 1 := by rw [← h2]; exact hζpow
  have hζneg : ζ = -1 := by
    rcases (sq_eq_one_iff.mp hζsq) with h | h
    · exact absurd h hζ1
    · exact h
  have hconj' : ∀ v, (h : U ≃ₗ[ZMod p] U) ((t' : U ≃ₗ[ZMod p] U)
      ((tA : U ≃ₗ[ZMod p] U) v)) =
      -((t' : U ≃ₗ[ZMod p] U) ((tA : U ≃ₗ[ZMod p] U)
        ((h : U ≃ₗ[ZMod p] U) v))) := by
    intro v
    have hh := hconj v
    rw [hg_eq, hζneg] at hh
    have hneg : (-1 : ZMod p) • ((t' * tA : A) : U ≃ₗ[ZMod p] U)
        ((h : U ≃ₗ[ZMod p] U) v) = -((t' * tA : A) : U ≃ₗ[ZMod p] U)
        ((h : U ≃ₗ[ZMod p] U) v) := neg_one_smul (ZMod p) _
    rw [hneg, Subgroup.coe_mul, LinearEquiv.mul_apply] at hh
    simpa using hh
  have hne_lin : (tA : U ≃ₗ[ZMod p] U) ≠ (t' : U ≃ₗ[ZMod p] U) :=
    fun h => hne (Subtype.ext h)
  obtain ⟨hdim, hpair, hinj⟩ :=
    frame_of_apply_mul_eq_neg hp ht ht' hcomm_lin.symm hne_lin hn hconj'
  exact hprim (znn_imprimitive_of_frame hp hgen h3 ht ht' hdim hpair hinj)

private theorem znn_case_order_three (hp : p ≠ 2) (hn : 4 ≤ Module.finrank (ZMod p) U)
    {g h tA t' : A} {ζ : ZMod p} (hζ1 : ζ ≠ 1) (hζpow : ζ ^ orderOf g = 1)
    (hconj : ∀ v, (h : U ≃ₗ[ZMod p] U) ((g : U ≃ₗ[ZMod p] U) v) =
      ζ • (g : U ≃ₗ[ZMod p] U) ((h : U ≃ₗ[ZMod p] U) v))
    (ht : IsRefl p (tA : U ≃ₗ[ZMod p] U)) (ht' : IsRefl p (t' : U ≃ₗ[ZMod p] U))
    (hg_eq : g = t' * tA) (h3ord : orderOf g = 3) : False := by
  have hζ2 : ζ ^ 2 ≠ 1 := by
    intro h2'
    apply hζ1
    have h3ζ : ζ ^ 3 = 1 := by rw [← h3ord]; exact hζpow
    rw [pow_succ'] at h3ζ
    rw [h2', mul_one] at h3ζ
    exact h3ζ
  have hconj' : ∀ v, (h : U ≃ₗ[ZMod p] U) ((t' : U ≃ₗ[ZMod p] U)
      ((tA : U ≃ₗ[ZMod p] U) v)) =
      ζ • (t' : U ≃ₗ[ZMod p] U) ((tA : U ≃ₗ[ZMod p] U)
        ((h : U ≃ₗ[ZMod p] U) v)) := by
    intro v
    have hh := hconj v
    rw [hg_eq] at hh
    simpa [LinearEquiv.mul_apply] using hh
  have hle := finrank_le_three_of_apply_mul_eq_smul hp ht ht' hζ1 hζ2 hconj'
  omega

private theorem znn_case_not_commute (hp : p ≠ 2)
    (hn : 4 ≤ Module.finrank (ZMod p) U) (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (hprim : ¬ CFSG.Quasithin.SimsG4.IsImprimitiveOnV A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {N₀ : Subgroup (A ⧸ Subgroup.center A)}
    (hN₀comm : ∀ x ∈ N₀, ∀ y ∈ N₀, x * y = y * x)
    {M : Subgroup A} (hMmap : ∀ m ∈ M, mk m ∈ N₀)
    {g h : A} (hnc : ¬ Commute h g) (hhM : h ∈ M) (hgM : g ∈ M)
    {tA t' : A} (ht : IsRefl p (tA : U ≃ₗ[ZMod p] U))
    (ht' : IsRefl p (t' : U ≃ₗ[ZMod p] U)) (hg_eq : g = t' * tA)
    (hord : orderOf g = 2 ∨ orderOf g = 3) : False := by
  obtain ⟨ζ, hζ1, hζpow, hconj⟩ :=
    znn_zeta_data hn hirr hN₀comm hMmap hnc hhM hgM
  rcases hord with h2 | h3ord
  · exact znn_case_order_two hp hn hgen hprim h3 hζ1 hζpow hconj ht ht' hg_eq h2
  · exact znn_case_order_three hp hn hζ1 hζpow hconj ht ht' hg_eq h3ord

omit [Module.Finite (ZMod p) U] in
private theorem znn_exists_normal_closure {r : ℕ} {M : Subgroup A} (hMnormal : M.Normal)
    {g : A} (hgM : g ∈ M) (hcomm : ∀ z ∈ M, Commute g z) (hgr : r = orderOf g) :
    ∃ K : Subgroup A, K.Normal ∧ g ∈ K ∧
      (∀ x ∈ K, ∀ y ∈ K, x * y = y * x) ∧ ∀ x ∈ K, x ^ r = 1 := by
  let S : Set A := {a * g * a⁻¹ | a : A}
  let K : Subgroup A := Subgroup.closure S
  have hSK : S ⊆ K := fun _ hx => Subgroup.subset_closure hx
  have hgK : g ∈ K := by
    have h : g = 1 * g * 1⁻¹ := by group
    rw [h]
    exact hSK ⟨1, rfl⟩
  have hScomm : ∀ x ∈ S, ∀ y ∈ S, Commute x y := by
    rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩
    have hyM : b * g * b⁻¹ ∈ M := hMnormal.conj_mem g hgM b
    have hxcent : ∀ z ∈ M, Commute (a * g * a⁻¹) z := by
      intro z hz
      have hzM : a⁻¹ * z * a ∈ M := by
        simpa using hMnormal.conj_mem z hz a⁻¹
      have hconj := (hcomm (a⁻¹ * z * a) hzM).conj a
      have heq : a * (a⁻¹ * z * a) * a⁻¹ = z := by group
      rwa [heq] at hconj
    exact hxcent (b * g * b⁻¹) hyM
  have hKcomm : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := by
    have hcommK : IsMulCommutative K :=
      Subgroup.isMulCommutative_closure (fun x hx y hy _ => hScomm x hx y hy)
    intro x hx y hy
    exact congrArg (fun z : K => (z : A)) (@mul_comm' K _ hcommK ⟨x, hx⟩ ⟨y, hy⟩)
  have hKnormal : K.Normal := by
    have hconjS : ∀ a : A, ∀ x ∈ S, a * x * a⁻¹ ∈ S := by
      rintro a _ ⟨b, rfl⟩
      exact ⟨a * b, by group⟩
    refine ⟨fun k hk a => ?_⟩
    have hmap : K.map (MulAut.conj a).toMonoidHom ≤ K := by
      dsimp only [K]
      rw [MonoidHom.map_closure]
      refine (Subgroup.closure_le K).mpr ?_
      rintro y ⟨x, hx, rfl⟩
      exact Subgroup.subset_closure (hconjS a x hx)
    simpa [MulAut.conj_apply] using
      hmap (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩)
  have hKpow : ∀ x ∈ K, x ^ r = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨a, rfl⟩ := hy
        have hord : orderOf (a * g * a⁻¹) = orderOf g := by
          simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj a) g)
        rw [hgr, ← hord]
        exact pow_orderOf_eq_one _
    | one => exact one_pow r
    | mul x y hx hy ihx ihy =>
        rw [Commute.mul_pow (hKcomm x hx y hy) r, ihx, ihy, one_mul]
    | inv x hx ih =>
        rw [inv_pow, ih, inv_one]
  exact ⟨K, hKnormal, hgK, hKcomm, hKpow⟩

private theorem znn_case_pCore {r : ℕ} (hirr : AbsIrred p A)
    {M : Subgroup A} (hMnormal : M.Normal) {g : A} (hgM : g ∈ M) (hgne : g ≠ 1)
    (hcomm : ∀ z ∈ M, Commute g z) (hgr : r = orderOf g) (hrp : r = p) : False := by
  obtain ⟨K, hKnormal, hgK, -, hKpow⟩ :=
    znn_exists_normal_closure hMnormal hgM hcomm hgr
  have hKp : IsPGroup p K := by
    apply IsPGroup.of_exponent_dvd_pow (n := 1)
    rw [pow_one]
    refine Monoid.exponent_dvd.mpr ?_
    intro x
    have h := orderOf_dvd_of_pow_eq_one (hKpow (x : A) x.2)
    rw [hrp] at h
    simpa only [Subgroup.orderOf_coe] using h
  have hKle : K ≤ CFSG.pCore p A := le_sSup ⟨hKnormal, hKp⟩
  have hV : Finite U := Module.finite_of_finite (ZMod p)
  have hcore : CFSG.pCore p A = ⊥ :=
    @CFSG.GroupTheory.CoprimeActionSupport.FaithfulIrreduciblePCoreTrivial.pCore_eq_bot
      p _ A U _ _ _ hV _ A.subtype (fun x y h => Subtype.ext h)
      (fun W hW => hirr.1 W (fun a ha w hw => hW ⟨a, ha⟩ w hw))
  rw [hcore] at hKle
  have hKbot : K = ⊥ := le_bot_iff.mp hKle
  have hg1 : g = 1 := by
    have hg : g ∈ (⊥ : Subgroup A) := by rw [← hKbot]; exact hgK
    simpa using hg
  exact hgne hg1

private theorem znn_case_not_pCore {r : ℕ}
    (hn : 3 ≤ Module.finrank (ZMod p) U) (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (hprim : ¬ CFSG.Quasithin.SimsG4.IsImprimitiveOnV A)
    {M : Subgroup A} (hMnormal : M.Normal) {g : A} (hgM : g ∈ M) (hgmk : mk g ≠ 1)
    (hcomm : ∀ z ∈ M, Commute g z) (hgr : r = orderOf g)
    (hr : r = 2 ∨ r = 3) (hrne : r ≠ p) : False := by
  obtain ⟨K, hKnormal, hgK, hKcomm, hKpow⟩ :=
    znn_exists_normal_closure hMnormal hgM hcomm hgr
  let B : Subgroup (U ≃ₗ[ZMod p] U) := K.map A.subtype
  have hBA : B ≤ A := Subgroup.map_subtype_le K
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    obtain ⟨kx, hkx, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨ky, hky, rfl⟩ := Subgroup.mem_map.mp hy
    simpa using congrArg (fun z : A => (z : U ≃ₗ[ZMod p] U)) (hKcomm kx hkx ky hky)
  have hBn : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B := by
    intro a ha b hb
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hb
    let a' : A := ⟨a, ha⟩
    have hmem : a' * k * a'⁻¹ ∈ K := hKnormal.conj_mem k hk a'
    have hmemB : A.subtype (a' * k * a'⁻¹) ∈ B :=
      Subgroup.mem_map.mpr ⟨a' * k * a'⁻¹, hmem, rfl⟩
    have heq : A.subtype (a' * k * a'⁻¹) = a * A.subtype k * a⁻¹ := by
      simp [a', Subgroup.coe_mul]
    rw [heq] at hmemB
    exact hmemB
  have hBp : ∀ b ∈ B, ¬ p ∣ orderOf b := by
    intro b hb
    obtain ⟨k, hkK, rfl⟩ := Subgroup.mem_map.mp hb
    have hdvd : orderOf (A.subtype k) ∣ r :=
      (orderOf_map_dvd A.subtype k).trans (orderOf_dvd_of_pow_eq_one (hKpow k hkK))
    have hrprime : r.Prime := by rcases hr with rfl | rfl <;> norm_num
    intro hpdiv
    have hpr : p ∣ r := hpdiv.trans hdvd
    rcases (Nat.dvd_prime hrprime).mp hpr with h1 | h1
    · exact (Fact.out : Nat.Prime p).ne_one h1
    · exact hrne h1.symm
  have hcommA : ∀ a ∈ A, a * (g : U ≃ₗ[ZMod p] U) = (g : U ≃ₗ[ZMod p] U) * a := by
    intro a ha
    exact commute_of_mem_of_isMulCommutative hn hgen hprim hBA hBn hBc hBp ha
      (Subgroup.mem_map.mpr ⟨g, hgK, rfl⟩)
  have hcentral : mk g ∈ Subgroup.center (A ⧸ Subgroup.center A) := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    have hA : a * g = g * a := by
      apply Subtype.ext
      simpa [Subgroup.coe_mul] using hcommA a a.2
    calc mk a * mk g = mk (a * g) := (QuotientGroup.mk_mul (Subgroup.center A) a g).symm
      _ = mk (g * a) := by rw [hA]
      _ = mk g * mk a := QuotientGroup.mk_mul (Subgroup.center A) g a
  rw [center_quotient_center_eq_bot hgen hirr hn] at hcentral
  exact hgmk (Subgroup.mem_bot.mp hcentral)


omit [Module.Finite (ZMod p) U] in
private theorem znn_r_eq_orderOf {r : ℕ} (hr : r = 2 ∨ r = 3)
    {N : Subgroup (A ⧸ Subgroup.center A)} (hNr : IsPGroup r N)
    {M : Subgroup A} (hMmap : ∀ m ∈ M, mk m ∈ N) {g : A} (hgM : g ∈ M)
    (hgmk : mk g ≠ 1) (hord : orderOf g = 2 ∨ orderOf g = 3) :
    r = orderOf g := by
  have hmk_dvd : orderOf (mk g) ∣ orderOf g := by
    simpa only [QuotientGroup.coe_mk'] using
      orderOf_map_dvd (QuotientGroup.mk' (Subgroup.center A)) g
  have hmk_ne : orderOf (mk g) ≠ 1 := by
    intro h1
    exact hgmk (orderOf_eq_one_iff.mp h1)
  have hmk_eq : orderOf (mk g) = orderOf g := by
    rcases hord with h | h
    · rw [h] at hmk_dvd ⊢
      rcases (Nat.dvd_prime Nat.prime_two).mp hmk_dvd with h1 | h1
      · exact absurd h1 hmk_ne
      · exact h1
    · rw [h] at hmk_dvd ⊢
      rcases (Nat.dvd_prime Nat.prime_three).mp hmk_dvd with h1 | h1
      · exact absurd h1 hmk_ne
      · exact h1
  obtain ⟨k, hk⟩ := IsPGroup.exists_orderOf_dvd_pow hNr ⟨mk g, hMmap g hgM⟩
  have hk' : orderOf (mk g) ∣ r ^ k := by
    simpa only [← Subgroup.orderOf_coe] using hk
  exact znn_eq_of_dvd_pow hord hr (by rw [← hmk_eq]; exact hk')


private theorem znn_setup {r : ℕ} {N : Subgroup (A ⧸ Subgroup.center A)}
    (hN : N.Normal) (hNr : IsPGroup r N) (hr : r = 2 ∨ r = 3) (hNne : N ≠ ⊥) :
    ∃ (N₀ : Subgroup (A ⧸ Subgroup.center A)) (M : Subgroup A),
      N₀.Normal ∧ N₀ ≤ N ∧ N₀ ≠ ⊥ ∧
      (∀ x ∈ N₀, ∀ y ∈ N₀, x * y = y * x) ∧
      M.Normal ∧ M = N₀.comap (QuotientGroup.mk' (Subgroup.center A)) ∧
      (∀ m ∈ M, mk m ∈ N₀) ∧ (∀ m ∈ M, mk m ∈ N) := by
  let mk' : A →* (A ⧸ Subgroup.center A) := QuotientGroup.mk' (Subgroup.center A)
  let N₀ : Subgroup (A ⧸ Subgroup.center A) := (Subgroup.center N).map N.subtype
  have hN₀normal : N₀.Normal :=
    @ConjAct.normal_of_characteristic_of_normal (A ⧸ Subgroup.center A) _
      N hN (Subgroup.center N) Subgroup.centerCharacteristic
  have hN₀le : N₀ ≤ N := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    exact z.2
  have hNnt : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNne
  have hrprime : r.Prime := by rcases hr with rfl | rfl <;> norm_num
  have hcenterN : Nontrivial (Subgroup.center N) :=
    @IsPGroup.center_nontrivial r N _ hNr ⟨hrprime⟩ hNnt _
  have hcne : Subgroup.center N ≠ ⊥ :=
    fun hc => (Subgroup.nontrivial_iff_ne_bot _).mp hcenterN hc
  have hN₀ne : N₀ ≠ ⊥ := by
    intro hbot
    exact hcne ((Subgroup.map_eq_bot_iff_of_injective
      (Subgroup.center N) N.subtype_injective).mp hbot)
  have hN₀comm : ∀ x ∈ N₀, ∀ y ∈ N₀, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    have hcomm : (x' : N) * (y' : N) = (y' : N) * (x' : N) :=
      (Subgroup.mem_center_iff.mp hx' y').symm
    simpa [Subgroup.coe_mul] using
      congrArg (fun z : N => (z : A ⧸ Subgroup.center A)) hcomm
  let M : Subgroup A := N₀.comap mk'
  have hMnormal : M.Normal := by
    refine ⟨fun m hm a => ?_⟩
    rw [Subgroup.mem_comap] at hm ⊢
    have hmap : mk' (a * m * a⁻¹) = mk' a * mk' m * (mk' a)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [hmap]
    exact hN₀normal.conj_mem (mk' m) hm (mk' a)
  have hMmap : ∀ m ∈ M, mk m ∈ N₀ := by
    intro m hm
    simpa [M, mk', QuotientGroup.coe_mk'] using hm
  exact ⟨N₀, M, hN₀normal, hN₀le, hN₀ne, hN₀comm, hMnormal, rfl, hMmap,
    fun m hm => hN₀le (hMmap m hm)⟩

theorem eq_bot_of_isPGroup_of_normal (hp : p ≠ 2)
    (hn : 4 ≤ Module.finrank (ZMod p) U) (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (hprim : ¬ CFSG.Quasithin.SimsG4.IsImprimitiveOnV A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {r : ℕ} (hr : r = 2 ∨ r = 3) {N : Subgroup (↥A ⧸ Subgroup.center ↥A)} (hN : N.Normal)
    (hNr : IsPGroup r N) : N = ⊥ := by
  classical
  by_contra hNne
  obtain ⟨N₀, M, hN₀normal, hN₀le, hN₀ne, hN₀comm, hMnormal, hMdef, hMmap, hMmapN⟩ :=
    znn_setup hN hNr hr hNne
  have hn3 : 3 ≤ Module.finrank (ZMod p) U := by omega
  obtain ⟨t, htA, ht, m, hmM, hnc⟩ :=
    znn_exists_refl_not_commute hgen hirr hn3 hN₀ne (M := M) hMdef
  let tA : ↥A := ⟨t, htA⟩
  have hnc' : ¬ Commute (mk tA) (mk m) := hnc
  obtain ⟨t', g, ht', hg_eq, hgM, hgmk, hord⟩ :=
    znn_exists_g h3 hMnormal ht hmM hnc'
  have hgne : g ≠ 1 := by
    intro hg1
    exact hgmk (by rw [hg1, QuotientGroup.mk_one])
  have hro : r = orderOf g :=
    znn_r_eq_orderOf hr hNr hMmapN hgM hgmk hord
  by_cases hcase : ∃ h ∈ M, ¬ Commute h g
  · obtain ⟨h, hhM, hnc_hg⟩ := hcase
    exact znn_case_not_commute hp hn hgen hirr hprim h3 hN₀comm hMmap hnc_hg hhM hgM
      ht ht' hg_eq hord
  · have hcommM : ∀ z ∈ M, Commute g z := by
      intro z hz
      by_contra hnc_gz
      exact hcase ⟨z, hz, fun hzg => hnc_gz hzg.symm⟩
    by_cases hrp : r = p
    · exact znn_case_pCore hirr hMnormal hgM hgne hcommM hro hrp
    · exact znn_case_not_pCore hn3 hgen hirr hprim hMnormal hgM hgmk hcommM hro hr hrp

end CFSG.StandardType.ZS
