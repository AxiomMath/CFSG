module

public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.StandardType.GGL48TW.Frob

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mul_pow_mul_inv_pow_mem {C : Subgroup G} {a c : G} (ha : a ∈ normalizer (C : Set G))
    (hc : c ∈ C) (n : ℕ) : (a * c) ^ n * (a ^ n)⁻¹ ∈ C := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (a * c) ^ (n + 1) * (a ^ (n + 1))⁻¹ =
        ((a * c) ^ n * (a ^ n)⁻¹) * (a ^ (n + 1) * c * (a ^ (n + 1))⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact C.mul_mem ih ((mem_normalizer_iff.mp (pow_mem ha (n + 1)) c).mp hc)

theorem mul_pow_mul_inv_mem {K V : Subgroup G} (hKV : K ≤ normalizer (V : Set G))
    (hcomm : ⁅K, K⁆ ≤ V) {a b : G} (ha : a ∈ K) (hb : b ∈ K) (n : ℕ) :
    (a * b) ^ n * (b ^ n)⁻¹ * (a ^ n)⁻¹ ∈ V := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (a * b) ^ (n + 1) * (b ^ (n + 1))⁻¹ * (a ^ (n + 1))⁻¹ =
        ((a * b) ^ n * (b ^ n)⁻¹ * (a ^ n)⁻¹) * (a ^ n * ⁅b ^ n, a⁆ * (a ^ n)⁻¹) := by
      rw [commutatorElement_def, pow_succ, pow_succ, pow_succ]
      group
    rw [e]
    exact V.mul_mem ih ((mem_normalizer_iff.mp (hKV (pow_mem ha n)) _).mp
      (hcomm (commutator_mem_commutator (pow_mem hb n) ha)))

theorem pow_eq_pow_mod {p : ℕ} {x : G} (hxp : x ^ p = 1) (a : ℕ) : x ^ a = x ^ (a % p) := by
  conv_lhs => rw [← Nat.div_add_mod a p, pow_add, pow_mul, hxp, one_pow, one_mul]

theorem not_mem_closure_of_coprime {p : ℕ} [hp : Fact p.Prime] {K V : Subgroup G}
    (hKV : K ≤ normalizer (V : Set G)) (hcomm : ⁅K, K⁆ ≤ V) {S : Set G}
    (hS : ∀ s ∈ S, s ∈ K ∧ ∃ m : ℕ, m.Coprime p ∧ s ^ m ∈ V) {x : G} (hxp : x ^ p = 1)
    (hxV : x ∉ V) : x ∉ closure S := by
  let V' : Subgroup G :=
    { carrier := {k | k ∈ K ∧ ∃ m : ℕ, m.Coprime p ∧ k ^ m ∈ V}
      mul_mem' := by
        rintro a b ⟨ha, m, hm, ham⟩ ⟨hb, m', hm', hbm⟩
        refine ⟨K.mul_mem ha hb, m * m', Nat.coprime_mul_iff_left.mpr ⟨hm, hm'⟩, ?_⟩
        have h1 := mul_pow_mul_inv_mem hKV hcomm ha hb (m * m')
        have h2 : a ^ (m * m') ∈ V := by rw [pow_mul]; exact V.pow_mem ham _
        have h3 : b ^ (m * m') ∈ V := by rw [mul_comm, pow_mul]; exact V.pow_mem hbm _
        have e : (a * b) ^ (m * m') =
            ((a * b) ^ (m * m') * (b ^ (m * m'))⁻¹ * (a ^ (m * m'))⁻¹) *
              (a ^ (m * m') * b ^ (m * m')) := by group
        rw [e]
        exact V.mul_mem h1 (V.mul_mem h2 h3)
      one_mem' := ⟨K.one_mem, 1, Nat.coprime_one_left p, by rw [one_pow]; exact V.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, m, hm, ham⟩
        exact ⟨K.inv_mem ha, m, hm, by rw [inv_pow]; exact V.inv_mem ham⟩ }
  have hle : closure S ≤ V' := (closure_le _).mpr fun s hs => hS s hs
  intro hx
  obtain ⟨-, m, hm, hxm⟩ := hle hx
  obtain ⟨m', -, hm'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hm hp.out.one_lt
  apply hxV
  have e : x = (x ^ m) ^ m' := by
    rw [← pow_mul, pow_eq_pow_mod hxp (m * m'), hm', pow_one]
  rw [e]
  exact V.pow_mem hxm _

theorem le_normalizer_of_le {Hn C M : Subgroup G} (hHC : Hn ≤ normalizer (C : Set G))
    (hCM : C ≤ M) (hMH : M ≤ Hn) : C ≤ normalizer (M : Set G) := by
  have fwd : ∀ c ∈ C, ∀ m ∈ M, c * m * c⁻¹ ∈ M := by
    intro c hc m hm
    have h1 : m * c⁻¹ * m⁻¹ ∈ C := (mem_normalizer_iff.mp (hHC (hMH hm)) _).mp (C.inv_mem hc)
    have e : c * m * c⁻¹ = (c * (m * c⁻¹ * m⁻¹)) * m := by group
    rw [e]
    exact M.mul_mem (hCM (C.mul_mem hc h1)) hm
  intro c hc
  rw [mem_normalizer_iff]
  intro m
  refine ⟨fun hm => fwd c hc m hm, fun hm => ?_⟩
  have := fwd c⁻¹ (C.inv_mem hc) _ hm
  rwa [show c⁻¹ * (c * m * c⁻¹) * c⁻¹⁻¹ = m by group] at this

theorem le_normalizer_closure {N : Subgroup G} {S : Set G}
    (hS : ∀ n ∈ N, ∀ s ∈ S, n * s * n⁻¹ ∈ S) : N ≤ normalizer (closure S : Set G) := by
  have fwd : ∀ n ∈ N, ∀ y ∈ closure S, n * y * n⁻¹ ∈ closure S := by
    intro n hn y hy
    have hle : closure S ≤ (closure S).comap (MulAut.conj n).toMonoidHom :=
      (closure_le _).mpr fun s hs => by
        show (MulAut.conj n).toMonoidHom s ∈ closure S
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact subset_closure (hS n hn s hs)
    have := hle hy
    rw [mem_comap] at this
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this
  intro n hn
  rw [mem_normalizer_iff]
  intro y
  refine ⟨fun hy => fwd n hn y hy, fun hy => ?_⟩
  have := fwd n⁻¹ (N.inv_mem hn) _ hy
  rwa [show n⁻¹ * (n * y * n⁻¹) * n⁻¹⁻¹ = y by group] at this

theorem orderOf_conj' (n g : G) : orderOf (n * g * n⁻¹) = orderOf g :=
  orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective g

theorem exists_units_hom {p : ℕ} [hp : Fact p.Prime] {N B₁ Z : Subgroup G} {b₁ : G}
    (hordb : orderOf b₁ = p) (hinf : zpowers b₁ ⊓ Z = ⊥)
    (hdec : ∀ u ∈ B₁, ∃ i < p, ∃ w ∈ Z, u = b₁ ^ i * w) (hb₁B : b₁ ∈ B₁) (hZB : Z ≤ B₁)
    (hcommB : ∀ a ∈ B₁, ∀ b ∈ B₁, a * b = b * a)
    (hNB : ∀ n ∈ N, ∀ u ∈ B₁, n * u * n⁻¹ ∈ B₁) (hNZ : ∀ n ∈ N, ∀ w ∈ Z, n * w * n⁻¹ ∈ Z) :
    ∃ χ : N →* (ZMod p)ˣ, ∀ n : N,
      χ n = 1 ↔ ∀ u ∈ B₁, ∃ w ∈ Z, (n : G) * u * (n : G)⁻¹ = u * w := by
  have hb₁p : b₁ ^ p = 1 := by rw [← hordb]; exact pow_orderOf_eq_one b₁
  have huniq : ∀ a b : ℕ, ∀ w ∈ Z, ∀ w' ∈ Z, b₁ ^ a * w = b₁ ^ b * w' →
      (a : ZMod p) = (b : ZMod p) := by
    intro a b w hw w' hw' h
    have h1 : (b₁ ^ b)⁻¹ * b₁ ^ a = w' * w⁻¹ := by
      calc (b₁ ^ b)⁻¹ * b₁ ^ a = (b₁ ^ b)⁻¹ * (b₁ ^ a * w) * w⁻¹ := by group
        _ = (b₁ ^ b)⁻¹ * (b₁ ^ b * w') * w⁻¹ := by rw [h]
        _ = w' * w⁻¹ := by group
    have h2 : (b₁ ^ b)⁻¹ * b₁ ^ a ∈ zpowers b₁ ⊓ Z :=
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ (mem_zpowers b₁) b))
          (Subgroup.pow_mem _ (mem_zpowers b₁) a),
        h1 ▸ Z.mul_mem hw' (Z.inv_mem hw)⟩
    rw [hinf, mem_bot] at h2
    have h3 : b₁ ^ a = b₁ ^ b := by
      calc b₁ ^ a = b₁ ^ b * ((b₁ ^ b)⁻¹ * b₁ ^ a) := by group
        _ = b₁ ^ b := by rw [h2, mul_one]
    rw [ZMod.natCast_eq_natCast_iff, ← hordb]
    exact pow_eq_pow_iff_modEq.mp h3
  have hex : ∀ n : N, ∃ i : ZMod p, ∃ w ∈ Z, (n : G) * b₁ * (n : G)⁻¹ = b₁ ^ i.val * w := by
    intro n
    obtain ⟨i, hi, w, hw, he⟩ := hdec _ (hNB n n.2 b₁ hb₁B)
    refine ⟨(i : ZMod p), w, hw, ?_⟩
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi]
    exact he
  choose f hf using hex
  have hval : ∀ i : ZMod p, ((i.val : ℕ) : ZMod p) = i := ZMod.natCast_zmod_val
  have hone : (1 : ZMod p).val = 1 := ZMod.val_one p
  let χ' : N →* ZMod p :=
    { toFun := f
      map_one' := by
        obtain ⟨w, hw, he⟩ := hf 1
        have h1 : b₁ ^ (f 1).val * w = b₁ ^ (1 : ZMod p).val * 1 := by
          rw [← he, hone, pow_one, mul_one]
          simp
        have := huniq _ _ w hw 1 Z.one_mem h1
        rwa [hval, hval] at this
      map_mul' := by
        intro n m
        obtain ⟨w, hw, he⟩ := hf (n * m)
        obtain ⟨wn, hwn, hen⟩ := hf n
        obtain ⟨wm, hwm, hem⟩ := hf m
        have hb1 : b₁ ^ (f m).val ∈ B₁ := B₁.pow_mem hb₁B _
        have hwnB : wn ∈ B₁ := hZB hwn
        have hconj : (n : G) * b₁ ^ (f m).val * (n : G)⁻¹ = (b₁ ^ (f n).val * wn) ^ (f m).val := by
          rw [← hen, conj_pow]
        have hcw : Commute b₁ wn := hcommB _ hb₁B _ hwnB
        have h1 : b₁ ^ (f (n * m)).val * w =
            b₁ ^ ((f n).val * (f m).val) * (wn ^ (f m).val * ((n : G) * wm * (n : G)⁻¹)) := by
          rw [← he]
          calc ((n * m : N) : G) * b₁ * ((n * m : N) : G)⁻¹
              = (n : G) * ((m : G) * b₁ * (m : G)⁻¹) * (n : G)⁻¹ := by simp; group
            _ = (n : G) * (b₁ ^ (f m).val * wm) * (n : G)⁻¹ := by rw [hem]
            _ = ((n : G) * b₁ ^ (f m).val * (n : G)⁻¹) * ((n : G) * wm * (n : G)⁻¹) := by group
            _ = (b₁ ^ (f n).val * wn) ^ (f m).val * ((n : G) * wm * (n : G)⁻¹) := by rw [hconj]
            _ = b₁ ^ ((f n).val * (f m).val) * (wn ^ (f m).val * ((n : G) * wm * (n : G)⁻¹)) := by
              rw [(hcw.pow_left _).mul_pow, ← pow_mul, mul_assoc]
        have := huniq _ _ w hw _ (Z.mul_mem (Z.pow_mem hwn _) (hNZ n n.2 wm hwm)) h1
        rw [hval, Nat.cast_mul, hval, hval] at this
        exact this }
  refine ⟨χ'.toHomUnits, fun n => ⟨fun h u hu => ?_, fun h => ?_⟩⟩
  · have hfn : f n = 1 := by
      have := congrArg Units.val h
      simpa [χ'] using this
    obtain ⟨wn, hwn, hen⟩ := hf n
    rw [hfn, hone, pow_one] at hen
    obtain ⟨i, -, z, hz, rfl⟩ := hdec u hu
    have hcw : Commute b₁ wn := hcommB _ hb₁B _ (hZB hwn)
    refine ⟨z⁻¹ * wn ^ i * ((n : G) * z * (n : G)⁻¹), Z.mul_mem (Z.mul_mem (Z.inv_mem hz)
      (Z.pow_mem hwn i)) (hNZ n n.2 z hz), ?_⟩
    have hcz : Commute (b₁ ^ i) z := hcommB _ (B₁.pow_mem hb₁B i) _ (hZB hz)
    have hcz' : Commute (b₁ ^ i) (wn ^ i) := (hcw.pow_right i).pow_left i
    calc (n : G) * (b₁ ^ i * z) * (n : G)⁻¹
        = ((n : G) * b₁ * (n : G)⁻¹) ^ i * ((n : G) * z * (n : G)⁻¹) := by rw [conj_pow]; group
      _ = (b₁ * wn) ^ i * ((n : G) * z * (n : G)⁻¹) := by rw [hen]
      _ = b₁ ^ i * wn ^ i * ((n : G) * z * (n : G)⁻¹) := by rw [hcw.mul_pow]
      _ = b₁ ^ i * z * (z⁻¹ * wn ^ i * ((n : G) * z * (n : G)⁻¹)) := by group
  · obtain ⟨w, hw, he⟩ := h b₁ hb₁B
    obtain ⟨wn, hwn, hen⟩ := hf n
    have h1 : b₁ ^ (f n).val * wn = b₁ ^ (1 : ZMod p).val * w := by
      rw [← hen, he, hone, pow_one]
    have := huniq _ _ wn hwn w hw h1
    rw [hval, hval] at this
    ext
    simpa [χ'] using this

theorem exists_coprime_generator [Finite G] {p : ℕ} [hp : Fact p.Prime] {N H : Subgroup G}
    (hHN : H ≤ N) (χ : N →* (ZMod p)ˣ) :
    ∃ h ∈ H, (orderOf h).Coprime p ∧ H ≤ (H ⊓ χ.ker.map N.subtype) ⊔ zpowers h := by
  set S : Subgroup (ZMod p)ˣ := (H.subgroupOf N).map χ with hSdef
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := S)
  obtain ⟨h₀', hh₀', hγeq⟩ := Subgroup.mem_map.mp γ.2
  have hh₀H : (h₀' : G) ∈ H := mem_subgroupOf.mp hh₀'
  obtain ⟨a, m, hm, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (h₀' : G)).ne' p hp.out.one_lt.ne'
  have hγdvd : orderOf (γ : (ZMod p)ˣ) ∣ p - 1 := ZMod.orderOf_units_dvd_card_sub_one _
  have hpcop : Nat.Coprime p (orderOf (γ : (ZMod p)ˣ)) := by
    refine Nat.Coprime.coprime_dvd_right hγdvd ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr ?_)
    exact Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hp.out.one_lt) (Nat.sub_lt hp.out.pos one_pos)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, (γ : (ZMod p)ˣ) ^ (p ^ a * c) = γ := by
    by_cases h1 : orderOf (γ : (ZMod p)ˣ) = 1
    · refine ⟨0, ?_⟩
      rw [orderOf_eq_one_iff] at h1
      rw [h1, one_pow]
    · have hlt : 1 < orderOf (γ : (ZMod p)ˣ) := by
        have := orderOf_pos (γ : (ZMod p)ˣ)
        omega
      obtain ⟨c, -, hc⟩ := Nat.exists_mul_mod_eq_one_of_coprime (Nat.Coprime.pow_left a hpcop) hlt
      exact ⟨c, by rw [← pow_mod_orderOf, hc, pow_one]⟩
  set h : G := (h₀' : G) ^ (p ^ a * c) with hh
  have hhH : h ∈ H := H.pow_mem hh₀H _
  have hhN : h ∈ N := hHN hhH
  refine ⟨h, hhH, ?_, ?_⟩
  · have hdvd : orderOf h ∣ m := by
      apply orderOf_dvd_of_pow_eq_one
      rw [hh, ← pow_mul, show p ^ a * c * m = (p ^ a * m) * c by ring, pow_mul, ← hord,
        pow_orderOf_eq_one, one_pow]
    exact Nat.Coprime.coprime_dvd_left hdvd ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm).symm
  · have hχh : χ ⟨h, hhN⟩ = γ := by
      have e : (⟨h, hhN⟩ : N) = h₀' ^ (p ^ a * c) := Subtype.ext (by simp [hh])
      rw [e, map_pow, hγeq, hc]
    intro h' hh'
    have hh'N : h' ∈ N := hHN hh'
    have hmem : χ ⟨h', hh'N⟩ ∈ S := Subgroup.mem_map_of_mem χ (mem_subgroupOf.mpr hh')
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (hγ ⟨_, hmem⟩)
    have hj' : (γ : (ZMod p)ˣ) ^ j = χ ⟨h', hh'N⟩ := by
      have := congrArg Subtype.val hj
      simpa using this
    have hk : h' * h ^ (-j) ∈ H ⊓ χ.ker.map N.subtype := by
      refine ⟨H.mul_mem hh' (H.zpow_mem hhH _), ?_⟩
      refine Subgroup.mem_map.mpr ⟨⟨h', hh'N⟩ * ⟨h, hhN⟩ ^ (-j), ?_, by simp⟩
      rw [MonoidHom.mem_ker, map_mul, map_zpow, hχh, ← hj', ← zpow_add, add_neg_cancel,
        zpow_zero]
    have e : h' = (h' * h ^ (-j)) * h ^ j := by group
    rw [e]
    exact mul_mem (mem_sup_left hk) (mem_sup_right (zpow_mem (mem_zpowers h) j))

end CFSG.StandardType.GGL48TW.Frob
