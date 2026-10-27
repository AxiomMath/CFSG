module

public import CFSG.Quasithin.H13.A6S1372L76N3c

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6L74

variable {G : Type} [Group G]

theorem conj_eq_of_odd {A W : Subgroup G} (hA : IsElemAbelian 2 A) (hWA : W ≤ A) {k : G}
    (hkW : ∀ w ∈ W, k * w * k⁻¹ = w) (hk : ∀ a ∈ A, k * a * k⁻¹ * a⁻¹ ∈ W) {m : ℕ}
    (hm : Odd m) (hkm : k ^ m = 1) {a : G} (ha : a ∈ A) : k * a * k⁻¹ = a := by
  obtain ⟨w, hwdef⟩ : ∃ w, w = k * a * k⁻¹ * a⁻¹ := ⟨_, rfl⟩
  have hwW : w ∈ W := hwdef ▸ hk a ha
  have hka : k * a * k⁻¹ = w * a := by rw [hwdef]; group
  have hpow : ∀ n : ℕ, k ^ n * a * (k ^ n)⁻¹ = w ^ n * a := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc k ^ (n + 1) * a * (k ^ (n + 1))⁻¹ = k * (k ^ n * a * (k ^ n)⁻¹) * k⁻¹ := by group
        _ = k * (w ^ n * a) * k⁻¹ := by rw [ih]
        _ = (k * w * k⁻¹) ^ n * (k * a * k⁻¹) := by rw [conj_pow]; group
        _ = w ^ n * (w * a) := by rw [hkW w hwW, hka]
        _ = w ^ (n + 1) * a := by group
  have h1 := hpow m
  rw [hkm, one_mul, inv_one, mul_one] at h1
  have hwm : w ^ m = 1 := by
    calc w ^ m = w ^ m * a * a⁻¹ := by group
      _ = 1 := by rw [← h1, mul_inv_cancel]
  have hw2 : w ^ 2 = 1 := hA.2 w (hWA hwW)
  obtain ⟨j, rfl⟩ := hm
  have hw1 : w = 1 := by
    rw [pow_succ, pow_mul, hw2, one_pow, one_mul] at hwm
    exact hwm
  rw [hka, hw1, one_mul]

theorem comm_comm_mem {A Z : Subgroup G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {c k w : G}
    (hcA : c ∈ Subgroup.normalizer (A : Set G)) (hkA : k ∈ Subgroup.normalizer (A : Set G))
    (hw : w ∈ A) (hcu : c * (k * w * k⁻¹ * w⁻¹) * c⁻¹ = k * w * k⁻¹ * w⁻¹)
    (hq : ∀ b ∈ A, (k * c * k⁻¹ * c⁻¹) * b * (k * c * k⁻¹ * c⁻¹)⁻¹ * b⁻¹ ∈ Z) :
    k * (c * w * c⁻¹ * w⁻¹) * k⁻¹ * (c * w * c⁻¹ * w⁻¹)⁻¹ ∈ Z := by
  obtain ⟨a, hadef⟩ : ∃ a, a = c * w * c⁻¹ * w⁻¹ := ⟨_, rfl⟩
  obtain ⟨u, hudef⟩ : ∃ u, u = k * w * k⁻¹ * w⁻¹ := ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q, q = k * c * k⁻¹ * c⁻¹ := ⟨_, rfl⟩
  rw [← hudef] at hcu
  rw [← hqdef] at hq
  rw [← hadef]
  have haA : a ∈ A := hadef ▸ A.mul_mem ((Subgroup.mem_normalizer_iff.mp hcA w).mp hw)
    (A.inv_mem hw)
  have huA : u ∈ A := hudef ▸ A.mul_mem ((Subgroup.mem_normalizer_iff.mp hkA w).mp hw)
    (A.inv_mem hw)
  have hau : a * u = u * a := hA a haA u huA
  have e1 : k * c * k⁻¹ = q * c := by rw [hqdef]; group
  have e2 : k * w * k⁻¹ = u * w := by rw [hudef]; group
  have e4 : c * w * c⁻¹ = a * w := by rw [hadef]; group
  have hb : u * a * w ∈ A := A.mul_mem (A.mul_mem huA haA) hw
  have key : k * a * k⁻¹ * a⁻¹ = q * (u * a * w) * q⁻¹ * (u * a * w)⁻¹ := by
    have h1 : k * a * k⁻¹ * a⁻¹ =
        (k * c * k⁻¹) * (k * w * k⁻¹) * (k * c * k⁻¹)⁻¹ * (k * w * k⁻¹)⁻¹ * a⁻¹ := by
      rw [hadef]; group
    have h2 : (q * c) * (u * w) * (q * c)⁻¹ * (u * w)⁻¹ * a⁻¹ =
        q * (c * u * c⁻¹) * (c * w * c⁻¹) * q⁻¹ * w⁻¹ * u⁻¹ * a⁻¹ := by group
    have h3 : u⁻¹ * a⁻¹ = a⁻¹ * u⁻¹ := by
      rw [← mul_inv_rev, ← mul_inv_rev, hau]
    rw [h1, e1, e2, h2, hcu, e4]
    calc q * u * (a * w) * q⁻¹ * w⁻¹ * u⁻¹ * a⁻¹ =
        q * u * (a * w) * q⁻¹ * w⁻¹ * (u⁻¹ * a⁻¹) := by group
      _ = q * u * (a * w) * q⁻¹ * w⁻¹ * (a⁻¹ * u⁻¹) := by rw [h3]
      _ = q * (u * a * w) * q⁻¹ * (u * a * w)⁻¹ := by group
  rw [key]
  exact hq _ hb

end A6L74

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

@[expose] noncomputable def C74 (H : Subgroup G) : Subgroup G :=
  centralizerMod (Subgroup.centralizer (pCoreOf 2 H : Set G)) H (conjClosure S.V3 H)

theorem mem_C74_iff {H : Subgroup G} {h : G} :
    h ∈ S.C74 H ↔ h ∈ H ∧ ∀ u ∈ conjClosure S.V3 H,
      h * u * h⁻¹ * u⁻¹ ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
  constructor
  · rintro ⟨hh, -, hu⟩
    exact ⟨hh, hu⟩
  · rintro ⟨hh, hu⟩
    exact ⟨hh, InternalSec.le_normalizer_centralizer (le_normalizer_pCoreOf 2 H) hh, hu⟩

theorem C74_le (H : Subgroup G) : S.C74 H ≤ H := fun _ h => ((S.mem_C74_iff).1 h).1

theorem le_normalizer_C74 (H : Subgroup G) :
    H ≤ Subgroup.normalizer (S.C74 H : Set G) := by
  have key : ∀ h ∈ H, ∀ x ∈ S.C74 H, h * x * h⁻¹ ∈ S.C74 H := by
    intro h hh x hx
    obtain ⟨hxH, hxu⟩ := (S.mem_C74_iff).1 hx
    refine (S.mem_C74_iff).2 ⟨H.mul_mem (H.mul_mem hh hxH) (H.inv_mem hh), fun u hu => ?_⟩
    have hu' : h⁻¹ * u * h⁻¹⁻¹ ∈ conjClosure S.V3 H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H (H.inv_mem hh)) u).mp hu
    have h1 := hxu _ hu'
    have h2 : h * (x * (h⁻¹ * u * h⁻¹⁻¹) * x⁻¹ * (h⁻¹ * u * h⁻¹⁻¹)⁻¹) * h⁻¹ ∈
        Subgroup.centralizer (pCoreOf 2 H : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (InternalSec.le_normalizer_centralizer
        (le_normalizer_pCoreOf 2 H) hh) _).mp h1
    have e : h * x * h⁻¹ * u * (h * x * h⁻¹)⁻¹ * u⁻¹ =
        h * (x * (h⁻¹ * u * h⁻¹⁻¹) * x⁻¹ * (h⁻¹ * u * h⁻¹⁻¹)⁻¹) * h⁻¹ := by group
    rw [e]
    exact h2
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key h hh x, fun hx => ?_⟩
  have := key h⁻¹ (H.inv_mem hh) _ hx
  simpa [mul_assoc] using this

section Setting

variable {S} (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz)
include hNS h13315 h1356two hH

theorem QH_le_C74 : pCoreOf 2 H ≤ S.C74 H := by
  have hF := S.hypF91 hNS h13315 h1356two hH
  intro q hq
  exact (S.mem_C74_iff).2 ⟨pCoreOf_le 2 H hq, fun u hu =>
    S.V1_le_centralizer_QH hNS h13315 h1356two hH (hF.commutator_mem_V₁ hq hu)⟩

theorem not_L1_le_C74 (h13314 : Stmt13_3_14)
    (hhat : ¬ IsHatA6 L) : ¬ S.L1 ≤ S.C74 H := by
  intro hle
  have hc := (S.mem_C74_iff).1 (hle (S.cL1_mem hhat))
  have h1 := hc.2 S.v2 (S.v2_mem_UH H)
  have hV3 : (S.cL1 hhat : G) * S.v2 * (S.cL1 hhat : G)⁻¹ * S.v2⁻¹ ∈ S.V3 :=
    S.V3.mul_mem (S.conj_v2_mem_V3 (S.cL1_rho hhat)) (S.V3.inv_mem S.v2_mem_V3)
  exact S.comm_v2_not_mem_V1 (S.cL1_rho hhat)
    (S.V3_inf_centralizer_QH_le hNS h13315 h1356two hH h13314 ⟨hV3, h1⟩)

theorem not_le_centralizer_U0
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) {K : Subgroup G} (hKC : K ≤ S.C74 H)
    (hK2 : oTwoRes K = K) (hKQ : ¬ K ≤ pCoreOf 2 H) :
    ¬ K ≤ Subgroup.centralizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hKU
  have hF := S.hypF91 hNS h13315 h1356two hH
  apply hKQ
  rw [← hK2]
  refine (Subgroup.closure_le _).2 ?_
  rintro k ⟨hk, m, hm, hkm⟩
  obtain ⟨hkH, hku⟩ := (S.mem_C74_iff).1 (hKC hk)
  have hkU : k ∈ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H hkH
  have hcent : ∀ u ∈ conjClosure S.V3 H, k * u * k⁻¹ = u := by
    intro u hu
    refine A6L74.conj_eq_of_odd hab (inf_le_left :
      conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ conjClosure S.V3 H)
      (fun w hw => ?_) (fun a ha => ⟨(conjClosure S.V3 H).mul_mem
        ((Subgroup.mem_normalizer_iff.mp hkU a).mp ha) ((conjClosure S.V3 H).inv_mem ha),
        hku a ha⟩) hm hkm hu
    have := Subgroup.mem_centralizer_iff.mp (hKU hk) w hw
    rw [← this, mul_inv_cancel_right]
  have hkQ : k ∈ pCoreOf 2 H :=
    (S.mem_QH_iff_tilde hNS h13315 h1356two hH hkH).2 fun u hu => by
      rw [hcent u hu, mul_inv_cancel]
      exact Subgroup.one_mem _
  exact hkQ

omit hNS h13315 h1356two in
theorem not_le_normalizer_L (h139 : Stmt13_3_9)
    (hhat : ¬ IsHatA6 L) {K : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hK2 : oTwoRes K = K) (hK1 : K ≠ ⊥)
    (hL1K : ¬ S.L1 ≤ K) : ¬ K ≤ Subgroup.normalizer (L : Set G) := by
  intro hKM
  have hz : S.z ∈ fsuV1 T V := S.mem_V1_iff.2 (Or.inr rfl)
  have hzL : S.z ∉ Subgroup.centralizer (L : Set G) := by
    intro h
    have h1 : S.z ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨S.z_mem_V, h⟩
    rw [S.zv, Subgroup.mem_bot] at h1
    exact S.z_ne_one h1
  have hKz : K ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({S.z} : Set G) :=
    le_inf hKM (hKH.trans hH.2.1)
  have hInH : InH T H := ⟨le_sup_right.trans hH.1.1, hH.1.2⟩
  rcases h139 G T L V H K S.z S.h13 S.irr S.a6 hInH hH.2.2 hK2 hKH hHK hz hzL hKz with
    h | ⟨-, hA6, -⟩
  · exact hK1 h
  · exact hL1K (hA6 (S.nonempty_alt6_of_not_hat hhat)).ge

end Setting

end Setting4

end CFSG.Quasithin.H13.A6
