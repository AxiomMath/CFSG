module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3320S1
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3320

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3
open scoped commutatorElement

namespace S3320

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem comm_of_sq {Q : Type*} [Group Q] {a b : Q} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b * (a * b) = 1) : a * b = b * a := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h := inv_eq_of_mul_eq_one_right hab
  rw [mul_inv_rev, ha', hb'] at h
  exact h.symm

omit [Finite G] in
theorem conj_sq_of_pow {Q : Type*} [Group Q] {τ b : Q} {j : ℕ} (hb : b ^ 3 = 1)
    (hj0 : j % 3 ≠ 0) (hj : τ * b * τ⁻¹ = b ^ j) : τ * τ * b * (τ * τ)⁻¹ = b := by
  have hjj : (j * j) % 3 = 1 := by
    rw [Nat.mul_mod]
    have : j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases this with h | h <;> rw [h]
  calc τ * τ * b * (τ * τ)⁻¹ = τ * (τ * b * τ⁻¹) * τ⁻¹ := by group
    _ = τ * b ^ j * τ⁻¹ := by rw [hj]
    _ = (τ * b * τ⁻¹) ^ j := conj_pow.symm
    _ = b ^ (j * j) := by rw [hj, ← pow_mul]
    _ = b := by rw [pow_eq_pow_mod _ hb, hjj, pow_one]

structure IsB₀ (X T D B₀ : Subgroup G) : Prop where
  le : B₀ ≤ X ⊔ T ⊔ D
  nor : X ⊔ T ⊔ D ≤ Subgroup.normalizer (B₀ : Set G)
  inf : (X ⊔ T) ⊓ B₀ ≤ pCoreOf 2 (X ⊔ T)
  max : ∀ N : Subgroup G, B₀ < N → N ≤ X ⊔ T ⊔ D →
    X ⊔ T ⊔ D ≤ Subgroup.normalizer (N : Set G) → ¬ (X ⊔ T) ⊓ N ≤ pCoreOf 2 (X ⊔ T)

namespace Hyp3320

variable {T M L D X : Subgroup G} (H : Hyp3320 G T M L D X)

include H

omit H in
theorem exists_isB₀ : ∃ B₀ : Subgroup G, IsB₀ X T D B₀ := by
  obtain ⟨B₀, h1, h2, h3, h4⟩ := exists_B₀ (X := X) (T := T) (D := D)
  exact ⟨B₀, ⟨h1, h2, h3, h4⟩⟩

theorem exists_x : ∃ x ∈ X, x ^ 3 = 1 ∧ x ∉ pCoreOf 2 (X ⊔ T) ∧
    ∀ x' ∈ X, ∃ j : ℕ, x' * (x ^ j)⁻¹ ∈ pCoreOf 2 (X ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := H.hS3
  set ψ : ↥(X ⊔ T) →* Equiv.Perm (Fin 3) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥(X ⊔ T))) with hψ
  have hψk : ∀ y : ↥(X ⊔ T), ψ y = 1 → (y : G) ∈ pCoreOf 2 (X ⊔ T) := by
    intro y hy
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥(X ⊔ T)) y = 1 :=
      (map_eq_one_iff e.toMonoidHom e.injective).mp hy
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact (Lem3328.mem_pCore_iff _).mp h2
  obtain ⟨x, hxX, hxo, hxR⟩ : ∃ x ∈ X, Odd (orderOf x) ∧ x ∉ pCoreOf 2 (X ⊔ T) := by
    by_contra hcon
    push Not at hcon
    apply H.not_X_le_R
    have h1 : oTwoUpper X ≤ pCoreOf 2 (X ⊔ T) :=
      (Subgroup.closure_le _).mpr fun y ⟨hy, ho⟩ => hcon y hy ho
    rwa [H.hXX] at h1
  have hxXT : x ∈ X ⊔ T := Subgroup.mem_sup_left hxX
  have hσ1 : ψ ⟨x, hxXT⟩ ≠ 1 := fun h1 => hxR (hψk _ h1)
  have hσs : Equiv.Perm.sign (ψ ⟨x, hxXT⟩) = 1 := sign_eq_one le_sup_left H.hXX ψ x hxX
  have h3 : ψ ⟨x, hxXT⟩ ^ 3 = 1 := One3323.pow_three_of_sign _ hσs
  have hgen : ∀ σ : Equiv.Perm (Fin 3), Equiv.Perm.sign σ = 1 →
      ∃ j : ℕ, j < 3 ∧ σ = ψ ⟨x, hxXT⟩ ^ j := by
    have key : ∀ κ σ : Equiv.Perm (Fin 3), κ ≠ 1 → Equiv.Perm.sign κ = 1 →
        Equiv.Perm.sign σ = 1 → ∃ j : ℕ, j < 3 ∧ σ = κ ^ j := by decide
    exact fun σ hσ => key _ σ hσ1 hσs hσ
  have hx3R : x ^ 3 ∈ pCoreOf 2 (X ⊔ T) := by
    have e1 : (⟨x ^ 3, (X ⊔ T).pow_mem hxXT 3⟩ : ↥(X ⊔ T)) = ⟨x, hxXT⟩ ^ 3 := rfl
    exact hψk ⟨x ^ 3, (X ⊔ T).pow_mem hxXT 3⟩ (by rw [e1, map_pow, h3])
  have hx3 : x ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (X ⊔ T)) ⟨_, hx3R⟩
    have hk' : (x ^ 3) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hodd : Odd (orderOf (x ^ 3)) := Odd.of_dvd_nat hxo (orderOf_pow_dvd 3)
    have h1 := orderOf_dvd_of_pow_eq_one hk'
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    rcases i with _ | i
    · rw [pow_zero, orderOf_eq_one_iff] at hi
      exact hi
    · rw [hi, pow_succ] at hodd
      exact absurd hodd (by simp [Nat.odd_mul])
  refine ⟨x, hxX, hx3, hxR, fun x' hx' => ?_⟩
  have hx'XT : x' ∈ X ⊔ T := Subgroup.mem_sup_left hx'
  obtain ⟨j, -, hj⟩ := hgen _ (sign_eq_one le_sup_left H.hXX ψ x' hx')
  refine ⟨j, hψk ⟨_, (X ⊔ T).mul_mem hx'XT ((X ⊔ T).inv_mem ((X ⊔ T).pow_mem hxXT j))⟩ ?_⟩
  have e1 : (⟨x' * (x ^ j)⁻¹, (X ⊔ T).mul_mem hx'XT ((X ⊔ T).inv_mem
      ((X ⊔ T).pow_mem hxXT j))⟩ : ↥(X ⊔ T)) = ⟨x', hx'XT⟩ * (⟨x, hxXT⟩ ^ j)⁻¹ := rfl
  rw [e1, map_mul, map_inv, map_pow, ← hj, mul_inv_cancel]

variable {B₀ : Subgroup G}

theorem cube_mem (hB : IsB₀ X T D B₀) (habel : ⁅conjClosure X D, conjClosure X D⁆ ≤ B₀) :
    (∀ y ∈ conjClosure X D, y ^ 3 ∈ B₀) ∧ X ⊓ pCoreOf 2 (X ⊔ T) ≤ B₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := conjClosure X D with hY
  have hYB : Y ≤ X ⊔ T ⊔ D := conjClosure_le fun d hd x hx => (X ⊔ T ⊔ D).mul_mem
    ((X ⊔ T ⊔ D).mul_mem (Subgroup.mem_sup_right hd) (Subgroup.mem_sup_left
      (Subgroup.mem_sup_left hx))) ((X ⊔ T ⊔ D).inv_mem (Subgroup.mem_sup_right hd))
  have hconjB₀ : ∀ {g : G}, g ∈ X ⊔ T ⊔ D → ∀ {b : G}, b ∈ B₀ → g * b * g⁻¹ ∈ B₀ :=
    fun hg b hb => (Subgroup.mem_normalizer_iff.mp (hB.nor hg) b).mp hb
  have hcomm : ∀ {a b : G}, a ∈ Y → b ∈ Y → ⁅a, b⁆ ∈ B₀ := fun ha hb =>
    habel (Subgroup.commutator_mem_commutator ha hb)
  have hcube : ∀ {a b : G}, a ∈ Y → b ∈ Y → a ^ 3 ∈ B₀ → b ^ 3 ∈ B₀ → (a * b) ^ 3 ∈ B₀ := by
    intro a b ha hb ha3 hb3
    have hN : (B₀.subgroupOf Y).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (hYB.trans hB.nor)
    set π := QuotientGroup.mk' (B₀.subgroupOf Y)
    have hc : Commute (π ⟨a, ha⟩) (π ⟨b, hb⟩) := by
      show π ⟨a, ha⟩ * π ⟨b, hb⟩ = π ⟨b, hb⟩ * π ⟨a, ha⟩
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have := hcomm (Y.inv_mem hb) (Y.inv_mem ha)
      rw [commutatorElement_def, inv_inv, inv_inv] at this
      convert this using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have h1 : π (⟨a, ha⟩ * ⟨b, hb⟩) ^ 3 = 1 := by
      rw [map_mul, hc.mul_pow]
      have ea : π ⟨a, ha⟩ ^ 3 = 1 := by
        rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        simpa using ha3
      have eb : π ⟨b, hb⟩ ^ 3 = 1 := by
        rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        simpa using hb3
      rw [ea, eb, one_mul]
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h1
    simpa using h1
  let Ω₀ : Subgroup G :=
    { carrier := {y | y ∈ Y ∧ y ^ 3 ∈ B₀}
      mul_mem' := fun ⟨ha, ha3⟩ ⟨hb, hb3⟩ => ⟨Y.mul_mem ha hb, hcube ha hb ha3 hb3⟩
      one_mem' := ⟨Y.one_mem, by rw [one_pow]; exact B₀.one_mem⟩
      inv_mem' := fun {a} ⟨ha, ha3⟩ => ⟨Y.inv_mem ha, by rw [inv_pow]; exact B₀.inv_mem ha3⟩ }
  have hΩN : X ⊔ T ⊔ D ≤ Subgroup.normalizer (Ω₀ : Set G) :=
    Main3324.le_normalizer_of_conj fun g hg y hy => ⟨(Subgroup.mem_normalizer_iff.mp
      (H.hBY hg) y).mp hy.1, by rw [conj_pow]; exact hconjB₀ hg hy.2⟩
  have hΩB : Ω₀ ≤ Subgroup.normalizer (B₀ : Set G) := fun y hy => hB.nor (hYB hy.1)
  obtain ⟨x, hxX, hx3, hxR, -⟩ := H.exists_x
  have hxB : x ∉ B₀ := fun h => hxR (hB.inf ⟨Subgroup.mem_sup_left hxX, h⟩)
  have hxΩ : x ∈ Ω₀ := ⟨le_conjClosure X D hxX, by rw [hx3]; exact B₀.one_mem⟩
  have hlt : B₀ < B₀ ⊔ Ω₀ :=
    lt_of_le_of_ne le_sup_left fun h => hxB (h ▸ Subgroup.mem_sup_right hxΩ)
  have hNN : X ⊔ T ⊔ D ≤ Subgroup.normalizer ((B₀ ⊔ Ω₀ : Subgroup G) : Set G) := fun g hg =>
    ChiefCount.mem_normalizer_sup (hB.nor hg) (hΩN hg)
  have hYN := (H.X_le_of_normal hNN (hB.max _ hlt (sup_le hB.le fun y hy => hYB hy.1) hNN)).2
  have hY3 : ∀ y ∈ Y, y ^ 3 ∈ B₀ := by
    intro y hy
    obtain ⟨b, hb, w, hw, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hΩB).mp (hYN hy)
    have hbY : b ∈ Y := by
      have := Y.mul_mem hy (Y.inv_mem hw.1)
      rwa [mul_inv_cancel_right] at this
    exact hcube hbY hw.1 (B₀.pow_mem hb 3) hw.2
  refine ⟨hY3, fun r ⟨hrX, hrR⟩ => ?_⟩
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (X ⊔ T)) ⟨r, hrR⟩
  have hk' : r ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  exact Lem3328.mem_of_pow_odd (by decide : Odd 3) (hY3 r (le_conjClosure X D hrX)) (e := k)
    (by rw [hk']; exact B₀.one_mem)

theorem sq_comm_mem (hB : IsB₀ X T D B₀) (habel : ⁅conjClosure X D, conjClosure X D⁆ ≤ B₀) :
    (∀ t ∈ T, t * t ∈ B₀) ∧ ∀ t ∈ T, ∀ t' ∈ T, ⁅t, t'⁆ ∈ B₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := conjClosure X D with hY
  set B := X ⊔ T ⊔ D with hBdef
  have hXB : X ≤ B := le_sup_left.trans le_sup_left
  have hTB : T ≤ B := le_sup_right.trans le_sup_left
  have hDB : D ≤ B := le_sup_right
  have hN : (B₀.subgroupOf B).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hB.nor
  set π := QuotientGroup.mk' (B₀.subgroupOf B) with hπ
  have hι1 : ∀ {g : G} (hg : g ∈ B), π ⟨g, hg⟩ = 1 ↔ g ∈ B₀ := fun hg => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  obtain ⟨hY3, hXR⟩ := H.cube_mem hB habel
  obtain ⟨x, hxX, hx3, hxR, hgen⟩ := H.exists_x
  have hxB : x ∉ B₀ := fun h => hxR (hB.inf ⟨Subgroup.mem_sup_left hxX, h⟩)
  have hgenB : ∀ x' (hx' : x' ∈ X), ∃ j : ℕ, π ⟨x', hXB hx'⟩ = π ⟨x, hXB hxX⟩ ^ j := by
    intro x' hx'
    obtain ⟨j, hj⟩ := hgen x' hx'
    refine ⟨j, ?_⟩
    have h1 : x' * (x ^ j)⁻¹ ∈ B₀ := hXR ⟨X.mul_mem hx' (X.inv_mem (X.pow_mem hxX j)), hj⟩
    have hmem : x' * (x ^ j)⁻¹ ∈ B := B.mul_mem (hXB hx') (B.inv_mem (B.pow_mem (hXB hxX) j))
    rw [← mul_inv_eq_one, ← map_pow, ← map_inv, ← map_mul]
    exact (hι1 hmem).mpr h1
  set a := π ⟨x, hXB hxX⟩ with ha
  have ha3 : a ^ 3 = 1 := by
    rw [ha, ← map_pow]
    exact (hι1 _).mpr (by simp [hx3, B₀.one_mem])
  have ha1 : a ≠ 1 := fun h => hxB ((hι1 _).mp h)
  have hact : ∀ t (ht : t ∈ T) d (hd : d ∈ D), ∃ j : ℕ, j % 3 ≠ 0 ∧
      π ⟨t, hTB ht⟩ * (π ⟨d, hDB hd⟩ * a * (π ⟨d, hDB hd⟩)⁻¹) * (π ⟨t, hTB ht⟩)⁻¹ =
        (π ⟨d, hDB hd⟩ * a * (π ⟨d, hDB hd⟩)⁻¹) ^ j := by
    intro t ht d hd
    have ht' : d⁻¹ * t * d⁻¹⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (H.h.DN (D.inv_mem hd)) t).mp ht
    have hx'' : (d⁻¹ * t * d⁻¹⁻¹) * x * (d⁻¹ * t * d⁻¹⁻¹)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (H.hTX ht') x).mp hxX
    obtain ⟨j, hj⟩ := hgenB _ hx''
    have e1 : π ⟨t, hTB ht⟩ * (π ⟨d, hDB hd⟩ * a * (π ⟨d, hDB hd⟩)⁻¹) * (π ⟨t, hTB ht⟩)⁻¹ =
        π ⟨d, hDB hd⟩ * π ⟨_, hXB hx''⟩ * (π ⟨d, hDB hd⟩)⁻¹ := by
      simp only [ha, ← map_mul, ← map_inv]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hpow : π ⟨t, hTB ht⟩ * (π ⟨d, hDB hd⟩ * a * (π ⟨d, hDB hd⟩)⁻¹) * (π ⟨t, hTB ht⟩)⁻¹ =
        (π ⟨d, hDB hd⟩ * a * (π ⟨d, hDB hd⟩)⁻¹) ^ j := by
      rw [e1, hj, conj_pow]
    refine ⟨j, fun hj0 => ha1 ?_, hpow⟩
    have hb3 : (π ⟨d, hDB hd⟩ * a * (π ⟨d, hDB hd⟩)⁻¹) ^ 3 = 1 := by
      rw [conj_pow, ha3, mul_one, mul_inv_cancel]
    have h0 : (π ⟨d, hDB hd⟩ * a * (π ⟨d, hDB hd⟩)⁻¹) ^ j = 1 := by
      rw [pow_eq_pow_mod j hb3, hj0, pow_zero]
    rw [← hpow] at h0
    have h1 : π ⟨d, hDB hd⟩ * a * (π ⟨d, hDB hd⟩)⁻¹ = 1 := by
      have := congrArg (fun q => (π ⟨t, hTB ht⟩)⁻¹ * q * π ⟨t, hTB ht⟩) h0
      simpa [mul_assoc] using this
    have := congrArg (fun q => (π ⟨d, hDB hd⟩)⁻¹ * q * π ⟨d, hDB hd⟩) h1
    simpa [mul_assoc] using this
  have hsq : ∀ t ∈ T, t * t ∈ B₀ := by
    intro t ht
    have httB : t * t ∈ B := B.mul_mem (hTB ht) (hTB ht)
    let C : Subgroup G := ((Subgroup.centralizer {π ⟨t * t, httB⟩}).comap π).map B.subtype
    have hYC : Y ≤ C := by
      refine conjClosure_le fun d hd x' hx' => ?_
      have hy : d * x' * d⁻¹ ∈ B := B.mul_mem (B.mul_mem (hDB hd) (hXB hx')) (B.inv_mem (hDB hd))
      refine ⟨⟨_, hy⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨k, hk⟩ := hgenB x' hx'
      obtain ⟨j, hj0, hj⟩ := hact t ht d hd
      have e2 : π ⟨d * x' * d⁻¹, hy⟩ = (π ⟨d, hDB hd⟩ * a * (π ⟨d, hDB hd⟩)⁻¹) ^ k := by
        rw [conj_pow, ← hk]
        simp only [← map_mul, ← map_inv]
        rfl
      have e3 : π ⟨t * t, httB⟩ = π ⟨t, hTB ht⟩ * π ⟨t, hTB ht⟩ := by rw [← map_mul]; rfl
      have hb3 : (π ⟨d, hDB hd⟩ * a * (π ⟨d, hDB hd⟩)⁻¹) ^ 3 = 1 := by
        rw [conj_pow, ha3, mul_one, mul_inv_cancel]
      have hτb := conj_sq_of_pow hb3 hj0 hj
      have h2 : π ⟨t, hTB ht⟩ * π ⟨t, hTB ht⟩ *
          (π ⟨d, hDB hd⟩ * a * (π ⟨d, hDB hd⟩)⁻¹) ^ k *
            (π ⟨t, hTB ht⟩ * π ⟨t, hTB ht⟩)⁻¹ =
          (π ⟨d, hDB hd⟩ * a * (π ⟨d, hDB hd⟩)⁻¹) ^ k := by
        rw [← conj_pow, hτb]
      rw [e2, e3]
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    refine H.faithful hB.le hB.nor hB.inf hB.max (T.mul_mem ht ht) fun y hy => ?_
    obtain ⟨y', hy', rfl⟩ := hYC hy
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hy'
    have hc1 : π ⁅(⟨t * t, httB⟩ : ↥B), y'⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hy'.symm
    exact (hι1 (⁅(⟨t * t, httB⟩ : ↥B), y'⁆).2).mp hc1
  refine ⟨hsq, fun t ht t' ht' => ?_⟩
  have hinv : ∀ {g : G} (hg : g ∈ T), π ⟨g, hTB hg⟩ * π ⟨g, hTB hg⟩ = 1 := fun hg => by
    rw [← map_mul]
    exact (hι1 (B.mul_mem (hTB hg) (hTB hg))).mpr (hsq _ hg)
  have h1 := hinv (T.mul_mem ht ht')
  have e1 : (⟨t * t', hTB (T.mul_mem ht ht')⟩ : ↥B) = ⟨t, hTB ht⟩ * ⟨t', hTB ht'⟩ := rfl
  rw [e1, map_mul] at h1
  have hc : π ⟨t, hTB ht⟩ * π ⟨t', hTB ht'⟩ = π ⟨t', hTB ht'⟩ * π ⟨t, hTB ht⟩ :=
    comm_of_sq (hinv ht) (hinv ht') h1
  have hc1 : π ⁅(⟨t, hTB ht⟩ : ↥B), ⟨t', hTB ht'⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc
  exact (hι1 (⁅(⟨t, hTB ht⟩ : ↥B), (⟨t', hTB ht'⟩ : ↥B)⁆).2).mp hc1

theorem four_le_index (hB : IsB₀ X T D B₀) : 4 ≤ (T ⊓ B₀).relIndex T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hT₀, hlt⟩ := H.T₀_eq hB.le hB.nor hB.inf hB.max
  obtain ⟨e⟩ := H.hS3
  have h3 : T.relIndex (X ⊔ T) = 3 := Lem3320.relIndex_eq_three_of_iso H.isSylowTwoOf_XT e
  have hpc : CFSG.pCore 2 ↥(X ⊔ T) = (pCoreOf 2 (X ⊔ T)).subgroupOf (X ⊔ T) := by
    ext y
    rw [Lem3328.mem_pCore_iff, Subgroup.mem_subgroupOf]
  have h6 : (pCoreOf 2 (X ⊔ T)).relIndex (X ⊔ T) = 6 := by
    rw [Subgroup.relIndex, ← hpc, Subgroup.index_eq_card, Nat.card_congr e.toEquiv,
      Nat.card_perm, Nat.card_fin]
    rfl
  have hRT := H.R_le_T
  have h2 : (pCoreOf 2 (X ⊔ T)).relIndex T = 2 := by
    have := Subgroup.relIndex_mul_relIndex (pCoreOf 2 (X ⊔ T)) T (X ⊔ T) hRT le_sup_right
    rw [h3, h6] at this
    omega
  have hT₀R : T ⊓ B₀ ≤ pCoreOf 2 (X ⊔ T) := hT₀ ▸ hlt.le
  have hge : 2 ≤ (T ⊓ B₀).relIndex (pCoreOf 2 (X ⊔ T)) := by
    have h0 : (T ⊓ B₀).relIndex (pCoreOf 2 (X ⊔ T)) ≠ 0 :=
      show ((T ⊓ B₀).subgroupOf (pCoreOf 2 (X ⊔ T))).index ≠ 0 from
        Subgroup.index_ne_zero_of_finite
    have h1 : (T ⊓ B₀).relIndex (pCoreOf 2 (X ⊔ T)) ≠ 1 := fun h => by
      rw [Subgroup.relIndex_eq_one] at h
      rw [← hT₀] at hlt
      exact hlt.not_ge h
    omega
  have := Subgroup.relIndex_mul_relIndex (T ⊓ B₀) (pCoreOf 2 (X ⊔ T)) T hT₀R hRT
  rw [h2] at this
  omega

end Hyp3320

end S3320

end CFSG.Quasithin.H13
