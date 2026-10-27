module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324Main
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323One

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3
open scoped commutatorElement

namespace S3320

variable {G : Type} [Group G] [Finite G]

theorem perm3_check : ∀ κ σ : Equiv.Perm (Fin 3), κ ≠ 1 → Equiv.Perm.sign σ = 1 →
    ∃ g h : Equiv.Perm (Fin 3), σ = (g * κ * g⁻¹) * (h * κ * h⁻¹) := by
  decide

theorem perm3_cycle : ∃ σ : Equiv.Perm (Fin 3), σ ≠ 1 ∧ σ ^ 3 = 1 := by
  decide

omit [Finite G] in
theorem pow_mul_mem {N : Subgroup G} {c r : G} (hc : c ∈ N)
    (hr : r ∈ Subgroup.normalizer (N : Set G)) (n : ℕ) : ∃ c' ∈ N, (c * r) ^ n = c' * r ^ n := by
  induction n with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨c', hc', e⟩ := ih
    have hrn : r ^ n ∈ Subgroup.normalizer (N : Set G) := Subgroup.pow_mem _ hr n
    refine ⟨c' * (r ^ n * c * (r ^ n)⁻¹), N.mul_mem hc'
      ((Subgroup.mem_normalizer_iff.mp hrn c).mp hc), ?_⟩
    rw [pow_succ, e]
    group

omit [Finite G] in
theorem le_of_le_sup_pgroup {X N S : Subgroup G} (hXX : oTwoUpper X = X)
    (hSN : S ≤ Subgroup.normalizer (N : Set G)) (hS2 : IsPGroup 2 S) (hXNS : X ≤ N ⊔ S) :
    X ≤ N := by
  rw [← hXX, oTwoUpper, Subgroup.closure_le]
  rintro x ⟨hxX, hxo⟩
  obtain ⟨c, hc, r, hr, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hSN).mp (hXNS hxX)
  obtain ⟨k, hk⟩ := hS2 ⟨r, hr⟩
  have hk' : r ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨c', hc', ec⟩ := pow_mul_mem hc (hSN hr) (2 ^ k)
  refine Lem3328.mem_of_pow_odd hxo (by rw [pow_orderOf_eq_one]; exact N.one_mem) (e := k) ?_
  rw [ec, hk', mul_one]
  exact hc'

omit [Finite G] in
theorem sign_eq_one {P X : Subgroup G} (hXP : X ≤ P) (hXX : oTwoUpper X = X)
    (ψ : ↥P →* Equiv.Perm (Fin 3)) (x : G) (hx : x ∈ X) :
    Equiv.Perm.sign (ψ ⟨x, hXP hx⟩) = 1 := by
  have key : ∀ y ∈ oTwoUpper X, ∀ hy : y ∈ X, Equiv.Perm.sign (ψ ⟨y, hXP hy⟩) = 1 := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
      intro _
      apply One3323.sign_eq_one_of_odd
      refine Odd.of_dvd_nat ?_ (orderOf_map_dvd ψ _)
      rw [Subgroup.orderOf_mk]
      exact hz.2
    | one =>
      intro _
      show Equiv.Perm.sign (ψ 1) = 1
      rw [map_one, map_one]
    | mul y z hy hz ihy ihz =>
      intro hyz
      have hy' : y ∈ X := oTwoUpper_le X hy
      have hz' : z ∈ X := oTwoUpper_le X hz
      have e1 : (⟨y * z, hXP hyz⟩ : ↥P) = ⟨y, hXP hy'⟩ * ⟨z, hXP hz'⟩ := rfl
      rw [e1, map_mul, map_mul, ihy hy', ihz hz', mul_one]
    | inv y hy ihy =>
      intro hy''
      have hy' : y ∈ X := oTwoUpper_le X hy
      have e1 : (⟨y⁻¹, hXP hy''⟩ : ↥P) = (⟨y, hXP hy'⟩ : ↥P)⁻¹ := rfl
      rw [e1, map_inv, map_inv, ihy hy', inv_one]
  exact key x (by rw [hXX]; exact hx) hx

structure Hyp3320 (G : Type) [Group G] [Finite G] (T M L D X : Subgroup G) : Prop where
  h : Hyp331 G T M L D
  hXX : oTwoUpper X = X
  hTX : T ≤ Subgroup.normalizer (X : Set G)
  hS3 : Nonempty (↥(X ⊔ T) ⧸ CFSG.pCore 2 ↥(X ⊔ T) ≃* Equiv.Perm (Fin 3))
  hD : ¬ D ≤ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G)
  hB : InH T (X ⊔ T ⊔ D)
  hBY : X ⊔ T ⊔ D ≤ Subgroup.normalizer (conjClosure X D : Set G)
  hBeq : X ⊔ T ⊔ D = conjClosure X D ⊔ T ⊔ D

namespace Hyp3320

variable {T M L D X : Subgroup G} (H : Hyp3320 G T M L D X)

include H

theorem isSylowTwoOf_XT : IsSylowTwoOf T (X ⊔ T) :=
  ⟨le_sup_right, H.h.sylow.1, fun h2 => H.h.sylow.2
    (h2.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩

theorem isSylowTwoOf_B : IsSylowTwoOf T (X ⊔ T ⊔ D) :=
  ⟨le_sup_right.trans le_sup_left, H.h.sylow.1, fun h2 => H.h.sylow.2
    (h2.trans (Subgroup.relIndex_dvd_index_of_le (le_sup_right.trans le_sup_left)))⟩

theorem R_le_T : pCoreOf 2 (X ⊔ T) ≤ T :=
  EscapingLocal.pCoreOf_le_of_isSylowTwoOf H.isSylowTwoOf_XT

theorem pCoreOf_le_R : pCoreOf 2 (X ⊔ T ⊔ D) ≤ pCoreOf 2 (X ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOT : pCoreOf 2 (X ⊔ T ⊔ D) ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf H.isSylowTwoOf_B
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hOT.trans le_sup_right)
    (le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

omit H in
theorem exists_B₀ : ∃ B₀ : Subgroup G, B₀ ≤ X ⊔ T ⊔ D ∧
    X ⊔ T ⊔ D ≤ Subgroup.normalizer (B₀ : Set G) ∧ (X ⊔ T) ⊓ B₀ ≤ pCoreOf 2 (X ⊔ T) ∧
    ∀ N : Subgroup G, B₀ < N → N ≤ X ⊔ T ⊔ D → X ⊔ T ⊔ D ≤ Subgroup.normalizer (N : Set G) →
      ¬ (X ⊔ T) ⊓ N ≤ pCoreOf 2 (X ⊔ T) := by
  classical
  let S : Set (Subgroup G) := {N | N ≤ X ⊔ T ⊔ D ∧
    X ⊔ T ⊔ D ≤ Subgroup.normalizer (N : Set G) ∧ (X ⊔ T) ⊓ N ≤ pCoreOf 2 (X ⊔ T)}
  have hbot : (⊥ : Subgroup G) ∈ S := ⟨bot_le, fun x _ => Subgroup.mem_normalizer_iff.mpr
    fun y => by simp, by rw [inf_bot_eq]; exact bot_le⟩
  have hS : S.toFinite.toFinset.Nonempty := ⟨⊥, by simpa using hbot⟩
  obtain ⟨B₀, hB, hmax⟩ := S.toFinite.toFinset.exists_max_image (fun N => Nat.card N) hS
  rw [Set.Finite.mem_toFinset] at hB
  refine ⟨B₀, hB.1, hB.2.1, hB.2.2, fun N hlt hNB hBN hNR => ?_⟩
  have h1 := hmax N (by rw [Set.Finite.mem_toFinset]; exact ⟨hNB, hBN, hNR⟩)
  have h2 : Nat.card B₀ < Nat.card N := Subgroup.card_lt_of_lt hlt
  omega

theorem T₀_eq {B₀ : Subgroup G} (hB₀B : B₀ ≤ X ⊔ T ⊔ D)
    (hBB₀ : X ⊔ T ⊔ D ≤ Subgroup.normalizer (B₀ : Set G))
    (hR : (X ⊔ T) ⊓ B₀ ≤ pCoreOf 2 (X ⊔ T))
    (hmax : ∀ N : Subgroup G, B₀ < N → N ≤ X ⊔ T ⊔ D →
      X ⊔ T ⊔ D ≤ Subgroup.normalizer (N : Set G) → ¬ (X ⊔ T) ⊓ N ≤ pCoreOf 2 (X ⊔ T)) :
    (X ⊔ T) ⊓ B₀ = T ⊓ B₀ ∧ T ⊓ B₀ = pCoreOf 2 (X ⊔ T ⊔ D) ∧
      pCoreOf 2 (X ⊔ T ⊔ D) < pCoreOf 2 (X ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRT := H.R_le_T
  have hOT : pCoreOf 2 (X ⊔ T ⊔ D) ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf H.isSylowTwoOf_B
  have hON : X ⊔ T ⊔ D ≤ Subgroup.normalizer (pCoreOf 2 (X ⊔ T ⊔ D) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have h1 : (X ⊔ T) ⊓ B₀ = T ⊓ B₀ :=
    le_antisymm (le_inf (hR.trans hRT) inf_le_right) (inf_le_inf_right _ le_sup_right)
  have hO : pCoreOf 2 (X ⊔ T ⊔ D) ≤ B₀ := by
    by_contra hcon
    have hlt : B₀ < pCoreOf 2 (X ⊔ T ⊔ D) ⊔ B₀ :=
      lt_of_le_of_ne le_sup_right fun h => hcon (le_sup_left.trans h.symm.le)
    refine hmax _ hlt (sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hB₀B)
      (fun b hb => ChiefCount.mem_normalizer_sup (hON hb) (hBB₀ hb)) ?_
    calc (X ⊔ T) ⊓ (pCoreOf 2 (X ⊔ T ⊔ D) ⊔ B₀)
        ≤ pCoreOf 2 (X ⊔ T ⊔ D) ⊔ (X ⊔ T) ⊓ B₀ :=
          ChiefCount.inf_sup_le (hOT.trans le_sup_right)
            (fun o ho => hBB₀ (CFSG.LieType.BorelTits.pCoreOf_le 2 _ ho))
      _ ≤ pCoreOf 2 (X ⊔ T) := sup_le H.pCoreOf_le_R hR
  have hTB₀ : T ⊓ B₀ ≤ pCoreOf 2 (X ⊔ T ⊔ D) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (inf_le_left.trans (le_sup_right.trans le_sup_left)) ?_ (H.h.sylow.1.to_le inf_le_left)
    rw [← h1]
    refine sup_le (fun x hx => ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer hx)
      (hBB₀ (Subgroup.mem_sup_left hx))) fun d hd => ?_
    rw [h1]
    exact ChiefCount.mem_normalizer_inf (H.h.DN hd) (hBB₀ (Subgroup.mem_sup_right hd))
  refine ⟨h1, le_antisymm hTB₀ (le_inf hOT hO), lt_of_le_of_ne H.pCoreOf_le_R fun heq => ?_⟩
  apply H.hD
  rw [← heq]
  exact le_sup_right.trans hON

theorem X_le_of_normal {N : Subgroup G}
    (hBN : X ⊔ T ⊔ D ≤ Subgroup.normalizer (N : Set G))
    (hNR : ¬ (X ⊔ T) ⊓ N ≤ pCoreOf 2 (X ⊔ T)) : X ≤ N ∧ conjClosure X D ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := H.hS3
  set ψ : ↥(X ⊔ T) →* Equiv.Perm (Fin 3) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥(X ⊔ T))) with hψ
  have hψs : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψk : ∀ y : ↥(X ⊔ T), ψ y = 1 → (y : G) ∈ pCoreOf 2 (X ⊔ T) := by
    intro y hy
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥(X ⊔ T)) y = 1 :=
      (map_eq_one_iff e.toMonoidHom e.injective).mp hy
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact (Lem3328.mem_pCore_iff _).mp h2
  obtain ⟨a, ⟨haXT, haN⟩, haR⟩ := Set.not_subset.mp hNR
  have hκ : ψ ⟨a, haXT⟩ ≠ 1 := fun h1 => haR (hψk _ h1)
  have hRN : pCoreOf 2 (X ⊔ T) ≤ Subgroup.normalizer (N : Set G) := fun r hr =>
    hBN ((le_sup_left : X ⊔ T ≤ X ⊔ T ⊔ D) (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hr))
  have hXNR : X ≤ N ⊔ pCoreOf 2 (X ⊔ T) := by
    intro x hxX
    have hxXT : x ∈ X ⊔ T := Subgroup.mem_sup_left hxX
    obtain ⟨g, h, hgh⟩ := perm3_check _ _ hκ (sign_eq_one le_sup_left H.hXX ψ x hxX)
    obtain ⟨g', rfl⟩ := hψs g
    obtain ⟨h', rfl⟩ := hψs h
    set c : ↥(X ⊔ T) := g' * ⟨a, haXT⟩ * g'⁻¹ * (h' * ⟨a, haXT⟩ * h'⁻¹) with hc
    have hcN : (c : G) ∈ N := by
      have hconj : ∀ k : ↥(X ⊔ T), ((k * ⟨a, haXT⟩ * k⁻¹ : ↥(X ⊔ T)) : G) ∈ N := fun k =>
        (Subgroup.mem_normalizer_iff.mp (hBN (Subgroup.mem_sup_left k.2)) a).mp haN
      exact N.mul_mem (hconj g') (hconj h')
    have hr : ((c⁻¹ * ⟨x, hxXT⟩ : ↥(X ⊔ T)) : G) ∈ pCoreOf 2 (X ⊔ T) := by
      apply hψk
      rw [map_mul, map_inv, hgh, hc]
      simp only [map_mul, map_inv, inv_mul_cancel]
    have hxcr : x = (c : G) * ((c⁻¹ * ⟨x, hxXT⟩ : ↥(X ⊔ T)) : G) := by simp
    rw [hxcr]
    exact Subgroup.mul_mem_sup hcN hr
  have hXN : X ≤ N := le_of_le_sup_pgroup H.hXX hRN
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)) hXNR
  refine ⟨hXN, conjClosure_le fun d hd x hx => ?_⟩
  exact (Subgroup.mem_normalizer_iff.mp (hBN (Subgroup.mem_sup_right hd)) x).mp (hXN hx)

theorem not_X_le_R : ¬ X ≤ pCoreOf 2 (X ⊔ T) := by
  intro hXR
  obtain ⟨e⟩ := H.hS3
  set ψ : ↥(X ⊔ T) →* Equiv.Perm (Fin 3) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥(X ⊔ T))) with hψ
  have hψs : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψR : ∀ y : ↥(X ⊔ T), (y : G) ∈ pCoreOf 2 (X ⊔ T) → ψ y = 1 := by
    intro y hy
    show e (QuotientGroup.mk' (CFSG.pCore 2 ↥(X ⊔ T)) y) = 1
    rw [QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff y).mpr ((Lem3328.mem_pCore_iff y).mpr hy), map_one]
  obtain ⟨σ, hσ1, hσ3⟩ := perm3_cycle
  obtain ⟨y, rfl⟩ := hψs σ
  obtain ⟨x, hx, t, ht, hxt⟩ := (B19Aux.mem_sup_iff_of_le_normalizer H.hTX).mp y.2
  have hy : y = ⟨x, Subgroup.mem_sup_left hx⟩ * ⟨t, Subgroup.mem_sup_right ht⟩ :=
    Subtype.ext (by rw [Subgroup.coe_mul]; exact hxt)
  have hψt : ψ y = ψ ⟨t, Subgroup.mem_sup_right ht⟩ := by
    rw [hy, map_mul, hψR _ (hXR hx), one_mul]
  obtain ⟨k, hk⟩ := H.h.sylow.1 ⟨t, ht⟩
  have hk' : ψ ⟨t, Subgroup.mem_sup_right ht⟩ ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨t, Subgroup.mem_sup_right ht⟩ : ↥(X ⊔ T)) ^ 2 ^ k = 1 := Subtype.ext (by
      have := congrArg Subtype.val hk
      simpa using this)
    rw [this, map_one]
  rw [← hψt] at hk'
  have h1 := pow_gcd_eq_one.mpr ⟨hσ3, hk'⟩
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num)), pow_one] at h1
  exact hσ1 h1

theorem not_X_le_B₀ {B₀ : Subgroup G} (hR : (X ⊔ T) ⊓ B₀ ≤ pCoreOf 2 (X ⊔ T)) : ¬ X ≤ B₀ :=
  fun hXB => H.not_X_le_R fun _ hx => hR ⟨Subgroup.mem_sup_left hx, hXB hx⟩

theorem not_R_le_B₀ {B₀ : Subgroup G} (hT₀ : T ⊓ B₀ = pCoreOf 2 (X ⊔ T ⊔ D))
    (hlt : pCoreOf 2 (X ⊔ T ⊔ D) < pCoreOf 2 (X ⊔ T)) : ¬ pCoreOf 2 (X ⊔ T) ≤ B₀ := by
  intro hRB
  rw [← hT₀] at hlt
  exact hlt.not_ge (le_inf H.R_le_T hRB)

theorem faithful {B₀ : Subgroup G} (hB₀B : B₀ ≤ X ⊔ T ⊔ D)
    (hBB₀ : X ⊔ T ⊔ D ≤ Subgroup.normalizer (B₀ : Set G))
    (hR : (X ⊔ T) ⊓ B₀ ≤ pCoreOf 2 (X ⊔ T))
    (hmax : ∀ N : Subgroup G, B₀ < N → N ≤ X ⊔ T ⊔ D →
      X ⊔ T ⊔ D ≤ Subgroup.normalizer (N : Set G) → ¬ (X ⊔ T) ⊓ N ≤ pCoreOf 2 (X ⊔ T))
    {t : G} (ht : t ∈ T) (htY : ∀ y ∈ conjClosure X D, ⁅t, y⁆ ∈ B₀) : t ∈ B₀ := by
  set Y := conjClosure X D with hY
  have hTB : T ≤ X ⊔ T ⊔ D := le_sup_right.trans le_sup_left
  have hconjB₀ : ∀ {g : G}, g ∈ X ⊔ T ⊔ D → ∀ {b : G}, b ∈ B₀ → g * b * g⁻¹ ∈ B₀ :=
    fun hg b hb => (Subgroup.mem_normalizer_iff.mp (hBB₀ hg) b).mp hb
  let S : Subgroup G :=
    { carrier := {s | s ∈ T ∧ ∀ y ∈ Y, ⁅s, y⁆ ∈ B₀}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨T.mul_mem ha hb, fun y hy => ?_⟩
        have e : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact B₀.mul_mem (hconjB₀ (hTB ha) (hb' y hy)) (ha' y hy)
      one_mem' := ⟨T.one_mem, fun y _ => by rw [commutatorElement_one_left]; exact B₀.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨T.inv_mem ha, fun y hy => ?_⟩
        have e : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact hconjB₀ (hTB (T.inv_mem ha)) (B₀.inv_mem (ha' y hy)) }
  have hST : S ≤ T := fun s hs => hs.1
  have hSN : S ≤ Subgroup.normalizer (B₀ : Set G) := fun s hs => hBB₀ (hTB hs.1)
  have hYN : X ⊔ T ⊔ D ≤ Subgroup.normalizer (Y : Set G) := H.hBY
  have hconjS : ∀ g ∈ T ⊔ D, ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
    intro g hg s hs
    have hgB : g ∈ X ⊔ T ⊔ D := by
      rw [sup_assoc]
      exact Subgroup.mem_sup_right hg
    have hgT : g ∈ Subgroup.normalizer (T : Set G) :=
      sup_le Subgroup.le_normalizer H.h.DN hg
    refine ⟨(Subgroup.mem_normalizer_iff.mp hgT s).mp hs.1, fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hYN ((X ⊔ T ⊔ D).inv_mem hgB)) y).mp hy
    have e : ⁅g * s * g⁻¹, y⁆ = g * ⁅s, g⁻¹ * y * g⁻¹⁻¹⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hconjB₀ hgB (hs.2 _ hy')
  have hconjN : ∀ g ∈ X ⊔ T ⊔ D, (∀ s ∈ S, g * s * g⁻¹ ∈ B₀ ⊔ S) →
      ∀ n ∈ B₀ ⊔ S, g * n * g⁻¹ ∈ B₀ ⊔ S := by
    intro g hg hgS n hn
    obtain ⟨b, hb, s, hs, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hSN).mp hn
    have e : g * (b * s) * g⁻¹ = (g * b * g⁻¹) * (g * s * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hconjB₀ hg hb)) (hgS s hs)
  have hXn : X ≤ Subgroup.normalizer ((B₀ ⊔ S : Subgroup G) : Set G) :=
    Main3324.le_normalizer_of_conj fun x hx => hconjN x (Subgroup.mem_sup_left
      (Subgroup.mem_sup_left hx)) fun s hs => by
        have hc : ⁅s, x⁆ ∈ B₀ := hs.2 x (le_conjClosure X D hx)
        have e : x * s * x⁻¹ = ⁅s, x⁆⁻¹ * s := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (B₀.inv_mem hc))
          (Subgroup.mem_sup_right hs)
  have hTDB : T ⊔ D ≤ X ⊔ T ⊔ D := by
    rw [sup_assoc]
    exact le_sup_right
  have hTDn : T ⊔ D ≤ Subgroup.normalizer ((B₀ ⊔ S : Subgroup G) : Set G) :=
    Main3324.le_normalizer_of_conj fun g hg => hconjN g (hTDB hg) fun s hs =>
      Subgroup.mem_sup_right (hconjS g hg s hs)
  have hNn : X ⊔ T ⊔ D ≤ Subgroup.normalizer ((B₀ ⊔ S : Subgroup G) : Set G) := by
    rw [sup_assoc]
    exact sup_le hXn hTDn
  by_contra ht0
  have htS : t ∈ S := ⟨ht, htY⟩
  have hlt : B₀ < B₀ ⊔ S :=
    lt_of_le_of_ne le_sup_left fun h => ht0 (h ▸ Subgroup.mem_sup_right htS)
  have hNR := hmax _ hlt (sup_le hB₀B (hST.trans hTB)) hNn
  have hXN := (H.X_le_of_normal hNn hNR).1
  exact H.not_X_le_B₀ hR (le_of_le_sup_pgroup H.hXX hSN (H.h.sylow.1.to_le hST) hXN)

end Hyp3320

end S3320

end CFSG.Quasithin.H13
