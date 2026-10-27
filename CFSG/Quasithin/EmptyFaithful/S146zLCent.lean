module

public import CFSG.Quasithin.EmptyFaithful.S146zLRot

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

section CommSub

variable {G : Type} [Group G]

@[expose] def zrCommSub (H Q : Subgroup G) (hQ : H ≤ Subgroup.normalizer (Q : Set G)) (x : G) :
    Subgroup G where
  carrier := {y | y ∈ H ∧ x * y * x⁻¹ * y⁻¹ ∈ Q}
  mul_mem' := by
    rintro y z ⟨hyH, hy⟩ ⟨hzH, hz⟩
    refine ⟨H.mul_mem hyH hzH, ?_⟩
    have e : x * (y * z) * x⁻¹ * (y * z)⁻¹ =
        (x * y * x⁻¹ * y⁻¹) * (y * (x * z * x⁻¹ * z⁻¹) * y⁻¹) := by group
    rw [e]
    exact Q.mul_mem hy ((Subgroup.mem_normalizer_iff.mp (hQ hyH) _).mp hz)
  one_mem' := ⟨H.one_mem, by simp⟩
  inv_mem' := by
    rintro y ⟨hyH, hy⟩
    refine ⟨H.inv_mem hyH, ?_⟩
    have e : x * y⁻¹ * x⁻¹ * y⁻¹⁻¹ = y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y := by group
    rw [e]
    have h1 := (Subgroup.mem_normalizer_iff.mp (hQ (H.inv_mem hyH)) _).mp (Q.inv_mem hy)
    simpa using h1

@[expose] def zrCentSub (H Q S : Subgroup G) (hQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hS : H ≤ Subgroup.normalizer (S : Set G)) : Subgroup G where
  carrier := {z | z ∈ H ∧ ∀ y ∈ S, z * y * z⁻¹ * y⁻¹ ∈ Q}
  mul_mem' := by
    rintro z₁ z₂ ⟨hz₁, h₁⟩ ⟨hz₂, h₂⟩
    refine ⟨H.mul_mem hz₁ hz₂, fun y hy => ?_⟩
    have e : z₁ * z₂ * y * (z₁ * z₂)⁻¹ * y⁻¹ =
        (z₁ * (z₂ * y * z₂⁻¹ * y⁻¹) * z₁⁻¹) * (z₁ * y * z₁⁻¹ * y⁻¹) := by group
    rw [e]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hQ hz₁) _).mp (h₂ y hy)) (h₁ y hy)
  one_mem' := ⟨H.one_mem, fun y _ => by simp⟩
  inv_mem' := by
    rintro z ⟨hz, h⟩
    refine ⟨H.inv_mem hz, fun y hy => ?_⟩
    have hy' : z⁻¹ * y * z⁻¹⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp (hS (H.inv_mem hz)) y).mp hy
    have h1 := h _ hy'
    have e : z⁻¹ * y * z⁻¹⁻¹ * y⁻¹ = (z * (z⁻¹ * y * z⁻¹⁻¹) * z⁻¹ * (z⁻¹ * y * z⁻¹⁻¹)⁻¹)⁻¹ := by group
    rw [e]
    exact Q.inv_mem h1

end CommSub

section Cent

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.centralizes_pq_of_gens (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t) (φ₁ : ↥H₁ →* DihedralGroup p)
    (hker₁ : ∀ y : ↥H₁, φ₁ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a₁ : ↥H₁}
    (ha₁ : φ₁ a₁ = DihedralGroup.r 1) (φ₂ : ↥H₂ →* DihedralGroup p)
    (hker₂ : ∀ y : ↥H₂, φ₂ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a₂ : ↥H₂}
    (ha₂ : φ₂ a₂ = DihedralGroup.r 1) :
    (∀ x ∈ H, x * (a₁ : G) * x⁻¹ * (a₁ : G)⁻¹ ∈ pCoreOf 2 H →
      x * (a₂ : G) * x⁻¹ * (a₂ : G)⁻¹ ∈ pCoreOf 2 H →
        ∀ y ∈ PQ, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H) ∧
    (∀ y ∈ PQ, (a₁ : G) * y * (a₁ : G)⁻¹ * y⁻¹ ∈ pCoreOf 2 H ∧
      (a₂ : G) * y * (a₂ : G)⁻¹ * y⁻¹ ∈ pCoreOf 2 H) := by
  have hQ : H ≤ Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) := le_normalizer_pCoreOf 2 H
  have hpq := h.pq_le_rot S hred φ₁ hker₁ ha₁ φ₂ hker₂ ha₂
  have ha₁H : (a₁ : G) ∈ H := h.le (h.le₁ a₁.2)
  have ha₂H : (a₂ : G) ∈ H := h.le (h.le₂ a₂.2)
  have hQc : ∀ x ∈ H, ∀ q ∈ pCoreOf 2 H, x * q * x⁻¹ * q⁻¹ ∈ pCoreOf 2 H := fun x hx q hq =>
    (pCoreOf 2 H).mul_mem ((Subgroup.mem_normalizer_iff.mp (hQ hx) q).mp hq)
      ((pCoreOf 2 H).inv_mem hq)
  have hcomm : (a₁ : G) * (a₂ : G) * (a₁ : G)⁻¹ * (a₂ : G)⁻¹ ∈ pCoreOf 2 H :=
    h.comm (Subgroup.commutator_mem_commutator a₁.2 a₂.2)
  refine ⟨fun x hxH hx₁ hx₂ => ?_, fun y hy => ?_⟩
  · have hle : Subgroup.zpowers (a₁ : G) ⊔ Subgroup.zpowers (a₂ : G) ⊔ pCoreOf 2 H ≤
        zrCommSub H (pCoreOf 2 H) hQ x :=
      sup_le (sup_le (Subgroup.zpowers_le.mpr ⟨ha₁H, hx₁⟩) (Subgroup.zpowers_le.mpr ⟨ha₂H, hx₂⟩))
        (fun q hq => ⟨pCoreOf_le 2 H hq, hQc x hxH q hq⟩)
    intro y hy
    exact (hle (hpq hy)).2
  · have hyR := hpq hy
    constructor
    · have hle : Subgroup.zpowers (a₁ : G) ⊔ Subgroup.zpowers (a₂ : G) ⊔ pCoreOf 2 H ≤
          zrCommSub H (pCoreOf 2 H) hQ (a₁ : G) :=
        sup_le (sup_le (Subgroup.zpowers_le.mpr ⟨ha₁H, by simp⟩)
          (Subgroup.zpowers_le.mpr ⟨ha₂H, hcomm⟩))
          (fun q hq => ⟨pCoreOf_le 2 H hq, hQc _ ha₁H q hq⟩)
      exact (hle hyR).2
    · have hcomm' : (a₂ : G) * (a₁ : G) * (a₂ : G)⁻¹ * (a₁ : G)⁻¹ ∈ pCoreOf 2 H := by
        have e : (a₂ : G) * (a₁ : G) * (a₂ : G)⁻¹ * (a₁ : G)⁻¹ =
            ((a₁ : G) * (a₂ : G) * (a₁ : G)⁻¹ * (a₂ : G)⁻¹)⁻¹ := by group
        rw [e]
        exact (pCoreOf 2 H).inv_mem hcomm
      have hle : Subgroup.zpowers (a₁ : G) ⊔ Subgroup.zpowers (a₂ : G) ⊔ pCoreOf 2 H ≤
          zrCommSub H (pCoreOf 2 H) hQ (a₂ : G) :=
        sup_le (sup_le (Subgroup.zpowers_le.mpr ⟨ha₁H, hcomm'⟩)
          (Subgroup.zpowers_le.mpr ⟨ha₂H, by simp⟩))
          (fun q hq => ⟨pCoreOf_le 2 H hq, hQc _ ha₂H q hq⟩)
      exact (hle hyR).2

theorem IsRedCE.centralizer_le_pq (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (habel : ∀ y ∈ PQ, ∀ z ∈ PQ, y * z * y⁻¹ * z⁻¹ ∈ pCoreOf 2 H)
    {x : G} (hxH : x ∈ H) (hx : ∀ y ∈ PQ, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H) : x ∈ PQ := by
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  set Q := pCoreOf 2 H with hQdef
  have hQ : H ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 H
  have hPQn : H ≤ Subgroup.normalizer (PQ : Set G) := hred.normal
  have hQT : Q ≤ T := S.pCoreOf_le_T hH
  have hQPQ : Q ≤ PQ := hred.lt.le
  have hmul : (↑(PQ ⊔ T) : Set G) = ↑PQ * ↑T :=
    Subgroup.coe_mul_of_right_le_normalizer_left PQ T (hTH.trans hPQn)
  let N : Subgroup G := zrCentSub H Q PQ hQ hPQn
  have hNn : ∀ g ∈ H, ∀ z ∈ N, g * z * g⁻¹ ∈ N := by
    rintro g hg z ⟨hzH, hz⟩
    refine ⟨H.mul_mem (H.mul_mem hg hzH) (H.inv_mem hg), fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ PQ :=
      (Subgroup.mem_normalizer_iff.mp (hPQn (H.inv_mem hg)) y).mp hy
    have h1 := (Subgroup.mem_normalizer_iff.mp (hQ hg) _).mp (hz _ hy')
    have e : g * (z * (g⁻¹ * y * g⁻¹⁻¹) * z⁻¹ * (g⁻¹ * y * g⁻¹⁻¹)⁻¹) * g⁻¹ =
        (g * z * g⁻¹) * y * (g * z * g⁻¹)⁻¹ * y⁻¹ := by group
    rw [← e]
    exact h1
  have hPQN : PQ ≤ N := fun z hz => ⟨hred.le hz, fun y hy => habel z hz y hy⟩
  have hTR : ∀ s ∈ T, ∀ r ∈ N ⊓ T, s * r * s⁻¹ ∈ N ⊓ T := fun s hs r hr =>
    ⟨hNn s (hTH hs) r hr.1, T.mul_mem (T.mul_mem hs hr.2) (T.inv_mem hs)⟩
  have hPR : ∀ y ∈ PQ, ∀ r ∈ N ⊓ T, y * r * y⁻¹ ∈ N ⊓ T := by
    intro y hy r hr
    refine ⟨hNn y (hred.le hy) r hr.1, ?_⟩
    have h1 := hr.1.2 y⁻¹ (PQ.inv_mem hy)
    have h2 : y * r * y⁻¹ * r⁻¹ ∈ Q := by
      have h3 := (Subgroup.mem_normalizer_iff.mp (hQ (hred.le hy)) _).mp h1
      have e : y * (r * y⁻¹ * r⁻¹ * y⁻¹⁻¹) * y⁻¹ = y * r * y⁻¹ * r⁻¹ := by group
      rw [e] at h3
      exact h3
    have e2 : y * r * y⁻¹ = (y * r * y⁻¹ * r⁻¹) * r := by group
    rw [e2]
    exact T.mul_mem (hQT h2) hr.2
  have hRn : ∀ g ∈ H, ∀ r ∈ N ⊓ T, g * r * g⁻¹ ∈ N ⊓ T := by
    intro g hg r hr
    have hg' : g ∈ (↑(PQ ⊔ T) : Set G) := by rw [← hred.eq]; exact hg
    rw [hmul] at hg'
    obtain ⟨y, hy, s, hs, rfl⟩ := Set.mem_mul.mp hg'
    have e : y * s * r * (y * s)⁻¹ = y * (s * r * s⁻¹) * y⁻¹ := by group
    rw [e]
    exact hPR y hy _ (hTR s hs r hr)
  have hRQ : N ⊓ T ≤ Q :=
    le_pCoreOf_of_le_normalizer 2 (fun z hz => hz.1.1) (le_normalizer_of_conj_mem hRn)
      (hT2.to_le inf_le_right)
  have hxN : x ∈ N := ⟨hxH, hx⟩
  have hx' : x ∈ (↑(PQ ⊔ T) : Set G) := by rw [← hred.eq]; exact hxH
  rw [hmul] at hx'
  obtain ⟨y, hy, s, hs, rfl⟩ := Set.mem_mul.mp hx'
  have hsN : s ∈ N := by
    have := N.mul_mem (N.inv_mem (hPQN hy)) hxN
    simpa using this
  have hsQ : s ∈ Q := hRQ ⟨hsN, hs⟩
  exact PQ.mul_mem hy (hQPQ hsQ)

theorem IsDecP.mem_pq_of_centralizes (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t) (φ₁ : ↥H₁ →* DihedralGroup p)
    (hker₁ : ∀ y : ↥H₁, φ₁ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a₁ : ↥H₁}
    (ha₁ : φ₁ a₁ = DihedralGroup.r 1) (φ₂ : ↥H₂ →* DihedralGroup p)
    (hker₂ : ∀ y : ↥H₂, φ₂ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a₂ : ↥H₂}
    (ha₂ : φ₂ a₂ = DihedralGroup.r 1) {x : G} (hxH : x ∈ H)
    (hx₁ : x * (a₁ : G) * x⁻¹ * (a₁ : G)⁻¹ ∈ pCoreOf 2 H)
    (hx₂ : x * (a₂ : G) * x⁻¹ * (a₂ : G)⁻¹ ∈ pCoreOf 2 H) : x ∈ PQ := by
  obtain ⟨hA, hB⟩ := h.centralizes_pq_of_gens S hred φ₁ hker₁ ha₁ φ₂ hker₂ ha₂
  have hinv : ∀ y : G, (a₁ : G) * y * (a₁ : G)⁻¹ * y⁻¹ ∈ pCoreOf 2 H →
      y * (a₁ : G) * y⁻¹ * (a₁ : G)⁻¹ ∈ pCoreOf 2 H := fun y hy => by
    have e : y * (a₁ : G) * y⁻¹ * (a₁ : G)⁻¹ = ((a₁ : G) * y * (a₁ : G)⁻¹ * y⁻¹)⁻¹ := by group
    rw [e]
    exact (pCoreOf 2 H).inv_mem hy
  have hinv₂ : ∀ y : G, (a₂ : G) * y * (a₂ : G)⁻¹ * y⁻¹ ∈ pCoreOf 2 H →
      y * (a₂ : G) * y⁻¹ * (a₂ : G)⁻¹ ∈ pCoreOf 2 H := fun y hy => by
    have e : y * (a₂ : G) * y⁻¹ * (a₂ : G)⁻¹ = ((a₂ : G) * y * (a₂ : G)⁻¹ * y⁻¹)⁻¹ := by group
    rw [e]
    exact (pCoreOf 2 H).inv_mem hy
  have habel : ∀ y ∈ PQ, ∀ z ∈ PQ, y * z * y⁻¹ * z⁻¹ ∈ pCoreOf 2 H := fun y hy z hz =>
    hA y (hred.le hy) (hinv y (hB y hy).1) (hinv₂ y (hB y hy).2) z hz
  exact hred.centralizer_le_pq S habel hxH (hA x hxH hx₁ hx₂)

theorem IsDecP.mem_pCore_of_centralizes (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t) (φ₁ : ↥H₁ →* DihedralGroup p)
    (hker₁ : ∀ y : ↥H₁, φ₁ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a₁ : ↥H₁}
    (ha₁ : φ₁ a₁ = DihedralGroup.r 1) (φ₂ : ↥H₂ →* DihedralGroup p)
    (hker₂ : ∀ y : ↥H₂, φ₂ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a₂ : ↥H₂}
    (ha₂ : φ₂ a₂ = DihedralGroup.r 1) {x : G} (hxH : x ∈ H) (hx2 : x * x = 1)
    (hx₁ : x * (a₁ : G) * x⁻¹ * (a₁ : G)⁻¹ ∈ pCoreOf 2 H)
    (hx₂ : x * (a₂ : G) * x⁻¹ * (a₂ : G)⁻¹ ∈ pCoreOf 2 H) : x ∈ pCoreOf 2 H := by
  have hxPQ : x ∈ PQ := h.mem_pq_of_centralizes S hred φ₁ hker₁ ha₁ φ₂ hker₂ ha₂ hxH hx₁ hx₂
  obtain ⟨k, hk⟩ := hred.pSec x hxPQ
  obtain ⟨m, hm⟩ := (hred.prime.odd_of_ne_two hred.odd).pow (n := k)
  have hxp : x ^ (p ^ k) = x := by
    rw [hm, pow_succ, pow_mul, pow_two, hx2, one_pow, one_mul]
  rw [← hxp]
  exact hk

end Cent

end CFSG.Quasithin
