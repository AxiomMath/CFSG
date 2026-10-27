module

public import CFSG.Quasithin.Recognition.St84.Gen.Sec46Sp4qDefs
public import CFSG.Quasithin.Recognition.St84.Sec4Local

import CFSG.Quasithin.Recognition.St84.Sec6QQuot
import CFSG.Quasithin.Recognition.St84.Gen.Sec6LeafGen
import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
open scoped commutatorElement

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem exists_mem_inf_centralizer_mul_of_finite {H Q N K : Subgroup G} [Finite ↥H]
    (hQH : Q ≤ H) (hNQ : N ≤ Q) (hKH : K ≤ H) (hQn : H ≤ Subgroup.normalizer (Q : Set G))
    (hNn : H ≤ Subgroup.normalizer (N : Set G)) (hsolv : Group.IsSolvable ↥(Q.subgroupOf H))
    (hcop : (Nat.card K).Coprime (Nat.card Q))
    (htriv : ∀ k ∈ K, ∀ q ∈ Q, q⁻¹ * (k * q * k⁻¹) ∈ N) {q : G} (hq : q ∈ Q) :
    ∃ c ∈ Q ⊓ Subgroup.centralizer (K : Set G), ∃ n ∈ N, q = c * n := by
  have hmN : N.subgroupOf H ≤ Q.subgroupOf H := Subgroup.subgroupOf_mono H hNQ
  have hnorm : ∀ {A : Subgroup G}, H ≤ Subgroup.normalizer (A : Set G) →
      ∀ x : ↥H, x ∈ Subgroup.normalizer ((A.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    intro A hA x
    refine Subgroup.mem_normalizer_iff.mpr (fun y => ?_)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rw [show ((x * y * x⁻¹ : ↥H) : G) = (x : G) * (y : G) * (x : G)⁻¹ from rfl]
    exact Subgroup.mem_normalizer_iff.mp (hA x.2) (y : G)
  have hcop' : (Nat.card ↥(K.subgroupOf H)).Coprime (Nat.card ↥(Q.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv]
  have htriv' : ∀ s ∈ K.subgroupOf H,
      (⟨q, hQH hq⟩ : ↥H)⁻¹ * (s * ⟨q, hQH hq⟩ * s⁻¹) ∈ N.subgroupOf H := by
    intro s hs
    rw [Subgroup.mem_subgroupOf] at hs ⊢
    exact htriv (s : G) hs q hq
  obtain ⟨c, hc, n, hn, hcn⟩ :=
    CFSG.LocalAnalysis.EvenBN.Common.exists_mem_inf_centralizer_mul_of_coprime
      (M := Q.subgroupOf H) (N := N.subgroupOf H) (S := K.subgroupOf H)
      hmN (fun x _ => hnorm hNn x) (fun x _ => hnorm hQn x) (fun x _ => hnorm hNn x) hsolv hcop'
      (Subgroup.mem_subgroupOf.mpr hq) htriv'
  refine ⟨c, ⟨Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hc).1, ?_⟩, n,
    Subgroup.mem_subgroupOf.mp hn, ?_⟩
  · refine Subgroup.mem_centralizer_iff.mpr (fun k hk => ?_)
    have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2
      (⟨k, hKH hk⟩ : ↥H) (Subgroup.mem_subgroupOf.mpr hk)
    simpa using congrArg (fun z : ↥H => (z : G)) h1
  · calc q = ((⟨q, hQH hq⟩ : ↥H) : G) := rfl
      _ = ((c * n : ↥H) : G) := by rw [hcn]
      _ = (c : G) * (n : G) := rfl

namespace Setup

variable {X : Setup Γ G}

theorem isSylowTwoOf_S_L (X : Setup Γ G) {i : ℤ} (hi : i = 0 ∨ i = 1) :
    IsSylowTwoOf X.S (X.L i) := by
  rcases hi with rfl | rfl
  · rw [← X.edgeSylow_zero]
    exact X.isSylowTwoOf_edgeSylow_L 0
  · rw [← X.edgeSylow_zero]
    exact X.isSylowTwoOf_edgeSylow_L_succ 0

theorem isSylowTwoOf_S_Gi (X : Setup Γ G) {i : ℤ} (hi : i = 0 ∨ i = 1) :
    IsSylowTwoOf X.S (X.Gi i) := by
  rcases hi with rfl | rfl
  · rw [← X.edgeSylow_zero]
    exact X.isSylowTwoOf_edgeSylow_Gi 0
  · rw [← X.edgeSylow_zero]
    exact X.isSylowTwoOf_edgeSylow_Gi_succ 0

theorem Q_le_S (X : Setup Γ G) {i : ℤ} (hi : i = 0 ∨ i = 1) : X.Q i ≤ X.S := by
  rcases hi with rfl | rfl
  · rw [← X.edgeSylow_zero]
    exact X.Q_le_edgeSylow_left 0
  · rw [← X.edgeSylow_zero]
    exact X.Q_le_edgeSylow 0

theorem relIndex_Q_S (X : Setup Γ G) {i : ℤ} (hi : i = 0 ∨ i = 1) :
    (X.Q i).relIndex X.S = 2 ^ X.n i := by
  rcases hi with rfl | rfl
  · rw [← X.edgeSylow_zero]
    exact X.relIndex_Q_edgeSylow 0
  · rw [← X.edgeSylow_zero]
    exact X.relIndex_Q_succ_edgeSylow 0

theorem sq_mem_Q_of_mem_S (X : Setup Γ G) {i : ℤ} (hi : i = 0 ∨ i = 1) {x : G}
    (hx : x ∈ X.S) : x ^ 2 ∈ X.Q i :=
  X.sq_mem_Q_of_relIndex ((X.isSylowTwoOf_S_L hi).1) (X.relIndex_Q_S hi) x hx

theorem CaseBGen.hasB (B : X.CaseBGen) {i : ℤ} (hi : i = 0 ∨ i = 1) : X.HasB i 1 := by
  rcases hi with rfl | rfl
  · exact B.b₀
  · exact B.b₁

theorem CaseBGen.Z_le_Gi (B : X.CaseBGen) {i : ℤ} (hi : i = 0 ∨ i = 1) {k : ℤ}
    (hk : (k - i).natAbs ≤ 1) : X.Z i ≤ X.Gi k := by
  have h := (B.hasB hi).1 (k - i) hk
  rwa [show i + (k - i) = k by ring] at h

theorem CaseBGen.Z_le_S (B : X.CaseBGen) {i : ℤ} (hi : i = 0 ∨ i = 1) : X.Z i ≤ X.S := by
  haveI : Finite ↥(X.Gi 0 ⊓ X.Gi (0 + 1)) :=
    finite_of_le_stabilizer X.hyp (H := X.Gi 0 ⊓ X.Gi (0 + 1)) inf_le_left
  have h0 : X.Z i ≤ X.Gi 0 := B.Z_le_Gi hi (by rcases hi with rfl | rfl <;> decide)
  have h1 : X.Z i ≤ X.Gi (0 + 1) := B.Z_le_Gi hi (by rcases hi with rfl | rfl <;> decide)
  rw [← X.edgeSylow_zero]
  exact le_of_normal_isSylowTwoOf (X.isSylowTwoOf_edgeSylow 0)
    (X.edgeSylow_subgroupOf_normal 0) (le_inf h0 h1)
    ((pCoreOf_isPGroup' (X.Gi i)).to_le (X.Z_le_Q i))

theorem CaseBGen.not_Z_le_Q (B : X.CaseBGen) {i : ℤ} (hi : i = 0 ∨ i = 1) :
    ¬ X.Z i ≤ X.Q (1 - i) := by
  intro hle
  rcases hi with rfl | rfl
  · apply B.b₀.2.1
    intro z hz
    have h := (X.Q_le_Gi_adj 1) (hle hz)
    simpa using (Subgroup.mem_inf.mp h).2
  · apply B.b₁.2.2
    intro z hz
    have h := (X.Q_le_Gi_adj 0) (hle hz)
    simpa using (Subgroup.mem_inf.mp h).1

theorem CaseBGen.Z_sup_Q (B : X.CaseBGen) {i : ℤ} (hi : i = 0 ∨ i = 1) :
    X.Z i ⊔ X.Q (1 - i) = X.S := by
  have hZS := B.Z_le_S hi
  have hnot := B.not_Z_le_Q hi
  have hK : ∀ j : ℤ, X.K ≤ Subgroup.normalizer (X.Z j : Set G) := fun j g hg =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal j g (X.K_le_Gi j hg))
  rcases hi with rfl | rfl
  · have h := X.sup_Q_eq_edgeSylow_of_gen 0 (A := X.Z 0)
      (inf_le_left.trans (hK 0)) (by rw [X.edgeSylow_zero]; exact hZS)
      (by simpa using hnot)
    simpa [X.edgeSylow_zero] using h
  · have h := X.sup_Q_eq_edgeSylow_of_left_gen 0 (A := X.Z 1)
      (inf_le_left.trans (hK 1)) (by rw [X.edgeSylow_zero]; exact hZS)
      (by simpa using hnot)
    simpa [X.edgeSylow_zero] using h

theorem CaseBGen.Q_sup_Q (B : X.CaseBGen) : X.Q 0 ⊔ X.Q 1 = X.S := by
  refine le_antisymm (sup_le (X.Q_le_S (Or.inl rfl)) (X.Q_le_S (Or.inr rfl))) ?_
  rw [← B.Z_sup_Q (Or.inl rfl)]
  exact sup_le_sup_right (X.Z_le_Q 0) _

theorem CaseBGen.Z_le_L (B : X.CaseBGen) {i : ℤ} (hi : i = 0 ∨ i = 1) :
    X.Z (1 - i) ≤ X.L i :=
  (B.Z_le_S (by rcases hi with rfl | rfl <;> simp)).trans ((X.isSylowTwoOf_S_L hi).1)

theorem CaseBGen.card_Q (B : X.CaseBGen) {i : ℤ} (hi : i = 0 ∨ i = 1) :
    Nat.card (X.Q i) = 2 ^ (X.n i + 2 * X.n (1 - i)) := by
  have h := Subgroup.relIndex_mul_card (H := X.Q i) (K := X.S)
  rw [inf_eq_left.mpr (X.Q_le_S hi), X.relIndex_Q_S hi, B.card_S] at h
  have hsum : 2 * X.n 0 + 2 * X.n 1 = X.n i + (X.n i + 2 * X.n (1 - i)) := by
    rcases hi with rfl | rfl <;> simp <;> ring
  rw [hsum, pow_add] at h
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h

theorem CaseBGen.R_elem (B : X.CaseBGen) : IsElemAbelian 2 ⁅X.Z 0, X.Z 1⁆ := by
  have hRZ0 : ⁅X.Z 0, X.Z 1⁆ ≤ X.Z 0 := B.R_le.trans inf_le_left
  have hmem0 : ∀ x ∈ X.Z 1, ∀ z ∈ X.Z 0, ⁅x, z⁆ ∈ X.Z 0 := by
    intro x hx z hz
    have h := (X.Z 0).inv_mem (hRZ0 (Subgroup.commutator_mem_commutator hz hx))
    simpa [commutatorElement_inv] using h
  have hsq : ∀ x ∈ X.Z 1, ∀ z ∈ X.Z 0, ⁅x, z⁆ ^ 2 = 1 := by
    intro x hx z hz
    have hc : ⁅x, z⁆ ∈ X.Z 0 := hmem0 x hx z hz
    have hcomm : Commute z ⁅x, z⁆ := X.Z_commute 0 z hz ⁅x, z⁆ hc
    rw [Commute.commutatorElement_pow_right hcomm 2]
    have hz2 : z ^ 2 ∈ X.Q 1 := X.sq_mem_Q_of_mem_S (Or.inr rfl) (B.Z_le_S (Or.inl rfl) hz)
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_inf.mp (X.Z_le_center 1 hx)).2 (z ^ 2) hz2).symm
  have hRA : ⁅X.Z 0, X.Z 1⁆ ≤
      { carrier := {y : G | y ∈ X.Z 0 ∧ y ^ 2 = 1}
        one_mem' := ⟨(X.Z 0).one_mem, by simp⟩
        mul_mem' := by
          rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
          exact ⟨(X.Z 0).mul_mem ha hb,
            by rw [Commute.mul_pow (X.Z_commute 0 a ha b hb) 2, ha2, hb2, mul_one]⟩
        inv_mem' := by
          rintro a ⟨ha, ha2⟩
          exact ⟨(X.Z 0).inv_mem ha, by rw [inv_pow, ha2, inv_one]⟩ } := by
    refine Subgroup.commutator_le.mpr ?_
    intro z hz x hx
    refine ⟨?_, ?_⟩
    · have h := (X.Z 0).inv_mem (hmem0 x hx z hz)
      simpa [commutatorElement_inv] using h
    · rw [← commutatorElement_inv, inv_pow, hsq x hx z hz, inv_one]
  refine ⟨⟨⟨fun a b => Subtype.ext (X.Z_commute 0 _ (hRA a.2).1 _ (hRA b.2).1)⟩⟩, ?_⟩
  intro x hx
  exact (hRA hx).2

end Setup

end CFSG.Quasithin.St84

end
