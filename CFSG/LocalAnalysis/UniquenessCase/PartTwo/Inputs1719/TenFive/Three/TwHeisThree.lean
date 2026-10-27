module


import CFSG.Mathlib.Algebra.MapAdd
public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycle
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcHeis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.LieType.AlgebraicGroups (fixedPointsIn mem_fixedPointsIn)
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 (Heis)
open scoped commutatorElement

private lemma twHeisThree_shuffle {G : Type*} [Group G] {b0 b0' b1 b1' b2 b2' : G}
    (h01 : Commute b0' b1) (h02 : Commute b0' b2) (h12 : Commute b1' b2) :
    b0 * b0' * (b1 * b1') * (b2 * b2') = b0 * b1 * b2 * (b0' * b1' * b2') := by
  calc b0 * b0' * (b1 * b1') * (b2 * b2')
      = b0 * (b0' * b1) * (b1' * b2) * b2' := by group
    _ = b0 * (b1 * b0') * (b2 * b1') * b2' := by rw [h01.eq, h12.eq]
    _ = b0 * b1 * (b0' * b2) * b1' * b2' := by group
    _ = b0 * b1 * (b2 * b0') * b1' * b2' := by rw [h02.eq]
    _ = b0 * b1 * b2 * (b0' * b1' * b2') := by group

private lemma twHeisThree_add_three {G k K : Type*} [Group G] [Field k] [Field K]
    (ι : K →+* k) {F : Fin 3 → k → G} (c0 c1 c2 : k)
    (hF : ∀ i x y, F i (x + y) = F i x * F i y)
    (hFF : ∀ i j x y, Commute (F i x) (F j y)) (r r' : K) :
    F 0 (c0 * ι (r + r')) * F 1 (c1 * ι (r + r')) * F 2 (c2 * ι (r + r')) =
      (F 0 (c0 * ι r) * F 1 (c1 * ι r) * F 2 (c2 * ι r)) *
      (F 0 (c0 * ι r') * F 1 (c1 * ι r') * F 2 (c2 * ι r')) := by
  have h0 : c0 * ι (r + r') = c0 * ι r + c0 * ι r' := by rw [map_add, mul_add]
  have h1 : c1 * ι (r + r') = c1 * ι r + c1 * ι r' := by rw [map_add, mul_add]
  have h2 : c2 * ι (r + r') = c2 * ι r + c2 * ι r' := by rw [map_add, mul_add]
  simp only [h0, h1, h2, hF]
  exact twHeisThree_shuffle (hFF 0 1 _ _) (hFF 0 2 _ _) (hFF 1 2 _ _)

private lemma twHeisThree_orbit_fixed {G k K : Type*} [Group G] [Field k] [Field K]
    (S : G →* G) (ι : K →+* k) {F : Fin 3 → k → G} (u : Fin 3 → k) {lam : k} (r : K)
    (hu : ∀ i, u i * u i = 1)
    (hSF : ∀ i c, S (F i c) = F (i + 1) (u i * c ^ 3))
    (hFF : ∀ i j c d, Commute (F i c) (F j d))
    (hlam : lam ^ 27 = lam * (u 0 * u 1 * u 2)) (hx : (ι r) ^ 3 = ι r) :
    S (F 0 (lam * ι r) * F 1 (u 0 * lam ^ 3 * ι r) * F 2 (u 0 * u 1 * lam ^ 9 * ι r)) =
      F 0 (lam * ι r) * F 1 (u 0 * lam ^ 3 * ι r) * F 2 (u 0 * u 1 * lam ^ 9 * ι r) := by
  have hu3 : ∀ i, u i ^ 3 = u i := fun i => by rw [pow_succ, sq, hu i, one_mul]
  have hu2 : (u 0 * u 1 * u 2) * (u 0 * u 1 * u 2) = 1 := by
    rw [show (u 0 * u 1 * u 2) * (u 0 * u 1 * u 2) =
      u 0 * u 0 * (u 1 * u 1) * (u 2 * u 2) by ring, hu 0, hu 1, hu 2]
    ring
  have hA1 : u 0 * (lam * ι r) ^ 3 = u 0 * lam ^ 3 * ι r := by
    rw [show (lam * ι r) ^ 3 = lam ^ 3 * (ι r) ^ 3 by ring, hx]
    ring
  have hA2 : u 1 * (u 0 * lam ^ 3 * ι r) ^ 3 = u 0 * u 1 * lam ^ 9 * ι r := by
    rw [show (u 0 * lam ^ 3 * ι r) ^ 3 = u 0 ^ 3 * lam ^ 9 * (ι r) ^ 3 by ring, hu3 0, hx]
    ring
  have hA3 : u 2 * (u 0 * u 1 * lam ^ 9 * ι r) ^ 3 = lam * ι r := by
    rw [show (u 0 * u 1 * lam ^ 9 * ι r) ^ 3 =
      u 0 ^ 3 * u 1 ^ 3 * lam ^ 27 * (ι r) ^ 3 by ring, hu3 0, hu3 1, hx, hlam]
    rw [show u 2 * (u 0 * u 1 * (lam * (u 0 * u 1 * u 2)) * ι r) =
      lam * ((u 0 * u 1 * u 2) * (u 0 * u 1 * u 2)) * ι r by ring, hu2]
    ring
  have e01 : (0 : Fin 3) + 1 = 1 := by decide
  have e12 : (1 : Fin 3) + 1 = 2 := by decide
  have e20 : (2 : Fin 3) + 1 = 0 := by decide
  simp only [map_mul, hSF, e01, e12, e20, hA1, hA2, hA3]
  exact (Commute.mul_left (hFF 1 0 _ _) (hFF 2 0 _ _)).eq.trans (mul_assoc _ _ _).symm

private theorem twHeisThree_commutator {G k K : Type*} [Group G] [Field k] [Field K]
    (ι : K →+* k) {B D : Fin 3 → k → G} {E : k → G} {s t n : Fin 3 → k}
    {lam mu : k} (r r' : K)
    (hBD : ∀ i j c d, i ≠ j → Commute (B i c) (D j d))
    (hBDi : ∀ i c d, ⁅B i c, D i d⁆ = E (n i * (c * d)))
    (hEB : ∀ i c d, Commute (E c) (B i d))
    (hED : ∀ i c d, Commute (E c) (D i d))
    (hE : ∀ c d, E (c + d) = E c * E d) :
    ⁅B 0 (lam * ι r) * B 1 (s 0 * lam ^ 3 * ι r) * B 2 (s 0 * s 1 * lam ^ 9 * ι r),
        D 0 (mu * ι r') * D 1 (t 0 * mu ^ 3 * ι r') *
          D 2 (t 0 * t 1 * mu ^ 9 * ι r')⁆ =
      E (n 0 * (lam * ι r * (mu * ι r'))) *
        (E (n 1 * (s 0 * lam ^ 3 * ι r * (t 0 * mu ^ 3 * ι r'))) *
          E (n 2 * (s 0 * s 1 * lam ^ 9 * ι r * (t 0 * t 1 * mu ^ 9 * ι r')))) := by
  have hB' : B 0 (lam * ι r) * B 1 (s 0 * lam ^ 3 * ι r) * B 2 (s 0 * s 1 * lam ^ 9 * ι r) =
      B 0 (lam * ι r) * (B 1 (s 0 * lam ^ 3 * ι r) * B 2 (s 0 * s 1 * lam ^ 9 * ι r)) :=
    mul_assoc _ _ _
  have hD' : D 0 (mu * ι r') * D 1 (t 0 * mu ^ 3 * ι r') * D 2 (t 0 * t 1 * mu ^ 9 * ι r') =
      D 0 (mu * ι r') * (D 1 (t 0 * mu ^ 3 * ι r') * D 2 (t 0 * t 1 * mu ^ 9 * ι r')) :=
    mul_assoc _ _ _
  rw [hB', hD']
  have hbc : Commute (B 2 (s 0 * s 1 * lam ^ 9 * ι r)) (D 1 (t 0 * mu ^ 3 * ι r')) :=
    hBD 2 1 _ _ (by decide)
  have had : Commute (B 1 (s 0 * lam ^ 3 * ι r)) (D 2 (t 0 * t 1 * mu ^ 9 * ι r')) :=
    hBD 1 2 _ _ (by decide)
  have hcbd : Commute (D 1 (t 0 * mu ^ 3 * ι r'))
      ⁅B 2 (s 0 * s 1 * lam ^ 9 * ι r), D 2 (t 0 * t 1 * mu ^ 9 * ι r')⁆ := by
    rw [hBDi 2 _ _]
    exact (hED 1 _ _).symm
  have habd : Commute (B 1 (s 0 * lam ^ 3 * ι r))
      ⁅B 2 (s 0 * s 1 * lam ^ 9 * ι r), D 2 (t 0 * t 1 * mu ^ 9 * ι r')⁆ := by
    rw [hBDi 2 _ _]
    exact (hEB 1 _ _).symm
  have hinner : ⁅B 1 (s 0 * lam ^ 3 * ι r) * B 2 (s 0 * s 1 * lam ^ 9 * ι r),
      D 1 (t 0 * mu ^ 3 * ι r') * D 2 (t 0 * t 1 * mu ^ 9 * ι r')⁆ =
      E (n 1 * (s 0 * lam ^ 3 * ι r * (t 0 * mu ^ 3 * ι r'))) *
        E (n 2 * (s 0 * s 1 * lam ^ 9 * ι r * (t 0 * t 1 * mu ^ 9 * ι r'))) := by
    have hcc : Commute ⁅B 1 (s 0 * lam ^ 3 * ι r), D 1 (t 0 * mu ^ 3 * ι r')⁆
        ⁅B 2 (s 0 * s 1 * lam ^ 9 * ι r), D 2 (t 0 * t 1 * mu ^ 9 * ι r')⁆ := by
      rw [hBDi 1 _ _, hBDi 2 _ _]
      exact commute_of_map_add hE _ _
    calc ⁅B 1 (s 0 * lam ^ 3 * ι r) * B 2 (s 0 * s 1 * lam ^ 9 * ι r),
          D 1 (t 0 * mu ^ 3 * ι r') * D 2 (t 0 * t 1 * mu ^ 9 * ι r')⁆
        = ⁅B 1 (s 0 * lam ^ 3 * ι r), D 1 (t 0 * mu ^ 3 * ι r')⁆ *
          ⁅B 2 (s 0 * s 1 * lam ^ 9 * ι r), D 2 (t 0 * t 1 * mu ^ 9 * ι r')⁆ :=
        TauCeti.commutatorElement_mul_mul_eq_mul_of_commute hbc had hcbd habd hcc
      _ = E (n 1 * (s 0 * lam ^ 3 * ι r * (t 0 * mu ^ 3 * ι r'))) *
          E (n 2 * (s 0 * s 1 * lam ^ 9 * ι r * (t 0 * t 1 * mu ^ 9 * ι r'))) := by
        rw [hBDi 1 _ _, hBDi 2 _ _]
  have hcbd' : Commute (D 0 (mu * ι r'))
      ⁅B 1 (s 0 * lam ^ 3 * ι r) * B 2 (s 0 * s 1 * lam ^ 9 * ι r),
        D 1 (t 0 * mu ^ 3 * ι r') * D 2 (t 0 * t 1 * mu ^ 9 * ι r')⁆ := by
    rw [hinner]
    exact (hED 0 _ _).symm.mul_right (hED 0 _ _).symm
  have habd' : Commute (B 0 (lam * ι r))
      ⁅B 1 (s 0 * lam ^ 3 * ι r) * B 2 (s 0 * s 1 * lam ^ 9 * ι r),
        D 1 (t 0 * mu ^ 3 * ι r') * D 2 (t 0 * t 1 * mu ^ 9 * ι r')⁆ := by
    rw [hinner]
    exact (hEB 0 _ _).symm.mul_right (hEB 0 _ _).symm
  have hccOuter : Commute ⁅B 0 (lam * ι r), D 0 (mu * ι r')⁆
      ⁅B 1 (s 0 * lam ^ 3 * ι r) * B 2 (s 0 * s 1 * lam ^ 9 * ι r),
        D 1 (t 0 * mu ^ 3 * ι r') * D 2 (t 0 * t 1 * mu ^ 9 * ι r')⁆ := by
    rw [hBDi 0 _ _, hinner]
    exact (commute_of_map_add hE _ _).mul_right (commute_of_map_add hE _ _)
  have hbc' : Commute (B 1 (s 0 * lam ^ 3 * ι r) * B 2 (s 0 * s 1 * lam ^ 9 * ι r))
      (D 0 (mu * ι r')) :=
    (hBD 1 0 _ _ (by decide)).mul_left (hBD 2 0 _ _ (by decide))
  have had' : Commute (B 0 (lam * ι r))
      (D 1 (t 0 * mu ^ 3 * ι r') * D 2 (t 0 * t 1 * mu ^ 9 * ι r')) :=
    (hBD 0 1 _ _ (by decide)).mul_right (hBD 0 2 _ _ (by decide))
  calc ⁅B 0 (lam * ι r) * (B 1 (s 0 * lam ^ 3 * ι r) * B 2 (s 0 * s 1 * lam ^ 9 * ι r)),
        D 0 (mu * ι r') * (D 1 (t 0 * mu ^ 3 * ι r') * D 2 (t 0 * t 1 * mu ^ 9 * ι r'))⁆
      = ⁅B 0 (lam * ι r), D 0 (mu * ι r')⁆ *
        ⁅B 1 (s 0 * lam ^ 3 * ι r) * B 2 (s 0 * s 1 * lam ^ 9 * ι r),
          D 1 (t 0 * mu ^ 3 * ι r') * D 2 (t 0 * t 1 * mu ^ 9 * ι r')⁆ :=
        TauCeti.commutatorElement_mul_mul_eq_mul_of_commute hbc' had' hcbd' habd' hccOuter
    _ = E (n 0 * (lam * ι r * (mu * ι r'))) *
        (E (n 1 * (s 0 * lam ^ 3 * ι r * (t 0 * mu ^ 3 * ι r'))) *
          E (n 2 * (s 0 * s 1 * lam ^ 9 * ι r * (t 0 * t 1 * mu ^ 9 * ι r')))) := by
        rw [hBDi 0 _ _, hinner]

theorem exists_heis_orbit_three {G : Type*} [Group G] (X : Subgroup G) (S : G →* G)
    {K k : Type*} [Field K] [Finite K] [Field k] (ι : K →+* k) (hK : Nat.card K = 3)
    {B D : Fin 3 → k → G} {E : k → G} (hB : ∀ i c d, B i (c + d) = B i c * B i d)
    (hD : ∀ i c d, D i (c + d) = D i c * D i d) (hE : ∀ c d, E (c + d) = E c * E d)
    (hBX : ∀ i c, B i c ∈ X) (hDX : ∀ i c, D i c ∈ X)
    {s t n : Fin 3 → k} (hs : ∀ i, s i * s i = 1) (ht : ∀ i, t i * t i = 1)
    (hSB : ∀ i c, S (B i c) = B (i + 1) (s i * c ^ 3))
    (hSD : ∀ i c, S (D i c) = D (i + 1) (t i * c ^ 3))
    (hBB : ∀ i j c d, Commute (B i c) (B j d)) (hDD : ∀ i j c d, Commute (D i c) (D j d))
    (hBD : ∀ i j c d, i ≠ j → Commute (B i c) (D j d))
    (hBDi : ∀ i c d, ⁅B i c, D i d⁆ = E (n i * (c * d)))
    (hEB : ∀ i c d, Commute (E c) (B i d)) (hED : ∀ i c d, Commute (E c) (D i d))
    (hEinj : ∀ c, E c = 1 → c = 0) {lam mu : k} (hlam : lam ^ 27 = lam * (s 0 * s 1 * s 2))
    (hmu : mu ^ 27 = mu * (t 0 * t 1 * t 2))
    (hw : n 0 * (lam * mu) + n 1 * (s 0 * t 0) * (lam * mu) ^ 3 +
      n 2 * (s 0 * s 1 * (t 0 * t 1)) * (lam * mu) ^ 9 ≠ 0) :
    ∃ ι' : Heis K →* fixedPointsIn X S, Function.Injective ι' ∧
      (∀ r, (ι' ⟨r, 0, 0⟩ : G) =
        B 0 (lam * ι r) * B 1 (s 0 * lam ^ 3 * ι r) * B 2 (s 0 * s 1 * lam ^ 9 * ι r)) ∧
      (∀ r, (ι' ⟨0, r, 0⟩ : G) =
        D 0 (mu * ι r) * D 1 (t 0 * mu ^ 3 * ι r) * D 2 (t 0 * t 1 * mu ^ 9 * ι r)) ∧
      ∀ r, (ι' ⟨0, 0, r⟩ : G) = E ((n 0 * (lam * mu) + n 1 * (s 0 * t 0) * (lam * mu) ^ 3 +
        n 2 * (s 0 * s 1 * (t 0 * t 1)) * (lam * mu) ^ 9) * ι r) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card, hK]
  have hι3 : ∀ r : K, (ι r) ^ 3 = ι r := by
    intro r
    rw [← map_pow, ← hcard]
    exact congrArg ι (FiniteField.pow_card r)
  let Xa : K → G := fun r => B 0 (lam * ι r) * B 1 (s 0 * lam ^ 3 * ι r) *
    B 2 (s 0 * s 1 * lam ^ 9 * ι r)
  let Xb : K → G := fun r => D 0 (mu * ι r) * D 1 (t 0 * mu ^ 3 * ι r) *
    D 2 (t 0 * t 1 * mu ^ 9 * ι r)
  have hXa : ∀ r, Xa r = B 0 (lam * ι r) * B 1 (s 0 * lam ^ 3 * ι r) *
      B 2 (s 0 * s 1 * lam ^ 9 * ι r) := fun r => rfl
  have hXb : ∀ r, Xb r = D 0 (mu * ι r) * D 1 (t 0 * mu ^ 3 * ι r) *
      D 2 (t 0 * t 1 * mu ^ 9 * ι r) := fun r => rfl
  have hXa_add : ∀ r r' : K, Xa (r + r') = Xa r * Xa r' := by
    intro r r'
    simp only [hXa]
    exact twHeisThree_add_three ι lam (s 0 * lam ^ 3) (s 0 * s 1 * lam ^ 9) hB hBB r r'
  have hXb_add : ∀ r r' : K, Xb (r + r') = Xb r * Xb r' := by
    intro r r'
    simp only [hXb]
    exact twHeisThree_add_three ι mu (t 0 * mu ^ 3) (t 0 * t 1 * mu ^ 9) hD hDD r r'
  have hXa_mem : ∀ r, Xa r ∈ X := by
    intro r
    rw [hXa]
    exact X.mul_mem (X.mul_mem (hBX 0 _) (hBX 1 _)) (hBX 2 _)
  have hXb_mem : ∀ r, Xb r ∈ X := by
    intro r
    rw [hXb]
    exact X.mul_mem (X.mul_mem (hDX 0 _) (hDX 1 _)) (hDX 2 _)
  have hXa_fix : ∀ r, S (Xa r) = Xa r := by
    intro r
    simp only [hXa]
    exact twHeisThree_orbit_fixed S ι (F := B) (u := s) (lam := lam) (r := r) hs hSB hBB hlam
      (hι3 r)
  have hXb_fix : ∀ r, S (Xb r) = Xb r := by
    intro r
    simp only [hXb]
    exact twHeisThree_orbit_fixed S ι (F := D) (u := t) (lam := mu) (r := r) ht hSD hDD hmu
      (hι3 r)
  set W : k := n 0 * (lam * mu) + n 1 * (s 0 * t 0) * (lam * mu) ^ 3 +
    n 2 * (s 0 * s 1 * (t 0 * t 1)) * (lam * mu) ^ 9 with hW_def
  have harg : ∀ r r' : K,
      n 0 * (lam * ι r * (mu * ι r')) +
        (n 1 * (s 0 * lam ^ 3 * ι r * (t 0 * mu ^ 3 * ι r')) +
          n 2 * (s 0 * s 1 * lam ^ 9 * ι r * (t 0 * t 1 * mu ^ 9 * ι r'))) =
      W * (ι r * ι r') := by
    intro r r'
    rw [hW_def]
    ring
  have hXcomm : ∀ r r' : K, ⁅Xa r, Xb r'⁆ =
      E (n 0 * (lam * ι r * (mu * ι r'))) *
        (E (n 1 * (s 0 * lam ^ 3 * ι r * (t 0 * mu ^ 3 * ι r'))) *
          E (n 2 * (s 0 * s 1 * lam ^ 9 * ι r * (t 0 * t 1 * mu ^ 9 * ι r')))) := by
    intro r r'
    rw [hXa, hXb]
    exact twHeisThree_commutator ι r r' hBD hBDi hEB hED hE
  let T := fixedPointsIn X S
  let xa : K → T := fun r => ⟨Xa r, mem_fixedPointsIn.2 ⟨hXa_mem r, hXa_fix r⟩⟩
  let xb : K → T := fun r => ⟨Xb r, mem_fixedPointsIn.2 ⟨hXb_mem r, hXb_fix r⟩⟩
  let z : K → T := fun r => ⁅xa r, xb 1⁆
  have hxa_def : ∀ r, (xa r : G) = Xa r := fun r => rfl
  have hxb_def : ∀ r, (xb r : G) = Xb r := fun r => rfl
  have hzG : ∀ r, (z r : G) = E (W * ι r) := by
    intro r
    have h1 : (z r : G) = ⁅Xa r, Xb 1⁆ := by
      have h := map_commutatorElement T.subtype (xa r) (xb 1)
      rw [show T.subtype (xa r) = Xa r from rfl,
        show T.subtype (xb 1) = Xb 1 from rfl] at h
      exact h
    rw [h1, hXcomm r 1, ← hE, ← hE, harg r 1, map_one, mul_one]
  have hz_add : ∀ r r' : K, z (r + r') = z r * z r' := by
    intro r r'
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    simp only [hzG]
    rw [show W * ι (r + r') = W * ι r + W * ι r' by rw [map_add]; ring]
    exact hE _ _
  have hz_inj : Function.Injective z := by
    intro r r' hrr
    have hW0 : W ≠ 0 := hw
    have hδ : z (r - r') = 1 := by
      have h1 : z r' * z (r - r') = z r' * 1 := by
        rw [mul_one, ← hz_add, show r' + (r - r') = r by ring, hrr]
      exact mul_left_cancel h1
    have hG : (z (r - r') : G) = 1 := by rw [hδ]; rfl
    rw [hzG] at hG
    have hc : W * ι (r - r') = 0 := hEinj _ hG
    have hιδ : ι (r - r') = 0 := (mul_eq_zero.mp hc).resolve_left hW0
    have hδ0 : r - r' = 0 := by
      apply ι.injective
      rw [hιδ, map_zero]
    exact sub_eq_zero.mp hδ0
  have hza : ∀ r r' : K, Commute (z r) (xa r') := by
    intro r r'
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    simp only [hzG, hxa_def, hXa]
    exact ((hEB 0 _ _).mul_right (hEB 1 _ _)).mul_right (hEB 2 _ _)
  have hzb : ∀ r r' : K, Commute (z r) (xb r') := by
    intro r r'
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    simp only [hzG, hxb_def, hXb]
    exact ((hED 0 _ _).mul_right (hED 1 _ _)).mul_right (hED 2 _ _)
  have hxa_add : ∀ r r' : K, xa (r + r') = xa r * xa r' := by
    intro r r'
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    simp only [hxa_def]
    exact hXa_add r r'
  have hxb_add : ∀ r r' : K, xb (r + r') = xb r * xb r' := by
    intro r r'
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    simp only [hxb_def]
    exact hXb_add r r'
  have hab : ∀ r r' : K, ⁅xa r, xb r'⁆ = z (r * r') := by
    intro r r'
    apply Subtype.ext
    have h1 : (((⁅xa r, xb r'⁆ : T)) : G) = ⁅Xa r, Xb r'⁆ := by
      have h := map_commutatorElement T.subtype (xa r) (xb r')
      rw [show T.subtype (xa r) = Xa r from rfl,
        show T.subtype (xb r') = Xb r' from rfl] at h
      exact h
    rw [h1, hXcomm r r', ← hE, ← hE, harg r r', hzG (r * r'), map_mul]
  obtain ⟨ι', hι'inj, hι'a, hι'b, hι'c⟩ :=
    exists_heis_of_comm (K := K) (S := T) hxa_add hxb_add hz_add hz_inj hab hza hzb
  refine ⟨ι', hι'inj, ?_, ?_, ?_⟩
  · intro r
    rw [hι'a r]
  · intro r
    rw [hι'b r]
  · intro r
    rw [hι'c r, hzG r]

theorem exists_heis_orbit_three_center {G : Type*} [Group G] (X : Subgroup G) (S : G →* G)
    {K k : Type*} [Field K] [Finite K] [Field k] [IsAlgClosed k] [CharP k 3] (ι : K →+* k)
    (hK : Nat.card K = 3) {B D : Fin 3 → k → G} {E : k → G}
    (hB : ∀ i c d, B i (c + d) = B i c * B i d) (hD : ∀ i c d, D i (c + d) = D i c * D i d)
    (hE : ∀ c d, E (c + d) = E c * E d) (hBX : ∀ i c, B i c ∈ X) (hDX : ∀ i c, D i c ∈ X)
    {s t n : Fin 3 → k} {se : k} (hs : ∀ i, s i * s i = 1) (ht : ∀ i, t i * t i = 1)
    (hse : se * se = 1) (hn : ∀ i, n i * n i = 1)
    (hSB : ∀ i c, S (B i c) = B (i + 1) (s i * c ^ 3))
    (hSD : ∀ i c, S (D i c) = D (i + 1) (t i * c ^ 3)) (hSE : ∀ c, S (E c) = E (se * c ^ 3))
    (hBB : ∀ i j c d, Commute (B i c) (B j d)) (hDD : ∀ i j c d, Commute (D i c) (D j d))
    (hBD : ∀ i j c d, i ≠ j → Commute (B i c) (D j d))
    (hBDi : ∀ i c d, ⁅B i c, D i d⁆ = E (n i * (c * d)))
    (hEB : ∀ i c d, Commute (E c) (B i d)) (hED : ∀ i c d, Commute (E c) (D i d))
    (hEinj : ∀ c, E c = 1 → c = 0) {lam : k} (hlam0 : lam ≠ 0)
    (hlam : lam ^ 27 = lam * (s 0 * s 1 * s 2)) {w : k} (hw : w * w = se) :
    ∃ (mu : k) (ι' : Heis K →* fixedPointsIn X S), Function.Injective ι' ∧
      (∀ r, (ι' ⟨r, 0, 0⟩ : G) =
        B 0 (lam * ι r) * B 1 (s 0 * lam ^ 3 * ι r) * B 2 (s 0 * s 1 * lam ^ 9 * ι r)) ∧
      (∀ r, (ι' ⟨0, r, 0⟩ : G) =
        D 0 (mu * ι r) * D 1 (t 0 * mu ^ 3 * ι r) * D 2 (t 0 * t 1 * mu ^ 9 * ι r)) ∧
      ∀ r, (ι' ⟨0, 0, r⟩ : G) = E (w * ι r) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card, hK]
  have hι3 : ∀ r : K, (ι r) ^ 3 = ι r := by
    intro r
    rw [← map_pow, ← hcard]
    exact congrArg ι (FiniteField.pow_card r)
  have hn3 : ∀ i : Fin 3, (n i) ^ 3 = n i := fun i => by rw [pow_succ, sq, hn i, one_mul]
  have hsign : ∀ i : Fin 3, n (i + 1) * (s i * t i) = se * n i := by
    intro i
    have h1 : S (⁅B i 1, D i 1⁆) = E (se * n i) := by
      rw [hBDi i 1 1]
      simp only [mul_one]
      rw [hSE, hn3 i]
    have h2 : S (⁅B i 1, D i 1⁆) = E (n (i + 1) * (s i * t i)) := by
      rw [map_commutatorElement, hSB, hSD, hBDi (i + 1)]
      simp
    rw [h2] at h1
    exact injective_of_map_add hE hEinj h1
  have hr0 : n 1 * (s 0 * t 0) = se * n 0 := hsign 0
  have hr1 : n 2 * (s 1 * t 1) = se * n 1 := hsign 1
  have hr2 : n 0 * (s 2 * t 2) = se * n 2 := hsign 2
  have hrn2 : n 2 * (s 0 * s 1 * (t 0 * t 1)) = n 0 := by
    calc n 2 * (s 0 * s 1 * (t 0 * t 1)) = (n 2 * (s 1 * t 1)) * (s 0 * t 0) := by ring
      _ = se * (n 1 * (s 0 * t 0)) := by rw [hr1]; ring
      _ = se * (se * n 0) := by rw [hr0]
      _ = n 0 := by rw [show se * (se * n 0) = (se * se) * n 0 by ring, hse, one_mul]
  have hn0 : n 0 ≠ 0 := left_ne_zero_of_mul_eq_one (hn 0)
  have hn1 : n 1 ≠ 0 := left_ne_zero_of_mul_eq_one (hn 1)
  have hn2 : n 2 ≠ 0 := left_ne_zero_of_mul_eq_one (hn 2)
  have hnprod : n 0 * n 1 * n 2 ≠ 0 := mul_ne_zero (mul_ne_zero hn0 hn1) hn2
  have hS2 : (s 0 * s 1 * s 2) * (s 0 * s 1 * s 2) = 1 := by
    rw [show (s 0 * s 1 * s 2) * (s 0 * s 1 * s 2) =
      s 0 * s 0 * (s 1 * s 1) * (s 2 * s 2) by ring, hs 0, hs 1, hs 2]
    ring
  have hmul : (n 0 * n 1 * n 2) * ((s 0 * s 1 * s 2) * (t 0 * t 1 * t 2)) =
      se * (n 0 * n 1 * n 2) := by
    calc (n 0 * n 1 * n 2) * ((s 0 * s 1 * s 2) * (t 0 * t 1 * t 2))
        = (n 1 * (s 0 * t 0)) * (n 2 * (s 1 * t 1)) * (n 0 * (s 2 * t 2)) := by ring
      _ = (se * n 0) * (se * n 1) * (se * n 2) := by rw [hr0, hr1, hr2]
      _ = se * (n 0 * n 1 * n 2) := by
          rw [show (se * n 0) * (se * n 1) * (se * n 2) = se ^ 3 * (n 0 * n 1 * n 2)
            by ring]
          rw [show se ^ 3 = se by
            have h2 : se ^ 2 = 1 := by rw [sq]; exact hse
            calc se ^ 3 = se ^ 2 * se := by ring
              _ = se := by rw [h2, one_mul]]
  have hST : (s 0 * s 1 * s 2) * (t 0 * t 1 * t 2) = se := by
    have h' : (n 0 * n 1 * n 2) * ((s 0 * s 1 * s 2) * (t 0 * t 1 * t 2)) =
        (n 0 * n 1 * n 2) * se := by
      rw [hmul]
      exact mul_comm se (n 0 * n 1 * n 2)
    exact mul_left_cancel₀ hnprod h'
  have htprod : t 0 * t 1 * t 2 = se * (s 0 * s 1 * s 2) := by
    calc t 0 * t 1 * t 2 =
          ((s 0 * s 1 * s 2) * (s 0 * s 1 * s 2)) * (t 0 * t 1 * t 2) := by
          rw [hS2, one_mul]
      _ = (s 0 * s 1 * s 2) * ((s 0 * s 1 * s 2) * (t 0 * t 1 * t 2)) := by ring
      _ = (s 0 * s 1 * s 2) * se := by rw [hST]
      _ = se * (s 0 * s 1 * s 2) := by ring
  obtain ⟨a, ha3⟩ : ∃ a : k, a ^ 3 = a + 1 := by
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root (Polynomial.X ^ 3 - Polynomial.X - 1 : Polynomial k)
      (by
        rw [show (Polynomial.X ^ 3 - Polynomial.X - 1 : Polynomial k).degree = 3 by
          compute_degree!]
        norm_num)
    refine ⟨a, ?_⟩
    have h : a ^ 3 - a - 1 = 0 := by simpa [Polynomial.IsRoot] using ha
    linear_combination h
  have h3k : (3 : k) = 0 := CharP.cast_eq_zero k 3
  have h2k : (2 : k) = -1 := by linear_combination h3k
  have h2neg : (-(2 : k)) = 1 := by rw [h2k]; ring
  have h6 : a ^ 6 = a ^ 2 - a + 1 := by
    have e : a ^ 6 = (a + 1) ^ 2 := by rw [show a ^ 6 = (a ^ 3) ^ 2 by ring, ha3]
    rw [e]
    calc (a + 1) ^ 2 = a ^ 2 + 2 * a + 1 := by ring
      _ = a ^ 2 - a + 1 := by rw [h2k]; ring
  have h9 : a ^ 9 = a + 2 := by
    have e : a ^ 9 = (a + 1) ^ 3 := by rw [show a ^ 9 = (a ^ 3) ^ 3 by ring, ha3]
    rw [e]
    calc (a + 1) ^ 3 = a ^ 3 + 3 * a ^ 2 + 3 * a + 1 := by ring
      _ = a ^ 3 + 1 := by rw [h3k]; ring
      _ = a + 2 := by rw [ha3]; ring
  have h9' : a ^ 9 = a - 1 := by rw [h9, h2k]; ring
  have h18 : a ^ 18 = a ^ 2 + a + 1 := by
    have e : a ^ 18 = (a - 1) ^ 2 := by rw [show a ^ 18 = (a ^ 9) ^ 2 by ring, h9']
    rw [e]
    calc (a - 1) ^ 2 = a ^ 2 + (-(2 : k)) * a + 1 := by ring
      _ = a ^ 2 + a + 1 := by rw [h2neg]; ring
  have h27 : a ^ 27 = a := by
    have e : a ^ 27 = (a - 1) ^ 3 := by rw [show a ^ 27 = (a ^ 9) ^ 3 by ring, h9']
    rw [e]
    calc (a - 1) ^ 3 = a ^ 3 - 3 * a ^ 2 + 3 * a - 1 := by ring
      _ = a ^ 3 - 1 := by rw [h3k]; ring
      _ = a := by rw [ha3]; ring
  have hasum : a ^ 2 + a ^ 6 + a ^ 18 = -1 := by
    rw [h6, h18]
    linear_combination (a ^ 2 + 1) * h3k
  set x : k := -(n 0 * w * a ^ 2) with hx_def
  set mu : k := x / lam with hmu_def
  have hxmulam : lam * mu = x := by
    rw [hmu_def, mul_comm]
    exact div_mul_cancel₀ x hlam0
  have hn0sq : n 0 * n 0 = 1 := hn 0
  have hw3 : w ^ 3 = w * se := by rw [show w ^ 3 = w * (w * w) by ring, hw]
  have hx3 : x ^ 3 = -(n 0 * w * se * a ^ 6) := by
    rw [hx_def]
    calc (-(n 0 * w * a ^ 2)) ^ 3 = -(n 0 ^ 3 * w ^ 3 * a ^ 6) := by ring
      _ = -(n 0 * w * se * a ^ 6) := by
          rw [hn3 0, hw3]
          ring
  have hx9 : x ^ 9 = -(n 0 * w * a ^ 18) := by
    have hwse2 : (w * se) ^ 2 = se := by
      have hw2 : w ^ 2 = se := by rw [sq]; exact hw
      have hse2 : se ^ 2 = 1 := by rw [sq]; exact hse
      rw [mul_pow, hw2, hse2, mul_one]
    have hwse3 : (w * se) ^ 3 = w := by
      calc (w * se) ^ 3 = (w * se) ^ 2 * (w * se) := by ring
        _ = se * (w * se) := by rw [hwse2]
        _ = w := by rw [show se * (w * se) = w * (se * se) by ring, hse, mul_one]
    calc x ^ 9 = (x ^ 3) ^ 3 := by ring
      _ = (-(n 0 * w * se * a ^ 6)) ^ 3 := by rw [hx3]
      _ = -(n 0 ^ 3 * (w * se) ^ 3 * a ^ 18) := by ring
      _ = -(n 0 * w * a ^ 18) := by
          rw [hn3 0, hwse3]
  have hx27 : x ^ 27 = se * x := by
    have h54 : a ^ 54 = a ^ 2 := by rw [show a ^ 54 = (a ^ 27) ^ 2 by ring, h27]
    calc x ^ 27 = (x ^ 9) ^ 3 := by ring
      _ = (-(n 0 * w * a ^ 18)) ^ 3 := by rw [hx9]
      _ = -(n 0 ^ 3 * w ^ 3 * a ^ 54) := by ring
      _ = -(n 0 * (w * se) * a ^ 2) := by rw [hn3 0, hw3, h54]
      _ = se * x := by rw [hx_def]; ring
  have hxsum : x + se * x ^ 3 + x ^ 9 = n 0 * w := by
    rw [hx3, hx9, hx_def]
    have e : se * (-(n 0 * w * se * a ^ 6)) = -(n 0 * w * a ^ 6) := by
      rw [show se * (-(n 0 * w * se * a ^ 6)) = -(n 0 * w * (se * se) * a ^ 6) by ring,
        hse]
      ring
    rw [e]
    linear_combination (-(n 0 * w)) * hasum
  have hW : n 0 * (lam * mu) + n 1 * (s 0 * t 0) * (lam * mu) ^ 3 +
      n 2 * (s 0 * s 1 * (t 0 * t 1)) * (lam * mu) ^ 9 = w := by
    rw [hxmulam, hr0, hrn2]
    calc n 0 * x + se * n 0 * x ^ 3 + n 0 * x ^ 9 =
          n 0 * (x + se * x ^ 3 + x ^ 9) := by ring
      _ = n 0 * (n 0 * w) := by rw [hxsum]
      _ = w := by
          rw [show n 0 * (n 0 * w) = (n 0 * n 0) * w by ring, hn0sq, one_mul]
  have hmu27 : mu ^ 27 = mu * (t 0 * t 1 * t 2) := by
    have h := hx27
    rw [← hxmulam] at h
    rw [mul_pow] at h
    rw [hlam] at h
    have h1 : lam * ((s 0 * s 1 * s 2) * mu ^ 27) = se * (lam * mu) := by
      rw [← h]
      ring
    have h2 : (s 0 * s 1 * s 2) * mu ^ 27 = se * mu := by
      refine mul_left_cancel₀ hlam0 ?_
      rw [h1]
      ring
    have h3 : mu ^ 27 * (s 0 * s 1 * s 2) = se * mu := by rw [← h2, mul_comm]
    calc mu ^ 27 = (mu ^ 27 * (s 0 * s 1 * s 2)) * (s 0 * s 1 * s 2) := by
          rw [mul_assoc, hS2, mul_one]
      _ = (se * mu) * (s 0 * s 1 * s 2) := by rw [h3]
      _ = mu * (se * (s 0 * s 1 * s 2)) := by ring
      _ = mu * (t 0 * t 1 * t 2) := by rw [← htprod]
  have hwne : w ≠ 0 := left_ne_zero_of_mul_eq_one (b := w * se) (by rw [← mul_assoc, hw, hse])
  have hw' : n 0 * (lam * mu) + n 1 * (s 0 * t 0) * (lam * mu) ^ 3 +
      n 2 * (s 0 * s 1 * (t 0 * t 1)) * (lam * mu) ^ 9 ≠ 0 := by
    rw [hW]
    exact hwne
  obtain ⟨ι', hι'inj, hι'a, hι'b, hι'c⟩ :=
    exists_heis_orbit_three X S ι hK hB hD hE hBX hDX hs ht hSB hSD hBB hDD hBD hBDi hEB hED
      hEinj hlam hmu27 hw'
  exact ⟨mu, ι', hι'inj, hι'a, hι'b, fun r => by simpa [hW] using hι'c r⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
