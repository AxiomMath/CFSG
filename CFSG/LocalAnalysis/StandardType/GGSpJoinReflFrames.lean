module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermBase
public import CFSG.LocalAnalysis.StandardType.GGSpFrameIso
public import CFSG.LocalAnalysis.StandardType.GGSpFrameOrbit
public import CFSG.LocalAnalysis.StandardType.GGSpJoinOrbitBound
public import CFSG.LocalAnalysis.StandardType.GGSpJoinCoxeterCard
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermGen
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import TauCeti.GroupTheory.ExponentPrime

public section

namespace CFSG.StandardType.SpJoinRefl

open CFSG.Open CFSG.StandardType.SpJoin CFSG.StandardType.SpCoord Multiplicative

section Helpers

private lemma tf_exists_pow_eq_of_ne_one {p : ℕ} (hp : p.Prime)
    {a b : Multiplicative (ZMod p)} (ha : a ≠ 1) : ∃ c : ℕ, a ^ c = b := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hA : a.toAdd ≠ 0 := fun h => ha (toAdd_eq_zero.mp h)
  refine ⟨(b.toAdd / a.toAdd).val, ?_⟩
  apply (Multiplicative.toAdd).injective
  rw [toAdd_pow, nsmul_eq_mul, ZMod.natCast_zmod_val]
  exact div_mul_cancel₀ b.toAdd hA

private lemma tf_mem_zpowers_of_supported {p N : ℕ} (hp : p.Prime)
    {u w : Fin N → Multiplicative (ZMod p)} (i0 : Fin N)
    (hu : ∀ i, i ≠ i0 → u i = 1) (hw : ∀ i, i ≠ i0 → w i = 1)
    (hui : u i0 ≠ 1) : w ∈ Subgroup.zpowers u := by
  obtain ⟨c, hc⟩ := tf_exists_pow_eq_of_ne_one hp hui
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨(c : ℤ), ?_⟩
  rw [zpow_natCast]
  funext i
  rw [Pi.pow_apply]
  by_cases hi : i = i0
  · subst hi; exact hc
  · rw [hu i hi, hw i hi, one_pow]

private lemma tf_exists_nontrivial_coord {p N : ℕ}
    {v : Fin N → Multiplicative (ZMod p)}
    (hv : ∀ i j, i ≠ j → v i = 1 ∨ v j = 1) (hv1 : v ≠ 1) :
    ∃ i0, v i0 ≠ 1 ∧ ∀ i, i ≠ i0 → v i = 1 := by
  obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 1 := by
    by_contra h
    push Not at h
    exact hv1 (funext fun i => h i)
  refine ⟨i0, hi0, fun i hi => ?_⟩
  rcases hv i i0 hi with h | h
  · exact h
  · exact absurd h hi0

private lemma tf_coordInv_apply_of_eq_one {N p : ℕ} (i : Fin N)
    {v : Fin N → Multiplicative (ZMod p)} (hv : v i = 1) :
    coordInv N p i v = v := by
  funext t
  rw [coordInv_apply, Function.update_apply]
  by_cases h : t = i
  · subst h; rw [if_pos rfl, hv, inv_one]
  · rw [if_neg h]

private lemma tf_pow_eq_one_of_zpow_neg_two_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {g : Multiplicative (ZMod p)} {i : ℤ} (h : g ^ (-(2*i)) = 1) : g ^ i = 1 := by
  have hg2 : ((g ^ i) : Multiplicative (ZMod p)) ^ 2 = 1 := by
    rw [← zpow_natCast (g ^ i) 2, ← zpow_mul]
    have h2 : g ^ (2 * i) = 1 := by
      have := congrArg Inv.inv h
      rwa [zpow_neg, inv_inv, inv_one] at this
    rw [show i * (↑(2:ℕ) : ℤ) = 2 * i by ring, h2]
  have hgp : ((g ^ i) : Multiplicative (ZMod p)) ^ p = 1 := by
    rw [← zpow_natCast (g ^ i) p, ← zpow_mul]
    have hg : g ^ p = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [show i * (↑p : ℤ) = (↑p : ℤ) * i by ring, zpow_mul, zpow_natCast, hg, one_zpow]
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
  exact (pow_eq_one_iff_of_coprime hcop).mp ⟨hg2, hgp⟩

private lemma tf_coords_zpowers_eq {p N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X Y Z W : Fin N → Multiplicative (ZMod p)}
    (σ : MulAut (Fin N → Multiplicative (ZMod p)))
    (hXax : ∀ i j, i ≠ j → X i = 1 ∨ X j = 1)
    (hYax : ∀ i j, i ≠ j → Y i = 1 ∨ Y j = 1)
    (hWax : ∀ i j, i ≠ j → W i = 1 ∨ W j = 1)
    (hX1 : X ≠ 1)
    (hYX : Y ∉ Subgroup.zpowers X)
    (hZX : Z ∉ Subgroup.zpowers X)
    (hZD : Z ∈ Subgroup.closure ({X, Y} : Set (Fin N → Multiplicative (ZMod p))))
    (hσX : σ X = X) (hσY : σ Y = W) (hσZ : σ Z = Z⁻¹) :
    Subgroup.zpowers Z = Subgroup.zpowers Y := by
  obtain ⟨a, hXa, hXoff⟩ := tf_exists_nontrivial_coord hXax hX1
  have hY1 : Y ≠ 1 := fun h => hYX (by rw [h]; exact Subgroup.one_mem _)
  obtain ⟨b, hYb, hYoff⟩ := tf_exists_nontrivial_coord hYax hY1
  have hab : a ≠ b := by
    intro hab'
    apply hYX
    refine tf_mem_zpowers_of_supported hp a hXoff ?_ hXa
    intro i hi
    exact hYoff i (fun hib => hi (hib.trans hab'.symm))
  have hrep : ∃ i j : ℤ, Z = X ^ i * Y ^ j := by
    let T : Subgroup (Fin N → Multiplicative (ZMod p)) :=
      { carrier := {w | ∃ i j : ℤ, w = X ^ i * Y ^ j}
        one_mem' := ⟨0, 0, by simp⟩
        mul_mem' := by
          rintro w w' ⟨i, j, rfl⟩ ⟨i', j', rfl⟩
          exact ⟨i + i', j + j', by rw [zpow_add, zpow_add]; ac_rfl⟩
        inv_mem' := by
          rintro w ⟨i, j, rfl⟩
          exact ⟨-i, -j, by rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]; ac_rfl⟩ }
    have hXmem : X ∈ T := ⟨1, 0, by simp⟩
    have hYmem : Y ∈ T := ⟨0, 1, by simp⟩
    have hle : Subgroup.closure ({X, Y} : Set (Fin N → Multiplicative (ZMod p))) ≤ T := by
      rw [Subgroup.closure_le]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact hXmem
      · exact hYmem
    exact hle hZD
  obtain ⟨i, j, hZrep⟩ := hrep
  have hYj1 : Y ^ j ≠ 1 := by
    intro hj
    apply hZX
    rw [hZrep, hj, mul_one]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers X) i
  have hβj : (Y b) ^ j ≠ 1 := by
    intro h
    apply hYj1
    funext t
    rw [Pi.pow_apply, Pi.one_apply]
    by_cases ht : t = b
    · subst ht; exact h
    · rw [hYoff t ht, one_zpow]
  have hWj : W ^ j = X ^ (-(2*i)) * Y ^ (-j) := by
    have h1 : σ Z = X ^ i * W ^ j := by
      rw [hZrep, map_mul, map_zpow, map_zpow, hσX, hσY]
    have h2 : Z⁻¹ = X ^ (-i) * Y ^ (-j) := by
      rw [hZrep, mul_inv_rev, ← zpow_neg, ← zpow_neg]
      ac_rfl
    have h4 : X ^ i * W ^ j = X ^ (-i) * Y ^ (-j) := by
      rw [← h1, hσZ, h2]
    calc W ^ j
        = (X ^ (-i) * X ^ i) * W ^ j := by rw [← zpow_add, neg_add_cancel, zpow_zero, one_mul]
      _ = X ^ (-i) * (X ^ i * W ^ j) := by rw [mul_assoc]
      _ = X ^ (-i) * (X ^ (-i) * Y ^ (-j)) := by rw [h4]
      _ = (X ^ (-i) * X ^ (-i)) * Y ^ (-j) := by rw [mul_assoc]
      _ = X ^ (-(2*i)) * Y ^ (-j) := by
            congr 1
            rw [← zpow_add]
            congr 1
            ring
  have hWjax : ∀ r s, r ≠ s → (W ^ j) r = 1 ∨ (W ^ j) s = 1 := by
    intro r s hrs
    rw [Pi.pow_apply, Pi.pow_apply]
    rcases hWax r s hrs with h | h
    · left; rw [h, one_zpow]
    · right; rw [h, one_zpow]
  have hWjb : (W ^ j) b = X b ^ (-(2*i)) * Y b ^ (-j) := by
    rw [hWj, Pi.mul_apply, Pi.pow_apply, Pi.pow_apply]
  have hWjb_ne : (W ^ j) b ≠ 1 := by
    intro h
    apply hβj
    have hh := h
    rw [hWjb, hXoff b (Ne.symm hab), one_zpow, one_mul] at hh
    rwa [zpow_neg, inv_eq_one] at hh
  have hWja_one : (W ^ j) a = 1 := by
    rcases hWjax a b hab with h | h
    · exact h
    · exact absurd h hWjb_ne
  have hα : (X a) ^ (-(2*i)) = 1 := by
    have hWja : (W ^ j) a = X a ^ (-(2*i)) * Y a ^ (-j) := by
      rw [hWj, Pi.mul_apply, Pi.pow_apply, Pi.pow_apply]
    rw [hWja_one, hYoff a hab, one_zpow, mul_one] at hWja
    exact hWja.symm
  have hXi1 : X ^ i = 1 := by
    funext t
    rw [Pi.pow_apply, Pi.one_apply]
    by_cases ht : t = a
    · subst ht
      exact tf_pow_eq_one_of_zpow_neg_two_mul hp hp2 hα
    · rw [hXoff t ht, one_zpow]
  have hZY : Z = Y ^ j := by rw [hZrep, hXi1, one_mul]
  apply le_antisymm
  · rw [Subgroup.zpowers_le, hZY]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers Y) j
  · rw [Subgroup.zpowers_le, hZY]
    have hYj_supp : ∀ i, i ≠ b → (Y ^ j) i = 1 := by
      intro i hi; rw [Pi.pow_apply, hYoff i hi, one_zpow]
    have hYj_b : (Y ^ j) b ≠ 1 := by
      rw [Pi.pow_apply]; exact hβj
    exact tf_mem_zpowers_of_supported hp b hYj_supp hYoff hYj_b

end Helpers

section Frames

variable {G : Type} [Group G] [Finite G]

private lemma fr_inv_ne_self {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Multiplicative (ZMod p)} (ha : a ≠ 1) : a⁻¹ ≠ a := by
  intro h
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hsq : a * a = 1 := by
    nth_rewrite 2 [h.symm]
    exact mul_inv_cancel a
  have h2 : Multiplicative.toAdd (a ^ 2) = 0 := by
    rw [show a ^ 2 = 1 by rw [sq]; exact hsq, toAdd_one]
  rw [toAdd_pow, nsmul_eq_mul] at h2
  have hsum : Multiplicative.toAdd a + Multiplicative.toAdd a = 0 := by
    simpa [two_mul] using h2
  exact ha (by rw [← toAdd_eq_zero]; exact (ZMod.add_self_eq_zero_iff_eq_zero hpodd).mp hsum)

private lemma fr_axial_support {N p : ℕ} {v : Fin N → Multiplicative (ZMod p)}
    (hv : ∀ i j, i ≠ j → v i = 1 ∨ v j = 1) (hv1 : v ≠ 1) :
    ∃ i0, v i0 ≠ 1 ∧ ∀ i, i ≠ i0 → v i = 1 := by
  obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 1 := by
    by_contra h
    push_neg at h
    exact hv1 (funext fun i => h i)
  refine ⟨i0, hi0, fun i hi => ?_⟩
  rcases hv i i0 hi with h | h
  · exact h
  · exact absurd h hi0

private lemma fr_coordPerm_apply_axial {N p : ℕ} (a c : Fin N)
    {X : Fin N → Multiplicative (ZMod p)} (hXoff : ∀ i, i ≠ a → X i = 1) :
    coordPerm N p (Equiv.swap a c) X = Pi.mulSingle c (X a) := by
  funext t
  rw [coordPerm_apply, Equiv.symm_swap, Pi.mulSingle_apply]
  by_cases ht : t = c
  · subst ht
    simp [Equiv.swap_apply_right]
  · have hne : Equiv.swap a c t ≠ a := by
      intro h
      apply ht
      have h2 := congrArg (Equiv.swap a c) h
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at h2
    rw [if_neg ht, hXoff _ hne]

private lemma fr_coordInv_mulSingle {N p : ℕ} (c : Fin N) (γ : Multiplicative (ZMod p)) :
    coordInv N p c (Pi.mulSingle c γ) = Pi.mulSingle c γ⁻¹ := by
  funext t
  by_cases ht : t = c <;> simp [coordInv_apply, Pi.mulSingle_apply, ht]

private lemma fr_phi_mem_orbit {p m : ℕ}
    {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)}
    (Φ : (Fin (m + 1) → Multiplicative (ZMod p)) ≃* ↥Bs)
    (hΦ : ∀ h ∈ spSignedGroup (m + 1) p, ∃ ψ ∈ A, ∀ a, ψ (Φ a) = Φ (h a))
    {x : G} (hx : x ∈ Bs) {X : Fin (m + 1) → Multiplicative (ZMod p)}
    (hX : Φ X = ⟨x, hx⟩) {h : Equiv.Perm (Fin (m + 1) → Multiplicative (ZMod p))}
    (hh : h ∈ spSignedGroup (m + 1) p) (u : Fin (m + 1) → Multiplicative (ZMod p))
    (hu : h X = u) : Φ u ∈ MulAction.orbit A (⟨x, hx⟩ : ↥Bs) := by
  obtain ⟨ψ, hψA, hψ⟩ := hΦ h hh
  refine MulAction.mem_orbit_iff.mpr ⟨⟨ψ, hψA⟩, ?_⟩
  rw [Subgroup.smul_def, MulAut.smul_def]
  show ψ ⟨x, hx⟩ = Φ u
  rw [← hX, hψ X, hu]

private lemma fr_two_mul_le_card_orbit {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m)
    {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)}
    (hA : GGWeylOfType p (CoxeterMatrix.B (m + 1)) A)
    (Φ : (Fin (m + 1) → Multiplicative (ZMod p)) ≃* ↥Bs)
    (hΦ : ∀ h ∈ spSignedGroup (m + 1) p, ∃ ψ ∈ A, ∀ a, ψ (Φ a) = Φ (h a))
    {H : Subgroup (MulAut ↥Bs)} (hHA : H ≤ A) {x : G} (hx : x ∈ Bs)
    (hfix : ∀ ψ ∈ H, ((ψ ⟨x, hx⟩ : ↥Bs) : G) = x)
    (hH : 2 ^ m * m.factorial ≤ Nat.card H) (hx1 : x ≠ 1) :
    2 * (m + 1) ≤ Nat.card (MulAction.orbit A (⟨x, hx⟩ : ↥Bs)) := by
  classical
  let X : Fin (m + 1) → Multiplicative (ZMod p) := Φ.symm ⟨x, hx⟩
  have hX : Φ X = ⟨x, hx⟩ := Φ.apply_symm_apply _
  have hX1 : X ≠ 1 := by
    intro hXe
    apply hx1
    have hsub : (⟨x, hx⟩ : ↥Bs) = 1 := by rw [← hX, hXe, map_one]
    have := congrArg (fun b : ↥Bs => (b : G)) hsub
    simpa using this
  have hXax : ∀ i j, i ≠ j → X i = 1 ∨ X j = 1 :=
    fun i j hij => SpFrame.coord_eq_one_of_fixed hp hp2 hm hA Φ hΦ hHA hx hfix hH hij
  obtain ⟨a, hXa, hXoff⟩ := fr_axial_support hXax hX1
  have hα : X a ≠ 1 := hXa
  have hαne : X a ≠ (X a)⁻¹ := fun hh => fr_inv_ne_self hp hp2 hα hh.symm
  let vf : Fin (m + 1) × Bool → Fin (m + 1) → Multiplicative (ZMod p) :=
    fun q => Pi.mulSingle q.1 (if q.2 then (X a)⁻¹ else X a)
  have hvf_self : ∀ q, vf q q.1 = if q.2 then (X a)⁻¹ else X a := by
    intro q; simp [vf]
  have hvf_ne : ∀ q, vf q q.1 ≠ 1 := by
    intro q
    rw [hvf_self]
    cases q.2
    · simpa using hα
    · simpa using inv_ne_one.mpr hα
  have hmem : ∀ q, Φ (vf q) ∈ MulAction.orbit A (⟨x, hx⟩ : ↥Bs) := by
    rintro ⟨c, b⟩
    have hpermp : coordPerm (m + 1) p (Equiv.swap a c) ∈ spSignedGroup (m + 1) p :=
      coordPerm_mem_spSignedGroup _
    cases b
    · refine fr_phi_mem_orbit Φ hΦ hx hX hpermp (vf (c, false)) ?_
      rw [fr_coordPerm_apply_axial a c hXoff]
      simp [vf]
    · have hpermi : coordInv (m + 1) p c ∈ spSignedGroup (m + 1) p :=
        coordInv_mem_spSignedGroup c
      have hperm : coordInv (m + 1) p c * coordPerm (m + 1) p (Equiv.swap a c) ∈
          spSignedGroup (m + 1) p := Subgroup.mul_mem _ hpermi hpermp
      refine fr_phi_mem_orbit Φ hΦ hx hX hperm (vf (c, true)) ?_
      rw [Equiv.Perm.mul_apply, fr_coordPerm_apply_axial a c hXoff, fr_coordInv_mulSingle]
      simp [vf]
  let F : Fin (m + 1) × Bool → MulAction.orbit A (⟨x, hx⟩ : ↥Bs) :=
    fun q => ⟨Φ (vf q), hmem q⟩
  have hF : Function.Injective F := by
    rintro ⟨c, b⟩ ⟨c', b'⟩ heq
    have hv : vf (c, b) = vf (c', b') := Φ.injective (Subtype.ext_iff.mp heq)
    have hc : c = c' := by
      by_contra hne
      have h := congrFun hv c
      have h1 : vf (c', b') c = 1 := Pi.mulSingle_eq_of_ne hne _
      rw [h1] at h
      exact hvf_ne (c, b) h
    have hb : b = b' := by
      have h := congrFun hv c
      rw [hc, hvf_self (c', b), hvf_self (c', b')] at h
      cases b <;> cases b' <;> simp_all [hαne]
    exact Prod.ext hc hb
  have hcarddom : Nat.card (Fin (m + 1) × Bool) = 2 * (m + 1) := by
    rw [Nat.card_prod, Nat.card_fin, Nat.card_eq_fintype_card, Fintype.card_bool]
    ring
  calc 2 * (m + 1) = Nat.card (Fin (m + 1) × Bool) := hcarddom.symm
    _ ≤ Nat.card (MulAction.orbit A (⟨x, hx⟩ : ↥Bs)) := Nat.card_le_card_of_injective F hF

private lemma fr_card_stabilizer_le {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m)
    {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)}
    (hA : GGWeylOfType p (CoxeterMatrix.B (m + 1)) A)
    (Φ : (Fin (m + 1) → Multiplicative (ZMod p)) ≃* ↥Bs)
    (hΦ : ∀ h ∈ spSignedGroup (m + 1) p, ∃ ψ ∈ A, ∀ a, ψ (Φ a) = Φ (h a))
    {H : Subgroup (MulAut ↥Bs)} (hHA : H ≤ A) {x : G} (hx : x ∈ Bs)
    (hfix : ∀ ψ ∈ H, ((ψ ⟨x, hx⟩ : ↥Bs) : G) = x)
    (hH : 2 ^ m * m.factorial ≤ Nat.card H) (hx1 : x ≠ 1) :
    Nat.card (MulAction.stabilizer A (⟨x, hx⟩ : ↥Bs)) ≤ 2 ^ m * m.factorial := by
  have hob := fr_two_mul_le_card_orbit hp hp2 hm hA Φ hΦ hHA hx hfix hH hx1
  have hAcard : Nat.card A ≤ (2 * (m + 1)) * (2 ^ m * m.factorial) := by
    obtain ⟨e, -⟩ := hA
    calc Nat.card A = Nat.card (CoxeterMatrix.B (m + 1)).Group :=
          (Nat.card_congr e.toEquiv).symm
      _ ≤ 2 ^ (m + 1) * (m + 1).factorial := card_coxeterB_le (m + 1)
      _ = (2 * (m + 1)) * (2 ^ m * m.factorial) := by
          rw [pow_succ, Nat.factorial_succ]; ring
  have hos : Nat.card (MulAction.orbit A (⟨x, hx⟩ : ↥Bs)) *
      Nat.card (MulAction.stabilizer A (⟨x, hx⟩ : ↥Bs)) = Nat.card A := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup A (⟨x, hx⟩ : ↥Bs))
  have hcpos : 0 < 2 * (m + 1) := by omega
  have hchain : (2 * (m + 1)) * Nat.card (MulAction.stabilizer A (⟨x, hx⟩ : ↥Bs)) ≤
      (2 * (m + 1)) * (2 ^ m * m.factorial) := by
    calc (2 * (m + 1)) * Nat.card (MulAction.stabilizer A (⟨x, hx⟩ : ↥Bs))
        ≤ Nat.card (MulAction.orbit A (⟨x, hx⟩ : ↥Bs)) *
            Nat.card (MulAction.stabilizer A (⟨x, hx⟩ : ↥Bs)) :=
          Nat.mul_le_mul_right _ hob
      _ = Nat.card A := hos
      _ ≤ (2 * (m + 1)) * (2 ^ m * m.factorial) := hAcard
  exact Nat.le_of_mul_le_mul_left hchain hcpos

theorem mem_of_signedPerm_fixing {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m)
    {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)}
    (hA : GGWeylOfType p (CoxeterMatrix.B (m + 1)) A)
    (Φ : (Fin (m + 1) → Multiplicative (ZMod p)) ≃* ↥Bs)
    (hΦ : ∀ h ∈ spSignedGroup (m + 1) p, ∃ ψ ∈ A, ∀ a, ψ (Φ a) = Φ (h a))
    {H : Subgroup (MulAut ↥Bs)} (hHA : H ≤ A) {x : G} (hx : x ∈ Bs) (hx1 : x ≠ 1)
    (hfix : ∀ ψ ∈ H, ((ψ ⟨x, hx⟩ : ↥Bs) : G) = x) (hH : 2 ^ m * m.factorial ≤ Nat.card H)
    {h : Equiv.Perm (Fin (m + 1) → Multiplicative (ZMod p))} (hh : h ∈ spSignedGroup (m + 1) p)
    (hhx : h (Φ.symm ⟨x, hx⟩) = Φ.symm ⟨x, hx⟩) {ψ : MulAut ↥Bs}
    (hψ : ∀ a, ψ (Φ a) = Φ (h a)) : ψ ∈ H := by
  classical
  obtain ⟨ψ₀, hψ₀A, hψ₀⟩ := hΦ h hh
  have hψeq : ψ = ψ₀ := by
    apply MulEquiv.ext
    intro b
    rw [← Φ.apply_symm_apply b, hψ, hψ₀]
  have hfix0 : ψ₀ ⟨x, hx⟩ = (⟨x, hx⟩ : ↥Bs) := by
    have h := hψ₀ (Φ.symm ⟨x, hx⟩)
    rw [Φ.apply_symm_apply, hhx, Φ.apply_symm_apply] at h
    exact h
  have hmem0 : (⟨ψ₀, hψ₀A⟩ : ↥A) ∈ MulAction.stabilizer A (⟨x, hx⟩ : ↥Bs) := by
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, MulAut.smul_def]
    exact hfix0
  have hle : H.subgroupOf A ≤ MulAction.stabilizer A (⟨x, hx⟩ : ↥Bs) := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, MulAut.smul_def]
    exact Subtype.ext (hfix g.1 (Subgroup.mem_subgroupOf.mp hg))
  have hcardH : Nat.card H = Nat.card (H.subgroupOf A) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHA).toEquiv).symm
  have hcard : Nat.card (MulAction.stabilizer A (⟨x, hx⟩ : ↥Bs)) ≤ Nat.card (H.subgroupOf A) := by
    rw [← hcardH]
    exact (fr_card_stabilizer_le hp hp2 hm hA Φ hΦ hHA hx hfix hH hx1).trans hH
  have hstab : H.subgroupOf A = MulAction.stabilizer A (⟨x, hx⟩ : ↥Bs) :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  rw [hψeq]
  exact Subgroup.mem_subgroupOf.mp (by rw [hstab]; exact hmem0)

private lemma fr_inv_eq_self_iff {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Multiplicative (ZMod p)} : a⁻¹ = a ↔ a = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h, inv_one]⟩
  by_contra ha
  exact fr_inv_ne_self hp hp2 ha h

private lemma fr_exists_pow_eq_of_ne_one {p : ℕ} (hp : p.Prime)
    {a b : Multiplicative (ZMod p)} (ha : a ≠ 1) : ∃ c : ℕ, a ^ c = b := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hA : a.toAdd ≠ 0 := fun h => ha (toAdd_eq_zero.mp h)
  refine ⟨(b.toAdd / a.toAdd).val, ?_⟩
  apply (Multiplicative.toAdd).injective
  rw [toAdd_pow, nsmul_eq_mul, ZMod.natCast_zmod_val]
  exact div_mul_cancel₀ b.toAdd hA

private lemma fr_supported_zpowers {p N : ℕ} (hp : p.Prime)
    {u w : Fin N → Multiplicative (ZMod p)} (i0 : Fin N)
    (hu : ∀ i, i ≠ i0 → u i = 1) (hw : ∀ i, i ≠ i0 → w i = 1) (hui : u i0 ≠ 1) :
    w ∈ Subgroup.zpowers u := by
  obtain ⟨c, hc⟩ := fr_exists_pow_eq_of_ne_one hp hui
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨(c : ℤ), ?_⟩
  rw [zpow_natCast]
  funext i
  rw [Pi.pow_apply]
  by_cases hi : i = i0
  · subst hi; exact hc
  · rw [hu i hi, hw i hi, one_pow]

private lemma fr_zpowers_subtype {G : Type} [Group G] {Bs : Subgroup G} {a b : ↥Bs} :
    a ∈ Subgroup.zpowers b ↔ (a : G) ∈ Subgroup.zpowers (b : G) := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨k, ?_⟩
    have := congrArg (fun w : ↥Bs => (w : G)) hk
    simpa using this
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem eq_one_of_fixed_weylJoin {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n)
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) (hrank : Nat.card Bs = p ^ (n + 1))
    {A AL R : Subgroup (MulAut ↥Bs)} (hA : GGWeylOfType p (CoxeterMatrix.B (n + 1)) A)
    (hAL : AL ≤ A) {x y' : G} (hx : x ∈ Bs) (hy' : y' ∈ Bs)
    (hfx : ∀ ψ ∈ AL, ((ψ ⟨x, hx⟩ : ↥Bs) : G) = x)
    (hcL : 2 ^ n * n.factorial ≤ Nat.card AL)
    (hCR : ∀ b : ↥Bs, (∀ ψ ∈ R, ψ b = b) → (b : G) ∈ Subgroup.zpowers y')
    (hx1 : x ≠ 1) (hy'x : y' ∉ Subgroup.zpowers x) :
    ∀ b : ↥Bs, (∀ ψ ∈ AL ⊔ R, ψ b = b) → b = 1 := by
  intro b hbfix
  classical
  obtain ⟨Φ, hΦ⟩ := SpFrame.exists_frame_iso_of_weyl hp hp2 hBs (by omega : 1 ≤ n) hrank hA
  let X : Fin (n + 1) → Multiplicative (ZMod p) := Φ.symm ⟨x, hx⟩
  let B : Fin (n + 1) → Multiplicative (ZMod p) := Φ.symm b
  have hX : Φ X = ⟨x, hx⟩ := Φ.apply_symm_apply _
  have hB : Φ B = b := Φ.apply_symm_apply _
  have hX1 : X ≠ 1 := by
    intro hXe
    apply hx1
    have hsub : (⟨x, hx⟩ : ↥Bs) = 1 := by rw [← hX, hXe, map_one]
    have := congrArg (fun w : ↥Bs => (w : G)) hsub
    simpa using this
  have hXax : ∀ i j, i ≠ j → X i = 1 ∨ X j = 1 :=
    fun i j hij => SpFrame.coord_eq_one_of_fixed hp hp2 hn hA Φ hΦ hAL hx hfx hcL hij
  obtain ⟨a, hXa, hXoff⟩ := fr_axial_support hXax hX1
  have hBoff : ∀ c, c ≠ a → B c = 1 := by
    intro c hc
    have hhh : coordInv (n + 1) p c ∈ spSignedGroup (n + 1) p := coordInv_mem_spSignedGroup c
    have hhx : coordInv (n + 1) p c X = X := by
      funext t
      by_cases ht : t = c <;> simp [coordInv_apply, ht, hXoff c hc]
    obtain ⟨ψc, -, hψc⟩ := hΦ (coordInv (n + 1) p c) hhh
    have hψcAL : ψc ∈ AL :=
      mem_of_signedPerm_fixing hp hp2 hn hA Φ hΦ hAL hx hx1 hfx hcL hhh hhx hψc
    have hfixc : ψc b = b := hbfix ψc (Subgroup.mem_sup_left hψcAL)
    have h1 : coordInv (n + 1) p c B = B := by
      apply Φ.injective
      rw [← hψc B, hB]
      exact hfixc
    have h2 : (B c)⁻¹ = B c := by
      have := congrFun h1 c
      simp [coordInv_apply] at this
      exact this
    exact (fr_inv_eq_self_iff hp hp2).mp h2
  have hbR : ∀ ψ ∈ R, ψ b = b := fun ψ hψ => hbfix ψ (Subgroup.mem_sup_right hψ)
  have hbY : b ∈ Subgroup.zpowers (⟨y', hy'⟩ : ↥Bs) :=
    fr_zpowers_subtype.mpr (hCR b hbR)
  have hBz : B ∈ Subgroup.zpowers X := fr_supported_zpowers hp a hXoff hBoff hXa
  have hbX : b ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hBz
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨k, ?_⟩
    have hmap := congrArg Φ hk
    rwa [map_zpow, hX, hB] at hmap
  by_contra hbne
  have hxpow : (⟨x, hx⟩ : ↥Bs) ^ p = 1 := by
    apply Subtype.ext
    simpa using hBs.2 x hx
  have hy'pow : (⟨y', hy'⟩ : ↥Bs) ^ p = 1 := by
    apply Subtype.ext
    simpa using hBs.2 y' hy'
  have e1 : Subgroup.zpowers b = Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) :=
    TauCeti.zpowers_eq_zpowers_of_mem_zpowers hp hxpow hbne hbX
  have e2 : Subgroup.zpowers b = Subgroup.zpowers (⟨y', hy'⟩ : ↥Bs) :=
    TauCeti.zpowers_eq_zpowers_of_mem_zpowers hp hy'pow hbne hbY
  apply hy'x
  have hy'mem : (⟨y', hy'⟩ : ↥Bs) ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
    have hm : (⟨y', hy'⟩ : ↥Bs) ∈ Subgroup.zpowers b := by
      have h := Subgroup.mem_zpowers (⟨y', hy'⟩ : ↥Bs)
      rwa [← e2] at h
    rwa [e1] at hm
  exact fr_zpowers_subtype.mp hy'mem


theorem card_eq_two_pow_mul_factorial_of_frame {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n)
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) (hrank : Nat.card Bs = p ^ (n + 1))
    {A AL : Subgroup (MulAut ↥Bs)} (hA : GGWeylOfType p (CoxeterMatrix.B (n + 1)) A)
    (hAL : AL ≤ A) {x : G} (hx : x ∈ Bs) (hfx : ∀ ψ ∈ AL, ((ψ ⟨x, hx⟩ : ↥Bs) : G) = x)
    (hcL : 2 ^ n * n.factorial ≤ Nat.card AL) (hx1 : x ≠ 1) :
    Nat.card AL = 2 ^ n * n.factorial := by
  obtain ⟨Φ, hΦ⟩ := SpFrame.exists_frame_iso_of_weyl hp hp2 hBs (by omega : 1 ≤ n) hrank hA
  have hle : AL.subgroupOf A ≤ MulAction.stabilizer A (⟨x, hx⟩ : ↥Bs) := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, MulAut.smul_def]
    exact Subtype.ext (hfx g.1 (Subgroup.mem_subgroupOf.mp hg))
  have h1 : Nat.card (AL.subgroupOf A) ≤
      Nat.card (MulAction.stabilizer A (⟨x, hx⟩ : ↥Bs)) := Subgroup.card_le_of_le hle
  have hcardAL : Nat.card AL = Nat.card (AL.subgroupOf A) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv).symm
  have h2 := fr_card_stabilizer_le hp hp2 hn hA Φ hΦ hAL hx hfx hcL hx1
  exact le_antisymm (by rw [hcardAL]; exact h1.trans h2) hcL

private lemma fr_coordPerm_mul {N p : ℕ} (σ : Equiv.Perm (Fin N))
    (u v : Fin N → Multiplicative (ZMod p)) :
    coordPerm N p σ (u * v) = coordPerm N p σ u * coordPerm N p σ v := by
  funext t; simp [coordPerm_apply, Pi.mul_apply]

private lemma fr_coordPerm_mulSingle {N p : ℕ} (σ : Equiv.Perm (Fin N))
    (i : Fin N) (γ : Multiplicative (ZMod p)) :
    coordPerm N p σ (Pi.mulSingle i γ) = Pi.mulSingle (σ i) γ := by
  funext t
  rw [coordPerm_apply, Pi.mulSingle_apply, Pi.mulSingle_apply]
  have hiff : σ.symm t = i ↔ t = σ i := Equiv.symm_apply_eq σ
  by_cases ht : t = σ i
  · rw [if_pos (hiff.mpr ht), if_pos ht]
  · rw [if_neg (fun h => ht (hiff.mp h)), if_neg ht]

private lemma fr_axial_eq_mulSingle {N p : ℕ} {v : Fin N → Multiplicative (ZMod p)}
    {i : Fin N} (hv : ∀ j, j ≠ i → v j = 1) : v = Pi.mulSingle i (v i) := by
  funext t
  by_cases ht : t = i <;> simp [Pi.mulSingle_apply, ht, hv]

private lemma fr_coordInv_two {N p : ℕ} {a c : Fin N} (hca : c ≠ a)
    (γ δ : Multiplicative (ZMod p)) :
    coordInv N p c (Pi.mulSingle a γ * Pi.mulSingle c δ) =
      Pi.mulSingle a γ * Pi.mulSingle c δ⁻¹ := by
  funext t
  rw [coordInv_apply]
  by_cases ht : t = c
  · subst ht
    rw [Function.update_apply, if_pos rfl]
    simp [Pi.mul_apply, Pi.mulSingle_apply, hca]
  · rw [Function.update_of_ne ht]
    by_cases ha : t = a
    · subst ha
      simp [Pi.mul_apply, Pi.mulSingle_apply, ht, hca]
    · simp [Pi.mul_apply, Pi.mulSingle_apply, ht, ha]

private lemma fr_sgnAut_eq_coordInv (k p : ℕ) (i : Fin k) :
    sgnAut (p := p) i = coordInv k p i := by
  ext f
  rfl

private lemma fr_permAut_eq_coordPerm (k p : ℕ) (σ : Equiv.Perm (Fin k)) :
    permAut (p := p) σ = coordPerm k p σ := by
  ext f
  rfl

private lemma fr_congr_apply {p N : ℕ} {Bs : Subgroup G}
    (Φ : (Fin N → Multiplicative (ZMod p)) ≃* ↥Bs)
    (u : MulAut (Fin N → Multiplicative (ZMod p)))
    (z : Fin N → Multiplicative (ZMod p)) :
    (MulAut.congr Φ u) (Φ z) = Φ (u z) := by
  rw [MulAut.congr_apply]
  simp [MulEquiv.trans_apply]

private lemma fr_isReflection_congr {p N : ℕ} {Bs : Subgroup G}
    (Φ : (Fin N → Multiplicative (ZMod p)) ≃* ↥Bs)
    {u : MulAut (Fin N → Multiplicative (ZMod p))}
    (hu2 : u ^ 2 = 1)
    (hufix : Nat.card {f : Fin N → Multiplicative (ZMod p) // u f = f} * p =
      Nat.card (Fin N → Multiplicative (ZMod p))) :
    GGIsReflection p (MulAut.congr Φ u) := by
  constructor
  · rw [← map_pow, hu2, map_one]
  · have heq : Nat.card {b : ↥Bs // MulAut.congr Φ u b = b} =
        Nat.card {f : Fin N → Multiplicative (ZMod p) // u f = f} := by
      apply Nat.card_congr
      refine
        { toFun := fun b => ⟨Φ.symm b.1, ?_⟩
          invFun := fun f => ⟨Φ f.1, ?_⟩
          left_inv := fun b => by apply Subtype.ext; simp
          right_inv := fun f => by apply Subtype.ext; simp }
      · apply Φ.injective
        rw [← fr_congr_apply Φ u (Φ.symm b.1), Φ.apply_symm_apply]
        exact b.2
      · rw [fr_congr_apply, f.2]
    rw [heq, ← Nat.card_congr Φ.toEquiv]
    exact hufix

private lemma fr_orderOf_sgnAut_mul_permAut_swap {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {c d : Fin k} (hcd : c ≠ d) :
    orderOf (sgnAut c * permAut (Equiv.swap c d) :
      MulAut (Fin k → Multiplicative (ZMod p))) = 4 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let w : MulAut (Fin k → Multiplicative (ZMod p)) := sgnAut c * permAut (Equiv.swap c d)
  have hwc : ∀ a : Multiplicative (ZMod p),
      w (Pi.mulSingle c a) = Pi.mulSingle d a := by
    intro a
    simp only [w, MulAut.mul_apply, permAut_mulSingle, Equiv.swap_apply_left,
      sgnAut_mulSingle_of_ne (Ne.symm hcd)]
  have hwd : ∀ a : Multiplicative (ZMod p),
      w (Pi.mulSingle d a) = Pi.mulSingle c a⁻¹ := by
    intro a
    simp only [w, MulAut.mul_apply, permAut_mulSingle, Equiv.swap_apply_right,
      sgnAut_mulSingle_self, Pi.mulSingle_inv]
  have hwi : ∀ (i : Fin k), i ≠ c → i ≠ d → ∀ a : Multiplicative (ZMod p),
      w (Pi.mulSingle i a) = Pi.mulSingle i a := by
    intro i hic hid a
    simp only [w, MulAut.mul_apply, permAut_mulSingle,
      Equiv.swap_apply_of_ne_of_ne hic hid, sgnAut_mulSingle_of_ne hic]
  have hw2eq : w ^ 2 = sgnAut c * sgnAut d := by
    have hhom : (w ^ 2).toMonoidHom =
        (sgnAut c * sgnAut d : MulAut (Fin k → Multiplicative (ZMod p))).toMonoidHom := by
      apply hom_ext_mulSingle
      intro i
      change (w ^ 2) (Pi.mulSingle i (ofAdd 1)) =
        (sgnAut c * sgnAut d : MulAut (Fin k → Multiplicative (ZMod p)))
          (Pi.mulSingle i (ofAdd 1))
      by_cases hic : i = c
      · subst hic
        rw [pow_two, MulAut.mul_apply, hwc (ofAdd 1), hwd (ofAdd 1), MulAut.mul_apply,
          sgnAut_mulSingle_of_ne hcd, sgnAut_mulSingle_self, Pi.mulSingle_inv]
      · by_cases hid : i = d
        · subst hid
          rw [pow_two, MulAut.mul_apply, hwd (ofAdd 1), hwc (ofAdd 1)⁻¹, MulAut.mul_apply,
            sgnAut_mulSingle_self, ← Pi.mulSingle_inv, sgnAut_mulSingle_of_ne (Ne.symm hcd)]
        · rw [pow_two, MulAut.mul_apply, hwi i hic hid, hwi i hic hid, MulAut.mul_apply,
            sgnAut_mulSingle_of_ne hid, sgnAut_mulSingle_of_ne hic]
    exact MulEquiv.ext (fun f => DFunLike.congr_fun hhom f)
  have hw4 : w ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hw2eq]
    calc (sgnAut c * sgnAut d : MulAut _) ^ 2
        = (sgnAut c * sgnAut d) * (sgnAut c * sgnAut d) := by rw [sq]
      _ = sgnAut c * (sgnAut d * sgnAut c) * sgnAut d := by group
      _ = sgnAut c * (sgnAut c * sgnAut d) * sgnAut d := by rw [sgnAut_mul_comm c d]
      _ = (sgnAut c * sgnAut c) * (sgnAut d * sgnAut d) := by group
      _ = 1 := by rw [← pow_two, sgnAut_sq, ← pow_two, sgnAut_sq, mul_one]
  have hw2ne : w ^ 2 ≠ 1 := by
    have hne1 : (ofAdd (1 : ZMod p))⁻¹ ≠ ofAdd 1 :=
      fr_inv_ne_self hp hp2 (by
        intro hh
        have h1 := congrArg Multiplicative.toAdd hh
        simp only [toAdd_one, toAdd_ofAdd] at h1
        exact hp.not_dvd_one ((ZMod.natCast_eq_zero_iff 1 p).mp (by simpa using h1)))
    intro h
    have h1 : (w ^ 2) (Pi.mulSingle c (ofAdd 1)) =
        (1 : MulAut (Fin k → Multiplicative (ZMod p))) (Pi.mulSingle c (ofAdd 1)) := by
      rw [h]
    rw [MulAut.one_apply, pow_two, MulAut.mul_apply, hwc (ofAdd 1), hwd (ofAdd 1)] at h1
    exact hne1 (Pi.mulSingle_injective c h1)
  have hdiv : orderOf w ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hw4
  have hndiv2 : ¬ orderOf w ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one]; exact hw2ne
  have hge : 1 ≤ orderOf w := Nat.pos_of_dvd_of_pos hdiv (by norm_num)
  have hle : orderOf w ≤ 4 := Nat.le_of_dvd (by norm_num) hdiv
  have hnot1 : orderOf w ≠ 1 := by
    intro h; exact hndiv2 (by rw [h]; norm_num)
  have hnot2 : orderOf w ≠ 2 := by
    intro h; exact hndiv2 (by rw [h])
  have hnot3 : orderOf w ≠ 3 := by
    intro h; exact absurd (h ▸ hdiv) (by norm_num)
  have hord : orderOf w = 4 := by omega
  change orderOf (sgnAut c * permAut (Equiv.swap c d)) = 4
  rw [← hord]

theorem exists_order_four_of_frame {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n)
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) (hrank : Nat.card Bs = p ^ (n + 1))
    {A AL : Subgroup (MulAut ↥Bs)} (hA : GGWeylOfType p (CoxeterMatrix.B (n + 1)) A)
    (hAL : AL ≤ A) {x : G} (hx : x ∈ Bs) (hfx : ∀ ψ ∈ AL, ((ψ ⟨x, hx⟩ : ↥Bs) : G) = x)
    (hcL : 2 ^ n * n.factorial ≤ Nat.card AL) (hx1 : x ≠ 1) :
    ∃ t ∈ AL, ∃ s ∈ AL, GGIsReflection p t ∧ GGIsReflection p s ∧ orderOf (t * s) = 4 := by
  classical
  obtain ⟨Φ, hΦ⟩ := SpFrame.exists_frame_iso_of_weyl hp hp2 hBs (by omega : 1 ≤ n) hrank hA
  let X : Fin (n + 1) → Multiplicative (ZMod p) := Φ.symm ⟨x, hx⟩
  have hX : Φ X = ⟨x, hx⟩ := Φ.apply_symm_apply _
  have hX1 : X ≠ 1 := by
    intro hXe
    apply hx1
    have hsub : (⟨x, hx⟩ : ↥Bs) = 1 := by rw [← hX, hXe, map_one]
    have := congrArg (fun w : ↥Bs => (w : G)) hsub
    simpa using this
  have hXax : ∀ i j, i ≠ j → X i = 1 ∨ X j = 1 :=
    fun i j hij => SpFrame.coord_eq_one_of_fixed hp hp2 hn hA Φ hΦ hAL hx hfx hcL hij
  obtain ⟨a, -, hXoff⟩ := fr_axial_support hXax hX1
  obtain ⟨c, hca, -⟩ := coord_exists_ne_ne (k := n + 1) (by omega : 3 ≤ n + 1) a a
  obtain ⟨d, hda, hdc⟩ := coord_exists_ne_ne (k := n + 1) (by omega : 3 ≤ n + 1) a c
  have hcd : c ≠ d := Ne.symm hdc
  have hCsg : (sgnAut (p := p) c : Equiv.Perm (Fin (n + 1) → Multiplicative (ZMod p)))
      ∈ spSignedGroup (n + 1) p := by
    rw [fr_sgnAut_eq_coordInv]
    exact coordInv_mem_spSignedGroup c
  have hCfix : (sgnAut (p := p) c : Equiv.Perm (Fin (n + 1) → Multiplicative (ZMod p))) X =
      X := by
    rw [fr_sgnAut_eq_coordInv]
    funext j
    by_cases hj : j = c <;> simp [coordInv_apply, hj, hXoff c hca]
  obtain ⟨t, -, htψ⟩ :=
    hΦ (sgnAut (p := p) c : Equiv.Perm (Fin (n + 1) → Multiplicative (ZMod p))) hCsg
  have htAL : t ∈ AL :=
    mem_of_signedPerm_fixing hp hp2 hn hA Φ hΦ hAL hx hx1 hfx hcL hCsg hCfix htψ
  have ht_eq : t = MulAut.congr Φ (sgnAut (p := p) c) := by
    apply MulEquiv.ext
    intro b
    rw [← Φ.apply_symm_apply b, fr_congr_apply]
    exact htψ (Φ.symm b)
  have hDsg : (permAut (p := p) (Equiv.swap c d) :
      Equiv.Perm (Fin (n + 1) → Multiplicative (ZMod p))) ∈ spSignedGroup (n + 1) p := by
    rw [fr_permAut_eq_coordPerm]
    exact coordPerm_mem_spSignedGroup _
  have hDfix : (permAut (p := p) (Equiv.swap c d) :
      Equiv.Perm (Fin (n + 1) → Multiplicative (ZMod p))) X = X := by
    rw [fr_permAut_eq_coordPerm, fr_axial_eq_mulSingle hXoff, fr_coordPerm_mulSingle,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hca) (Ne.symm hda)]
  obtain ⟨s, -, hsψ⟩ :=
    hΦ (permAut (p := p) (Equiv.swap c d) :
      Equiv.Perm (Fin (n + 1) → Multiplicative (ZMod p))) hDsg
  have hsAL : s ∈ AL :=
    mem_of_signedPerm_fixing hp hp2 hn hA Φ hΦ hAL hx hx1 hfx hcL hDsg hDfix hsψ
  have hs_eq : s = MulAut.congr Φ (permAut (p := p) (Equiv.swap c d)) := by
    apply MulEquiv.ext
    intro b
    rw [← Φ.apply_symm_apply b, fr_congr_apply]
    exact hsψ (Φ.symm b)
  have ht_refl : GGIsReflection p t := by
    rw [ht_eq]
    exact fr_isReflection_congr Φ (sgnAut_sq c) (card_fix_sgnAut hp hp2 c)
  have hs_refl : GGIsReflection p s := by
    rw [hs_eq]
    exact fr_isReflection_congr Φ (permAut_swap_sq c d) (card_fix_permAut_swap hp hp2 hcd)
  have hts_eq : t * s = MulAut.congr Φ
      (sgnAut (p := p) c * permAut (p := p) (Equiv.swap c d)) := by
    rw [ht_eq, hs_eq, ← map_mul]
  have hord : orderOf (t * s) = 4 := by
    rw [hts_eq, MulEquiv.orderOf_eq]
    exact fr_orderOf_sgnAut_mul_permAut_swap hp hp2 hcd
  exact ⟨t, htAL, s, hsAL, ht_refl, hs_refl, hord⟩

theorem two_mul_le_card_orbit_of_frame {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n)
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) (hrank : Nat.card Bs = p ^ (n + 1))
    {A AL AK : Subgroup (MulAut ↥Bs)} (hA : GGWeylOfType p (CoxeterMatrix.B (n + 1)) A)
    (hAL : AL ≤ A) (hAK : AK ≤ A) {x y y' : G} (hx : x ∈ Bs) (hy : y ∈ Bs) (hy' : y' ∈ Bs)
    (hfx : ∀ ψ ∈ AL, ((ψ ⟨x, hx⟩ : ↥Bs) : G) = x)
    (hfy : ∀ ψ ∈ AK, ((ψ ⟨y, hy⟩ : ↥Bs) : G) = y)
    (hcL : 2 ^ n * n.factorial ≤ Nat.card AL) (hcK : 2 ^ n * n.factorial ≤ Nat.card AK)
    (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x) (hy'x : y' ∉ Subgroup.zpowers x)
    (hy'D : y' ∈ Subgroup.closure ({x, y} : Set G)) :
    2 * n ≤ Nat.card (MulAction.orbit AL (⟨y', hy'⟩ : ↥Bs)) := by
  classical
  obtain ⟨Φ, hΦ⟩ := SpFrame.exists_frame_iso_of_weyl hp hp2 hBs (by omega : 1 ≤ n) hrank hA
  let X : Fin (n + 1) → Multiplicative (ZMod p) := Φ.symm ⟨x, hx⟩
  let Y : Fin (n + 1) → Multiplicative (ZMod p) := Φ.symm ⟨y, hy⟩
  let Z : Fin (n + 1) → Multiplicative (ZMod p) := Φ.symm ⟨y', hy'⟩
  have hX : Φ X = ⟨x, hx⟩ := Φ.apply_symm_apply _
  have hY : Φ Y = ⟨y, hy⟩ := Φ.apply_symm_apply _
  have hZ : Φ Z = ⟨y', hy'⟩ := Φ.apply_symm_apply _
  have hX1 : X ≠ 1 := by
    intro hXe
    apply hx1
    have hsub : (⟨x, hx⟩ : ↥Bs) = 1 := by rw [← hX, hXe, map_one]
    have := congrArg (fun w : ↥Bs => (w : G)) hsub
    simpa using this
  have hY1 : Y ≠ 1 := by
    intro hYe
    apply hyx
    have hsub : (⟨y, hy⟩ : ↥Bs) = 1 := by rw [← hY, hYe, map_one]
    have h1 : y = 1 := by
      have := congrArg (fun w : ↥Bs => (w : G)) hsub
      simpa using this
    rw [h1]; exact Subgroup.one_mem _
  have hXax : ∀ i j, i ≠ j → X i = 1 ∨ X j = 1 :=
    fun i j hij => SpFrame.coord_eq_one_of_fixed hp hp2 hn hA Φ hΦ hAL hx hfx hcL hij
  have hYax : ∀ i j, i ≠ j → Y i = 1 ∨ Y j = 1 :=
    fun i j hij => SpFrame.coord_eq_one_of_fixed hp hp2 hn hA Φ hΦ hAK hy hfy hcK hij
  obtain ⟨a, hXa, hXoff⟩ := fr_axial_support hXax hX1
  obtain ⟨b, hYb, hYoff⟩ := fr_axial_support hYax hY1
  have hba : b ≠ a := by
    intro hba'
    apply hyx
    have hYz : Y ∈ Subgroup.zpowers X :=
      fr_supported_zpowers hp a hXoff
        (fun i hi => hYoff i (fun hib => hi (hib.trans hba'))) hXa
    have : (⟨y, hy⟩ : ↥Bs) ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hYz
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨k, ?_⟩
      have hmap := congrArg Φ hk
      rwa [map_zpow, hX, hY] at hmap
    exact fr_zpowers_subtype.mp this
  have hzB : (⟨y', hy'⟩ : ↥Bs) ∈ Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩} : Set ↥Bs) := by
    have hle : Subgroup.closure ({x, y} : Set G) ≤
        (Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩} : Set ↥Bs)).map (Bs.subtype : ↥Bs →* G) := by
      rw [Subgroup.closure_le]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with hwx | hwy
      · rw [hwx]
        exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.subset_closure (by simp), rfl⟩
      · rw [hwy]
        exact Subgroup.mem_map.mpr ⟨⟨y, hy⟩, Subgroup.subset_closure (by simp), rfl⟩
    obtain ⟨b0, hb0, hb0z⟩ := Subgroup.mem_map.mp (hle hy'D)
    have : b0 = ⟨y', hy'⟩ := Subtype.ext (by simpa using hb0z)
    rwa [this] at hb0
  have hZD : Z ∈ Subgroup.closure ({X, Y} : Set (Fin (n + 1) → Multiplicative (ZMod p))) := by
    have himg : (Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩} : Set ↥Bs)).map
        (Φ.symm : ↥Bs →* (Fin (n + 1) → Multiplicative (ZMod p))) =
        Subgroup.closure ({X, Y} : Set (Fin (n + 1) → Multiplicative (ZMod p))) := by
      rw [MonoidHom.map_closure]
      congr 1
      rw [Set.image_pair]
      rfl
    rw [← himg]
    exact Subgroup.mem_map.mpr ⟨⟨y', hy'⟩, hzB, rfl⟩
  have hZoff : ∀ i, i ≠ a → i ≠ b → Z i = 1 := by
    let S : Subgroup (Fin (n + 1) → Multiplicative (ZMod p)) :=
      { carrier := {w | ∀ i, i ≠ a → i ≠ b → w i = 1}
        one_mem' := by intro i _ _; rfl
        mul_mem' := by
          intro u v hu hv i hi hj
          rw [Pi.mul_apply, hu i hi hj, hv i hi hj, one_mul]
        inv_mem' := by
          intro u hu i hi hj
          rw [Pi.inv_apply, hu i hi hj, inv_one] }
    have hle : Subgroup.closure ({X, Y} : Set (Fin (n + 1) → Multiplicative (ZMod p))) ≤ S := by
      rw [Subgroup.closure_le]
      intro w hw
      rcases hw with rfl | rfl
      · intro i hi _; exact hXoff i hi
      · intro i _ hj; exact hYoff i hj
    exact hle hZD
  have hδ : Z b ≠ 1 := by
    intro hδ1
    apply hy'x
    have hZz : Z ∈ Subgroup.zpowers X :=
      fr_supported_zpowers hp a hXoff (fun i hi => by
        by_cases hib : i = b
        · subst hib; exact hδ1
        · exact hZoff i hi hib) hXa
    have : (⟨y', hy'⟩ : ↥Bs) ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hZz
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨k, ?_⟩
      have hmap := congrArg Φ hk
      rwa [map_zpow, hX, hZ] at hmap
    exact fr_zpowers_subtype.mp this
  let γ : Multiplicative (ZMod p) := Z a
  let δ : Multiplicative (ZMod p) := Z b
  have hδne : δ ≠ δ⁻¹ := fun h => fr_inv_ne_self hp hp2 hδ h.symm
  have hZstruct : Z = Pi.mulSingle a γ * Pi.mulSingle b δ := by
    funext i
    by_cases hia : i = a
    · subst hia
      simp [γ, Pi.mul_apply, Pi.mulSingle_apply, Ne.symm hba]
    · by_cases hib : i = b
      · subst hib
        simp [δ, Pi.mul_apply, Pi.mulSingle_apply, hba]
      · rw [hZoff i hia hib]
        simp [Pi.mul_apply, Pi.mulSingle_apply, hia, hib]
  let vec : Fin n × Bool → Fin (n + 1) → Multiplicative (ZMod p) :=
    fun q => Pi.mulSingle a γ * Pi.mulSingle (a.succAbove q.1) (if q.2 then δ⁻¹ else δ)
  have hvec_self : ∀ q, vec q (a.succAbove q.1) = if q.2 then δ⁻¹ else δ := by
    intro q
    simp [vec, Pi.mul_apply, Pi.mulSingle_apply, Fin.succAbove_ne]
  have hmem : ∀ q, Φ (vec q) ∈ MulAction.orbit AL (⟨y', hy'⟩ : ↥Bs) := by
    rintro ⟨c, s⟩
    have hc'a : a.succAbove c ≠ a := Fin.succAbove_ne a c
    have hsa : Equiv.swap b (a.succAbove c) a = a :=
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hba) (Ne.symm hc'a)
    have hsb : Equiv.swap b (a.succAbove c) b = a.succAbove c := Equiv.swap_apply_left _ _
    have hpermp : coordPerm (n + 1) p (Equiv.swap b (a.succAbove c)) ∈
        spSignedGroup (n + 1) p := coordPerm_mem_spSignedGroup _
    have hpermfix : coordPerm (n + 1) p (Equiv.swap b (a.succAbove c)) X = X := by
      rw [fr_axial_eq_mulSingle hXoff, fr_coordPerm_mulSingle, hsa,
        fr_axial_eq_mulSingle hXoff]
    have hZmap : coordPerm (n + 1) p (Equiv.swap b (a.succAbove c)) Z =
        Pi.mulSingle a γ * Pi.mulSingle (a.succAbove c) δ := by
      rw [hZstruct, fr_coordPerm_mul, fr_coordPerm_mulSingle, fr_coordPerm_mulSingle, hsa, hsb]
    have hifx : coordInv (n + 1) p (a.succAbove c) X = X := by
      funext t
      by_cases ht : t = a.succAbove c <;> simp [coordInv_apply, ht, hXoff _ hc'a]
    cases s
    · obtain ⟨ψ, -, hψ⟩ := hΦ (coordPerm (n + 1) p (Equiv.swap b (a.succAbove c))) hpermp
      have hψAL : ψ ∈ AL :=
        mem_of_signedPerm_fixing hp hp2 hn hA Φ hΦ hAL hx hx1 hfx hcL hpermp hpermfix hψ
      refine MulAction.mem_orbit_iff.mpr ⟨⟨ψ, hψAL⟩, ?_⟩
      rw [Subgroup.smul_def, MulAut.smul_def, ← hZ, hψ Z, hZmap]
      rfl
    · have hperm2 : coordInv (n + 1) p (a.succAbove c) *
          coordPerm (n + 1) p (Equiv.swap b (a.succAbove c)) ∈ spSignedGroup (n + 1) p :=
        Subgroup.mul_mem _ (coordInv_mem_spSignedGroup _) hpermp
      have hpermfix2 : (coordInv (n + 1) p (a.succAbove c) *
          coordPerm (n + 1) p (Equiv.swap b (a.succAbove c))) X = X := by
        rw [Equiv.Perm.mul_apply, hpermfix, hifx]
      have hZmap2 : (coordInv (n + 1) p (a.succAbove c) *
          coordPerm (n + 1) p (Equiv.swap b (a.succAbove c))) Z =
          Pi.mulSingle a γ * Pi.mulSingle (a.succAbove c) δ⁻¹ := by
        rw [Equiv.Perm.mul_apply, hZmap, fr_coordInv_two hc'a]
      obtain ⟨ψ, -, hψ⟩ := hΦ (coordInv (n + 1) p (a.succAbove c) *
        coordPerm (n + 1) p (Equiv.swap b (a.succAbove c))) hperm2
      have hψAL : ψ ∈ AL :=
        mem_of_signedPerm_fixing hp hp2 hn hA Φ hΦ hAL hx hx1 hfx hcL hperm2 hpermfix2 hψ
      refine MulAction.mem_orbit_iff.mpr ⟨⟨ψ, hψAL⟩, ?_⟩
      rw [Subgroup.smul_def, MulAut.smul_def, ← hZ, hψ Z, hZmap2]
      rfl
  let F : Fin n × Bool → MulAction.orbit AL (⟨y', hy'⟩ : ↥Bs) :=
    fun q => ⟨Φ (vec q), hmem q⟩
  have hF : Function.Injective F := by
    rintro ⟨c, s⟩ ⟨c', s'⟩ heq
    have hv : vec (c, s) = vec (c', s') := Φ.injective (Subtype.ext_iff.mp heq)
    have hval : (if s then δ⁻¹ else δ) = vec (c', s') (a.succAbove c) := by
      have := congrFun hv (a.succAbove c)
      rwa [hvec_self (c, s)] at this
    have hcc' : c = c' := by
      by_contra hne
      have h1 : vec (c', s') (a.succAbove c) = 1 := by
        dsimp only [vec]
        simp only [Pi.mul_apply, Pi.mulSingle_apply]
        rw [if_neg (Fin.succAbove_ne a c),
          if_neg (fun h => hne (Fin.succAbove_right_injective h)), mul_one]
      rw [h1] at hval
      cases s <;> simp_all [hδ, inv_ne_one.mpr hδ]
    have hss' : s = s' := by
      rw [← hcc'] at hval
      rw [hvec_self (c, s')] at hval
      cases s <;> cases s' <;> simp_all [hδne]
    exact Prod.ext hcc' hss'
  have hcarddom : Nat.card (Fin n × Bool) = 2 * n := by
    rw [Nat.card_prod, Nat.card_fin, Nat.card_eq_fintype_card, Fintype.card_bool]
    ring
  calc 2 * n = Nat.card (Fin n × Bool) := hcarddom.symm
    _ ≤ Nat.card (MulAction.orbit AL (⟨y', hy'⟩ : ↥Bs)) := Nat.card_le_card_of_injective F hF


theorem zpowers_eq_of_two_frames {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m)
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) (hrank : Nat.card Bs = p ^ (m + 1))
    {A A' : Subgroup (MulAut ↥Bs)} (hA : GGWeylOfType p (CoxeterMatrix.B (m + 1)) A)
    (hA' : GGWeylOfType p (CoxeterMatrix.B (m + 1)) A')
    {Hx Hy Hz : Subgroup (MulAut ↥Bs)} (hHx : Hx ≤ A ⊓ A') (hHy : Hy ≤ A) (hHz : Hz ≤ A')
    {x y z : G} (hx : x ∈ Bs) (hy : y ∈ Bs) (hz : z ∈ Bs)
    (hfx : ∀ ψ ∈ Hx, ((ψ ⟨x, hx⟩ : ↥Bs) : G) = x)
    (hfy : ∀ ψ ∈ Hy, ((ψ ⟨y, hy⟩ : ↥Bs) : G) = y)
    (hfz : ∀ ψ ∈ Hz, ((ψ ⟨z, hz⟩ : ↥Bs) : G) = z)
    (hcx : 2 ^ m * m.factorial ≤ Nat.card Hx) (hcy : 2 ^ m * m.factorial ≤ Nat.card Hy)
    (hcz : 2 ^ m * m.factorial ≤ Nat.card Hz)
    (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x) (hzx : z ∉ Subgroup.zpowers x)
    (hzD : z ∈ Subgroup.closure ({x, y} : Set G)) :
    Subgroup.zpowers z = Subgroup.zpowers y := by
  classical
  obtain ⟨Φ, hΦ⟩ := SpFrame.exists_frame_iso_of_weyl hp hp2 hBs (by omega : 1 ≤ m) hrank hA
  obtain ⟨Φ', hΦ'⟩ := SpFrame.exists_frame_iso_of_weyl hp hp2 hBs (by omega : 1 ≤ m) hrank hA'
  let C := Fin (m + 1) → Multiplicative (ZMod p)
  let xb : ↥Bs := ⟨x, hx⟩
  let yb : ↥Bs := ⟨y, hy⟩
  let zb : ↥Bs := ⟨z, hz⟩
  let X : C := Φ.symm xb
  let Y : C := Φ.symm yb
  let Z : C := Φ.symm zb
  let X' : C := Φ'.symm xb
  let Z' : C := Φ'.symm zb
  have hΦX : Φ X = xb := Φ.apply_symm_apply xb
  have hΦY : Φ Y = yb := Φ.apply_symm_apply yb
  have hΦZ : Φ Z = zb := Φ.apply_symm_apply zb
  have hΦ'X' : Φ' X' = xb := Φ'.apply_symm_apply xb
  have hΦ'Z' : Φ' Z' = zb := Φ'.apply_symm_apply zb
  have hXax : ∀ i j, i ≠ j → X i = 1 ∨ X j = 1 :=
    fun i j hij => SpFrame.coord_eq_one_of_fixed hp hp2 hm hA Φ hΦ
      (hHx.trans inf_le_left) hx hfx hcx hij
  have hYax : ∀ i j, i ≠ j → Y i = 1 ∨ Y j = 1 :=
    fun i j hij => SpFrame.coord_eq_one_of_fixed hp hp2 hm hA Φ hΦ hHy hy hfy hcy hij
  have hX'ax : ∀ i j, i ≠ j → X' i = 1 ∨ X' j = 1 :=
    fun i j hij => SpFrame.coord_eq_one_of_fixed hp hp2 hm hA' Φ' hΦ'
      (hHx.trans inf_le_right) hx hfx hcx hij
  have hZ'ax : ∀ i j, i ≠ j → Z' i = 1 ∨ Z' j = 1 :=
    fun i j hij => SpFrame.coord_eq_one_of_fixed hp hp2 hm hA' Φ' hΦ' hHz hz hfz hcz hij
  have hz1 : z ≠ 1 := fun h => hzx (by rw [h]; exact Subgroup.one_mem _)
  have hX'1 : X' ≠ 1 := by
    intro h
    apply hx1
    have h2 : xb = 1 := by rw [← hΦ'X', h, map_one]
    exact Subtype.ext_iff.mp h2
  have hZ'1 : Z' ≠ 1 := by
    intro h
    apply hz1
    have h2 : zb = 1 := by rw [← hΦ'Z', h, map_one]
    exact Subtype.ext_iff.mp h2
  obtain ⟨a', hX'a', hX'off⟩ := tf_exists_nontrivial_coord hX'ax hX'1
  obtain ⟨c', hZ'c', hZ'off⟩ := tf_exists_nontrivial_coord hZ'ax hZ'1
  have hc'a' : c' ≠ a' := by
    intro hca
    apply hzx
    have hX'supp : ∀ i, i ≠ c' → X' i = 1 := by
      intro i hi
      exact hX'off i (fun hia => hi (hia.trans hca.symm))
    have hX'c'_ne : X' c' ≠ 1 := by rw [hca]; exact hX'a'
    have hmem' : Z' ∈ Subgroup.zpowers X' :=
      tf_mem_zpowers_of_supported hp c' hX'supp hZ'off hX'c'_ne
    have hmem'' : zb ∈ Subgroup.zpowers xb := by
      have h := Subgroup.mem_map_of_mem Φ'.toMonoidHom hmem'
      simp only [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hΦ'Z', hΦ'X'] at h
      exact h
    have hmemG : z ∈ Subgroup.zpowers x := by
      have h := Subgroup.mem_map_of_mem Bs.subtype hmem''
      simpa using h
    exact hmemG
  have hh : coordInv (m + 1) p c' ∈ spSignedGroup (m + 1) p := coordInv_mem_spSignedGroup c'
  obtain ⟨σ, hσA', hσval⟩ := hΦ' (coordInv (m + 1) p c') hh
  have hX'c' : X' c' = 1 := hX'off c' hc'a'
  have hfix' : coordInv (m + 1) p c' X' = X' := tf_coordInv_apply_of_eq_one c' hX'c'
  have hσHx : σ ∈ Hx :=
    mem_of_signedPerm_fixing hp hp2 hm hA' Φ' hΦ' (hHx.trans inf_le_right) hx hx1 hfx hcx
      hh hfix' hσval
  have hσA : σ ∈ A := (Subgroup.mem_inf.mp (hHx hσHx)).1
  have hσx : σ xb = xb := by
    have h1 : σ (Φ' X') = Φ' (coordInv (m + 1) p c' X') := hσval X'
    rw [hfix', hΦ'X'] at h1
    exact h1
  have hciZ' : coordInv (m + 1) p c' Z' = Z'⁻¹ := by
    funext t
    rw [coordInv_apply, Function.update_apply, Pi.inv_apply]
    by_cases ht : t = c'
    · subst ht; simp
    · rw [if_neg ht, hZ'off t ht, inv_one]
  have hσz : σ zb = zb⁻¹ := by
    have h1 : σ (Φ' Z') = Φ' (coordInv (m + 1) p c' Z') := hσval Z'
    rw [hciZ', map_inv, hΦ'Z'] at h1
    exact h1
  let H' : Subgroup (MulAut ↥Bs) := Hy.map (MulAut.conj σ).toMonoidHom
  have hH'A : H' ≤ A := by
    change Hy.map (MulAut.conj σ).toMonoidHom ≤ A
    rw [Subgroup.map_le_iff_le_comap]
    intro h hh
    rw [Subgroup.mem_comap]
    change (MulAut.conj σ) h ∈ A
    rw [MulAut.conj_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hσA (hHy hh)) (Subgroup.inv_mem _ hσA)
  have hH'card : Nat.card H' = Nat.card Hy := by
    change Nat.card ↥(Hy.map (MulAut.conj σ).toMonoidHom) = Nat.card ↥Hy
    rw [Subgroup.card_map_of_injective]
    exact (MulAut.conj σ).injective
  have hfyb : ∀ ψ ∈ Hy, ψ yb = yb := fun ψ hψ => Subtype.ext (hfy ψ hψ)
  have hH'fix : ∀ ψ ∈ H', ψ (σ yb) = σ yb := by
    intro ψ hψ
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hψ
    change (MulAut.conj σ) h (σ yb) = σ yb
    rw [MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply,
      MulEquiv.symm_apply_apply, hfyb h hh]
  have hWax : ∀ i j, i ≠ j →
      (Φ.symm (σ yb)) i = 1 ∨ (Φ.symm (σ yb)) j = 1 := by
    intro i j hij
    exact SpFrame.coord_eq_one_of_fixed hp hp2 hm hA Φ hΦ hH'A (σ yb).2
      (fun ψ hψ => congrArg Subtype.val (hH'fix ψ hψ)) (by rw [hH'card]; exact hcy) hij
  let σc : MulAut C := (Φ.trans σ).trans Φ.symm
  have hσcX : σc X = X := by
    change Φ.symm (σ (Φ X)) = X
    rw [hΦX, hσx]
  have hσcY : σc Y = Φ.symm (σ yb) := by
    change Φ.symm (σ (Φ Y)) = Φ.symm (σ yb)
    rw [hΦY]
  have hσcZ : σc Z = Z⁻¹ := by
    change Φ.symm (σ (Φ Z)) = Z⁻¹
    rw [hΦZ, hσz, map_inv]
  have hZD : Z ∈ Subgroup.closure ({X, Y} : Set C) := by
    have hzB : zb ∈ Subgroup.closure ({xb, yb} : Set ↥Bs) := by
      have hle : Subgroup.closure ({x, y} : Set G) ≤
          (Subgroup.closure ({xb, yb} : Set ↥Bs)).map (Bs.subtype : ↥Bs →* G) := by
        rw [Subgroup.closure_le]
        intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with hwx | hwy
        · rw [hwx]
          exact Subgroup.mem_map.mpr ⟨xb, Subgroup.subset_closure (by simp), rfl⟩
        · rw [hwy]
          exact Subgroup.mem_map.mpr ⟨yb, Subgroup.subset_closure (by simp), rfl⟩
      obtain ⟨b, hb, hbz⟩ := Subgroup.mem_map.mp (hle hzD)
      have hb_eq : b = zb := Subtype.ext (by simpa [zb] using hbz)
      rwa [hb_eq] at hb
    have himg : (Subgroup.closure ({xb, yb} : Set ↥Bs)).map
        (Φ.symm : ↥Bs →* C) = Subgroup.closure ({X, Y} : Set C) := by
      rw [MonoidHom.map_closure]
      congr 1
      rw [Set.image_pair]
      rfl
    rw [← himg]
    exact Subgroup.mem_map.mpr ⟨zb, hzB, rfl⟩
  have hYX : Y ∉ Subgroup.zpowers X := by
    intro hmem
    apply hyx
    have h := Subgroup.mem_map_of_mem Φ.toMonoidHom hmem
    simp only [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hΦX, hΦY] at h
    have h2 := Subgroup.mem_map_of_mem Bs.subtype h
    simpa using h2
  have hZX : Z ∉ Subgroup.zpowers X := by
    intro hmem
    apply hzx
    have h := Subgroup.mem_map_of_mem Φ.toMonoidHom hmem
    simp only [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hΦX, hΦZ] at h
    have h2 := Subgroup.mem_map_of_mem Bs.subtype h
    simpa using h2
  have hX1 : X ≠ 1 := by
    intro h
    apply hx1
    have h2 : xb = 1 := by rw [← hΦX, h, map_one]
    exact Subtype.ext_iff.mp h2
  have hcoord := tf_coords_zpowers_eq hp hp2 σc hXax hYax hWax hX1 hYX hZX hZD hσcX hσcY hσcZ
  have hBs : Subgroup.zpowers zb = Subgroup.zpowers yb := by
    have h := congrArg (Subgroup.map Φ.toMonoidHom) hcoord
    simp only [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hΦZ, hΦY] at h
    exact h
  have hG := congrArg (Subgroup.map Bs.subtype) hBs
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hG
  simpa using hG

end Frames

end CFSG.StandardType.SpJoinRefl
