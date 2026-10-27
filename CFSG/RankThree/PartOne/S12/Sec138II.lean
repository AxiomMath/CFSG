module

public import CFSG.RankThree.PartOne.S12.Sec138Trans
public import CFSG.RankThree.PartOne.S12.Sec137

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace Sec138II

open Equiv

theorem exists_conj_square_one : ∀ σ : Perm (Fin 4), σ ^ 3 = 1 → σ ≠ 1 →
    ∃ g : Perm (Fin 4), (σ * (g * σ * g⁻¹)) ^ 2 = 1 ∧ σ * (g * σ * g⁻¹) ≠ 1 := by
  decide +kernel

theorem eq_one_of_mem_normal {M : Type*} [Group M] {H : Subgroup M} (ψ : H ≃* Perm (Fin 4))
    {R : Set M} (hmul : ∀ x ∈ R, ∀ y ∈ R, x * y ∈ R)
    (hconj : ∀ h ∈ H, ∀ x ∈ R, h * x * h⁻¹ ∈ R)
    (hR : ∀ x ∈ R, x ∈ H → ∃ k : ℕ, orderOf x = 3 ^ k) {x : M} (hxH : x ∈ H) (hxR : x ∈ R) :
    x = 1 := by
  have h3 : ∀ y : H, (y : M) ∈ R → ψ y ^ 3 = 1 := by
    intro y hy
    obtain ⟨k, hk⟩ := hR y hy y.2
    have h1 : orderOf (ψ y) = 3 ^ k := by
      rw [MulEquiv.orderOf_eq ψ y, ← Subgroup.orderOf_coe]
      exact hk
    have h2 : orderOf (ψ y) ∣ 24 := by
      have := orderOf_dvd_natCard (ψ y)
      rwa [Nat.card_perm, Nat.card_fin] at this
    rw [h1] at h2
    have hk1 : k ≤ 1 := by
      by_contra hk2
      have h9 : 3 ^ 2 ∣ 3 ^ k := Nat.pow_dvd_pow 3 (by omega)
      have := dvd_trans h9 h2
      norm_num at this
    have hpow : ψ y ^ (3 ^ k) = 1 := by
      rw [← h1]
      exact pow_orderOf_eq_one _
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk1 with rfl | rfl
    · have : ψ y = 1 := by simpa using hpow
      rw [this, one_pow]
    · simpa using hpow
  by_contra hx1
  set a : H := ⟨x, hxH⟩ with ha
  have ha3 : ψ a ^ 3 = 1 := h3 a hxR
  have ha1 : ψ a ≠ 1 := by
    intro h
    apply hx1
    have : a = 1 := ψ.injective (by rw [h, map_one])
    exact congrArg Subtype.val this
  obtain ⟨g, hg2, hg1⟩ := exists_conj_square_one (ψ a) ha3 ha1
  set h : H := ψ.symm g with hh
  set y : H := a * (h * a * h⁻¹) with hy
  have hyR : (y : M) ∈ R := hmul x hxR _ (hconj h h.2 x hxR)
  have hψy : ψ y = ψ a * (g * ψ a * g⁻¹) := by
    rw [hy, map_mul, map_mul, map_mul, map_inv, hh, MulEquiv.apply_symm_apply]
  have hy3 : ψ y ^ 3 = 1 := h3 y hyR
  have hy2 : ψ y ^ 2 = 1 := by
    rw [hψy]
    exact hg2
  have hy1 : ψ y = 1 := by
    have : ψ y = ψ y ^ 3 * (ψ y ^ 2)⁻¹ := by group
    rw [this, hy3, hy2]
    simp
  exact hg1 (by rw [← hψy]; exact hy1)

end Sec138II

theorem threeCoreCentral_of_pair {p : ℕ} {G : Type} [Group G] [Finite G] {E : Subgroup G}
    (hp : p.Prime) (hD3 : ThreeTranspD p E)
    (hpair : ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, s * t ≠ t * s →
      ∃ I ∈ thetaCompZeroStarE p E, s ∈ torusImage E I ∧ t ∈ torusImage E I)
    (hrow : ∀ I ∈ thetaCompZeroStarE p E, Nonempty (torusImage E I ≃* Equiv.Perm (Fin 4)) ∧
      torusImage E I ≤ reflectionGroup p E) :
    ThreeCoreCentral p E := by
  set X := reflectionGroup p E with hX
  set R' : Subgroup (MulAut E) := (CFSG.pCore 3 ↥X).map X.subtype with hR'
  have hconjR : ∀ x ∈ X, ∀ n ∈ R', x * n * x⁻¹ ∈ R' := by
    intro x hx n hn
    obtain ⟨n0, hn0, rfl⟩ := Subgroup.mem_map.1 hn
    refine Subgroup.mem_map.2 ⟨⟨x, hx⟩ * n0 * ⟨x, hx⟩⁻¹, ?_, rfl⟩
    exact (CFSG.pCore_normal (p := 3) (G := ↥X)).conj_mem n0 hn0 ⟨x, hx⟩
  have hordR : ∀ n ∈ R', ∃ k : ℕ, orderOf n = 3 ^ k := by
    intro n hn
    obtain ⟨n0, hn0, rfl⟩ := Subgroup.mem_map.1 hn
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 (CFSG.pCore_isPGroup (p := 3) (G := ↥X)))
      ⟨n0, hn0⟩
    refine ⟨k, ?_⟩
    have h1 : orderOf (X.subtype n0) = orderOf n0 := Subgroup.orderOf_coe n0
    have h2 : orderOf n0 = orderOf (⟨n0, hn0⟩ : ↥(CFSG.pCore 3 ↥X)) :=
      Subgroup.orderOf_coe (⟨n0, hn0⟩ : ↥(CFSG.pCore 3 ↥X))
    rw [h1, h2, hk]
  intro r hr
  rw [Subgroup.mem_center_iff]
  intro g
  have hr'R : (r : MulAut E) ∈ R' := Subgroup.mem_map.2 ⟨r, hr, rfl⟩
  have hkey : ∀ t ∈ reflectionSet p E, Commute t (r : MulAut E) := by
    intro t ht
    have hrW : (r : MulAut E) ∈ torusWeyl E := WeylIso.closure_le_weyl r.2
    have ht'D : (r : MulAut E) * t * (r : MulAut E)⁻¹ ∈ reflectionSet p E :=
      WeylIso.conj_mem_reflectionSet_of_weyl hp hrW ht
    by_cases heq : (r : MulAut E) * t * (r : MulAut E)⁻¹ = t
    · rw [mul_inv_eq_iff_eq_mul] at heq
      exact heq.symm
    · exfalso
      set t' := (r : MulAut E) * t * (r : MulAut E)⁻¹ with ht'
      have hts : t * t = 1 := RefFacts.mul_self_eq_one ht.1
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left hts
      have haR : t * t' ∈ R' := by
        have htX : t ∈ X := Subgroup.subset_closure ht
        have h1 : t * (r : MulAut E) * t⁻¹ ∈ R' := hconjR t htX _ hr'R
        have h2 : t * t' = (t * (r : MulAut E) * t⁻¹) * (r : MulAut E)⁻¹ := by
          rw [ht', htinv]
          group
        rw [h2]
        exact R'.mul_mem h1 (R'.inv_mem hr'R)
      have hle : orderOf (t * t') ≤ 3 := hD3 t ht t' ht'D
      obtain ⟨k, hk⟩ := hordR _ haR
      have hne1 : t * t' ≠ 1 := by
        intro h1
        apply heq
        have := eq_inv_of_mul_eq_one_right h1
        rw [htinv] at this
        exact this
      have hk1 : k = 1 := by
        rcases Nat.lt_or_ge k 2 with hk2 | hk2
        · rcases Nat.lt_or_ge k 1 with hk0 | hk0
          · exfalso
            have : k = 0 := by omega
            rw [this, pow_zero] at hk
            exact hne1 (orderOf_eq_one_iff.1 hk)
          · omega
        · exfalso
          have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
          omega
      have hord3 : orderOf (t * t') = 3 := by
        rw [hk, hk1, pow_one]
      have hncomm : t * t' ≠ t' * t := by
        intro hc
        have hts' : t' * t' = 1 := RefFacts.mul_self_eq_one ht'D.1
        have h2 : (t * t') ^ 2 = 1 := by
          rw [Commute.mul_pow hc, pow_two t, hts, pow_two t', hts', one_mul]
        have := orderOf_dvd_of_pow_eq_one h2
        rw [hord3] at this
        omega
      obtain ⟨I, hI, htI, ht'I⟩ := hpair t ht t' ht'D hncomm
      obtain ⟨⟨ψ⟩, hIX⟩ := hrow I hI
      have haI : t * t' ∈ torusImage E I := (torusImage E I).mul_mem htI ht'I
      have h1 := Sec138II.eq_one_of_mem_normal ψ (R := (R' : Set (MulAut E)))
        (fun x hx y hy => R'.mul_mem hx hy) (fun h hh x hx => hconjR h (hIX hh) x hx)
        (fun x hx _ => hordR x hx) haI haR
      exact hne1 h1
  have hgen : ∀ g0 ∈ Subgroup.closure (reflectionSet p E), Commute g0 (r : MulAut E) := by
    intro g0 hg0
    induction hg0 using Subgroup.closure_induction with
    | mem x hx => exact hkey x hx
    | one => exact Commute.one_left _
    | mul x y _ _ hx hy => exact hx.mul_left hy
    | inv x _ hx => exact hx.inv_left
  exact Subtype.ext (hgen g.1 g.2).eq

theorem rowNine_all (h136 : Node136) (h138I : Node138I) (hSchreier : SchreierFor InCatalog)
    (hTwoAction : TwoActionInputs) (h106 : SectionTenMaximalMovingThetaComponentsQuasisimple)
    (h11 : Sec11One) (h122 : Node122) (h122b : Node122b) (h123 : Node123) (h124 : Node124)
    (h124b : Node124b) (h125 : Node125) (h126 : Node126) (h127 : Node127) (h128 : Node128)
    (h129 : Node129) {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (hF13 : Sec13Facts G p A c L E) (hp : p.Prime)
    (hcard : Nat.card E = p ^ 4) (hT : ¬ Outcome152Five p E A (lieGenerated p E)) (hEA : E ≠ A) :
    ∀ I ∈ thetaCompZeroStarE p E, Nonempty (torusImage E I ≃* Equiv.Perm (Fin 4)) ∧
      torusImage E I ≤ reflectionGroup p E := by
  intro X' hX'
  obtain ⟨B', c', hB'adm, hc'B', hc'1, hH', hF12'⟩ := hF13.reinstantiate X' hX'
  have hT' : ¬ Outcome152Five p E B' (lieGenerated p E) := by
    rintro ⟨f, hf1, hpf, hmod, hweyl5, hc5, -, hev⟩
    exact hT ⟨f, hf1, hpf, hmod, hweyl5, hc5, hEA, hev⟩
  have hEB' : E ≠ B' := by
    intro hEB
    have h1 : Nat.card B' = p ^ 3 := hB'adm.2.2.1
    rw [← hEB, hcard] at h1
    have : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hF13' := Sec13Facts.of_nodes hSchreier hTwoAction h106 h11 h122 h122b h123 h124 h125
    h126 h127 h128 h129 hH' hT'
  obtain ⟨hclX, hweylX, -, -, -⟩ :=
    Sec138Trans.rowNine_data h136 h138I h124b hH' hF12' hF13' hT' hEB'
  exact ⟨hweylX, Sec138Trans.torusImage_le_reflectionGroup hclX⟩

@[expose] def Node138Loc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E ≠ A → RowModel p L 9 → ThreeTranspD p E →
    TransitiveD p E → LocalSThree p E

theorem node138II_of_loc (hloc : Node138Loc) (hpair : KF134Pair) (h136 : Node136)
    (h138I : Node138I) (hSchreier : SchreierFor InCatalog) (hTwoAction : TwoActionInputs)
    (h106 : SectionTenMaximalMovingThetaComponentsQuasisimple) (h11 : Sec11One)
    (h122 : Node122) (h122b : Node122b) (h123 : Node123) (h124 : Node124) (h124b : Node124b)
    (h125 : Node125) (h126 : Node126) (h127 : Node127) (h128 : Node128) (h129 : Node129) :
    Node138II := by
  intro G _ _ p A c L E h hF12 hF13 hT hEA hmodel hD3 htrans
  refine ⟨hloc G p A c L E h hF12 hF13 hT hEA hmodel hD3 htrans, ?_⟩
  have hp : p.Prime := h.prime
  obtain ⟨-, r, -, -, -, -, hr8, hr9⟩ := hF12.three
  have hr9' : 9 ≤ r := by
    by_contra hlt
    exact hEA (hr8 (by omega))
  have hcard : Nat.card E = p ^ 4 := hr9 hr9'
  exact threeCoreCentral_of_pair hp hD3
    (fun s hs t ht hne => hpair G p A c L E h hF12 hF13 hT (Or.inl hEA) s hs t ht hne)
    (rowNine_all h136 h138I hSchreier hTwoAction h106 h11 h122 h122b h123 h124 h124b h125 h126
      h127 h128 h129 hF13 hp hcard hT hEA)

end CFSG.RankThree.PartOne
