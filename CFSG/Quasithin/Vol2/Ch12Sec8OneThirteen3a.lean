module

public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.H13.L128N

variable {G : Type*} [Group G]

@[expose] def conjSub {U : Subgroup G} (a : G) (ha : a ∈ Subgroup.normalizer (U : Set G)) :
    ↥U →* ↥U where
  toFun u := ⟨a * u * a⁻¹, (Subgroup.mem_normalizer_iff.1 ha u).1 u.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjSub_apply {U : Subgroup G} (a : G) (ha : a ∈ Subgroup.normalizer (U : Set G))
    (u : ↥U) : ((conjSub a ha u : ↥U) : G) = a * u * a⁻¹ := rfl

variable [Finite G]

theorem mem_of_fixed_of_card_eight {W V₁ : Subgroup G} (hV₁W : V₁ ≤ W)
    (hWV₁ : W ≤ Subgroup.normalizer (V₁ : Set G)) (hcW : Nat.card W = 8)
    (hcV₁ : Nat.card V₁ = 2) (hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y * x⁻¹ * y⁻¹ ∈ V₁)
    (hsq : ∀ x ∈ W, x ^ 2 ∈ V₁) {a : G} (haW : a ∈ Subgroup.normalizer (W : Set G))
    (haV₁ : a ∈ Subgroup.normalizer (V₁ : Set G)) (hodd : Odd (orderOf a)) {x : G} (hxW : x ∈ W)
    (hx : a * x * a⁻¹ * x⁻¹ ∉ V₁) {w : G} (hwW : w ∈ W) (hw : a * w * a⁻¹ * w⁻¹ ∈ V₁) :
    w ∈ V₁ := by
  classical
  by_contra hwV
  set N := V₁.subgroupOf W with hNdef
  have hN : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hV₁W).2 hWV₁
  have hmk : ∀ x y : ↥W, ((x : ↥W ⧸ N) = (y : ↥W ⧸ N)) ↔ (x : G)⁻¹ * y ∈ V₁ := by
    intro x y
    rw [QuotientGroup.eq]
    rfl
  have hmk1 : ∀ x : ↥W, ((x : ↥W ⧸ N) = 1) ↔ (x : G) ∈ V₁ := by
    intro x
    rw [QuotientGroup.eq_one_iff]
    rfl
  have hQc : ∀ p q : ↥W ⧸ N, p * q = q * p := by
    intro p q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hmk]
    have h := hcomm _ (W.inv_mem y.2) _ (W.inv_mem x.2)
    simp only [Subgroup.coe_mul, mul_inv_rev, inv_inv] at h ⊢
    simpa [mul_assoc] using h
  have hsq2 : ∀ q : ↥W ⧸ N, q * q = 1 := by
    intro q
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, hmk1]
    simpa [sq] using hsq _ u.2
  have hcQ : Nat.card (↥W ⧸ N) = 4 := by
    have h1 := N.card_eq_card_quotient_mul_card_subgroup
    rw [hcW, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₁W).toEquiv, hcV₁] at h1
    omega
  set K := Subgroup.normalizer (W : Set G) ⊓ Subgroup.normalizer (V₁ : Set G) with hK
  have hle : ∀ g : ↥K, N ≤ N.comap (conjSub (g : G) g.2.1) := by
    intro g y hy
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, conjSub_apply]
    exact (Subgroup.mem_normalizer_iff.1 g.2.2 y).1 hy
  let φ : ↥K → (↥W ⧸ N →* ↥W ⧸ N) := fun g => QuotientGroup.map N N (conjSub (g : G) g.2.1) (hle g)
  have hφ : ∀ (g : ↥K) (u : ↥W), φ g (u : ↥W ⧸ N) = ((conjSub (g : G) g.2.1 u : ↥W) : ↥W ⧸ N) :=
    fun g u => rfl
  have hφmul : ∀ (g h : ↥K) (q : ↥W ⧸ N), φ (g * h) q = φ g (φ h q) := by
    intro g h q
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hφ, hφ, hφ]
    congr 1
    apply Subtype.ext
    simp only [conjSub_apply, Subgroup.coe_mul, mul_inv_rev]
    group
  have hφone : ∀ q : ↥W ⧸ N, φ 1 q = q := by
    intro q
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hφ]
    congr 1
    apply Subtype.ext
    simp [conjSub_apply]
  set A : ↥K := ⟨a, haW, haV₁⟩ with hA
  have hφinj : ∀ p q : ↥W ⧸ N, φ A p = φ A q → p = q := by
    intro p q h
    have h1 := congrArg (φ A⁻¹) h
    rwa [← hφmul, ← hφmul, inv_mul_cancel, hφone, hφone] at h1
  set wq : ↥W ⧸ N := ((⟨w, hwW⟩ : ↥W) : ↥W ⧸ N) with hwq
  set xq : ↥W ⧸ N := ((⟨x, hxW⟩ : ↥W) : ↥W ⧸ N) with hxq
  have hwfix : φ A wq = wq := by
    rw [hwq, hφ, hmk, conjSub_apply]
    have h1 := V₁.inv_mem hw
    have h2 := (Subgroup.mem_normalizer_iff.1 (hWV₁ (W.inv_mem hwW)) _).1 h1
    have e1 : w⁻¹ * (a * w * a⁻¹ * w⁻¹)⁻¹ * w⁻¹⁻¹ = (a * w * a⁻¹)⁻¹ * w := by group
    rwa [e1] at h2
  have hxmove : φ A xq ≠ xq := by
    intro h
    rw [hxq, hφ, hmk, conjSub_apply] at h
    apply hx
    have h2 := (Subgroup.mem_normalizer_iff.1 (hWV₁ hxW) _).1 (V₁.inv_mem h)
    have e1 : x * ((a * x * a⁻¹)⁻¹ * x)⁻¹ * x⁻¹ = a * x * a⁻¹ * x⁻¹ := by group
    rwa [e1] at h2
  have hw1 : wq ≠ 1 := fun h => hwV ((hmk1 _).1 h)
  have hx1 : xq ≠ 1 := fun h => hxmove (by rw [h, map_one])
  have hwx : wq ≠ xq := fun h => hxmove (by rw [← h, hwfix])
  have hwx1 : wq * xq ≠ 1 := by
    intro h
    apply hwx
    calc wq = wq * (xq * xq) := by rw [hsq2, mul_one]
      _ = (wq * xq) * xq := by rw [mul_assoc]
      _ = xq := by rw [h, one_mul]
  have hwxw : wq * xq ≠ wq := fun h => hx1 (by
    calc xq = wq * wq * xq := by rw [hsq2, one_mul]
      _ = wq * (wq * xq) := by rw [mul_assoc]
      _ = 1 := by rw [h, hsq2])
  have hwxx : wq * xq ≠ xq := fun h => hw1 (by
    calc wq = wq * xq * xq := by rw [mul_assoc, hsq2, mul_one]
      _ = 1 := by rw [h, hsq2])
  have : Fintype (↥W ⧸ N) := Fintype.ofFinite _
  have hall : ∀ q : ↥W ⧸ N, q = 1 ∨ q = wq ∨ q = xq ∨ q = wq * xq := by
    intro q
    set s : Finset (↥W ⧸ N) := {1, wq, xq, wq * xq} with hs
    have hcs : s.card = 4 := by
      rw [hs, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_pair hwxx.symm]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hwx, fun h => hwxw h.symm⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hw1.symm, hx1.symm, hwx1.symm⟩
    have huniv : s = Finset.univ := Finset.eq_univ_of_card s (by
      rw [hcs, ← Nat.card_eq_fintype_card, hcQ])
    have hq : q ∈ s := huniv ▸ Finset.mem_univ q
    simpa [hs] using hq
  have hφx : φ A xq = wq * xq := by
    rcases hall (φ A xq) with h | h | h | h
    · exact absurd (hφinj _ _ (h.trans (map_one _).symm)) hx1
    · exact absurd (hφinj _ _ (h.trans hwfix.symm)) hwx.symm
    · exact absurd h hxmove
    · exact h
  have hφ2 : φ (A ^ 2) xq = xq := by
    rw [sq, hφmul, hφx, map_mul, hwfix, hφx, ← mul_assoc, hsq2, one_mul]
  have hφpow : ∀ k : ℕ, φ ((A ^ 2) ^ k) xq = xq := by
    intro k
    induction k with
    | zero => rw [pow_zero, hφone]
    | succ k ih => rw [pow_succ', hφmul, ih, hφ2]
  obtain ⟨m, hm⟩ := hodd
  have hA : (A ^ 2) ^ (m + 1) = A := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, hA]
    rw [← pow_mul, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, ← hm,
      pow_orderOf_eq_one, one_mul]
  apply hxmove
  rw [← hA, hφpow]

theorem mem_of_fixed_of_norm {U V₁ P : Subgroup G} (S : Set G) (hU : U = Subgroup.closure S)
    (hV₁U : V₁ ≤ U) (hUV₁ : U ≤ Subgroup.normalizer (V₁ : Set G))
    (hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ V₁) (hsq : ∀ x ∈ U, x ^ 2 ∈ V₁)
    (hPU : P ≤ Subgroup.normalizer (U : Set G)) (hPV₁ : P ≤ Subgroup.normalizer (V₁ : Set G))
    (hodd : Odd (Nat.card P))
    (hS : ∀ s ∈ S, ∃ W : Subgroup G, s ∈ W ∧ W ≤ U ∧ P ≤ Subgroup.normalizer (W : Set G) ∧
      ∀ w ∈ W, (∀ a ∈ P, a * w * a⁻¹ * w⁻¹ ∈ V₁) → w ∈ V₁)
    {z : G} (hz : z ∈ U) (hzP : ∀ a ∈ P, a * z * a⁻¹ * z⁻¹ ∈ V₁) : z ∈ V₁ := by
  classical
  set N := V₁.subgroupOf U with hNdef
  have hN : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hV₁U).2 hUV₁
  have hmk : ∀ x y : ↥U, ((x : ↥U ⧸ N) = (y : ↥U ⧸ N)) ↔ (x : G)⁻¹ * y ∈ V₁ := by
    intro x y
    rw [QuotientGroup.eq]
    rfl
  have hQc : ∀ a b : ↥U ⧸ N, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hmk]
    have h := hcomm _ (U.inv_mem y.2) _ (U.inv_mem x.2)
    simp only [Subgroup.coe_mul, mul_inv_rev, inv_inv] at h ⊢
    simpa [mul_assoc] using h
  let _ : CommGroup (↥U ⧸ N) := { (inferInstance : Group (↥U ⧸ N)) with mul_comm := hQc }
  have hle : ∀ a : ↥P, N ≤ N.comap (conjSub (a : G) (hPU a.2)) := by
    intro a x hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, conjSub_apply]
    exact (Subgroup.mem_normalizer_iff.1 (hPV₁ a.2) x).1 hx
  let φ : ↥P → (↥U ⧸ N →* ↥U ⧸ N) := fun a =>
    QuotientGroup.map N N (conjSub (a : G) (hPU a.2)) (hle a)
  have hφ : ∀ (a : ↥P) (u : ↥U), φ a (u : ↥U ⧸ N) = ((conjSub (a : G) (hPU a.2) u : ↥U) : ↥U ⧸ N) :=
    fun a u => rfl
  have hφmul : ∀ (a b : ↥P) (q : ↥U ⧸ N), φ b (φ a q) = φ (b * a) q := by
    intro a b q
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hφ, hφ, hφ]
    congr 1
    apply Subtype.ext
    simp only [conjSub_apply, Subgroup.coe_mul, mul_inv_rev]
    group
  have : Fintype ↥P := Fintype.ofFinite _
  set e : ↥U ⧸ N →* ↥U ⧸ N := ∏ a : ↥P, φ a with he
  have heapp : ∀ q, e q = ∏ a : ↥P, φ a q := fun q => by
    rw [he, MonoidHom.finsetProd_apply]
  have hefix : ∀ (b : ↥P) (q : ↥U ⧸ N), φ b (e q) = e q := by
    intro b q
    rw [heapp, map_prod]
    simp only [hφmul]
    exact Fintype.prod_equiv (Equiv.mulLeft b) _ _ (fun a => rfl)
  have hsq2 : ∀ q : ↥U ⧸ N, q ^ 2 = 1 := by
    intro q
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    rw [Subgroup.mem_subgroupOf]
    simpa using hsq _ u.2
  have hgen : ∀ s (hs : s ∈ S), e ((⟨s, hU ▸ Subgroup.subset_closure hs⟩ : ↥U) : ↥U ⧸ N) = 1 := by
    intro s hs
    obtain ⟨W, hsW, hWU, hPW, hfp⟩ := hS s hs
    set q : ↥U ⧸ N := ((⟨s, hU ▸ Subgroup.subset_closure hs⟩ : ↥U) : ↥U ⧸ N) with hq
    set Wq := (W.subgroupOf U).map (QuotientGroup.mk' N) with hWq
    have hmem : e q ∈ Wq := by
      rw [heapp]
      refine Subgroup.prod_mem _ fun a _ => ?_
      rw [hq, hφ]
      refine ⟨conjSub (a : G) (hPU a.2) ⟨s, hU ▸ Subgroup.subset_closure hs⟩, ?_, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 (hPW a.2) s).1 hsW
    obtain ⟨w, hwW, hwq⟩ := hmem
    have hwW' : (w : G) ∈ W := hwW
    have hw : (w : G) ∈ V₁ := by
      refine hfp w hwW' fun a ha => ?_
      have h1 := hefix ⟨a, ha⟩ q
      rw [← hwq] at h1
      have h2 : φ ⟨a, ha⟩ (QuotientGroup.mk' N w) = QuotientGroup.mk' N w := h1
      rw [QuotientGroup.mk'_apply, hφ, hmk, conjSub_apply] at h2
      have h3 := (Subgroup.mem_normalizer_iff.1 (hUV₁ w.2) _).1 (V₁.inv_mem h2)
      have e1 : (w : G) * ((a * w * a⁻¹)⁻¹ * w)⁻¹ * (w : G)⁻¹ = a * w * a⁻¹ * (w : G)⁻¹ := by
        group
      rwa [e1] at h3
    rw [← hwq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hw
  have he1 : ∀ x, x ∈ Subgroup.closure S → ∀ hxU : x ∈ U,
      e ((⟨x, hxU⟩ : ↥U) : ↥U ⧸ N) = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem s hs => intro _; exact hgen s hs
    | one =>
      intro _
      show e ((1 : ↥U) : ↥U ⧸ N) = 1
      rw [QuotientGroup.mk_one, map_one]
    | mul x y hx hy ihx ihy =>
      intro hxyU
      have hxU : x ∈ U := hU ▸ hx
      have hyU : y ∈ U := hU ▸ hy
      have e1 : ((⟨x * y, hxyU⟩ : ↥U) : ↥U ⧸ N) =
          ((⟨x, hxU⟩ : ↥U) : ↥U ⧸ N) * ((⟨y, hyU⟩ : ↥U) : ↥U ⧸ N) := rfl
      rw [e1, map_mul, ihx hxU, ihy hyU, one_mul]
    | inv x hx ihx =>
      intro hxU'
      have hxU : x ∈ U := hU ▸ hx
      have e1 : ((⟨x⁻¹, hxU'⟩ : ↥U) : ↥U ⧸ N) = (((⟨x, hxU⟩ : ↥U) : ↥U ⧸ N))⁻¹ := rfl
      rw [e1, map_inv, ihx hxU, inv_one]
  set q₀ : ↥U ⧸ N := ((⟨z, hz⟩ : ↥U) : ↥U ⧸ N) with hq₀
  have hfix0 : ∀ a : ↥P, φ a q₀ = q₀ := by
    intro a
    rw [hq₀, hφ, hmk, conjSub_apply]
    have h1 := V₁.inv_mem (hzP a a.2)
    have h2 := (Subgroup.mem_normalizer_iff.1 (hUV₁ (U.inv_mem hz)) _).1 h1
    have e1 : z⁻¹ * (a * z * (a : G)⁻¹ * z⁻¹)⁻¹ * z⁻¹⁻¹ = (a * z * (a : G)⁻¹)⁻¹ * z := by group
    rwa [e1] at h2
  have hq0 : e q₀ = q₀ := by
    rw [heapp]
    simp only [hfix0, Finset.prod_const, Finset.card_univ]
    obtain ⟨k, hk⟩ := hodd
    rw [← Nat.card_eq_fintype_card, hk, pow_succ, pow_mul, hsq2, one_pow, one_mul]
  have h1 : q₀ = 1 := hq0.symm.trans (he1 z (hU ▸ hz) hz)
  rw [hq₀, QuotientGroup.eq_one_iff] at h1
  exact h1

end CFSG.Quasithin.H13.L128N
