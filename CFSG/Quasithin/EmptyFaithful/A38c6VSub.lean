module

public import CFSG.Quasithin.EmptyFaithful.A38c6Defs
public import CFSG.Quasithin.Background.A3Structure316
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

open CFSG.Open

namespace CFSG.Quasithin.A38c6

open CFSG.Quasithin.A38c5.Fm Equiv

private def vsubQuads : List (Fin 8 × Fin 8 × Fin 8 × Fin 8) :=
  [(0, 1, 2, 3), (4, 5, 6, 7), (0, 1, 4, 5), (2, 3, 6, 7), (0, 1, 6, 7), (2, 3, 4, 5)]

private def vsubKv4 (a b c d : Fin 8) : Fin 4 → P8 :=
  ![1, swap a b * swap c d, swap a c * swap b d, swap a d * swap b c]

private def vsubDt3 (a b c d : Fin 8) : Fin 3 → P8 :=
  ![swap a b * swap c d, swap a c * swap b d, swap a d * swap b c]

private def vsubTf (a b c d u v w z x : Fin 8) : Fin 8 :=
  if x = a then u else if x = b then v else if x = c then w else if x = d then z else x

set_option maxRecDepth 100000
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

private theorem vsub_quad_ne : ∀ a b c d : Fin 8, (a, b, c, d) ∈ vsubQuads →
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  decide +kernel

private theorem vsub_kv4_supp : ∀ a b c d : Fin 8, (a, b, c, d) ∈ vsubQuads → ∀ i : Fin 4,
    ∀ x : Fin 8, x ≠ a → x ≠ b → x ≠ c → x ≠ d → vsubKv4 a b c d i x = x := by
  decide +kernel

private theorem vsub_dt3_supp : ∀ a b c d : Fin 8, (a, b, c, d) ∈ vsubQuads → ∀ i : Fin 3,
    ∀ x : Fin 8, x ≠ a → x ≠ b → x ≠ c → x ≠ d → vsubDt3 a b c d i x = x := by
  decide +kernel

private theorem vsub_kv4_stab : ∀ a b c d : Fin 8, (a, b, c, d) ∈ vsubQuads → ∀ i : Fin 4,
    ∀ x : Fin 8, (x = a ∨ x = b ∨ x = c ∨ x = d) →
      (vsubKv4 a b c d i x = a ∨ vsubKv4 a b c d i x = b ∨ vsubKv4 a b c d i x = c ∨
        vsubKv4 a b c d i x = d) := by
  decide +kernel

private theorem vsub_dt3_stab : ∀ a b c d : Fin 8, (a, b, c, d) ∈ vsubQuads → ∀ i : Fin 3,
    ∀ x : Fin 8, (x = a ∨ x = b ∨ x = c ∨ x = d) →
      (vsubDt3 a b c d i x = a ∨ vsubDt3 a b c d i x = b ∨ vsubDt3 a b c d i x = c ∨
        vsubDt3 a b c d i x = d) := by
  decide +kernel

private theorem vsub_kv4_comm : ∀ a b c d : Fin 8, (a, b, c, d) ∈ vsubQuads → ∀ i : Fin 4,
    ∀ j : Fin 3, vsubKv4 a b c d i * vsubDt3 a b c d j = vsubDt3 a b c d j * vsubKv4 a b c d i := by
  decide +kernel

private theorem vsub_dts_core : ∀ a b c d : Fin 8, (a, b, c, d) ∈ vsubQuads →
    ∀ a' b' c' d' : Fin 8, a' ≠ b' → a' ≠ c' → a' ≠ d' → b' ≠ c' → b' ≠ d' → c' ≠ d' →
      ({a', b', c', d'} : Finset (Fin 8)) = {a, b, c, d} →
      ∃ j : Fin 3, swap a' b' * swap c' d' = vsubDt3 a b c d j := by
  decide +kernel

private theorem vsub_cyc_core : ∀ x y z : Fin 8, x ≠ y → y ≠ z → x ≠ z →
    (swap x y * swap y z) ^ 3 = 1 ∧ swap x y * swap y z ≠ 1 := by
  decide +kernel

private theorem vsub_cyc_id : ∀ a b c d : Fin 8, (a, b, c, d) ∈ vsubQuads →
    swap a b * swap c d = (swap a c * swap c b) * (swap a c * swap c d) ∧
    swap a c * swap b d = (swap a b * swap b c) * (swap a b * swap b d) ∧
    swap a d * swap b c = (swap a b * swap b d) * (swap a b * swap b c) := by
  decide +kernel

private theorem vsub_core_V : ∀ a b c d : Fin 8, (a, b, c, d) ∈ vsubQuads →
    ∀ u : Fin 8, (u = a ∨ u = b ∨ u = c ∨ u = d) →
    ∀ v : Fin 8, (v = a ∨ v = b ∨ v = c ∨ v = d) → u ≠ v →
    ∀ w : Fin 8, (w = a ∨ w = b ∨ w = c ∨ w = d) → u ≠ w → v ≠ w →
    ∀ z : Fin 8, (z = a ∨ z = b ∨ z = c ∨ z = d) → u ≠ z → v ≠ z → w ≠ z →
    (∀ i : Fin 3, ∀ x : Fin 8, (x = a ∨ x = b ∨ x = c ∨ x = d) →
        vsubTf a b c d u v w z (vsubDt3 a b c d i x) =
          vsubDt3 a b c d i (vsubTf a b c d u v w z x)) →
    ∃ i : Fin 4, vsubKv4 a b c d i a = u ∧ vsubKv4 a b c d i b = v ∧ vsubKv4 a b c d i c = w ∧
      vsubKv4 a b c d i d = z := by
  decide +kernel

private theorem vsub_core_N : ∀ a b c d : Fin 8, (a, b, c, d) ∈ vsubQuads →
    ∀ u : Fin 8, (u = a ∨ u = b ∨ u = c ∨ u = d) →
    ∀ v : Fin 8, (v = a ∨ v = b ∨ v = c ∨ v = d) → u ≠ v →
    ∀ w : Fin 8, (w = a ∨ w = b ∨ w = c ∨ w = d) → u ≠ w → v ≠ w →
    ∀ z : Fin 8, (z = a ∨ z = b ∨ z = c ∨ z = d) → u ≠ z → v ≠ z → w ≠ z →
    ¬ (((swap u v * swap v w) * (swap a b * swap b c)⁻¹) ^ 3 = 1 ∧
       ((swap u v * swap v w) * (swap a b * swap b c)⁻¹) ≠ 1) →
    (∀ x : Fin 8, (x = a ∨ x = b ∨ x = c ∨ x = d) →
       vsubTf a b c d u v w z (vsubTf a b c d u v w z (vsubTf a b c d u v w z x)) = x →
       vsubTf a b c d u v w z x = x) →
    ∃ i : Fin 4, vsubKv4 a b c d i a = u ∧ vsubKv4 a b c d i b = v ∧ vsubKv4 a b c d i c = w ∧
      vsubKv4 a b c d i d = z := by
  decide +kernel

private theorem vsub_core_S : ∀ a b c d : Fin 8, (a, b, c, d) ∈ vsubQuads →
    ∀ u : Fin 8, u ≠ a → u ≠ b → u ≠ c → u ≠ d →
    ∀ v : Fin 8, v ≠ a → v ≠ b → v ≠ c → v ≠ d → u ≠ v →
    ∀ w : Fin 8, w ≠ a → w ≠ b → w ≠ c → w ≠ d → u ≠ w → v ≠ w →
    (((swap u v * swap v w) * (swap a b * swap b c)⁻¹) ^ 3 = 1 ∧
       ((swap u v * swap v w) * (swap a b * swap b c)⁻¹) ≠ 1) := by
  decide +kernel

private theorem vsub_blocks {B : Finset (Fin 8)} (hB : B ∈ blocks3) :
    ∃ a b c d e f g h : Fin 8, (a, b, c, d) ∈ vsubQuads ∧ (e, f, g, h) ∈ vsubQuads ∧
      B = {a, b, c, d} ∧ Bᶜ = {e, f, g, h} ∧
      (∀ i j : Fin 4, (vsubKv4 a b c d i * vsubKv4 e f g h j) *
          (vsubKv4 a b c d i * vsubKv4 e f g h j) = 1 ∧
        Equiv.Perm.sign (vsubKv4 a b c d i * vsubKv4 e f g h j) = 1) ∧
      (Finset.univ.image fun ij : Fin 4 × Fin 4 =>
        vsubKv4 a b c d ij.1 * vsubKv4 e f g h ij.2).card = 16 := by
  simp only [blocks3, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl
  · exact ⟨0, 1, 2, 3, 4, 5, 6, 7, by decide, by decide, rfl, by decide, by decide +kernel,
      by decide +kernel⟩
  · exact ⟨0, 1, 4, 5, 2, 3, 6, 7, by decide, by decide, rfl, by decide, by decide +kernel,
      by decide +kernel⟩
  · exact ⟨0, 1, 6, 7, 2, 3, 4, 5, by decide, by decide, rfl, by decide, by decide +kernel,
      by decide +kernel⟩

private theorem vsub_tf_spec (p : P8) (a b c d x : Fin 8) (hx : x = a ∨ x = b ∨ x = c ∨ x = d) :
    p x = vsubTf a b c d (p a) (p b) (p c) (p d) x := by
  unfold vsubTf
  by_cases h1 : x = a
  · subst h1; simp
  · by_cases h2 : x = b
    · subst h2; simp [h1]
    · by_cases h3 : x = c
      · subst h3; simp [h1, h2]
      · have h4 : x = d := by tauto
        subst h4; simp [h1, h2, h3]

private theorem vsub_comm_of_supp {f g : P8} {S T : Finset (Fin 8)} (hST : Disjoint S T)
    (hf : ∀ x, x ∉ S → f x = x) (hg : ∀ x, x ∉ T → g x = x) : f * g = g * f := by
  have hfS : ∀ x ∈ S, f x ∈ S := by
    intro x hx
    by_contra h
    have h1 : f (f x) = f x := hf _ h
    have h2 : f x = x := f.injective h1
    exact h (by rw [h2]; exact hx)
  have hgT : ∀ x ∈ T, g x ∈ T := by
    intro x hx
    by_contra h
    have h1 : g (g x) = g x := hg _ h
    have h2 : g x = x := g.injective h1
    exact h (by rw [h2]; exact hx)
  ext x
  simp only [Equiv.Perm.mul_apply]
  by_cases hxS : x ∈ S
  · have hxT : x ∉ T := Finset.disjoint_left.mp hST hxS
    have hfxT : f x ∉ T := Finset.disjoint_left.mp hST (hfS x hxS)
    rw [hg x hxT, hg (f x) hfxT]
  · rw [hf x hxS]
    by_cases hxT : x ∈ T
    · have : g x ∉ S := fun h => Finset.disjoint_left.mp hST h (hgT x hxT)
      rw [hf (g x) this]
    · rw [hg x hxT, hf x hxS]

private theorem vsub_pgroup_cube {N : Subgroup P8} (hN : IsPGroup 2 ↥N) {y : P8} (hy : y ∈ N)
    (h3 : y ^ 3 = 1) : y = 1 := by
  obtain ⟨k, hk⟩ := hN ⟨y, hy⟩
  have hk' : y ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa [Subgroup.coe_pow] using this
  have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  have h4 : orderOf y ∣ Nat.gcd (2 ^ k) 3 := Nat.dvd_gcd h1 h2
  rw [hcop.gcd_eq_one] at h4
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)

private theorem vsub_part_V {a b c d : Fin 8} (hq : (a, b, c, d) ∈ vsubQuads) {g : P8}
    (hS : ∀ x, (g x = a ∨ g x = b ∨ g x = c ∨ g x = d) ↔ (x = a ∨ x = b ∨ x = c ∨ x = d))
    (hc : ∀ j : Fin 3, g * vsubDt3 a b c d j = vsubDt3 a b c d j * g) :
    ∃ i : Fin 4, ∀ x, (x = a ∨ x = b ∨ x = c ∨ x = d) → g x = vsubKv4 a b c d i x := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := vsub_quad_ne a b c d hq
  have hu := (hS a).2 (Or.inl rfl)
  have hv := (hS b).2 (Or.inr (Or.inl rfl))
  have hw := (hS c).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hz := (hS d).2 (Or.inr (Or.inr (Or.inr rfl)))
  have hcomm : ∀ (i : Fin 3) (x : Fin 8), (x = a ∨ x = b ∨ x = c ∨ x = d) →
      vsubTf a b c d (g a) (g b) (g c) (g d) (vsubDt3 a b c d i x) =
        vsubDt3 a b c d i (vsubTf a b c d (g a) (g b) (g c) (g d) x) := by
    intro i x hx
    rw [← vsub_tf_spec g a b c d _ (vsub_dt3_stab a b c d hq i x hx),
      ← vsub_tf_spec g a b c d x hx]
    have := Equiv.Perm.ext_iff.mp (hc i) x
    simpa only [Equiv.Perm.mul_apply] using this
  obtain ⟨i, h1, h2, h3, h4⟩ := vsub_core_V a b c d hq (g a) hu (g b) hv (g.injective.ne hab)
    (g c) hw (g.injective.ne hac) (g.injective.ne hbc) (g d) hz (g.injective.ne had)
    (g.injective.ne hbd) (g.injective.ne hcd) hcomm
  refine ⟨i, ?_⟩
  rintro x (rfl | rfl | rfl | rfl)
  · exact h1.symm
  · exact h2.symm
  · exact h3.symm
  · exact h4.symm

private theorem vsub_part_N {a b c d : Fin 8} (hq : (a, b, c, d) ∈ vsubQuads) {N H : Subgroup P8}
    (hN : IsPGroup 2 ↥N) (hnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hr : swap a b * swap b c ∈ H) {p : P8} (hp : p ∈ N)
    (hS : ∀ x, (p x = a ∨ p x = b ∨ p x = c ∨ p x = d) ↔ (x = a ∨ x = b ∨ x = c ∨ x = d)) :
    ∃ i : Fin 4, ∀ x, (x = a ∨ x = b ∨ x = c ∨ x = d) → p x = vsubKv4 a b c d i x := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := vsub_quad_ne a b c d hq
  have hu := (hS a).2 (Or.inl rfl)
  have hv := (hS b).2 (Or.inr (Or.inl rfl))
  have hw := (hS c).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hz := (hS d).2 (Or.inr (Or.inr (Or.inr rfl)))
  have c1 : ¬ (((swap (p a) (p b) * swap (p b) (p c)) * (swap a b * swap b c)⁻¹) ^ 3 = 1 ∧
      ((swap (p a) (p b) * swap (p b) (p c)) * (swap a b * swap b c)⁻¹) ≠ 1) := by
    rintro ⟨h3, h1⟩
    have hcm : p * ((swap a b * swap b c) * p⁻¹ * (swap a b * swap b c)⁻¹) ∈ N :=
      N.mul_mem hp (hnorm _ hr _ (N.inv_mem hp))
    have e : p * ((swap a b * swap b c) * p⁻¹ * (swap a b * swap b c)⁻¹) =
        (swap (p a) (p b) * swap (p b) (p c)) * (swap a b * swap b c)⁻¹ := by
      rw [Equiv.swap_apply_apply, Equiv.swap_apply_apply]; group
    rw [e] at hcm
    exact h1 (vsub_pgroup_cube hN hcm h3)
  set T : Fin 8 → Fin 8 := vsubTf a b c d (p a) (p b) (p c) (p d) with hT
  have c2 : ∀ x : Fin 8, (x = a ∨ x = b ∨ x = c ∨ x = d) → T (T (T x)) = x → T x = x := by
    intro x hx h3
    have hspec : ∀ y, (y = a ∨ y = b ∨ y = c ∨ y = d) → p y = T y :=
      fun y hy => vsub_tf_spec p a b c d y hy
    have hp1 : p x = T x := hspec x hx
    have hx1 : p x = a ∨ p x = b ∨ p x = c ∨ p x = d := (hS x).2 hx
    have hp2 : p (p x) = T (T x) := by
      rw [← hp1]; exact hspec _ hx1
    have hx2 : p (p x) = a ∨ p (p x) = b ∨ p (p x) = c ∨ p (p x) = d := (hS _).2 hx1
    have hp3 : p (p (p x)) = T (T (T x)) := by
      rw [← hp2]; exact hspec _ hx2
    rw [h3] at hp3
    obtain ⟨k, hk⟩ := hN ⟨p, hp⟩
    have hk' : p ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa [Subgroup.coe_pow] using this
    have hper1 : Function.IsPeriodicPt (⇑p) 3 x := hp3
    have hper2 : Function.IsPeriodicPt (⇑p) (2 ^ k) x := by
      show (⇑p)^[2 ^ k] x = x
      rw [Equiv.Perm.iterate_eq_pow, hk']
      rfl
    have hcop : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
    have hper := hper1.gcd hper2
    rw [hcop] at hper
    have hfix : p x = x := hper
    rw [← hp1]; exact hfix
  obtain ⟨i, h1, h2, h3, h4⟩ := vsub_core_N a b c d hq (p a) hu (p b) hv (p.injective.ne hab)
    (p c) hw (p.injective.ne hac) (p.injective.ne hbc) (p d) hz (p.injective.ne had)
    (p.injective.ne hbd) (p.injective.ne hcd) c1 c2
  refine ⟨i, ?_⟩
  rintro x (rfl | rfl | rfl | rfl)
  · exact h1.symm
  · exact h2.symm
  · exact h3.symm
  · exact h4.symm

private theorem vsub_part_S {a b c d : Fin 8} (hq : (a, b, c, d) ∈ vsubQuads) {N H : Subgroup P8}
    (hN : IsPGroup 2 ↥N) (hnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hr : swap a b * swap b c ∈ H) {p : P8} (hp : p ∈ N)
    (hS : ∀ x, (p x = a ∨ p x = b ∨ p x = c ∨ p x = d) ↔ ¬ (x = a ∨ x = b ∨ x = c ∨ x = d)) :
    False := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := vsub_quad_ne a b c d hq
  have hna : ¬ (p a = a ∨ p a = b ∨ p a = c ∨ p a = d) := fun h => (hS a).1 h (Or.inl rfl)
  have hnb : ¬ (p b = a ∨ p b = b ∨ p b = c ∨ p b = d) := fun h =>
    (hS b).1 h (Or.inr (Or.inl rfl))
  have hnc : ¬ (p c = a ∨ p c = b ∨ p c = c ∨ p c = d) := fun h =>
    (hS c).1 h (Or.inr (Or.inr (Or.inl rfl)))
  simp only [not_or] at hna hnb hnc
  obtain ⟨h3, h1⟩ := vsub_core_S a b c d hq (p a) hna.1 hna.2.1 hna.2.2.1 hna.2.2.2 (p b) hnb.1
    hnb.2.1 hnb.2.2.1 hnb.2.2.2 (p.injective.ne hab) (p c) hnc.1 hnc.2.1 hnc.2.2.1 hnc.2.2.2
    (p.injective.ne hac) (p.injective.ne hbc)
  have hcm : p * ((swap a b * swap b c) * p⁻¹ * (swap a b * swap b c)⁻¹) ∈ N :=
    N.mul_mem hp (hnorm _ hr _ (N.inv_mem hp))
  have e : p * ((swap a b * swap b c) * p⁻¹ * (swap a b * swap b c)⁻¹) =
      (swap (p a) (p b) * swap (p b) (p c)) * (swap a b * swap b c)⁻¹ := by
    rw [Equiv.swap_apply_apply, Equiv.swap_apply_apply]; group
  rw [e] at hcm
  exact h1 (vsub_pgroup_cube hN hcm h3)

private theorem vsub_mem_dts {a b c d : Fin 8} (hq : (a, b, c, d) ∈ vsubQuads) {e : P8} :
    e ∈ dts ({a, b, c, d} : Finset (Fin 8)) ↔ ∃ j : Fin 3, e = vsubDt3 a b c d j := by
  constructor
  · rintro ⟨a', b', c', d', h1, h2, h3, h4, h5, h6, hS, rfl⟩
    obtain ⟨j, hj⟩ := vsub_dts_core a b c d hq a' b' c' d' h1 h2 h3 h4 h5 h6 hS
    exact ⟨j, hj⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := vsub_quad_ne a b c d hq
    fin_cases j
    · exact ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl, rfl⟩
    · refine ⟨a, c, b, d, hac, hab, had, hbc.symm, hcd, hbd, ?_, rfl⟩
      ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    · refine ⟨a, d, b, c, had, hab, hac, hbd.symm, hcd.symm, hbc, ?_, rfl⟩
      ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

private theorem vsub_compl (B : Finset (Fin 8)) : Vsub Bᶜ = Vsub B := by
  ext g
  rw [mem_Vsub, mem_Vsub, compl_compl, Set.union_comm]
  simp only [Finset.mem_compl, not_iff_not]

private theorem vsub_mem_B {B : Finset (Fin 8)} {a b c d : Fin 8} (hB : B = {a, b, c, d})
    (y : Fin 8) : y ∈ B ↔ y = a ∨ y = b ∨ y = c ∨ y = d := by
  rw [hB]; simp only [Finset.mem_insert, Finset.mem_singleton]

private theorem vsub_mem_Bc {B : Finset (Fin 8)} {a b c d : Fin 8} (hBc : Bᶜ = {a, b, c, d})
    (y : Fin 8) : y ∉ B ↔ y = a ∨ y = b ∨ y = c ∨ y = d := by
  rw [← Finset.mem_compl, hBc]; simp only [Finset.mem_insert, Finset.mem_singleton]

private theorem vsub_agree {B : Finset (Fin 8)} {a b c d a' b' c' d' : Fin 8}
    (hq1 : (a, b, c, d) ∈ vsubQuads) (hq2 : (a', b', c', d') ∈ vsubQuads)
    (hmem1 : ∀ x, x ∈ B ↔ x = a ∨ x = b ∨ x = c ∨ x = d)
    (hmem2 : ∀ x, x ∉ B ↔ x = a' ∨ x = b' ∨ x = c' ∨ x = d') {p : P8} {i j : Fin 4}
    (hi : ∀ x, (x = a ∨ x = b ∨ x = c ∨ x = d) → p x = vsubKv4 a b c d i x)
    (hj : ∀ x, (x = a' ∨ x = b' ∨ x = c' ∨ x = d') → p x = vsubKv4 a' b' c' d' j x) :
    p = vsubKv4 a b c d i * vsubKv4 a' b' c' d' j := by
  ext x
  simp only [Equiv.Perm.mul_apply]
  by_cases hx : x ∈ B
  · have hx1 := (hmem1 x).1 hx
    have hx2 : ¬ (x = a' ∨ x = b' ∨ x = c' ∨ x = d') := fun h => (hmem2 x).2 h hx
    simp only [not_or] at hx2
    rw [vsub_kv4_supp a' b' c' d' hq2 j x hx2.1 hx2.2.1 hx2.2.2.1 hx2.2.2.2, hi x hx1]
  · have hx2 := (hmem2 x).1 hx
    have hy := vsub_kv4_stab a' b' c' d' hq2 j x hx2
    have hy' : ¬ (vsubKv4 a' b' c' d' j x = a ∨ vsubKv4 a' b' c' d' j x = b ∨
        vsubKv4 a' b' c' d' j x = c ∨ vsubKv4 a' b' c' d' j x = d) :=
      fun h => (hmem2 _).2 hy ((hmem1 _).2 h)
    simp only [not_or] at hy'
    rw [vsub_kv4_supp a b c d hq1 i _ hy'.1 hy'.2.1 hy'.2.2.1 hy'.2.2.2, hj x hx2]

private theorem vsub_decomp {B : Finset (Fin 8)} {a b c d a' b' c' d' : Fin 8}
    (hq1 : (a, b, c, d) ∈ vsubQuads) (hq2 : (a', b', c', d') ∈ vsubQuads)
    (hB : B = {a, b, c, d}) (hBc : Bᶜ = {a', b', c', d'}) {x : P8} (hx : x ∈ Vsub B) :
    ∃ i j : Fin 4, x = vsubKv4 a b c d i * vsubKv4 a' b' c' d' j := by
  have hmem1 := vsub_mem_B hB
  have hmem2 := vsub_mem_Bc hBc
  obtain ⟨hcomm, hfix⟩ := mem_Vsub.1 hx
  have hS1 : ∀ y, (x y = a ∨ x y = b ∨ x y = c ∨ x y = d) ↔ (y = a ∨ y = b ∨ y = c ∨ y = d) := by
    intro y; rw [← hmem1, ← hmem1]; exact hfix y
  have hS2 : ∀ y, (x y = a' ∨ x y = b' ∨ x y = c' ∨ x y = d') ↔
      (y = a' ∨ y = b' ∨ y = c' ∨ y = d') := by
    intro y; rw [← hmem2, ← hmem2]; exact not_congr (hfix y)
  have hc1 : ∀ j : Fin 3, x * vsubDt3 a b c d j = vsubDt3 a b c d j * x := fun j =>
    hcomm _ (Or.inl (by rw [hB]; exact (vsub_mem_dts hq1).2 ⟨j, rfl⟩))
  have hc2 : ∀ j : Fin 3, x * vsubDt3 a' b' c' d' j = vsubDt3 a' b' c' d' j * x := fun j =>
    hcomm _ (Or.inr (by rw [hBc]; exact (vsub_mem_dts hq2).2 ⟨j, rfl⟩))
  obtain ⟨i, hi⟩ := vsub_part_V hq1 hS1 hc1
  obtain ⟨j, hj⟩ := vsub_part_V hq2 hS2 hc2
  exact ⟨i, j, vsub_agree hq1 hq2 hmem1 hmem2 hi hj⟩

private theorem vsub_mem_kv4 {B : Finset (Fin 8)} {a b c d a' b' c' d' : Fin 8}
    (hq1 : (a, b, c, d) ∈ vsubQuads) (hq2 : (a', b', c', d') ∈ vsubQuads)
    (hB : B = {a, b, c, d}) (hBc : Bᶜ = {a', b', c', d'}) (i : Fin 4) :
    vsubKv4 a b c d i ∈ Vsub B := by
  have hmem1 := vsub_mem_B hB
  rw [mem_Vsub]
  refine ⟨?_, ?_⟩
  · rintro c' (hc | hc)
    · rw [hB] at hc
      obtain ⟨j, rfl⟩ := (vsub_mem_dts hq1).1 hc
      exact vsub_kv4_comm a b c d hq1 i j
    · rw [hBc] at hc
      obtain ⟨j, rfl⟩ := (vsub_mem_dts hq2).1 hc
      refine vsub_comm_of_supp (S := {a, b, c, d}) (T := {a', b', c', d'}) ?_ ?_ ?_
      · rw [← hB, ← hBc]; exact disjoint_compl_right
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        exact vsub_kv4_supp a b c d hq1 i x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        exact vsub_dt3_supp a' b' c' d' hq2 j x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
  · intro x
    rw [hmem1, hmem1]
    constructor
    · intro hx
      by_contra hx'
      have hx'' : ¬ x = a ∧ ¬ x = b ∧ ¬ x = c ∧ ¬ x = d := by simpa only [not_or] using hx'
      rw [vsub_kv4_supp a b c d hq1 i x hx''.1 hx''.2.1 hx''.2.2.1 hx''.2.2.2] at hx
      exact hx' hx
    · exact vsub_kv4_stab a b c d hq1 i x

private theorem vsub_mem_kv4' {B : Finset (Fin 8)} {a b c d a' b' c' d' : Fin 8}
    (hq1 : (a, b, c, d) ∈ vsubQuads) (hq2 : (a', b', c', d') ∈ vsubQuads)
    (hB : B = {a, b, c, d}) (hBc : Bᶜ = {a', b', c', d'}) (j : Fin 4) :
    vsubKv4 a' b' c' d' j ∈ Vsub B := by
  rw [← vsub_compl B]
  exact vsub_mem_kv4 hq2 hq1 hBc (by rw [compl_compl]; exact hB) j

private theorem vsub_dts_conj {S S' : Finset (Fin 8)} {g c : P8} (h : ∀ x, g x ∈ S' ↔ x ∈ S)
    (hc : c ∈ dts S) : g * c * g⁻¹ ∈ dts S' := by
  obtain ⟨a, b, c', d, h1, h2, h3, h4, h5, h6, hS, rfl⟩ := hc
  refine ⟨g a, g b, g c', g d, g.injective.ne h1, g.injective.ne h2, g.injective.ne h3,
    g.injective.ne h4, g.injective.ne h5, g.injective.ne h6, ?_, ?_⟩
  · ext y
    have hy : y ∈ S' ↔ g⁻¹ y ∈ S := by
      rw [← h (g⁻¹ y)]; simp
    rw [hy, ← hS]
    simp only [Finset.mem_insert, Finset.mem_singleton, Equiv.Perm.inv_eq_iff_eq]
  · rw [Equiv.swap_apply_apply g a b, Equiv.swap_apply_apply g c' d]; group

private theorem vsub_conj_mem {B : Finset (Fin 8)} {g v : P8} (hg : g ∈ PStab B)
    (hv : v ∈ Vsub B) : g * v * g⁻¹ ∈ Vsub B := by
  have hdts : ∀ g' ∈ PStab B, ∀ c ∈ dts B ∪ dts Bᶜ, g' * c * g'⁻¹ ∈ dts B ∪ dts Bᶜ := by
    intro g' hg' c hc
    rcases hg' with hf | hs
    · rcases hc with hc | hc
      · exact Or.inl (vsub_dts_conj hf hc)
      · exact Or.inr (vsub_dts_conj (fun x => by simp only [Finset.mem_compl, hf x]) hc)
    · rcases hc with hc | hc
      · exact Or.inr (vsub_dts_conj (S := B) (S' := Bᶜ)
          (fun x => by simp only [Finset.mem_compl, hs x, not_not]) hc)
      · exact Or.inl (vsub_dts_conj (S := Bᶜ) (S' := B)
          (fun x => by simp only [Finset.mem_compl, hs x]) hc)
  obtain ⟨hcomm, hfix⟩ := mem_Vsub.1 hv
  rw [mem_Vsub]
  refine ⟨?_, ?_⟩
  · intro c hc
    have hc' := hcomm _ (hdts g⁻¹ (inv_mem hg) c hc)
    rw [inv_inv] at hc'
    calc g * v * g⁻¹ * c = g * (v * (g⁻¹ * c * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * c * g) * v) * g⁻¹ := by rw [hc']
      _ = c * (g * v * g⁻¹) := by group
  · intro y
    rcases hg with hf | hs
    · simp only [Equiv.Perm.mul_apply]
      rw [hf (v (g⁻¹ y)), hfix (g⁻¹ y)]
      simpa using (hf (g⁻¹ y)).symm
    · simp only [Equiv.Perm.mul_apply]
      rw [hs (v (g⁻¹ y)), hfix (g⁻¹ y)]
      simpa using (hs (g⁻¹ y)).symm

private theorem vsub_residual_le {B : Finset (Fin 8)} :
    oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ PStab B) ≤ PStab B := by
  unfold oPrimeResidualOf
  rw [Subgroup.closure_le]
  intro y hy
  exact hy.1.2

private theorem vsub_swap_mem_iff {B : Finset (Fin 8)} {x y : Fin 8} (h : x ∈ B ↔ y ∈ B)
    (w : Fin 8) : swap x y w ∈ B ↔ w ∈ B := by
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact h.symm
  · subst h2; exact h
  · exact Iff.rfl

private theorem vsub_cyc_mem_R {B : Finset (Fin 8)} {x y z : Fin 8} (hxy : x ≠ y) (hyz : y ≠ z)
    (hxz : x ≠ z) (h1 : x ∈ B ↔ y ∈ B) (h2 : y ∈ B ↔ z ∈ B) :
    swap x y * swap y z ∈ oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ PStab B) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨h3, hne⟩ := vsub_cyc_core x y z hxy hyz hxz
  unfold oPrimeResidualOf
  refine Subgroup.subset_closure ⟨⟨?_, Or.inl ?_⟩, 1, ?_⟩
  · apply Equiv.Perm.mem_alternatingGroup.mpr
    simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxy, Equiv.Perm.sign_swap hyz]
  · intro w
    simp only [Equiv.Perm.mul_apply]
    exact (vsub_swap_mem_iff h1 _).trans (vsub_swap_mem_iff h2 w)
  · simpa using orderOf_eq_prime h3 hne

private theorem vsub_kv4_mem_R {B : Finset (Fin 8)} {a b c d : Fin 8}
    (hq : (a, b, c, d) ∈ vsubQuads)
    (hhom : ∀ x y : Fin 8, (x = a ∨ x = b ∨ x = c ∨ x = d) → (y = a ∨ y = b ∨ y = c ∨ y = d) →
      (x ∈ B ↔ y ∈ B)) (i : Fin 4) :
    vsubKv4 a b c d i ∈ oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ PStab B) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := vsub_quad_ne a b c d hq
  obtain ⟨e1, e2, e3⟩ := vsub_cyc_id a b c d hq
  have ha : a = a ∨ a = b ∨ a = c ∨ a = d := Or.inl rfl
  have hb : b = a ∨ b = b ∨ b = c ∨ b = d := Or.inr (Or.inl rfl)
  have hc : c = a ∨ c = b ∨ c = c ∨ c = d := Or.inr (Or.inr (Or.inl rfl))
  have hd : d = a ∨ d = b ∨ d = c ∨ d = d := Or.inr (Or.inr (Or.inr rfl))
  fin_cases i
  · exact one_mem _
  · show swap a b * swap c d ∈ _
    rw [e1]
    exact mul_mem (vsub_cyc_mem_R hac hbc.symm hab (hhom _ _ ha hc) (hhom _ _ hc hb))
      (vsub_cyc_mem_R hac hcd had (hhom _ _ ha hc) (hhom _ _ hc hd))
  · show swap a c * swap b d ∈ _
    rw [e2]
    exact mul_mem (vsub_cyc_mem_R hab hbc hac (hhom _ _ ha hb) (hhom _ _ hb hc))
      (vsub_cyc_mem_R hab hbd had (hhom _ _ ha hb) (hhom _ _ hb hd))
  · show swap a d * swap b c ∈ _
    rw [e3]
    exact mul_mem (vsub_cyc_mem_R hab hbd had (hhom _ _ ha hb) (hhom _ _ hb hd))
      (vsub_cyc_mem_R hab hbc hac (hhom _ _ ha hb) (hhom _ _ hb hc))

theorem Vsub_card {B : Finset (Fin 8)} (hB : B ∈ blocks3) : Nat.card ↥(Vsub B) = 16 := by
  obtain ⟨a, b, c, d, a', b', c', d', hq1, hq2, hB1, hB2, -, hcard⟩ := vsub_blocks hB
  have hmem : ∀ x : P8, x ∈ Vsub B ↔
      x ∈ Finset.univ.image fun ij : Fin 4 × Fin 4 =>
        vsubKv4 a b c d ij.1 * vsubKv4 a' b' c' d' ij.2 := by
    intro x
    rw [Finset.mem_image]
    constructor
    · intro hx
      obtain ⟨i, j, rfl⟩ := vsub_decomp hq1 hq2 hB1 hB2 hx
      exact ⟨(i, j), Finset.mem_univ _, rfl⟩
    · rintro ⟨⟨i, j⟩, -, rfl⟩
      exact mul_mem (vsub_mem_kv4 hq1 hq2 hB1 hB2 i) (vsub_mem_kv4' hq1 hq2 hB1 hB2 j)
  rw [Nat.card_congr (Equiv.subtypeEquivRight hmem), Nat.card_eq_fintype_card, Fintype.card_coe,
    hcard]

theorem Vsub_sq {B : Finset (Fin 8)} (hB : B ∈ blocks3) : ∀ v ∈ Vsub B, v * v = 1 := by
  obtain ⟨a, b, c, d, a', b', c', d', hq1, hq2, hB1, hB2, hsq, -⟩ := vsub_blocks hB
  intro x hx
  obtain ⟨i, j, rfl⟩ := vsub_decomp hq1 hq2 hB1 hB2 hx
  exact (hsq i j).1

theorem Vsub_le_alt {B : Finset (Fin 8)} (hB : B ∈ blocks3) :
    Vsub B ≤ alternatingGroup (Fin 8) := by
  obtain ⟨a, b, c, d, a', b', c', d', hq1, hq2, hB1, hB2, hsq, -⟩ := vsub_blocks hB
  intro x hx
  obtain ⟨i, j, rfl⟩ := vsub_decomp hq1 hq2 hB1 hB2 hx
  exact Equiv.Perm.mem_alternatingGroup.mpr (hsq i j).2

theorem PStab_le_normalizer_Vsub {B : Finset (Fin 8)} (hB : B ∈ blocks3) :
    PStab B ≤ Subgroup.normalizer (Vsub B : Set P8) := by
  have _ := hB
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨fun hv => vsub_conj_mem hg hv, fun hv => ?_⟩
  have h1 := vsub_conj_mem (inv_mem hg) hv
  have e : g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v := by group
  rwa [e] at h1

theorem Vsub_le_R {B : Finset (Fin 8)} (hB : B ∈ blocks3) :
    Vsub B ≤ oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ PStab B) := by
  obtain ⟨a, b, c, d, a', b', c', d', hq1, hq2, hB1, hB2, -, -⟩ := vsub_blocks hB
  have hmem1 := vsub_mem_B hB1
  have hmem2 := vsub_mem_Bc hB2
  intro x hx
  obtain ⟨i, j, rfl⟩ := vsub_decomp hq1 hq2 hB1 hB2 hx
  refine mul_mem (vsub_kv4_mem_R hq1 ?_ i) (vsub_kv4_mem_R hq2 ?_ j)
  · intro x y hx hy
    exact ⟨fun _ => (hmem1 y).2 hy, fun _ => (hmem1 x).2 hx⟩
  · intro x y hx hy
    exact ⟨fun h => absurd h ((hmem2 x).2 hx), fun h => absurd h ((hmem2 y).2 hy)⟩

private theorem vsub_isPGroup {B : Finset (Fin 8)} (hB : B ∈ blocks3) : IsPGroup 2 ↥(Vsub B) := by
  intro q
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simp only [pow_one, pow_two, Subgroup.coe_mul, Subgroup.coe_one]
  exact Vsub_sq hB q.1 q.2

theorem pCoreOf_eq_Vsub {B : Finset (Fin 8)} (hB : B ∈ blocks3) {T : Subgroup P8}
    (hT : T ≤ PStab B) :
    pCoreOf 2 (oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ PStab B) ⊔ T) = Vsub B := by
  obtain ⟨a, b, c, d, a', b', c', d', hq1, hq2, hB1, hB2, -, -⟩ := vsub_blocks hB
  have hmem1 := vsub_mem_B hB1
  have hmem2 := vsub_mem_Bc hB2
  obtain ⟨hab, hac, -, hbc, -, -⟩ := vsub_quad_ne a b c d hq1
  obtain ⟨hab', hac', -, hbc', -, -⟩ := vsub_quad_ne a' b' c' d' hq2
  have hA : a ∈ B := (hmem1 a).2 (Or.inl rfl)
  have hBm : b ∈ B := (hmem1 b).2 (Or.inr (Or.inl rfl))
  have hC : c ∈ B := (hmem1 c).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hA' : a' ∉ B := (hmem2 a').2 (Or.inl rfl)
  have hB' : b' ∉ B := (hmem2 b').2 (Or.inr (Or.inl rfl))
  have hC' : c' ∉ B := (hmem2 c').2 (Or.inr (Or.inr (Or.inl rfl)))
  have hHle : oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ PStab B) ⊔ T ≤ PStab B :=
    sup_le vsub_residual_le hT
  have hr1 : swap a b * swap b c ∈
      oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ PStab B) ⊔ T :=
    Subgroup.mem_sup_left (vsub_cyc_mem_R hab hbc hac ⟨fun _ => hBm, fun _ => hA⟩
      ⟨fun _ => hC, fun _ => hBm⟩)
  have hr2 : swap a' b' * swap b' c' ∈
      oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ PStab B) ⊔ T :=
    Subgroup.mem_sup_left (vsub_cyc_mem_R hab' hbc' hac'
      ⟨fun h => absurd h hA', fun h => absurd h hB'⟩
      ⟨fun h => absurd h hB', fun h => absurd h hC'⟩)
  apply le_antisymm
  · intro p hp
    have hNp : IsPGroup 2
        ↥(pCoreOf 2 (oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ PStab B) ⊔ T)) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
    have hnorm : ∀ h ∈ oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ PStab B) ⊔ T,
        ∀ n ∈ pCoreOf 2 (oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ PStab B) ⊔ T),
          h * n * h⁻¹ ∈ pCoreOf 2 (oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ PStab B) ⊔ T) :=
      fun h hh n hn =>
        (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hh) n).mp hn
    have hpW : p ∈ PStab B := hHle (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hp)
    rcases hpW with hfix | hswp
    · have hS1 : ∀ x, (p x = a ∨ p x = b ∨ p x = c ∨ p x = d) ↔
          (x = a ∨ x = b ∨ x = c ∨ x = d) := by
        intro x; rw [← hmem1, ← hmem1]; exact hfix x
      have hS2 : ∀ x, (p x = a' ∨ p x = b' ∨ p x = c' ∨ p x = d') ↔
          (x = a' ∨ x = b' ∨ x = c' ∨ x = d') := by
        intro x; rw [← hmem2, ← hmem2]; exact not_congr (hfix x)
      obtain ⟨i, hi⟩ := vsub_part_N hq1 hNp hnorm hr1 hp hS1
      obtain ⟨j, hj⟩ := vsub_part_N hq2 hNp hnorm hr2 hp hS2
      rw [vsub_agree hq1 hq2 hmem1 hmem2 hi hj]
      exact mul_mem (vsub_mem_kv4 hq1 hq2 hB1 hB2 i) (vsub_mem_kv4' hq1 hq2 hB1 hB2 j)
    · exfalso
      refine vsub_part_S hq1 hNp hnorm hr1 hp ?_
      intro x
      rw [← hmem1, ← hmem1]
      exact hswp x
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((Vsub_le_R hB).trans le_sup_left)
      (hHle.trans (PStab_le_normalizer_Vsub hB)) (vsub_isPGroup hB)

end CFSG.Quasithin.A38c6
